#![allow(unused_imports)]
use super::shared::{fence_acquire, invalid_mut, AtomicPtrRmw, SpinWait, StrictProvenance, Waiter};
use std::{
    fmt,
    pin::Pin,
    ptr::{self, NonNull},
    sync::atomic::{AtomicPtr, Ordering},
};

const UNLOCKED: usize = 0;
const LOCKED: usize = 1;
const READING: usize = 2;
const QUEUED: usize = 4;
const QUEUE_LOCKED: usize = 8;
const READER_SHIFT: u32 = 16usize.trailing_zeros();
const SINGLE_READER: usize = LOCKED | READING | (1 << READER_SHIFT);

/// Raw rwlock type implemented with lock-free userspace thread queues.
#[derive(Default)]
#[repr(transparent)]
pub struct RawRwLock {
    /// This atomic integer holds the current state of the rwlock instance.
    /// The four least significant bits are used to track the different states of the RwLock.
    ///
    /// # State table:
    ///
    /// LOCKED | READING | QUEUED | QUEUE_LOCKED | Remaining | Description
    ///    0   |    0    |   0    |      0       |     0     | The RwLock is unlocked and in an empty state.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    ///    1   |    0    |   0    |      0       |     0     | One writer holds the lock and there are no waiting threads.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    ///    1   |    0    |   1    |      0       |  *Waiter  | One writer holds the lock and the Remaining bits point to
    ///        |         |        |              |           | the head Waiter node of the waiting-thread queue.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    ///    1   |    0    |   1    |      1       |  *Waiter  | One writer holds the lock and the Remaining bits point to
    ///        |         |        |              |           | the head Waiter node of the waiting thread queue. There is
    ///        |         |        |              |           | also a thread which is updating the waiting-thread queue.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    ///    0   |    0    |   1    |      1       |  *Waiter  | The rwlock is not held, but there are waiting threads.
    ///        |         |        |              |           | There is also one thread which is trying to dequeue and
    ///        |         |        |              |           | wake up a thread from the waiting-thread queue.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    ///    1   |    1    |   0    |      0       |     n     | `n` readers hold the lock and there are no waiting threads.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    ///    1   |    1    |   0    |      1       |  *Waiter  | The lock is held by readers and the Remaining bits point to
    ///        |         |        |              |           | the head Waiter node of the waiting thread queue. The reader
    ///        |         |        |              |           | count has also been moved to the `counter` field on the tail
    ///        |         |        |              |           | node of the waiting-thread queue.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    ///    1   |    1    |   1    |      1       |  *Waiter  | The lock is held by readers and the remaining bits point to
    ///        |         |        |              |           | the head Waiter node of the waiting thread queue. There is
    ///        |         |        |              |           | also a thread which is updating the waiting-thread queue.
    /// -------+---------+--------+--------------+-----------+-------------------------------------------------------------
    pub(super) state: AtomicPtr<Waiter>,
}

impl fmt::Debug for RawRwLock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("RawRwLock { .. }")
    }
}

unsafe impl Send for RawRwLock {}
unsafe impl Sync for RawRwLock {}

unsafe impl lock_api::RawRwLock for RawRwLock {
    type GuardMarker = crate::GuardMarker;

    const INIT: Self = Self {
        state: AtomicPtr::new(invalid_mut(UNLOCKED)),
    };

    #[inline]
    fn is_locked(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        state.address() & LOCKED != 0
    }

    #[inline]
    fn is_locked_exclusive(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        state.address() & (LOCKED | READING) == LOCKED
    }

    #[inline]
    fn try_lock_exclusive(&self) -> bool {
        self.try_lock_exclusive_fast()
    }

    #[inline]
    fn lock_exclusive(&self) {
        if !self.try_lock_exclusive() {
            self.lock_exclusive_slow();
        }
    }

    #[inline]
    unsafe fn unlock_exclusive(&self) {
        self.unlock_exclusive_fast()
    }

    #[inline]
    fn try_lock_shared(&self) -> bool {
        self.try_lock_shared_fast() || self.try_lock_shared_slow()
    }

    #[inline]
    fn lock_shared(&self) {
        if !self.try_lock_shared_fast() {
            self.lock_shared_slow();
        }
    }

    #[inline]
    unsafe fn unlock_shared(&self) {
        if !self.unlock_shared_fast() {
            self.unlock_shared_slow();
        }
    }
}

//  --- X86 Specializations

#[cfg(all(any(target_arch = "x86", target_arch = "x86_64"), not(miri)))]
impl RawRwLock {
    #[inline(always)]
    fn try_lock_exclusive_assuming(&self, _state: *mut Waiter) -> bool {
        use lock_api::RawRwLock as _;
        self.try_lock_exclusive()
    }

    #[inline(always)]
    fn try_lock_exclusive_fast(&self) -> bool {
        // Since 1.65, rustc lowers this to a single `lock bts` on x86, which
        // is often faster for acquiring exclusive ownership than a `lock cmpxchg`
        // as the former wont spuriously fail when a thread is updating the
        // QUEUE_LOCKED bit or adding themselves to the queue.
        self.state
            .fetch_ptr_or(invalid_mut(LOCKED), Ordering::Acquire)
            .address()
            & LOCKED
            != LOCKED
    }

    #[inline(always)]
    unsafe fn unlock_exclusive_fast(&self) {
        // On x86, we unlock the exclusive lock first, then try and wake later.
        // This is faster than using a `lock cmpxchg` loop as it doesn't have
        // to fail and retry from other threads updating QUEUE_LOCKED bit or queueing themselves.
        let locked = ptr::null_mut::<Waiter>().with_address(LOCKED);
        let state = self.state.fetch_sub(locked, Ordering::Release);
        debug_assert_eq!(state.address() & (LOCKED | READING), LOCKED);

        // Only try to unpark if there's no QUEUE_LOCKED owner yet and if there's threads queued.
        if state.address() & (QUEUED | QUEUE_LOCKED) == QUEUED {
            self.try_unpark();
        }
    }

    #[cold]
    unsafe fn unlock_shared_and_unpark(&self) {
        // On x86, we unlock the shared lock first, then try and wake later.
        // This is faster than using a `lock cmpxchg` loop as it doesn't have
        // to fail and retry from other threads updating QUEUE_LOCKED bit or queueing themselves.
        let read_locked = ptr::null_mut::<Waiter>().with_address(LOCKED | READING);
        let state = self.state.fetch_sub(read_locked, Ordering::Release);
        debug_assert_eq!(state.address() & (LOCKED | READING), LOCKED | READING);

        // Only try to unpark if there's no QUEUE_LOCKED owner yet and if there's threads queued.
        if state.address() & (QUEUED | QUEUE_LOCKED) == QUEUED {
            self.try_unpark();
        }
    }

    #[cold]
    fn try_unpark(&self) {
        let mut state = self.state.load(Ordering::Relaxed);

        // Try to grab the QUEUE_LOCKED bit to wake up threads iff:
        // - theres no lock holder, as they can be the ones to do the wake up
        // - there are still threads queued to actually wake up
        // - the QUEUE_LOCKED bit isnt held as someone is already doing wake up
        while state.address() & (LOCKED | QUEUED | QUEUE_LOCKED) == QUEUED {
            let new_state = state.map_address(|addr| addr | QUEUE_LOCKED);
            match self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return unsafe { self.unpark(new_state) },
                Err(e) => state = e,
            }
        }
    }
}

#[cfg(any(miri, not(any(target_arch = "x86", target_arch = "x86_64"))))]
impl RawRwLock {
    #[inline(always)]
    fn try_lock_exclusive_assuming(&self, mut state: *mut Waiter) -> bool {
        while state.address() & LOCKED == 0 {
            match self.state.compare_exchange_weak(
                state,
                state.map_address(|addr| addr | LOCKED),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(e) => state = e,
            }
        }

        false
    }

    #[inline(always)]
    fn try_lock_exclusive_fast(&self) -> bool {
        self.state
            .compare_exchange(
                invalid_mut(UNLOCKED),
                invalid_mut(LOCKED),
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .is_ok()
    }

    #[inline(always)]
    unsafe fn unlock_exclusive_fast(&self) {
        if self
            .state
            .compare_exchange(
                invalid_mut(LOCKED),
                invalid_mut(UNLOCKED),
                Ordering::Release,
                Ordering::Relaxed,
            )
            .is_err()
        {
            self.unlock_and_unpark();
        }
    }

    #[inline(always)]
    unsafe fn unlock_shared_and_unpark(&self) {
        self.unlock_and_unpark()
    }

    #[cold]
    unsafe fn unlock_and_unpark(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            assert_ne!(state.address() & LOCKED, 0);
            assert_ne!(state.address() & QUEUED, 0);

            // Unlocks the rwlock and tries to grab the QUEUE_LOCKED bit for wake up.
            let new_state = state.map_address(|mut addr| {
                addr &= !(LOCKED | READING);
                addr |= QUEUE_LOCKED;
                addr
            });

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            if state.address() & QUEUE_LOCKED == 0 {
                self.unpark(new_state);
            }

            return;
        }
    }
}

//  --- Generic Code

impl RawRwLock {
    #[inline(always)]
    fn try_lock_shared_assuming(
        &self,
        state: *mut Waiter,
    ) -> Option<Result<*mut Waiter, *mut Waiter>> {
        // Returns None if the lock is held by a writer
        if state.address() != UNLOCKED {
            if state.address() & (LOCKED | READING | QUEUED) != (LOCKED | READING) {
                return None;
            }
        }

        // Check for reader count overflow when trying to add a reader.
        // On overflow, readers will queue themselves and be woken up by the last active reader.
        // Overflow is very unlikely though as it requires `usize::MAX >> 4` active readers at once.
        // On a system where `usize` is 64 bits, that's over a quintillion (1 million ^ 5) readers.
        // On a system where `usize` is 32 bits, that's still over 260 million readers.
        if let Some(with_reader) = state.address().checked_add(1 << READER_SHIFT) {
            return Some(self.state.compare_exchange_weak(
                state,
                state.with_address(with_reader | LOCKED | READING),
                Ordering::Acquire,
                Ordering::Relaxed,
            ));
        }

        None
    }

    #[inline(always)]
    fn try_lock_shared_fast(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        let result = self.try_lock_shared_assuming(state);
        matches!(result, Some(Ok(_)))
    }

    #[cold]
    fn try_lock_shared_slow(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            match self.try_lock_shared_assuming(state) {
                None => return false,
                Some(Err(e)) => state = e,
                Some(Ok(_)) => return true,
            }
        }
    }

    #[inline(always)]
    unsafe fn unlock_shared_fast(&self) -> bool {
        // Just go to the slow path if we're not the only reader
        let state = self.state.load(Ordering::Relaxed);
        if state.address() != SINGLE_READER {
            return false;
        }

        self.state
            .compare_exchange(
                state.with_address(SINGLE_READER),
                state.with_address(UNLOCKED),
                Ordering::Release,
                Ordering::Relaxed,
            )
            .is_ok()
    }

    #[cold]
    unsafe fn unlock_shared_slow(&self) {
        // Try to just bump the reader count down when there's no waiting threads.
        // This only works because the Remaining bits still point to the reader count.
        // When threads start waiting, they override these bits with the queue pointer.
        let mut state = self.state.load(Ordering::Relaxed);
        while state.address() & QUEUED == 0 {
            assert_ne!(state.address() & LOCKED, 0);
            assert_ne!(state.address() & READING, 0);
            assert_ne!(state.address() >> READER_SHIFT, 0);

            let mut new_state = state.map_address(|addr| addr - (1 << READER_SHIFT));
            if state.address() == SINGLE_READER {
                new_state = state.with_address(UNLOCKED);
            }

            match self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => state = e,
            }
        }

        // The'ers threads waiting on the RwLock.
        // The reader count has moved to the tail of the queue.
        assert_ne!(state.address() & LOCKED, 0);
        assert_ne!(state.address() & QUEUED, 0);
        assert_ne!(state.address() & READING, 0);

        // Find the tail of the wait queue while also caching it at the current head.
        // As long as the Waiter writes are atomic, this can be soundly racing with
        // other callers to get_and_link_queue() like link_queue_or_unpark() or other readers.
        // Acquire barrier to ensure Waiter queue writes to head happen before we start scanning.
        fence_acquire(&self.state);
        let (_head, tail) = Waiter::get_and_link_queue(state, |_| {});

        // Decrement the reader count which was moved to the tail.
        // Release barrier to ensure RwLock-protected reads/loads happen before we "release" the read lock.
        let readers = tail.as_ref().counter.fetch_sub(1, Ordering::Release);
        assert_ne!(readers, 0);

        // The last reader unsets the LOCKED bit and tries to wake up waiting threads.
        // Acquire barrier synchronizes with the Release to counter above to ensure
        // that the unsetting of the LOCKED bit happens after all the readers reads/loads occur.
        if readers == 1 {
            fence_acquire(&self.state);
            self.unlock_shared_and_unpark();
        }
    }

    #[cold]
    fn lock_exclusive_slow(&self) {
        let is_writer = true;
        let try_lock = |state: *mut Waiter| -> Option<bool> {
            match state.address() & LOCKED {
                0 => Some(self.try_lock_exclusive_assuming(state)),
                _ => None,
            }
        };

        self.lock_common(is_writer, try_lock)
    }

    #[cold]
    fn lock_shared_slow(&self) {
        let is_writer = false;
        let try_lock = |state: *mut Waiter| -> Option<bool> {
            let result = self.try_lock_shared_assuming(state)?;
            Some(result.is_ok())
        };

        self.lock_common(is_writer, try_lock)
    }

    fn lock_common(&self, is_writer: bool, mut try_lock: impl FnMut(*mut Waiter) -> Option<bool>) {
        Waiter::with(|waiter| {
            waiter.waiting_on.set(Some(NonNull::from(self).cast()));
            waiter.flags.set(is_writer as usize);

            let mut spin = SpinWait::default();
            loop {
                let mut state = self.state.load(Ordering::Relaxed);
                loop {
                    // Try to acquire the RwLock.
                    // On failure, spins a bit to decrease cache-line contension.
                    let mut backoff = SpinWait::default();
                    while let Some(was_locked) = try_lock(state) {
                        if was_locked {
                            return;
                        }

                        backoff.yield_now();
                        state = self.state.load(Ordering::Relaxed);
                    }

                    // We can't acquire the RwLock at the moment.
                    // Try to spin for a little in hopes the RwLock is released quickly.
                    // Also don't spin if threads are waiting as we should start waiting too.
                    if (state.address() & QUEUED == 0) && spin.try_yield_now() {
                        state = self.state.load(Ordering::Relaxed);
                        continue;
                    }

                    if unsafe { self.try_queue(&mut state, waiter.as_ref()) } {
                        assert!(waiter.parker.park(None));
                        break;
                    }
                }
            }
        });
    }

    #[cold]
    pub(super) unsafe fn try_requeue(&self, waiter: Pin<&Waiter>) -> bool {
        let is_writer = waiter.flags.get() != 0;
        assert!(is_writer);

        let waiting_on = waiter.waiting_on.get();
        assert_eq!(waiting_on, Some(NonNull::from(self).cast()));

        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Don't requeue if the waiter (which is a writer) could acquire the lock.
            if state.address() & LOCKED == 0 {
                return false;
            }

            // Returns true when this waiter is requeued
            if self.try_queue(&mut state, waiter.as_ref()) {
                return true;
            }
        }
    }

    unsafe fn try_queue(&self, state: &mut *mut Waiter, waiter: Pin<&Waiter>) -> bool {
        // Prepare to push our waiter to the head of the wait queue.
        let waiter_ptr = NonNull::from(&*waiter).as_ptr();
        let mut new_state = waiter_ptr.map_address(|addr| {
            let state_bits = (*state).address() & !Waiter::MASK;
            addr | state_bits | QUEUED
        });

        if (*state).address() & QUEUED == 0 {
            // The first queued waiter will be the tail and it now needs to
            // track the readers since its overriding the remaining state bits.
            let readers = (*state).address() >> READER_SHIFT;
            waiter.counter.store(readers, Ordering::Relaxed);

            // The first queued waiter also sets its `tail` field to itself.
            // This allows `Waiter::get_and_link_queue` to eventually find the queue tail.
            waiter.prev.set(None);
            waiter.next.set(None);
            waiter.tail.set(Some(NonNull::from(&*waiter)));
        } else {
            // The thread which holds the QUEUE_LOCKED bit, or active read-lock holders, will update the queue.
        
