#![allow(dead_code)]

use std::sync::atomic::{AtomicPtr, Ordering};

/// An unsafe atomic pointer. Only supports basic atomic operations
pub struct AtomicConstPtr<T> {
    atomic_ptr: AtomicPtr<T>
}

impl<T> AtomicConstPtr<T> {
    /// Create a new `AtomicConstPtr`
    pub fn new(p: *const T) -> AtomicConstPtr<T> {
        AtomicConstPtr {
            atomic_ptr: AtomicPtr::new(p as *mut T)
        }
    }

    /// Load the value.
    ///
    /// # Failure
    ///
    /// Fails if `order` is `Release` or `AcqRel`.
    #[inline]
    pub fn load(&self, order: Ordering) -> *const T {
        self.atomic_ptr.load(order) as *const T
    }

    /// Store the value.
    ///
    /// # Failure
    ///
    /// Fails if `order` is `Acquire` or `AcqRel`.
    #[inline]
    pub fn store(&self, ptr: *const T, order: Ordering) {
        self.atomic_ptr.store(ptr as *mut T, order)
    }

    /// Store a value, returning the old value
    #[inline]
    pub fn swap(&self, ptr: *const T, order: Ordering) -> *const T {
        self.atomic_ptr.swap(ptr as *mut T, order) as *const T
    }

    /// If the current value is the same as expected, store a new value
    ///
    /// Compare the current value with `old`; if they are the same then
    /// replace the current value with `new`. Return the previous value.
    /// If the return value is equal to `old` then the value was updated.
    #[inline]
    pub fn compare_and_swap(&self, old: *const T, new: *const T, order: Ordering) -> *const T {
        self.atomic_ptr.compare_and_swap(old as *mut T, new as *mut T, order) as *const T
    }
}
