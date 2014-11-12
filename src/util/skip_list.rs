#![allow(dead_code)]

use arena::TypedArena;
use std::{fmt, ptr, rand};
use std::kinds::marker;
use std::sync::atomic::{AcqRel, Acquire, Release};
use std::sync::Mutex;

use super::atomic::AtomicConstPtr;

/// A concurrent, lock-free, linearizable, insert-only, sorted map.
///
/// References:
///  * Herlihy, Maurice, et al. [A provably correct scalable concurrent skip list.]
///    (http://people.csail.mit.edu/shanir/publications/OPODIS2006-BA.pdf).
///  * [leveldb](https://github.com/google/leveldb/blob/master/db/skiplist.h)
///
// Insert isn't really lock-free without a lock-free arena, but lets ignore that, shall we?
pub struct SkipList<K, V> {
    start: *const Node<K, V>,
    end: *const Node<K, V>,
    arena: Mutex<TypedArena<Node<K, V>>>,
    max_height: u8,
    branch_factor: u8
}

impl <K: Ord + Sync + Send, V: Sync + Send> SkipList<K, V> {

    /// Creates a new skip list with the given maximum height and branch factor.
    pub fn new() -> SkipList<K, V> {
        SkipList::with_parameters(9, 3)
    }

    /// Creates a new skip list with the given maximum height and branch factor.
    pub fn with_parameters(max_height: u8, branch_factor: u8) -> SkipList<K, V> {
        assert!(max_height > 0, "max_height must be greater than 0.");
        assert!(branch_factor > 1, "branch_factor must be greater than 0.");

        let arena = TypedArena::new();
        let end: *const Node<K, V> = arena.alloc(EndSentinel::<K, V>) as *mut _ as *const _;
        let succs = Vec::from_fn(max_height as uint, |_| AtomicConstPtr::new(end));
        let start: *const Node<K, V> =
            arena.alloc(StartSentinel { succs: succs }) as *mut _ as *const _;

        SkipList {
            start: start,
            end: end,
            arena: Mutex::new(arena),
            max_height: max_height,
            branch_factor: branch_factor,
        }
    }

    /// Generates a new random height based on this skip list's maximum height and branch factor.
    fn random_height(&self) -> uint {
        let mut level = 1;
        while level < self.max_height && rand::random::<u8>() % self.branch_factor == 0 {
            level += 1;
        }
        debug_assert!(level > 0);
        debug_assert!(level <= self.max_height);
        level as uint
    }

    /// Gets the predecessor nodes to the key at every height.
    ///
    /// For example, for a skip list which contains 7 keys (`a` - `g`), a max height of 4,
    /// and with the following heights:
    ///
    /// ```ascii
    ///  x<-                     x
    ///  x<-                     x
    ///  x       x<-     x       x
    ///  x   x   x   x<- x   x   x
    ///  a   b   c   d   e   f   g
    ///  ```
    ///
    /// `get_pred(d)` returns `[d, c, a, a]`.
    ///
    /// `None` is returned if this list already contains an entry for `key`.
    fn get_preds(&self, key: &K) -> Option<Vec<&Node<K, V>>> {
        let max_height = self.max_height as uint;
        let mut preds = Vec::<&Node<K, V>>::with_capacity(max_height);
        let mut pred = self.start();
        for height in range(0, max_height).rev() {

            let mut curr = pred.succ(height);

            loop {
                match curr.cmp_to_key(key) {
                    Less => {
                        // The `curr` node is less than the desired key; continue to the next node
                        // at this height.
                        pred = curr;
                        curr = pred.succ(height);
                    },
                    Equal => return None,
                    Greater => {
                        // The `curr` node is greater than the desired key; add `pred` to the list
                        // of predecessor nodes and continue to the next height.
                        preds.push(pred);
                        break;
                    },
                }
            }
        }
        Some(preds)
    }

    /// Returns the node in the skip list for the given key wrapped in `Ok`, or the next-previous
    /// node wrapped in `Err` if the key does not exist in this skip list.
    fn get_or_prev(&self, key: &K) -> Result<&Node<K, V>, &Node<K, V>> {
        let max_height = self.max_height as uint;
        let mut pred = self.start();
        for height in range(0, max_height).rev() {
            let mut curr = pred.succ(height);
            loop {
                match curr.cmp_to_key(key) {
                    Less => {
                        // The `curr` node is less than the desired key; continue to the next node
                        // at this height.
                        pred = curr;
                        curr = pred.succ(height);
                    },
                    Equal => return Ok(curr),
                    Greater => {
                        // The `curr` node is greater than the desired key; continue to the next
                        // height.
                        break;
                    },
                }
            }
        }
        Err(pred)
    }

    /// Inserts a key-value pair into the skip list. An existing value for a key is *not* replaced
    /// by the new value. Returns true if the key did not already exist in the map.
    pub fn insert(&self, key: K, val: V) -> bool {
        let top_height = self.random_height();

        let mut pred_nodes: Vec<&Node<K, V>> = match self.get_preds(&key) {
            Some(pred_nodes) => pred_nodes,
            None => return false,
        };

        // Terrible borrow-check hack to get around the limitation that references can not escape
        // the lexical scope of a lock borrow. This is safe, because the lock is only needed to
        // insert an element into the arena; once a reference is returned the element can be
        // safely used without holding the lock.
        let entry: &Node<K, V> = unsafe {
            &*(self.arena.lock().alloc(
                Entry { key: key,
                        val: val,
                        succs: Vec::from_fn(top_height, |_| AtomicConstPtr::new(ptr::null())),
                }) as *mut _ as *const _)
        };

        // Insert the new entry into the skip list at each height up to `max_height`.
        for (height, &pred) in pred_nodes.iter_mut().rev().take(top_height).enumerate() {
            let mut pred = pred;
            loop {
                let succ = pred.succ(height);
                match entry.cmp(succ) {
                    Less => {
                        // The new entry falls between `pred` and `succ`. Attempt to insert it here.
                        entry.set_succ(height, succ);
                        if pred.compare_and_swap_succ(height, succ, entry) {
                            // Success; the `pred` node has successfully been updated to point to
                            // `entry` at this height.
                            break;
                        } else {
                            // Failure; this thread has been beaten in a race with another thread
                            // to insert between `pred` and `succ`. Retry.
                            continue;
                        }
                    },
                    Equal => {
                        assert!(height == 0, "Concurrent insert conflict at height {}.", height);
                        return false
                    },
                    Greater => {
                        // The new entry is greater than `succ`; continue to the next slot and
                        // attempt again.
                        pred = succ;
                        continue;
                    },
                };
            }
        };
        true
    }

    /// Gets the value for the given key if it exists in this skip list.
    pub fn get(&self, key: &K) -> Option<&V> {
        match self.get_or_prev(key) {
            Ok(node) => Some(node.val()),
            _ => None
        }
    }

    /// Gets an iterator over the sorted elements of this skip list.
    ///
    /// The returned iterator may include elements inserted by concurrent writers.
    pub fn iter<'a>(&'a self) -> Entries<'a, K, V> {
        Entries { start: self.start().next(),
                  end: self.end,
                  marker: marker::ContravariantLifetime::<'a> }
    }

    /// Gets an iterator over the sorted elements of this skip list beginning with the given `key`,
    /// inclusive.
    ///
    /// The returned iterator may include elements inserted by concurrent writers.
    pub fn iter_from<'a>(&'a self, key: &K) -> Entries<'a, K, V> {
        let start: &Node<K, V> = match self.get_or_prev(key) {
            Ok(start) => start,
            Err(prev) => {

                // The key does not exist in this skip list, so we get the next greatest entry
                // with `prev.next()`.
                //
                // However, If a concurrent writer writes an entry with a key which falls between
                // `prev.key()` and `key` at this time, then `prev.next()` will erroneously return
                // that entry. To guard against this, continue along the chain of entries until
                // a node with a key >= `key` is found.

                let mut prev = prev.next();
                while prev.cmp_to_key(key) == Less { prev = prev.next() }
                prev
            }
        };

        Entries { start: start, end: self.end, marker: marker::ContravariantLifetime::<'a> }
    }

    /// Gets a reference to the start node.
    fn start<'a>(&'a self) -> &'a Node<K, V> {
        // This is safe because a skip list's start pointer must be valid for its entire lifetime
        unsafe { &*self.start }
    }

    /// Gets a reference to the end node.
    fn end<'a>(&'a self) -> &'a Node<K, V> {
        // This is safe because a skip list's end pointer must be valid for its entire lifetime
        unsafe { &*self.end }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//// Node
///////////////////////////////////////////////////////////////////////////////////////////////////

pub enum Node<K, V> {
    StartSentinel {
        succs: Vec<AtomicConstPtr<Node<K, V>>>,
    },
    Entry {
        key: K,
        val: V,
        succs: Vec<AtomicConstPtr<Node<K, V>>>,
    },
    EndSentinel
}

impl <K: Sync + Send, V: Sync + Send> Node<K, V> {

    /// Gets this node's vector of successor pointers.
    ///
    /// # Panics
    ///
    /// This method panics if this node is an end sentinel.
    fn succs(&self) -> &Vec<AtomicConstPtr<Node<K, V>>> {
        match *self {
            StartSentinel { ref succs, .. }
            |       Entry { ref succs, .. } => succs,
            EndSentinel => panic!("Illegal argument: Node::succs may not be called on an end sentinel.")
        }
    }

    /// Gets a reference to the node's successor at the given height.
    ///
    /// # Panics
    ///
    /// This method panics if this node does not have a successor for the height, or if this node
    /// is an end sentinel.
    fn succ(&self, height: uint) -> &Node<K, V> {
        // safe since all nodes in the skip list have valid next pointers which point to nodes with
        // the same lifetime as the skip list.
        match *self {
            StartSentinel { ref succs, .. }
            |       Entry { ref succs, .. } => {
                unsafe { &*succs[height].load(Acquire) }
            },
            EndSentinel => panic!("Illegal argument: Node::succ may not be called on an end sentinel.")
        }
    }

    /// Sets this node's successor at the given height to the given node.
    ///
    /// # Panics
    ///
    /// This method panics if this node does not have a successor for the height, or if this node
    /// is an end sentinel.
    fn set_succ(&self, height: uint, node: *const Node<K, V>) {
        match *self {
            StartSentinel { ref succs, .. }
            |       Entry { ref succs, .. } => succs[height].store(node, Release),
            EndSentinel => panic!("Illegal argument: Node::set_succ may not be called on an end sentinel.")
        }
    }

    /// Conditionally sets this node's successor at the given height if the previous successor is
    /// `old`.  Returns `true` if the set is successful.
    ///
    /// # Panics
    ///
    /// This method panics if this node does not have a successor for the height, or if this node
    /// is an end sentinel.
    fn compare_and_swap_succ(&self,
                             height: uint,
                             old: *const Node<K, V>,
                             new: *const Node<K, V>)
                             -> bool {
        match *self {
            StartSentinel { ref succs, .. }
            |       Entry { ref succs, .. } => succs[height].compare_and_swap(old, new, AcqRel) == old,
            EndSentinel => panic!("Illegal argument: Node::compare_and_swap_succ may not be called on an end sentinel.")
        }
    }

    /// Gets a reference to the next node after this node.
    ///
    /// # Panics
    ///
    /// This method panics if this node is an end sentinel.
    fn next(&self) -> &Node<K, V> {
        match *self {
            // safe since every node is guaranteed to have at least one successor, and since all
            // in the skip list have valid next pointers which point to nodes with the same
            // lifetime as the skip list.
            StartSentinel { ref succs, .. }
            |       Entry { ref succs, .. } => unsafe { &*succs[].unsafe_get(0).load(Acquire) },
            EndSentinel => panic!("Illegal argument: Node::next may not be called on an end sentinel.")
        }
    }

    /// Gets this node's key.
    ///
    /// # Panics
    ///
    /// This method panics if this node is a start sentinel or an end sentinel.
    fn key(&self) -> &K {
        match *self {
            StartSentinel { .. } => panic!("Illegal argument: Node::key may not be called on a start sentinel."),
            Entry { ref key, .. } => key,
            EndSentinel => panic!("Illegal argument: Node::key may not be called on an end sentinel."),
        }
    }

    /// Get this node's value.
    ///
    /// # Panics
    ///
    /// This method panics if this node is a start sentinel or an end sentinel.
    fn val(&self) -> &V {
        match *self {
            StartSentinel { .. } => panic!("Illegal argument: Node::val may not be called on a start sentinel."),
            Entry { ref val, .. } => val,
            EndSentinel => panic!("Illegal argument: Node::val may not be called on an end sentinel."),
        }
    }
}

impl <K: Ord, V> Node<K, V> {

    /// Compares this node to a given key.
    fn cmp_to_key(&self, key: &K) -> Ordering {
        match *self {
            Entry { key: ref self_key, .. } => self_key.cmp(key),
            EndSentinel => Greater,
            StartSentinel { .. } => Less,
        }
    }
}

/// Equality between `Node`s is defined only by the keys.
impl <K: PartialEq, V> PartialEq for Node<K, V> {
    fn eq(&self, other: &Node<K, V>) -> bool {
        match (self, other) {
            (&StartSentinel { .. }, &StartSentinel { .. }) => true,
            (&EndSentinel, &EndSentinel) => true,
            (&Entry { key: ref self_key, .. }, &Entry { key: ref other_key, .. }) => self_key == other_key,
            _ => false
        }
    }
}

/// Equality between `Node`s is defined only by the keys.
impl <K: Eq, V> Eq for Node<K, V> { }

/// Ordering between `Node`s is defined only by the keys.
impl <K: PartialOrd, V> PartialOrd for Node<K, V> {
    fn partial_cmp(&self, other: &Node<K, V>) -> Option<Ordering> {
        match (self, other) {
            (&StartSentinel { .. }, &StartSentinel { .. }) => Some(Equal),
            (&StartSentinel { .. }, _) => Some(Less),
            (_, &StartSentinel { .. }) => Some(Greater),
            (&EndSentinel, &EndSentinel) => Some(Equal),
            (&EndSentinel, _) => Some(Greater),
            (_, &EndSentinel) => Some(Less),
            (&Entry { key: ref self_key, .. }, &Entry { key: ref other_key, .. }) => self_key.partial_cmp(other_key)
        }
    }
}

/// Ordering between `Node`s is defined only by the keys.
impl <K: Ord, V> Ord for Node<K, V> {
    fn cmp(&self, other: &Node<K, V>) -> Ordering {
        match (self, other) {
            (&StartSentinel { .. }, &StartSentinel { .. }) => Equal,
            (&StartSentinel { .. }, _) => Less,
            (_, &StartSentinel { .. }) => Greater,
            (&EndSentinel, &EndSentinel) => Equal,
            (&EndSentinel, _) => Greater,
            (_, &EndSentinel) => Less,
            (&Entry { key: ref self_key, .. }, &Entry { key: ref other_key, .. }) => self_key.cmp(other_key)
        }
    }
}

impl <K: fmt::Show, V: fmt::Show> fmt::Show for Node<K, V> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            StartSentinel { ref succs, .. } =>
                write!(formatter, "StartSentinel {{ height: {} }}", succs.len()),
            EndSentinel => write!(formatter, "EndSentinel"),
            Entry { ref key, ref val, ref succs, .. } =>
                write!(formatter, "Entry {{ key: {}, val: {}, height: {} }}", key, val, succs.len()),
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//// Iterator
///////////////////////////////////////////////////////////////////////////////////////////////////

struct Entries<'a, K, V> {
    /// The first entry to iterate over, inclusive.
    start: *const Node<K, V>,
    /// The last entry to iterate over, exclusive.
    end: *const Node<K, V>,
    marker: marker::ContravariantLifetime<'a>,
}

impl<'a, K, V> Entries<'a, K, V> {

    /// Gets a reference to the start node.
    ///
    /// This method is safe, because that start pointer must be valid for the lifetime of a skip
    /// list iterator.
    fn start(&self) -> &'a Node<K, V> {
        // This is safe because a skip list iterator's start pointer must be valid for its entire
        // lifetime.
        unsafe { &*self.start }
    }

    /// Gets a reference to the end node.
    ///
    /// This method is safe, because that start pointer must be valid for the lifetime of a skip
    /// list iterator.
    fn end(&self) -> &'a Node<K, V> {
        // This is safe because a skip list iterator's end pointer must be valid for its entire
        // lifetime.
        unsafe { &*self.end }
    }
}

impl<'a, K: Sync + Send, V: Sync + Send> Iterator<(&'a K, &'a V)> for Entries<'a, K, V> {

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.start == self.end {
            None
        } else {
            let next = Some((self.start().key(), self.start().val()));
            self.start = self.start().next() as *const _;
            next
        }
    }
}

#[cfg(test)]
mod test {

    #[phase(plugin)]
    extern crate quickcheck_macros;
    extern crate quickcheck;

    use std::collections::TreeMap;
    use std::sync::Barrier;
    use std::sync::Arc;
    use std::rand;
    use std::rand::Rand;

    use quickcheck::TestResult;

    use super::*;

    /// Checks that a given skip list is the valid outcome of inserting a sequence of elements into
    /// an empty skip list in order.
    fn verify_map_properties<K: Clone + Rand + Send + Sync + Ord, V: Clone + Send + Sync + Ord>(
        skip_list: &SkipList<K, V>,
        elements: Vec<(K, V)>)
        -> bool {

        let mut tree_map = TreeMap::new();
        // Insert the elements backwards into the tree map, because, unlike a skip list, the tree
        // map will overwrite old values with newer values.
        for &(ref k, ref v) in elements.iter().rev() {
            tree_map.insert(k.clone(), v.clone());
        }

        // `get` on the skip list and tree map should produce the same answer for any key
        for &(ref k, _) in elements.iter() {
            if skip_list.get(k) != tree_map.get(k) {
                return false
            }
        }

        for _ in range(0u, 100) {
            let key = rand::random();
            if skip_list.get(&key) != tree_map.get(&key) {
                return false
            }
        }

        // The skip list and tree map iterators should have the same elements at every position
        for ((ref k1, ref v1), (ref k2, ref v2)) in skip_list.iter().zip(tree_map.iter()) {
            if k1 != k2 || v1 != v2 {
                return false;
            }
        }

        if skip_list.iter().count() != tree_map.len() {
            return false
        }

        // The skip list and tree map lower bound iterators should have the same elements at every position
        for &(ref from_key, _) in elements.iter() {
            if skip_list.iter_from(from_key).next() != tree_map.lower_bound(from_key).next() {
                return false;
            }
        }

        true
    }

    /// Checks that a given skip list is a valid outcome of inserting a sequence of elements into
    /// an empty skip list in undetermined order.
    fn verify_map_properties_concurrent<K: Clone + Rand + Send + Sync + Ord, V: Clone + Send + Sync + Ord>(
        skip_list: &SkipList<K, V>,
        mut elements: Vec<(K, V)>)
        -> bool {

        // Check that there is an entry in the skip list for each key in the input elements
        for &(ref k, _) in elements.iter() {
            if skip_list.get(k).is_none() {
                return false
            }
        }

        // Check that each element in the skip list is in the input elements.
        let sorted_elements = elements.as_mut_slice();
        sorted_elements.sort();
        for (k, v) in skip_list.iter() {
            let element = (k.clone(), v.clone());
            if sorted_elements.binary_search(|probe| probe.cmp(&element)).found().is_none() {
                return false
            }
        }

        let elements =
            skip_list.iter().map(|(k, v)| (k.clone(), v.clone())).collect::<Vec<(K, V)>>();

        verify_map_properties(skip_list, elements)
    }

    #[quickcheck]
    fn check_map_properties(elements: Vec<(int, String)>,
                            max_height: u8, branch_factor: u8) -> TestResult {
        if max_height < 1 || branch_factor < 2 { return TestResult::discard() };

        let skip_list = SkipList::with_parameters(max_height, branch_factor);

        for &(ref k, ref v) in elements.iter() {
            skip_list.insert(k.clone(), v.clone());
        }

        TestResult::from_bool(verify_map_properties(&skip_list, elements))
    }

    #[quickcheck]
    fn check_concurrent_access(elements: Vec<Vec<(int, String)>>,
                               max_height: u8,
                               branch_factor: u8) -> TestResult {
        if max_height < 1 || branch_factor < 2 { return TestResult::discard() };
        let skip_list = Arc::new(SkipList::with_parameters(max_height, branch_factor));
        let start_barrier = Arc::new(Barrier::new(elements.len() * 2));
        let end_barrier = Arc::new(Barrier::new(elements.len() * 2 + 1));

        // Concurrent writers
        for vec in elements.clone().into_iter() {
            let start = start_barrier.clone();
            let end = end_barrier.clone();
            let skip_list = skip_list.clone();
            spawn(proc() {
                start.wait();
                for (k, v) in vec.into_iter() {
                    skip_list.insert(k, v);
                }
                end.wait();
            });
        }

        // Concurrent readers
        for vec in elements.clone().into_iter() {
            let start = start_barrier.clone();
            let end = end_barrier.clone();
            let skip_list = skip_list.clone();
            spawn(proc() {
                start.wait();
                for &(ref k, _) in vec.iter() {
                    skip_list.get(k);
                }
                end.wait();
            });
        }

        end_barrier.wait();

        let all_elements =
            elements.into_iter().flat_map(|v| v.into_iter()).collect::<Vec<(int, String)>>();
        TestResult::from_bool(verify_map_properties_concurrent(&*skip_list, all_elements))
    }

    #[test]
    fn get_empty() {
        let m = SkipList::<int, int>::new();
        assert!(m.get(&5) == None);
    }

    #[test]
    fn get_not_found() {
        let m = SkipList::new();
        assert!(m.insert(1i, 2i));
        assert!(m.insert(5i, 3i));
        assert!(m.insert(9i, 3i));
        assert_eq!(m.get(&2), None);
    }

    #[test]
    fn insert_replace() {
        let m = SkipList::new();
        assert!(m.insert(5i, 2i));
        assert!(m.insert(2, 9));
        assert!(!m.insert(2, 11));
        assert_eq!(m.get(&2).unwrap(), &9);
    }

    #[test]
    fn test_insert() {
        let skip_list = SkipList::new();
        skip_list.insert(1i, 1i);
        skip_list.insert(5, 5);
        skip_list.insert(3, 3);
        skip_list.insert(2, 2);
        skip_list.insert(4, 4);
    }

    #[test]
    fn test_get() {
        let skip_list = SkipList::new();
        skip_list.insert(1i, 1i);
        skip_list.insert(5, 5);
        skip_list.insert(3, 3);
        skip_list.insert(2, 2);
        skip_list.insert(4, 4);
        assert_eq!(Some(&1), skip_list.get(&1));
        assert_eq!(Some(&2), skip_list.get(&2));
        assert_eq!(Some(&3), skip_list.get(&3));
        assert_eq!(Some(&4), skip_list.get(&4));
        assert_eq!(Some(&5), skip_list.get(&5));
    }

    #[test]
    fn test_iter() {
        let m = SkipList::new();

        assert!(m.insert(3i, 6i));
        assert!(m.insert(0, 0));
        assert!(m.insert(4, 8));
        assert!(m.insert(2, 4));
        assert!(m.insert(1, 2));

        let mut n = 0;
        for (k, v) in m.iter() {
            assert_eq!(*k, n);
            assert_eq!(*v, n * 2);
            n += 1;
        }
        assert_eq!(n, 5);
    }

    #[test]
    fn test_iter_from() {
        let m = SkipList::new();

        assert!(m.insert(3i, 6i));
        assert!(m.insert(0, 0));
        assert!(m.insert(4, 8));
        assert!(m.insert(2, 4));
        assert!(m.insert(1, 2));

        let mut n = 2;
        for (k, v) in m.iter_from(&2) {
            assert_eq!(*k, n);
            assert_eq!(*v, n * 2);
            n += 1;
        }
        assert_eq!(n, 5);
    }

    #[test]
    #[should_fail]
    fn test_0_max_height() {
        SkipList::<int, int>::with_parameters(0, 2);
    }

    #[test]
    #[should_fail]
    fn test_0_branch_factor() {
        SkipList::<int, int>::with_parameters(12, 0);
    }

    #[test]
    #[should_fail]
    fn test_1_branch_factor() {
        SkipList::<int, int>::with_parameters(12, 1);
    }
}

#[cfg(test)]
mod bench {
    extern crate test;
    use std::rand::{weak_rng, Rng};
    use std::rand;
    use test::{Bencher, black_box};
    use std::collections::BTreeMap;

    use super::SkipList;

    pub fn find_rand_n<M, T>(n: uint, map: &mut M, b: &mut Bencher,
                             insert: |&mut M, uint|,
                             find: |&M, uint| -> T) {
        // setup
        let mut rng = rand::weak_rng();
        let mut keys = Vec::from_fn(n, |_| rng.gen::<uint>() % n);

        for k in keys.iter() {
            insert(map, *k);
        }

        rng.shuffle(keys.as_mut_slice());

        // measure
        let mut i = 0;
        b.iter(|| {
            let t = find(map, keys[i]);
            i = (i + 1) % n;
            t
        })
    }

    pub fn find_seq_n<M, T>(n: uint, map: &mut M, b: &mut Bencher,
                            insert: |&mut M, uint|,
                            find: |&M, uint| -> T) {
        // setup
        for i in range(0u, n) {
            insert(map, i);
        }

        // measure
        let mut i = 0;
        b.iter(|| {
            let x = find(map, i);
            i = (i + 1) % n;
            x
        })
    }

    fn btree_iter_n(n: uint, b: &mut Bencher) {
        let mut map = BTreeMap::<uint, uint>::new();
        let mut rng = weak_rng();
        let keys = Vec::from_fn(n, |_| rng.gen::<uint>() % n);

        for k in keys.iter() {
            map.insert(*k, 1);
        }

        b.iter(|| {
            for entry in map.iter() {
                black_box(entry);
            }
        });
    }

    fn skip_list_iter_n(n: uint, b: &mut Bencher) {
        let map = SkipList::<uint, uint>::new();
        let mut rng = weak_rng();
        let keys = Vec::from_fn(n, |_| rng.gen::<uint>() % n);

        for k in keys.iter() {
            map.insert(*k, 1);
        }

        b.iter(|| {
            for entry in map.iter() {
                black_box(entry);
            }
        });
    }

    // Find rand
    #[bench]
    pub fn get_rand_100_skip_list(b: &mut Bencher) {
        let mut m : SkipList<uint,uint> = SkipList::new();
        find_rand_n(100, &mut m, b,
                    |m, i| { m.insert(i, 1); },
                    |m, i| { m.get(&i); });
    }

    #[bench]
    pub fn get_rand_10_000_skip_list(b: &mut Bencher) {
        let mut m : SkipList<uint,uint> = SkipList::new();
        find_rand_n(10_000, &mut m, b,
                    |m, i| { m.insert(i, 1); },
                    |m, i| { m.get(&i); });
    }

    // Find seq
    #[bench]
    pub fn get_seq_100_skip_list(b: &mut Bencher) {
        let mut m : SkipList<uint,uint> = SkipList::new();
        find_seq_n(100, &mut m, b,
                   |m, i| { m.insert(i, 1); },
                   |m, i| { m.get(&i); });
    }

    #[bench]
    pub fn get_seq_10_000_skip_list(b: &mut Bencher) {
        let mut m : SkipList<uint,uint> = SkipList::new();
        find_seq_n(10_000, &mut m, b,
                   |m, i| { m.insert(i, 1); },
                   |m, i| { m.get(&i); });
    }

    // iter
    #[bench]
    pub fn iter_100_skip_list(b: &mut Bencher) {
        skip_list_iter_n(100, b);
    }

    #[bench]
    pub fn iter_10_000_skip_list(b: &mut Bencher) {
        skip_list_iter_n(10_000, b);
    }

    // Find rand
    #[bench]
    pub fn get_rand_100_btree(b: &mut Bencher) {
        let mut m : BTreeMap<uint,uint> = BTreeMap::new();
        find_rand_n(100, &mut m, b,
                    |m, i| { m.insert(i, 1); },
                    |m, i| { m.get(&i); });
    }

    #[bench]
    pub fn get_rand_10_000_btree(b: &mut Bencher) {
        let mut m : BTreeMap<uint,uint> = BTreeMap::new();
        find_rand_n(10_000, &mut m, b,
                    |m, i| { m.insert(i, 1); },
                    |m, i| { m.get(&i); });
    }

    // Find seq
    #[bench]
    pub fn get_seq_100_btree(b: &mut Bencher) {
        let mut m : BTreeMap<uint,uint> = BTreeMap::new();
        find_seq_n(100, &mut m, b,
                   |m, i| { m.insert(i, 1); },
                   |m, i| { m.get(&i); });
    }

    #[bench]
    pub fn get_seq_10_000_btree(b: &mut Bencher) {
        let mut m : BTreeMap<uint,uint> = BTreeMap::new();
        find_seq_n(10_000, &mut m, b,
                   |m, i| { m.insert(i, 1); },
                   |m, i| { m.get(&i); });
    }

    // iter
    #[bench]
    pub fn iter_100_btree(b: &mut Bencher) {
        btree_iter_n(100, b);
    }

    #[bench]
    pub fn iter_10_000_btree(b: &mut Bencher) {
        btree_iter_n(10_000, b);
    }
}
