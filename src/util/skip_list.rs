#![allow(dead_code)]

use arena::TypedArena;
use std::{fmt, ptr, rand};
use std::kinds::marker;
use std::sync::atomic::{AcqRel, Acquire, Release};
use std::sync::Mutex;

use super::atomic::AtomicConstPtr;

const MAX_HEIGHT: uint = 7;

/// A concurrent, lock-free, linearizable, insert-only, sorted set.
///
/// References:
///  * Herlihy, Maurice, et al. [A provably correct scalable concurrent skip list.]
///    (http://people.csail.mit.edu/shanir/publications/OPODIS2006-BA.pdf).
///  * [leveldb](https://github.com/google/leveldb/blob/master/db/skiplist.h)
///
// Insert isn't really lock-free without a lock-free arena, but lets ignore that, shall we?
pub struct SkipList<T> {
    start: *const Node<T>,
    end: *const Node<T>,
    arena: Mutex<TypedArena<Node<T>>>,
    branch_factor: u8
}

impl <T: Ord + Sync + Send> SkipList<T> {

    /// Creates a new skip list with the given maximum height and branch factor.
    pub fn new() -> SkipList<T> {
        SkipList::with_parameters(4)
    }

    /// Creates a new skip list with the given maximum height and branch factor.
    pub fn with_parameters(branch_factor: u8) -> SkipList<T> {
        assert!(branch_factor > 1, "branch_factor must be greater than 0.");

        let arena = TypedArena::new();
        let end: *const Node<T> = arena.alloc(EndSentinel::<T>) as *mut _ as *const _;
        let start: *const Node<T> =
            arena.alloc(StartSentinel { succs: SkipList::new_succ_array(end) }) as *mut _ as *const _;

        SkipList {
            start: start,
            end: end,
            arena: Mutex::new(arena),
            branch_factor: branch_factor,
        }
    }

    /// Generates a new random height based on the skip list's maximum height and branch factor.
    fn random_height(&self) -> uint {
        let mut level = 1;
        while level < MAX_HEIGHT && rand::random::<u8>() % self.branch_factor == 0 {
            level += 1;
        }
        debug_assert!(level > 0);
        debug_assert!(level <= MAX_HEIGHT);
        level as uint
    }

    /// Gets the predecessor nodes to the element at every height.
    ///
    /// For example, for a skip list which contains 6 elements, `{a, b, c, d, f, g}` with the
    /// following heights:
    ///
    /// ```ascii
    ///  x<-                 x
    ///  x<-                 x
    ///  x       x<-         x
    ///  x   x   x   x<- x   x
    ///  a   b   c   d   f   g
    ///  ```
    ///
    /// `get_pred(e)` returns `Some([d, c, a, a])`.
    /// `get_pred(f)` returns `None`.
    ///
    /// `None` is returned if the skip list already contains `elem`.
    fn get_preds(&self, elem: &T) -> Option<Vec<&Node<T>>> {
        let mut preds = Vec::<&Node<T>>::with_capacity(MAX_HEIGHT);
        let mut pred = self.start();
        for height in range(0, MAX_HEIGHT).rev() {

            let mut curr = pred.succ(height);

            loop {
                match curr.cmp_elem(elem) {
                    Less => {
                        // The `curr` node is less than the desired element; continue to the next
                        // node at this height.
                        pred = curr;
                        curr = pred.succ(height);
                    },
                    Equal => return None,
                    Greater => {
                        // The `curr` node is greater than the desired element; add `pred` to the
                        // list of predecessor nodes and continue to the next height.
                        preds.push(pred);
                        break;
                    },
                }
            }
        }
        Some(preds)
    }

    /// Returns the node in the skip list for the given element wrapped in `Ok`, or the
    /// next-previous node wrapped in `Err` if the element does not exist in the skip list.
    fn get_or_prev(&self, elem: &T) -> Result<&Node<T>, &Node<T>> {
        let mut pred = self.start();
        for height in range(0, MAX_HEIGHT).rev() {
            let mut curr = pred.succ(height);
            loop {
                match curr.cmp_elem(elem) {
                    Less => {
                        // The `curr` node is less than the desired element; continue to the next
                        // node at this height.
                        pred = curr;
                        curr = pred.succ(height);
                    },
                    Equal => return Ok(curr),
                    Greater => {
                        // The `curr` node is greater than the desired element; continue to the next
                        // height.
                        break;
                    },
                }
            }
        }
        Err(pred)
    }

    /// Adds an element to the skip list. Returns `true` if the element was not already present in
    /// the skip list.
    pub fn insert(&self, elem: T) -> bool {
        let top_height = self.random_height();

        let mut pred_nodes: Vec<&Node<T>> = match self.get_preds(&elem) {
            Some(pred_nodes) => pred_nodes,
            None => return false,
        };

        // Terrible borrow-check hack to get around the limitation that references can not escape
        // the lexical scope of a lock borrow. This is safe, because the lock is only needed to
        // insert an element into the arena; once a reference is returned the element can be
        // safely used without holding the lock.
        let elem: &Node<T> = unsafe {
            &*(self.arena.lock().alloc(
                Element { elem: elem,
                          succs: SkipList::new_succ_array(ptr::null()),
                }) as *mut _ as *const _)
        };

        // Insert the new element into the skip list at each height up to `max_height`.
        for (height, &pred) in pred_nodes.iter_mut().rev().take(top_height).enumerate() {
            let mut pred = pred;
            loop {
                let succ = pred.succ(height);
                match elem.cmp(succ) {
                    Less => {
                        // The new element falls between `pred` and `succ`. Attempt to insert it.
                        elem.set_succ(height, succ);
                        if pred.compare_and_swap_succ(height, succ, elem) {
                            // Success; the `pred` node has successfully been updated to point to
                            // the new element at this height.
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
                        // The new element is greater than `succ`; continue to the next slot and
                        // attempt again.
                        pred = succ;
                        continue;
                    },
                };
            }
        };
        true
    }

    /// Gets an iterator over the sorted elements of this skip list beginning with the given
    /// element, inclusive.
    ///
    /// The returned iterator may include elements inserted by concurrent writers.
    pub fn iter_from<'a>(&'a self, elem: &T) -> Items<'a, T> {
        let start: &Node<T> = match self.get_or_prev(elem) {
            Ok(start) => start,
            Err(prev) => {

                // The element does not exist in this skip list, so we get the next greatest entry
                // with `prev.next()`.
                //
                // However, If there is a concurrent insert of an element which falls between
                // `prev.key()` and `key` at this time, then `prev.next()` will erroneously return
                // that element. To guard against this, continue along the chain of elements until
                // a node >= `elem` is found.

                let mut prev = prev.next();
                while prev.cmp_elem(elem) == Less { prev = prev.next() }
                prev
            }
        };

        Items { inclusive: false,
                start: start,
                end: self.end,
                marker: marker::ContravariantLifetime::<'a> }
    }

    /// Gets a reference to the start node.
    fn start<'a>(&'a self) -> &'a Node<T> {
        // This is safe because a skip list's start pointer must be valid for its entire lifetime
        unsafe { &*self.start }
    }

    /// Gets a reference to the end node.
    fn end<'a>(&'a self) -> &'a Node<T> {
        // This is safe because a skip list's end pointer must be valid for its entire lifetime
        unsafe { &*self.end }
    }

    fn new_succ_array(ptr: *const T) -> [AtomicConstPtr<T>, .. MAX_HEIGHT ] {
        [ AtomicConstPtr::new(ptr),
          AtomicConstPtr::new(ptr),
          AtomicConstPtr::new(ptr),
          AtomicConstPtr::new(ptr),
          AtomicConstPtr::new(ptr),
          AtomicConstPtr::new(ptr),
          AtomicConstPtr::new(ptr) ]
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//// Node
///////////////////////////////////////////////////////////////////////////////////////////////////

enum Node<T> {
    StartSentinel {
        succs: [AtomicConstPtr<Node<T>>, .. MAX_HEIGHT],
    },
    Element {
        succs: [AtomicConstPtr<Node<T>>, .. MAX_HEIGHT],
        elem: T,
    },
    EndSentinel
}

impl <T: Sync + Send> Node<T> {

    /// Gets this node's vector of successor pointers.
    ///
    /// # Panics
    ///
    /// This method panics if this node is an end sentinel.
    fn succs(&self) -> &[AtomicConstPtr<Node<T>>, .. MAX_HEIGHT] {
        match *self {
            StartSentinel { ref succs, .. }
            |     Element { ref succs, .. } => succs,
            EndSentinel => panic!("Illegal argument: Node::succs may not be called on an end sentinel.")
        }
    }

    /// Gets a reference to the node's successor at the given height.
    ///
    /// # Panics
    ///
    /// This method panics if this node does not have a successor for the height, or if this node
    /// is an end sentinel.
    fn succ(&self, height: uint) -> &Node<T> {
        // safe since all nodes in the skip list have valid next pointers which point to nodes with
        // the same lifetime as the skip list.
        match *self {
            StartSentinel { ref succs, .. }
            |     Element { ref succs, .. } => {
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
    fn set_succ(&self, height: uint, node: *const Node<T>) {
        match *self {
            StartSentinel { ref succs, .. }
            |     Element { ref succs, .. } => succs[height].store(node, Release),
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
                             old: *const Node<T>,
                             new: *const Node<T>)
                             -> bool {
        match *self {
            StartSentinel { ref succs, .. }
            |     Element { ref succs, .. } => succs[height].compare_and_swap(old, new, AcqRel) == old,
            EndSentinel => panic!("Illegal argument: Node::compare_and_swap_succ may not be called on an end sentinel.")
        }
    }

    /// Gets a reference to the next node after this node.
    ///
    /// # Panics
    ///
    /// This method panics if this node is an end sentinel.
    fn next(&self) -> &Node<T> {
        match *self {
            // safe since every node is guaranteed to have at least one successor, and since all
            // in the skip list have valid next pointers which point to nodes with the same
            // lifetime as the skip list.
            StartSentinel { ref succs, .. }
            |     Element { ref succs, .. } => unsafe { &*succs[].unsafe_get(0).load(Acquire) },
            EndSentinel => panic!("Illegal argument: Node::next may not be called on an end sentinel.")
        }
    }

    /// Get this node's element.
    ///
    /// # Panics
    ///
    /// This method panics if this node is a start sentinel or an end sentinel.
    fn elem(&self) -> &T {
        match *self {
            StartSentinel { .. } => panic!("Illegal argument: Node::val may not be called on a start sentinel."),
            Element { ref elem, .. } => elem,
            EndSentinel => panic!("Illegal argument: Node::val may not be called on an end sentinel."),
        }
    }
}

impl <T: Ord> Node<T> {

    /// Compares this node to a given element.
    fn cmp_elem(&self, elem: &T) -> Ordering {
        match *self {
            Element { elem: ref self_elem, .. } => self_elem.cmp(elem),
            EndSentinel => Greater,
            StartSentinel { .. } => Less,
        }
    }
}

impl <T: PartialEq> PartialEq for Node<T> {
    fn eq(&self, other: &Node<T>) -> bool {
        match (self, other) {
            (&StartSentinel { .. }, &StartSentinel { .. }) => true,
            (&EndSentinel, &EndSentinel) => true,
            (&Element { elem: ref self_elem, .. }, &Element { elem: ref other_elem, .. }) => self_elem == other_elem,
            _ => false
        }
    }
}

/// Equality between `Node`s is defined only by the keys.
impl <T: Eq> Eq for Node<T> { }

/// Ordering between `Node`s is defined only by the keys.
impl <T: PartialOrd> PartialOrd for Node<T> {
    fn partial_cmp(&self, other: &Node<T>) -> Option<Ordering> {
        match (self, other) {
            (&StartSentinel { .. }, &StartSentinel { .. }) => Some(Equal),
            (&StartSentinel { .. }, _) => Some(Less),
            (_, &StartSentinel { .. }) => Some(Greater),
            (&EndSentinel, &EndSentinel) => Some(Equal),
            (&EndSentinel, _) => Some(Greater),
            (_, &EndSentinel) => Some(Less),
            (&Element { elem: ref self_elem, .. }, &Element { elem: ref other_elem, .. }) => self_elem.partial_cmp(other_elem)
        }
    }
}

/// Ordering between `Node`s is defined only by the keys.
impl <T: Ord> Ord for Node<T> {
    fn cmp(&self, other: &Node<T>) -> Ordering {
        match (self, other) {
            (&StartSentinel { .. }, &StartSentinel { .. }) => Equal,
            (&StartSentinel { .. }, _) => Less,
            (_, &StartSentinel { .. }) => Greater,
            (&EndSentinel, &EndSentinel) => Equal,
            (&EndSentinel, _) => Greater,
            (_, &EndSentinel) => Less,
            (&Element { elem: ref self_elem, .. }, &Element { elem: ref other_elem, .. }) => self_elem.cmp(other_elem)
        }
    }
}

impl <T: fmt::Show> fmt::Show for Node<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            StartSentinel { ref succs, .. } =>
                write!(formatter, "StartSentinel {{ height: {} }}", succs.len()),
            EndSentinel => write!(formatter, "EndSentinel"),
            Element { ref elem, ref succs, .. } =>
                write!(formatter, "Element {{ elem: {}, height: {} }}", elem, succs.len()),
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//// Iterator
///////////////////////////////////////////////////////////////////////////////////////////////////

struct Items<'a, T> {
    /// Whether the end element is inclusive.
    inclusive: bool,
    /// The start element, inclusive.
    start: *const Node<T>,
    /// The last element.
    end: *const Node<T>,
    marker: marker::ContravariantLifetime<'a>,
}

impl<'a, T> Items<'a, T> {

    /// Gets a reference to the start node.
    fn start(&self) -> &'a Node<T> {
        // This is safe because all Nodes must outlive the 'a lifetime.
        unsafe { &*self.start }
    }
}

impl<'a, T: Sync + Send> Iterator<&'a T> for Items<'a, T> {

    fn next(&mut self) -> Option<&'a T> {
        if self.start == self.end {
            if self.inclusive {
                self.inclusive = false;
                Some(self.start().elem())
            } else {
                None
            }
        } else {
            let next = self.start();
            self.start = next.next() as *const _;
            Some(next.elem())
        }
    }
}

#[cfg(test)]
mod test {

    #[phase(plugin)]
    extern crate quickcheck_macros;
    extern crate quickcheck;

    use std::collections::TreeSet;
    use std::sync::Barrier;
    use std::sync::Arc;
    use std::rand::Rand;

    use quickcheck::TestResult;

    use super::*;

    /// Checks that a given skip list is the valid outcome of inserting a sequence of elements into
    /// an empty skip list in order.
    fn verify_set_properties<T: Clone + Rand + Send + Sync + Ord>(skip_list: &SkipList<T>,
                                                                  elements: Vec<T>)
                                                                  -> bool {
        let mut tree_set = TreeSet::new();
        for elem in elements.iter() {
            tree_set.insert(elem.clone());
        }

        // The skip list and tree set should have the same number of elements
        if tree_set.len() > 0 {
            if skip_list.iter_from(tree_set.iter().next().unwrap()).count() != tree_set.len() {
                return false
            }
        }

        // The skip list and tree set lower bound iterators should have the same elements at every position
        for from_elem in elements.iter() {
            if skip_list.iter_from(from_elem).next() != tree_set.lower_bound(from_elem).next() {
                return false;
            }
        }

        true
    }

    #[quickcheck]
    fn check_set_properties(elements: Vec<int>,
                            branch_factor: u8)
                            -> TestResult {
        if branch_factor < 2 { return TestResult::discard() };

        let skip_list = SkipList::with_parameters(branch_factor);

        for element in elements.iter() {
            skip_list.insert(element.clone());
        }

        TestResult::from_bool(verify_set_properties(&skip_list, elements))
    }

    #[quickcheck]
    fn check_concurrent_access(elements: Vec<Vec<int>>,
                               branch_factor: u8) -> TestResult {
        if branch_factor < 2 { return TestResult::discard() };
        let skip_list = Arc::new(SkipList::with_parameters(branch_factor));
        let start_barrier = Arc::new(Barrier::new(elements.len() * 2));
        let end_barrier = Arc::new(Barrier::new(elements.len() * 2 + 1));

        // Concurrent writers
        for vec in elements.clone().into_iter() {
            let start = start_barrier.clone();
            let end = end_barrier.clone();
            let skip_list = skip_list.clone();
            spawn(proc() {
                start.wait();
                for element in vec.into_iter() {
                    skip_list.insert(element);
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
                for element in vec.iter() {
                    skip_list.iter_from(element).count();
                }
                end.wait();
            });
        }

        end_barrier.wait();

        let all_elements = elements.into_iter().flat_map(|v| v.into_iter()).collect::<Vec<int>>();
        TestResult::from_bool(verify_set_properties(&*skip_list, all_elements))
    }

    #[test]
    fn insert_replace() {
        let set = SkipList::new();
        assert!(set.insert(5i));
        assert!(set.insert(2));
        assert!(!set.insert(2));
    }

    #[test]
    fn test_insert() {
        let set = SkipList::new();
        set.insert(1i);
        set.insert(5);
        set.insert(3);
        set.insert(2);
        set.insert(4);
    }

    #[test]
    fn test_iter_from() {
        let m = SkipList::new();

        assert!(m.insert(3i));
        assert!(m.insert(0));
        assert!(m.insert(4));
        assert!(m.insert(2));
        assert!(m.insert(1));

        let mut n = 2;
        for element in m.iter_from(&2) {
            assert_eq!(*element, n);
            n += 1;
        }
        assert_eq!(n, 5);
    }

    #[test]
    #[should_fail]
    fn test_0_branch_factor() {
        SkipList::<int>::with_parameters(0);
    }

    #[test]
    #[should_fail]
    fn test_1_branch_factor() {
        SkipList::<int>::with_parameters(1);
    }
}

#[cfg(test)]
mod bench {
    extern crate test;
    use std::rand::{weak_rng, Rng};
    use test::{Bencher, black_box};
    use std::collections::TreeSet;
    use std::io::MemWriter;

    use super::SkipList;

    /// Populate a btree set with `n` elements, and iterate through `m` elements starting at a
    /// random offset into the set.
    fn tree_seek_scan(n: uint, m: uint, b: &mut Bencher) {
        let mut set = TreeSet::<Vec<u8>>::new();
        let mut rng = weak_rng();

        for elem in rng.gen_iter().take(n) {
            let mut writer = MemWriter::new();
            writer.write_le_u64(elem);
            set.insert(writer.unwrap());
        }

        b.iter(|| {
            let mut writer = MemWriter::new();
            writer.write_le_u64(rng.gen());
            for entry in set.lower_bound(&writer.unwrap()).take(m) {
                black_box(entry);
            }
        });
    }

    /// Populate a skip list with `n` elements, and iterate through `m` elements starting at a
    /// random offset into the set.
    fn skip_list_seek_scan(n: uint, m: uint, b: &mut Bencher) {
        let set = SkipList::<Vec<u8>>::new();
        let mut rng = weak_rng();

        for elem in rng.gen_iter().take(n) {
            let mut writer = MemWriter::new();
            writer.write_le_u64(elem);
            set.insert(writer.unwrap());
        }

        b.iter(|| {
            let mut writer = MemWriter::new();
            writer.write_le_u64(rng.gen());
            for entry in set.iter_from(&writer.unwrap()).take(m) {
                black_box(entry);
            }
        });
    }

    #[bench]
    pub fn seek_100_scan_0_skip_list(b: &mut Bencher) {
        skip_list_seek_scan(100, 0, b);
    }

    #[bench]
    pub fn seek_100_scan_10_skip_list(b: &mut Bencher) {
        skip_list_seek_scan(100, 10, b);
    }

    #[bench]
    pub fn seek_10_000_scan_0_skip_list(b: &mut Bencher) {
        skip_list_seek_scan(10_000, 0, b);
    }

    #[bench]
    pub fn seek_10_000_scan_10_skip_list(b: &mut Bencher) {
        skip_list_seek_scan(10_000, 10, b);
    }

    #[bench]
    pub fn seek_10_000_scan_100_skip_list(b: &mut Bencher) {
        skip_list_seek_scan(10_000, 100, b);
    }

    #[bench]
    pub fn seek_100_scan_0_tree(b: &mut Bencher) {
        tree_seek_scan(100, 0, b);
    }

    #[bench]
    pub fn seek_100_scan_10_tree(b: &mut Bencher) {
        tree_seek_scan(100, 10, b);
    }

    #[bench]
    pub fn seek_10_000_scan_0_tree(b: &mut Bencher) {
        tree_seek_scan(10_000, 0, b);
    }

    #[bench]
    pub fn seek_10_000_scan_10_tree(b: &mut Bencher) {
        tree_seek_scan(10_000, 10, b);
    }

    #[bench]
    pub fn seek_10_000_scan_100_tree(b: &mut Bencher) {
        tree_seek_scan(10_000, 100, b);
    }
}
