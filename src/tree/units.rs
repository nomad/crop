use std::sync::Arc;

use crate::tree::{Leaf, Lnode, Metric, Node, Tree, TreeSlice};

/// An iterator over consecutive units of a particular metric.
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    forward: UnitsForward<'a, FANOUT, L, M>,

    /// TODO: docs
    backward: UnitsBackward<'a, FANOUT, L, M>,

    /// TODO: docs
    yielded: L::BaseMetric,

    /// TODO: docs
    total: L::BaseMetric,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            forward: self.forward.clone(),
            backward: self.backward.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        // println!("{tree:#?}");

        Self {
            forward: UnitsForward::new(
                tree.root(),
                None,
                M::measure(tree.summary()),
            ),
            backward: UnitsBackward::new(tree.root(), None),
            yielded: L::BaseMetric::zero(),
            total: L::BaseMetric::measure(tree.summary()),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
    From<&'a TreeSlice<'a, FANOUT, L>> for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Units<'a, FANOUT, L, M> {
        // TODO: this doesn't yet work.

        todo!();

        // let front = UnitsFront::new(
        //     tree_slice.root(),
        //     None,
        //     M::measure(tree_slice.summary()),
        // );

        // Self {
        //     front,

        //     initialized_back: false,
        //     stack_back: Vec::with_capacity(stack_capacity),
        //     end_slice: tree_slice.end_slice(),
        //     end_summary: tree_slice.end_summary().clone(),

        //     yielded: L::BaseMetric::zero(),
        //     total: L::BaseMetric::measure(tree_slice.summary()),

        //     i: 0,
        // }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Iterator
    for Units<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded == self.total {
            None
        } else {
            let tree_slice = self.forward.next();
            self.yielded += L::BaseMetric::measure(tree_slice.summary());
            Some(tree_slice)
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> DoubleEndedIterator
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.yielded == self.total {
            None
        } else {
            let tree_slice = self.backward.next();
            self.yielded += L::BaseMetric::measure(tree_slice.summary());
            Some(tree_slice)
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> std::iter::FusedIterator
    for Units<'a, FANOUT, L, M>
{
}

#[derive(Debug)]
struct UnitsForward<'a, const N: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    is_initialized: bool,

    /// TODO: docs
    stack: Vec<(&'a Arc<Node<N, L>>, usize, L::Summary)>,

    /// TODO: docs
    start_slice: &'a L::Slice,

    /// TODO: docs
    start_summary: L::Summary,

    /// TODO: docs
    yielded: M,

    /// TODO: docs
    total: M,

    i: usize,
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> Clone
    for UnitsForward<'a, N, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            start_summary: self.start_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> UnitsForward<'a, N, L, M> {
    #[inline]
    fn new(
        root: &'a Arc<Node<N, L>>,
        start: Option<(&'a L::Slice, L::Summary)>,
        total: M,
    ) -> Self
    where
        for<'d> &'d L::Slice: Default,
    {
        let (start_slice, start_summary) = start.unwrap_or_default();

        let mut stack = Vec::with_capacity(root.depth());
        stack.push((root, 0, L::Summary::default()));

        Self {
            is_initialized: false,
            stack,
            start_slice,
            start_summary,
            yielded: M::zero(),
            total,
            i: 0,
        }
    }

    /// TODO: docs
    #[inline]
    fn initialize(&mut self) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        let mut node = self.stack[0].0;

        loop {
            match &**node {
                Node::Internal(inode) => {
                    let first = inode.first();
                    self.push(first, 0, L::Summary::default());
                    node = first;
                    continue;
                },

                Node::Leaf(leaf) => {
                    // If the base measure of `start_summary` is zero it means
                    // Self was created from a Tree, in which case the start
                    // slice should be this leaf. If it's > 0 it was created
                    // from a TreeSlice, and we can leave `start_slice` and
                    // `start_summary` untouched.
                    if L::BaseMetric::measure(&self.start_summary)
                        == L::BaseMetric::zero()
                    {
                        self.start_slice = leaf.as_slice();
                        self.start_summary = leaf.summary().clone();
                    } else {
                        // To handle this correctly we'd have to land to the
                        // leaf containing the start_slice, which we don't
                        // because we always go to the first leaf.
                        todo!();
                    }

                    return;
                },
            }
        }
    }

    #[inline]
    fn last_mut(
        &mut self,
    ) -> (&'a Arc<Node<N, L>>, &mut usize, &mut L::Summary) {
        debug_assert!(!self.stack.is_empty());

        let last_idx = self.stack.len() - 1;

        let &mut (root, ref mut visited, ref mut yielded_in_root) =
            &mut self.stack[last_idx];

        (root, visited, yielded_in_root)
    }

    #[inline]
    fn push(
        &mut self,
        node: &'a Arc<Node<N, L>>,
        child_idx: usize,
        measured: L::Summary,
    ) {
        debug_assert!(node.is_internal() || node.is_leaf() && child_idx == 0);
        self.stack.push((node, child_idx, measured));
    }

    #[inline]
    fn pop(&mut self) -> Option<(&'a Arc<Node<N, L>>, usize, L::Summary)> {
        self.stack.pop()
    }

    /// TODO: docs
    #[inline]
    fn next_leaf(&mut self) -> Option<&'a Lnode<L>> {
        let (mut last, _, _) = self.pop().unwrap();

        debug_assert!(last.is_leaf());

        let mut node = loop {
            let (node, visited, yielded) = self.last_mut();

            // Safety: TODO
            let inode = unsafe { node.as_internal_unchecked() };

            *visited += 1;

            if *visited == inode.children().len() {
                (last, _, _) = self.pop()?;
            } else {
                *yielded += last.summary();
                break &inode.children()[*visited];
            }
        };

        self.push(node, 0, L::Summary::default());

        loop {
            match &**node {
                Node::Internal(inode) => {
                    let first = inode.first();
                    self.push(first, 0, L::Summary::default());
                    node = first;
                    continue;
                },

                Node::Leaf(leaf) => {
                    return Some(leaf);
                },
            }
        }
    }

    /// TODO: docs
    #[inline]
    fn next_leaf_with_unit(
        &mut self,
        before: &mut L::Summary,
        summary: &mut L::Summary,
        leaf_count: &mut usize,
    ) -> &'a Lnode<L> {
        debug_assert!(self.yielded < self.total);
        debug_assert!(self.last_mut().0.is_internal());

        let (node, visited, measured) = self.last_mut();

        // Safety: TODO
        let inode = unsafe { node.as_internal_unchecked() };

        debug_assert!(*visited < inode.children().len() - 1);

        for child in &inode.children()[..*visited] {
            *before += child.summary();
        }

        *visited += 1;

        for child in &inode.children()[*visited..] {
            let child_summary = child.summary();

            if M::measure(child_summary) > M::zero() {
                break;
            } else {
                *visited += 1;
                *measured += child_summary;

                *summary += child_summary;
                *leaf_count += child.num_leaves();
            }
        }

        let mut node = &inode.children()[*visited];

        'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    let mut measured = L::Summary::default();

                    for (idx, child) in inode.children().iter().enumerate() {
                        let (child_summary, child_leaves) = match &**child {
                            Node::Internal(i) => (i.summary(), i.num_leaves()),
                            Node::Leaf(l) => (l.summary(), 1),
                        };

                        if M::measure(child_summary) != M::zero() {
                            self.push(node, idx, measured);
                            node = child;
                            continue 'outer;
                        } else {
                            measured += child_summary;
                            *summary += child_summary;
                            *leaf_count += child_leaves;
                        }
                    }
                },

                Node::Leaf(leaf) => {
                    self.push(node, 0, L::Summary::default());
                    return leaf;
                },
            }
        }
    }

    /// TODO: docs
    #[inline]
    fn next_unit_single_leaf(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(M::measure(&self.start_summary) > M::zero());
        debug_assert!(self.last_mut().0.is_leaf());

        let (root, _, yielded_in_root) = self.last_mut();

        debug_assert!(root.is_leaf());

        let before = yielded_in_root.clone();

        let (start_slice, start_summary, rest_slice, rest_summary) =
            M::split(self.start_slice, M::one(), &self.start_summary);

        if L::BaseMetric::measure(&rest_summary) > L::BaseMetric::zero() {
            let (_, _, measured) = self.last_mut();
            *measured += &start_summary;
            self.start_slice = rest_slice;
            self.start_summary = rest_summary;
        } else if let Some(leaf) = self.next_leaf() {
            self.start_slice = leaf.as_slice();
            self.start_summary = leaf.summary().clone();
        }

        TreeSlice {
            root,
            before,
            summary: start_summary.clone(),
            end_slice: start_slice,
            end_summary: start_summary.clone(),
            start_slice,
            start_summary,
            num_leaves: 1,
        }
    }

    /// TODO: docs
    #[inline]
    fn next_unit_multi_leaf(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(M::measure(&self.start_summary) == M::zero());
        debug_assert!(self.yielded < self.total);
        debug_assert!(self.last_mut().0.is_leaf());

        let start_slice = self.start_slice;
        let start_summary = self.start_summary.clone();

        let (mut popped, _, mut before) = self.pop().unwrap();

        let mut summary = start_summary.clone();

        let mut num_leaves = 1;

        let root = loop {
            let (node, _, measured) = self.last_mut();

            // Safety: TODO
            let inode = unsafe { node.as_internal_unchecked() };

            before += measured;

            if M::measure(inode.summary()) > M::measure(&before) {
                before -= measured;
                *measured += popped.summary();
                break node;
            } else {
                let (node, visited, _) = self.pop().unwrap();

                popped = node;

                // Safety: TODO
                let inode = unsafe { node.as_internal_unchecked() };

                for child in &inode.children()[visited + 1..] {
                    summary += child.summary();
                    num_leaves += child.num_leaves();
                }
            }
        };

        let leaf = self.next_leaf_with_unit(
            &mut before,
            &mut summary,
            &mut num_leaves,
        );

        debug_assert!(M::measure(leaf.summary()) > M::zero());

        let (end_slice, end_summary, rest_slice, rest_summary) =
            M::split(leaf.as_slice(), M::one(), leaf.summary());

        if L::BaseMetric::measure(&rest_summary) > L::BaseMetric::zero() {
            let (_, _, measured) = self.last_mut();
            *measured += &end_summary;
            self.start_slice = rest_slice;
            self.start_summary = rest_summary;
        } else if let Some(leaf) = self.next_leaf() {
            self.start_slice = leaf.as_slice();
            self.start_summary = leaf.summary().clone();
        }

        summary += &end_summary;
        num_leaves += 1;

        TreeSlice {
            root,
            before,
            summary,
            end_slice,
            end_summary,
            start_slice,
            start_summary,
            num_leaves,
        }
    }

    /// TODO: docs
    #[inline]
    fn yield_rest(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(M::measure(&self.start_summary) == M::zero());
        debug_assert!(self.yielded == self.total);
        debug_assert!(self.last_mut().0.is_leaf());

        let start_slice = self.start_slice;
        let start_summary = self.start_summary.clone();

        let (mut popped, _, mut before) = self.pop().unwrap();

        let mut summary = start_summary.clone();

        let mut num_leaves = 1;

        todo!();
    }

    #[inline]
    fn next(&mut self) -> TreeSlice<'a, N, L> {
        if !self.is_initialized {
            self.initialize();
        }

        debug_assert!(
            L::BaseMetric::measure(&self.start_summary)
                > L::BaseMetric::zero()
        );

        self.i += 1;

        let print = 2;

        // if self.i == print {
        //     println!("=======================");
        //     println!("=======================");
        //     println!("=======================");
        //     println!("=======================");
        //     println!("STATE AT START");
        //     println!("{:#?}", self);
        // }

        // TreeSlice spans leaf root.
        let tree_slice = if M::measure(&self.start_summary) > M::zero() {
            self.next_unit_single_leaf()
        }
        // This is the general case.
        else if self.yielded < self.total {
            self.next_unit_multi_leaf()
        }
        // All units have been yielded but the range has not been
        // exhausted, it means there's a final TreeSlice to yield
        // containing the rest.
        else {
            self.yield_rest()
        };

        self.yielded += M::one();

        // if self.i == print {
        //     println!("");
        //     println!("");
        //     println!("=======================");
        //     println!("ITERATION {}", self.i);
        //     println!("RETURNING {tree_slice:#?}");
        //     println!("");
        //     println!("");
        //     println!("");
        // }

        tree_slice
    }
}

#[derive(Debug)]
struct UnitsBackward<'a, const N: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    is_initialized: bool,

    /// TODO: docs
    stack: Vec<(&'a Arc<Node<N, L>>, usize, L::Summary)>,

    /// TODO: docs
    end_slice: &'a L::Slice,

    /// TODO: docs
    end_summary: L::Summary,

    /// TODO: docs
    yielded: M,
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> Clone
    for UnitsBackward<'a, N, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            end_summary: self.end_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> UnitsBackward<'a, N, L, M> {
    #[inline]
    fn new(
        root: &'a Arc<Node<N, L>>,
        end: Option<(&'a L::Slice, L::Summary)>,
    ) -> Self
    where
        for<'d> &'d L::Slice: Default,
    {
        let (end_slice, end_summary) = end.unwrap_or_default();

        let mut stack = Vec::with_capacity(root.depth());
        stack.push((root, 0, L::Summary::default()));

        Self {
            is_initialized: false,
            stack,
            end_slice,
            end_summary,
            yielded: M::zero(),
        }
    }

    #[inline]
    fn initialize(&mut self) {}

    #[inline]
    fn next(&mut self) -> TreeSlice<'a, N, L> {
        if !self.is_initialized {
            self.initialize();
        }

        debug_assert!(
            L::BaseMetric::measure(&self.end_summary) > L::BaseMetric::zero()
        );

        todo!();
    }
}

// impl<'a, const N: usize, L: Leaf, M: Metric<L>> Units<'a, N, L, M> {
//     #[inline]
//     fn last_front(&mut self) -> (&'a Arc<Node<N, L>>, L::Summary) {
//         debug_assert!(!self.stack_front.is_empty());
//         let (node, _, summary) = &self.stack_front[self.stack_front.len() - 1];
//         (*node, summary.clone())
//     }

//     #[inline]
//     fn last_is_exhausted_front(&self) -> bool {
//         debug_assert!(!self.stack_front.is_empty());
//         let (node, _, summary) = &self.stack_front[self.stack_front.len() - 1];
//         M::measure(node.summary()) == M::measure(summary)
//     }

//     #[inline]
//     fn pop_front(&mut self) -> (&'a Arc<Node<N, L>>, usize, L::Summary) {
//         debug_assert!(!self.stack_front.is_empty());
//         self.stack_front.pop().unwrap()
//     }

//     #[inline]
//     fn push_front(
//         &mut self,
//         node: &'a Arc<Node<N, L>>,
//         child_idx: usize,
//         measured: L::Summary,
//     ) {
//         debug_assert!(node.is_internal() || node.is_leaf() && child_idx == 0);
//         self.stack_front.push((node, child_idx, measured));
//     }

//     #[inline]
//     fn update_measured_front(&mut self, summary: &L::Summary) {
//         debug_assert!(!self.stack_front.is_empty());
//         let last_idx = self.stack_front.len() - 1;
//         let (_, _, measured) = &mut self.stack_front[last_idx];
//         *measured += summary
//     }

//     /// TODO: docs
//     #[inline]
//     fn initialize_front(&mut self) {
//         // TODO: this only works if we're iterating from start to finish. Make
//         // it work if iterating in a specific range.

//         self.initialized_front = true;

//         let mut node = self.root;

//         'outer: loop {
//             match &**node {
//                 Node::Internal(inode) => {
//                     self.push_front(node, 0, L::Summary::default());
//                     node = inode.first();
//                     continue 'outer;
//                 },

//                 Node::Leaf(leaf) => {
//                     // If the base measure of `start_summary` is zero it means
//                     // Self was created from a Tree, in which case the start
//                     // slice should be this leaf. If it's > 0 it was created
//                     // from a TreeSlice, and we can leave `start_slice` and
//                     // `start_summary` untouched.
//                     if L::BaseMetric::measure(&self.start_summary)
//                         == L::BaseMetric::zero()
//                     {
//                         self.start_slice = leaf.as_slice();
//                         self.start_summary = leaf.summary().clone();
//                         if M::measure(leaf.summary()) != M::zero() {
//                             self.push_front(node, 0, L::Summary::default());
//                         }
//                     } else {
//                         // To handle this correctly we'd have to land to the
//                         // leaf containing the start_slice, which we don't
//                         // because we always go to the first leaf.
//                         todo!();
//                     }

//                     return;
//                 },
//             }
//         }
//     }

//     /// TODO: docs
//     #[inline]
//     fn next_leaf_with_unit_front(
//         &mut self,
//         summary: &mut L::Summary,
//         leaf_count: &mut usize,
//     ) -> &'a Lnode<L> {
//         debug_assert!(!self.last_is_exhausted_front());

//         let last_idx = self.stack_front.len() - 1;

//         let &mut (root, ref mut visited, ref mut measured) =
//             &mut self.stack_front[last_idx];

//         let mut node = match &**root {
//             Node::Internal(inode) => {
//                 let mut new_child_idx = *visited + 1;
//                 let mut children = inode.children()[new_child_idx..].iter();

//                 loop {
//                     let child = children.next().unwrap();

//                     let (child_summary, child_leaves) = match &**child {
//                         Node::Internal(i) => (i.summary(), i.num_leaves()),
//                         Node::Leaf(l) => (l.summary(), 1),
//                     };

//                     if M::measure(child_summary) != M::zero() {
//                         *visited = new_child_idx;
//                         break child;
//                     } else {
//                         new_child_idx += 1;
//                         *measured += child_summary;
//                         *summary += child_summary;
//                         *leaf_count += child_leaves;
//                     }
//                 }
//             },

//             Node::Leaf(_) => root,
//         };

//         'outer: loop {
//             match &**node {
//                 Node::Internal(inode) => {
//                     let mut measured = L::Summary::default();

//                     for (idx, child) in inode.children().iter().enumerate() {
//                         let (child_summary, child_leaves) = match &**child {
//                             Node::Internal(i) => (i.summary(), i.num_leaves()),
//                             Node::Leaf(l) => (l.summary(), 1),
//                         };

//                         if M::measure(child_summary) != M::zero() {
//                             self.push_front(node, idx, measured);
//                             node = child;
//                             continue 'outer;
//                         } else {
//                             measured += child_summary;
//                             *summary += child_summary;
//                             *leaf_count += child_leaves;
//                         }
//                     }
//                 },

//                 Node::Leaf(leaf) => {
//                     self.push_front(node, 0, L::Summary::default());
//                     return leaf;
//                 },
//             }
//         }
//     }

//     /// TODO: docs
//     #[inline]
//     fn next_leaf_front(&mut self) -> Option<&'a Lnode<L>> {
//         debug_assert!(self.last_front().0.is_leaf());

//         let (mut last, _, _) = self.pop_front();

//         let mut last_idx = self.stack_front.len() - 1;

//         let mut node = loop {
//             let &mut (root, ref mut visited, ref mut measured) =
//                 &mut self.stack_front[last_idx];

//             // Safety: TODO.
//             let inode = unsafe { root.as_internal_unchecked() };

//             *visited += 1;

//             if *visited == inode.children().len() {
//                 last = self.pop_front().0;

//                 // TODO: handle empty stack
//                 if last_idx == 0 {
//                     return None;
//                 } else {
//                     last_idx -= 1;
//                 }
//             } else {
//                 *measured += last.summary();
//                 break &inode.children()[*visited];
//             }
//         };

//         'outer: loop {
//             match &**node {
//                 Node::Internal(inode) => {
//                     self.push_front(node, 0, L::Summary::default());
//                     node = inode.first();
//                     continue 'outer;
//                 },

//                 Node::Leaf(leaf) => {
//                     if M::measure(leaf.summary()) != M::zero() {
//                         self.push_front(node, 0, L::Summary::default());
//                     }
//                     return Some(leaf);
//                 },
//             }
//         }
//     }

//     /// TODO: docs
//     #[inline]
//     fn next(&mut self) -> TreeSlice<'a, N, L> {
//         debug_assert!(
//             L::BaseMetric::measure(&self.start_summary)
//                 > L::BaseMetric::zero()
//         );

//         // TODO: this doesn't work if start_summary > M::zero().
//         let mut start_slice = self.start_slice;
//         let mut start_summary = self.start_summary.clone();

//         let (mut root, mut before) = self.last_front();
//         let mut summary = start_summary.clone();
//         let mut num_leaves = 1;

//         let (slice, summaro, a) =
//             if M::measure(&self.start_summary) == M::zero() {
//                 if self.last_front().0.is_leaf() {
//                     self.pop_front();
//                 }

//                 self.update_measured_front(&start_summary);

//                 // Pop the stack until the node at the top contains some units
//                 // to yield.
//                 loop {
//                     let mut ciao = before.clone();

//                     let last_idx = self.stack_front.len() - 1;

//                     let &mut (node, _, ref mut measured) =
//                         &mut self.stack_front[last_idx];

//                     let inode = unsafe { node.as_internal_unchecked() };

//                     println!("ADDING MEASURED {measured:?} TO CIAO {ciao:?}");

//                     ciao += measured;

//                     if M::measure(&ciao) == M::measure(inode.summary()) {
//                         before = ciao;

//                         let (last, visited, _) = self.pop_front();

//                         if let Node::Internal(inode) = &**last {
//                             // Add the leaf count and summary of all the
//                             // children of this internal node that we haven't
//                             // visited.
//                             for child in &inode.children()[visited + 1..] {
//                                 let (summ, leaf_count) = match &**child {
//                                     Node::Internal(inode) => {
//                                         (inode.summary(), inode.num_leaves())
//                                     },
//                                     Node::Leaf(leaf) => (leaf.summary(), 1),
//                                 };

//                                 summary += summ;
//                                 num_leaves += leaf_count;
//                             }
//                         }
//                     } else {
//                         // self.update_measured_front(inode.summary());
//                         break;
//                     }
//                 }

//                 // while self.last_is_exhausted_front() {
//                 //     let (last, visited, measured) = self.pop_front();

//                 //     println!("");

//                 //     if let Node::Internal(inode) = &**last {
//                 //         // TODO: comment this
//                 //         println!("ADDING MEASURED IN {inode:#?}");
//                 //         println!("MEASURED: {measured:?}");

//                 //         before += &measured;

//                 //         for child in &inode.children()[visited + 1..] {
//                 //             let (summ, leaf_count) = match &**child {
//                 //                 Node::Internal(inode) => {
//                 //                     (inode.summary(), inode.num_leaves())
//                 //                 },
//                 //                 Node::Leaf(leaf) => (leaf.summary(), 1),
//                 //             };

//                 //             summary += summ;
//                 //             num_leaves += leaf_count;
//                 //         }
//                 //     }
//                 // }

//                 // The node that's now at the top of the stack is the root of
//                 // the TreeSlice that will be returned.
//                 root = self.last_front().0;

//                 // Now add nodes to the stack until we get to the leaf node
//                 // containing the next unit.
//                 let next_leaf = self
//                     .next_leaf_with_unit_front(&mut summary, &mut num_leaves);

//                 debug_assert!(M::measure(next_leaf.summary()) > M::zero());

//                 (next_leaf.as_slice(), next_leaf.summary(), true)
//             } else {
//                 debug_assert!(root.is_leaf());
//                 (self.start_slice, &self.start_summary, false)
//             };

//         let (end_slice, end_summary, rest_slice, rest_summary) =
//             M::split(slice, M::one(), summaro);

//         if L::BaseMetric::measure(&rest_summary) == L::BaseMetric::zero() {
//             if let Some(next_leaf) = self.next_leaf_front() {
//                 self.start_slice = next_leaf.as_slice();
//                 self.start_summary = next_leaf.summary().clone();
//             }
//         } else {
//             self.update_measured_front(&end_summary);
//             self.start_slice = rest_slice;
//             self.start_summary = rest_summary;
//         }

//         if a {
//             summary += &end_summary;
//             num_leaves += 1;
//         } else {
//             start_slice = end_slice;
//             start_summary = end_summary.clone();
//             summary = end_summary.clone();
//         }

//         TreeSlice {
//             root,
//             before,
//             summary,
//             end_slice,
//             end_summary,
//             start_slice,
//             start_summary,
//             num_leaves,
//         }
//     }

// /// TODO: docs
// #[inline]
// fn initialize_back(&mut self) {}

// /// TODO: docs
// #[inline]
// fn next_back(&mut self) -> TreeSlice<'a, N, L> {
//     todo!();
// }
// }
