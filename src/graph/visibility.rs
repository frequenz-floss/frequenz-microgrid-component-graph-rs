// License: MIT
// Copyright © 2024 Frequenz Energy-as-a-Service GmbH

//! The visibility of components in a [`ComponentGraph`].
//!
//! The visible view hides components that play no part in the operational
//! picture of the site: pass-through categories and inactive components. Each
//! component gets one [`Visibility`], computed once after validation.
//!
//! Validators and formula generators use the crate-internal view, which only
//! walks past pass-through categories, so inactive components still take part
//! in validation and formula generation.

use std::collections::{HashSet, VecDeque};

use petgraph::graph::NodeIndex;

use crate::component_category::CategoryPredicates;
use crate::{ComponentGraph, Edge, Node};

/// How the visible view treats a component.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Visibility {
    /// Listed, and yielded by neighbor walks.
    Visible,
    /// Hidden. Neighbor walks pass through it to its own neighbors: a
    /// pass-through category, or an inactive component that is not a battery or
    /// hybrid inverter.
    Transparent,
    /// Hidden. Neighbor walks stop at it: an inactive battery or hybrid
    /// inverter, since a battery behind a dead inverter cannot be used.
    Blocking,
    /// Hidden. Not reachable from any component without predecessors, nor from
    /// the root, without passing through a blocking component.
    Pruned,
}

impl<N, E> ComponentGraph<N, E>
where
    N: Node,
    E: Edge,
{
    /// The visibility of the component at `index`.
    pub(crate) fn visibility(&self, index: NodeIndex) -> Visibility {
        self.visibility[index.index()]
    }

    /// Computes the visibility of every component, indexed by node index.
    ///
    /// The root is always visible, even when inactive: hiding it would hide the
    /// whole graph.
    pub(crate) fn compute_visibility(&self) -> Vec<Visibility> {
        let root = self.node_indices[&self.root_id];
        let mut visibility: Vec<Visibility> = self
            .graph
            .node_indices()
            .map(|index| {
                let node = &self.graph[index];
                if index == root {
                    Visibility::Visible
                } else if node.category().is_passthrough() {
                    Visibility::Transparent
                } else if !node.is_inactive() {
                    Visibility::Visible
                } else if node.is_battery_inverter(&self.config) || node.is_hybrid_inverter() {
                    Visibility::Blocking
                } else {
                    Visibility::Transparent
                }
            })
            .collect();

        // Pruned: not reachable from the root or from an entry component (one
        // without predecessors) without entering a blocking component. Every
        // entry counts, so an unconnected island the config allows is treated
        // like the root's own tree. An unconnected cycle has no entry, so it is
        // pruned as a whole.
        let reachable = self.reachable_from_entries(root, &visibility);
        for index in self.graph.node_indices() {
            if visibility[index.index()] != Visibility::Blocking && !reachable.contains(&index) {
                visibility[index.index()] = Visibility::Pruned;
            }
        }

        visibility
    }

    /// The components reachable along outgoing edges from `root` and from the
    /// components without predecessors, never entering a blocking component.
    fn reachable_from_entries(
        &self,
        root: NodeIndex,
        visibility: &[Visibility],
    ) -> HashSet<NodeIndex> {
        let enter = |index: NodeIndex| visibility[index.index()] != Visibility::Blocking;
        let mut queue: VecDeque<NodeIndex> = self
            .graph
            .node_indices()
            .filter(|&index| {
                enter(index)
                    && (index == root
                        || self
                            .graph
                            .neighbors_directed(index, petgraph::Direction::Incoming)
                            .next()
                            .is_none())
            })
            .collect();
        let mut reachable: HashSet<NodeIndex> = queue.iter().copied().collect();
        while let Some(index) = queue.pop_front() {
            for next in self
                .graph
                .neighbors_directed(index, petgraph::Direction::Outgoing)
            {
                if enter(next) && reachable.insert(next) {
                    queue.push_back(next);
                }
            }
        }
        reachable
    }
}
