// License: MIT
// Copyright © 2024 Frequenz Energy-as-a-Service GmbH

//! Iterators over components and connections in a `ComponentGraph`.

use std::{collections::HashSet, iter::Flatten, vec::IntoIter};

use petgraph::graph::{DiGraph, NodeIndices};

use crate::{ComponentGraph, Edge, Node};

use super::Visibility;

/// An iterator over the components in a `ComponentGraph`.
///
/// Returned by [`ComponentGraph::visible_components`], which skips the
/// components hidden from the visible view, and
/// [`ComponentGraph::raw_components`], which yields every component.
pub struct Components<'a, N>
where
    N: Node,
{
    pub(crate) graph: &'a DiGraph<N, ()>,
    pub(crate) iter: NodeIndices,
    pub(crate) visibility: &'a [Visibility],
    /// Whether to skip the components hidden from the visible view.
    pub(crate) visible_only: bool,
}

impl<'a, N> Iterator for Components<'a, N>
where
    N: Node,
{
    type Item = &'a N;

    fn next(&mut self) -> Option<Self::Item> {
        for index in self.iter.by_ref() {
            if !self.visible_only || self.visibility[index.index()] == Visibility::Visible {
                return Some(&self.graph[index]);
            }
        }
        None
    }
}

/// An iterator over every connection in a `ComponentGraph`.
///
/// Returned by [`ComponentGraph::raw_connections`].
pub struct RawConnections<'a, N, E>
where
    N: Node,
    E: Edge,
{
    pub(crate) cg: &'a ComponentGraph<N, E>,
    pub(crate) iter: std::slice::Iter<'a, petgraph::graph::Edge<()>>,
}

impl<'a, N, E> Iterator for RawConnections<'a, N, E>
where
    N: Node,
    E: Edge,
{
    type Item = &'a E;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .and_then(|e| self.cg.edges.get(&(e.source(), e.target())))
    }
}

/// An iterator over the connections between visible components, as `(source_id,
/// destination_id)` pairs.
///
/// Returned by [`ComponentGraph::visible_connections`]. A pair joins a visible
/// component to each of its visible successors, so a chain of hidden components
/// between the two is folded into one pair. Eagerly collected at construction
/// time.
pub struct VisibleConnections {
    pub(crate) iter: IntoIter<(u64, u64)>,
}

impl Iterator for VisibleConnections {
    type Item = (u64, u64);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// An iterator over the *raw* (graph-direct) neighbors of a component.
///
/// Returned by [`ComponentGraph::raw_predecessors`] and
/// [`ComponentGraph::raw_successors`]. Yields every node connected by an edge,
/// including the components the visible view hides.
pub struct RawNeighbors<'a, N>
where
    N: Node,
{
    pub(crate) graph: &'a DiGraph<N, ()>,
    pub(crate) iter: petgraph::graph::Neighbors<'a, ()>,
}

impl<'a, N> Iterator for RawNeighbors<'a, N>
where
    N: Node,
{
    type Item = &'a N;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|i| &self.graph[i])
    }
}

/// An iterator over the neighbors a filtered walk collects for a component.
///
/// Returned by [`ComponentGraph::visible_predecessors`] and
/// [`ComponentGraph::visible_successors`], which yield only visible
/// components, walking past transparent ones and stopping at blocking ones;
/// and by the crate-internal `effective_predecessors` and
/// `effective_successors`, which walk past pass-through categories only.
/// Eagerly collected at construction time.
pub struct Neighbors<'a, N>
where
    N: Node,
{
    pub(crate) iter: IntoIter<&'a N>,
}

impl<'a, N> Iterator for Neighbors<'a, N>
where
    N: Node,
{
    type Item = &'a N;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// An iterator over the siblings of a component in a `ComponentGraph`.
pub struct Siblings<'a, N>
where
    N: Node,
{
    pub(crate) component_id: u64,
    pub(crate) iter: Flatten<IntoIter<Neighbors<'a, N>>>,
    visited: HashSet<u64>,
}

impl<'a, N> Siblings<'a, N>
where
    N: Node,
{
    pub(crate) fn new(component_id: u64, iter: Flatten<IntoIter<Neighbors<'a, N>>>) -> Self {
        Siblings {
            component_id,
            iter,
            visited: HashSet::new(),
        }
    }
}

impl<'a, N> Iterator for Siblings<'a, N>
where
    N: Node,
{
    type Item = &'a N;

    fn next(&mut self) -> Option<Self::Item> {
        for i in self.iter.by_ref() {
            if i.component_id() == self.component_id || !self.visited.insert(i.component_id()) {
                continue;
            }
            return Some(i);
        }
        None
    }
}
