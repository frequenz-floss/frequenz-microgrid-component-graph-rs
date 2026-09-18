// License: MIT
// Copyright © 2024 Frequenz Energy-as-a-Service GmbH

//! Methods for retrieving components and connections from a [`ComponentGraph`].

use crate::iterators::{Components, Connections, Neighbors, RawNeighbors, Siblings};
use crate::{ComponentGraph, Edge, Error, Node};
use petgraph::graph::NodeIndex;
use std::collections::{BTreeSet, HashSet, VecDeque};

use super::Visibility;

/// `Component` and `Connection` retrieval.
impl<N, E> ComponentGraph<N, E>
where
    N: Node,
    E: Edge,
{
    /// Returns the component with the given `component_id`, if it exists.
    pub fn component(&self, component_id: u64) -> Result<&N, Error> {
        self.node_indices
            .get(&component_id)
            .map(|i| &self.graph[*i])
            .ok_or_else(|| {
                Error::component_not_found(format!("Component with id {component_id} not found."))
            })
    }

    /// Returns an iterator over the components in the graph.
    pub fn components(&self) -> Components<'_, N> {
        self.raw_components()
    }

    /// Returns an iterator over *every* component in the graph, including those
    /// hidden from [`components`][Self::components].
    pub fn raw_components(&self) -> Components<'_, N> {
        Components {
            iter: self.graph.raw_nodes().iter(),
        }
    }

    /// Returns an iterator over the connections in the graph.
    pub fn connections(&self) -> Connections<'_, N, E> {
        Connections {
            cg: self,
            iter: self.graph.raw_edges().iter(),
        }
    }

    /// Returns an iterator over the *raw* (graph-direct) predecessors of the
    /// component with the given `component_id`.
    ///
    /// "Raw" means every node connected by an incoming edge, including hidden
    /// components. Most callers want
    /// [`visible_predecessors`][Self::visible_predecessors] instead, which
    /// walks past hidden components.
    ///
    /// Returns an error if the given `component_id` does not exist.
    pub fn raw_predecessors(&self, component_id: u64) -> Result<RawNeighbors<'_, N>, Error> {
        self.raw_neighbors(component_id, petgraph::Direction::Incoming)
    }

    /// Returns an iterator over the *raw* (graph-direct) successors of the
    /// component with the given `component_id`.
    ///
    /// "Raw" means every node connected by an outgoing edge, including hidden
    /// components. Most callers want
    /// [`visible_successors`][Self::visible_successors] instead, which walks
    /// past hidden components.
    ///
    /// Returns an error if the given `component_id` does not exist.
    pub fn raw_successors(&self, component_id: u64) -> Result<RawNeighbors<'_, N>, Error> {
        self.raw_neighbors(component_id, petgraph::Direction::Outgoing)
    }

    /// Shared implementation for [`raw_predecessors`][Self::raw_predecessors]
    /// and [`raw_successors`][Self::raw_successors].
    fn raw_neighbors(
        &self,
        component_id: u64,
        direction: petgraph::Direction,
    ) -> Result<RawNeighbors<'_, N>, Error> {
        self.node_indices
            .get(&component_id)
            .map(|&index| RawNeighbors {
                graph: &self.graph,
                iter: self.graph.neighbors_directed(index, direction),
            })
            .ok_or_else(|| {
                Error::component_not_found(format!("Component with id {component_id} not found."))
            })
    }

    /// Returns an iterator over the visible *predecessors* of the component
    /// with the given `component_id`, walking transparently past hidden
    /// components.
    ///
    /// Pass-through categories and inactive components are skipped: their
    /// visible ancestors take their place in the iterator. An inactive battery
    /// or hybrid inverter is not walked through, so the components behind it
    /// have no visible predecessors. A hidden component has no visible
    /// predecessors either. For the raw (graph-direct) view, use
    /// [`raw_predecessors`][Self::raw_predecessors].
    ///
    /// Returns an error if the given `component_id` does not exist.
    pub fn visible_predecessors(&self, component_id: u64) -> Result<Neighbors<'_, N>, Error> {
        self.collect_visible_neighbors(component_id, petgraph::Direction::Incoming)
    }

    /// Crate-internal view of the predecessors of the component with the given
    /// `component_id`: walks past pass-through categories only.
    ///
    /// Validators and formula generators use this view so that inactive
    /// components, which the public
    /// [`visible_predecessors`][Self::visible_predecessors] hides,
    /// still take part in validation and formula generation.
    pub(crate) fn effective_predecessors(
        &self,
        component_id: u64,
    ) -> Result<Neighbors<'_, N>, Error> {
        self.collect_effective_neighbors(component_id, petgraph::Direction::Incoming)
    }

    /// Returns an iterator over the visible *successors* of the component with
    /// the given `component_id`, walking transparently past hidden components.
    ///
    /// Pass-through categories and inactive components are skipped: their
    /// visible descendants take their place in the iterator. An inactive
    /// battery or hybrid inverter is not walked through, so it and the
    /// components behind it never appear. A hidden component has no visible
    /// successors either. For the raw (graph-direct) view, use
    /// [`raw_successors`][Self::raw_successors].
    ///
    /// Returns an error if the given `component_id` does not exist.
    pub fn visible_successors(&self, component_id: u64) -> Result<Neighbors<'_, N>, Error> {
        self.collect_visible_neighbors(component_id, petgraph::Direction::Outgoing)
    }

    /// Crate-internal view of the successors of the component with the given
    /// `component_id`: walks past pass-through categories only.
    ///
    /// See [`effective_predecessors`][Self::effective_predecessors].
    pub(crate) fn effective_successors(
        &self,
        component_id: u64,
    ) -> Result<Neighbors<'_, N>, Error> {
        self.collect_effective_neighbors(component_id, petgraph::Direction::Outgoing)
    }

    /// BFS through pass-through nodes in the given direction, collecting
    /// the first non-pass-through node along each branch.
    fn collect_effective_neighbors(
        &self,
        component_id: u64,
        direction: petgraph::Direction,
    ) -> Result<Neighbors<'_, N>, Error> {
        let start = self.index_of(component_id)?;
        Ok(self.collect_neighbors_from(start, direction, |idx| {
            if self.graph[idx].category().is_passthrough() {
                Visibility::Transparent
            } else {
                Visibility::Visible
            }
        }))
    }

    /// BFS through hidden nodes in the given direction, collecting the first
    /// visible node along each branch and stopping at blocking ones. A hidden
    /// start has no visible neighbors.
    fn collect_visible_neighbors(
        &self,
        component_id: u64,
        direction: petgraph::Direction,
    ) -> Result<Neighbors<'_, N>, Error> {
        let start = self.index_of(component_id)?;
        Ok(self.collect_visible_neighbors_from(start, direction))
    }

    /// [`collect_visible_neighbors`][Self::collect_visible_neighbors] from a
    /// node index.
    fn collect_visible_neighbors_from(
        &self,
        start: NodeIndex,
        direction: petgraph::Direction,
    ) -> Neighbors<'_, N> {
        if self.visibility(start) != Visibility::Visible {
            return Neighbors {
                iter: Vec::new().into_iter(),
            };
        }
        self.collect_neighbors_from(start, direction, |idx| self.visibility(idx))
    }

    /// The node index of the component with the given `component_id`.
    ///
    /// Returns an error if the given `component_id` does not exist.
    fn index_of(&self, component_id: u64) -> Result<NodeIndex, Error> {
        self.node_indices
            .get(&component_id)
            .copied()
            .ok_or_else(|| {
                Error::component_not_found(format!("Component with id {component_id} not found."))
            })
    }

    /// BFS from `start` in the given direction, letting `classify` decide per
    /// node whether the walk yields it (visible), walks through it
    /// (transparent) or stops (blocking or pruned).
    fn collect_neighbors_from(
        &self,
        start: NodeIndex,
        direction: petgraph::Direction,
        classify: impl Fn(NodeIndex) -> Visibility,
    ) -> Neighbors<'_, N> {
        let mut queue: VecDeque<NodeIndex> =
            self.graph.neighbors_directed(start, direction).collect();
        // The start is never its own neighbor, even on a cycle.
        let mut visited: HashSet<NodeIndex> = HashSet::from([start]);
        let mut result: Vec<&N> = Vec::new();

        while let Some(idx) = queue.pop_front() {
            if !visited.insert(idx) {
                continue;
            }
            match classify(idx) {
                Visibility::Visible => result.push(&self.graph[idx]),
                Visibility::Transparent => {
                    queue.extend(self.graph.neighbors_directed(idx, direction));
                }
                Visibility::Blocking | Visibility::Pruned => {}
            }
        }

        Neighbors {
            iter: result.into_iter(),
        }
    }

    /// Returns an iterator over the *siblings* of the component with the
    /// given `component_id`, that have shared predecessors.
    ///
    /// Returns an error if the given `component_id` does not exist.
    pub(crate) fn siblings_from_predecessors(
        &self,
        component_id: u64,
    ) -> Result<Siblings<'_, N>, Error> {
        Ok(Siblings::new(
            component_id,
            self.effective_predecessors(component_id)?
                .map(|x| self.effective_successors(x.component_id()))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten(),
        ))
    }

    /// Returns an iterator over the *siblings* of the component with the
    /// given `component_id`, that have shared successors.
    ///
    /// Returns an error if the given `component_id` does not exist.
    pub(crate) fn siblings_from_successors(
        &self,
        component_id: u64,
    ) -> Result<Siblings<'_, N>, Error> {
        Ok(Siblings::new(
            component_id,
            self.effective_successors(component_id)?
                .map(|x| self.effective_predecessors(x.component_id()))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten(),
        ))
    }

    /// Returns a set of all components that match the given predicate, starting
    /// from the component with the given `component_id`, in the given direction.
    ///
    /// If `follow_after_match` is `true`, the search continues deeper beyond
    /// the matching components.
    pub(crate) fn find_all(
        &self,
        from: u64,
        pred: impl Fn(&N) -> bool,
        direction: petgraph::Direction,
        follow_after_match: bool,
    ) -> Result<BTreeSet<u64>, Error> {
        let index = self.node_indices.get(&from).ok_or_else(|| {
            Error::component_not_found(format!("Component with id {from} not found."))
        })?;
        let mut stack = vec![*index];
        let mut visited = HashSet::new();
        let mut found = BTreeSet::new();

        while let Some(index) = stack.pop() {
            // Skip nodes already expanded: a DAG with diamonds reaches the
            // same node by multiple paths, and re-expanding it is redundant
            // (and exponential on chained diamonds).
            if !visited.insert(index) {
                continue;
            }
            let node = &self.graph[index];
            // Pass-through nodes are transparent: skip the predicate
            // check but follow through their neighbors.
            if !node.category().is_passthrough() && pred(node) {
                found.insert(node.component_id());
                if !follow_after_match {
                    continue;
                }
            }

            let neighbors = self.graph.neighbors_directed(index, direction);
            stack.extend(neighbors);
        }

        Ok(found)
    }

    /// Whether any component matching the given predicate is reachable from
    /// the component with the given `component_id`, in the given direction.
    /// Stops at the first match, unlike [`ComponentGraph::find_all`], which
    /// collects them all. Pass-through nodes are transparent here too: they
    /// never match, but the search follows through their neighbors.
    pub(crate) fn reaches_any(
        &self,
        from: u64,
        pred: impl Fn(&N) -> bool,
        direction: petgraph::Direction,
    ) -> Result<bool, Error> {
        let index = self.node_indices.get(&from).ok_or_else(|| {
            Error::component_not_found(format!("Component with id {from} not found."))
        })?;
        let mut stack = vec![*index];
        let mut visited = HashSet::new();

        while let Some(index) = stack.pop() {
            // Skip nodes already expanded: a DAG with diamonds reaches the
            // same node by multiple paths, and re-expanding it is redundant
            // (and exponential on chained diamonds).
            if !visited.insert(index) {
                continue;
            }
            let node = &self.graph[index];
            if !node.category().is_passthrough() && pred(node) {
                return Ok(true);
            }
            stack.extend(self.graph.neighbors_directed(index, direction));
        }

        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ComponentCategory;
    use crate::ComponentGraphConfig;
    use crate::InverterType;
    use crate::OperationalMode;
    use crate::component_category::BatteryType;
    use crate::component_category::CategoryPredicates;
    use crate::error::Error;
    use crate::graph::test_utils::ComponentGraphBuilder;
    use crate::graph::test_utils::{TestComponent, TestConnection};

    fn ids<'a>(iter: impl Iterator<Item = &'a TestComponent>) -> Vec<u64> {
        let mut ids: Vec<u64> = iter.map(|c| c.component_id()).collect();
        ids.sort_unstable();
        ids
    }

    fn nodes_and_edges() -> (Vec<TestComponent>, Vec<TestConnection>) {
        let components = vec![
            TestComponent::new(6, ComponentCategory::Meter),
            TestComponent::new(1, ComponentCategory::GridConnectionPoint),
            TestComponent::new(7, ComponentCategory::Inverter(InverterType::Battery)),
            TestComponent::new(3, ComponentCategory::Meter),
            TestComponent::new(5, ComponentCategory::Battery(BatteryType::Unspecified)),
            TestComponent::new(8, ComponentCategory::Battery(BatteryType::LiIon)),
            TestComponent::new(4, ComponentCategory::Inverter(InverterType::Battery)),
            TestComponent::new(2, ComponentCategory::Meter),
        ];
        let connections = vec![
            TestConnection::new(3, 4),
            TestConnection::new(1, 2),
            TestConnection::new(7, 8),
            TestConnection::new(4, 5),
            TestConnection::new(2, 3),
            TestConnection::new(6, 7),
            TestConnection::new(2, 6),
        ];

        (components, connections)
    }

    #[test]
    fn test_component() -> Result<(), Error> {
        let config = ComponentGraphConfig::default();
        let (components, connections) = nodes_and_edges();
        let graph = ComponentGraph::try_new(components.clone(), connections.clone(), config)?;

        assert_eq!(
            graph.component(1),
            Ok(&TestComponent::new(
                1,
                ComponentCategory::GridConnectionPoint
            ))
        );
        assert_eq!(
            graph.component(5),
            Ok(&TestComponent::new(
                5,
                ComponentCategory::Battery(BatteryType::Unspecified)
            ))
        );
        assert_eq!(
            graph.component(9),
            Err(Error::component_not_found("Component with id 9 not found."))
        );

        Ok(())
    }

    #[test]
    fn test_components() -> Result<(), Error> {
        let config = ComponentGraphConfig::default();
        let (components, connections) = nodes_and_edges();
        let graph = ComponentGraph::try_new(components.clone(), connections.clone(), config)?;

        assert!(graph.components().eq(&components));
        assert!(graph.components().filter(|x| x.is_battery()).eq(&[
            TestComponent::new(5, ComponentCategory::Battery(BatteryType::Unspecified)),
            TestComponent::new(8, ComponentCategory::Battery(BatteryType::LiIon))
        ]));

        Ok(())
    }

    #[test]
    fn test_connections() -> Result<(), Error> {
        let config = ComponentGraphConfig::default();
        let (components, connections) = nodes_and_edges();
        let graph = ComponentGraph::try_new(components.clone(), connections.clone(), config)?;

        assert!(graph.connections().eq(&connections));

        assert!(
            graph
                .connections()
                .filter(|x| x.source() == 2)
                .eq(&[TestConnection::new(2, 3), TestConnection::new(2, 6)])
        );

        Ok(())
    }

    #[test]
    fn test_neighbors() -> Result<(), Error> {
        let config = ComponentGraphConfig::default();
        let (components, connections) = nodes_and_edges();
        let graph = ComponentGraph::try_new(components.clone(), connections.clone(), config)?;

        assert!(graph.visible_predecessors(1).is_ok_and(|x| x.eq(&[])));

        assert!(
            graph
                .visible_predecessors(3)
                .is_ok_and(|x| x.eq(&[TestComponent::new(2, ComponentCategory::Meter)]))
        );

        assert!(
            graph
                .visible_successors(1)
                .is_ok_and(|x| x.eq(&[TestComponent::new(2, ComponentCategory::Meter)]))
        );

        assert!(graph.visible_successors(2).is_ok_and(|x| {
            x.eq(&[
                TestComponent::new(6, ComponentCategory::Meter),
                TestComponent::new(3, ComponentCategory::Meter),
            ])
        }));

        assert!(graph.visible_successors(5).is_ok_and(|x| x.eq(&[])));

        assert!(
            graph
                .visible_predecessors(32)
                .is_err_and(|e| e == Error::component_not_found("Component with id 32 not found."))
        );
        assert!(
            graph
                .visible_successors(32)
                .is_err_and(|e| e == Error::component_not_found("Component with id 32 not found."))
        );

        Ok(())
    }

    #[test]
    fn test_siblings() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();

        // Add a grid meter to the grid, with no successors.
        let grid_meter = builder.meter();
        builder.connect(grid, grid_meter);

        assert_eq!(grid_meter.component_id(), 1);

        // Add a battery chain with three inverters and two battery.
        let meter_bat_chain = builder.meter_bat_chain(3, 2);
        builder.connect(grid_meter, meter_bat_chain);

        assert_eq!(meter_bat_chain.component_id(), 2);

        let graph = builder.build(None)?;
        assert_eq!(
            graph
                .siblings_from_predecessors(3)
                .unwrap()
                .collect::<Vec<_>>(),
            [
                &TestComponent::new(5, ComponentCategory::Inverter(InverterType::Battery)),
                &TestComponent::new(4, ComponentCategory::Inverter(InverterType::Battery))
            ]
        );

        assert_eq!(
            graph
                .siblings_from_successors(3)
                .unwrap()
                .collect::<Vec<_>>(),
            [
                &TestComponent::new(5, ComponentCategory::Inverter(InverterType::Battery)),
                &TestComponent::new(4, ComponentCategory::Inverter(InverterType::Battery))
            ]
        );

        assert_eq!(
            graph
                .siblings_from_successors(6)
                .unwrap()
                .collect::<Vec<_>>(),
            Vec::<&TestComponent>::new()
        );

        assert_eq!(
            graph
                .siblings_from_predecessors(6)
                .unwrap()
                .collect::<Vec<_>>(),
            [&TestComponent::new(
                7,
                ComponentCategory::Battery(BatteryType::LiIon)
            )]
        );

        // Add two dangling meter to the grid meter
        let dangling_meter = builder.meter();
        builder.connect(grid_meter, dangling_meter);
        assert_eq!(dangling_meter.component_id(), 8);

        let dangling_meter = builder.meter();
        builder.connect(grid_meter, dangling_meter);
        assert_eq!(dangling_meter.component_id(), 9);

        let graph = builder.build(None)?;
        assert_eq!(
            graph
                .siblings_from_predecessors(8)
                .unwrap()
                .collect::<Vec<_>>(),
            [
                &TestComponent::new(9, ComponentCategory::Meter),
                &TestComponent::new(2, ComponentCategory::Meter),
            ]
        );

        Ok(())
    }

    /// `raw_predecessors` / `raw_successors` expose the graph-direct
    /// view (including pass-through nodes), while `predecessors` /
    /// `successors` walk past them.
    ///
    /// Topology: `Grid → PT → Meter → BatteryInverter → Battery`.
    #[test]
    fn test_raw_neighbors_includes_passthroughs() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();
        let pt = builder.power_transformer();
        let meter = builder.meter();
        let inverter = builder.battery_inverter();
        let battery = builder.battery();

        builder.connect(grid, pt);
        builder.connect(pt, meter);
        builder.connect(meter, inverter);
        builder.connect(inverter, battery);

        let graph = builder.build(None)?;

        // Raw view sees the PT directly.
        let raw_preds: Vec<u64> = graph
            .raw_predecessors(meter.component_id())?
            .map(|n| n.component_id())
            .collect();
        assert_eq!(raw_preds, vec![pt.component_id()]);

        let raw_succs: Vec<u64> = graph
            .raw_successors(grid.component_id())?
            .map(|n| n.component_id())
            .collect();
        assert_eq!(raw_succs, vec![pt.component_id()]);

        // The visible view walks past the PT.
        let preds: Vec<u64> = graph
            .visible_predecessors(meter.component_id())?
            .map(|n| n.component_id())
            .collect();
        assert_eq!(preds, vec![grid.component_id()]);

        let succs: Vec<u64> = graph
            .visible_successors(grid.component_id())?
            .map(|n| n.component_id())
            .collect();
        assert_eq!(succs, vec![meter.component_id()]);

        // Unknown component_id behaves the same as the visible methods.
        assert!(graph.raw_predecessors(999).is_err());
        assert!(graph.raw_successors(999).is_err());

        // Make sure the unused `battery` and `inverter` handles aren't
        // optimised away in unrelated test setup.
        let _ = (battery, inverter);
        Ok(())
    }

    /// `find_all` skips pass-through nodes when checking the predicate
    /// — even if the predicate would match. This keeps PTs out of
    /// callers' result sets without forcing them to filter.
    ///
    /// Topology: `Grid → PT → Meter`.
    #[test]
    fn test_find_all_skips_passthroughs() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();
        let pt = builder.power_transformer();
        let meter = builder.meter();

        builder.connect(grid, pt);
        builder.connect(pt, meter);

        let graph = builder.build(None)?;

        // Predicate matches everything; PT is excluded from the result.
        let found = graph.find_all(
            grid.component_id(),
            |_| true,
            petgraph::Direction::Outgoing,
            true,
        )?;
        assert_eq!(
            found,
            BTreeSet::from([grid.component_id(), meter.component_id()])
        );

        // Predicate that explicitly tries to match PTs still returns nothing.
        let found = graph.find_all(
            grid.component_id(),
            |n| n.category() == ComponentCategory::PowerTransformer,
            petgraph::Direction::Outgoing,
            true,
        )?;
        assert!(found.is_empty());
        Ok(())
    }

    #[test]
    fn test_find_all() -> Result<(), Error> {
        let (components, connections) = nodes_and_edges();
        let graph = ComponentGraph::try_new(
            components.clone(),
            connections.clone(),
            ComponentGraphConfig::default(),
        )?;

        let found = graph.find_all(
            graph.root_id,
            |x| x.is_meter(),
            petgraph::Direction::Outgoing,
            false,
        )?;
        assert_eq!(found, [2].iter().cloned().collect());

        let found = graph.find_all(
            graph.root_id,
            |x| x.is_meter(),
            petgraph::Direction::Outgoing,
            true,
        )?;
        assert_eq!(found, [2, 3, 6].iter().cloned().collect());

        let found = graph.find_all(
            graph.root_id,
            |x| !x.is_grid() && !graph.is_component_meter(x.component_id()).unwrap_or(false),
            petgraph::Direction::Outgoing,
            true,
        )?;
        assert_eq!(found, [2, 4, 5, 7, 8].iter().cloned().collect());

        let found = graph.find_all(
            6,
            |x| !x.is_grid() && !graph.is_component_meter(x.component_id()).unwrap_or(false),
            petgraph::Direction::Outgoing,
            true,
        )?;
        assert_eq!(found, [7, 8].iter().cloned().collect());

        let found = graph.find_all(
            graph.root_id,
            |x| !x.is_grid() && !graph.is_component_meter(x.component_id()).unwrap_or(false),
            petgraph::Direction::Outgoing,
            false,
        )?;
        assert_eq!(found, [2].iter().cloned().collect());

        let found = graph.find_all(
            graph.root_id,
            |_| true,
            petgraph::Direction::Outgoing,
            false,
        )?;
        assert_eq!(found, [1].iter().cloned().collect());

        let found = graph.find_all(3, |_| true, petgraph::Direction::Outgoing, true)?;
        assert_eq!(found, [3, 4, 5].iter().cloned().collect());

        Ok(())
    }

    /// `find_all` deduplicates on a re-converging (diamond) topology: a node
    /// reachable by two paths is expanded once, not once per path. This is the
    /// shape the `visited` set guards — the tree topologies above never exercise
    /// it. `follow_after_match = true` is the case that actually re-expands (a
    /// matched node keeps expanding), so the diamond apex and its subtree must
    /// still appear exactly once.
    ///
    /// Topology (ids): `Grid:0 → {Meter:1, Meter:2}`, both `→ Inverter:3 → Battery:4`.
    #[test]
    fn test_find_all_dedups_on_diamond() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();
        let meter_a = builder.meter();
        let meter_b = builder.meter();
        let inverter = builder.battery_inverter();
        let battery = builder.battery();

        builder.connect(grid, meter_a);
        builder.connect(grid, meter_b);
        // The inverter is the diamond apex: reachable via both meters.
        builder.connect(meter_a, inverter);
        builder.connect(meter_b, inverter);
        builder.connect(inverter, battery);

        let graph = builder.build(None)?;

        // follow_after_match = true: the inverter matches yet keeps expanding, and
        // it is reached by both meters — it and its battery must appear once each.
        let found = graph.find_all(
            grid.component_id(),
            |n| !n.is_grid(),
            petgraph::Direction::Outgoing,
            true,
        )?;
        assert_eq!(
            found,
            BTreeSet::from([
                meter_a.component_id(),
                meter_b.component_id(),
                inverter.component_id(),
                battery.component_id(),
            ])
        );

        // A predicate matching only the apex's subtree still reaches it through
        // the diamond — the apex is expanded, not skipped before its successors.
        let found = graph.find_all(
            grid.component_id(),
            |n| n.is_battery(),
            petgraph::Direction::Outgoing,
            true,
        )?;
        assert_eq!(found, BTreeSet::from([battery.component_id()]));

        Ok(())
    }

    /// An inactive meter is transparent to the visible view: its neighbours see
    /// through it in both directions, while the crate-internal view still stops
    /// at it.
    ///
    /// Topology: `Grid → Meter (inactive) → PvInverter`.
    #[test]
    fn test_inactive_meter_is_transparent() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();
        let meter =
            builder.add_component_with_mode(ComponentCategory::Meter, OperationalMode::Inactive);
        let pv = builder.solar_inverter();
        builder.connect(grid, meter);
        builder.connect(meter, pv);
        let graph = builder.build(None)?;

        assert_eq!(
            ids(graph.visible_successors(grid.component_id())?),
            vec![pv.component_id()]
        );
        assert_eq!(
            ids(graph.visible_predecessors(pv.component_id())?),
            vec![grid.component_id()]
        );
        assert_eq!(
            ids(graph.effective_successors(grid.component_id())?),
            vec![meter.component_id()]
        );
        Ok(())
    }

    /// The root stays visible even when inactive: hiding it would hide the
    /// whole graph.
    ///
    /// Topology: `Grid (inactive) → Meter`.
    #[test]
    fn test_inactive_root_stays_visible() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.add_component_with_mode(
            ComponentCategory::GridConnectionPoint,
            OperationalMode::Inactive,
        );
        let meter = builder.meter();
        builder.connect(grid, meter);
        let graph = builder.build(None)?;

        assert_eq!(
            ids(graph.visible_predecessors(meter.component_id())?),
            vec![grid.component_id()]
        );
        assert_eq!(
            ids(graph.visible_successors(grid.component_id())?),
            vec![meter.component_id()]
        );
        Ok(())
    }

    /// An inactive leaf simply disappears from the visible view.
    ///
    /// Topology: `Grid → Meter → BatteryInverter → Battery (inactive)`.
    #[test]
    fn test_inactive_leaf_is_hidden() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();
        let meter = builder.meter();
        let inverter = builder.battery_inverter();
        let battery = builder.add_component_with_mode(
            ComponentCategory::Battery(BatteryType::LiIon),
            OperationalMode::Inactive,
        );
        builder.connect(grid, meter);
        builder.connect(meter, inverter);
        builder.connect(inverter, battery);
        let graph = builder.build(None)?;

        assert!(
            graph
                .visible_successors(inverter.component_id())?
                .next()
                .is_none()
        );
        assert_eq!(
            ids(graph.effective_successors(inverter.component_id())?),
            vec![battery.component_id()]
        );
        Ok(())
    }

    /// An inactive battery or hybrid inverter is not walked through: it and the
    /// battery behind it are pruned from the visible view.
    ///
    /// Topology: `Grid → Meter → Inverter (inactive) → Battery`.
    #[test]
    fn test_inactive_battery_or_hybrid_inverter_prunes_its_battery() -> Result<(), Error> {
        for inverter_type in [InverterType::Battery, InverterType::Hybrid] {
            let mut builder = ComponentGraphBuilder::new();
            let grid = builder.grid();
            let meter = builder.meter();
            let inverter = builder.add_component_with_mode(
                ComponentCategory::Inverter(inverter_type),
                OperationalMode::Inactive,
            );
            let battery = builder.battery();
            builder.connect(grid, meter);
            builder.connect(meter, inverter);
            builder.connect(inverter, battery);
            let graph = builder.build(None)?;

            assert!(
                graph
                    .visible_successors(meter.component_id())?
                    .next()
                    .is_none(),
                "{inverter_type}"
            );
            assert!(
                graph
                    .visible_predecessors(battery.component_id())?
                    .next()
                    .is_none(),
                "{inverter_type}"
            );
            // The internal view still sees the whole chain.
            assert_eq!(
                ids(graph.effective_successors(meter.component_id())?),
                vec![inverter.component_id()]
            );
        }
        Ok(())
    }

    /// A battery still reachable through an active inverter is kept, even
    /// though its other inverter is inactive.
    ///
    /// Topology: `Grid → Meter → {BatteryInverter (inactive), BatteryInverter}
    /// → Battery`.
    #[test]
    fn test_shared_battery_survives_one_inactive_inverter() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();
        let meter = builder.meter();
        let dead = builder.add_component_with_mode(
            ComponentCategory::Inverter(InverterType::Battery),
            OperationalMode::Inactive,
        );
        let live = builder.battery_inverter();
        let battery = builder.battery();
        builder.connect(grid, meter);
        builder.connect(meter, dead);
        builder.connect(meter, live);
        builder.connect(dead, battery);
        builder.connect(live, battery);
        let graph = builder.build(None)?;

        assert_eq!(
            ids(graph.visible_successors(meter.component_id())?),
            vec![live.component_id()]
        );
        assert_eq!(
            ids(graph.visible_predecessors(battery.component_id())?),
            vec![live.component_id()]
        );
        assert_eq!(
            ids(graph.visible_successors(live.component_id())?),
            vec![battery.component_id()]
        );
        Ok(())
    }

    /// Lookup by id is explicit, so a hidden component stays resolvable.
    ///
    /// Topology: `Grid → Meter (inactive) → PvInverter`.
    #[test]
    fn test_component_resolves_hidden_id() -> Result<(), Error> {
        let mut builder = ComponentGraphBuilder::new();
        let grid = builder.grid();
        let meter =
            builder.add_component_with_mode(ComponentCategory::Meter, OperationalMode::Inactive);
        let pv = builder.solar_inverter();
        builder.connect(grid, meter);
        builder.connect(meter, pv);
        let graph = builder.build(None)?;

        assert_eq!(
            graph.component(meter.component_id())?.component_id(),
            meter.component_id()
        );
        Ok(())
    }
}
