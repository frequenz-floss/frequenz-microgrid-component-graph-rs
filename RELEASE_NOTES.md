# Frequenz Component Graph Release Notes

## Summary

<!-- Here goes a general summary of what this release is about -->

## Upgrading

- The query API now has two views, and the unprefixed methods are gone. `components()`, `connections()`, `predecessors()` and `successors()` no longer exist. `raw_components()` and `raw_connections()` return every component and connection, as `components()` and `connections()` did. `raw_predecessors()` and `raw_successors()` are unchanged. `visible_components()`, `visible_predecessors()` and `visible_successors()` hide pass-through components and components whose operational mode is `Inactive`: pass-throughs and inactive components other than battery and hybrid inverters are walked through, so their neighbours see each other directly, while an inactive battery or hybrid inverter is not walked through, and every component only reachable through it is hidden as well. The grid connection point stays visible whatever its mode. Called on a hidden component, `visible_predecessors()` and `visible_successors()` yield nothing and do not error; use `component(id)` or the `raw_` walks to inspect one. There is no replacement for the old `predecessors()` and `successors()`, which walked past pass-throughs but still returned inactive components; pick `raw_` or `visible_` depending on whether inactive components matter to the caller. `component(id)` is unchanged and still resolves hidden ids. The iterator type `Connections` is renamed to `RawConnections`. Validators, formula generators and the meter role checks keep seeing inactive components.

## New Features

- `visible_connections()` lists the connections of the visible view as `(source_id, destination_id)` pairs. Each visible component is paired with each of its visible successors, so hidden components between the two are folded into one pair. Together with `visible_components()` it describes the visible graph.

## Bug Fixes

<!-- Here goes notable bug fixes that are worth a special mention or explanation -->
