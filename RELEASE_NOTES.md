# Frequenz Component Graph Release Notes

## Bug Fixes

- `ComponentGraph::try_new` no longer fails on a component of category `Unspecified` that has no connections. It logs a warning for the component, and `components()` and `component()` can return it. Aggregate and per-category formulas leave the component out, even if it is a real device. A component of category `Unspecified` that has a connection still makes `try_new` fail.
