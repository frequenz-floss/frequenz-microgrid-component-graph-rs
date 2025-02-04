// License: MIT
// Copyright © 2024 Frequenz Energy-as-a-Service GmbH

//! This module contains the configuration options for the `ComponentGraph`.

/// Configuration options for the `ComponentGraph`.
#[derive(Clone, Default, Debug)]
pub struct ComponentGraphConfig {
    /// Whether to allow validation errors on components.  When this is `true`,
    /// the graph will be built even if there are validation errors on
    /// components.
    pub allow_component_validation_failures: bool,

    /// Whether to allow unconnected components in the graph, that are not
    /// reachable from the root.
    pub allow_unconnected_components: bool,

    /// Whether to allow untyped inverters in the graph.  When this is `true`,
    /// inverters that have `InverterType::Unspecified` will be assumed to be
    /// Battery inverters.
    pub allow_unspecified_inverters: bool,

    /// Whether to disable fallback components in generated formulas.  When this
    /// is `true`, the formulas will not include fallback components.
    pub disable_fallback_components: bool,
}
