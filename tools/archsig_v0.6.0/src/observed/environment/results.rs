//! 再利用する計算結果と、その入力同一性の記録。
use super::*;

#[derive(Default)]
pub(crate) struct ResultStore {
    // 元三入力にのみ依存する不変族。Arcを保持し、同一性の再利用を防ぐ。
    pub(in crate::observed) verified_view_transports:
        RefCell<Vec<crate::observed::object_view_map::KernelCacheEntry>>,
    pub(in crate::observed) verified_law_transports:
        RefCell<Vec<crate::observed::object_law_map::KernelCacheEntry>>,
    pub(super) verified_relation_families:
        RefCell<Vec<std::sync::Arc<crate::observed::public_compare::relation_sources::Family>>>,
    pub(in crate::observed) verified_finite_law_diagrams:
        RefCell<Vec<std::sync::Arc<crate::observed::finite_law_diagram::Source>>>,
    pub(in crate::observed) verified_polynomial_law_diagrams:
        RefCell<Vec<std::sync::Arc<crate::observed::polynomial_law_diagram::Source>>>,
    pub(in crate::observed) verified_object_components:
        RefCell<Vec<std::sync::Arc<crate::observed::object_component_diagram::Source>>>,
    pub(in crate::observed) verified_internal_arrows:
        RefCell<Vec<std::sync::Arc<crate::observed::internal_arrow_diagram::Source>>>,
    pub(in crate::observed) verified_circuit_patterns:
        RefCell<Vec<std::sync::Arc<crate::observed::circuit_pattern::Source>>>,
    pub(super) dotted_inputs: RefCell<DottedInputCache>,
    // 純粋AST計算の入力値と全分析Contextだけをキーにする。Graphを読まず、
    // producer/証拠の照合成功は保存しない。それらは各不変借用で再検査する。
    pub(super) scoped_values: RefCell<Vec<(ScopedKey, SourceValue, BTreeSet<Fact>)>>,
    pub(super) cache: RefCell<ValidationCache>,
    pub(super) validation_snapshot: RefCell<Option<ValidationSnapshot>>,
}
