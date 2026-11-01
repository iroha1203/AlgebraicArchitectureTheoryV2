//! 再利用する計算結果と、その入力同一性の記録。
use super::super::result_kind::ResultKind;
use super::*;
use std::{
    cell::{Ref, RefCell},
    sync::Arc,
};

/// 保存する値が、型の決まった欄を選ぶ。実行時の型判定は行わない。
pub(in crate::observed) trait StoredValue: Sized {
    fn entries(table: &VerifiedResults) -> &RefCell<Vec<Self>>;
}

macro_rules! result_table {
    ($($(#[$attr:meta])* $lifetime:ident $field:ident: $value:ty),* $(,)?) => {
        #[derive(Default)]
        pub(in crate::observed) struct VerifiedResults {
            $($(#[$attr])* $field: RefCell<Vec<$value>>),*
        }
        $($(#[$attr])* impl StoredValue for $value {
            fn entries(table: &VerifiedResults) -> &RefCell<Vec<Self>> { &table.$field }
        })*
        impl VerifiedResults {
            fn clear_session(&self) {
                $($(#[$attr])* { result_table!(@clear $lifetime self.$field); })*
            }
        }
    };
    (@clear persistent $field:expr) => {};
    (@clear session $field:expr) => { *$field.borrow_mut() = Vec::new(); };
}

// Environmentと同じ期間保持する値と、Graphの検査区間に限る値を区別する。
// 各欄を別々に借用するので、ある種類の読取り中にも別の種類を検査できる。
result_table! {
    persistent finite_laws: <super::super::finite_law_diagram::Data as ResultKind>::Stored,
    persistent polynomial_laws: <super::super::polynomial_law_diagram::Data as ResultKind>::Stored,
    persistent object_components: <super::super::object_component_diagram::Data as ResultKind>::Stored,
    persistent internal_arrows: <super::super::internal_arrow_diagram::Data as ResultKind>::Stored,
    persistent circuits: <super::super::circuit_pattern::Data as ResultKind>::Stored,
    persistent view_kernels: super::super::object_view_map::KernelCacheEntry,
    persistent law_kernels: super::super::object_law_map::KernelCacheEntry,
    persistent relation_families: Arc<super::super::public_compare::relation_sources::Family>,
    session changes: <super::super::change_result::Data as ResultKind>::Stored,
    session quotients: <super::super::quotient_result::Data as ResultKind>::Stored,
    session locals: <super::super::local_result::Data as ResultKind>::Stored,
    session object_maps: <super::super::object_map_result::Data as ResultKind>::Stored,
    session builds: <super::super::build_result::Data as ResultKind>::Stored,
    #[cfg(test)] persistent test_u32: Arc<u32>,
    #[cfg(test)] persistent test_u64: Arc<u64>,
    #[cfg(test)] session test_i32: Arc<i32>,
}

#[derive(Default)]
pub(crate) struct ResultStore {
    verified: VerifiedResults,
    pub(super) dotted_inputs: RefCell<DottedInputCache>,
    // 純粋AST計算の入力値と全分析Contextだけをキーにする。Graphを読まず、
    // producer/証拠の照合成功は保存しない。それらは各不変借用で再検査する。
    pub(super) scoped_values: RefCell<Vec<(ScopedKey, SourceValue, BTreeSet<Fact>)>>,
    pub(super) cache: RefCell<ValidationCache>,
    pub(super) validation_snapshot: RefCell<Option<ValidationSnapshot>>,
}

impl ResultStore {
    pub(in crate::observed) fn verified<T: StoredValue>(&self) -> Ref<'_, [T]> {
        Ref::map(T::entries(&self.verified).borrow(), |values| {
            values.as_slice()
        })
    }
    pub(in crate::observed) fn remember<T: StoredValue>(&self, value: T) {
        T::entries(&self.verified).borrow_mut().push(value);
    }
    pub(in crate::observed) fn source_checked<T>(&self, source: &Arc<T>) -> bool
    where
        Arc<T>: StoredValue,
    {
        self.verified::<Arc<T>>()
            .iter()
            .any(|saved| Arc::ptr_eq(saved, source))
    }
    pub(super) fn clear_validation(&self) {
        self.verified.clear_session();
        *self.cache.borrow_mut() = ValidationCache::default();
    }
}

#[cfg(test)]
mod tests {
    use super::ResultStore;
    use std::sync::Arc;

    #[test]
    fn validation_reset_drops_session_sources_and_keeps_input_results() {
        let store = ResultStore::default();
        let persistent = Arc::new(7u32);
        let session = Arc::new(8i32);
        let persistent_weak = Arc::downgrade(&persistent);
        let session_weak = Arc::downgrade(&session);
        store.remember(persistent.clone());
        store.remember(session.clone());
        assert!(store.source_checked(&persistent));
        assert!(store.source_checked(&session));
        assert!(
            !store.source_checked(&Arc::new(7u32)),
            "same value is not source identity"
        );
        drop(persistent);
        drop(session);
        let held = store.verified::<Arc<u32>>();
        store.clear_validation();
        assert_eq!(held.len(), 1);
        assert!(persistent_weak.upgrade().is_some());
        assert!(session_weak.upgrade().is_none());
        assert!(store.verified::<Arc<i32>>().is_empty());
        drop(held);
        drop(store);
        assert!(persistent_weak.upgrade().is_none());
    }

    #[test]
    fn verified_kinds_are_separate_and_keep_source_identity_alive() {
        let store = ResultStore::default();
        assert!(store.verified::<Arc<u32>>().is_empty());
        let source = Arc::new(7u32);
        let identity = Arc::downgrade(&source);
        store.remember(source.clone());
        store.remember(Arc::new(7u64));
        store.remember(Arc::new(11u32));
        assert!(Arc::ptr_eq(&store.verified::<Arc<u32>>()[0], &source));
        assert_eq!(
            store
                .verified::<Arc<u32>>()
                .iter()
                .map(|v| **v)
                .collect::<Vec<_>>(),
            [7, 11]
        );
        assert_eq!(
            store
                .verified::<Arc<u64>>()
                .iter()
                .map(|v| **v)
                .collect::<Vec<_>>(),
            [7]
        );
        // 別の読取り借用があっても、空の種類の照会は可変借用を取らない。
        let held = store.verified::<Arc<u32>>();
        assert!(store.verified::<Arc<i32>>().is_empty());
        drop(held);
        drop(source);
        assert!(identity.upgrade().is_some());
        drop(store);
        assert!(identity.upgrade().is_none());
    }
}
