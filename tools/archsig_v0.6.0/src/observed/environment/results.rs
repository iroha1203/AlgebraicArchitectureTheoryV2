//! 再利用する計算結果と、その入力同一性の記録。
use super::*;

#[derive(Default)]
pub(crate) struct ResultStore {
    // 種類ごとの型をキーとし、元入力とArcの寿命をそのまま保持する。
    verified: RefCell<BTreeMap<std::any::TypeId, Box<dyn std::any::Any>>>,
    pub(super) dotted_inputs: RefCell<DottedInputCache>,
    // 純粋AST計算の入力値と全分析Contextだけをキーにする。Graphを読まず、
    // producer/証拠の照合成功は保存しない。それらは各不変借用で再検査する。
    pub(super) scoped_values: RefCell<Vec<(ScopedKey, SourceValue, BTreeSet<Fact>)>>,
    pub(super) cache: RefCell<ValidationCache>,
    pub(super) validation_snapshot: RefCell<Option<ValidationSnapshot>>,
}

impl ResultStore {
    pub(in crate::observed) fn verified<T: 'static>(&self) -> std::cell::Ref<'_, [T]> {
        let key = std::any::TypeId::of::<T>();
        std::cell::Ref::map(self.verified.borrow(), |entries| {
            entries
                .get(&key)
                .map(|values| {
                    values
                        .downcast_ref::<Vec<T>>()
                        .expect("種類キーと保存型が一致")
                        .as_slice()
                })
                .unwrap_or(&[])
        })
    }
    pub(in crate::observed) fn remember<T: 'static>(&self, value: T) {
        let mut entries = self.verified.borrow_mut();
        let values = entries
            .entry(std::any::TypeId::of::<T>())
            .or_insert_with(|| Box::new(Vec::<T>::new()));
        values
            .downcast_mut::<Vec<T>>()
            .expect("種類キーと保存型が一致")
            .push(value);
    }
}

#[cfg(test)]
mod tests {
    use super::ResultStore;
    use std::sync::Arc;

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
