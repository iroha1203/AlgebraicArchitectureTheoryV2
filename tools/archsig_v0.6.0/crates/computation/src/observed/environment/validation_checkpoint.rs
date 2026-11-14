//! Retain an existing validation prefix while releasing a scratch body.
//! Fixed successes stay in place; only additions after the prefix are undone.
use super::*;

/// Successful keys are append-only within one validation epoch. Recording starts
/// only when a closed-body caller establishes a rollback prefix; raw evaluation
/// does not keep a second copy of its successful keys.
#[derive(Default)]
pub(super) struct SuccessSet {
    keys: BTreeSet<NodeRefKey>,
    additions: Option<Vec<NodeRefKey>>,
}
impl SuccessSet {
    pub(super) fn contains(&self, key: &NodeRefKey) -> bool {
        self.keys.contains(key)
    }
    pub(super) fn insert(&mut self, key: NodeRefKey) -> bool {
        if !self.keys.insert(key) {
            return false;
        }
        if let Some(additions) = &mut self.additions {
            additions.push(key);
        }
        true
    }
    pub(super) fn extend(&mut self, keys: impl IntoIterator<Item = NodeRefKey>) {
        for key in keys {
            self.insert(key);
        }
    }
    fn begin_prefix(&mut self) {
        self.additions = Some(Vec::new());
    }
    fn rollback(&mut self) {
        if let Some(additions) = &mut self.additions {
            for key in additions.drain(..) {
                self.keys.remove(&key);
            }
        }
    }
    #[cfg(test)]
    pub(super) fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }
}

pub(in crate::observed) struct ValidationCheckpoint {
    epoch: std::rc::Rc<()>,
    registry_read: bool,
    sources: usize,
    candidates: usize,
    frames: BTreeSet<(usize, usize)>,
    universal_frames: usize,
    universal_sources: usize,
    iterations: BTreeSet<IterationKey>,
    seeds: BTreeSet<completion::MemoKey>,
    domains: BTreeSet<completion::DomainKey>,
    cases: BTreeSet<completion::MemoKey>,
    slots: BTreeSet<completion::SlotsKey>,
    verified: results::VerifiedCheckpoint,
    snapshot: Option<ValidationSnapshot>,
}
impl ResultStore {
    fn checkpoint_validation(&self) -> ValidationCheckpoint {
        let mut c = self.cache.borrow_mut();
        // One active rollback region per cache. A later capture supersedes the
        // earlier token, so a stale token can only clear the session, not retain
        // successes from a different branch at reused indices.
        c.epoch = std::rc::Rc::new(());
        c.checked.begin_prefix();
        c.rechecked.begin_prefix();
        ValidationCheckpoint {
            epoch: c.epoch.clone(),
            registry_read: c.registry_read,
            sources: c.sources.entries.len(),
            candidates: c.context_candidates.checkpoint(),
            frames: c.frames.keys().copied().collect(),
            universal_frames: c.universal_frames.len(),
            universal_sources: c.universal_sources.len(),
            iterations: c.iterations.keys().copied().collect(),
            seeds: c.completion_seeds.keys().copied().collect(),
            domains: c.completion_domains.keys().copied().collect(),
            cases: c.completion_cases.keys().copied().collect(),
            slots: c.completion_slots.keys().cloned().collect(),
            verified: self.checkpoint_verified(),
            snapshot: self.validation_snapshot.borrow().clone(),
        }
    }
    fn rollback_validation(&self, prefix: &ValidationCheckpoint) -> bool {
        // Pure AST memo keys contain Scope/Context references too. Their values
        // are cheap to recompute; never let scratch identities survive reuse.
        self.scoped_values.borrow_mut().clear();
        if !std::rc::Rc::ptr_eq(&self.cache.borrow().epoch, &prefix.epoch) {
            // A nested failure/session reset invalidated the original proof.
            // Do not restore keys or verified sources from a previous epoch.
            self.clear_validation();
            self.validation_snapshot.replace(None);
            return false;
        }
        let mut c = self.cache.borrow_mut();
        c.registry_read = prefix.registry_read;
        c.checked.rollback();
        c.rechecked.rollback();
        c.sources.entries.truncate(prefix.sources);
        c.sources.by_context.retain(|_, positions| {
            positions.retain(|&position| position < prefix.sources);
            !positions.is_empty()
        });
        c.context_candidates.rollback(prefix.candidates);
        c.frames.retain(|key, _| prefix.frames.contains(key));
        c.universal_frames.truncate(prefix.universal_frames);
        c.universal_sources.truncate(prefix.universal_sources);
        c.iterations
            .retain(|key, _| prefix.iterations.contains(key));
        c.completion_seeds
            .retain(|key, _| prefix.seeds.contains(key));
        c.completion_domains
            .retain(|key, _| prefix.domains.contains(key));
        c.completion_cases
            .retain(|key, _| prefix.cases.contains(key));
        c.completion_slots
            .retain(|key, _| prefix.slots.contains(key));
        drop(c);
        self.rollback_verified(&prefix.verified);
        self.validation_snapshot.replace(prefix.snapshot.clone());
        true
    }
}
impl Environment<'_> {
    /// Capture once after the fixed Graph prefix is locally validated.
    pub(in crate::observed) fn validation_checkpoint(
        &self,
    ) -> Result<ValidationCheckpoint, InternalError> {
        if self.state.validation_depth.get() != 0 {
            return Err(internal!("検査中のsessionを反復prefixとして保存できない"));
        }
        Ok(self.results.checkpoint_validation())
    }
    /// Only after the scratch Graph suffix has been discarded and its immutable
    /// prefix verified unchanged. No checkpoints/analysis are run after Stop.
    /// False means a nested reset invalidated the prefix cache; nothing revived.
    pub(in crate::observed) fn rollback_validation(
        &self,
        prefix: &ValidationCheckpoint,
    ) -> Result<bool, InternalError> {
        if self.state.validation_depth.get() != 0 {
            return Err(internal!("検査中のsessionを反復prefixへ戻せない"));
        }
        Ok(self.results.rollback_validation(prefix))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    fn analysis(value: i32) -> SourceAnalysis {
        SourceAnalysis {
            condition_failed: false,
            condition_pending: false,
            symbolic: None,
            comparison: None,
            scope: Scope::default(),
            known_value: Some(Scalar::Z(value.into())),
            affine: None,
            missing: None,
            support: vec![].into(),
            scalar_scope: None,
        }
    }
    #[test]
    fn validation_rollback_removes_new_prefix_keys_but_keeps_duplicate_successes() {
        let store = ResultStore::default();
        let context = crate::observed::call::Context::default();
        store.cache.borrow_mut().checked.insert((context, 4));
        assert!(store.cache.borrow().checked.additions.is_none());
        let prefix = store.checkpoint_validation();
        for _ in 0..3 {
            let mut cache = store.cache.borrow_mut();
            assert!(!cache.checked.insert((context, 4)));
            assert!(cache.checked.insert((context, 0)));
            cache.rechecked.extend([(context, 0), (context, 0)]);
            drop(cache);
            assert!(store.rollback_validation(&prefix));
            let cache = store.cache.borrow();
            assert!(cache.checked.contains(&(context, 4)));
            assert!(!cache.checked.contains(&(context, 0)));
            assert!(cache.rechecked.is_empty());
        }
    }
    #[test]
    fn validation_rollback_superseded_prefix_cannot_retain_new_branch_successes() {
        let store = ResultStore::default();
        let context = crate::observed::call::Context::default();
        store.cache.borrow_mut().checked.insert((context, 0));
        let first = store.checkpoint_validation();
        store.cache.borrow_mut().checked.insert((context, 1));
        let second = store.checkpoint_validation();
        store.cache.borrow_mut().checked.insert((context, 2));
        assert!(store.rollback_validation(&second));
        assert!(store.cache.borrow().checked.contains(&(context, 1)));
        assert!(!store.cache.borrow().checked.contains(&(context, 2)));
        assert!(!store.rollback_validation(&first));
        assert!(store.cache.borrow().checked.is_empty());
        assert!(!store.rollback_validation(&second));
        assert!(store.cache.borrow().checked.is_empty());
    }
    #[test]
    fn validation_rollback_keeps_prefix_sources_and_drops_scratch_owners() {
        let store = ResultStore::default();
        let context = crate::observed::call::Context::default();
        let old = Arc::new(3i32);
        let scratch = Arc::new(4i32);
        let persistent = Arc::new(5u32);
        let old_weak = Arc::downgrade(&old);
        let scratch_weak = Arc::downgrade(&scratch);
        store.remember(old.clone());
        store.remember(persistent.clone());
        store.cache.borrow_mut().checked.insert((context, 0));
        store
            .cache
            .borrow_mut()
            .sources
            .insert(context, (1, (2, 3), vec![], analysis(7)));
        let prefix = store.checkpoint_validation();
        store.remember(scratch.clone());
        store.cache.borrow_mut().checked.insert((context, 1));
        store.cache.borrow_mut().rechecked.insert((context, 0));
        store
            .cache
            .borrow_mut()
            .sources
            .insert(context, (1, (2, 3), vec![], analysis(8)));
        store.cache.borrow_mut().completion_slots.insert(
            (
                0,
                context,
                1,
                crate::observed::call::CompletionMode::FiniteDomain,
                vec![0],
            ),
            (vec![], vec![], vec![]),
        );
        drop(old);
        drop(scratch);
        assert!(store.rollback_validation(&prefix));
        assert!(old_weak.upgrade().is_some());
        assert!(scratch_weak.upgrade().is_none());
        assert!(store.source_checked(&persistent));
        let c = store.cache.borrow();
        assert_eq!(c.checked.keys, BTreeSet::from([(context, 0)]));
        assert!(c.rechecked.is_empty());
        assert!(c.completion_slots.is_empty());
        assert_eq!(c.sources.entries.len(), 1);
        assert_eq!(
            c.sources.get(context, 1, (2, 3), &[]).unwrap().known_value,
            Some(Scalar::Z(7.into()))
        );
    }
    #[test]
    fn validation_rollback_does_not_revive_a_cleared_session_at_reused_indices() {
        let store = ResultStore::default();
        let context = crate::observed::call::Context::default();
        let old = Arc::new(3i32);
        let old_weak = Arc::downgrade(&old);
        store.remember(old);
        store.cache.borrow_mut().checked.insert((context, 0));
        let prefix = store.checkpoint_validation();
        store.clear_validation();
        assert!(old_weak.upgrade().is_none());
        store.cache.borrow_mut().checked.insert((context, 0));
        let replacement = Arc::new(9i32);
        let replacement_weak = Arc::downgrade(&replacement);
        store.remember(replacement);
        assert!(!store.rollback_validation(&prefix));
        assert!(store.cache.borrow().checked.is_empty());
        assert!(store.validation_snapshot.borrow().is_none());
        assert!(replacement_weak.upgrade().is_none());
    }
    #[test]
    fn validation_rollback_reuses_one_prefix_without_stale_body_source_hits() {
        let store = ResultStore::default();
        let context = crate::observed::call::Context::default();
        let prefix = store.checkpoint_validation();
        for value in [11, 29, -5] {
            assert!(
                store
                    .cache
                    .borrow()
                    .sources
                    .get(context, 2, (2, 3), &[])
                    .is_none()
            );
            store
                .cache
                .borrow_mut()
                .sources
                .insert(context, (2, (2, 3), vec![], analysis(value)));
            assert_eq!(
                store
                    .cache
                    .borrow()
                    .sources
                    .get(context, 2, (2, 3), &[])
                    .unwrap()
                    .known_value,
                Some(Scalar::Z(value.into()))
            );
            assert!(store.rollback_validation(&prefix));
            assert!(store.cache.borrow().sources.by_context.is_empty());
        }
    }
    #[allow(dead_code)]
    mod fixture {
        include!("../../../../../tests/common/primitive_valuation_data.rs");
    }
    #[test]
    fn validation_rollback_preserves_committed_prefix_after_stop_without_checkpoints() {
        use std::sync::atomic::{AtomicI32, Ordering};
        let flag = Arc::new(AtomicI32::new(0));
        let control = Control::from_signal_flag(flag.clone(), 2, 15);
        let inputs = fixture::inputs();
        let env = Environment::new(&inputs, &control).unwrap();
        let context = crate::observed::call::Context::default();
        env.results.cache.borrow_mut().checked.insert((context, 0));
        let prefix = env.validation_checkpoint().unwrap();
        env.results.cache.borrow_mut().checked.insert((context, 1));
        flag.store(2, Ordering::Relaxed);
        assert_eq!(control.stop_reason(), Some(Signal::Int));
        assert!(env.rollback_validation(&prefix).unwrap());
        assert_eq!(
            env.results.cache.borrow().checked.keys,
            BTreeSet::from([(context, 0)])
        );
        assert_eq!(control.stop_reason(), Some(Signal::Int));
        let _depth = env.state.validation_depth.scoped(1);
        assert!(env.validation_checkpoint().is_err());
        assert!(env.rollback_validation(&prefix).is_err());
    }
}
