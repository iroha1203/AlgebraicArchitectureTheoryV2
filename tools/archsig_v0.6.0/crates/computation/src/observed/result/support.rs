//! 支持は直factと共有因子の和。Fact列への射影は消費側が明示する。
use super::{Fact, FlatFacts, ValidationFailure};
use archsig_common::control::{Checkpoint, Control};
use std::{collections::BTreeSet, sync::Arc};

#[derive(Clone)]
pub(crate) struct Support(Arc<Expression>);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UnionOrder {
    Fact,
    CanonicalWire,
}
#[derive(Debug)]
struct Expression {
    own: FlatFacts,
    factors: Vec<Support>,
    union: Option<UnionOrder>,
}
impl Default for Support {
    fn default() -> Self {
        Self::from(Vec::new())
    }
}
impl From<Vec<Fact>> for Support {
    fn from(own: Vec<Fact>) -> Self {
        Self::from(FlatFacts::from(own))
    }
}
impl From<FlatFacts> for Support {
    fn from(own: FlatFacts) -> Self {
        Self(Arc::new(Expression {
            own,
            factors: Vec::new(),
            union: None,
        }))
    }
}
impl Support {
    /// 入力Scalar/Node/SourceAnalysis全体は保持しない。
    pub(crate) fn sum(mut own: Vec<Fact>, factors: impl IntoIterator<Item = Support>) -> Self {
        own.sort();
        own.dedup();
        let factors: Vec<_> = factors.into_iter().collect();
        if own.is_empty() && factors.len() == 1 {
            let factor = &factors[0];
            // 同じ比較順のunion、または空/単Fact葉だけは再正規化が恒等。
            // 未整列・重複のある一般leafやconcatは共有短絡しない。
            if factor.0.union == Some(UnionOrder::Fact)
                || (factor.0.factors.is_empty() && factor.0.own.len() <= 1)
            {
                return factor.clone();
            }
        }
        Self(Arc::new(Expression {
            own: own.into(),
            factors,
            union: Some(UnionOrder::Fact),
        }))
    }
    /// 旧native factoryのwire canonical順を保つunion。
    pub(crate) fn sum_canonical(
        mut own: Vec<Fact>,
        factors: impl IntoIterator<Item = Support>,
    ) -> Self {
        own.sort_by_key(|fact| fact.wire().canonical());
        own.dedup();
        Self(Arc::new(Expression {
            own: own.into(),
            factors: factors.into_iter().collect(),
            union: Some(UnionOrder::CanonicalWire),
        }))
    }
    /// 元factoryが整列・重複除去しなかった列の追記。
    pub(crate) fn concat(factors: impl IntoIterator<Item = Support>) -> Self {
        Self(Arc::new(Expression {
            own: FlatFacts::default(),
            factors: factors.into_iter().collect(),
            union: None,
        }))
    }
    /// 表現の高速一致。意味上のFact集合同値とは区別する。
    pub(crate) fn same_recipe(&self, other: &Self) -> bool {
        self.compare_recipe(other, None)
            .expect("停止Control無しの表現比較")
    }
    fn compare_recipe(
        &self,
        other: &Self,
        control: Option<&Control>,
    ) -> Result<bool, ValidationFailure> {
        if Arc::ptr_eq(&self.0, &other.0) {
            return Ok(true);
        }
        let mut pending = vec![(self, other)];
        let mut visited = BTreeSet::new();
        while let Some((left, right)) = pending.pop() {
            if let Some(control) = control {
                control
                    .checkpoint(Checkpoint::FiniteIteration)
                    .map_err(ValidationFailure::Stop)?;
            }
            if Arc::ptr_eq(&left.0, &right.0) {
                continue;
            }
            if !visited.insert((
                Arc::as_ptr(&left.0) as usize,
                Arc::as_ptr(&right.0) as usize,
            )) {
                continue;
            }
            if left.0.union != right.0.union
                || left.0.own != right.0.own
                || left.0.factors.len() != right.0.factors.len()
            {
                return Ok(false);
            }
            pending.extend(left.0.factors.iter().zip(&right.0.factors));
        }
        Ok(true)
    }
    pub(crate) fn matches_flat(
        &self,
        facts: &[Fact],
        control: &Control,
    ) -> Result<bool, ValidationFailure> {
        if self.0.factors.is_empty() {
            return Ok(self.0.own.as_slice() == facts);
        }
        Ok(self.materialize(control)?.as_slice() == facts)
    }
    pub(crate) fn is_empty(&self, control: &Control) -> Result<bool, ValidationFailure> {
        Ok(!self.any_fact(control, |_| true)?)
    }
    pub(crate) fn direct_facts(&self) -> &[Fact] {
        &self.0.own
    }
    /// 与えられた実producerから得た支持を検査してから比較する。
    /// 共有handleは最適化だけであり、別factorization/旧flatも拒否しない。
    pub(crate) fn same_facts(
        &self,
        other: &Self,
        control: &Control,
    ) -> Result<bool, ValidationFailure> {
        if self.compare_recipe(other, Some(control))? {
            return Ok(true);
        }
        Ok(self.materialize(control)? == other.materialize(control)?)
    }
    /// 順序非依存のquery専用。同じ共有因子は一度だけ訪問する。
    /// 元配列の順序・重複を配送するAPIとしては使用しない。
    pub(crate) fn visit_facts(
        &self,
        control: &Control,
        mut visit: impl FnMut(&Fact),
    ) -> Result<(), ValidationFailure> {
        self.try_visit_facts(control, |fact| {
            visit(fact);
            Ok(())
        })
    }
    pub(crate) fn try_visit_facts(
        &self,
        control: &Control,
        mut visit: impl FnMut(&Fact) -> Result<(), ValidationFailure>,
    ) -> Result<(), ValidationFailure> {
        let mut pending = vec![self];
        let mut visited = BTreeSet::new();
        while let Some(support) = pending.pop() {
            control
                .checkpoint(Checkpoint::FiniteIteration)
                .map_err(ValidationFailure::Stop)?;
            if !visited.insert(Arc::as_ptr(&support.0) as usize) {
                continue;
            }
            for fact in &support.0.own {
                control
                    .checkpoint(Checkpoint::FiniteIteration)
                    .map_err(ValidationFailure::Stop)?;
                visit(fact)?;
            }
            pending.extend(support.0.factors.iter());
        }
        Ok(())
    }
    pub(crate) fn any_fact(
        &self,
        control: &Control,
        mut predicate: impl FnMut(&Fact) -> bool,
    ) -> Result<bool, ValidationFailure> {
        let mut pending = vec![self];
        let mut visited = BTreeSet::new();
        while let Some(support) = pending.pop() {
            control
                .checkpoint(Checkpoint::FiniteIteration)
                .map_err(ValidationFailure::Stop)?;
            if !visited.insert(Arc::as_ptr(&support.0) as usize) {
                continue;
            }
            for fact in &support.0.own {
                control
                    .checkpoint(Checkpoint::FiniteIteration)
                    .map_err(ValidationFailure::Stop)?;
                if predicate(fact) {
                    return Ok(true);
                }
            }
            pending.extend(support.0.factors.iter());
        }
        Ok(false)
    }
    /// 列/unionそれぞれの順序で最初の一致だけを返す。Fact列は保持しない。
    pub(crate) fn find_fact(
        &self,
        control: &Control,
        mut predicate: impl FnMut(&Fact) -> bool,
    ) -> Result<Option<Fact>, ValidationFailure> {
        let mut pending = vec![self];
        while let Some(support) = pending.pop() {
            control
                .checkpoint(Checkpoint::FiniteIteration)
                .map_err(ValidationFailure::Stop)?;
            if let Some(order) = support.0.union {
                let mut found: Option<Fact> = None;
                support.visit_facts(control, |fact| {
                    if predicate(fact)
                        && found.as_ref().is_none_or(|previous| match order {
                            UnionOrder::Fact => fact < previous,
                            UnionOrder::CanonicalWire => {
                                fact.wire().canonical() < previous.wire().canonical()
                            }
                        })
                    {
                        found = Some(fact.clone());
                    }
                })?;
                if found.is_some() {
                    return Ok(found);
                }
            } else {
                for fact in &support.0.own {
                    control
                        .checkpoint(Checkpoint::FiniteIteration)
                        .map_err(ValidationFailure::Stop)?;
                    if predicate(fact) {
                        return Ok(Some(fact.clone()));
                    }
                }
                pending.extend(support.0.factors.iter().rev());
            }
        }
        Ok(None)
    }
    pub(crate) fn to_flat_facts(&self, control: &Control) -> Result<FlatFacts, ValidationFailure> {
        control
            .checkpoint(Checkpoint::FiniteIteration)
            .map_err(ValidationFailure::Stop)?;
        if self.0.factors.is_empty() {
            return Ok(self.0.own.clone());
        }
        self.materialize(control).map(FlatFacts::from)
    }
    #[cfg(test)]
    pub(crate) fn shares_recipe_storage_for_test(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    #[cfg(test)]
    pub(crate) fn shares_largest_fact_storage_for_test(&self, other: &Self) -> bool {
        fn largest(support: &Support) -> BTreeSet<(usize, usize)> {
            let mut pending = vec![support];
            let mut visited = BTreeSet::new();
            let mut buffers = BTreeSet::new();
            let mut max = 0;
            while let Some(support) = pending.pop() {
                if !visited.insert(Arc::as_ptr(&support.0) as usize) {
                    continue;
                }
                let len = support.0.own.len();
                if len > max {
                    buffers.clear();
                    max = len;
                }
                if len > 0 && len == max {
                    buffers.insert((len, support.0.own.as_ptr() as usize));
                }
                pending.extend(support.0.factors.iter());
            }
            buffers
        }
        let left = largest(self);
        let right = largest(other);
        !left.is_empty() && left.iter().any(|buffer| right.contains(buffer))
    }
    #[cfg(test)]
    pub(crate) fn materialize_for_test(&self) -> Vec<Fact> {
        self.materialize(&Control::unlimited())
            .expect("試験の明示Fact射影")
    }
    /// 既存cold改変試験は、独立したflat列へ射影した後でFactを改変する。
    #[cfg(test)]
    pub(crate) fn materialize_mut_for_test(&mut self) -> &mut Vec<Fact> {
        let facts = self.materialize_for_test();
        *self = Self::from(facts);
        Arc::get_mut(&mut self.0)
            .expect("新しい試験用葉")
            .own
            .make_owned()
    }
    pub(crate) fn materialize(&self, control: &Control) -> Result<Vec<Fact>, ValidationFailure> {
        #[cfg(test)]
        crate::observed::data::observe_actual(
            (0, 0),
            crate::observed::call::Context::default(),
            "support_materialize",
            0,
        );
        let mut output = Vec::new();
        let mut pending = vec![self];
        while let Some(support) = pending.pop() {
            control
                .checkpoint(Checkpoint::FiniteIteration)
                .map_err(ValidationFailure::Stop)?;
            if let Some(order) = support.0.union {
                let mut facts = BTreeSet::new();
                support.visit_facts(control, |fact| {
                    facts.insert(fact.clone());
                })?;
                let mut facts: Vec<_> = facts.into_iter().collect();
                if order == UnionOrder::CanonicalWire {
                    facts.sort_by_key(|fact| fact.wire().canonical());
                }
                output.extend(facts);
            } else {
                for fact in &support.0.own {
                    control
                        .checkpoint(Checkpoint::FiniteIteration)
                        .map_err(ValidationFailure::Stop)?;
                    output.push(fact.clone());
                }
                pending.extend(support.0.factors.iter().rev());
            }
        }
        Ok(output)
    }
}
// Node/Partの表現比較にFact集合の展開を隠さない。rawの意味比較はsame_facts。
impl PartialEq for Support {
    fn eq(&self, other: &Self) -> bool {
        self.same_recipe(other)
    }
}
impl Eq for Support {}

// 最後のrootだけが深い因子鎖を保持していても、Arcの解放を再帰させない。
impl Drop for Expression {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.factors);
        while let Some(Support(expression)) = pending.pop() {
            if let Ok(mut expression) = Arc::try_unwrap(expression) {
                pending.append(&mut expression.factors);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fact(subject: &str) -> Fact {
        Fact::from(archsig_input::archmap::FactData {
            snapshot: "snapshot".into(),
            subject: subject.into(),
            field: None,
            atom: None,
        })
    }
    #[test]
    fn leaf_preserves_order_and_duplicates_but_union_normalizes() {
        let control = Control::unlimited();
        let original = vec![fact("b"), fact("a"), fact("b")];
        let leaf = Support::from(original.clone());
        assert_eq!(leaf.materialize(&control).unwrap(), original);
        let union = Support::sum(vec![], [leaf]);
        assert_eq!(
            union.materialize(&control).unwrap(),
            vec![fact("a"), fact("b")]
        );
    }
    #[test]
    fn alternative_factorization_is_not_rejected_by_pointer_identity() {
        let control = Control::unlimited();
        let composed = Support::sum(vec![fact("b")], [Support::from(vec![fact("a")])]);
        let flat = Support::from(vec![fact("a"), fact("b")]);
        assert!(!composed.same_recipe(&flat));
        assert!(composed.same_facts(&flat, &control).unwrap());
    }
    #[test]
    fn normalized_single_factor_is_shared_without_changing_leaf_sequence_contract() {
        let ordered = Support::sum(vec![], [Support::from(vec![fact("b"), fact("a")])]);
        let shared = Support::sum(vec![], [ordered.clone()]);
        assert!(shared.shares_recipe_storage_for_test(&ordered));
        assert_eq!(shared.materialize_for_test(), vec![fact("a"), fact("b")]);
        let sequence = Support::from(vec![fact("b"), fact("a"), fact("b")]);
        let normalized = Support::sum(vec![], [sequence.clone()]);
        assert!(!normalized.shares_recipe_storage_for_test(&sequence));
        assert_eq!(
            sequence.materialize_for_test(),
            vec![fact("b"), fact("a"), fact("b")]
        );
        assert_eq!(
            normalized.materialize_for_test(),
            vec![fact("a"), fact("b")]
        );
    }
    #[test]
    fn concat_preserves_factor_order_and_repeated_factors() {
        let control = Control::unlimited();
        let factor = Support::from(vec![fact("b"), fact("a")]);
        let composed = Support::concat([factor.clone(), factor]);
        assert_eq!(
            composed.materialize(&control).unwrap(),
            vec![fact("b"), fact("a"), fact("b"), fact("a")]
        );
    }
    #[test]
    fn final_root_of_deep_shared_chain_drops_iteratively() {
        const DEPTH: usize = 100_000;
        let mut root = Support::default();
        for _ in 0..DEPTH {
            // sum(empty,[root]) may return the same normalized factor. Concat
            // deliberately keeps a new layer, so this tests a real final-owner chain.
            root = Support::concat([root]);
        }
        let mut depth = 0;
        let mut cursor = &root;
        while let Some(next) = cursor.0.factors.first() {
            assert_eq!(cursor.0.factors.len(), 1);
            depth += 1;
            cursor = next;
        }
        assert_eq!(depth, DEPTH);
        drop(root);
    }
}

// 診断表示で支持DAG全体を再帰的に展開しない。完全Fact列はwireの明示射影で得る。
impl std::fmt::Debug for Support {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Support")
            .field("own_facts", &self.0.own.len())
            .field("factors", &self.0.factors.len())
            .field("union", &self.0.union)
            .finish()
    }
}
