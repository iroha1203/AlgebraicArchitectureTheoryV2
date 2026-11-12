//! 旧意味評価器が実際に計算したflat Fact集合。Derefは実Vecを借りるだけで合成支持を展開しない。
use super::Fact;
/// 確定した支持。加工する側は所有 Vec を明示的に取り出す。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FlatFacts(std::sync::Arc<Vec<Fact>>);
impl FlatFacts {
    /// 共有先を変えずに加工するため、この値の Vec を一意所有にする。
    pub(crate) fn make_owned(&mut self) -> &mut Vec<Fact> {
        std::sync::Arc::make_mut(&mut self.0)
    }
    pub(crate) fn into_vec(self) -> Vec<Fact> {
        std::sync::Arc::try_unwrap(self.0).unwrap_or_else(|shared| (*shared).clone())
    }
}
impl From<Vec<Fact>> for FlatFacts {
    fn from(facts: Vec<Fact>) -> Self {
        Self(std::sync::Arc::new(facts))
    }
}
impl std::ops::Deref for FlatFacts {
    type Target = Vec<Fact>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl PartialEq<Vec<Fact>> for FlatFacts {
    fn eq(&self, other: &Vec<Fact>) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl PartialEq<FlatFacts> for Vec<Fact> {
    fn eq(&self, other: &FlatFacts) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl<'a> IntoIterator for &'a FlatFacts {
    type Item = &'a Fact;
    type IntoIter = std::slice::Iter<'a, Fact>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
#[test]
fn owned_flat_fact_edits_leave_shared_facts_unchanged() {
    let original = FlatFacts::from(vec![Fact::from(archsig_input::archmap::FactData {
        snapshot: "snapshot".into(),
        subject: "subject".into(),
        field: Some("Example.Entity.field".into()),
        atom: Some("known".into()),
    })]);
    let expected = original.to_vec();
    let mut edited = original.clone();
    edited.make_owned()[0].subject = "caller-local".into();
    edited.make_owned().clear();
    assert!(edited.is_empty());
    assert_eq!(original, expected);
    let mut extracted = original.clone().into_vec();
    extracted[0].atom = Some("different".into());
    assert_eq!(original, expected);
}
