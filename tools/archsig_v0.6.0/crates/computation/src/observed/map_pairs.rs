//! Map の行と、型・key の一意性を検査した検索索引。
use super::result::{Scalar, ValidationFailure};
use archsig_common::{
    control::{Checkpoint, Control},
    internal,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Deref,
    sync::{Arc, OnceLock},
};

#[derive(Clone)]
pub(crate) struct MapPairs(Arc<Rows>);

#[cfg_attr(test, derive(Clone))]
struct Rows {
    values: Vec<(Scalar, Scalar)>,
    index: OnceLock<Index>,
}

#[derive(Clone)]
struct Index {
    domain: String,
    codomain: String,
    order: Vec<usize>,
}

fn identity(value: &Scalar) -> Option<(&str, &str, &str)> {
    match value {
        Scalar::Subject {
            snapshot,
            subject,
            entity,
        } => Some((snapshot, subject, entity)),
        _ => None,
    }
}

type Reference<'a> = (&'a str, &'a str, &'a str);

impl MapPairs {
    fn indexed(
        &self,
        domain: &str,
        codomain: &str,
        control: &Control,
    ) -> Result<&Index, ValidationFailure> {
        control.checkpoint(Checkpoint::FiniteIteration)?;
        if self.0.index.get().is_none() {
            let mut keys = BTreeMap::new();
            for (row, (key, image)) in self.iter().enumerate() {
                #[cfg(test)]
                super::data::observe_iteration("map_check", row);
                control.checkpoint(Checkpoint::FiniteIteration)?;
                let Some((snapshot, subject, entity)) = identity(key) else {
                    return Err(internal!("Mapのkeyが参照でない").into());
                };
                if entity != domain
                    || identity(image).is_none_or(|(_, _, entity)| entity != codomain)
                {
                    return Err(internal!("Mapのkey/value型が違う").into());
                }
                if keys.insert((snapshot, subject), row).is_some() {
                    return Err(internal!("Mapに重複keyがある").into());
                }
            }
            let mut order = Vec::with_capacity(keys.len());
            for row in keys.into_values() {
                control.checkpoint(Checkpoint::FiniteIteration)?;
                order.push(row);
            }
            let _ = self.0.index.set(Index {
                domain: domain.into(),
                codomain: codomain.into(),
                order,
            });
        }
        let index = self
            .0
            .index
            .get()
            .ok_or(internal!("検査済みMap索引がない"))?;
        if !self.is_empty() && (index.domain != domain || index.codomain != codomain) {
            return Err(internal!("Mapのkey/value型が違う").into());
        }
        Ok(index)
    }

    pub(super) fn check(
        &self,
        domain: &str,
        codomain: &str,
        control: &Control,
    ) -> Result<(), ValidationFailure> {
        self.indexed(domain, codomain, control).map(|_| ())
    }

    pub(super) fn lookup(
        &self,
        domain: &str,
        codomain: &str,
        key: &Scalar,
        control: &Control,
    ) -> Result<Option<&Scalar>, ValidationFailure> {
        let index = self.indexed(domain, codomain, control)?;
        let Some((snapshot, subject, entity)) = identity(key) else {
            return Err(internal!("Map適用の実keyが参照でない").into());
        };
        if entity != domain {
            return Err(internal!("Map適用の実key型が始域型と違う").into());
        }
        let target = (snapshot, subject);
        let mut candidates = index.order.as_slice();
        #[cfg(test)]
        let mut comparisons = 0;
        while !candidates.is_empty() {
            #[cfg(test)]
            {
                super::data::observe_iteration("map_lookup", comparisons);
                comparisons += 1;
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
            let middle = candidates.len() / 2;
            let (key, value) = &self[candidates[middle]];
            let (snapshot, subject, _) =
                identity(key).ok_or(internal!("検査済みMapのkeyが参照でない"))?;
            match (snapshot, subject).cmp(&target) {
                std::cmp::Ordering::Less => candidates = &candidates[middle + 1..],
                std::cmp::Ordering::Greater => candidates = &candidates[..middle],
                std::cmp::Ordering::Equal => return Ok(Some(value)),
            }
        }
        Ok(None)
    }

    pub(super) fn shared_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    pub(super) fn equal_references(&self, other: &Self) -> Option<bool> {
        if let (Some(left), Some(right)) = (self.0.index.get(), other.0.index.get()) {
            return Some(
                left.order
                    .iter()
                    .zip(&right.order)
                    .all(|(&a, &b)| self[a] == other[b]),
            );
        }
        fn rows(pairs: &MapPairs) -> Option<BTreeSet<(Reference<'_>, Reference<'_>)>> {
            pairs
                .iter()
                .map(|(key, value)| Some((identity(key)?, identity(value)?)))
                .collect()
        }
        Some(rows(self)? == rows(other)?)
    }

    pub(super) fn take_unique_rows(&mut self) -> Vec<(Scalar, Scalar)> {
        Arc::get_mut(&mut self.0).map_or_else(Vec::new, |rows| std::mem::take(&mut rows.values))
    }
}

impl From<Vec<(Scalar, Scalar)>> for MapPairs {
    fn from(values: Vec<(Scalar, Scalar)>) -> Self {
        Self(Arc::new(Rows {
            values,
            index: OnceLock::new(),
        }))
    }
}

impl FromIterator<(Scalar, Scalar)> for MapPairs {
    fn from_iter<T: IntoIterator<Item = (Scalar, Scalar)>>(rows: T) -> Self {
        Self::from(rows.into_iter().collect::<Vec<_>>())
    }
}

impl Deref for MapPairs {
    type Target = Vec<(Scalar, Scalar)>;
    fn deref(&self) -> &Self::Target {
        &self.0.values
    }
}

#[cfg(test)]
impl std::ops::DerefMut for MapPairs {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let rows = Arc::make_mut(&mut self.0);
        rows.index.take();
        &mut rows.values
    }
}

impl<'a> IntoIterator for &'a MapPairs {
    type Item = &'a (Scalar, Scalar);
    type IntoIter = std::slice::Iter<'a, (Scalar, Scalar)>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl std::fmt::Debug for MapPairs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.values.fmt(f)
    }
}
