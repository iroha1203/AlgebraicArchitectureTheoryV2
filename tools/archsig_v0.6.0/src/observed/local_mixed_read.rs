//! 有限作用の局所状態にも整数readの情報の包含・交わりを使う。
use super::*;
use crate::observed::{environment::change_affine, integer_fiber::Matrix};
use integer::linear::Reading;
use num_bigint::BigInt as Z;
use num_traits::Zero;

pub(in crate::observed::local_result) struct Information {
    slots: Vec<Fact>,
    pub patches: Vec<Reading>,
    pub reads: Vec<Reading>,
    laws: Vec<Matrix>,
}
impl Information {
    pub fn new(env: &Environment<'_>, model: &finite_model::Model) -> Result<Self, ValidationFailure> {
        let mut laws = vec![];
        for requirement in &model.requirements {
            let mut pending = change_affine::Pending::default();
            let (rows, _) = change_affine::state_equations(env, &model.slots, std::slice::from_ref(requirement), &mut pending)?;
            if !pending.facts.is_empty() { return Err("整数readのLawに未観測位置がある".into()); }
            laws.push(rows);
        }
        Ok(Self { slots: model.slots.clone(), patches: vec![], reads: vec![], laws })
    }
    pub fn slots(&self) -> &[Fact] { &self.slots }
    pub fn identity(&self, c: &Control) -> Result<Reading, ValidationFailure> {
        self.reading(None, &self.slots, c)
    }
    pub fn reading(&self, information: Option<&(Vec<Fact>, crate::observed::field_fiber::Matrix)>, visible: &[Fact], c: &Control) -> Result<Reading, ValidationFailure> {
        let n = self.slots.len();
        let mut rows = vec![];
        if let Some((slots, matrix)) = information {
            for row in matrix {
                if row.len() != slots.len() { return Err("整数readの係数次元が違う".into()); }
                let mut full = vec![Z::zero(); n];
                for (slot, value) in slots.iter().zip(row) {
                    let i = self.slots.iter().position(|f| f == slot).ok_or("整数readの自由位置がない")?;
                    full[i] = integer::read_coefficient(value)?;
                }
                rows.push(full);
            }
        } else {
            for (i, slot) in self.slots.iter().enumerate() {
                if visible.contains(slot) {
                    rows.push((0..n).map(|j| Z::from(u8::from(i == j))).collect());
                }
            }
        }
        Reading::new(&rows, n, c)
    }
    pub fn visible_law(&self, support: &Support, reading: &Reading, required: &Support, i: usize, c: &Control) -> Result<bool, ValidationFailure> {
        let mut required = required.clone();
        required.visible.retain(|f| !self.slots.contains(f));
        Ok(support.contains(&required) && reading.sees(&self.laws[i], c)?)
    }
    pub fn adequate(&self, patches: &[Support], laws: &[Support], c: &Control) -> Result<bool, ValidationFailure> {
        if patches.len() != self.patches.len() { return Err("整数readのpatch数が違う".into()); }
        let rows = self.patches.iter().flat_map(|r| r.map.iter().cloned()).collect();
        if Reading::new(&rows, self.slots.len(), c)?.map.len() != self.slots.len() { return Ok(false); }
        for (i, law) in laws.iter().enumerate() {
            let mut covered = false;
            for (support, reading) in patches.iter().zip(&self.patches) {
                covered |= self.visible_law(support, reading, law, i, c)?;
            }
            if !covered { return Ok(false); }
        }
        Ok(true)
    }
}
pub(super) fn contains(a: &Option<Reading>, b: &Option<Reading>, c: &Control) -> Result<bool, ValidationFailure> {
    match (a,b) {
        (None,None) => Ok(true),
        (Some(a),Some(b)) => a.contains(b,c),
        _ => Err("整数readの有無がcontext間で違う".into()),
    }
}
pub(super) fn intersect(a: &Option<Reading>, b: &Option<Reading>, c: &Control) -> Result<Option<Reading>, ValidationFailure> {
    match (a,b) {
        (None,None) => Ok(None),
        (Some(a),Some(b)) => a.intersect(b,c).map(Some),
        _ => Err("整数readの有無が交わりで違う".into()),
    }
}
pub(super) fn find(supports: &[Support], readings: &[Option<Reading>], support: &Support, reading: &Option<Reading>, c: &Control) -> Result<Option<usize>, ValidationFailure> {
    for (i, old) in supports.iter().enumerate() {
        c.clone().checkpoint(crate::observed::control::Checkpoint::Localize)?;
        if old == support && contains(&readings[i],reading,c)? && contains(reading,&readings[i],c)? { return Ok(Some(i)); }
    }
    Ok(None)
}
