//! 観測位置の全単射から局所状態とordered Čech座標の実写像を作る。
use super::*;
use crate::archmap::{Slot, Value};
use crate::observed::local_result::integer::{Diagram, linear};
use integer_fiber::Matrix;
use std::collections::BTreeSet;

pub(in crate::observed::local_result) struct Maps {
    pub forward: Vec<Matrix>,
    pub inverse: Option<Vec<Matrix>>,
}
struct Renaming {
    fields: BTreeMap<(String, String, Option<String>), Fact>,
}
impl Renaming {
    fn fact(&self, fact: &Fact) -> Option<Fact> {
        self.fields
            .get(&(
                fact.snapshot.clone(),
                fact.subject.clone(),
                fact.field.clone(),
            ))
            .cloned()
    }
    fn subject(&self, snapshot: &str, subject: &str) -> Option<Fact> {
        self.fact(&Fact {
            snapshot: snapshot.into(),
            subject: subject.into(),
            field: None,
            atom: None,
        })
    }
    fn carrier(&self, value: &Json) -> Option<Json> {
        let Json::Obj(fields) = value else {
            return None;
        };
        let mut fields = fields.clone();
        let Some(Json::Arr(pair)) = fields.get("value") else {
            return None;
        };
        let [Json::Str(snapshot), Json::Str(subject)] = pair.as_slice() else {
            return None;
        };
        let image = self.subject(snapshot, subject)?;
        fields.insert(
            "value".into(),
            Json::Arr(vec![Json::str(image.snapshot), Json::str(image.subject)]),
        );
        Some(Json::Obj(fields))
    }
    fn value(&self, a: &Value, b: &Value, c: &mut Control) -> Result<bool, ValidationFailure> {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            Ok(match (a, b) {
                (
                    Value::Ref { snapshot, subject },
                    Value::Ref {
                        snapshot: bs,
                        subject: bu,
                    },
                ) => self
                    .subject(snapshot, subject)
                    .is_some_and(|f| f.snapshot == *bs && f.subject == *bu),
                (Value::Tuple(a), Value::Tuple(b)) | (Value::List(a), Value::List(b)) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    for (a, b) in a.iter().zip(b) {
                        if !self.value(a, b, c)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                (Value::Set(a), Value::Set(b)) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    for a in a {
                        let mut found = false;
                        for b in b {
                            found |= self.value(a, b, c)?;
                        }
                        if !found {
                            return Ok(false);
                        }
                    }
                    true
                }
                (Value::Map(a), Value::Map(b)) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    for (ak, av) in a {
                        let mut found = false;
                        for (bk, bv) in b {
                            found |= self.value(ak, bk, c)? && self.value(av, bv, c)?;
                        }
                        if !found {
                            return Ok(false);
                        }
                    }
                    true
                }
                (Value::Option(Some(a)), Value::Option(Some(b))) => self.value(a, b, c)?,
                (
                    Value::Data {
                        constructor: a,
                        args: x,
                    },
                    Value::Data {
                        constructor: b,
                        args: y,
                    },
                ) => {
                    if a != b || x.len() != y.len() {
                        return Ok(false);
                    }
                    for (a, b) in x.iter().zip(y) {
                        if !self.value(a, b, c)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                (Value::Term(_), _) | (_, Value::Term(_)) => false,
                _ => a == b,
            })
        })
    }
    fn binding(&self, a: &Scalar, b: &Scalar) -> bool {
        match (a, b) {
            (
                Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                },
                Scalar::Subject {
                    snapshot: bs,
                    subject: bu,
                    entity: be,
                },
            ) => {
                entity == be
                    && self
                        .subject(snapshot, subject)
                        .is_some_and(|f| f.snapshot == *bs && f.subject == *bu)
            }
            (
                Scalar::Unit
                | Scalar::Bool(_)
                | Scalar::Z(_)
                | Scalar::Q(_, _)
                | Scalar::Fp { .. }
                | Scalar::Text(_),
                _,
            ) => a == b,
            _ => false,
        }
    }
}
fn coordinates(
    basis: &Matrix,
    rank: usize,
    values: &Matrix,
    cols: usize,
    c: &mut Control,
) -> Result<Option<Matrix>, ValidationFailure> {
    let mut result = vec![vec![Z::zero(); cols]; rank];
    for j in 0..cols {
        let rhs = values.iter().map(|row| row[j].clone()).collect::<Vec<_>>();
        let solution = integer_fiber::solve(basis, rank, &rhs, c)?;
        let Some(point) = solution.particular else {
            return Ok(None);
        };
        if solution.rank != rank {
            return Ok(None);
        }
        for i in 0..rank {
            result[i][j] = point[i].clone();
        }
    }
    Ok(Some(result))
}
fn dependencies(g: &Graph, context: NodeRef) -> Result<Vec<Fact>, ValidationFailure> {
    let Some(Json::Arr(values)) = record(g, context)?.get("dependencies") else {
        return Err("contextの依存位置がない".into());
    };
    values
        .iter()
        .map(|v| {
            let Json::Obj(fields) = v else {
                return Err("contextの依存位置がrecordでない".into());
            };
            let subject = reference_value(
                g,
                context,
                fields.get("subject").ok_or("位置のsubjectがない")?,
            )?;
            let Scalar::Subject {
                snapshot, subject, ..
            } = g.scalar(subject)?
            else {
                return Err("位置がsubjectでない".into());
            };
            let Some(Json::Str(field)) = fields.get("field") else {
                return Err("位置のfieldがない".into());
            };
            Ok(Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: Some(field.clone()),
                atom: None,
            })
        })
        .collect()
}
struct Level {
    tuples: Vec<Vec<usize>>,
    contexts: Vec<usize>,
    offsets: Vec<usize>,
    rank: usize,
}
fn levels(
    d: &Diagram,
    semantic: bool,
    count: usize,
    c: &mut Control,
) -> Result<Vec<Level>, ValidationFailure> {
    let states = if semantic { &d.semantic } else { &d.equation };
    let mut tuples = d.patches.iter().map(|i| vec![*i]).collect::<Vec<_>>();
    let mut levels = vec![];
    for k in 0..count {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let mut contexts = vec![];
        let mut offsets = vec![];
        let mut rank = 0;
        for tuple in &tuples {
            let mut context = tuple[0];
            for p in &tuple[1..] {
                context = d.intersections[context][*p];
            }
            contexts.push(context);
            offsets.push(rank);
            rank += states[context].rank;
        }
        let mut next = vec![];
        if k + 1 < count {
            for tuple in &tuples {
                for p in &d.patches {
                    c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                    let mut v = tuple.clone();
                    v.push(*p);
                    next.push(v);
                }
            }
        }
        levels.push(Level {
            tuples,
            contexts,
            offsets,
            rank,
        });
        tuples = next;
    }
    Ok(levels)
}
fn cochains(
    a: &[Level],
    b: &[Level],
    contexts: &[usize],
    coefficients: &[Matrix],
    c: &mut Control,
) -> Result<Vec<Matrix>, ValidationFailure> {
    let mut maps = vec![];
    for (a, b) in a.iter().zip(b) {
        let mut map = vec![vec![Z::zero(); a.rank]; b.rank];
        for (i, tuple) in a.tuples.iter().enumerate() {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            let image = tuple.iter().map(|p| contexts[*p]).collect::<Vec<_>>();
            let j = b
                .tuples
                .iter()
                .position(|t| *t == image)
                .ok_or("移送先のpatch tupleがない")?;
            if b.contexts[j] != contexts[a.contexts[i]] {
                return Err("移送と交わりが可換でない".into());
            }
            for (r, row) in coefficients[a.contexts[i]].iter().enumerate() {
                for (s, x) in row.iter().enumerate() {
                    map[b.offsets[j] + r][a.offsets[i] + s] = x.clone();
                }
            }
        }
        maps.push(map);
    }
    Ok(maps)
}
pub(in crate::observed::local_result) fn between(
    env: &Environment<'_>,
    g: &Graph,
    left: NodeRef,
    right: NodeRef,
    along: NodeRef,
    c: &mut Control,
) -> Result<Option<Maps>, ValidationFailure> {
    let ls = field(g, left, "system")?;
    let rs = field(g, right, "system")?;
    let Some(l) = &local(g, ls)?.source.system else {
        return Ok(None);
    };
    let Some(r) = &local(g, rs)?.source.system else {
        return Ok(None);
    };
    let (Some(a), Some(b)) = (&l.integer, &r.integer) else {
        return Ok(None);
    };
    let (from, to, _, _) = public_compose::components(g, along)?;
    let op = public_compose::op(g, along)?;
    if field(g, ls, "base")? != from
        || field(g, rs, "base")? != to
        || op.source().reading() != op.target().reading()
        || !a.assignments.is_empty()
        || !b.assignments.is_empty()
        || a.slots.len() != b.slots.len()
        || a.contexts.len() != b.contexts.len()
    {
        return Ok(None);
    }
    let mut rename = Renaming {
        fields: BTreeMap::new(),
    };
    for (source, image) in op
        .map()
        .candidate()
        .universe()
        .iter()
        .zip(op.map().candidate().images())
    {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        if source.field != image.field {
            continue;
        }
        let key = (
            source.snapshot.clone(),
            source.subject.clone(),
            source.field.clone(),
        );
        let mut image = image.clone();
        image.atom = None;
        if rename
            .fields
            .insert(key, image.clone())
            .is_some_and(|old| old != image)
        {
            return Ok(None);
        }
    }
    let mut targets = BTreeSet::new();
    let mut sources = BTreeSet::new();
    for source in &l.fixed_positions {
        let mut key = source.clone();
        key.atom = None;
        if !sources.insert(key) {
            continue;
        }
        let Some(image) = rename.fact(source) else {
            return Ok(None);
        };
        if !targets.insert(image.clone()) {
            return Ok(None);
        }
        if !r.fixed_positions.iter().any(|p| {
            p.snapshot == image.snapshot && p.subject == image.subject && p.field == image.field
        }) {
            return Ok(None);
        }
        if let Some(name) = &source.field {
            let sf = env.field(&source.snapshot, &source.subject, name)?;
            let tf = env.field(&image.snapshot, &image.subject, name)?;
            let (Slot::Known { value: x, .. }, Slot::Known { value: y, .. }) = (&sf.slot, &tf.slot)
            else {
                return Ok(None);
            };
            if sf.ty != tf.ty || !rename.value(x, y, c)? {
                return Ok(None);
            }
        }
    }
    let target_positions = r
        .fixed_positions
        .iter()
        .map(|p| {
            let mut p = p.clone();
            p.atom = None;
            p
        })
        .collect::<BTreeSet<_>>();
    if targets != target_positions {
        return Ok(None);
    }
    if a.requirements.len() != b.requirements.len() {
        return Ok(None);
    }
    let mut laws = vec![];
    for (name, bindings) in &a.requirements {
        let matches = b
            .requirements
            .iter()
            .enumerate()
            .filter(|(_, (n, bs))| {
                n == name
                    && bs.len() == bindings.len()
                    && bindings
                        .iter()
                        .zip(bs)
                        .all(|((n, x), (m, y))| n == m && rename.binding(x, y))
            })
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        if matches.len() != 1 || laws.contains(&matches[0]) {
            return Ok(None);
        }
        laws.push(matches[0]);
    }
    let n = a.slots.len();
    let mut permutation = vec![vec![Z::zero(); n]; n];
    let mut seen = BTreeSet::new();
    for (i, source) in a.slots.iter().enumerate() {
        let Some(image) = rename.fact(source) else {
            return Ok(None);
        };
        let Some(j) = b.slots.iter().position(|p| {
            p.snapshot == image.snapshot && p.subject == image.subject && p.field == image.field
        }) else {
            return Ok(None);
        };
        if !seen.insert(j) {
            return Ok(None);
        }
        permutation[j][i] = Z::from(1);
    }
    let semantic = record(g, left)?.get("side") == Some(&Json::str("semantic"));
    let sa = if semantic { &a.semantic } else { &a.equation };
    let sb = if semantic { &b.semantic } else { &b.equation };
    let mut context_map = vec![];
    let mut coefficients = vec![];
    let mut inverses = vec![];
    for (i, context) in a.contexts.iter().enumerate() {
        let Some(Json::Arr(carrier)) = record(g, *context)?.get("carrier") else {
            return Err("contextのcarrierがない".into());
        };
        let Some(mut carrier) = carrier
            .iter()
            .map(|v| rename.carrier(v))
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        carrier.sort_by_key(Json::canonical);
        let Some(mut deps) = dependencies(g, *context)?
            .iter()
            .map(|f| rename.fact(f))
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        deps.sort();
        let selected = list(g, *context, "law_coordinates")?
            .iter()
            .map(|r| {
                a.law_refs
                    .iter()
                    .position(|l| l == r)
                    .map(|k| b.law_refs[laws[k]].0)
            })
            .collect::<Option<BTreeSet<_>>>()
            .ok_or("局所Lawの元がない")?;
        let mut matches = vec![];
        for (j, target) in b.contexts.iter().enumerate() {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            let Some(Json::Arr(other)) = record(g, *target)?.get("carrier") else {
                return Err("contextのcarrierがない".into());
            };
            let mut other = other.clone();
            other.sort_by_key(Json::canonical);
            let mut td = dependencies(g, *target)?;
            td.sort();
            if carrier != other
                || deps != td
                || selected
                    != list(g, *target, "law_coordinates")?
                        .into_iter()
                        .map(|r| r.0)
                        .collect()
            {
                continue;
            }
            let transported = integer_fiber::multiply(&b.readings[j].map, &permutation, n, c)?;
            let hidden = a.readings[i].kernel.first().map_or(0, Vec::len);
            if integer_fiber::multiply(&transported, &a.readings[i].kernel, hidden, c)?
                .iter()
                .flatten()
                .any(|x| !x.is_zero())
            {
                continue;
            }
            let map = integer_fiber::multiply(
                &transported,
                &a.readings[i].lift,
                a.readings[i].map.len(),
                c,
            )?;
            let ra = a.readings[i].map.len();
            let rb = b.readings[j].map.len();
            let Some(inverse) = coordinates(&map, ra, &identity(rb), rb, c)? else {
                continue;
            };
            if integer_fiber::multiply(&inverse, &map, ra, c)? != identity(ra) {
                continue;
            }
            let moved = integer_fiber::multiply(&map, &sa[i].basis, sa[i].rank, c)?;
            let Some(coeff) = coordinates(&sb[j].basis, sb[j].rank, &moved, sa[i].rank, c)? else {
                continue;
            };
            let back = integer_fiber::multiply(&inverse, &sb[j].basis, sb[j].rank, c)?;
            let inv = coordinates(&sa[i].basis, sa[i].rank, &back, sb[j].rank, c)?;
            if sa[i].known != sb[j].known {
                continue;
            }
            match (&sa[i].origin, &sb[j].origin) {
                (Some(x), Some(y)) => {
                    let x = linear::apply(&map, x, c)?;
                    let delta = x.iter().zip(y).map(|(x, y)| vec![x - y]).collect();
                    if coordinates(&sb[j].basis, sb[j].rank, &delta, 1, c)?.is_none() {
                        continue;
                    }
                }
                (None, None) => {}
                _ => continue,
            }
            matches.push((j, coeff, inv));
        }
        if matches.len() != 1 {
            return Ok(None);
        }
        let (j, f, v) = matches.pop().ok_or("contextの像がない")?;
        if context_map.contains(&j) {
            return Ok(None);
        }
        context_map.push(j);
        coefficients.push(f);
        inverses.push(v);
    }
    if context_map.first() != Some(&0) {
        return Ok(None);
    }
    if a.patches
        .iter()
        .map(|p| context_map[*p])
        .collect::<BTreeSet<_>>()
        != b.patches.iter().copied().collect()
    {
        return Ok(None);
    }
    for i in 0..context_map.len() {
        for j in 0..context_map.len() {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            if context_map[a.intersections[i][j]] != b.intersections[context_map[i]][context_map[j]]
            {
                return Ok(None);
            }
            match (
                a.restrictions.get(&(i, j)),
                b.restrictions.get(&(context_map[i], context_map[j])),
            ) {
                (Some(x), Some(y)) => {
                    let x = if semantic { &x.1 } else { &x.0 };
                    let y = if semantic { &y.1 } else { &y.0 };
                    if integer_fiber::multiply(&coefficients[i], x, sa[j].rank, c)?
                        != integer_fiber::multiply(y, &coefficients[j], sa[j].rank, c)?
                    {
                        return Ok(None);
                    }
                }
                (None, None) => {}
                _ => return Ok(None),
            }
        }
    }
    let count = list(g, field(g, left, "complex")?, "modules")?.len();
    let al = levels(a, semantic, count, c)?;
    let bl = levels(b, semantic, count, c)?;
    let mut inverse_context = vec![0; context_map.len()];
    let mut inverse_coeff = vec![vec![]; context_map.len()];
    let invertible = inverses.iter().all(Option::is_some);
    for (i, j) in context_map.iter().enumerate() {
        inverse_context[*j] = i;
        if let Some(inverse) = &inverses[i] {
            inverse_coeff[*j] = inverse.clone();
        }
    }
    Ok(Some(Maps {
        forward: cochains(&al, &bl, &context_map, &coefficients, c)?,
        inverse: if invertible {
            Some(cochains(&bl, &al, &inverse_context, &inverse_coeff, c)?)
        } else {
            None
        },
    }))
}
