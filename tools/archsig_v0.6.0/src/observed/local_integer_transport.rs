//! 観測位置の全単射から局所状態とordered Čech座標の実写像を作る。
use super::*;
use crate::archmap::Slot;
use integer_fiber::Matrix;
use std::collections::BTreeSet;

pub(in crate::observed::local_result) struct Maps {
    pub forward: Vec<Matrix>,
    pub inverse: Option<Vec<Matrix>>,
}
pub(in crate::observed::local_result) struct Renaming<'a> {
    law: &'a crate::law::CheckedLaw,
    fields: BTreeMap<(String, String, Option<crate::names::QualifiedName>), Fact>,
}
impl<'a> Renaming<'a> {
    pub(in crate::observed::local_result) fn operation(
        g: &Graph,
        law: &'a crate::law::CheckedLaw,
        along: NodeRef,
        c: &mut Control,
    ) -> Result<Option<Self>, ValidationFailure> {
        let op = public_compose::op(g, along)?;
        let mut rename = Renaming {
            law,
            fields: BTreeMap::new(),
        };
        for (source, image) in op
            .map()
            .candidate()
            .universe()
            .iter()
            .zip(op.map().candidate().images())
        {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
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
        Ok(Some(rename))
    }
    pub(in crate::observed::local_result) fn positions(
        &self,
        env: &Environment<'_>,
        left: &[Fact],
        right: &[Fact],
        injective: bool,
        c: &mut Control,
    ) -> Result<bool, ValidationFailure> {
        let mut targets = BTreeSet::new();
        let mut sources = BTreeSet::new();
        for source in left {
            let mut key = source.clone();
            key.atom = None;
            if !sources.insert(key) {
                continue;
            }
            let Some(image) = self.fact(source) else {
                return Ok(false);
            };
            if !targets.insert(image.clone()) && injective {
                return Ok(false);
            }
            if !right.iter().any(|p| {
                p.snapshot == image.snapshot && p.subject == image.subject && p.field == image.field
            }) {
                return Ok(false);
            }
            if let Some(name) = &source.field {
                let sf = env.field(&source.snapshot, &source.subject, name)?;
                let tf = env.field(&image.snapshot, &image.subject, name)?;
                let (Slot::Known { value: x, .. }, Slot::Known { value: y, .. }) =
                    (&sf.slot, &tf.slot)
                else {
                    return Ok(false);
                };
                if sf.ty != tf.ty {
                    return Ok(false);
                }
                let (Some(x), Some(y)) = (
                    crate::observed::environment::scalar_from(x, &sf.ty, self.law, c)?,
                    crate::observed::environment::scalar_from(y, &tf.ty, self.law, c)?,
                ) else { return Ok(false); };
                if !self.binding(&x, &y, c)? {
                    return Ok(false);
                }
            }
        }
        let target_positions = right
            .iter()
            .map(|p| {
                let mut p = p.clone();
                p.atom = None;
                p
            })
            .collect::<BTreeSet<_>>();
        if targets != target_positions {
            return Ok(false);
        }
        Ok(true)
    }

    fn image(&self, fact: &Fact) -> Option<Fact> {
        self.fields
            .get(&(
                fact.snapshot.clone(),
                fact.subject.clone(),
                fact.field.clone(),
            ))
            .cloned()
    }
    pub(in crate::observed::local_result) fn fact(&self, fact: &Fact) -> Option<Fact> {
        self.image(fact).filter(|image| image.field == fact.field)
    }
    fn path(
        &self, a: &crate::observed::path_value::PathValue,
        b: &crate::observed::path_value::PathValue, c: &mut Control,
    ) -> Result<bool, ValidationFailure> {
        a.check(c)?;
        b.check(c)?;
        if a.reading != b.reading || !self.binding(&a.object(), &b.object(), c)?
            || !self.binding(&a.target(), &b.target(), c)? { return Ok(false); }
        match (&a.step, &b.step) {
            (None, None) => Ok(true),
            (Some(a), Some(b)) => {
                if a.word_tail.len() != b.word_tail.len()
                    || !self.binding(&a.generator, &b.generator, c)? { return Ok(false); }
                for (x, y) in a.word_tail.iter().zip(&b.word_tail) {
                    if !self.binding(x, y, c)? { return Ok(false); }
                }
                // Operation の全域作用と Path の全域作用の可換性。
                // 対象外の位置を根へ送る作用も保持する。
                for (source, image) in a.carrier.iter().zip(&a.images) {
                    c.checkpoint(crate::control::Checkpoint::Localize)?;
                    let Some(mapped_source) = self.image(source) else { return Ok(false); };
                    let Some(mapped_image) = self.image(image) else { return Ok(false); };
                    let mut target_image = None;
                    for (point, value) in b.carrier.iter().zip(&b.images) {
                        c.checkpoint(crate::control::Checkpoint::Localize)?;
                        if point.snapshot == mapped_source.snapshot && point.subject == mapped_source.subject
                            && point.field == mapped_source.field {
                            if target_image.is_some() { return Ok(false); }
                            target_image = Some(value);
                        }
                    }
                    let Some(target_image) = target_image else { return Ok(false); };
                    if target_image.snapshot != mapped_image.snapshot || target_image.subject != mapped_image.subject
                        || target_image.field != mapped_image.field { return Ok(false); }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }
    fn subject(&self, snapshot: &str, subject: &str) -> Option<Fact> {
        self.fact(&Fact {
            snapshot: snapshot.into(),
            subject: subject.into(),
            field: None,
            atom: None,
        })
    }
    pub(in crate::observed::local_result) fn carrier(&self, value: &Json) -> Option<Json> {
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
    pub(in crate::observed::local_result) fn binding(&self, a: &Scalar, b: &Scalar, c: &mut Control) -> Result<bool, ValidationFailure> {
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            if a.ty() != b.ty() { return Ok(false); }
            Ok(match (a, b) {
                (Scalar::Subject { snapshot, subject, .. }, Scalar::Subject { snapshot: bs, subject: bu, .. }) =>
                    self.subject(snapshot, subject).is_some_and(|f| f.snapshot == *bs && f.subject == *bu),
                (Scalar::Tuple(a), Scalar::Tuple(b))
                | (Scalar::List { items: a, .. }, Scalar::List { items: b, .. }) => {
                    if a.len() != b.len() { return Ok(false); }
                    for (x,y) in a.iter().zip(b) { if !self.binding(x,y,c)? { return Ok(false); } }
                    true
                }
                (Scalar::Set { items: a, .. }, Scalar::Set { items: b, .. }) => {
                    if a.len() != b.len() { return Ok(false); }
                    let mut used = BTreeSet::new();
                    for x in a {
                        let mut image = None;
                        for (i,y) in b.iter().enumerate() {
                            if self.binding(x,y,c)? {
                                if image.replace(i).is_some() { return Ok(false); }
                            }
                        }
                        let Some(i) = image else { return Ok(false); };
                        if !used.insert(i) { return Ok(false); }
                    }
                    true
                }
                (Scalar::Map { pairs: a, .. }, Scalar::Map { pairs: b, .. }) => {
                    if a.len() != b.len() { return Ok(false); }
                    let mut used = BTreeSet::new();
                    for (ak,av) in a {
                        let mut image = None;
                        for (i,(bk,bv)) in b.iter().enumerate() {
                            if self.binding(ak,bk,c)? && self.binding(av,bv,c)? {
                                if image.replace(i).is_some() { return Ok(false); }
                            }
                        }
                        let Some(i) = image else { return Ok(false); };
                        if !used.insert(i) { return Ok(false); }
                    }
                    true
                }
                (Scalar::Option { value: a, .. }, Scalar::Option { value: b, .. }) => match (a,b) {
                    (Some(x),Some(y)) => self.binding(x,y,c)?,
                    (None,None) => true,
                    _ => false,
                },
                (Scalar::Data { constructor: a, args: x, .. }, Scalar::Data { constructor: b, args: y, .. }) => {
                    if a != b || x.len() != y.len() { return Ok(false); }
                    for (x,y) in x.iter().zip(y) { if !self.binding(x,y,c)? { return Ok(false); } }
                    true
                }
                (Scalar::Term(_), Scalar::Term(_)) =>
                    crate::observed::value_equality::equal(a, b, self.law, c)? == Some(true),
                (Scalar::Path(a), Scalar::Path(b)) => self.path(a, b, c)?,
                (Scalar::Path(_) | Scalar::Term(_), _) | (_, Scalar::Path(_) | Scalar::Term(_)) => false,
                _ => a == b,
            })
        })
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
pub(in crate::observed::local_result) fn dependencies(g: &Graph, context: NodeRef) -> Result<Vec<Fact>, ValidationFailure> {
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
                field: Some(field.clone().into()),
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
        c.checkpoint(crate::control::Checkpoint::Localize)?;
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
                    c.checkpoint(crate::control::Checkpoint::Localize)?;
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
            c.checkpoint(crate::control::Checkpoint::Localize)?;
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
    let (Some(a), Some(b)) = (diagram(l), diagram(r)) else {
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
    let Some(rename) = Renaming::operation(g, env.inputs.law(), along, c)? else {
        return Ok(None);
    };
    if !rename.positions(env, &l.fixed_positions, &r.fixed_positions, true, c)? {
        return Ok(None);
    }
    if a.requirements.len() != b.requirements.len() {
        return Ok(None);
    }
    let mut laws = vec![];
    for (name, bindings) in &a.requirements {
        let mut matches = vec![];
        for (i,(n,bs)) in b.requirements.iter().enumerate() {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            if n != name || bs.len() != bindings.len() { continue; }
            let mut equal = true;
            for ((n,x),(m,y)) in bindings.iter().zip(bs) {
                if n != m || !rename.binding(x,y,c)? { equal = false; break; }
            }
            if equal { matches.push(i); }
        }
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
        permutation[j][i] = Z::from(1usize);
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
            c.checkpoint(crate::control::Checkpoint::Localize)?;
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
            c.checkpoint(crate::control::Checkpoint::Localize)?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::result::Signal;
    #[test]
    fn compound_bindings_preserve_structure_and_actual_images() {
        let subject=|s:&str| Scalar::Subject {snapshot:"v".into(),subject:s.into(),entity:"R.Item".into()};
        let law = crate::law::CheckedLaw {
            resolved_names: Default::default(),
            bytes_digest: String::new(), model_digest: String::new(), declarations: BTreeMap::new(),
            exprs: vec![], expr_types: vec![], quantifier_types: vec![], infos: vec![],
            definitions: crate::definition::CheckedDefinitions::empty(),
        };
        let rename=Renaming {law: &law, fields:[("a","z"),("b","y")].into_iter().map(|(a,b)|
            (("v".into(),a.into(),None),Fact{snapshot:"v".into(),subject:b.into(),field:None,atom:None})).collect()};
        let ty=Type::Ref("R.Item".into());
        let set=|items|Scalar::Set{element:ty.clone(),items};
        let list=|items|Scalar::List{element:ty.clone(),items};
        let map=|pairs|Scalar::Map{domain:ty.clone(),codomain:ty.clone(),pairs};
        let data=|name:&str,args|Scalar::Data{family:"R.Packet".into(),constructor:name.into(),args};
        let mut c=Control::unlimited();
        for (a,b) in [
            (set(vec![subject("a"),subject("b")]),set(vec![subject("y"),subject("z")])),
            (map(vec![(subject("a"),subject("b")),(subject("b"),subject("a"))]),map(vec![(subject("y"),subject("z")),(subject("z"),subject("y"))])),
            (data("Wrap",vec![list(vec![subject("a"),subject("b"),subject("a")])]),data("Wrap",vec![list(vec![subject("z"),subject("y"),subject("z")])])),
            (Scalar::Option{element:ty.clone(),value:None},Scalar::Option{element:ty.clone(),value:None}),
        ] { assert!(rename.binding(&a,&b,&mut c).unwrap()); }
        for (a,b) in [
            (list(vec![subject("a"),subject("b")]),list(vec![subject("y"),subject("z")])),
            (set(vec![subject("a"),subject("b")]),set(vec![subject("z")])),
            (map(vec![(subject("a"),subject("b"))]),map(vec![(subject("z"),subject("z"))])),
            (data("Wrap",vec![subject("a")]),data("Other",vec![subject("z")])),
            (Scalar::Option{element:ty.clone(),value:None},Scalar::Option{element:ty.clone(),value:Some(Box::new(subject("z")))}),
            (Scalar::Tuple(vec![subject("a"),Scalar::Z(2.into())]),Scalar::Tuple(vec![subject("z"),Scalar::Z(3.into())])),
        ] { assert!(!rename.binding(&a,&b,&mut c).unwrap()); }
        let mut stopped=Control::new(|_|Some(Signal::Int));
        assert!(matches!(rename.binding(&subject("a"),&subject("z"),&mut stopped),Err(ValidationFailure::Stop(_))));
    }
}
