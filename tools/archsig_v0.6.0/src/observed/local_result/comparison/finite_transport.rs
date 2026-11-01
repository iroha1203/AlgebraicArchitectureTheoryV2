//! 有限局所状態を実Operationの位置対応に沿って運ぶ。
use super::integer::{Renaming, dependencies, list, record, reference_value};
use super::*;
use crate::observed::integer_fiber::{self, Matrix};
use crate::observed::local_result::integer as affine;
use crate::observed::local_result::rational as rational_affine;
use rational_affine::integer_fiber as rational_fiber;
use std::collections::BTreeSet;
pub(super) struct Maps {
    pub global: Vec<(NodeRef, NodeRef)>,
    pub matching: Vec<(NodeRef, NodeRef)>,
    pub outside_count: num_bigint::BigInt,
    pub outside_image: Option<NodeRef>,
}
fn object(value: &Json) -> Result<&BTreeMap<String, Json>, ValidationFailure> {
    let Json::Obj(fields) = value else {
        return Err("有限輸送のrecordがない".into());
    };
    Ok(fields)
}
fn array(value: &Json) -> Result<&[Json], ValidationFailure> {
    let Json::Arr(values) = value else {
        return Err("有限輸送の列がない".into());
    };
    Ok(values)
}
fn member<'a>(
    fields: &'a BTreeMap<String, Json>,
    name: &str,
) -> Result<&'a Json, ValidationFailure> {
    fields
        .get(name)
        .ok_or_else(|| ValidationFailure::from("有限輸送のfieldがない"))
}
fn text(value: &Json) -> Result<&str, ValidationFailure> {
    let Json::Str(s) = value else {
        return Err("有限輸送の名前がない".into());
    };
    Ok(s)
}
fn law_matches(
    g: &Graph,
    a: NodeRef,
    b: NodeRef,
    rename: &Renaming,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    let x = record(g, a)?;
    let y = record(g, b)?;
    if x.get("name") != y.get("name") {
        return Ok(false);
    }
    let xs = array(member(x, "bindings")?)?;
    let ys = array(member(y, "bindings")?)?;
    if xs.len() != ys.len() {
        return Ok(false);
    }
    for (x, y) in xs.iter().zip(ys) {
        let x = object(x)?;
        let y = object(y)?;
        if x.get("name") != y.get("name")
            || !rename.binding(
                g.scalar(reference_value(g, a, member(x, "value")?)?)?,
                g.scalar(reference_value(g, b, member(y, "value")?)?)?,
                c,
            )?
        {
            return Ok(false);
        }
    }
    Ok(true)
}
struct State {
    context: NodeRef,
    slots: Vec<Fact>,
    values: Vec<NodeRef>,
}
fn states(g: &Graph, system: NodeRef, semantic: bool) -> Result<Vec<State>, ValidationFailure> {
    let wire = record(g, system)?;
    let equations = array(member(wire, "equation_states")?)?;
    let meanings = array(member(wire, "semantic_states")?)?;
    if equations.len() != meanings.len() {
        return Err("有限状態のcontext列が違う".into());
    }
    let mut result = vec![];
    for (e, s) in equations.iter().zip(meanings) {
        let e = object(e)?;
        let s = object(s)?;
        if e.get("context") != s.get("context") {
            return Err("有限状態のcontext順が違う".into());
        }
        let context = reference_value(g, system, member(e, "context")?)?;
        let space = reference_value(g, system, member(e, "space")?)?;
        let mut slots = vec![];
        for v in array(member(record(g, space)?, "variables")?)? {
            let position = object(member(object(v)?, "position")?)?;
            if text(member(position, "kind")?)? != "observation"
                || !array(member(position, "component")?)?.is_empty()
            {
                return Err("有限状態の座標が観測fieldでない".into());
            }
            let f = object(member(position, "field")?)?;
            slots.push(Fact {
                snapshot: text(member(f, "snapshot")?)?.into(),
                subject: text(member(f, "subject")?)?.into(),
                field: Some(text(member(f, "field")?)?.into()),
                atom: None,
            });
        }
        let values = if semantic
            || local(g, system)?
                .source
                .system
                .as_ref()
                .is_some_and(|s| s.finite.is_none())
        {
            elements(g, reference_value(g, system, member(s, "state_image")?)?)?
        } else {
            let solution = reference_value(g, system, member(e, "solutions")?)?;
            let representation = object(member(record(g, solution)?, "representation")?)?;
            if text(member(representation, "kind")?)? != "finite" {
                return Err("有限解の列挙がない".into());
            }
            array(member(representation, "values")?)?
                .iter()
                .map(|v| reference_value(g, solution, v))
                .collect::<Result<Vec<_>, _>>()?
        };
        result.push(State {
            context,
            slots,
            values,
        });
    }
    Ok(result)
}
fn position_map(
    a: &[Fact],
    b: &[Fact],
    rename: &Renaming,
    c: &Control,
) -> Result<Option<Vec<usize>>, ValidationFailure> {
    if a.len() < b.len() {
        return Ok(None);
    }
    let mut result = vec![];
    for x in a {
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        let Some(y) = rename.fact(x) else {
            return Ok(None);
        };
        let Some(i) = b.iter().position(|z| *z == y) else {
            return Ok(None);
        };
        result.push(i);
    }
    if result.iter().copied().collect::<BTreeSet<_>>().len() != b.len() {
        return Ok(None);
    }
    Ok(Some(result))
}
enum Coordinates {
    Fields(Vec<usize>),
    Read(Matrix, usize),
    Rational(rational_fiber::Matrix, usize),
}
macro_rules! read_coordinates {
    ($name:ident,$field:ident,$fiber:ident,$variant:ident) => {
        fn $name(
            a: &$field::Diagram,
            b: &$field::Diagram,
            i: usize,
            j: usize,
            rename: &Renaming,
            c: &Control,
        ) -> Result<Option<Coordinates>, ValidationFailure> {
            let Some(positions) = position_map(&a.slots, &b.slots, rename, c)? else {
                return Ok(None);
            };
            if a.slots.len() != b.slots.len() {
                return Ok(None);
            }
            let n = a.slots.len();
            let mut permutation = vec![vec![num_traits::Zero::zero(); n]; n];
            for (i, j) in positions.iter().enumerate() {
                permutation[*j][i] = 1usize.into();
            }
            let source = &a.readings[i];
            let target = &b.readings[j];
            let transported = $fiber::multiply(&target.map, &permutation, n, c)?;
            let reading = $field::linear::Reading::new(&transported, n, c)?;
            // 有限の試料が偶然一致するだけでは、異なる read の context を同一視しない。
            if !source.contains(&reading, c)? || !reading.contains(source, c)? {
                return Ok(None);
            }
            let map = $fiber::multiply(&transported, &source.lift, source.map.len(), c)?;
            Ok(Some(Coordinates::$variant(map, source.map.len())))
        }
    };
}
read_coordinates!(integer_coordinates, affine, integer_fiber, Read);
read_coordinates!(
    rational_coordinates,
    rational_affine,
    rational_fiber,
    Rational
);
fn state_matches(
    a: &Scalar,
    b: &Scalar,
    coordinates: &Coordinates,
    rename: &Renaming,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    let positions = match coordinates {
        Coordinates::Fields(p) => p,
        Coordinates::Rational(map, width) => {
            let (Scalar::Tuple(a), Scalar::Tuple(b)) = (a, b) else {
                return Ok(false);
            };
            if a.len() != *width || b.len() != map.len() {
                return Ok(false);
            }
            let a = a
                .iter()
                .map(rational_affine::read_coefficient)
                .collect::<Result<Vec<_>, _>>()?;
            let b = b
                .iter()
                .map(rational_affine::read_coefficient)
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(rational_affine::linear::apply(map, &a, c)? == b);
        }
        Coordinates::Read(map, width) => {
            let (Scalar::Tuple(a), Scalar::Tuple(b)) = (a, b) else {
                return Ok(false);
            };
            if a.len() != *width || b.len() != map.len() {
                return Ok(false);
            }
            let a = a
                .iter()
                .map(affine::read_coefficient)
                .collect::<Result<Vec<_>, _>>()?;
            let b = b
                .iter()
                .map(affine::read_coefficient)
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(affine::linear::apply(map, &a, c)? == b);
        }
    };
    if matches!((a, b), (Scalar::Unit, Scalar::Unit)) {
        return Ok(positions.is_empty());
    }
    let (Scalar::Tuple(a), Scalar::Tuple(b)) = (a, b) else {
        return Ok(false);
    };
    if a.len() != positions.len()
        || b.len() != positions.iter().copied().collect::<BTreeSet<_>>().len()
    {
        return Ok(false);
    }
    for (x, i) in a.iter().zip(positions) {
        if !rename.binding(x, &b[*i], c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn injection(
    g: &Graph,
    a: &[NodeRef],
    b: &[NodeRef],
    c: &Control,
    mut same: impl FnMut(&Scalar, &Scalar, &Control) -> Result<bool, ValidationFailure>,
) -> Result<Option<Vec<(NodeRef, NodeRef)>>, ValidationFailure> {
    if a.len() > b.len() {
        return Ok(None);
    }
    let mut result = vec![];
    let mut used = BTreeSet::new();
    for x in a {
        let mut image = None;
        for y in b {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            if same(g.scalar(*x)?, g.scalar(*y)?, c)? {
                if image.replace(*y).is_some() {
                    return Ok(None);
                }
            }
        }
        let Some(y) = image else { return Ok(None) };
        if !used.insert(y.0) {
            return Ok(None);
        }
        result.push((*x, y));
    }
    Ok(Some(result))
}
fn record_outside(
    pairs: &[(NodeRef, NodeRef)],
    targets: &[NodeRef],
    count: &mut num_bigint::BigInt,
    example: &mut Option<NodeRef>,
    c: &Control,
) -> Result<(), ValidationFailure> {
    let mut images = BTreeSet::new();
    for (_, image) in pairs {
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        images.insert(image.0);
    }
    for target in targets {
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        if !images.contains(&target.0) {
            *count += 1;
            if example.is_none() {
                *example = Some(*target);
            }
        }
    }
    Ok(())
}
fn mapped(
    g: &Graph,
    pairs: &[(NodeRef, NodeRef)],
    x: NodeRef,
) -> Result<Option<NodeRef>, ValidationFailure> {
    for (a, b) in pairs {
        if g.scalar(*a)? == g.scalar(x)? {
            return Ok(Some(*b));
        }
    }
    Ok(None)
}
fn restrictions(
    g: &Graph,
    system: NodeRef,
    semantic: bool,
    states: &[State],
) -> Result<BTreeMap<(usize, usize), NodeRef>, ValidationFailure> {
    let mut result = BTreeMap::new();
    for r in array(member(record(g, system)?, "restrictions")?)? {
        let r = object(r)?;
        if text(member(r, "side")?)? != if semantic { "semantic" } else { "equation" } {
            continue;
        }
        let arrow = reference_value(g, system, member(r, "arrow")?)?;
        let from = field(g, arrow, "target")?;
        let to = field(g, arrow, "source")?;
        let from = states
            .iter()
            .position(|s| s.context == from)
            .ok_or("制限元contextがない")?;
        let to = states
            .iter()
            .position(|s| s.context == to)
            .ok_or("制限先contextがない")?;
        if result
            .insert((from, to), reference_value(g, system, member(r, "map")?)?)
            .is_some()
        {
            return Err("有限制限が重複している".into());
        }
    }
    Ok(result)
}
pub(super) fn between(
    env: &Environment<'_>,
    g: &Graph,
    left: NodeRef,
    right: NodeRef,
    along: NodeRef,
    c: &Control,
) -> Result<Option<Maps>, ValidationFailure> {
    let ls = field(g, left, "system")?;
    let rs = field(g, right, "system")?;
    let ld = local(g, ls)?;
    let rd = local(g, rs)?;
    let (Some(l), Some(r)) = (&ld.source.system, &rd.source.system) else {
        return Ok(None);
    };
    let equation_side = record(g, left)?.get("side") != Some(&Json::str("semantic"));
    if l.integer
        .as_ref()
        .is_some_and(|d| !d.equation_only || equation_side)
        || r.integer
            .as_ref()
            .is_some_and(|d| !d.equation_only || equation_side)
    {
        return Ok(None);
    }
    if l.rational
        .as_ref()
        .is_some_and(|d| !d.equation_only || equation_side)
        || r.rational
            .as_ref()
            .is_some_and(|d| !d.equation_only || equation_side)
    {
        return Ok(None);
    }
    let (from, to, _, _) = public_compose::components(g, along)?;
    let op = public_compose::op(g, along)?;
    let left_base = field(g, ls, "base")?;
    let right_base = field(g, rs, "base")?;
    let endpoints = left_base == from && right_base == to;
    let same_object = op.source() == op.target()
        && [from, to].contains(&left_base)
        && [from, to].contains(&right_base);
    if !(endpoints || same_object) || op.source().reading() != op.target().reading() {
        return Ok(None);
    }
    let Some(rename) = Renaming::operation(g, env.indexes.inputs.law(), along, c)? else {
        return Ok(None);
    };
    if !rename.positions(env, &l.fixed_positions, &r.fixed_positions, false, c)? {
        return Ok(None);
    }
    if l.laws.len() != r.laws.len() {
        return Ok(None);
    }
    let mut laws = BTreeMap::new();
    let mut used = BTreeSet::new();
    for x in &l.laws {
        let mut image = None;
        for y in &r.laws {
            if law_matches(g, *x, *y, &rename, c)? {
                if image.replace(*y).is_some() {
                    return Ok(None);
                }
            }
        }
        let Some(y) = image else { return Ok(None) };
        if !used.insert(y.0) {
            return Ok(None);
        }
        laws.insert(x.0, y);
    }
    let semantic = record(g, left)?.get("side") == Some(&Json::str("semantic"));
    let a = states(g, ls, semantic)?;
    let b = states(g, rs, semantic)?;
    if a.len() != b.len() {
        return Ok(None);
    }
    let mut contexts = vec![];
    let mut coordinates = vec![];
    let mut maps = vec![];
    let mut outside_count = num_bigint::BigInt::from(0);
    let mut outside_image = None;
    for (i, x) in a.iter().enumerate() {
        let Some(mut carrier) = array(member(record(g, x.context)?, "carrier")?)?
            .iter()
            .map(|v| rename.carrier(v))
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        carrier.sort_by_key(Json::canonical);
        carrier.dedup();
        let Some(mut deps) = dependencies(g, x.context)?
            .iter()
            .map(|p| rename.fact(p))
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        deps.sort();
        deps.dedup();
        let selected = list(g, x.context, "law_coordinates")?
            .iter()
            .map(|r| laws.get(&r.0).map(|v| v.0))
            .collect::<Option<BTreeSet<_>>>()
            .ok_or("局所Lawの対応がない")?;
        let mut matches = vec![];
        for (j, y) in b.iter().enumerate() {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            let mut other = array(member(record(g, y.context)?, "carrier")?)?.to_vec();
            other.sort_by_key(Json::canonical);
            let mut yd = dependencies(g, y.context)?;
            yd.sort();
            if carrier != other
                || deps != yd
                || selected
                    != list(g, y.context, "law_coordinates")?
                        .into_iter()
                        .map(|r| r.0)
                        .collect()
            {
                continue;
            }
            let p = match (&l.integer, &r.integer) {
                (Some(a), Some(b)) => integer_coordinates(a, b, i, j, &rename, c)?,
                (None, None) => match (&l.rational, &r.rational) {
                    (Some(a), Some(b)) => rational_coordinates(a, b, i, j, &rename, c)?,
                    (None, None) => {
                        position_map(&x.slots, &y.slots, &rename, c)?.map(Coordinates::Fields)
                    }
                    _ => None,
                },
                _ => None,
            };
            let Some(p) = p else {
                continue;
            };
            let Some(map) = injection(g, &x.values, &y.values, c, |a, b, c| {
                state_matches(a, b, &p, &rename, c)
            })?
            else {
                continue;
            };
            matches.push((j, p, map));
        }
        if matches.len() != 1 {
            return Ok(None);
        }
        let (j, p, map) = matches.pop().ok_or("有限contextの像がない")?;
        if contexts.contains(&j) {
            return Ok(None);
        }
        contexts.push(j);
        coordinates.push(p);
        maps.push(map);
    }
    if contexts.first() != Some(&0) {
        return Ok(None);
    }
    let patches = |system| -> Result<Vec<usize>, ValidationFailure> {
        let state = if system == ls { &a } else { &b };
        list(g, field(g, system, "cover")?, "patches")?
            .iter()
            .map(|r| {
                state
                    .iter()
                    .position(|s| s.context == *r)
                    .ok_or_else(|| ValidationFailure::from("coverのcontextがない"))
            })
            .collect()
    };
    let ap = patches(ls)?;
    let bp = patches(rs)?;
    if ap.iter().map(|i| contexts[*i]).collect::<BTreeSet<_>>() != bp.iter().copied().collect() {
        return Ok(None);
    }
    let ar = restrictions(g, ls, semantic, &a)?;
    let br = restrictions(g, rs, semantic, &b)?;
    if ar.len() != br.len() {
        return Ok(None);
    }
    for ((from, to), map) in ar {
        let Some(other) = br.get(&(contexts[from], contexts[to])) else {
            return Ok(None);
        };
        let rp = pairs(g, *other)?;
        for (x, y) in pairs(g, map)? {
            let Some(x) = mapped(g, &maps[from], x)? else {
                return Ok(None);
            };
            let Some(y) = mapped(g, &maps[to], y)? else {
                return Ok(None);
            };
            let Some(z) = mapped(g, &rp, x)? else {
                return Ok(None);
            };
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            if g.scalar(y)? != g.scalar(z)? {
                return Ok(None);
            }
        }
    }
    let lm = elements(g, field(g, left, "matching")?)?;
    let rm = elements(g, field(g, right, "matching")?)?;
    let Some(matching) = injection(g, &lm, &rm, c, |x, y, c| {
        let (Scalar::Tuple(x), Scalar::Tuple(y)) = (x, y) else {
            return Ok(false);
        };
        if x.len() != ap.len() || y.len() != bp.len() {
            return Ok(false);
        }
        for (value, i) in x.iter().zip(&ap) {
            let j = bp
                .iter()
                .position(|p| *p == contexts[*i])
                .ok_or("移送先patchがない")?;
            if !state_matches(value, &y[j], &coordinates[*i], &rename, c)? {
                return Ok(false);
            }
        }
        Ok(true)
    })?
    else {
        return Ok(None);
    };
    let globals = elements(g, field(g, field(g, left, "restriction")?, "source")?)?;
    let targets = elements(g, field(g, field(g, right, "restriction")?, "source")?)?;
    let Some(global) = injection(g, &globals, &targets, c, |x, y, c| {
        state_matches(x, y, &coordinates[0], &rename, c)
    })?
    else {
        return Ok(None);
    };
    record_outside(&matching, &rm, &mut outside_count, &mut outside_image, c)?;
    record_outside(&global, &targets, &mut outside_count, &mut outside_image, c)?;
    Ok(Some(Maps {
        global,
        matching,
        outside_count,
        outside_image,
    }))
}
