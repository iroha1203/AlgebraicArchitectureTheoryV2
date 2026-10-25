//! 読取り上の恒等Operationが誘導する、同一局所系の整数診断間の実写像。
use super::*;
use crate::observed::{change_result::linear_result as wire, integer_fiber};
use num_bigint::BigInt as Z;

fn record(g: &Graph, r: NodeRef) -> Result<&BTreeMap<String, Json>, ValidationFailure> {
    let Json::Obj(fields) = &local(g, r)?.part().wire else {
        return Err("整数診断のレコードがない".into());
    };
    Ok(fields)
}
fn reference_value(g: &Graph, owner: NodeRef, value: &Json) -> Result<NodeRef, ValidationFailure> {
    local(g, owner)?
        .part()
        .arguments
        .iter()
        .find(|r| r.wire() == *value)
        .copied()
        .ok_or_else(|| "整数診断の参照が依存にない".into())
}
fn list(g: &Graph, r: NodeRef, name: &str) -> Result<Vec<NodeRef>, ValidationFailure> {
    let Some(Json::Arr(values)) = record(g, r)?.get(name) else {
        return Err("整数診断の参照列がない".into());
    };
    values.iter().map(|v| reference_value(g, r, v)).collect()
}
fn size(g: &Graph, module: NodeRef) -> Result<usize, ValidationFailure> {
    let Some(Json::Arr(generators)) = record(g, module)?.get("generators") else {
        return Err("整数加群の生成元がない".into());
    };
    Ok(generators.len())
}
fn integer(g: &Graph, owner: NodeRef, value: &Json) -> Result<Z, ValidationFailure> {
    let Scalar::Z(value) = g.scalar(reference_value(g, owner, value)?)? else {
        return Err("整数係数でない".into());
    };
    Ok(value.clone())
}
fn rows(g: &Graph, r: NodeRef, name: &str) -> Result<Vec<Vec<Z>>, ValidationFailure> {
    let Some(Json::Arr(values)) = record(g, r)?.get(name) else {
        return Err("整数表示の係数列がない".into());
    };
    values
        .iter()
        .map(|v| {
            let Json::Arr(row) = v else {
                return Err("整数表示の行がない".into());
            };
            row.iter().map(|x| integer(g, r, x)).collect()
        })
        .collect()
}
fn same_module(g: &Graph, left: NodeRef, right: NodeRef) -> Result<bool, ValidationFailure> {
    let a = record(g, left)?;
    let z = record(g, right)?;
    Ok(size(g, left)? == size(g, right)?
        && record(g, field(g, left, "ring")?)? == record(g, field(g, right, "ring")?)?
        && a.get("free_rank") == z.get("free_rank")
        && a.get("torsion") == z.get("torsion")
        && rows(g, left, "relations")? == rows(g, right, "relations")?)
}
fn same_map(g: &Graph, left: NodeRef, right: NodeRef) -> Result<bool, ValidationFailure> {
    Ok(
        same_module(g, field(g, left, "source")?, field(g, right, "source")?)?
            && same_module(g, field(g, left, "target")?, field(g, right, "target")?)?
            && rows(g, left, "columns")? == rows(g, right, "columns")?,
    )
}
fn identity(n: usize) -> integer_fiber::Matrix {
    (0..n)
        .map(|i| (0..n).map(|j| Z::from(usize::from(i == j))).collect())
        .collect()
}
fn coordinates(g: &Graph, vector: NodeRef) -> Result<Vec<Z>, ValidationFailure> {
    let Some(Json::Arr(values)) = record(g, vector)?.get("coordinates") else {
        return Err("類の整数座標がない".into());
    };
    values.iter().map(|v| integer(g, vector, v)).collect()
}
pub(super) fn compare(
    b: &mut Builder<'_>,
    request: &Request,
    left: NodeRef,
    right: NodeRef,
    along: NodeRef,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    let g = b.g;
    let lc = field(g, left, "complex")?;
    let rc = field(g, right, "complex")?;
    let lm = list(g, lc, "modules")?;
    let rm = list(g, rc, "modules")?;
    let ld = list(g, lc, "differentials")?;
    let rd = list(g, rc, "differentials")?;
    if lm.len() != rm.len()
        || ld.len() != rd.len()
        || record(g, lc)?.get("convention") != record(g, rc)?.get("convention")
        || field(g, lc, "cover")? != field(g, rc, "cover")?
    {
        return Err("同じ局所系の複体の表示が一致しない".into());
    }
    let mut components = vec![];
    for (a, z) in lm.iter().zip(&rm) {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        if !same_module(g, *a, *z)? {
            return Err("複体の同一座標の加群が一致しない".into());
        }
        let n = size(g, *a)?;
        components.push(wire::map(b, *a, *z, &identity(n), n, c)?);
    }
    // 同一のordered coverの座標を移す。各微分の実係数を照合して可換性を検査する。
    for (a, z) in ld.iter().zip(&rd) {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        if !same_map(g, *a, *z)? {
            return Err("恒等cochain写像と微分が可換でない".into());
        }
    }
    let cochain = b.push(
        NodeType::Construction(T::CochainMap),
        "cochain_map",
        Json::obj([
            ("source", lc.wire()),
            ("target", rc.wire()),
            ("components", refs(&components)),
        ]),
        [lc, rc, along]
            .into_iter()
            .chain(components.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let ls = field(g, left, "space")?;
    let rs = field(g, right, "space")?;
    let lh = field(g, ls, "module")?;
    let rh = field(g, rs, "module")?;
    // cycleの包含と商射影まで照合する。rankの一致だけでHの写像を決めない。
    if !same_module(g, lh, rh)?
        || !same_map(g, field(g, ls, "inclusion")?, field(g, rs, "inclusion")?)?
        || !same_map(g, field(g, ls, "projection")?, field(g, rs, "projection")?)?
    {
        return Err("同じ複体からのコホモロジー表示が一致しない".into());
    }
    let n = size(g, lh)?;
    let hmap = wire::map(b, lh, rh, &identity(n), n, c)?;
    let inverse = wire::map(b, rh, lh, &identity(n), n, c)?;
    // 実表示で互いに逆な恒等写像なので、torsionを含めkernel/cokernelは零。
    let ring = field(g, lh, "ring")?;
    let kernel = wire::module(b, ring, 0, "kernel", vec![hmap])?;
    let cokernel = wire::module(b, ring, 0, "quotient", vec![hmap])?;
    let mut conditions = vec![
        b.proposition(
            "naturality",
            vec![cochain],
            ld.iter().chain(&rd).copied().collect(),
            Decision::Established,
        )?,
        b.proposition(
            "naturality",
            vec![cochain, hmap],
            vec![ls, rs],
            Decision::Established,
        )?,
        b.proposition(
            "inverse_maps",
            vec![hmap, inverse],
            vec![cochain],
            Decision::Established,
        )?,
    ];
    let mut status = Decision::Established;
    let mut reasons = vec![];
    let mut class_transport = None;
    if record(g, left)?.get("degree") == Some(&Json::Nat(1)) {
        let left_class = record(g, left)?
            .get("class")
            .map(|v| reference_value(g, left, v))
            .transpose()?;
        let right_class = record(g, right)?
            .get("class")
            .map(|v| reference_value(g, right, v))
            .transpose()?;
        let transport = if let (Some(a), Some(z)) = (left_class, right_class) {
            let av = field(g, a, "coordinates")?;
            let zv = field(g, z, "coordinates")?;
            let x = coordinates(g, av)?;
            let y = coordinates(g, zv)?;
            if x.len() != n || y.len() != n {
                return Err("対象類の座標次元が違う".into());
            }
            let relations = rows(g, rh, "relations")?;
            let matrix = (0..n)
                .map(|i| relations.iter().map(|r| r[i].clone()).collect())
                .collect();
            let delta = x.iter().zip(&y).map(|(x, y)| x - y).collect::<Vec<_>>();
            let equal = integer_fiber::solve(&matrix, relations.len(), &delta, c)?
                .particular
                .is_some();
            status = if equal {
                Decision::Established
            } else {
                Decision::Refuted
            };
            let transported = wire::vector(b, rh, &x, c)?;
            b.proposition("equal", vec![transported, zv], vec![a, z, hmap], status)?
        } else {
            status = Decision::Undetermined;
            let condition = b.proposition(
                "constructible",
                vec![left, right],
                vec![],
                Decision::Undetermined,
            )?;
            reasons.push(Reason {
                kind: ReasonKind::ConditionFailed {
                    condition,
                    construction: "class_transport",
                },
                request: request.id.clone(),
                dependencies: vec![left, right, condition],
                missing: vec![],
                location: None,
            });
            condition
        };
        conditions.push(transport);
        class_transport = Some(transport);
    }
    let mut fields = BTreeMap::from([
        ("kind".into(), Json::str("diagnostics")),
        ("left".into(), left.wire()),
        ("right".into(), right.wire()),
        ("along".into(), along.wire()),
        ("cochain_map".into(), cochain.wire()),
        ("cohomology_map".into(), hmap.wire()),
        ("kernel".into(), kernel.wire()),
        ("cokernel".into(), cokernel.wire()),
        ("conditions".into(), refs(&conditions)),
    ]);
    if let Some(r) = class_transport {
        fields.insert("class_transport".into(), r.wire());
    }
    let comparison = b.push(
        NodeType::Construction(T::Comparison),
        "comparison",
        Json::Obj(fields),
        [left, right, along, cochain, hmap, kernel, cokernel]
            .into_iter()
            .chain(conditions)
            .collect(),
        None,
        None,
    )?;
    let claim = b.proposition("diagnostics_preserved", vec![comparison], vec![], status)?;
    let part = &mut b.parts[claim.0 - b.base];
    part.reasons.extend(reasons);
    sort_reasons(&mut part.reasons);
    part.judgment
        .as_mut()
        .ok_or("整数診断比較の判断がない")?
        .reasons = part.reasons.clone();
    let reasons = part.reasons.clone();
    let scope = b.parts[comparison.0 - b.base].scope.clone();
    Ok(Answer {
        id: request.id.clone(),
        status,
        outputs: BTreeMap::from([
            ("comparison".into(), comparison),
            ("proposition".into(), claim),
        ]),
        claim: Some(claim),
        evidence: vec![],
        reasons,
        scope,
    })
}
