// 係数型に応じる局所診断の実写像。
use super::*;
use num_traits::Zero;
#[path = "local_integer_transport.rs"]
mod transport;
pub(super) use transport::{between, dependencies, Renaming};

pub(super) fn record(g: &Graph, r: NodeRef) -> Result<&BTreeMap<String, Json>, ValidationFailure> {
    let Json::Obj(fields) = &local(g, r)?.part().wire else {
        return Err("整数診断のレコードがない".into());
    };
    Ok(fields)
}
pub(super) fn reference_value(
    g: &Graph,
    owner: NodeRef,
    value: &Json,
) -> Result<NodeRef, ValidationFailure> {
    local(g, owner)?
        .part()
        .arguments
        .iter()
        .find(|r| r.wire() == *value)
        .copied()
        .ok_or_else(|| "整数診断の参照が依存にない".into())
}
pub(super) fn list(g: &Graph, r: NodeRef, name: &str) -> Result<Vec<NodeRef>, ValidationFailure> {
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
    read_coefficient(g.scalar(reference_value(g, owner, value)?)?)
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
fn from_columns(
    columns: &[Vec<Z>],
    rows: usize,
) -> Result<integer_fiber::Matrix, ValidationFailure> {
    if columns.iter().any(|c| c.len() != rows) {
        return Err("整数表示の列次元が違う".into());
    }
    Ok((0..rows)
        .map(|i| columns.iter().map(|c| c[i].clone()).collect())
        .collect())
}
fn map_matrix(g: &Graph, map: NodeRef) -> Result<integer_fiber::Matrix, ValidationFailure> {
    from_columns(
        &rows(g, map, "columns")?,
        size(g, field(g, map, "target")?)?,
    )
}
fn zero_columns(
    g: &Graph,
    module: NodeRef,
    matrix: &integer_fiber::Matrix,
    cols: usize,
    c: &mut Control,
) -> Result<bool, ValidationFailure> {
    let relations = rows(g, module, "relations")?;
    let relations_matrix = from_columns(&relations, size(g, module)?)?;
    for j in 0..cols {
        let rhs = matrix.iter().map(|r| r[j].clone()).collect::<Vec<_>>();
        if integer_fiber::solve(&relations_matrix, relations.len(), &rhs, c)?
            .particular
            .is_none()
        {
            return Ok(false);
        }
    }
    Ok(true)
}
fn induced(
    g: &Graph,
    source: NodeRef,
    target: NodeRef,
    map: &integer_fiber::Matrix,
    c: &mut Control,
) -> Result<integer_fiber::Matrix, ValidationFailure> {
    let si = field(g, source, "inclusion")?;
    let ti = field(g, target, "inclusion")?;
    let sp = field(g, source, "projection")?;
    let tp = field(g, target, "projection")?;
    let sm = field(g, source, "module")?;
    let tm = field(g, target, "module")?;
    let cycles = size(g, field(g, si, "source")?)?;
    let target_cycles = size(g, field(g, ti, "source")?)?;
    let images = integer_fiber::multiply(map, &map_matrix(g, si)?, cycles, c)?;
    let cycle_map = linear::coordinates(&map_matrix(g, ti)?, target_cycles, &images, cycles, c)?;
    let on_cycles = integer_fiber::multiply(&map_matrix(g, tp)?, &cycle_map, cycles, c)?;
    let n = size(g, sm)?;
    let projection = map_matrix(g, sp)?;
    let mut lift = vec![vec![Z::zero(); n]; cycles];
    for j in 0..n {
        let mut unit = vec![Z::zero(); n];
        unit[j] = Z::from(1usize);
        let column = integer_fiber::solve(&projection, cycles, &unit, c)?
            .particular
            .ok_or("cohomology商射影が全射でない")?;
        for i in 0..cycles {
            lift[i][j] = column[i].clone();
        }
    }
    let result = integer_fiber::multiply(&on_cycles, &lift, n, c)?;
    let factored = integer_fiber::multiply(&result, &projection, cycles, c)?;
    let residual = factored
        .iter()
        .zip(&on_cycles)
        .map(|(a, b)| a.iter().zip(b).map(|(x, y)| x - y).collect())
        .collect();
    let relations = rows(g, sm, "relations")?;
    let images =
        integer_fiber::multiply(&result, &from_columns(&relations, n)?, relations.len(), c)?;
    if !zero_columns(g, tm, &residual, cycles, c)?
        || !zero_columns(g, tm, &images, relations.len(), c)?
    {
        return Err("cohomology写像がcycle商を通じて因子分解しない".into());
    }
    Ok(result)
}
fn check_inverse(
    g: &Graph,
    module: NodeRef,
    left: &integer_fiber::Matrix,
    right: &integer_fiber::Matrix,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let n = size(g, module)?;
    let composite = integer_fiber::multiply(left, right, n, c)?;
    let residual = composite
        .iter()
        .zip(identity(n))
        .map(|(a, b)| a.iter().zip(b).map(|(x, y)| x - y).collect())
        .collect();
    if !zero_columns(g, module, &residual, n, c)? {
        return Err("cohomology写像の合成が恒等でない".into());
    }
    Ok(())
}
// H写像の核は、target関係の逆像をsource関係で割ったもの。
// 余核はtargetの生成元をtarget関係と写像の像で割る。
fn quotient_module(
    b: &mut Builder<'_>,
    ring: NodeRef,
    relation: &integer_fiber::Matrix,
    relation_count: usize,
    generators: usize,
    name: &str,
    hmap: NodeRef,
    c: &mut Control,
) -> Result<(NodeRef, linear::Cohomology), ValidationFailure> {
    let q = linear::cohomology(relation, relation_count, &vec![], generators, c)?;
    let rank = q.torsion.len() + q.free_rank;
    let mut relations = vec![];
    let mut arguments = vec![ring, hmap];
    for (i, divisor) in q.torsion.iter().enumerate() {
        let mut column = vec![];
        for j in 0..rank {
            column.push(change_result::value(
                b,
                &coefficient_value(if i == j { divisor.clone() } else { Z::zero() }),
            )?);
        }
        relations.push(refs(&column));
        arguments.extend(column);
    }
    let module = b.push(
        NodeType::Construction(T::Module),
        "module",
        Json::obj([
            ("ring", ring.wire()),
            (
                "generators",
                Json::Arr(
                    (0..rank)
                        .map(|i| {
                            Json::obj([
                                ("type", Type::Text.wire()),
                                ("value", Json::str(format!("e{i}"))),
                            ])
                        })
                        .collect(),
                ),
            ),
            ("relations", Json::Arr(relations)),
            ("free_rank", Json::Nat(q.free_rank as u64)),
            (
                "torsion",
                Json::Arr(q.torsion.iter().map(|x| Json::str(x.to_string())).collect()),
            ),
            (
                "construction",
                Json::obj([("name", Json::str(name)), ("arguments", refs(&[hmap]))]),
            ),
        ]),
        arguments,
        None,
        None,
    )?;
    Ok((module, q))
}
fn kernel_cokernel(
    b: &mut Builder<'_>,
    source: NodeRef,
    target: NodeRef,
    hmap: NodeRef,
    map: &integer_fiber::Matrix,
    c: &mut Control,
) -> Result<(NodeRef, NodeRef, NodeRef, Decision), ValidationFailure> {
    let n = size(b.g, source)?;
    let m = size(b.g, target)?;
    let ring = field(b.g, source, "ring")?;
    let sr = rows(b.g, source, "relations")?;
    let tr = rows(b.g, target, "relations")?;
    let target_relations = from_columns(&tr, m)?;
    let equations = map
        .iter()
        .zip(&target_relations)
        .map(|(a, r)| a.iter().cloned().chain(r.iter().map(|x| -x)).collect())
        .collect();
    let fiber = integer_fiber::solve(&equations, n + tr.len(), &vec![Z::zero(); m], c)?;
    let preimage = fiber.kernel[..n].to_vec();
    let (basis, k) = linear::image(&preimage, n + tr.len() - fiber.rank, c)?;
    let relations = linear::coordinates(&basis, k, &from_columns(&sr, n)?, sr.len(), c)?;
    let (kernel, kq) = quotient_module(b, ring, &relations, sr.len(), k, "kernel", hmap, c)?;
    let kr = kq.free_rank + kq.torsion.len();
    let mut lift = vec![vec![Z::zero(); kr]; k];
    for j in 0..kr {
        let mut unit = vec![Z::zero(); kr];
        unit[j] = Z::from(1usize);
        let x = integer_fiber::solve(&kq.projection, k, &unit, c)?
            .particular
            .ok_or("核の商射影が全射でない")?;
        for i in 0..k {
            lift[i][j] = x[i].clone();
        }
    }
    let inclusion = integer_fiber::multiply(&basis, &lift, kr, c)?;
    let kernel_inclusion = wire::map(b, kernel, source, &inclusion, kr, c)?;
    let relations = target_relations
        .iter()
        .zip(map)
        .map(|(r, a)| r.iter().chain(a).cloned().collect())
        .collect();
    let (cokernel, cq) =
        quotient_module(b, ring, &relations, tr.len() + n, m, "quotient", hmap, c)?;
    let projection = wire::map(b, target, cokernel, &cq.projection, m, c)?;
    let status =
        if kq.free_rank == 0 && kq.torsion.is_empty() && cq.free_rank == 0 && cq.torsion.is_empty()
        {
            Decision::Established
        } else {
            Decision::Refuted
        };
    // Smith表示には自明なtorsion因子がないため、生成元総数が零 iff 核・余核が零。
    let generators = num_bigint::BigInt::from(kq.free_rank)
        + num_bigint::BigInt::from(kq.torsion.len())
        + num_bigint::BigInt::from(cq.free_rank)
        + num_bigint::BigInt::from(cq.torsion.len());
    let count = change_result::value(b, &Scalar::Z(generators))?;
    let zero = change_result::value(b, &Scalar::Z(0.into()))?;
    let condition = b.proposition(
        "equal",
        vec![count, zero],
        vec![hmap, kernel, cokernel, kernel_inclusion, projection],
        status,
    )?;
    Ok((kernel, cokernel, condition, status))
}
pub(super) fn compare(
    b: &mut Builder<'_>,
    request: &Request,
    left: NodeRef,
    right: NodeRef,
    along: NodeRef,
    transported: Option<&transport::Maps>,
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
        || (transported.is_none() && field(g, lc, "cover")? != field(g, rc, "cover")?)
    {
        return Err("同じ局所系の複体の表示が一致しない".into());
    }
    let (forward, backward) = if let Some(maps) = transported {
        (maps.forward.clone(), maps.inverse.clone())
    } else {
        let mut maps = vec![];
        for (a, z) in lm.iter().zip(&rm) {
            if !same_module(g, *a, *z)? {
                return Err("複体の同一座標の加群が一致しない".into());
            }
            maps.push(identity(size(g, *a)?));
        }
        (maps.clone(), Some(maps))
    };
    if forward.len() != lm.len() || backward.as_ref().is_some_and(|maps| maps.len() != lm.len()) {
        return Err("cochain写像の次数が違う".into());
    }
    let mut components = vec![];
    for i in 0..lm.len() {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let ns = size(g, lm[i])?;
        let nt = size(g, rm[i])?;
        if forward[i].len() != nt || forward[i].iter().any(|r| r.len() != ns) {
            return Err("cochain写像の順逆が一致しない".into());
        }
        if let Some(backward) = &backward {
            if backward[i].len() != ns
                || backward[i].iter().any(|r| r.len() != nt)
                || integer_fiber::multiply(&backward[i], &forward[i], ns, c)? != identity(ns)
                || integer_fiber::multiply(&forward[i], &backward[i], nt, c)? != identity(nt)
            {
                return Err("cochain写像の順逆が一致しない".into());
            }
        }
        components.push(wire::map(b, lm[i], rm[i], &forward[i], ns, c)?);
    }
    for i in 0..ld.len() {
        let source = map_matrix(g, ld[i])?;
        let target = map_matrix(g, rd[i])?;
        if integer_fiber::multiply(&target, &forward[i], size(g, lm[i])?, c)?
            != integer_fiber::multiply(&forward[i + 1], &source, size(g, lm[i])?, c)?
        {
            return Err("cochain写像と微分が可換でない".into());
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
    let n = size(g, lh)?;
    let target_n = size(g, rh)?;
    let (hforward, hbackward) = if transported.is_some() {
        let Some(Json::Nat(degree)) = record(g, left)?.get("degree") else {
            return Err("診断の次数がない".into());
        };
        let degree = usize::try_from(*degree)
            .map_err(|_| ValidationFailure::from("診断次数が大きすぎる"))?;
        let f = induced(
            g,
            ls,
            rs,
            forward.get(degree).ok_or("次数のcochain写像がない")?,
            c,
        )?;
        let v = if let Some(backward) = &backward {
            let v = induced(
                g,
                rs,
                ls,
                backward.get(degree).ok_or("次数の逆cochain写像がない")?,
                c,
            )?;
            check_inverse(g, lh, &v, &f, c)?;
            check_inverse(g, rh, &f, &v, c)?;
            Some(v)
        } else {
            None
        };
        (f, v)
    } else {
        if !same_module(g, lh, rh)?
            || !same_map(g, field(g, ls, "inclusion")?, field(g, rs, "inclusion")?)?
            || !same_map(g, field(g, ls, "projection")?, field(g, rs, "projection")?)?
        {
            return Err("同じ複体からのコホモロジー表示が一致しない".into());
        }
        (identity(n), Some(identity(n)))
    };
    let hmap = wire::map(b, lh, rh, &hforward, n, c)?;
    let ring = field(g, lh, "ring")?;
    let (kernel, cokernel, group_condition, group_status) = if let Some(backward) = &hbackward {
        let inverse = wire::map(b, rh, lh, backward, target_n, c)?;
        let kernel = wire::module(b, ring, 0, "kernel", vec![hmap])?;
        let cokernel = wire::module(b, ring, 0, "quotient", vec![hmap])?;
        let condition = b.proposition(
            "inverse_maps",
            vec![hmap, inverse],
            vec![cochain],
            Decision::Established,
        )?;
        (kernel, cokernel, condition, Decision::Established)
    } else {
        kernel_cokernel(b, lh, rh, hmap, &hforward, c)?
    };
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
        group_condition,
    ];
    let mut status = group_status;
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
            if x.len() != n || y.len() != target_n {
                return Err("対象類の座標次元が違う".into());
            }
            let x = linear::apply(&hforward, &x, c)?;
            let relations = rows(g, rh, "relations")?;
            let matrix = (0..target_n)
                .map(|i| relations.iter().map(|r| r[i].clone()).collect())
                .collect();
            let delta = x.iter().zip(&y).map(|(x, y)| x - y).collect::<Vec<_>>();
            let equal = integer_fiber::solve(&matrix, relations.len(), &delta, c)?
                .particular
                .is_some();
            let class_status = if equal {
                Decision::Established
            } else {
                Decision::Refuted
            };
            status = if group_status == Decision::Refuted || !equal {
                Decision::Refuted
            } else {
                Decision::Established
            };
            let transported = wire::vector(b, rh, &x, c)?;
            b.proposition(
                "equal",
                vec![transported, zv],
                vec![a, z, hmap],
                class_status,
            )?
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
