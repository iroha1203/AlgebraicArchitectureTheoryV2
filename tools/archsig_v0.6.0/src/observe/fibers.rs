use super::*;
use std::collections::BTreeSet;

fn names(node: &JNode) -> Result<Vec<&str>> {
    let values = arr(node)?.iter().map(token).collect::<Result<Vec<_>>>()?;
    if values.iter().copied().collect::<BTreeSet<_>>().len() != values.len() {
        return Err(invalid("duplicate name"));
    }
    Ok(values)
}
fn exact(node: &JNode, expected: &[&str]) -> Result<()> {
    let fields = obj(node)?;
    if fields.len() != expected.len()
        || fields
            .iter()
            .any(|(key, _)| !expected.contains(&key.as_str()))
    {
        return Err(invalid(format!("expected exactly {expected:?}")));
    }
    Ok(())
}

pub(super) fn check(table: &JNode) -> Result<(Json, bool)> {
    check_inner(table).map_err(|mut issue| {
        if let ResultIssue::Input(issue) = issue.as_mut() {
            issue.location = Location::Definition {
                input: "table".into(),
                pointer: String::new(),
                span: None,
            };
        }
        issue
    })
}

fn check_inner(table: &JNode) -> Result<(Json, bool)> {
    exact(table, &["scope", "sources", "laws", "q", "v"])?;
    let scope = token(field(table, "scope")?)?;
    let sources = names(field(table, "sources")?)?;
    let laws = names(field(table, "laws")?)?;
    let q = field(table, "q")?;
    let v = field(table, "v")?;
    exact(q, &sources)?;
    exact(v, &sources)?;
    let mut rows = Vec::new();
    let mut q_groups: Vec<(&str, Vec<usize>)> = Vec::new();
    let mut joint_groups: Vec<(Vec<&str>, Vec<&str>)> = Vec::new();
    for (i, source) in sources.iter().enumerate() {
        let q_value = token(field(q, source)?)?;
        let row = field(v, source)?;
        exact(row, &laws)?;
        let values = laws
            .iter()
            .map(|law| token(field(row, law)?))
            .collect::<Result<Vec<_>>>()?;
        if let Some((_, members)) = q_groups.iter_mut().find(|(value, _)| *value == q_value) {
            members.push(i);
        } else {
            q_groups.push((q_value, vec![i]));
        }
        if let Some((_, members)) = joint_groups.iter_mut().find(|(value, _)| *value == values) {
            members.push(*source);
        } else {
            joint_groups.push((values.clone(), vec![*source]));
        }
        rows.push(values);
    }
    let mut witnesses = Vec::new();
    for (_, group) in &q_groups {
        for (offset, &left) in group.iter().enumerate() {
            for &right in &group[offset + 1..] {
                let differences: Vec<_> = laws
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| rows[left][*i] != rows[right][*i])
                    .map(|(_, law)| *law)
                    .collect();
                if !differences.is_empty() {
                    witnesses.push(Json::obj([
                        ("left", Json::str(sources[left])),
                        ("right", Json::str(sources[right])),
                        ("laws", strings(&differences)),
                    ]));
                }
            }
        }
    }
    let adequate = witnesses.is_empty();
    let mut result = BTreeMap::from([
        ("scope".into(), Json::str(scope)),
        ("source_count".into(), Json::Nat(sources.len() as u64)),
        ("law_count".into(), Json::Nat(laws.len() as u64)),
        ("adequate_on_table".into(), Json::Bool(adequate)),
        (
            "vacuous".into(),
            Json::Bool(sources.is_empty() || laws.is_empty()),
        ),
        (
            "q_partition".into(),
            Json::Arr(
                q_groups
                    .iter()
                    .map(|(_, group)| {
                        strings(&group.iter().map(|&i| sources[i]).collect::<Vec<_>>())
                    })
                    .collect(),
            ),
        ),
        (
            "joint_law_partition".into(),
            Json::Arr(
                joint_groups
                    .iter()
                    .map(|(_, group)| strings(group))
                    .collect(),
            ),
        ),
        ("counterexamples".into(), Json::Arr(witnesses)),
    ]);
    if adequate {
        result.insert(
            "descent".into(),
            Json::Obj(
                q_groups
                    .iter()
                    .map(|(q, group)| {
                        (
                            (*q).into(),
                            Json::Obj(
                                laws.iter()
                                    .zip(&rows[group[0]])
                                    .map(|(law, value)| ((*law).into(), Json::str(*value)))
                                    .collect(),
                            ),
                        )
                    })
                    .collect(),
            ),
        );
    }
    Ok((Json::Obj(result), adequate))
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_common::json::parse;
    fn check_text(text: &str) -> Result<(Json, bool)> {
        check(&parse(text.as_bytes()).unwrap())
    }
    #[test]
    fn exhaustive_three_sources_two_binary_laws() {
        for bits in 0..512 {
            let bit = |i: usize| -> u32 { (bits >> i) & 1 };
            let text = format!(
                r#"{{"scope":"finite","sources":["a","b","c"],"laws":["x","y"],"q":{{"a":"{}","b":"{}","c":"{}"}},"v":{{"a":{{"x":"{}","y":"{}"}},"b":{{"x":"{}","y":"{}"}},"c":{{"x":"{}","y":"{}"}}}}}}"#,
                bit(0),
                bit(1),
                bit(2),
                bit(3),
                bit(4),
                bit(5),
                bit(6),
                bit(7),
                bit(8)
            );
            let (output, adequate) = check_text(&text).unwrap();
            let same = |a, b| bit(3 + 2 * a) == bit(3 + 2 * b) && bit(4 + 2 * a) == bit(4 + 2 * b);
            let expected = (0..3).all(|a| (0..3).all(|b| bit(a) != bit(b) || same(a, b)));
            assert_eq!(adequate, expected, "{text}");
            let Json::Obj(ref fields) = output else {
                panic!()
            };
            assert_eq!(fields.contains_key("descent"), expected);
            let Json::Arr(classes) = &fields["joint_law_partition"] else {
                panic!()
            };
            for a in 0..3 {
                for b in 0..3 {
                    let name = |i| Json::str(["a", "b", "c"][i]);
                    let together = classes.iter().any(|group| matches!(group, Json::Arr(m) if m.contains(&name(a)) && m.contains(&name(b))));
                    assert_eq!(together, same(a, b));
                }
            }
            if let Some(Json::Obj(descent)) = fields.get("descent") {
                for a in 0..3 {
                    assert_eq!(
                        descent[&bit(a).to_string()],
                        Json::obj([
                            ("x", Json::str(bit(3 + 2 * a).to_string())),
                            ("y", Json::str(bit(4 + 2 * a).to_string()))
                        ])
                    );
                }
            }
        }
    }
    #[test]
    fn empty_and_incomplete_tables() {
        for (text, partition) in [
            (
                r#"{"scope":"empty","sources":[],"laws":["x"],"q":{},"v":{}}"#,
                Json::Arr(vec![]),
            ),
            (
                r#"{"scope":"empty laws","sources":["a","b"],"laws":[],"q":{"a":"one","b":"two"},"v":{"a":{},"b":{}}}"#,
                Json::Arr(vec![strings(&["a", "b"])]),
            ),
        ] {
            let (result, adequate) = check_text(text).unwrap();
            assert!(adequate);
            let Json::Obj(ref fields) = result else {
                panic!()
            };
            assert_eq!(fields["vacuous"], Json::Bool(true));
            assert_eq!(fields["joint_law_partition"], partition);
        }
        let valid = r#"{"scope":"one","sources":["a"],"laws":["x"],"q":{"a":"same"},"v":{"a":{"x":"yes"}}}"#;
        for (from, to) in [
            ("[\"a\"]", "[\"a\",\"a\"]"),
            ("[\"x\"]", "[\"x\",\"x\"]"),
            ("\"same\"", "true"),
            ("\"yes\"", "null"),
            ("\"yes\"", "\"\""),
            ("\"x\":\"yes\"", ""),
            ("\"a\":\"same\"", ""),
            ("\"scope\":", "\"extra\":0,\"scope\":"),
        ] {
            assert!(
                check_text(&valid.replace(from, to)).is_err(),
                "{from} => {to}"
            );
        }
    }
}
