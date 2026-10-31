//! Tuple changeの独立入力と、移送の数学的な期待値。CLI配送処理は持たない。
use archsig::{canonical::Json, input::InputSources, json::JNode};
#[allow(dead_code)]
#[path = "architecture_environment.rs"]
mod architecture;
pub const REQUESTS: [&str; 3] = [
    "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
    "same=compare($m.operation,to=$m.operation,kind=action)",
    "n=needed($m)",
];
#[derive(Clone, Copy, Debug)]
pub struct Case {
    pub ty: &'static str,
    pub nested: bool,
    pub name: &'static str,
    pub code: i32,
    missing: bool,
    left: &'static str,
    right: &'static str,
    sg: &'static str,
    tg: &'static str,
}
pub fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for (ty, nested) in [("Z", false), ("Q", false), ("Z", true), ("Q", true)] {
        for (case, left, right, sg, tg, missing, code) in [
            (
                "same-fields",
                "free=s.free+pair.0+last+more.1,held=s.held",
                "free=t.free+next.0+final+tail.1,held=t.held",
                "",
                "",
                false,
                0,
            ),
            (
                "target-extra",
                "free=s.free+pair.0",
                "free=t.free+next.0,held=t.held",
                "",
                "",
                false,
                0,
            ),
            (
                "simultaneous",
                "free=s.held+pair.0,held=s.free",
                "free=t.held+next.0,held=t.free",
                "",
                "",
                false,
                0,
            ),
            (
                "slanted",
                "free=s.free",
                "free=t.free,held=t.held+next.0+next.1-3",
                " when pair.0+pair.1=3",
                " when next.0+next.1=3",
                false,
                0,
            ),
            (
                "fraction",
                "free=s.free",
                "free=t.free,held=t.held+tail.1",
                " when 2*more.1=1",
                " when 2*tail.1=1",
                false,
                if ty == "Q" { 1 } else { 0 },
            ),
            (
                "source-fraction",
                "free=s.free,held=s.held+more.1",
                "free=t.free",
                " when 2*more.1=1",
                " when 2*tail.1=1",
                false,
                if ty == "Q" { 1 } else { 0 },
            ),
            (
                "kernel",
                "free=s.free",
                "free=t.free,held=t.held+tail.1",
                " when pair.0=1",
                " when next.0=1",
                false,
                1,
            ),
            (
                "guard",
                "free=s.free",
                "free=t.free,held=t.held",
                " when pair.0=1",
                " when next.0=0",
                false,
                1,
            ),
            (
                "reverse-guard",
                "free=s.free",
                "free=t.free,held=t.held",
                " when pair.0=0",
                "",
                false,
                1,
            ),
            (
                "empty",
                "free=s.free",
                "free=t.free,held=t.held+tail.1",
                " when pair.0=0 and pair.0=1",
                " when next.0=0 and next.0=1",
                true,
                0,
            ),
            (
                "missing",
                "free=s.free",
                "free=t.free,held=t.held",
                "",
                "",
                true,
                2,
            ),
            (
                "partial",
                "free=s.free",
                "free=t.free,held=t.held+tail.1",
                "",
                "",
                true,
                1,
            ),
            (
                "nonlinear",
                "free=s.free",
                "free=t.free,held=t.held+tail.1*tail.1",
                "",
                "",
                false,
                2,
            ),
            (
                "inequality",
                "free=s.free",
                "free=t.free,held=t.held",
                " when pair.0>0",
                " when next.0>0",
                false,
                2,
            ),
            (
                "mixed",
                "free=s.free",
                "free=t.free,held=t.held",
                "",
                "",
                false,
                70,
            ),
        ] {
            out.push(Case {
                ty,
                nested,
                name: case,
                code,
                missing,
                left,
                right,
                sg,
                tg,
            });
        }
    }
    out
}
impl Case {
    pub fn input(&self) -> InputSources {
        let Self {
            ty,
            nested,
            name: case,
            left,
            right,
            sg,
            tg,
            missing,
            ..
        } = *self;
        let old = include_str!("../fixtures/reservations.atoms.json").to_string();
        let definition = if ty == "Q" {
            old.replace(
                r#""name": "free", "type": "Z""#,
                r#""name": "free", "type": "Q""#,
            )
            .replace(
                r#""name": "held", "type": "Z""#,
                r#""name": "held", "type": "Q""#,
            )
        } else {
            old.clone()
        };
        let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
        let after =
            archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        let digest = &after.vocabularies()["Reservations"].digest;
        let text = include_str!("../fixtures/object-configuration-map.archmap.json")
            .to_string()
            .replace(
                r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"4""#,
                r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"2""#,
            )
            .replace(
                r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"3""#,
                r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"1""#,
            )
            .replace(&before.vocabularies()["Reservations"].digest, digest);
        let mut archmap = architecture::owned(&archsig::json::parse(text.as_bytes()).unwrap());
        let atoms = architecture::atoms(&mut archmap);
        atoms.retain(|atom|!missing||!matches!(atom,Json::Obj(a) if a.get("subject")==Some(&Json::str("p"))&&a.get("field")==Some(&Json::str("Reservations.State.held"))));
        if ty == "Q" {
            for atom in atoms {
                let Json::Obj(a) = atom else { panic!("atom") };
                if matches!(a.get("field"),Some(Json::Str(f)) if matches!(f.as_str(),"Reservations.State.free"|"Reservations.State.held"))
                {
                    let n = a["value"].clone();
                    let d = if n == Json::str("0") { "1" } else { "3" };
                    a.insert("value".into(), Json::Arr(vec![n, Json::str(d)]));
                }
            }
        }
        let last_ty = if case == "mixed" {
            if ty == "Z" { "Q" } else { "Z" }
        } else {
            ty
        };
        let mut law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}";change tune(s:State,pair:({ty},{ty}),last:{last_ty},more:({ty},{ty})){sg}=s with {{{left}}};}}
reading After {{use vocabulary Reservations version "1" digest "{digest}";change tune(t:State,next:({ty},{ty}),final:{last_ty},tail:({ty},{ty})){tg}=t with {{{right}}};}}"#
        );
        if nested {
            law = law.replace(
                &format!("({ty},{ty})"),
                &format!("(({ty},{ty}),({ty},{ty}))"),
            );
            for name in ["pair", "next", "more", "tail"] {
                law = law
                    .replace(&format!("{name}.0"), &format!("{name}.0.0"))
                    .replace(&format!("{name}.1"), &format!("{name}.1.1"));
            }
        }
        InputSources::from_bytes(
            vec![definition.into_bytes()],
            law.into_bytes(),
            archmap.canonical().into_bytes(),
        )
    }
    pub fn label(&self) -> String {
        format!(
            "{}-{}-{}",
            self.ty,
            if self.nested { "nested" } else { "flat" },
            self.name
        )
    }
    pub fn assert_result(&self, result: &JNode) {
        let Self {
            ty,
            nested,
            name: case,
            code,
            missing,
            ..
        } = *self;
        let map = answer(&result, "m");
        assert_eq!(
            s(get(map, "status")),
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert_eq!(has(get(map, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let completed = value(&result, get(get(map, "outputs"), "map"));
            let transport = value(&result, &arr(get(completed, "transports"))[0]);
            for clause in arr(get(transport, "clauses")) {
                let qs = arr(get(value(&result, get(clause, "commutes")), "quantifiers"));
                assert_eq!(
                    qs.iter().map(|q| s(get(q, "name"))).collect::<Vec<_>>(),
                    ["s", "pair", "last", "more"]
                );
                assert!(has(&qs[0], "domain"));
                for q in &qs[1..] {
                    assert_eq!(s(get(q, "kind")), "forall");
                    assert!(!has(q, "domain"));
                }
                let args = value(&result, get(clause, "arguments"));
                assert_json(
                    &arr(get(args, "source_type"))[2],
                    &numeric_tuple_test_type(ty, nested),
                );
            }
        }
        if code == 1 {
            let examples = arr(get(map, "counterexamples"));
            assert!(!examples.is_empty());
            for example in examples {
                let data = get(value(&result, example), "data");
                let bs = arr(get(data, "bindings"));
                assert_eq!(
                    bs.iter().map(|b| s(get(b, "name"))).collect::<Vec<_>>(),
                    ["s", "pair", "last", "more"]
                );
                let pair = arr(value(&result, get(&bs[1], "value")));
                let more = arr(value(&result, get(&bs[3], "value")));
                assert_eq!(pair.len(), 2);
                assert_eq!(more.len(), 2);
                let pair = numeric_tuple_test_leaves(pair, nested);
                let more = numeric_tuple_test_leaves(more, nested);
                let q = |v: &JNode| {
                    if ty == "Z" {
                        (s(v).parse::<i128>().unwrap(), 1)
                    } else {
                        let a = arr(v);
                        (
                            s(&a[0]).parse::<i128>().unwrap(),
                            s(&a[1]).parse::<i128>().unwrap(),
                        )
                    }
                };
                let (a, ad) = q(&pair[0]);
                if case == "guard" {
                    assert_eq!(a, ad);
                    assert_json(value(&result, get(data, "left")), "true");
                    assert_json(value(&result, get(data, "right")), "false");
                } else if case == "reverse-guard" {
                    assert_ne!(a, 0);
                    assert_json(value(&result, get(data, "left")), "false");
                    assert_json(value(&result, get(data, "right")), "true");
                } else {
                    let (n, d) = q(&more[1]);
                    assert_ne!(n, 0);
                    if case.contains("fraction") {
                        assert_eq!((n, d), (1, 2));
                    }
                    if case == "kernel" {
                        assert_eq!(a, ad);
                    }
                    let (ln, ld) = q(value(&result, get(data, "left")));
                    let (rn, rd) = q(value(&result, get(data, "right")));
                    let delta = if case == "source-fraction" {
                        ln * rd - rn * ld
                    } else {
                        rn * ld - ln * rd
                    };
                    assert_eq!(delta * d, n * ld * rd);
                }
            }
        }
        if missing && case != "empty" {
            assert!(
                arr(get(map, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "missing_observation"
                        && !arr(get(r, "missing")).is_empty())
            );
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            if code == 2 {
                assert!(arr(get(plan, "requirements")).iter().any(|r| {
                    let f = get(r, "field");
                    s(get(f, "subject")) == "p" && s(get(f, "field")) == "Reservations.State.held"
                }));
            } else {
                assert!(arr(get(plan, "requirements")).is_empty());
            }
        }
        if matches!(case, "nonlinear" | "inequality") {
            assert!(
                arr(get(map, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "unsupported_algorithm")
            );
        }
    }
}
fn get<'a>(j: &'a JNode, k: &str) -> &'a JNode {
    let archsig::json::JValue::Obj(v) = &j.value else {
        panic!("object")
    };
    v.iter()
        .find(|(n, _)| n == k)
        .map(|(_, v)| v)
        .unwrap_or_else(|| {
            panic!(
                "missing {k}; keys: {:?}",
                v.iter().map(|(n, _)| n).collect::<Vec<_>>()
            )
        })
}
fn has(j: &JNode, k: &str) -> bool {
    let archsig::json::JValue::Obj(v) = &j.value else {
        panic!("object")
    };
    v.iter().any(|(n, _)| n == k)
}
fn arr(j: &JNode) -> &[JNode] {
    let archsig::json::JValue::Arr(v) = &j.value else {
        panic!("array")
    };
    v
}
fn s(j: &JNode) -> &str {
    let archsig::json::JValue::Str(v) = &j.value else {
        panic!("string")
    };
    v
}
fn answer<'a>(r: &'a JNode, id: &str) -> &'a JNode {
    arr(get(r, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn value<'a>(r: &'a JNode, reference: &JNode) -> &'a JNode {
    get(
        arr(get(r, "nodes"))
            .iter()
            .find(|n| s(get(n, "id")) == s(get(reference, "node")))
            .unwrap(),
        "value",
    )
}
fn assert_json(actual: &JNode, expected: &str) {
    assert_eq!(
        actual.value,
        archsig::json::parse(expected.as_bytes()).unwrap().value
    );
}
fn numeric_tuple_test_type(ty: &str, nested: bool) -> String {
    if nested {
        format!(r#"["Tuple",["Tuple","{ty}","{ty}"],["Tuple","{ty}","{ty}"]]"#)
    } else {
        format!(r#"["Tuple","{ty}","{ty}"]"#)
    }
}

fn numeric_tuple_test_leaves(values: &[JNode], nested: bool) -> Vec<&JNode> {
    if nested {
        assert_eq!(arr(&values[0]).len(), 2);
        assert_eq!(arr(&values[1]).len(), 2);
        vec![&arr(&values[0])[0], &arr(&values[1])[1]]
    } else {
        values.iter().collect()
    }
}
