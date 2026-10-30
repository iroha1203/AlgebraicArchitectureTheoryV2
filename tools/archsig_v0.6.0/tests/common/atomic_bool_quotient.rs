use super::*;

mod bool_fixture {
    include!("finite_data_quotient.rs");
}
fn bool_result(extra: &str, asks: &[&str]) -> JNode {
    use archsig::observed::{
        control::{Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
    };
    let result = evaluate_observed_bytes(
        bool_fixture::sources("", extra),
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    archsig::json::parse(result.wire().canonical().as_bytes()).unwrap()
}
#[test]
fn atomic_bool_law_keeps_false_values_and_actual_separating_witnesses() {
    let result = bool_result(
        "view first(s:State):Bool=s.x;view last(s:State):Bool=s.y;law optional grouped(s:State):((s.x));",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "good=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.valid)",
            "bad=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.valid)",
            "grouped=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.grouped)",
        ],
    );
    let answers = arr(get(&result, "answers"));
    for index in [1, 3] {
        assert_eq!(s(get(&answers[index], "status")), "established");
        let map = node(&result, get(quotient(&result, index), "descent"));
        let mut values = vec![];
        for entry in arr(get(get(map, "value"), "pairs")) {
            let entry = arr(entry);
            let class = members(get(node(&result, &entry[0]), "value"));
            let family = arr(get(node(&result, &entry[1]), "value"));
            assert_eq!(family.len(), 1);
            let value = get(&arr(&family[0])[1], "some");
            assert_eq!(value.value, JValue::Bool(class[0].0));
            values.push(matches!(value.value, JValue::Bool(true)));
        }
        assert!(values.contains(&false) && values.contains(&true));
    }
    assert_eq!(s(get(&answers[2], "status")), "refuted");
    let witness = node(&result, &arr(get(&answers[2], "evidence"))[0]);
    let data = get(get(witness, "value"), "data");
    let first = pair(get(node(&result, get(data, "first")), "value"));
    let second = pair(get(node(&result, get(data, "second")), "value"));
    assert_eq!(first.1, second.1);
    assert_ne!(first.0, second.0);
    for (value, expected) in arr(get(data, "law_values")).iter().zip([first.0, second.0]) {
        let family = arr(get(node(&result, value), "value"));
        assert_eq!(
            get(&arr(&family[0])[1], "some").value,
            JValue::Bool(expected)
        );
    }
}
#[test]
fn atomic_bool_bound_keys_literals_and_parenthesized_equality_keep_their_types() {
    let result = bool_result(
        "view first(s:State):Bool=s.x;view fixed():Bool=false;view yes():Bool=true;law optional bound(b:Bool,s:State,a:Bool):((b));law optional literal(s:State):((false));law optional same(s:State):((s.y=s.y));",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "v=evaluate(Pair.yes)",
            "f=evaluate(Pair.fixed)",
            "q=quotient(Pair.first,on=$s.domain,a=$f.value,s=@v/s,b=$v.value,law=Pair.bound)",
            "literal=quotient(Pair.fixed,on=$s.domain,s=@v/s,law=Pair.literal)",
            "equal=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.same)",
        ],
    );
    let answers = arr(get(&result, "answers"));
    for index in [3, 4] {
        assert_eq!(s(get(&answers[index], "status")), "established");
    }
    for entry in arr(get(
        get(node(&result, get(quotient(&result, 3), "descent")), "value"),
        "pairs",
    )) {
        let family = arr(get(node(&result, &arr(entry)[1]), "value"));
        let item = arr(&family[0]);
        let key = arr(&item[0]);
        assert_eq!(key.len(), 3);
        assert_eq!(key[0].value, JValue::Bool(true));
        assert_eq!(key[2].value, JValue::Bool(false));
        assert_eq!(s(&arr(&key[1])[0]), "v");
        assert_eq!(s(&arr(&key[1])[1]), "s");
        assert_eq!(get(&item[1], "some").value, JValue::Bool(true));
    }
    assert_eq!(s(get(&answers[5], "status")), "refuted");
    let witness = node(&result, &arr(get(&answers[5], "evidence"))[0]);
    for value in arr(get(get(get(witness, "value"), "data"), "law_values")) {
        let family = arr(get(node(&result, value), "value"));
        let operands = arr(get(&arr(&family[0])[1], "some"));
        assert_eq!(operands.len(), 2);
        assert_eq!(operands[0].value, operands[1].value);
    }
}
#[test]
fn compound_bool_observations_preserve_equality_values() {
    for (params, body, expected) in [
        ("s:State", "s.x and s.y", "refuted"),
        ("s:State", "not s.x", "established"),
        ("s:State", "if s.y then s.x else false", "refuted"),
        ("s:State", "first(s)", "established"),
        ("s:State", "forall b:Bool . b", "established"),
        ("s:State,b:Bool", "b", "established"),
        ("s:State", "(s.y=s.y) and true", "refuted"),
        ("s:State", "if true then s.y=s.y else true", "refuted"),
        ("s:State", "forall b:Bool . (s.y=b)", "refuted"),
    ] {
        let extra = format!("view first(s:State):Bool=s.x;law optional test({params}):{body};");
        let result = bool_result(
            &extra,
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.test)",
            ],
        );
        assert_eq!(
            s(get(&arr(get(&result, "answers"))[1], "status")),
            expected,
            "{body}"
        );
    }
}
#[test]
fn atomic_bool_cli_saves_and_reuses_checked_families() {
    let dir = law_input("quotient-atomic-bool-cli", "view first(s:State):Bool=s.x;");
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.valid)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 0, "{} {}", first.stdout, first.stderr);
    let result = result_json(&dir, &first);
    let repeated = execute(&dir, "reuse", &asks, Some("out"));
    assert_eq!(repeated.code, 0, "{} {}", repeated.stdout, repeated.stderr);
    let reused = result_json(&dir, &repeated);
    for key in ["answers", "nodes"] {
        assert_eq!(get(&result, key).value, get(&reused, key).value);
    }
}
#[test]
fn atomic_bool_guard_false_and_body_false_remain_different_and_unknown_guard_is_not_erased() {
    use archsig::observed::{
        control::{Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
        input::InputSources,
    };
    let original = bool_fixture::sources(
        "",
        "view fixed(s:State):Bool=false;law optional gated(s:State) when s.y:s.x;",
    );
    let law = String::from_utf8(original.law().bytes().to_vec())
        .unwrap()
        .replace("with{x=a,y=b}", "with{x=a}");
    let map = String::from_utf8(original.archmap().bytes().to_vec()).unwrap();
    let missing = map.replace(
        r#",{"id":"y","subject":"s","field":"Pair.State.y","value":false,"origin":"o"}"#,
        "",
    );
    for (map, expected) in [
        (map.clone(), "established"),
        (
            map.replace(
                r#""field":"Pair.State.y","value":false"#,
                r#""field":"Pair.State.y","value":true"#,
            ),
            "refuted",
        ),
        (missing, "undetermined"),
    ] {
        let sources = InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.as_bytes().to_vec(),
            map.into_bytes(),
        );
        let result = evaluate_observed_bytes(
            sources,
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "q=quotient(Pair.fixed,on=$s.domain,s=@v/s,law=Pair.gated)",
            ],
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        let result = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answer = &arr(get(&result, "answers"))[1];
        assert_eq!(s(get(answer, "status")), expected);
        if expected == "undetermined" {
            assert!(!has(get(answer, "outputs"), "quotient"));
            assert!(format!("{:?}", get(answer, "reasons")).contains("Pair.State.y"));
        } else if expected == "established" {
            let map = node(&result, get(quotient(&result, 1), "descent"));
            let pairs = arr(get(get(map, "value"), "pairs"));
            assert_eq!(pairs.len(), 1);
            let family = arr(get(node(&result, &arr(&pairs[0])[1]), "value"));
            assert!(has(&arr(&family[0])[1], "none"));
        } else {
            let witness = node(&result, &arr(get(answer, "evidence"))[0]);
            let families = arr(get(get(get(witness, "value"), "data"), "law_values"));
            let mut values = vec![];
            for family in families {
                let family = arr(get(node(&result, family), "value"));
                values.push(matches!(
                    get(&arr(&family[0])[1], "some").value,
                    JValue::Bool(true)
                ));
            }
            assert!(values.contains(&false) && values.contains(&true));
        }
    }
}

#[test]
fn atomic_bool_evaluation_stop_keeps_prior_solve_and_exact_reason() {
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
    };
    use std::{cell::Cell, rc::Rc};
    for mode in 0..4 {
        let active = Rc::new(Cell::new(false));
        let stopped = Rc::new(Cell::new(false));
        let (inside, hit) = (active.clone(), stopped.clone());
        let mut control = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |point| {
                if point == Checkpoint::Quotient {
                    inside.set(true);
                }
                if inside.get() && point == Checkpoint::FiniteLawOperand {
                    hit.set(true);
                }
                if hit.get() {
                    match mode {
                        0 => Usage {
                            elapsed_ms: 2,
                            ..Usage::default()
                        },
                        1 => Usage {
                            memory_mib: 2,
                            ..Usage::default()
                        },
                        _ => Usage {
                            signal: Some(if mode == 2 {
                                archsig::result::Signal::Int
                            } else {
                                archsig::result::Signal::Term
                            }),
                            ..Usage::default()
                        },
                    }
                } else {
                    Usage::default()
                }
            },
        );
        let result = evaluate_observed_bytes(
            bool_fixture::sources("", "view first(s:State):Bool=s.x;"),
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.valid)",
            ],
            &mut control,
        )
        .unwrap();
        assert!(stopped.get());
        let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        assert_eq!(s(get(&answers[0], "status")), "established");
        assert_eq!(s(get(&answers[1], "status")), "undetermined");
        assert!(!has(get(&answers[1], "outputs"), "quotient"));
        let reasons = format!("{:?}", get(&answers[1], "reasons"));
        for expected in match mode {
            0 => vec!["budget_exhausted", "time_ms"],
            1 => vec!["budget_exhausted", "memory_mib"],
            2 => vec!["cancelled", "SIGINT"],
            _ => vec!["cancelled", "SIGTERM"],
        } {
            assert!(reasons.contains(expected), "{reasons}");
        }
    }
}

#[test]
fn compound_missing_reads_follow_selected_branch_and_short_circuit() {
    use archsig::observed::{
        control::{Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
        input::InputSources,
    };
    for (body, expected) in [
        ("if false then s.y else s.x", "established"),
        ("if true then s.x else s.y", "established"),
        ("false and s.y", "established"),
        ("true or s.y", "established"),
        ("if s.y then true else true", "undetermined"),
        ("true and s.y", "undetermined"),
        ("forall b:Bool . s.y or b", "undetermined"),
    ] {
        let original = bool_fixture::sources(
            "",
            &format!("view first(s:State):Bool=s.x;law optional test(s:State):{body};"),
        );
        let law = String::from_utf8(original.law().bytes().to_vec())
            .unwrap()
            .replace("with{x=a,y=b}", "with{x=a}");
        let map = String::from_utf8(original.archmap().bytes().to_vec())
            .unwrap()
            .replace(
                r#",{"id":"y","subject":"s","field":"Pair.State.y","value":false,"origin":"o"}"#,
                "",
            );
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                original
                    .definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                law.into_bytes(),
                map.into_bytes(),
            ),
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.test)",
            ],
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        let result = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answer = &arr(get(&result, "answers"))[1];
        assert_eq!(s(get(answer, "status")), expected, "{body}");
        if expected == "undetermined" {
            assert!(!has(get(answer, "outputs"), "quotient"));
        }
    }
}

#[test]
fn compound_named_boundary_and_quantified_values_are_explicit() {
    let result = bool_result(
        "view first(s:State):Bool=s.x;view same(s:State):Bool=s.y=s.y;law optional named(s:State):same(s);law optional quantified(s:State):forall b:Bool . s.y=b;",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "named=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.named)",
            "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.quantified)",
        ],
    );
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[1], "status")),
        "established"
    );
    let answer = &arr(get(&result, "answers"))[2];
    assert_eq!(s(get(answer, "status")), "refuted");
    let witness = node(&result, &arr(get(answer, "evidence"))[0]);
    let families = arr(get(get(get(witness, "value"), "data"), "law_values"));
    for family in families {
        let family = arr(get(node(&result, family), "value"));
        let observations = arr(get(&arr(&family[0])[1], "some"));
        assert_eq!(observations.len(), 2);
        let mut bindings = vec![];
        for observation in observations {
            let pair = arr(observation);
            let operands = arr(&pair[1]);
            assert_eq!(pair[0].value, operands[1].value);
            bindings.push(matches!(pair[0].value, JValue::Bool(true)));
        }
        assert!(bindings.contains(&false) && bindings.contains(&true));
    }
}

#[test]
fn compound_cli_refutation_save_reuse_and_tamper() {
    let dir = law_input(
        "quotient-compound-cli",
        "law optional wrapped(s:State):(s.x=s.x) and true;",
    );
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.wrapped)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 1, "{} {}", first.stdout, first.stderr);
    let result = result_json(&dir, &first);
    let repeated = execute(&dir, "reused", &asks, Some("out"));
    assert_eq!(repeated.code, 1, "{} {}", repeated.stdout, repeated.stderr);
    let reused = result_json(&dir, &repeated);
    for key in ["answers", "nodes"] {
        assert_eq!(get(&result, key).value, get(&reused, key).value);
    }
    let path = dir.join(s(get(&first.receipt, "result")));
    let saved = std::fs::read_to_string(&path).unwrap();
    for (index, changed) in [
        saved.replace("refuted", "established"),
        saved.replace("false", "true"),
    ]
    .into_iter()
    .enumerate()
    {
        assert_ne!(saved, changed);
        std::fs::write(&path, changed).unwrap();
        let rejected = execute(&dir, &format!("tampered-{index}"), &asks, Some("out"));
        assert_eq!(rejected.code, 1, "{} {}", rejected.stdout, rejected.stderr);
        let rebuilt = result_json(&dir, &rejected);
        for key in ["answers", "nodes"] {
            assert_eq!(get(&result, key).value, get(&rebuilt, key).value);
        }
        assert!(!warnings(&rebuilt).is_empty());
        assert_eq!(
            s(get(get(&warnings(&rebuilt)[0], "details"), "argument")),
            "--reuse"
        );
    }
}

#[test]
fn compound_quantifier_empty_finite_and_symbolic_infinite_are_distinct() {
    use archsig::observed::{
        control::{Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
        result::EvaluationFailure,
    };
    let result = bool_result(
        "view first(s:State):Bool=s.x;law optional empty_family(s:State):forall b in list<Bool>[] . b;",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.empty_family)",
        ],
    );
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[1], "status")),
        "established"
    );
    let map = node(&result, get(quotient(&result, 1), "descent"));
    for entry in arr(get(get(map, "value"), "pairs")) {
        let family = arr(get(node(&result, &arr(entry)[1]), "value"));
        assert!(arr(get(&arr(&family[0])[1], "some")).is_empty());
    }
    let result = evaluate_observed_bytes(
        bool_fixture::sources(
            "",
            "view first(s:State):Bool=s.x;law optional infinite(s:State):forall z:Z . forall w:Z . true;",
        ),
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.infinite)",
        ],
        &mut Control::new(Limits::default(), |_| Usage::default()),
    );
    assert!(
        matches!(result, Err(EvaluationFailure::NotImplemented { .. })),
        "{result:?}"
    );
}

#[test]
fn compound_nested_finite_quantifiers_keep_every_binding_and_operand() {
    let result = bool_result(
        "view first(s:State):Bool=s.x;law optional nested(s:State):forall b:Bool . forall c:Bool . (s.y,b)=(c,b);",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.first,on=$s.domain,s=@v/s,law=Pair.nested)",
        ],
    );
    let answer = &arr(get(&result, "answers"))[1];
    assert_eq!(s(get(answer, "status")), "refuted");
    let witness = node(&result, &arr(get(answer, "evidence"))[0]);
    for family in arr(get(get(get(witness, "value"), "data"), "law_values")) {
        let family = arr(get(node(&result, family), "value"));
        let outer = arr(get(&arr(&family[0])[1], "some"));
        assert_eq!(outer.len(), 2);
        for b in outer {
            let b = arr(b);
            let inner = arr(&b[1]);
            assert_eq!(inner.len(), 2);
            for c in inner {
                let c = arr(c);
                let operands = arr(&c[1]);
                assert_eq!(arr(&operands[0])[1].value, b[0].value);
                assert_eq!(arr(&operands[1])[0].value, c[0].value);
                assert_eq!(arr(&operands[1])[1].value, b[0].value);
            }
        }
    }
}
