//! 公開buildから後続の実評価までを、独立した三入力で検査する。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::json::JNode;
use cli::*;
use std::path::{Path, PathBuf};

const DEFINITION: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Build","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Build.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Build.Part","meaning":"部分。","parameters":[{"name":"owner","type":["Ref","Build.Root"],"meaning":"所属。"}],"fields":[{"name":"quantity","type":"Z","meaning":"数量。"}],"alignments":[]}]}]}"#;
const BODY: &str = "view amount(c:Part):Z=c.quantity;law required zero(c:Part):c.quantity=0;";
#[test]
fn universal_numeric_laws_build_objects_for_later_queries() {
    for ty in ["Z", "Q"] {
        let dir=files(&format!("universal-build-{ty}"),&format!("view amount(c:Part):Z=c.quantity;law required reflexive(c:Part,n:{ty}):n=n;"),false);
        let run=asks(&dir,&["b=build(R,on=@v/root)","n=evaluate(R.amount,on=$b.object,c=@v/q)","l=localize($b.object)","d=diagnose($l.system,degree=0)"]);
        let result=saved(&dir,&run,"complete",0);
        let outputs=get(answer(&result,"b"),"outputs");
        assert!(has(outputs,"object") && has(outputs,"algebra"));
        assert_eq!(s(value(&result,get(get(answer(&result,"n"),"outputs"),"value"))),"1");
        assert_eq!(s(get(answer(&result,"d"),"status")),"established");
    }
}
#[test]
fn constant_numeric_families_build_without_samples_and_reuse_compact_results() {
    for ty in ["Z", "Q"] {
        for offset in [0, 1] {
            let dir = files(&format!("constant-family-{ty}-{offset}"), &format!(
                "law required balanced(c:Part,n:{ty},m:{ty}):let a=n+m in a=n+m+{offset};"
            ), false);
            let requests = ["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/p)"];
            let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
            for request in requests { args.extend(["--ask", request]); }
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, offset, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            let summary = archsig::json::parse(normal.stdout.as_bytes()).unwrap();
            assert_eq!(s(get(&summary, "format")), "archsig.summary/1");
            assert!(!has(&summary, "nodes"));
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            eprintln!("constant family {ty}/{offset}: stdout {} bytes", normal.stdout.len());
            let run = asks(&dir, &requests);
            let result = saved(&dir, &run, "complete", offset);
            eprintln!("constant family {ty}/{offset}: saved {} bytes", std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
            assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
            assert_eq!(s(get(answer(&result, "c"), "status")), if offset == 0 { "established" } else { "refuted" });
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, run.code, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            for field in ["answers", "nodes"] {
                assert_eq!(get(&again, field).value, get(&result, field).value);
            }
        }
    }
}
#[test]
fn rational_literals_in_universal_laws_feed_public_build_and_checks() {
    for (rhs, code) in [("n+rat(2,4)", 0), ("n", 1)] {
        let dir = files(&format!("rational-family-{code}"), &format!(
            "law required balanced(c:Part,n:Q):n+rat(1,2)={rhs};"
        ), false);
        let run = asks(&dir, &["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/p)"]);
        let result = saved(&dir, &run, "complete", code);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "c"), "status")), if code == 0 { "established" } else { "refuted" });
    }
}
fn files(name: &str, body: &str, missing: bool) -> PathBuf {
    let dir = workdir(name);
    let defs =
        archsig::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())]).unwrap();
    let digest = &defs.vocabularies["Build"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading R{{use vocabulary Build version \"1\" digest \"{digest}\";{body}}}"
    );
    let quantity = if missing {
        ""
    } else {
        r#",{"id":"xq","subject":"q","field":"Build.Part.quantity","value":"1","origin":"model"}"#
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Build","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"独立の公開構成入力。","locations":[],"note":"p=0、q=1。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"root","type":"Build.Root","origin":"model"}},{{"id":"p","type":"Build.Part","origin":"model"}},{{"id":"q","type":"Build.Part","origin":"model"}}],"atoms":[{{"id":"op","subject":"p","field":"Build.Part.owner","value":["v","root"],"origin":"model"}},{{"id":"oq","subject":"q","field":"Build.Part.owner","value":["v","root"],"origin":"model"}},{{"id":"xp","subject":"p","field":"Build.Part.quantity","value":"0","origin":"model"}}{quantity}]}}]}}"#
    );
    for (name, bytes) in [
        ("d.json", DEFINITION.as_bytes()),
        ("l.law", law.as_bytes()),
        ("a.json", map.as_bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn asks(dir: &Path, requests: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "out",
        "--time-ms",
        "120000",
    ];
    for request in requests {
        args.extend(["--ask", request]);
    }
    run(dir, &args)
}
fn answer<'a>(r: &'a JNode, id: &str) -> &'a JNode {
    arr(get(r, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(r: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(r, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn value<'a>(r: &'a JNode, reference: &JNode) -> &'a JNode {
    get(node(r, reference), "value")
}
fn saved(dir: &Path, run: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(run.code, code, "{}", run.stdout);
    assert_eq!(s(get(&run.receipt, "status")), status);
    assert_eq!(num(get(&run.receipt, "exit_code")), code as u64);
    let result = result_json(dir, run);
    assert_eq!(s(get(&result, "command")), "run");
    assert_eq!(s(get(&result, "status")), status);
    assert_eq!(num(get(&result, "exit_code")), code as u64);
    for (src, dst) in [
        ("d.json", "inputs/definitions/0.json"),
        ("l.law", "inputs/law.law"),
        ("a.json", "inputs/archmap.json"),
    ] {
        assert_eq!(
            std::fs::read(dir.join(src)).unwrap(),
            std::fs::read(dir.join("out").join(dst)).unwrap()
        );
    }
    result
}

#[test]
fn build_publishes_the_complete_algebra_and_its_object_drives_later_evaluation() {
    let dir = files("public-build-algebra", BODY, false);
    // 指定順と依存順を別にし、同じ完成Architectureを後続で消費する。
    let run = asks(
        &dir,
        &[
            "n=evaluate(R.amount,on=$b.object,c=@v/q)",
            "b=build(R,on=@v/root)",
            "ok=check(R.zero,on=$b.object,c=@v/q)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    let b = answer(&result, "b");
    assert_eq!(s(get(b, "status")), "established");
    let outputs = get(b, "outputs");
    for key in ["proposition", "object", "algebra"] {
        get(outputs, key);
    }
    let object = value(&result, get(outputs, "object"));
    assert_eq!(s(get(object, "reading")), "R");
    let algebra = value(&result, get(outputs, "algebra"));
    assert_eq!(arr(get(algebra, "objects")).len(), 3);
    let extension = get(algebra, "extension");
    assert_eq!(s(get(extension, "kind")), "finite_pattern");
    assert_eq!(arr(get(extension, "profiles")).len(), 3);
    get(extension, "compatibility");
    let equations = value(&result, get(algebra, "equations"));
    assert_eq!(arr(get(equations, "indices")).len(), 2);
    assert_eq!(arr(get(equations, "objects")).len(), 3);
    assert!(!arr(get(algebra, "circuits")).is_empty());
    assert_eq!(arr(get(algebra, "invariants")).len(), 4);
    assert_eq!(arr(get(algebra, "signature")).len(), 2);
    assert_eq!(
        s(get(get(algebra, "operations"), "kind")),
        "typed_free_words"
    );
    let n = answer(&result, "n");
    assert_eq!(s(get(n, "status")), "established");
    assert_eq!(s(value(&result, get(get(n, "outputs"), "value"))), "1");
    assert_eq!(s(get(answer(&result, "ok"), "status")), "refuted");
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn missing_readings_keep_the_constructed_object_and_the_actual_needed_slot() {
    let dir = files("public-build-missing", BODY, true);
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "n=evaluate(R.amount,on=$b.object,c=@v/q)",
            "plan=needed($b)",
        ],
    );
    let result = saved(&dir, &run, "partial", 2);
    let b = answer(&result, "b");
    assert_eq!(s(get(b, "status")), "undetermined");
    assert!(has(get(b, "outputs"), "object"));
    assert!(!has(get(b, "outputs"), "algebra"));
    let n = answer(&result, "n");
    assert_eq!(s(get(n, "status")), "undetermined");
    assert!(arr(get(n, "reasons")).iter().any(|r| {
        s(get(r, "code")) == "missing_observation"
            && arr(get(r, "missing"))
                .iter()
                .any(|p| s(get(p, "subject")) == "q" && s(get(p, "field")) == "Build.Part.quantity")
    }));
    assert!(has(get(answer(&result, "plan"), "outputs"), "plan"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn algebra_base_supplies_a_public_root_handle_and_architecture() {
    let dir = files("public-build-handle", BODY, false);
    let run = asks(
        &dir,
        &[
            "a=build(R,on=$b.algebra.base.subject)",
            "b=build(R,on=@v/root)",
            "n=evaluate(R.amount,on=$a.algebra.base.object,c=@v/q)",
        ],
    );
    let result = saved(&dir, &run, "complete", 0);
    for id in ["a", "b", "n"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    assert_eq!(
        s(value(
            &result,
            get(get(answer(&result, "n"), "outputs"), "value")
        )),
        "1"
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn finite_guarded_law_and_value_parameters_flow_through_public_build() {
    let dir = files(
        "public-build-finite",
        "view enabled():Bool=true;view amount(c:Part):Fp(2)=c.quantity;law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        false,
    );
    let old =
        archsig::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())]).unwrap();
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Fp","2"]"#);
    let new =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    std::fs::write(dir.join("d.json"), definition).unwrap();
    for name in ["l.law", "a.json"] {
        let text = std::fs::read_to_string(dir.join(name)).unwrap().replace(
            &old.vocabularies["Build"].digest,
            &new.vocabularies["Build"].digest,
        );
        std::fs::write(dir.join(name), text).unwrap();
    }
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "n=evaluate(R.amount,on=$b.object,c=@v/q)",
            "flag=evaluate(R.enabled,on=$b.object)",
            "bad=check(R.bit,on=$b.object,c=@v/q,b=$flag.value)",
            "good=check(R.bit,on=$b.object,c=@v/p,b=$flag.value)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    assert_eq!(s(get(answer(&result, "b"), "status")), "established");
    let algebra = value(
        &result,
        get(get(answer(&result, "b"), "outputs"), "algebra"),
    );
    assert_eq!(arr(get(algebra, "circuits")).len(), 4);
    assert_eq!(
        s(value(
            &result,
            get(get(answer(&result, "n"), "outputs"), "value")
        )),
        "1"
    );
    assert_eq!(s(get(answer(&result, "bad"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "good"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn tuple_equations_keep_zero_components_out_of_refutation() {
    let dir = files(
        "public-build-tuple",
        "law required pair(c:Part):(c.quantity,0)=(0,0);",
        false,
    );
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "bad=check(R.pair,on=$b.object,c=@v/q)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    let algebra = value(
        &result,
        get(get(answer(&result, "b"), "outputs"), "algebra"),
    );
    let detectors = arr(get(algebra, "circuits"));
    assert_eq!(detectors.len(), 4);
    let mut refuted_first = false;
    for detector in detectors {
        let detector = value(&result, detector);
        let component = arr(get(detector, "component"));
        assert_eq!(component.len(), 1);
        for case in arr(get(detector, "cases")) {
            let case = value(&result, case);
            let evaluation = value(&result, get(case, "refutation"));
            let decision = &value(&result, get(evaluation, "value")).value;
            if num(&component[0]) == 1 {
                assert!(matches!(decision, archsig::json::JValue::Bool(false)));
            } else if matches!(decision, archsig::json::JValue::Bool(true)) {
                refuted_first = true;
            }
        }
    }
    assert!(refuted_first);
    assert_eq!(s(get(answer(&result, "bad"), "status")), "refuted");
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn owned_arrow_is_published_as_a_checked_generator() {
    let dir = files("public-build-arrow", BODY, false);
    let arrow = r#"{"kind":"arrow","name":"Build.Step","meaning":"部分間の操作。","parameters":[{"name":"owner","type":["Ref","Build.Root"],"meaning":"所属。"},{"name":"from","type":["Owned","Build.Part","owner"],"meaning":"始点。"},{"name":"to","type":["Owned","Build.Part","owner"],"meaning":"終点。"}],"fields":[],"alignments":[]}"#;
    let definition = format!(
        "{},{}]}}]}}",
        DEFINITION.strip_suffix("]}]}").unwrap(),
        arrow
    );
    let old =
        archsig::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())]).unwrap();
    let new =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    std::fs::write(dir.join("d.json"), definition).unwrap();
    for name in ["l.law", "a.json"] {
        let text = std::fs::read_to_string(dir.join(name)).unwrap().replace(
            &old.vocabularies["Build"].digest,
            &new.vocabularies["Build"].digest,
        );
        std::fs::write(dir.join(name), text).unwrap();
    }
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(
            r#"{"id":"q","type""#,
            r#"{"id":"e","type":"Build.Step","origin":"model"},{"id":"q","type""#,
        );
    let atoms = r#"{"id":"oe","subject":"e","field":"Build.Step.owner","value":["v","root"],"origin":"model"},{"id":"ef","subject":"e","field":"Build.Step.from","value":["v","p"],"origin":"model"},{"id":"et","subject":"e","field":"Build.Step.to","value":["v","q"],"origin":"model"}"#;
    let map = format!("{},{}]}}]}}", map.strip_suffix("]}]}").unwrap(), atoms);
    std::fs::write(dir.join("a.json"), map).unwrap();
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "n=evaluate(R.amount,on=$b.object,c=@v/q)",
        ],
    );
    let result = saved(&dir, &run, "complete", 0);
    let algebra = value(
        &result,
        get(get(answer(&result, "b"), "outputs"), "algebra"),
    );
    let generators = arr(get(get(algebra, "operations"), "generators"));
    assert_eq!(generators.len(), 1);
    let operation = value(&result, &generators[0]);
    get(operation, "configuration_map");
    get(operation, "action");
    assert_eq!(arr(get(algebra, "objects")).len(), 3);
    assert_eq!(
        s(value(
            &result,
            get(get(answer(&result, "n"), "outputs"), "value")
        )),
        "1"
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn incompatible_extension_keeps_counterexample_and_reusable_object() {
    let dir = files(
        "public-build-incompatible",
        "view amount(c:Root):Z=0;law required zero(c:Part):c.quantity=0;",
        false,
    );
    let mut map = std::fs::read_to_string(dir.join("a.json")).unwrap();
    for row in [
        r#",{"id":"q","type":"Build.Part","origin":"model"}"#,
        r#",{"id":"oq","subject":"q","field":"Build.Part.owner","value":["v","root"],"origin":"model"}"#,
        r#",{"id":"xq","subject":"q","field":"Build.Part.quantity","value":"1","origin":"model"}"#,
    ] {
        assert!(map.contains(row));
        map = map.replace(row, "");
    }
    std::fs::write(dir.join("a.json"), map).unwrap();
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "n=evaluate(R.amount,on=$b.object,c=@v/root)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    let b = answer(&result, "b");
    assert_eq!(s(get(b, "status")), "refuted");
    assert!(has(get(b, "outputs"), "object"));
    assert!(!has(get(b, "outputs"), "algebra"));
    let evidence = arr(get(b, "counterexamples"));
    assert!(!evidence.is_empty());
    for proof in evidence {
        assert_eq!(s(get(value(&result, proof), "kind")), "counterexample");
    }
    assert_eq!(s(get(answer(&result, "n"), "status")), "established");
    assert_eq!(
        s(value(
            &result,
            get(get(answer(&result, "n"), "outputs"), "value")
        )),
        "0"
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn lexical_law_bindings_survive_outside_rows_and_public_consumption() {
    for (index, body) in [
        "view amount(c:Part):Z=c.quantity;law required zero(c:Part):let x=c.quantity in x=0;",
        "view amount(c:Part):Z=c.quantity;law required zero(c:Part):let x=c.quantity in let y=x+1 in y=1;",
        "view amount(c:Part):Z=c.quantity;law required zero(c:Part):let x=(c.quantity,0) in x=(0,0);",
    ].iter().enumerate() {
        let dir = files(&format!("public-build-lexical-{index}"), body, false);
        let run = asks(&dir, &["b=build(R,on=@v/root)", "n=evaluate(R.amount,on=$b.object,c=@v/q)", "bad=check(R.zero,on=$b.object,c=@v/q)"]);
        let result = saved(&dir, &run, "complete", 1);
        assert_eq!(s(get(answer(&result, "b"), "status")), "established");
        assert_eq!(s(get(answer(&result, "bad"), "status")), "refuted");
        assert_eq!(s(value(&result, get(get(answer(&result, "n"), "outputs"), "value"))), "1");
        let algebra = value(&result, get(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(arr(get(algebra, "circuits")).len(), if index == 2 { 4 } else { 2 });
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn missing_views_block_algebra_without_relying_on_laws_or_matching_patterns() {
    for variant in 0..3 {
        let body = if variant == 1 {
            "view amount(c:Part):Z=c.quantity;law required constant(c:Part):0=0;"
        } else {
            "view amount(c:Part):Z=c.quantity;"
        };
        let dir = files(&format!("public-build-view-missing-{variant}"), body, true);
        let subject = if variant == 2 {
            // baseと唯一の部分対象は同じpatternだが、必要viewは両方で欠測。
            let mut map = std::fs::read_to_string(dir.join("a.json")).unwrap();
            for row in [
                r#",{"id":"q","type":"Build.Part","origin":"model"}"#,
                r#",{"id":"oq","subject":"q","field":"Build.Part.owner","value":["v","root"],"origin":"model"}"#,
                r#",{"id":"xp","subject":"p","field":"Build.Part.quantity","value":"0","origin":"model"}"#,
            ] {
                assert!(map.contains(row));
                map = map.replace(row, "");
            }
            std::fs::write(dir.join("a.json"), map).unwrap();
            "p"
        } else {
            "q"
        };
        let query = format!("n=evaluate(R.amount,on=$b.object,c=@v/{subject})");
        let run = asks(&dir, &["b=build(R,on=@v/root)", &query, "plan=needed($b)"]);
        let result = saved(&dir, &run, "partial", 2);
        let b = answer(&result, "b");
        assert_eq!(s(get(b, "status")), "undetermined");
        assert!(has(get(b, "outputs"), "object"));
        assert!(!has(get(b, "outputs"), "algebra"));
        assert!(arr(get(b, "reasons")).iter().any(|reason| {
            s(get(reason, "code")) == "missing_observation"
                && arr(get(reason, "missing")).iter().any(|slot| {
                    s(get(slot, "subject")) == subject
                        && s(get(slot, "field")) == "Build.Part.quantity"
                })
        }));
        assert_eq!(s(get(answer(&result, "n"), "status")), "undetermined");
        assert!(has(get(answer(&result, "plan"), "outputs"), "plan"));
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn mixed_tuple_fields_and_lexical_aliases_preserve_each_scalar_component() {
    mixed_tuple_public_cases(
        "lexical",
        &[
            ("", "c.quantity=(0,0)"),
            ("", "let x=c.quantity in x=(0,0)"),
            ("", "let x=c.quantity in let y=x in y=(0,0)"),
            ("", "let x=(c.quantity.0,c.quantity.1) in x=(0,0)"),
            ("", "let x=c in let y=x.quantity in y=(0,0)"),
        ],
    );
}

#[test]
fn helper_arguments_keep_caller_bindings_and_mixed_tuple_components() {
    mixed_tuple_public_cases(
        "helper",
        &[
            (
                "view first(x:(Z,Q)):Z=x.0;",
                "(first(c.quantity),c.quantity.1)=(0,0)",
            ),
            (
                "view passPair(x:(Z,Q)):(Z,Q)=x;",
                "passPair(c.quantity)=(0,0)",
            ),
            (
                "view first(x:(Z,Q)):Z=x.0;view keep(x:(Z,Q)):(Z,Q)=(first(x),x.1);",
                "let x=c.quantity in keep(x)=(0,0)",
            ),
        ],
    );
}

#[test]
fn binding_matches_and_rational_constants_preserve_the_public_equation() {
    mixed_tuple_public_cases(
        "match-rational",
        &[
            ("", "match c.quantity {n=>n=(0,0);}"),
            ("", "match c.quantity {_=>c.quantity=(0,0);}"),
            (
                "view passPair(x:(Z,Q)):(Z,Q)=match x {n=>n;};",
                "passPair(c.quantity)=(0,0)",
            ),
            ("", "c.quantity=(0,rat(0,1))"),
            ("", "let x=c.quantity in x=(0,rat(0,2))"),
        ],
    );
}

#[test]
fn rational_coefficients_use_the_declared_exact_value() {
    mixed_tuple_public_cases_at(
        "positive-rational",
        &[
            ("", "c.quantity=(0,rat(1,2))"),
            ("", "c.quantity=(0,rat(2,4))"),
        ],
        r#"["1","2"]"#,
    );
    mixed_tuple_public_cases_at(
        "negative-rational",
        &[("", "c.quantity=(0,-rat(1,2))")],
        r#"["-1","2"]"#,
    );
}

fn mixed_tuple_public_cases(name: &str, expressions: &[(&str, &str)]) {
    mixed_tuple_public_cases_at(name, expressions, r#"["0","1"]"#);
}

fn mixed_tuple_public_cases_at(name: &str, expressions: &[(&str, &str)], q: &str) {
    for (index, (helpers, expression)) in expressions.iter().enumerate() {
        let body = format!(
            "{helpers}view amount(c:Part):Z=c.quantity.0;law required pair(c:Part):{expression};"
        );
        let dir = files(
            &format!("public-build-mixed-tuple-{name}-{index}"),
            &body,
            false,
        );
        let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Tuple","Z","Q"]"#);
        let old = archsig::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())])
            .unwrap();
        let new = archsig::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
        std::fs::write(dir.join("d.json"), definition).unwrap();
        for name in ["l.law", "a.json"] {
            let text = std::fs::read_to_string(dir.join(name))
                .unwrap()
                .replace(
                    &old.vocabularies["Build"].digest,
                    &new.vocabularies["Build"].digest,
                )
                .replace(r#""value":"0""#, &format!(r#""value":["0",{q}]"#))
                .replace(r#""value":"1""#, &format!(r#""value":["1",{q}]"#));
            std::fs::write(dir.join(name), text).unwrap();
        }
        let run = asks(
            &dir,
            &[
                "b=build(R,on=@v/root)",
                "n=evaluate(R.amount,on=$b.object,c=@v/q)",
                "bad=check(R.pair,on=$b.object,c=@v/q)",
                "good=check(R.pair,on=$b.object,c=@v/p)",
            ],
        );
        let result = saved(&dir, &run, "complete", 1);
        assert_eq!(s(get(answer(&result, "b"), "status")), "established");
        assert_eq!(s(get(answer(&result, "bad"), "status")), "refuted");
        assert_eq!(s(get(answer(&result, "good"), "status")), "established");
        assert_eq!(
            s(value(
                &result,
                get(get(answer(&result, "n"), "outputs"), "value")
            )),
            "1"
        );
        let algebra = value(
            &result,
            get(get(answer(&result, "b"), "outputs"), "algebra"),
        );
        let detectors = arr(get(algebra, "circuits"));
        assert_eq!(detectors.len(), 4);
        let mut refuted_first = false;
        for detector in detectors {
            let detector = value(&result, detector);
            let component = arr(get(detector, "component"));
            assert_eq!(component.len(), 1);
            for case in arr(get(detector, "cases")) {
                let case = value(&result, case);
                let evaluation = value(&result, get(case, "refutation"));
                let decision = &value(&result, get(evaluation, "value")).value;
                if num(&component[0]) == 1 {
                    assert!(matches!(decision, archsig::json::JValue::Bool(false)));
                } else if matches!(decision, archsig::json::JValue::Bool(true)) {
                    refuted_first = true;
                }
            }
        }
        assert!(refuted_first);
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn integer_fields_keep_all_finite_guard_rows_and_feed_later_checks() {
    let dir = files(
        "public-build-integer-finite-guard",
        "view enabled():Bool=true;view disabled():Bool=false;view amount(c:Part):Z=c.quantity;law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        false,
    );
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "n=evaluate(R.amount,on=$b.object,c=@v/q)",
            "flag=evaluate(R.enabled,on=$b.object)",
            "bad=check(R.bit,on=$b.object,c=@v/q,b=$flag.value)",
            "good=check(R.bit,on=$b.object,c=@v/p,b=$flag.value)",
            "off=evaluate(R.disabled,on=$b.object)",
            "inactive=check(R.bit,on=$b.object,c=@v/q,b=$off.value)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    assert_eq!(s(get(answer(&result, "b"), "status")), "established");
    assert_eq!(s(get(answer(&result, "bad"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "good"), "status")), "established");
    assert_eq!(s(get(answer(&result, "inactive"), "status")), "established");
    assert_eq!(
        s(value(
            &result,
            get(get(answer(&result, "n"), "outputs"), "value")
        )),
        "1"
    );
    let algebra = value(
        &result,
        get(get(answer(&result, "b"), "outputs"), "algebra"),
    );
    assert_eq!(arr(get(algebra, "objects")).len(), 3);
    assert_eq!(arr(get(algebra, "circuits")).len(), 4);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn unsupported_integer_order_presentation_keeps_the_object_for_checks_and_localization() {
    for (tag, body, expected) in [
        ("less", "c.quantity<2", true),
        ("greater", "c.quantity>2", false),
    ] {
        let dir = files(
            &format!("build-order-{tag}"),
            &format!("view amount(c:Part):Z=c.quantity; law required ordered(c:Part):{body};"),
            false,
        );
        let requests = [
            "b=build(R,on=@v/root)",
            "v=evaluate(R.amount,on=$b.object,c=@v/q)",
            "c=check(R.ordered,on=$b.object,c=@v/q)",
            "l=localize($b.object,law=R.ordered,c=@v/q)",
            "d=diagnose($l.system)",
            "n=needed($b)",
        ];
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "partial", 2);
        let b = answer(&result, "b");
        assert_eq!(s(get(b, "status")), "undetermined");
        assert!(has(get(b, "outputs"), "object"));
        assert!(!has(get(b, "outputs"), "algebra"));
        let reasons = arr(get(b, "reasons"));
        assert!(!reasons.is_empty());
        for reason in reasons {
            assert_eq!(s(get(reason, "code")), "unsupported_algorithm");
            assert_eq!(s(get(get(reason, "details"), "question")), "build");
            assert_eq!(
                s(get(get(reason, "details"), "method")),
                "integer_order_equation_presentation"
            );
            assert!(arr(get(reason, "dependencies")).is_empty());
            assert!(arr(get(reason, "missing")).is_empty());
        }
        assert_eq!(
            s(value(
                &result,
                get(get(answer(&result, "v"), "outputs"), "value")
            )),
            "1"
        );
        for id in ["c", "d"] {
            assert_eq!(
                s(get(answer(&result, id), "status")),
                if expected { "established" } else { "refuted" }
            );
        }
        assert_eq!(s(get(answer(&result, "l"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        for reason in reasons {
            assert!(arr(get(plan, "blockers")).contains(reason));
        }

        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "again",
            "--reuse",
            "out",
            "--time-ms",
            "120000",
        ];
        for r in requests {
            args.extend(["--ask", r]);
        }
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, run.code, "{} {}", reused.stdout, reused.stderr);
        let again = result_json(&dir, &reused);
        assert_eq!(get(&again, "answers").value, get(&result, "answers").value);
        assert_eq!(get(&again, "nodes").value, get(&result, "nodes").value);
    }
}

#[test]
fn unsupported_order_presentation_does_not_replace_an_unobserved_value() {
    let dir = files(
        "build-order-missing",
        "view amount(c:Part):Z=c.quantity; law required ordered(c:Part):c.quantity<2;",
        true,
    );
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "v=evaluate(R.amount,on=$b.object,c=@v/q)",
            "c=check(R.ordered,on=$b.object,c=@v/q)",
            "n=needed($b)",
        ],
    );
    let result = saved(&dir, &run, "partial", 2);
    assert!(has(get(answer(&result, "b"), "outputs"), "object"));
    assert!(!has(get(answer(&result, "b"), "outputs"), "algebra"));
    for id in ["v", "c"] {
        assert_eq!(s(get(answer(&result, id), "status")), "undetermined");
    }
    assert!(!has(get(answer(&result, "v"), "outputs"), "value"));
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).iter().any(|r| {
        let field = get(r, "field");
        s(get(field, "subject")) == "q" && s(get(field, "field")) == "Build.Part.quantity"
    }));
}

#[test]
fn explicit_local_instances_cover_each_owned_subject_and_keep_missing_values() {
    for missing in [false, true] {
        let dir = files(
            "build-local-instances",
            &format!("{BODY} local each(c:Part) reads (c.owner,c.quantity);"),
            missing,
        );
        let r = asks(
            &dir,
            &[
                "b=build(R,on=@v/root)",
                "l=localize($b.object)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
                "n=needed($l)",
            ],
        );
        assert_eq!(
            r.code,
            if missing { 2 } else { 1 },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let j = result_json(&dir, &r);
        let a = answer(&j, "l");
        if missing {
            assert!(!has(get(a, "outputs"), "system"));
            let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
            assert!(
                arr(get(plan, "requirements"))
                    .iter()
                    .any(|r| s(get(get(r, "field"), "field")) == "Build.Part.quantity")
            );
        } else {
            let system = value(&j, get(get(a, "outputs"), "system"));
            let cover = value(&j, get(system, "cover"));
            assert_eq!(arr(get(cover, "patches")).len(), 2);
            assert_eq!(arr(get(system, "contexts")).len(), 4);
            let mut subjects = vec![];
            for patch in arr(get(cover, "patches")) {
                let context = value(&j, patch);
                let locals = arr(get(context, "locals"));
                assert_eq!(locals.len(), 1);
                let binding = &arr(get(&locals[0], "bindings"))[0];
                subjects.push(s(&arr(value(&j, get(binding, "value")))[1]).to_owned());
                assert_eq!(arr(get(context, "law_coordinates")).len(), 1);
            }
            subjects.sort();
            assert_eq!(subjects, vec!["p", "q"]);
            assert_eq!(s(get(answer(&j, "e"), "status")), "refuted");
            assert_eq!(s(get(answer(&j, "s"), "status")), "refuted");
        }
    }
}

#[test]
fn missing_owner_keeps_build_partial_and_needed_reusable() {
    for missing in [true, false] {
        let dir = files("public-build-owner", BODY, false);
        if missing {
            let path = dir.join("a.json");
            let map = std::fs::read_to_string(&path).unwrap();
            let atom = r#"{"id":"op","subject":"p","field":"Build.Part.owner","value":["v","root"],"origin":"model"},"#;
            assert!(map.contains(atom));
            std::fs::write(path, map.replace(atom, "")).unwrap();
        }
        let requests = ["b=build(R,on=@v/root)", "n=needed($b)"];
        let result_run = asks(&dir, &requests);
        let result = saved(&dir, &result_run, if missing { "partial" } else { "complete" }, if missing { 2 } else { 0 });
        let b = answer(&result, "b");
        assert_eq!(s(get(b, "status")), if missing { "undetermined" } else { "established" });
        assert_eq!(has(get(b, "outputs"), "object"), !missing);
        assert_eq!(has(get(b, "outputs"), "algebra"), !missing);
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        let requirements = arr(get(plan, "requirements"));
        if missing {
            assert!(requirements.iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "subject")) == "p" && s(get(field, "field")) == "Build.Part.owner"
            }));
        } else {
            assert!(requirements.is_empty());
        }
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json", "--out", "again", "--reuse", "out", "--time-ms", "120000"];
        for request in requests { args.extend(["--ask", request]); }
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, result_run.code, "{} {}", reused.stdout, reused.stderr);
        let again = result_json(&dir, &reused);
        for field in ["answers", "nodes"] {
            assert_eq!(get(&again, field).value, get(&result, field).value);
        }
    }
}
