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
fn partial_data_known_component_selects_checked_arm() {
    let definition = numeric_data_definition("Z").replace(r#""meaning":"数量。"}"#, r#""meaning":"数量。"},{"name":"payload","type":["Data","Build.Payload"],"meaning":"未観測の包装。"}"#)
        .replace(r#""declarations":["#, r#""declarations":[{"kind":"data","name":"Build.Flag","meaning":"選択。","constructors":[{"name":"Off","arguments":[],"meaning":"偽。"},{"name":"On","arguments":[],"meaning":"真。"}]},{"kind":"data","name":"Build.Pair","meaning":"包装と選択。","constructors":[{"name":"Join","arguments":[["Data","Build.Payload"],["Data","Build.Flag"]],"meaning":"組。"}]},"#);
    let dir = files_with_definition("partial-data-arm", "law required short(c:Part):match Pair.Join(c.payload,Flag.Off){Join(Packed(_),On)=>false;_=>true;};law required uncertain(c:Part):match c.payload{Empty=>true;Packed(x)=>x=0;};", false, &definition);
    let normal_args = ["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json", "--ask", "b=check(R.short,c=@v/q)"];
    let before = ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
    let normal = cli::run(&dir, &normal_args);
    assert_eq!(normal.code, 0, "{}", normal.stdout);
    assert!(normal.stderr.is_empty());
    eprintln!("partial Data check: stdout {} bytes", normal.stdout.len());
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    assert!(!has(&normal.receipt, "nodes"));
    assert!(!has(&normal.receipt, "result"));
    for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) { assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes); }
    let requests = ["b=check(R.short,c=@v/q)", "u=check(R.uncertain,c=@v/q)", "n=needed($u)"];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "partial", 2);
    assert_eq!(s(get(answer(&result, "b"), "status")), "established");
    assert_eq!(s(get(answer(&result, "u"), "status")), "undetermined");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(get(r, "field"), "field")) == "Build.Part.payload"));
    let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json", "--out", "again", "--reuse", "out"];
    for request in requests { args.extend(["--ask", request]); }
    let reused = cli::run(&dir, &args);
    let again = saved(&dir, &reused, "partial", 2);
    assert!(warnings(&again).is_empty());
    for field in ["answers", "nodes"] { assert_eq!(get(&result, field).value, get(&again, field).value); }
    let copied_law = dir.join("again/inputs/law.law");
    let original = std::fs::read(&copied_law).unwrap();
    std::fs::write(&copied_law, "wrong saved input").unwrap();
    assert!(std::panic::catch_unwind(|| saved(&dir, &reused, "partial", 2)).is_err());
    std::fs::write(&copied_law, original).unwrap();
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap().replace("Flag.Off", "Flag.On");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let out_at = args.iter().position(|arg| *arg == "--out").unwrap()+1;
    args[out_at] = "changed";
    let changed = cli::run(&dir, &args);
    let changed = saved(&dir, &changed, "partial", 2);
    assert_eq!(s(get(answer(&changed, "b"), "status")), "undetermined");
}
#[test]
fn known_data_payload_match_preserves_numeric_products() {
    for ty in ["Z", "Q"] {
        let definition = numeric_data_definition(ty);
        for (name, helper, expression) in [
            ("data-payload", "", "(match Payload.Packed(n){Empty=>0;Packed(x)=>x;})"),
            ("data-nested", "", "(match Wrapper.Wrapped(Payload.Packed(n)){Wrapped(inner)=>match inner{Empty=>0;Packed(x)=>x;};})"),
            ("data-helper", "view unpack(p:Payload):Number=match p{Empty=>0;Packed(x)=>x;};", "unpack(Payload.Packed(n))"),
            ("data-constant-payload", "", "(match Payload.Packed(n-n){Empty=>0;Packed(x)=>x+n;})"),
            ("data-literal-payload", "", "(match Payload.Packed(0){Empty=>0;Packed(x)=>x+n;})"),
        ] {
            let helper = helper.replace("Number", ty);
            let body = format!("{helper}law required zero(c:Part,n:{ty}):{expression}*c.quantity=0;");
            known_numeric_product_case(name, ty, &body, &definition);
        }
        let chain_definition = definition.replace(r#""declarations":["#, &format!(r#""declarations":[{{"kind":"data","name":"Build.Chain","meaning":"有限の包装列。","constructors":[{{"name":"Leaf","arguments":["{ty}"],"meaning":"数値。"}},{{"name":"Next","arguments":[["Data","Build.Chain"]],"meaning":"次。"}}]}},"#));
        let mut expression = "Chain.Leaf(n)".to_owned();
        let mut pattern = "Leaf(x)".to_owned();
        for _ in 0..12 { expression = format!("Chain.Next({expression})"); pattern = format!("Next({pattern})"); }
        let body = format!("law required zero(c:Part,n:{ty}):(match {expression}{{{pattern}=>x;_=>0;}})*c.quantity=0;");
        known_numeric_product_case("data-chain", ty, &body, &chain_definition);
    }
}
fn numeric_data_definition(ty: &str) -> String {
    DEFINITION.replace(r#""declarations":["#, &format!(r#""declarations":[{{"kind":"data","name":"Build.Payload","meaning":"数値を包む。","constructors":[{{"name":"Empty","arguments":[],"meaning":"空。"}},{{"name":"Packed","arguments":["{ty}"],"meaning":"数値。"}}]}},{{"kind":"data","name":"Build.Wrapper","meaning":"包装。","constructors":[{{"name":"Wrapped","arguments":[["Data","Build.Payload"]],"meaning":"包装。"}}]}},"#))
        .replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#))
}
#[test]
fn data_payload_guards_keep_missing_and_applicability() {
    for ty in ["Z", "Q"] { for active in [true, false] {
        let condition = if active { "x=x" } else { "x+1=x" };
        let body = format!("view amount(c:Part):{ty}=c.quantity;law required zero(c:Part,n:{ty}) when match Payload.Packed(n){{Empty=>false;Packed(x)=>{condition};}}:n*c.quantity=0;");
        let dir = files_with_definition(&format!("data-guard-{ty}-{active}"), &body, true, &numeric_data_definition(ty));
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#""value":"0""#, r#""value":["0","1"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = ["b=build(R,on=@v/root)", "p=check(R.zero,on=$b.object,c=@v/p)", "q=check(R.zero,on=$b.object,c=@v/q)", "v=evaluate(R.amount,on=$b.object,c=@v/q)", "n=needed($v)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let before = ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 2, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert!(!has(&normal.receipt, "nodes"));
        assert!(!has(&normal.receipt, "result"));
        eprintln!("data guard {ty}/{active}: stdout {} bytes", normal.stdout.len());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) { assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes); }
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "partial", 2);
        assert_eq!(s(get(answer(&result, "p"), "status")), "established");
        assert_eq!(s(get(answer(&result, "q"), "status")), if active { "undetermined" } else { "established" });
        if !active { for id in ["p", "q"] { assert_eq!(s(get(answer(&result, id), "applicability")), "not_applicable"); } }
        assert_eq!(s(get(answer(&result, "v"), "status")), "undetermined");
        assert!(!has(get(answer(&result, "v"), "outputs"), "value"));
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(get(r, "field"), "field")) == "Build.Part.quantity"));
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        let again = saved(&dir, &reused, "partial", 2);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }}
}
#[test]
fn unknown_data_constructor_does_not_choose_match_branch() {
    let definition = numeric_data_definition("Z").replace(r#""meaning":"数量。"}"#, r#""meaning":"数量。"},{"name":"payload","type":["Data","Build.Payload"],"meaning":"未観測の包装。"}"#);
    let dir = files_with_definition("data-unknown-constructor", "law required zero(c:Part):match c.payload{Empty=>true;Packed(x)=>x=0;};", false, &definition);
    let requests = ["c=check(R.zero,c=@v/q)", "n=needed($c)"];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "partial", 2);
    assert_eq!(s(get(answer(&result, "c"), "status")), "undetermined");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(get(r, "field"), "field")) == "Build.Part.payload"));
}
#[test]
fn mixed_type_order_guards_preserve_numeric_products() {
    mixed_numeric_guard_product("order", "c.guardValue+Offset>c.guardValue and n+1>n");
}
#[test]
fn mixed_type_data_payload_guards_preserve_numeric_products() {
    mixed_numeric_guard_product("data", "match Payload.Packed(c.guardValue){Packed(x)=>x=x and x+Offset>x;}");
}
fn mixed_numeric_guard_product(name: &str, guard: &str) {
    for (ty, other, zero) in [("Z", "Q", r#"["0","1"]"#), ("Q", "Z", r#""0""#)] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#))
            .replace(r#""meaning":"数量。"}"#, &format!(r#""meaning":"数量。"}},{{"name":"guardValue","type":"{other}","meaning":"比較する値。"}}"#))
            .replace(r#""declarations":["#, &format!(r#""declarations":[{{"kind":"data","name":"Build.Payload","meaning":"数値を包む。","constructors":[{{"name":"Packed","arguments":["{other}"],"meaning":"数値。"}}]}},"#));
        let offset = if other == "Q" { "rat(1,2)" } else { "1" };
        let guard = guard.replace("Offset", offset);
        let dir = files_with_definition(&format!("mixed-{name}-{ty}"), &format!(
            "law required zero(c:Part,n:{ty}) when {guard}:n*c.quantity=0;"
        ), false, &definition);
        let mut map = std::fs::read_to_string(dir.join("a.json")).unwrap();
        if ty == "Q" { map = map.replace(r#""value":"0""#, r#""value":["0","1"]"#).replace(r#""value":"1""#, r#""value":["1","2"]"#); }
        let atoms = format!(r#"{{"id":"gp","subject":"p","field":"Build.Part.guardValue","value":{zero},"origin":"model"}},{{"id":"gq","subject":"q","field":"Build.Part.guardValue","value":{zero},"origin":"model"}},"#);
        std::fs::write(dir.join("a.json"), map.replace(r#""atoms":["#, &format!(r#""atoms":[{atoms}"#))).unwrap();
        let requests = ["b=build(R,on=@v/root)", "p=check(R.zero,on=$b.object,c=@v/p)", "q=check(R.zero,on=$b.object,c=@v/q)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let before = ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert!(!has(&normal.receipt, "nodes"));
        for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) { assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes); }
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 1);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "p"), "status")), "established");
        assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        let again = saved(&dir, &reused, "complete", 1);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }
}
#[test]
fn constant_order_guards_preserve_numeric_products() {
    for (name, guard) in [
        ("order-lt", "n<n+1"), ("order-le", "n+n<=2*n"),
        ("order-gt", "n+1>n"), ("order-ge", "n+n>=2*n"),
        ("order-slot", "c.quantity+1>c.quantity"),
    ] { known_numeric_product(name, "", guard); }
}
#[test]
fn constant_order_true_guard_keeps_missing_body_undetermined() {
    active_products("constant-order", &[("", " when c.quantity+1>c.quantity")]);
}
#[test]
fn constant_order_false_guard_keeps_missing_read_undetermined() {
    inactive_products("constant-order", &["n<n", "n+1<=n", "n>n", "n>=n+1"]);
    inactive_products_with_guard_reads("constant-order-slot", &["c.quantity+1<=c.quantity"], true);
}
#[test]
fn right_boolean_constant_guards_preserve_numeric_products() {
    for (name, guard) in [
        ("right-or-true", "n=0 or true"),
        ("right-implies-true", "n=0 implies true"),
    ] { known_numeric_product(name, "", guard); }
}
#[test]
fn right_boolean_true_guard_keeps_missing_body_undetermined() {
    active_products("right-boolean", &[("", " when n=0 or true")]);
}
#[test]
fn right_boolean_false_guard_keeps_missing_read_undetermined() {
    inactive_products("right-boolean", &["n=0 and false"]);
}
#[test]
fn same_slot_guards_preserve_numeric_products() {
    for (name,guard) in [
        ("same-slot-option", "some(c.quantity)=some(c.quantity)"),
        ("same-slot-option-difference", "some(c.quantity+1)!=some(c.quantity)"),
        ("same-slot-tuple", "(n,c.quantity,true)=(n,c.quantity,true)"),
        ("same-slot-list", "list<Number>[c.quantity,n]=list<Number>[c.quantity,n]"),
    ] { known_numeric_product(name,"",guard); }
}
#[test]
fn same_slot_guard_keeps_missing_body_undetermined() {
    active_products("same-slot", &[("", " when some(c.quantity)=some(c.quantity)")]);
}
#[test]
fn same_slot_false_guard_keeps_missing_read_undetermined() {
    inactive_products_with_guard_reads("same-slot", &["some(c.quantity+1)=some(c.quantity)"], true);
}
#[test]
fn text_literal_guards_preserve_numeric_products() {
    for (name,guard) in [
        ("text-literal-equality", r#"(n,"ready")=(n,"ready")"#),
        ("text-literal-difference", r#"(n,"ready")!=(n,"done")"#),
        ("text-literal-let", r#"let tag="ready" in (n,tag)=(n,"ready")"#),
        ("text-literal-unicode", r#"(n,"数量")=(n,"数量")"#),
        ("text-literal-decoded", r#"(n,"line\n")=(n,"line\u000a")"#),
    ] { known_numeric_product(name, "", guard); }
}
#[test]
fn list_numeric_parameter_equality_preserves_products() {
    for (name,guard) in [
        ("symbolic-list-equality", "list<Number>[n,n]=list<Number>[n,n]"),
        ("symbolic-list-affine-equality", "list<Number>[n+n]=list<Number>[2*n]"),
        ("symbolic-list-let-equality", "let xs=list<Number>[n,n+1] in xs=list<Number>[n,n+1]"),
        ("symbolic-list-length-inequality", "list<Number>[n]!=list<Number>[n,n]"),
        ("symbolic-list-order-inequality", "list<Number>[n,n+1]!=list<Number>[n+1,n]"),
        ("symbolic-list-nested-equality", "list<Option<Number>>[some(n),none<Number>]=list<Option<Number>>[some(n),none<Number>]"),
    ] { known_numeric_product(name, "", guard); }
}
#[test]
fn tuple_numeric_parameter_equality_preserves_products() {
    for (name,guard) in [
        ("symbolic-tuple-equality", "(n,true)=(n,true)"),
        ("symbolic-tuple-affine", "(n+n,false)=(2*n,false)"),
        ("symbolic-tuple-let", "let x=(n,true) in x=(n,true)"),
        ("symbolic-tuple-nested", "(some(n),(n,true))=(some(n),(n,true))"),
        ("symbolic-tuple-numeric", "(n,n+n)=(n,2*n)"),
    ] { known_numeric_product(name, "", guard); }
    known_numeric_product("symbolic-tuple-finite-bool", ",b:Bool", "(n,b)=(n,b)");
}
#[test]
fn option_numeric_parameter_equality_preserves_products() {
    for (name,guard) in [
        ("symbolic-option-equality", "some(n)=some(n)"),
        ("symbolic-option-affine", "some(n+n)=some(2*n)"),
        ("symbolic-option-let", "let x=some(n) in x=some(n)"),
        ("symbolic-option-nested", "some(some(n))=some(some(n))"),
        ("symbolic-option-constructor", "some(n)!=none<Number>"),
    ] { known_numeric_product(name, "", guard); }
}
#[test]
fn explicit_list_sum_cancels_numeric_parameters() {
    for (name,guard) in [
        ("symbolic-list-sum", "sum(list<Number>[n,-n])=0"),
        ("symbolic-list-sum-double", "sum(list<Number>[n,n])=n+n"),
        ("symbolic-list-sum-let", "let xs=list<Number>[n,-n] in sum(xs)=0"),
        ("symbolic-list-sum-empty", "sum(list<Number>[])=0"),
    ] { known_numeric_product(name, "", guard); }
}
#[test]
fn explicit_list_count_uses_shape_with_numeric_parameters() {
    for (name,guard) in [
        ("symbolic-list-count", "count(list<Number>[n,n])=2"),
        ("symbolic-list-count-let", "let xs=list<Number>[n,n+n] in count(xs)=2"),
    ] { known_numeric_product(name, "", guard); }
}
#[test]
fn explicit_list_aggregate_guards_preserve_numeric_products() {
    for (name, guard) in [
        ("list-count-sum", "count(list<Bool>[true,false,true])=3 and sum(list<Z>[1,1])=2"),
        ("list-rational-sum", "sum(list<Q>[rat(1,2),rat(1,2)])=1"),
    ] {
        known_numeric_product(name, "", guard);
    }
}
#[test]
fn finite_aggregates_preserve_known_numeric_products() {
    for (name, finite_type, guard) in [
        ("count-known", "Set<Bool>", "count(b)>0 and count(b)<=2"),
        ("sum-known", "Set<Fp(2)>", "sum(b)=1"),
    ] {
        known_numeric_product(name, &format!(",b:{finite_type}"), guard);
    }
}
#[test]
fn finite_count_keeps_missing_and_applicability() {
    finite_missing_product(
        "count",
        "Set<Bool>",
        "set<Bool>{}",
        "set<Bool>{true,false,true}",
        "count(b)>0 and count(b)<=2",
    );
}
#[test]
fn finite_sum_keeps_missing_and_applicability() {
    finite_missing_product(
        "sum",
        "Set<Fp(2)>",
        "set<Fp(2)>{}",
        "set<Fp(2)>{1,1}",
        "sum(b)=1",
    );
}
#[test]
fn finite_set_guards_preserve_known_numeric_products() {
    finite_set_known_product("set-equality", "b=set<Bool>{false,true}");
}
#[test]
fn finite_predicates_preserve_known_numeric_products() {
    finite_set_known_product("set-predicate", "b!=set<Bool>{} and (true in b implies false in b)");
}
#[test]
fn finite_predicates_keep_missing_and_applicability() {
    finite_missing_product(
        "set-predicate",
        "Set<Bool>",
        "set<Bool>{}",
        "set<Bool>{false,true}",
        "b!=set<Bool>{} and (true in b implies false in b)",
    );
}
#[test]
fn finite_tuple_equality_keeps_missing_and_applicability() {
    finite_missing_product(
        "tuple-equality",
        "(Bool,Bool)",
        "(false,true)",
        "(true,true)",
        "b=(true,true)",
    );
}
fn finite_set_known_product(name: &str, guard: &str) {
    known_numeric_product(name, ",b:Set<Bool>", guard);
}
#[test]
fn numeric_guards_preserve_known_products() {
    for (name, guard) in [("numeric-implies", "false implies n*n=1"), ("numeric-or", "true or n*n=1"), ("numeric-and", "n=n and true")] {
        known_numeric_product(name, "", guard);
    }
}
fn known_numeric_product(name: &str, extra: &str, guard: &str) {
    for ty in ["Z", "Q"] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let guard = guard.replace("Number", ty);
        let body = format!(
            "law required zero(c:Part,n:{ty}{extra}) when {guard}:n*c.quantity=0;"
        );
        known_numeric_product_case(name, ty, &body, &definition);
    }
}
fn known_numeric_product_case(name: &str, ty: &str, body: &str, definition: &str) {
        let dir = files_with_definition(&format!("known-product-{name}-{ty}"), body, false, definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .replace(r#""value":"0""#, r#""value":["0","1"]"#)
                .replace(r#""value":"1""#, r#""value":["1","2"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = [
            "a=build(R,on=@v/root)",
            "p=check(R.zero,on=$a.object,c=@v/p)",
            "q=check(R.zero,on=$a.object,c=@v/q)",
        ];
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in requests {
            args.extend(["--ask", request]);
        }
        let before =
            ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
            assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
        }
        assert!(!has(&normal.receipt, "nodes"));
        assert!(!has(&normal.receipt, "result"));
        assert_eq!(
            s(get(answer(&normal.receipt, "p"), "status")),
            "established"
        );
        assert_eq!(s(get(answer(&normal.receipt, "q"), "status")), "refuted");
        eprintln!("known numeric product {ty}: stdout {} bytes", normal.stdout.len());
        let r = asks(&dir, &requests);
        let j = saved(&dir, &r, "complete", 1);
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 1, "{}", reused.stdout);
        assert!(reused.stderr.is_empty());
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] {
            assert_eq!(get(&j, field).value, get(&again, field).value);
        }
}
#[test]
fn finite_set_numeric_products_keep_missing_and_applicability() {
    finite_missing_product(
        "set",
        "Set<Bool>",
        "set<Bool>{}",
        "set<Bool>{true,false,true}",
        "b=set<Bool>{false,true}",
    );
}
#[test]
fn finite_data_guards_keep_numeric_products() {
    finite_data_guard_product(false);
}
#[test]
fn finite_data_constructor_guards_keep_numeric_products() {
    finite_data_guard_product(true);
}
fn finite_data_guard_product(constructor: bool) {
    for ty in ["Z", "Q"] {
        for missing in [false, true] {
            let mode = if constructor { "constructor" } else { "match" };
            let dir = finite_data_product_input(ty, missing, mode);
            if constructor {
                let law = std::fs::read_to_string(dir.join("l.law")).unwrap().replace("match tag{Packed(inner)=>match inner{Off=>false;On(b)=>b;};}", "tag=Packed(On(true)) and not(tag=Packed(Off))");
                std::fs::write(dir.join("l.law"), law).unwrap();
            }
            let requests = [
                "a=build(R,on=@v/root)",
                "p=check(R.zero,on=$a.object,c=@v/p)",
                "q=check(R.zero,on=$a.object,c=@v/q)",
            ];
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in requests {
                args.extend(["--ask", request]);
            }
            let before =
                ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
            let normal = cli::run(&dir, &args);
            let code = if missing { 2 } else { 1 };
            assert_eq!(normal.code, code, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
                assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
            }
            assert!(!has(&normal.receipt, "nodes"));
            assert!(!has(&normal.receipt, "result"));
            assert_eq!(
                s(get(answer(&normal.receipt, "p"), "status")),
                "established"
            );
            assert_eq!(
                s(get(answer(&normal.receipt, "q"), "status")),
                if missing { "undetermined" } else { "refuted" }
            );
            eprintln!(
                "finite data {ty}/{missing}: stdout {} bytes",
                normal.stdout.len()
            );
            let mut full_requests = requests.to_vec();
            full_requests.extend([
                "f=evaluate(R.off,on=$a.object)",
                "d=evaluate(R.deny,on=$a.object)",
                "t=evaluate(R.on,on=$a.object)",
                "off=check(R.zero,on=$a.object,c=@v/q,tag=$f.value)",
                "deny=check(R.zero,on=$a.object,c=@v/q,tag=$d.value)",
                "on=check(R.zero,on=$a.object,c=@v/q,tag=$t.value)",
                "n=needed($q)",
            ]);
            let r = asks(&dir, &full_requests);
            let j = saved(&dir, &r, if missing { "partial" } else { "complete" }, code);
            for id in ["off", "deny"] {
                assert_eq!(s(get(answer(&j, id), "applicability")), "not_applicable");
            }
            assert_eq!(s(get(answer(&j, "on"), "applicability")), "applicable");
            assert_eq!(
                s(get(answer(&j, "on"), "status")),
                if missing { "undetermined" } else { "refuted" }
            );
            if missing {
                for id in ["a", "q", "on"] {
                    assert!(
                        arr(get(answer(&j, id), "reasons"))
                            .iter()
                            .all(|r| s(get(r, "code")) == "missing_observation")
                    );
                }
                let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
                assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                    get(r, "field"),
                    "field"
                )) == "Build.Part.quantity"
                    && s(get(get(r, "field"), "subject")) == "q"));
            }
            let mut reuse_args = vec![
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
            ];
            for request in full_requests {
                reuse_args.extend(["--ask", request]);
            }
            let reused = cli::run(&dir, &reuse_args);
            assert_eq!(reused.code, code, "{}", reused.stdout);
            assert!(reused.stderr.is_empty());
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for field in ["answers", "nodes"] {
                assert_eq!(get(&j, field).value, get(&again, field).value);
            }
        }
    }
}
fn finite_data_product_input(ty: &str, missing: bool, mode: &str) -> PathBuf {
    let definition = DEFINITION.replace(r#""declarations":["#,r#""declarations":[{"kind":"data","name":"Build.Flag","meaning":"選択。","constructors":[{"name":"Off","arguments":[],"meaning":"停止。"},{"name":"On","arguments":["Bool"],"meaning":"選択。"}]},{"kind":"data","name":"Build.Wrapper","meaning":"包装。","constructors":[{"name":"Packed","arguments":[["Data","Build.Flag"]],"meaning":"包装。"}]},"#).replace(r#""type":"Z""#,&format!(r#""type":"{ty}""#));
    let body = format!(
        "view off():Wrapper=Packed(Off);view deny():Wrapper=Packed(On(false));view on():Wrapper=Packed(On(true));view active(tag:Wrapper):Bool=match tag{{Packed(inner)=>match inner{{Off=>false;On(b)=>b;}};}};law required zero(c:Part,n:{ty},tag:Wrapper) when active(tag):n*c.quantity=0;"
    );
    let dir = files_with_definition(&format!("finite-data-product-{mode}-{ty}-{missing}"), &body, missing, &definition);
    if ty == "Q" {
        let map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(r#""value":"0""#, r#""value":["0","1"]"#)
            .replace(r#""value":"1""#, r#""value":["1","2"]"#);
        std::fs::write(dir.join("a.json"), map).unwrap();
    }
    dir
}
#[test]
fn unit_and_option_parameters_keep_numeric_products() {
    for ty in ["Z", "Q"] {
        for (parameter, guard) in [
            ("b:Option<Bool>", "b=some(true)"),
            ("u:Unit", "u=unit"),
            ("b:Option<Unit>", "b=none<Unit>"),
        ] {
            let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
            let dir = files_with_definition(
                "unit-option-product",
                &format!(
                    "law required zero(c:Part,n:{ty},{parameter}) when {guard}:n*c.quantity=0;"
                ),
                false,
                &definition,
            );
            if ty == "Q" {
                let map = std::fs::read_to_string(dir.join("a.json"))
                    .unwrap()
                    .replace(r#""value":"0""#, r#""value":["0","1"]"#)
                    .replace(r#""value":"1""#, r#""value":["1","2"]"#);
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let requests = [
                "a=build(R,on=@v/root)",
                "p=check(R.zero,on=$a.object,c=@v/p)",
                "q=check(R.zero,on=$a.object,c=@v/q)",
            ];
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in requests {
                args.extend(["--ask", request]);
            }
            let before =
                ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, 1, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert!(!has(&normal.receipt, "nodes"));
            assert!(!has(&normal.receipt, "result"));
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
                assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
            }
            assert_eq!(
                s(get(answer(&normal.receipt, "a"), "status")),
                "established"
            );
            assert!(has(get(answer(&normal.receipt, "a"), "outputs"), "algebra"));
            assert_eq!(
                s(get(answer(&normal.receipt, "p"), "status")),
                "established"
            );
            assert_eq!(s(get(answer(&normal.receipt, "q"), "status")), "refuted");
            eprintln!(
                "finite unit/option {ty}/{parameter}: stdout {} bytes",
                normal.stdout.len()
            );
            if ty == "Q" {
                let r = asks(&dir, &requests);
                let j = saved(&dir, &r, "complete", 1);
                args.extend(["--out", "again", "--reuse", "out"]);
                let reused = cli::run(&dir, &args);
                assert_eq!(reused.code, 1, "{}", reused.stdout);
                assert!(reused.stderr.is_empty());
                let again = result_json(&dir, &reused);
                assert!(warnings(&again).is_empty());
                for field in ["answers", "nodes"] {
                    assert_eq!(get(&j, field).value, get(&again, field).value);
                }
            }
        }
    }
}
#[test]
fn option_boolean_numeric_products_keep_missing_and_applicability() {
    finite_missing_product(
        "option-bool",
        "Option<Bool>",
        "none<Bool>",
        "some(true)",
        "b=some(true)",
    );
}
#[test]
fn option_unit_numeric_products_keep_missing_and_applicability() {
    finite_missing_product(
        "option-unit",
        "Option<Unit>",
        "some(unit)",
        "none<Unit>",
        "b=none<Unit>",
    );
}
#[test]
fn option_tuple_numeric_products_keep_missing_and_applicability() {
    finite_missing_product(
        "option-tuple",
        "Option<(Bool,Unit)>",
        "none<(Bool,Unit)>",
        "some((true,unit))",
        "b=some((true,unit))",
    );
}
#[test]
fn correlated_missing_products_decide_constant_differences_and_reuse() {
    for (ty, lexical, offset) in [
        ("Z", false, 0),
        ("Q", false, 1),
        ("Z", true, 1),
        ("Q", true, 0),
    ] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let predicate = if lexical {
            format!("let v=n*c.quantity in v=c.quantity*n+{offset}")
        } else {
            format!("n*c.quantity=c.quantity*n+{offset}")
        };
        let body = format!(
            "view amount(c:Part):{ty}=c.quantity;law required zero(c:Part,n:{ty}):{predicate};"
        );
        let dir = files_with_definition("correlated-missing-product", &body, true, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .replace(r#""value":"0""#, r#""value":["0","1"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = [
            "a=build(R,on=@v/root)",
            "q=check(R.zero,on=$a.object,c=@v/q)",
            "v=evaluate(R.amount,on=$a.object,c=@v/q)",
            "n=needed($v)",
        ];
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in requests {
            args.extend(["--ask", request]);
        }
        let before =
            ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 2, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert!(!has(&normal.receipt, "nodes"));
        assert!(!has(&normal.receipt, "result"));
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
            assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
        }
        let status = if offset == 0 {
            "established"
        } else {
            "refuted"
        };
        assert_eq!(s(get(answer(&normal.receipt, "q"), "status")), status);
        assert_eq!(
            s(get(answer(&normal.receipt, "v"), "status")),
            "undetermined"
        );
        assert!(!has(get(answer(&normal.receipt, "v"), "outputs"), "value"));
        eprintln!(
            "correlated product {ty}/{lexical}/{offset}: stdout {} bytes",
            normal.stdout.len()
        );
        let r = asks(&dir, &requests);
        let j = saved(&dir, &r, "partial", 2);
        assert_eq!(s(get(answer(&j, "q"), "status")), status);
        assert_eq!(
            s(get(get(answer(&j, "q"), "scope"), "domain")),
            "all_completions"
        );
        assert!(
            arr(get(get(answer(&j, "q"), "scope"), "quantifiers"))
                .iter()
                .any(|q| s(get(q, "name")) == "n"
                    && s(get(q, "kind")) == "forall"
                    && s(get(q, "type")) == ty)
        );
        let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
        assert!(
            arr(get(plan, "requirements"))
                .iter()
                .any(
                    |r| s(get(get(r, "field"), "field")) == "Build.Part.quantity"
                        && s(get(get(r, "field"), "subject")) == "q"
                )
        );
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 2, "{}", reused.stdout);
        assert!(reused.stderr.is_empty());
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] {
            assert_eq!(get(&j, field).value, get(&again, field).value);
        }
    }
}
#[test]
fn different_missing_product_slots_remain_independent() {
    for ty in ["Z", "Q"] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let body = format!("law required equal(c:Part,d:Part,n:{ty}):n*c.quantity=n*d.quantity;");
        let dir = files_with_definition("independent-missing-product", &body, true, &definition);
        let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#",{"id":"xp","subject":"p","field":"Build.Part.quantity","value":"0","origin":"model"}"#,"").replace("p=0、q=1。", "pとqの数量は未観測。");
        std::fs::write(dir.join("a.json"), map).unwrap();
        let r = cli::run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--ask",
                "a=build(R,on=@v/root)",
                "--ask",
                "same=check(R.equal,on=$a.object,c=@v/q,d=@v/q)",
                "--ask",
                "different=check(R.equal,on=$a.object,c=@v/p,d=@v/q)",
            ],
        );
        assert_eq!(r.code, 2, "{}", r.stdout);
        assert!(r.stderr.is_empty());
        assert_eq!(s(get(answer(&r.receipt, "same"), "status")), "established");
        assert_eq!(
            s(get(answer(&r.receipt, "different"), "status")),
            "undetermined"
        );
        let reasons = arr(get(answer(&r.receipt, "different"), "reasons"));
        assert!(
            reasons
                .iter()
                .all(|r| s(get(r, "code")) == "missing_observation")
        );
        for subject in ["p", "q"] {
            assert!(
                reasons
                    .iter()
                    .flat_map(|r| arr(get(r, "missing")))
                    .any(|f| s(get(f, "subject")) == subject
                        && s(get(f, "field")) == "Build.Part.quantity")
            );
        }
    }
}
#[test]
fn boolean_numeric_products_keep_missing_coefficients_separate_from_applicability() {
    finite_missing_product("bool", "Bool", "false", "true", "b");
}
#[test]
fn field_numeric_products_keep_missing_coefficients_separate_from_applicability() {
    finite_missing_product("field", "Fp(2)", "0", "1", "b=1");
}
#[test]
fn tuple_numeric_products_keep_missing_coefficients_separate_from_applicability() {
    finite_missing_product(
        "tuple",
        "(Fp(2),Bool)",
        "(0,false)",
        "(1,true)",
        "b.1 and b.0=1",
    );
}
fn finite_missing_product(name: &str, finite_type: &str, off: &str, on: &str, guard: &str) {
    for ty in ["Z", "Q"] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let body = format!(
            "view off():{finite_type} = {off};view on():{finite_type} = {on};law required zero(c:Part,n:{ty},b:{finite_type}) when {guard}:n*c.quantity=0;"
        );
        let dir = files_with_definition(
            &format!("finite-product-missing-{name}-{ty}"),
            &body,
            true,
            &definition,
        );
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .replace(r#""value":"0""#, r#""value":["0","1"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let mut requests = vec![
            "a=build(R,on=@v/root)",
            "f=evaluate(R.off,on=$a.object)",
            "t=evaluate(R.on,on=$a.object)",
            "off=check(R.zero,on=$a.object,c=@v/q,b=$f.value)",
            "on=check(R.zero,on=$a.object,c=@v/q,b=$t.value)",
        ];
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let before =
            ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 2, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert!(!has(&normal.receipt, "nodes"));
        assert!(!has(&normal.receipt, "result"));
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
            assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
        }
        assert_eq!(
            s(get(answer(&normal.receipt, "off"), "applicability")),
            "not_applicable"
        );
        for id in ["a", "on"] {
            let answer = answer(&normal.receipt, id);
            assert_eq!(s(get(answer, "status")), "undetermined");
            assert!(!arr(get(answer, "reasons")).is_empty());
            assert!(
                arr(get(answer, "reasons"))
                    .iter()
                    .all(|r| s(get(r, "code")) == "missing_observation")
            );
        }
        eprintln!(
            "finite missing product {name}/{ty}: stdout {} bytes",
            normal.stdout.len()
        );
        requests.extend([
            "p=check(R.zero,on=$a.object,c=@v/p,b=$t.value)",
            "n=needed($on)",
        ]);
        let r = asks(&dir, &requests);
        let j = saved(&dir, &r, "partial", 2);
        assert!(has(get(answer(&j, "a"), "outputs"), "object"));
        assert_eq!(s(get(answer(&j, "p"), "status")), "established");
        assert_eq!(s(get(answer(&j, "off"), "applicability")), "not_applicable");
        let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
        assert!(
            arr(get(plan, "requirements"))
                .iter()
                .any(
                    |r| s(get(get(r, "field"), "field")) == "Build.Part.quantity"
                        && s(get(get(r, "field"), "subject")) == "q"
                )
        );
        let mut reuse_args = vec![
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
        ];
        for request in requests {
            reuse_args.extend(["--ask", request]);
        }
        let reused = cli::run(&dir, &reuse_args);
        assert_eq!(reused.code, 2, "{}", reused.stdout);
        assert!(reused.stderr.is_empty());
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] {
            assert_eq!(get(&j, field).value, get(&again, field).value);
        }
    }
}
#[test]
fn active_parameter_product_keeps_missing_observation_undetermined() {
    active_products("parameter", &[
            ("", ""),
            ("", " when true"),
            (",u:Unit", " when u=unit"),
            ("", " when false implies n*n=1"),
            ("", " when true or n*n=1"),
            ("", " when sum(list<Q>[rat(1,2),rat(1,2)])=1"),
            ("", " when count(list<Number>[n,n])=2"),
            ("", " when sum(list<Number>[n,-n])=0"),
            ("", " when some(n)=some(n)"),
            ("", " when (n,true)=(n,true)"),
            ("", " when list<Number>[n,n]=list<Number>[n,n]"),
    ]);
}
fn active_products(name: &str, guards: &[(&str,&str)]) {
    for ty in ["Z", "Q"] {
        for (case,(extra,guard)) in guards.iter().enumerate() {
            let guard = guard.replace("Number",ty);
            let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
            let body = format!("law required zero(c:Part,n:{ty}{extra}){guard}:n*c.quantity=0;");
            let dir = files_with_definition(&format!("active-product-{name}-{ty}-{case}"), &body, true, &definition);
            if ty == "Q" {
                let map = std::fs::read_to_string(dir.join("a.json"))
                    .unwrap()
                    .replace(r#""value":"0""#, r#""value":["0","1"]"#);
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let requests = [
                "b=build(R,on=@v/root)",
                "p=check(R.zero,on=$b.object,c=@v/p)",
                "q=check(R.zero,on=$b.object,c=@v/q)",
                "n=needed($b)",
            ];
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in requests {
                args.extend(["--ask", request]);
            }
            let before =
                ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, 2, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert!(!has(&normal.receipt, "nodes"));
            assert!(!has(&normal.receipt, "result"));
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
                assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
            }
            eprintln!(
                "active missing product {ty}/{guard}: stdout {} bytes",
                normal.stdout.len()
            );
            for id in ["b", "q"] {
                let answer = answer(&normal.receipt, id);
                assert_eq!(s(get(answer, "status")), "undetermined");
                let reasons = arr(get(answer, "reasons"));
                assert!(!reasons.is_empty());
                assert!(
                    reasons
                        .iter()
                        .all(|r| s(get(r, "code")) == "missing_observation")
                );
            }
            assert_eq!(
                s(get(answer(&normal.receipt, "p"), "status")),
                "established"
            );
            let r = asks(&dir, &requests);
            let j = saved(&dir, &r, "partial", 2);
            assert!(has(get(answer(&j, "b"), "outputs"), "object"));
            assert!(!has(get(answer(&j, "b"), "outputs"), "algebra"));
            let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "field"
            )) == "Build.Part.quantity"
                && s(get(get(r, "field"), "subject")) == "q"));
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, 2, "{}", reused.stdout);
            assert!(reused.stderr.is_empty());
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for field in ["answers", "nodes"] {
                assert_eq!(get(&j, field).value, get(&again, field).value);
            }
        }
    }
}
#[test]
fn missing_coefficient_does_not_hide_unsupported_integer_existential() {
    let dir = files(
        "existential-product-missing",
        "law required zero(c:Part):exists n:Z.n*n=c.quantity;",
        true,
    );
    let r = cli::run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "b=build(R,on=@v/root)",
            "--ask",
            "q=check(R.zero,on=$b.object,c=@v/q)",
        ],
    );
    assert_eq!(r.code, 2, "{}", r.stdout);
    assert!(r.stderr.is_empty());
    for id in ["b", "q"] {
        let reasons = arr(get(answer(&r.receipt, id), "reasons"));
        assert!(
            reasons
                .iter()
                .any(|r| s(get(r, "code")) == "missing_observation")
        );
        assert!(
            reasons
                .iter()
                .any(|r| s(get(r, "code")) == "unsupported_algorithm")
        );
    }
}
#[test]
fn inactive_parameter_product_keeps_missing_body_outside_applicability() {
    inactive_products(
        "parameter",
        &[
            "false",
            "inactive(n)",
            "false and n*n=1",
            "count(list<Bool>[])>0",
            "sum(list<Q>[])!=0",
            "count(list<Number>[n,n])=1",
            "sum(list<Number>[n,-n])!=0",
            "some(n)=none<Number>",
            "some(n+1)=some(n)",
            "some(n)!=some(n)",
            "(n,true)=(n,false)",
            "(n+1,true)=(n,true)",
            "(n,true)!=(n,true)",
            "(n,true)=(0,false)",
            "list<Number>[n]=list<Number>[n,n]",
            "list<Number>[n,n+1]=list<Number>[n+1,n]",
            "list<Number>[n]!=list<Number>[n]",
            "list<Number>[n,0]=list<Number>[0,1]",
        ],
    );
}
#[test]
fn text_literal_false_guard_keeps_missing_values_undetermined() {
    inactive_products("text-literal", &[r#"(n,"ready")=(n,"done")"#]);
}
fn inactive_products(name: &str, guards: &[&str]) {
    inactive_products_with_guard_reads(name, guards, false);
}
fn inactive_products_with_guard_reads(name: &str, guards: &[&str], guard_reads: bool) {
    for ty in ["Z", "Q"] {
        for guard in guards {
            let guard = guard.replace("Number",ty);
            for read_missing in [false, true] {
                let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
                let view = if read_missing {
                    format!("view amount(c:Part):{ty}=c.quantity;")
                } else {
                    String::new()
                };
                let body = format!(
                    "view inactive(n:{ty}):Bool=n+1=n;{view}law required zero(c:Part,n:{ty}) when {guard}:n*c.quantity=0;"
                );
                let dir =
                    files_with_definition(&format!("inactive-product-{name}-{ty}-{read_missing}"), &body, true, &definition);
                if ty == "Q" {
                    let map = std::fs::read_to_string(dir.join("a.json"))
                        .unwrap()
                        .replace(r#""value":"0""#, r#""value":["0","1"]"#);
                    std::fs::write(dir.join("a.json"), map).unwrap();
                }
                let mut requests = vec![
                    "b=build(R,on=@v/root)",
                    "p=check(R.zero,on=$b.object,c=@v/p)",
                    "q=check(R.zero,on=$b.object,c=@v/q)",
                ];
                if read_missing {
                    requests.extend(["v=evaluate(R.amount,on=$b.object,c=@v/q)", "n=needed($v)"]);
                }
                // 恒偽でもguard自身の原始読取りはbuildの支持に残る。
                let build_missing = read_missing || guard_reads;
                let code = if build_missing { 2 } else { 0 };
                let mut args = vec![
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                ];
                for request in &requests {
                    args.extend(["--ask", request]);
                }
                let before: Vec<_> = ["d.json", "l.law", "a.json"]
                    .map(|name| std::fs::read(dir.join(name)).unwrap())
                    .into();
                let normal = cli::run(&dir, &args);
                assert_eq!(normal.code, code, "{ty}/{guard}: {}", normal.stdout);
                assert!(normal.stderr.is_empty());
                assert!(!has(&normal.receipt, "nodes"));
                assert!(!has(&normal.receipt, "result"));
                assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
                for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
                    assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
                }
                for id in ["p", "q"] {
                    assert_eq!(
                        s(get(answer(&normal.receipt, id), "applicability")),
                        "not_applicable"
                    );
                }
                eprintln!(
                    "inactive product {ty}/{guard}: stdout {} bytes",
                    normal.stdout.len()
                );
                // 同じ未観測値を実際に求めれば未決。適用外は値の捏造ではない。
                let r = asks(&dir, &requests);
                let j = saved(
                    &dir,
                    &r,
                    if build_missing { "partial" } else { "complete" },
                    code,
                );
                assert_eq!(
                    has(get(answer(&j, "b"), "outputs"), "algebra"),
                    !build_missing
                );
                for id in ["p", "q"] {
                    assert_eq!(s(get(answer(&j, id), "status")), "established");
                    assert_eq!(s(get(answer(&j, id), "applicability")), "not_applicable");
                }
                if read_missing {
                    assert_eq!(s(get(answer(&j, "v"), "status")), "undetermined");
                    assert!(!has(get(answer(&j, "v"), "outputs"), "value"));
                    let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
                    assert!(
                        arr(get(plan, "requirements"))
                            .iter()
                            .any(|r| s(get(get(r, "field"), "field")) == "Build.Part.quantity")
                    );
                }
                let mut reuse_args = vec![
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
                ];
                for request in requests {
                    reuse_args.extend(["--ask", request]);
                }
                let reused = cli::run(&dir, &reuse_args);
                assert_eq!(reused.code, code, "{}", reused.stdout);
                assert!(reused.stderr.is_empty());
                let again = result_json(&dir, &reused);
                assert!(warnings(&again).is_empty());
                for field in ["answers", "nodes"] {
                    assert_eq!(get(&j, field).value, get(&again, field).value);
                }
            }
        }
    }
}
#[test]
fn observed_parameter_products_feed_public_build() {
    let dir=files("observed-parameter-product","law required zero(c:Part,n:Z):n*c.quantity=0;",false);
    let r=asks(&dir,&["b=build(R,on=@v/root)","p=check(R.zero,on=$b.object,c=@v/p)","q=check(R.zero,on=$b.object,c=@v/q)"]);
    let j=saved(&dir,&r,"complete",1);
    assert_eq!(s(get(answer(&j,"p"),"status")),"established");
    assert_eq!(s(get(answer(&j,"q"),"status")),"refuted");
}
#[test]
fn predicate_helper_guards_keep_missing_reads_separate_from_constant_truth() {
    for condition in ["x=x", "true"] {
        let dir=files("predicate-guard-missing", &format!("view active(x:Z,y:Z):Bool={condition};view zero():Z=0;view one():Z=1;law required equal(c:Part,n:Z) when active(n,c.quantity):n=0;"),true);
        let r=asks(&dir,&["b=build(R,on=@v/root)","z=evaluate(R.zero,on=$b.object)","o=evaluate(R.one,on=$b.object)","p=check(R.equal,on=$b.object,c=@v/p,n=$z.value)","q=check(R.equal,on=$b.object,c=@v/q,n=$o.value)","n=needed($b)"]);
        let j=saved(&dir,&r,"partial",2);
        assert_eq!(s(get(answer(&j,"p"),"status")),"established");
        // 未観測yのどの補完でもguardは真。n=1の本体は反証できるが、読取りの欠測は残る。
        assert_eq!(s(get(answer(&j,"q"),"status")),"refuted");
        let plan=value(&j,get(get(answer(&j,"n"),"outputs"),"plan"));
        assert!(arr(get(plan,"requirements")).iter().any(|r| s(get(get(r,"field"),"field"))=="Build.Part.quantity"));
    }
}
#[test]
fn predicate_helper_guards_keep_parameter_dependent_laws() {
    for ty in ["Z", "Q"] {
        let dir=files("predicate-helper-guard", &format!("view active(x:{ty}):Bool=x=x;law required zero(c:Part,n:{ty}) when active(n):n=0;"),false);
        let r=asks(&dir,&["b=build(R,on=@v/root)","c=check(R.zero,on=$b.object,c=@v/p)"]);
        let j=saved(&dir,&r,"complete",1);
        assert!(has(get(answer(&j,"b"),"outputs"),"algebra"));
        assert_eq!(s(get(answer(&j,"c"),"status")),"refuted");
    }
}
#[test]
fn predicate_helper_guards_build_check_and_reuse_without_extra_files() {
    for ty in ["Z","Q"] { for active in [true,false] {
        let condition=if active {"x=x"}else{"x+1=x"};
        let dir=files("predicate-guard-delivery",&format!("view inner(x:{ty}):Bool={condition};view active(n:{ty}):Bool=inner(n);view zero():{ty}=0;view one():{ty}=1;law required equal(c:Part,n:{ty}) when active(n):n=0;"),false);
        let requests=["b=build(R,on=@v/root)","z=evaluate(R.zero,on=$b.object)","o=evaluate(R.one,on=$b.object)","all=check(R.equal,on=$b.object,c=@v/p)","zero=check(R.equal,on=$b.object,c=@v/p,n=$z.value)","one=check(R.equal,on=$b.object,c=@v/p,n=$o.value)"];
        let mut args=vec!["run","--atom-definition","d.json","--law","l.law","--archmap","a.json"];
        for request in requests { args.extend(["--ask",request]); }
        let normal=cli::run(&dir,&args); let code=if active{1}else{0};
        assert_eq!(normal.code,code,"{}",normal.stdout); assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(),3); assert!(!has(&normal.receipt,"nodes"));
        eprintln!("predicate guard {ty}/{active}: stdout {} bytes",normal.stdout.len());
        let r=asks(&dir,&requests); let j=saved(&dir,&r,"complete",code);
        assert_eq!(s(get(answer(&j,"zero"),"status")),"established");
        for id in ["all","one"] { assert_eq!(s(get(answer(&j,id),"status")),if active{"refuted"}else{"established"}); }
        if !active { assert_eq!(s(get(answer(&j,"all"),"applicability")),"not_applicable"); }
        args.extend(["--out","again","--reuse","out"]); let reused=cli::run(&dir,&args);
        assert_eq!(reused.code,code,"{}",reused.stdout); let again=result_json(&dir,&reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers","nodes"] { assert_eq!(get(&j,field).value,get(&again,field).value); }
    }}
}
#[test]
fn parameter_predicate_helpers_feed_public_build() {
    let dir = files("parameter-predicate-helper", "view iszero(n:Z):Bool=n=0;law required zero(c:Part,n:Z):iszero(n);", false);
    let r = asks(&dir, &["b=build(R,on=@v/root)", "c=check(R.zero,on=$b.object,c=@v/p)"]);
    let j = saved(&dir, &r, "complete", 1);
    assert!(has(get(answer(&j,"b"),"outputs"),"algebra"));
}
#[test]
fn parameter_predicate_helpers_keep_caller_bindings_and_reuse() {
    for ty in ["Z", "Q"] { for nested in [false,true] {
        let helpers = if nested {
            format!("view eq(x:{ty},y:{ty}):Bool=let n=x in n=y;view flipped(m:{ty},n:{ty}):Bool=eq(n,m);")
        } else { format!("view flipped(m:{ty},n:{ty}):Bool=n=m;") };
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let dir = files_with_definition("predicate-helper-bindings", &format!("{helpers}view one():{ty}=1;view two():{ty}=2;law required equal(c:Part,n:{ty},m:{ty}):flipped(m,n+c.quantity);"), false, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#""value":"0""#,r#""value":["0","1"]"#).replace(r#""value":"1""#,r#""value":["1","1"]"#);
            std::fs::write(dir.join("a.json"),map).unwrap();
        }
        let requests = ["b=build(R,on=@v/root)","i=evaluate(R.one,on=$b.object)","j=evaluate(R.two,on=$b.object)","all=check(R.equal,on=$b.object,c=@v/p)","p=check(R.equal,on=$b.object,c=@v/p,n=$i.value,m=$i.value)","q0=check(R.equal,on=$b.object,c=@v/q,n=$i.value,m=$i.value)","q1=check(R.equal,on=$b.object,c=@v/q,n=$i.value,m=$j.value)"];
        let mut args = vec!["run","--atom-definition","d.json","--law","l.law","--archmap","a.json"];
        for request in requests { args.extend(["--ask",request]); }
        let normal = cli::run(&dir,&args);
        assert_eq!(normal.code,1,"{}",normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(),3);
        assert!(!has(&normal.receipt,"nodes"));
        eprintln!("predicate helper {ty}/{nested}: stdout {} bytes",normal.stdout.len());
        let r=asks(&dir,&requests); let j=saved(&dir,&r,"complete",1);
        for (id,status) in [("all","refuted"),("p","established"),("q0","refuted"),("q1","established")] { assert_eq!(s(get(answer(&j,id),"status")),status); }
        args.extend(["--out","again","--reuse","out"]);
        let reused=cli::run(&dir,&args); assert_eq!(reused.code,1,"{}",reused.stdout);
        let again=result_json(&dir,&reused); assert!(warnings(&again).is_empty());
        for field in ["answers","nodes"] { assert_eq!(get(&j,field).value,get(&again,field).value); }
    }}
}
#[test]
fn affine_parameter_families_feed_localization_and_diagnosis() {
    for predicate in ["n=0", "n+c.quantity=0", "2*(n+c.quantity)=0"] {
        let dir = files("affine-family-local", &format!("law required zero(c:Part,n:Z):{predicate}; local each(c:Part) reads (c.owner,c.quantity);"), false);
        let r = asks(&dir, &["b=build(R,on=@v/root)", "l=localize($b.object)", "e=diagnose($l.system)", "s=diagnose($l.system,side=semantic)"]);
        let j = saved(&dir, &r, "complete", 1);
        for id in ["e", "s"] { assert_eq!(s(get(answer(&j,id),"status")),"refuted", "{predicate}/{id}"); }
    }
}
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
            assert!(warnings(&again).is_empty());
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
#[test]
fn universal_true_guards_feed_public_build_and_checks() {
    for (ty, guard, offset) in [("Z", "true", 0), ("Q", "n=n", 1)] {
        let dir = files(&format!("true-guard-{ty}"), &format!(
            "law required balanced(c:Part,n:{ty}) when {guard}:n=n+{offset};"
        ), false);
        let normal = cli::run(&dir, &["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json",
            "--ask", "b=build(R,on=@v/root)", "--ask", "c=check(R.balanced,on=$b.object,c=@v/p)"]);
        assert_eq!(normal.code, offset, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        assert!(!has(&normal.receipt, "nodes"));
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        eprintln!("true guard {ty}: stdout {} bytes", normal.stdout.len());
        let run = asks(&dir, &["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/p)"]);
        let result = saved(&dir, &run, "complete", offset);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "c"), "status")), if offset == 0 { "established" } else { "refuted" });
    }
}
#[test]
fn numeric_views_in_universal_laws_feed_public_build_and_checks() {
    for (ty, offset) in [("Z", 0), ("Q", 1)] {
        let dir = files(&format!("numeric-view-{ty}"), &format!(
            "view plus(x:{ty}):{ty}=x+1;law required balanced(c:Part,n:{ty}):plus(n)=n+1+{offset};"
        ), false);
        let run = asks(&dir, &["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/p)"]);
        let result = saved(&dir, &run, "complete", offset);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "c"), "status")), if offset == 0 { "established" } else { "refuted" });
    }
}
#[test]
fn numeric_view_build_delivers_values_and_reuses_without_extra_files() {
    let dir = files("numeric-view-delivery", "view plus(x:Z):Z=let y=x+1 in y;view seed():Z=41;law required balanced(c:Part,n:Z):plus(n)=n+1;", false);
    let requests = ["b=build(R,on=@v/root)", "i=evaluate(R.seed,on=$b.object)", "v=evaluate(R.plus,on=$b.object,x=$i.value)"];
    let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
    for request in requests { args.extend(["--ask", request]); }
    let normal = cli::run(&dir, &args);
    assert_eq!(normal.code, 0, "{}", normal.stdout);
    assert!(normal.stderr.is_empty());
    assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
    assert!(!has(&normal.receipt, "nodes"));
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    eprintln!("numeric view: stdout {} bytes", normal.stdout.len());
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 0);
    assert_eq!(s(value(&result, get(get(answer(&result, "v"), "outputs"), "value"))), "42");
    eprintln!("numeric view: saved {} bytes", std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
    args.extend(["--out", "again", "--reuse", "out"]);
    let reused = cli::run(&dir, &args);
    assert_eq!(reused.code, 0, "{}", reused.stdout);
    let again = result_json(&dir, &reused);
    for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
}
#[test]
fn nested_numeric_helpers_feed_public_build_and_checks() {
    let dir = files("nested-numeric-helpers", "view plus(x:Z):Z=x+1;view twice(y:Z):Z=plus(plus(y));law required balanced(c:Part,n:Z):twice(n)=n+2;", false);
    let run = asks(&dir, &["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/p)"]);
    let result = saved(&dir, &run, "complete", 0);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "c"), "status")), "established");
}
#[test]
fn inactive_numeric_laws_feed_public_build_and_checks() {
    for (ty, guard) in [("Z", "false"), ("Q", "n+1=n")] {
        let dir = files(&format!("inactive-numeric-{ty}"), &format!(
            "law required balanced(c:Part,n:{ty}) when {guard}:n=n+1;"
        ), false);
        let requests = ["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/p)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 0, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        assert!(!has(&normal.receipt, "nodes"));
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert_eq!(s(get(answer(&normal.receipt, "c"), "applicability")), "not_applicable");
        eprintln!("inactive numeric {ty}: stdout {} bytes", normal.stdout.len());
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 0);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "c"), "status")), "established");
        assert_eq!(s(get(answer(&result, "c"), "applicability")), "not_applicable");
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 0, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }
}
#[test]
fn boolean_view_guards_feed_public_build_and_checks() {
    for (ty, condition, applicable) in [("Z", "x=x", true), ("Q", "x+1=x", false)] {
        let dir = files(&format!("boolean-view-guard-{ty}"), &format!(
            "view active(x:{ty}):Bool={condition};law required balanced(c:Part,n:{ty}) when active(n):n=n;"
        ), false);
        let run = asks(&dir, &["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/p)"]);
        let result = saved(&dir, &run, "complete", 0);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "c"), "status")), "established");
        assert_eq!(s(get(answer(&result, "c"), "applicability")), if applicable { "applicable" } else { "not_applicable" });
    }
}
#[test]
fn observed_numeric_view_family_feeds_public_build_and_evaluate() {
    let dir = files("observed-numeric-view", "view plus(c:Part,x:Z):Z=c.quantity+x;view seed():Z=2;law required balanced(c:Part):c.quantity=c.quantity;", false);
    let requests = ["b=build(R,on=@v/root)", "s=evaluate(R.seed,on=$b.object)", "v=evaluate(R.plus,on=$b.object,c=@v/q,x=$s.value)"];
    let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
    for request in requests { args.extend(["--ask", request]); }
    let normal = cli::run(&dir, &args);
    assert_eq!(normal.code, 0, "{}", normal.stdout);
    assert!(normal.stderr.is_empty());
    assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
    assert!(!has(&normal.receipt, "nodes"));
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    eprintln!("observed numeric view: stdout {} bytes", normal.stdout.len());
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 0);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(value(&result, get(get(answer(&result, "v"), "outputs"), "value"))), "3");
    eprintln!("observed numeric view: saved {} bytes", std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
    args.extend(["--out", "again", "--reuse", "out"]);
    let reused = cli::run(&dir, &args);
    assert_eq!(reused.code, 0, "{}", reused.stdout);
    let again = result_json(&dir, &reused);
    for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
}
#[test]
fn mixed_numeric_view_family_feeds_public_build_and_evaluate() {
    let dir = files("mixed-numeric-view", "view plus(c:Part,x:Z,b:Bool):Z=if b then c.quantity+x else x;view seed():Z=2;view enabled():Bool=true;law required balanced(c:Part):c.quantity=c.quantity;", false);
    let requests = ["b=build(R,on=@v/root)", "s=evaluate(R.seed,on=$b.object)", "e=evaluate(R.enabled,on=$b.object)", "v=evaluate(R.plus,on=$b.object,c=@v/q,x=$s.value,b=$e.value)"];
    let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
    for request in requests { args.extend(["--ask", request]); }
    let normal = cli::run(&dir, &args);
    assert_eq!(normal.code, 0, "{}", normal.stdout);
    assert!(normal.stderr.is_empty());
    assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
    assert!(!has(&normal.receipt, "nodes"));
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    eprintln!("mixed numeric view: stdout {} bytes", normal.stdout.len());
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 0);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(value(&result, get(get(answer(&result, "v"), "outputs"), "value"))), "3");
    eprintln!("mixed numeric view: saved {} bytes", std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
    args.extend(["--out", "again", "--reuse", "out"]);
    let reused = cli::run(&dir, &args);
    assert_eq!(reused.code, 0, "{}", reused.stdout);
    let again = result_json(&dir, &reused);
    for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
}
#[test]
fn observed_numeric_law_cancellation_feeds_public_build_and_check() {
    for (offset, missing) in [(0, false), (1, false), (1, true)] {
        let body = if missing { "view plus(c:Part,x:Z):Z=c.quantity+x;law required balanced(c:Part,n:Z):let a=plus(c,n) in a=n+c.quantity+1;".to_owned() }
            else { format!("law required balanced(c:Part,n:Z):c.quantity+n=n+c.quantity+{offset};") };
        let dir = files(&format!("observed-numeric-law-{offset}-{missing}"), &body, missing);
        let code = if missing { 2 } else { offset };
        let requests = ["b=build(R,on=@v/root)", "c=check(R.balanced,on=$b.object,c=@v/q)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, code, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        assert!(!has(&normal.receipt, "nodes"));
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        eprintln!("observed numeric law {offset}: stdout {} bytes", normal.stdout.len());
        if missing { assert_missing_quantity_once(&normal.receipt); }
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, if missing { "partial" } else { "complete" }, code);
        if missing { assert_missing_quantity_once(&result); }
        assert!(has(get(answer(&result, "b"), "outputs"), if missing { "object" } else { "algebra" }));
        assert_eq!(s(get(answer(&result, "c"), "status")), if offset == 0 { "established" } else { "refuted" });
        eprintln!("observed numeric law {offset}: saved {} bytes", std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }
}
fn assert_missing_quantity_once(result: &JNode) {
    for id in ["b", "c"] {
        let reasons = arr(get(answer(result, id), "reasons"));
        assert_eq!(reasons.len(), 1);
        assert_eq!(s(get(&reasons[0], "code")), "missing_observation");
        let missing = arr(get(&reasons[0], "missing"));
        assert_eq!(missing.len(), 1);
        assert_eq!(s(get(&missing[0], "subject")), "q");
        assert_eq!(s(get(&missing[0], "field")), "Build.Part.quantity");
    }
}
#[test]
fn state_dependent_numeric_law_builds_and_checks_each_observed_object() {
    let dir = files("state-dependent-law", "law required balanced(c:Part,n:Z):c.quantity+n=n;", false);
    let requests = ["b=build(R,on=@v/root)", "p=check(R.balanced,on=$b.object,c=@v/p)", "q=check(R.balanced,on=$b.object,c=@v/q)"];
    let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
    for request in requests { args.extend(["--ask", request]); }
    let normal = cli::run(&dir, &args);
    assert_eq!(normal.code, 1, "{}", normal.stdout);
    assert!(normal.stderr.is_empty());
    assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    eprintln!("state-dependent law: stdout {} bytes", normal.stdout.len());
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "p"), "status")), "established");
    assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
    eprintln!("state-dependent law: saved {} bytes", std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
    args.extend(["--out", "again", "--reuse", "out"]);
    let reused = cli::run(&dir, &args);
    assert_eq!(reused.code, 1, "{}", reused.stdout);
    let again = result_json(&dir, &reused);
    for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
}
#[test]
fn scaled_numeric_binders_build_check_and_reuse() {
    for (ty, equation, p_value, q_value) in [
        ("Z", "2*(n+c.quantity)=m", "2", "4"), ("Z", "(n+c.quantity)*2=m", "2", "4"),
        ("Q", "rat(1,2)*(n+c.quantity)=m", "rat(1,2)", "1"), ("Q", "(n+c.quantity)*rat(1,2)=m", "rat(1,2)", "1"),
    ] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let dir = files_with_definition(&format!("scaled-binders-{ty}-{equation}"), &format!(
            "view one():{ty}=1;view pvalue():{ty}={p_value};view qvalue():{ty}={q_value};law required equal(c:Part,n:{ty},m:{ty}):{equation};"
        ), false, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap()
                .replace(r#""value":"0""#, r#""value":["0","1"]"#)
                .replace(r#""value":"1""#, r#""value":["1","1"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = ["b=build(R,on=@v/root)", "i=evaluate(R.one,on=$b.object)", "pv=evaluate(R.pvalue,on=$b.object)", "qv=evaluate(R.qvalue,on=$b.object)",
            "all=check(R.equal,on=$b.object,c=@v/p)", "p=check(R.equal,on=$b.object,c=@v/p,n=$i.value,m=$pv.value)",
            "q0=check(R.equal,on=$b.object,c=@v/q,n=$i.value,m=$pv.value)", "q1=check(R.equal,on=$b.object,c=@v/q,n=$i.value,m=$qv.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 1);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        for (id, status) in [("all", "refuted"), ("p", "established"), ("q0", "refuted"), ("q1", "established")] {
            assert_eq!(s(get(answer(&result, id), "status")), status);
        }
        eprintln!("scaled binders {ty}/{equation}: stdout {} bytes, saved {} bytes", normal.stdout.len(), std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
        args.extend(["--reuse", "out", "--out", "again"]);
        let reused = cli::run(&dir, &args);
        let again = saved(&dir, &reused, "complete", 1);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }
}
#[test]
fn scaled_mixed_parameter_law_builds_for_later_checks() {
    let dir = files("scaled-mixed-parameter", "view zero():Z=0;law required equal(c:Part,n:Z):2*(n+c.quantity)=0;", false);
    let run = asks(&dir, &["b=build(R,on=@v/root)", "z=evaluate(R.zero,on=$b.object)",
        "all=check(R.equal,on=$b.object,c=@v/p)", "p=check(R.equal,on=$b.object,c=@v/p,n=$z.value)"]);
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "all"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "p"), "status")), "established");
}
#[test]
fn mixed_numeric_binders_build_check_and_reuse() {
    for (ty, equation) in [("Z", "2*n+c.quantity=m"), ("Q", "m=2*n+c.quantity"), ("Z", "n+c.quantity=2*n+m")] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let dir = files_with_definition(&format!("mixed-binders-{ty}-{equation}"), &format!(
            "view zero():{ty}=0;view one():{ty}=1;law required equal(c:Part,n:{ty},m:{ty}):{equation};"
        ), false, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap()
                .replace(r#""value":"0""#, r#""value":["0","1"]"#)
                .replace(r#""value":"1""#, r#""value":["1","1"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = ["b=build(R,on=@v/root)", "z=evaluate(R.zero,on=$b.object)", "i=evaluate(R.one,on=$b.object)",
            "all=check(R.equal,on=$b.object,c=@v/p)", "p=check(R.equal,on=$b.object,c=@v/p,n=$z.value,m=$z.value)",
            "q0=check(R.equal,on=$b.object,c=@v/q,n=$z.value,m=$z.value)", "q1=check(R.equal,on=$b.object,c=@v/q,n=$z.value,m=$i.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 1);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        for (id, status) in [("all", "refuted"), ("p", "established"), ("q0", "refuted"), ("q1", "established")] {
            assert_eq!(s(get(answer(&result, id), "status")), status);
        }
        eprintln!("mixed binders {ty}/{equation}: stdout {} bytes, saved {} bytes", normal.stdout.len(), std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
        args.extend(["--reuse", "out", "--out", "again"]);
        let reused = cli::run(&dir, &args);
        let again = saved(&dir, &reused, "complete", 1);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }
}
#[test]
fn mixed_observation_parameter_law_builds_for_later_checks() {
    let dir = files("mixed-observation-parameter", "view zero():Z=0;law required equal(c:Part,n:Z):n+c.quantity=0;", false);
    let run = asks(&dir, &["b=build(R,on=@v/root)", "z=evaluate(R.zero,on=$b.object)",
        "all=check(R.equal,on=$b.object,c=@v/p)", "p=check(R.equal,on=$b.object,c=@v/p,n=$z.value)"]);
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "all"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "p"), "status")), "established");
}
#[test]
fn cancelled_observation_parameter_law_builds_for_later_checks() {
    for (ty, equation) in [
        ("Z", "n+c.quantity=c.quantity+1"), ("Z", "c.quantity+1=n+c.quantity"),
        ("Q", "n+c.quantity=c.quantity+1"), ("Q", "c.quantity+1=n+c.quantity"),
    ] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let dir = files_with_definition(&format!("cancelled-observation-{ty}-{equation}"), &format!("view one():{ty}=1;law required equal(c:Part,n:{ty}):{equation};"), false, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap()
                .replace(r#""value":"0""#, r#""value":["0","1"]"#)
                .replace(r#""value":"1""#, r#""value":["1","1"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = ["b=build(R,on=@v/root)", "i=evaluate(R.one,on=$b.object)",
            "all=check(R.equal,on=$b.object,c=@v/p)", "p=check(R.equal,on=$b.object,c=@v/p,n=$i.value)",
            "q=check(R.equal,on=$b.object,c=@v/q,n=$i.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 1);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        for (id, status) in [("all", "refuted"), ("p", "established"), ("q", "established")] {
            assert_eq!(s(get(answer(&result, id), "status")), status);
        }
        eprintln!("cancelled observation {ty}/{equation}: stdout {} bytes, saved {} bytes", normal.stdout.len(), std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
        args.extend(["--reuse", "out", "--out", "again"]);
        let reused = cli::run(&dir, &args);
        let again = saved(&dir, &reused, "complete", 1);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }
}
#[test]
fn observed_offset_parameter_law_builds_for_later_checks() {
    for ty in ["Z", "Q"] {
        for equation in ["n=c.quantity+1", "c.quantity+1=n"] {
            let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
            let dir = files_with_definition(&format!("observed-offset-{ty}-{equation}"), &format!(
                "view one():{ty}=1;law required equal(c:Part,n:{ty}):{equation};"
            ), false, &definition);
            if ty == "Q" {
                let map = std::fs::read_to_string(dir.join("a.json")).unwrap()
                    .replace(r#""value":"0""#, r#""value":["0","1"]"#)
                    .replace(r#""value":"1""#, r#""value":["1","1"]"#);
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let requests = ["b=build(R,on=@v/root)", "i=evaluate(R.one,on=$b.object)",
                "all=check(R.equal,on=$b.object,c=@v/p)", "p=check(R.equal,on=$b.object,c=@v/p,n=$i.value)",
                "q=check(R.equal,on=$b.object,c=@v/q,n=$i.value)"];
            let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
            for request in requests { args.extend(["--ask", request]); }
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, 1, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
            let run = asks(&dir, &requests);
            let result = saved(&dir, &run, "complete", 1);
            assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
            for (id, status) in [("all", "refuted"), ("p", "established"), ("q", "refuted")] {
                assert_eq!(s(get(answer(&result, id), "status")), status);
            }
            eprintln!("observed offset {ty}/{equation}: stdout {} bytes, saved {} bytes", normal.stdout.len(), std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
            args.extend(["--reuse", "out", "--out", "again"]);
            let reused = cli::run(&dir, &args);
            let again = saved(&dir, &reused, "complete", 1);
            assert!(warnings(&again).is_empty());
            for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
        }
    }
}
#[test]
fn true_guards_on_parameter_dependent_laws_feed_public_build() {
    for (ty, guard, equation) in [("Z", "true", "n=0"), ("Q", "n=n", "n=0"), ("Z", "n=n", "n=c.quantity")] {
        let dir = files(&format!("parameter-guard-{ty}-{equation}"), &format!(
            "view zero():{ty}=0;law required equal(c:Part,n:{ty}) when {guard}:{equation};"
        ), false);
        let requests = ["b=build(R,on=@v/root)", "z=evaluate(R.zero,on=$b.object)",
            "all=check(R.equal,on=$b.object,c=@v/p)", "p=check(R.equal,on=$b.object,c=@v/p,n=$z.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 1);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "all"), "status")), "refuted");
        assert_eq!(s(get(answer(&result, "p"), "status")), "established");
        eprintln!("parameter guard {ty}/{guard}/{equation}: stdout {} bytes", normal.stdout.len());
        args.extend(["--reuse", "out", "--out", "again"]);
        let reused = cli::run(&dir, &args);
        let again = saved(&dir, &reused, "complete", 1);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
    }
}
#[test]
fn missing_observation_in_parameter_law_keeps_known_checks_and_needed() {
    let dir = files("missing-parameter-law", "view zero():Z=0;law required equal(c:Part,n:Z):n=c.quantity;", true);
    let requests = ["b=build(R,on=@v/root)", "z=evaluate(R.zero,on=$b.object)",
        "p=check(R.equal,on=$b.object,c=@v/p,n=$z.value)", "q=check(R.equal,on=$b.object,c=@v/q,n=$z.value)", "n=needed($b)"];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "partial", 2);
    assert_eq!(s(get(answer(&result, "b"), "status")), "undetermined");
    assert!(has(get(answer(&result, "b"), "outputs"), "object"));
    assert_eq!(s(get(answer(&result, "p"), "status")), "established");
    assert_eq!(s(get(answer(&result, "q"), "status")), "undetermined");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).iter().any(|r| {
        let field = get(r, "field");
        s(get(field, "subject")) == "q" && s(get(field, "field")) == "Build.Part.quantity"
    }));
}
#[test]
fn observed_and_parameter_numeric_law_builds_for_later_checks() {
    for ty in ["Z", "Q"] {
        for equation in ["n=c.quantity", "c.quantity=n"] {
            let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
            let body = format!("view zero():{ty}=0;view one():{ty}=1;law required equal(c:Part,n:{ty}):{equation};");
            let dir = files_with_definition(&format!("observed-parameter-{ty}-{equation}"), &body, false, &definition);
            if ty == "Q" {
                let map = std::fs::read_to_string(dir.join("a.json")).unwrap()
                    .replace(r#""value":"0""#, r#""value":["0","1"]"#)
                    .replace(r#""value":"1""#, r#""value":["1","1"]"#);
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let requests = ["b=build(R,on=@v/root)", "z=evaluate(R.zero,on=$b.object)", "i=evaluate(R.one,on=$b.object)",
                "all=check(R.equal,on=$b.object,c=@v/q)", "p0=check(R.equal,on=$b.object,c=@v/p,n=$z.value)",
                "q0=check(R.equal,on=$b.object,c=@v/q,n=$z.value)", "q1=check(R.equal,on=$b.object,c=@v/q,n=$i.value)"];
            let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
            for request in requests { args.extend(["--ask", request]); }
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, 1, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
            let run = asks(&dir, &requests);
            let result = saved(&dir, &run, "complete", 1);
            assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
            let algebra = value(&result, get(get(answer(&result, "b"), "outputs"), "algebra"));
            let equations = value(&result, get(algebra, "equations"));
            let base_row = &arr(get(equations, "objects"))[0];
            let presentation = value(&result, &arr(get(base_row, "presentations"))[0]);
            let ring = value(&result, get(presentation, "ring"));
            assert_eq!(arr(get(ring, "variables")).len(), 2);
            assert_eq!(s(get(value(&result, get(ring, "base")), "scalar")), ty);
            let mut axes = vec![];
            for coordinate in arr(get(presentation, "coordinates")) {
                let nu = value(&result, get(coordinate, "nu"));
                let epsilon = value(&result, get(coordinate, "epsilon"));
                assert_eq!(arr(get(nu, "parameters")).len(), 1);
                assert_eq!(arr(get(nu, "terms")).len(), 2);
                for term in arr(get(nu, "terms")) {
                    let powers = arr(get(term, "powers")).iter().map(num).collect::<Vec<_>>();
                    if powers.iter().any(|p| *p != 0) { axes.push(powers); }
                    else { assert_eq!(s(get(node(&result, get(term, "coefficient")), "type")), "Expression"); }
                }
                let terms = arr(get(epsilon, "terms"));
                assert_eq!(terms.len(), 1);
                assert!(arr(get(&terms[0], "powers")).iter().all(|p| num(p) == 0));
            }
            axes.sort();
            assert_eq!(axes, vec![vec![0,1], vec![1,0]]);
            for (id, status) in [("all", "refuted"), ("p0", "established"), ("q0", "refuted"), ("q1", "established")] {
                assert_eq!(s(get(answer(&result, id), "status")), status);
            }
            eprintln!("observed parameter {ty}/{equation}: stdout {} bytes, saved {} bytes", normal.stdout.len(), std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
            args.extend(["--reuse", "out", "--out", "again"]);
            let reused = cli::run(&dir, &args);
            let again = saved(&dir, &reused, "complete", 1);
            assert!(warnings(&again).is_empty());
            for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
        }
    }
}
#[test]
fn parameter_dependent_numeric_law_builds_without_constant_residual() {
    let dir = files("parameter-dependent-law", "law required zero(c:Part,n:Z):n=0;", false);
    let run = asks(&dir, &["b=build(R,on=@v/root)", "q=check(R.zero,on=$b.object,c=@v/q)"]);
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
}
#[test]
fn parameter_families_coexist_with_closed_numeric_laws() {
    for ty in ["Z", "Q"] {
        let dir = files(&format!("parameter-closed-{ty}"), &format!(
            "law required zero(c:Part,n:{ty}):n=0;law required plain(c:Part):0=0;"
        ), false);
        let requests = ["b=build(R,on=@v/root)", "q=check(R.zero,on=$b.object,c=@v/q)", "p=check(R.plain,on=$b.object,c=@v/p)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 1);
        assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
        assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
        assert_eq!(s(get(answer(&result, "p"), "status")), "established");
    }
}
#[test]
fn parameter_family_build_compares_identical_patterns() {
    let dir = files("parameter-identical-patterns", "law required zero(c:Part,n:Z):n=0;", false);
    let map = std::fs::read_to_string(dir.join("a.json")).unwrap()
        .replace(r#",{"id":"q","type":"Build.Part","origin":"model"}"#, "")
        .replace(r#",{"id":"oq","subject":"q","field":"Build.Part.owner","value":["v","root"],"origin":"model"}"#, "")
        .replace(r#",{"id":"xq","subject":"q","field":"Build.Part.quantity","value":"1","origin":"model"}"#, "");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let run = asks(&dir, &["b=build(R,on=@v/root)", "q=check(R.zero,on=$b.object,c=@v/p)"]);
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
}
#[test]
fn numeric_parameter_circuits_keep_pointwise_conditions_and_compact_cli() {
    for ty in ["Z", "Q"] {
        let dir = files(&format!("parameter-circuit-{ty}"), &format!(
            "view zero():{ty}=0;view one():{ty}=1;view difference(n:{ty},m:{ty}):{ty}=n-m;law required balanced(c:Part,n:{ty},m:{ty}):2*difference(n,m)=0;"
        ), false);
        let requests = ["b=build(R,on=@v/root)", "z=evaluate(R.zero,on=$b.object)", "i=evaluate(R.one,on=$b.object)", "all=check(R.balanced,on=$b.object,c=@v/q)",
            "zero=check(R.balanced,on=$b.object,c=@v/q,n=$z.value,m=$z.value)",
            "one=check(R.balanced,on=$b.object,c=@v/q,n=$i.value,m=$z.value)",
            "equal=check(R.balanced,on=$b.object,c=@v/q,n=$i.value,m=$i.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(s(get(&normal.receipt, "format")), "archsig.summary/1");
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 1);
        for (id, status) in [("all", "refuted"), ("zero", "established"), ("one", "refuted"), ("equal", "established")] {
            assert_eq!(s(get(answer(&result, id), "status")), status);
        }
        let algebra = value(&result, get(get(answer(&result, "b"), "outputs"), "algebra"));
        let equations = value(&result, get(algebra, "equations"));
        let base_row = &arr(get(equations, "objects"))[0];
        let presentation = value(&result, &arr(get(base_row, "presentations"))[0]);
        let ring = value(&result, get(presentation, "ring"));
        assert!(arr(get(ring, "variables")).is_empty());
        assert_eq!(s(get(value(&result, get(ring, "base")), "scalar")), ty);
        let ideal = value(&result, get(presentation, "required_ideal"));
        assert!(!has(ideal, "parameters"));
        for coordinate in arr(get(presentation, "coordinates")) {
            for key in ["nu", "epsilon"] {
                let polynomial = value(&result, get(coordinate, key));
                assert_eq!(arr(get(polynomial, "parameters")).len(), 2);
                for term in arr(get(polynomial, "terms")) {
                    let coefficient = node(&result, get(term, "coefficient"));
                    assert_eq!(s(get(coefficient, "type")), "Expression");
                    assert_eq!(get(get(coefficient, "value"), "parameters").value, get(polynomial, "parameters").value);
                }
            }
        }
        for witness in arr(get(presentation, "witness_ideals")) {
            assert_eq!(arr(get(value(&result, witness), "parameters")).len(), 2);
        }
        let coefficients = arr(get(ideal, "generators")).iter().flat_map(|r| arr(get(value(&result, r), "terms")))
            .map(|term| value(&result, get(term, "coefficient"))).collect::<Vec<_>>();
        assert!(!coefficients.is_empty());
        for coefficient in coefficients {
            let numerator = if ty == "Q" { &arr(coefficient)[0] } else { coefficient };
            assert!(matches!(s(numerator), "2" | "-2"));
        }
        let detectors = arr(get(algebra, "circuits"));
        assert!(!detectors.is_empty());
        for detector in detectors {
            let detector = value(&result, detector);
            assert_eq!(arr(get(detector, "parameters")).len(), 2);
            let cases = arr(get(detector, "cases"));
            assert!(!cases.is_empty());
            for case in cases {
                let case = value(&result, case);
                assert_eq!(arr(get(value(&result, get(case, "when")), "parameters")).len(), 2);
                assert!(!has(value(&result, get(case, "refutation")), "value"));
            }
        }
        eprintln!("parameter family {ty}: stdout {} bytes, saved {} bytes", normal.stdout.len(), std::fs::metadata(dir.join(s(get(&run.receipt, "result")))).unwrap().len());
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 1, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&again, field).value, get(&result, field).value); }
        let original = std::fs::read_to_string(dir.join(s(get(&run.receipt, "result")))).unwrap();
        let prefix = format!("\"type\":\"Polynomial\",\"value\":{{\"parameters\":[{{\"name\":\"n\",\"type\":\"{ty}\"}},{{\"name\":\"m\",\"type\":\"{ty}\"}}],");
        let tampered = original.replacen(&prefix, "\"type\":\"Polynomial\",\"value\":{", 1);
        assert_ne!(tampered, original);
        std::fs::create_dir(dir.join("tampered")).unwrap();
        std::fs::write(dir.join("tampered/result.json"), tampered).unwrap();
        let out_at = args.iter().position(|s| *s == "--out").unwrap() + 1;
        let reuse_at = args.iter().position(|s| *s == "--reuse").unwrap() + 1;
        args[out_at] = "rejected";
        args[reuse_at] = "tampered";
        let rejected = cli::run(&dir, &args);
        assert_eq!(rejected.code, 1, "{}", rejected.stdout);
        let checked = result_json(&dir, &rejected);
        assert!(!warnings(&checked).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&checked, field).value, get(&result, field).value); }
    }
}
fn files(name: &str, body: &str, missing: bool) -> PathBuf {
    files_with_definition(name, body, missing, DEFINITION)
}
fn files_with_definition(name: &str, body: &str, missing: bool, definition: &str) -> PathBuf {
    let dir = workdir(name);
    let defs =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
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
        ("d.json", definition.as_bytes()),
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
    let result_path = dir.join(s(get(&run.receipt, "result")));
    let saved_dir = result_path.parent().unwrap();
    for (src, dst) in [
        ("d.json", "inputs/definitions/0.json"),
        ("l.law", "inputs/law.law"),
        ("a.json", "inputs/archmap.json"),
    ] {
        assert_eq!(
            std::fs::read(dir.join(src)).unwrap(),
            std::fs::read(saved_dir.join(dst)).unwrap()
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

#[test]
fn observed_parameter_products_keep_rational_coefficients_and_explicit_reuse() {
    for ty in ["Z", "Q"] {
        for expression in ["n*c.quantity", "c.quantity*n", "2*(n*c.quantity)+c.quantity", "n*c.quantity+m*c.quantity", "product(n,c.quantity)"] {
            let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
            let body = format!("view product(x:{ty},y:{ty}):{ty}=x*y;law required zero(c:Part,n:{ty},m:{ty}):{expression}=0;");
            let dir = files_with_definition("products-reuse", &body, false, &definition);
            if ty == "Q" {
                let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#""value":"0""#, r#""value":["0","1"]"#).replace(r#""value":"1""#, r#""value":["1","2"]"#);
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let requests = ["b=build(R,on=@v/root)", "p=check(R.zero,on=$b.object,c=@v/p)", "q=check(R.zero,on=$b.object,c=@v/q)"];
            let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
            for request in requests { args.extend(["--ask", request]); }
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, 1, "{ty}/{expression}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            assert!(!has(&normal.receipt, "nodes"));
            eprintln!("product {ty}/{expression}: stdout {} bytes", normal.stdout.len());
            let r = asks(&dir, &requests);
            let j = saved(&dir, &r, "complete", 1);
            assert_eq!(s(get(answer(&j,"p"),"status")), "established");
            assert_eq!(s(get(answer(&j,"q"),"status")), "refuted");
            assert!(arr(get(&j,"nodes")).iter().any(|n| has(n,"value") && has(get(n,"value"),"operation") && s(get(get(n,"value"),"operation")) == "multiply"));
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, 1, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for field in ["answers", "nodes"] { assert_eq!(get(&j,field).value, get(&again,field).value); }
        }
    }
}

#[test]
fn finite_and_numeric_parameters_keep_observed_products() {
    let dir=files("finite-numeric-product","law required zero(c:Part,n:Z,b:Bool) when b:n*c.quantity=0;",false);
    let r=asks(&dir,&["a=build(R,on=@v/root)","p=check(R.zero,on=$a.object,c=@v/p)","q=check(R.zero,on=$a.object,c=@v/q)"]);
    let j=saved(&dir,&r,"complete",1);
    assert_eq!(s(get(answer(&j,"p"),"status")),"established");
    assert_eq!(s(get(answer(&j,"q"),"status")),"refuted");
}

#[test]
fn boolean_cases_keep_numeric_products_applicability_and_reuse() {
    for ty in ["Z", "Q"] {
        for guard in ["b", "enabled(b)"] {
            let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
            let body = format!("view enabled(x:Bool):Bool=not x;view off():Bool=false;view on():Bool=true;law required zero(c:Part,n:{ty},b:Bool) when {guard}:n*c.quantity=0;");
            let dir = files_with_definition("boolean-product-reuse", &body, false, &definition);
            if ty == "Q" {
                let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#""value":"0""#, r#""value":["0","1"]"#).replace(r#""value":"1""#, r#""value":["1","2"]"#);
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let requests = ["a=build(R,on=@v/root)", "f=evaluate(R.off,on=$a.object)", "t=evaluate(R.on,on=$a.object)",
                "p=check(R.zero,on=$a.object,c=@v/p)", "q=check(R.zero,on=$a.object,c=@v/q)",
                "off=check(R.zero,on=$a.object,c=@v/q,b=$f.value)", "on=check(R.zero,on=$a.object,c=@v/q,b=$t.value)"];
            let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
            for request in requests { args.extend(["--ask", request]); }
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, 1, "{ty}/{guard}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            assert!(!has(&normal.receipt, "nodes"));
            eprintln!("finite product {ty}/{guard}: stdout {} bytes", normal.stdout.len());
            let r = asks(&dir, &requests);
            let j = saved(&dir, &r, "complete", 1);
            assert_eq!(s(get(answer(&j,"p"),"status")), "established");
            assert_eq!(s(get(answer(&j,"q"),"status")), "refuted");
            let inactive = if guard == "b" { "off" } else { "on" };
            let active = if guard == "b" { "on" } else { "off" };
            assert_eq!(s(get(answer(&j,inactive),"status")), "established");
            assert_eq!(s(get(answer(&j,inactive),"applicability")), "not_applicable");
            assert_eq!(s(get(answer(&j,active),"status")), "refuted");
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, 1, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for field in ["answers", "nodes"] { assert_eq!(get(&j,field).value, get(&again,field).value); }
        }
    }
}

#[test]
fn boolean_cases_keep_laws_after_numeric_parameter_cancellation() {
    for ty in ["Z", "Q"] { for offset in [0, 1] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let body = format!("view off():Bool=false;law required balanced(c:Part,n:{ty},b:Bool) when b:n*c.quantity=n*c.quantity+{offset};");
        let dir = files_with_definition("finite-cancelled-parameter", &body, false, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#""value":"0""#, r#""value":["0","1"]"#).replace(r#""value":"1""#, r#""value":["1","2"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = ["a=build(R,on=@v/root)", "f=evaluate(R.off,on=$a.object)", "c=check(R.balanced,on=$a.object,c=@v/q)", "off=check(R.balanced,on=$a.object,c=@v/q,b=$f.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, offset, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert!(!has(&normal.receipt, "nodes"));
        eprintln!("cancelled finite product {ty}/{offset}: stdout {} bytes", normal.stdout.len());
        let r = asks(&dir, &requests);
        let j = saved(&dir, &r, "complete", offset);
        assert_eq!(s(get(answer(&j,"c"),"status")), if offset == 0 { "established" } else { "refuted" });
        assert_eq!(s(get(answer(&j,"off"),"status")), "established");
        assert_eq!(s(get(answer(&j,"off"),"applicability")), "not_applicable");
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, offset, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&j,field).value, get(&again,field).value); }
    }}
}

#[test]
fn finite_field_cases_keep_numeric_parameter_laws() {
    let dir = files("finite-field-parameter", "law required zero(c:Part,n:Z,k:Fp(2)) when k=0:n*c.quantity=0;", false);
    let r = asks(&dir, &["a=build(R,on=@v/root)", "p=check(R.zero,on=$a.object,c=@v/p)", "q=check(R.zero,on=$a.object,c=@v/q)"]);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(s(get(answer(&j,"p"),"status")), "established");
    assert_eq!(s(get(answer(&j,"q"),"status")), "refuted");
}

#[test]
fn finite_field_guards_keep_numeric_products_and_explicit_reuse() {
    for ty in ["Z", "Q"] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let body = format!("view off():Fp(3)=0;view on():Fp(3)=2;view active(k:Fp(3)):Bool=k+1=0;law required zero(c:Part,n:{ty},k:Fp(3)) when active(k):n*c.quantity=0;");
        let dir = files_with_definition("finite-field-product-reuse", &body, false, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#""value":"0""#, r#""value":["0","1"]"#).replace(r#""value":"1""#, r#""value":["1","2"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = ["a=build(R,on=@v/root)", "f=evaluate(R.off,on=$a.object)", "t=evaluate(R.on,on=$a.object)",
            "p=check(R.zero,on=$a.object,c=@v/p)", "q=check(R.zero,on=$a.object,c=@v/q)",
            "off=check(R.zero,on=$a.object,c=@v/q,k=$f.value)", "on=check(R.zero,on=$a.object,c=@v/q,k=$t.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert!(!has(&normal.receipt, "nodes"));
        eprintln!("finite field product {ty}: stdout {} bytes", normal.stdout.len());
        let r = asks(&dir, &requests);
        let j = saved(&dir, &r, "complete", 1);
        for (id, status) in [("p", "established"), ("q", "refuted"), ("off", "established"), ("on", "refuted")] {
            assert_eq!(s(get(answer(&j,id),"status")), status);
        }
        assert_eq!(s(get(answer(&j,"off"),"applicability")), "not_applicable");
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 1, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&j,field).value, get(&again,field).value); }
    }
}

#[test]
fn finite_tuple_cases_keep_numeric_parameter_laws() {
    let dir = files("finite-tuple-parameter", "law required zero(c:Part,n:Z,tag:(Fp(3),Bool)) when tag.1 and tag.0+1=0:n*c.quantity=0;", false);
    let r = asks(&dir, &["a=build(R,on=@v/root)", "p=check(R.zero,on=$a.object,c=@v/p)", "q=check(R.zero,on=$a.object,c=@v/q)"]);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(s(get(answer(&j,"p"),"status")), "established");
    assert_eq!(s(get(answer(&j,"q"),"status")), "refuted");
}

#[test]
fn finite_tuple_guards_keep_numeric_products_and_explicit_reuse() {
    for ty in ["Z", "Q"] {
        let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
        let body = format!("view off():(Fp(3),Bool)=(0,false);view on():(Fp(3),Bool)=(2,true);view active(tag:(Fp(3),Bool)):Bool=tag.1 and tag.0+1=0;law required zero(c:Part,n:{ty},tag:(Fp(3),Bool)) when active(tag):n*c.quantity=0;");
        let dir = files_with_definition("finite-tuple-product-reuse", &body, false, &definition);
        if ty == "Q" {
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#""value":"0""#, r#""value":["0","1"]"#).replace(r#""value":"1""#, r#""value":["1","2"]"#);
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let requests = ["a=build(R,on=@v/root)", "f=evaluate(R.off,on=$a.object)", "t=evaluate(R.on,on=$a.object)",
            "p=check(R.zero,on=$a.object,c=@v/p)", "q=check(R.zero,on=$a.object,c=@v/q)",
            "off=check(R.zero,on=$a.object,c=@v/q,tag=$f.value)", "on=check(R.zero,on=$a.object,c=@v/q,tag=$t.value)"];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        assert!(!has(&normal.receipt, "nodes"));
        eprintln!("finite tuple product {ty}: stdout {} bytes", normal.stdout.len());
        let r = asks(&dir, &requests);
        let j = saved(&dir, &r, "complete", 1);
        for (id, status) in [("p", "established"), ("q", "refuted"), ("off", "established"), ("on", "refuted")] { assert_eq!(s(get(answer(&j,id),"status")), status); }
        assert_eq!(s(get(answer(&j,"off"),"applicability")), "not_applicable");
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 1, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for field in ["answers", "nodes"] { assert_eq!(get(&j,field).value, get(&again,field).value); }
    }
}

#[test]
fn numeric_tuple_view_families_build_evaluate_and_reuse() {
    for ty in ["Z", "Q"] {
        for nested in [false, true] {
            for finite in [false, true] {
                let pair_ty = if nested {
                    format!("({ty},({ty},{ty}))")
                } else {
                    format!("({ty},{ty})")
                };
                let last = if nested { "pair.1.1" } else { "pair.1" };
                let seed = match (ty, nested) {
                    ("Q", true) => "(rat(1,2),(1,rat(3,2)))",
                    ("Q", false) => "(rat(1,2),rat(3,2))",
                    (_, true) => "(1,(2,3))",
                    _ => "(1,3)",
                };
                let extra = if finite { ",take:Bool" } else { "" };
                let body = if finite {
                    format!("if take then pair.0+{last} else {last}-pair.0")
                } else {
                    format!("pair.0+{last}")
                };
                let dir = files(&format!("numeric-tuple-view-{ty}-{nested}-{finite}"), &format!(
                    "law required balanced(c:Part):c.quantity=c.quantity;view combine(c:Part,pair:{pair_ty}{extra}):({ty},Z)=({body},c.quantity);view seed():{pair_ty}={seed};view yes():Bool=true;view no():Bool=false;"
                ), false);
                let request = if finite {
                    "v=evaluate(R.combine,on=$b.object,c=@v/q,pair=$s.value,take=$yes.value)"
                } else {
                    "v=evaluate(R.combine,on=$b.object,c=@v/q,pair=$s.value)"
                };
                let other = if finite {
                    "w=evaluate(R.combine,on=$b.object,c=@v/p,pair=$s.value,take=$no.value)"
                } else {
                    "w=evaluate(R.combine,on=$b.object,c=@v/p,pair=$s.value)"
                };
                let requests = [
                    "b=build(R,on=@v/root)",
                    "s=evaluate(R.seed,on=$b.object)",
                    "yes=evaluate(R.yes,on=$b.object)",
                    "no=evaluate(R.no,on=$b.object)",
                    request,
                    other,
                ];
                let mut args = vec![
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                ];
                for request in requests {
                    args.extend(["--ask", request]);
                }
                let before = ["d.json", "l.law", "a.json"]
                    .map(|name| std::fs::read(dir.join(name)).unwrap());
                let normal = cli::run(&dir, &args);
                assert_eq!(normal.code, 0, "{ty}/{nested}/{finite}: {}", normal.stdout);
                assert!(normal.stderr.is_empty());
                assert!(!has(&normal.receipt, "nodes") && !has(&normal.receipt, "result"));
                assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
                for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
                    assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
                }
                let run = asks(&dir, &requests);
                let result = saved(&dir, &run, "complete", 0);
                assert!(has(get(answer(&result, "b"), "outputs"), "object"));
                assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
                let expected = if ty == "Q" {
                    r#"[["2","1"],"1"]"#
                } else {
                    r#"["4","1"]"#
                };
                assert_eq!(
                    value(&result, get(get(answer(&result, "v"), "outputs"), "value")).value,
                    archsig::json::parse(expected.as_bytes()).unwrap().value
                );
                let expected = match (ty, finite) {
                    ("Q", true) => r#"[["1","1"],"0"]"#,
                    ("Q", false) => r#"[["2","1"],"0"]"#,
                    (_, true) => r#"["2","0"]"#,
                    _ => r#"["4","0"]"#,
                };
                assert_eq!(
                    value(&result, get(get(answer(&result, "w"), "outputs"), "value")).value,
                    archsig::json::parse(expected.as_bytes()).unwrap().value
                );
                args.extend(["--out", "again", "--reuse", "out"]);
                let reused = cli::run(&dir, &args);
                let again = saved(&dir, &reused, "complete", 0);
                assert!(warnings(&again).is_empty());
                for field in ["answers", "nodes"] {
                    assert_eq!(get(&again, field).value, get(&result, field).value);
                }
            }
        }
    }
}

#[test]
fn numeric_tuple_view_families_keep_missing_observations() {
    let dir = files("numeric-tuple-view-missing", "law required balanced(c:Part):true;view combine(c:Part,pair:(Z,(Z,Z)),take:Bool):(Z,Z)=(if take then pair.0+pair.1.1 else pair.1.1-pair.0,c.quantity);view seed():(Z,(Z,Z))=(1,(2,3));view enabled():Bool=true;", true);
    let requests = [
        "b=build(R,on=@v/root)",
        "s=evaluate(R.seed,on=$b.object)",
        "e=evaluate(R.enabled,on=$b.object)",
        "v=evaluate(R.combine,on=$b.object,c=@v/q,pair=$s.value,take=$e.value)",
        "n=needed($v)",
    ];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "partial", 2);
    assert!(has(get(answer(&result, "b"), "outputs"), "object"));
    let v = answer(&result, "v");
    assert_eq!(s(get(v, "status")), "undetermined");
    assert!(!has(get(v, "outputs"), "value"));
    assert!(!has(v, "counterexamples"));
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).iter().any(|r| {
        let field = get(r, "field");
        s(get(field, "subject")) == "q" && s(get(field, "field")) == "Build.Part.quantity"
    }));
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
    ];
    for request in requests {
        args.extend(["--ask", request]);
    }
    let reused = cli::run(&dir, &args);
    let again = saved(&dir, &reused, "partial", 2);
    assert!(warnings(&again).is_empty());
    for field in ["answers", "nodes"] {
        assert_eq!(get(&again, field).value, get(&result, field).value);
    }
}

fn required_tuple_inputs(name: &str, ty: &str, body: &str, missing: bool) -> PathBuf {
    let definition = DEFINITION.replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#));
    let dir = files_with_definition(name, body, missing, &definition);
    if ty == "Q" {
        let map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(r#""value":"0""#, r#""value":["0","1"]"#)
            .replace(r#""value":"1""#, r#""value":["1","2"]"#);
        std::fs::write(dir.join("a.json"), map).unwrap();
    }
    dir
}
fn required_tuple_law_case(ty: &str, case: &str) {
    let nested = !case.ends_with("flat") && case != "observed";
    let shape = if nested {
        format!("({ty},({ty},{ty}))")
    } else {
        format!("({ty},{ty})")
    };
    let a = "pair.0";
    let z = if nested { "pair.1.1" } else { "pair.1" };
    let expression = match case {
        "held-flat" | "held-nested" => format!("{a}+last+more.1={a}+last+more.1"),
        "later" => "last=more.1".to_owned(),
        "finite" => format!("(if take then {a} else {z})={z}"),
        "empty" => "c.quantity=100".to_owned(),
        "missing" | "observed" => format!("{a}+c.quantity={a}"),
        "unknown" => format!("{a}*{z}=1"),
        "helper" => format!("tail(pair)={a}"),
        _ => format!("{a}={z}"),
    };
    let guard = if case == "empty" {
        format!(" when {a}+1={a}")
    } else {
        String::new()
    };
    let finite = if case == "finite" { "take:Bool," } else { "" };
    let helper = if case == "helper" {
        format!(
            "view tail(p:{shape}):{ty}={};",
            if nested { "p.1.1" } else { "p.1" }
        )
    } else {
        String::new()
    };
    let signature = if case == "observed" {
        format!("pair:{shape},c:Part")
    } else {
        format!("{finite}pair:{shape},c:Part,last:{ty},more:({ty},{ty})")
    };
    let body = format!("{helper}law required balanced({signature}){guard}:{expression};");
    let missing = case == "missing";
    let dir = required_tuple_inputs(&format!("required-tuple-{ty}-{case}"), ty, &body, missing);
    let code = match case {
        "held-flat" | "held-nested" | "empty" => 0,
        "missing" | "unknown" => 2,
        _ => 1,
    };
    let mut requests = vec![
        "b=build(R,on=@v/root)",
        "c=check(R.balanced,on=$b.object,c=@v/q)",
    ];
    if case != "observed" {
        requests.push("n=needed($c)");
    }
    if case == "missing" {
        requests.push("p=check(R.balanced,on=$b.object,c=@v/p)");
    }
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
    ];
    for request in &requests {
        args.extend(["--ask", *request]);
    }
    let before = ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
    let normal = cli::run(&dir, &args);
    assert_eq!(
        normal.code, code,
        "{ty}/{case}: {} {}",
        normal.stdout, normal.stderr
    );
    assert!(normal.stderr.is_empty());
    assert!(!has(&normal.receipt, "nodes") && !has(&normal.receipt, "result"));
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
        assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
    }
    let run = asks(&dir, &requests);
    let result = saved(
        &dir,
        &run,
        if code == 2 { "partial" } else { "complete" },
        code,
    );
    assert!(has(get(answer(&result, "b"), "outputs"), "object"));
    let checked = answer(&result, "c");
    assert_eq!(
        s(get(checked, "status")),
        match code {
            0 => "established",
            1 => "refuted",
            _ => "undetermined",
        }
    );
    if case == "empty" {
        assert_eq!(s(get(checked, "applicability")), "not_applicable");
    }
    if code == 1 {
        let examples = arr(get(checked, "counterexamples"));
        assert!(!examples.is_empty());
        for example in examples {
            let data = get(value(&result, example), "data");
            let bindings = arr(get(data, "bindings"));
            let names: Vec<_> = bindings.iter().map(|b| s(get(b, "name"))).collect();
            assert_eq!(
                names,
                if case == "finite" {
                    vec!["take", "pair", "c", "last", "more"]
                } else if case == "observed" {
                    vec!["pair", "c"]
                } else {
                    vec!["pair", "c", "last", "more"]
                }
            );
            let binding = |name: &str| {
                value(
                    &result,
                    get(
                        bindings.iter().find(|b| s(get(b, "name")) == name).unwrap(),
                        "value",
                    ),
                )
            };
            let pair = arr(binding("pair"));
            assert_eq!(pair.len(), 2);
            let end = if nested {
                assert_eq!(arr(&pair[1]).len(), 2);
                &arr(&pair[1])[1]
            } else {
                &pair[1]
            };
            if case != "observed" {
                let more = arr(binding("more"));
                assert_eq!(more.len(), 2);
                if case == "later" {
                    assert_ne!(binding("last").value, more[1].value);
                } else {
                    assert_ne!(pair[0].value, end.value);
                }
            }
            if case == "finite" {
                assert_eq!(
                    binding("take").value,
                    archsig::json::parse(b"true").unwrap().value
                );
            }
            let left = value(&result, get(value(&result, get(data, "left")), "value"));
            let right = value(&result, get(value(&result, get(data, "right")), "value"));
            assert_ne!(left.value, right.value);
            if case == "observed" {
                if ty == "Z" {
                    assert_eq!(
                        s(left).parse::<i128>().unwrap() - s(right).parse::<i128>().unwrap(),
                        1
                    );
                } else {
                    let l = arr(left);
                    let r = arr(right);
                    let ln = s(&l[0]).parse::<i128>().unwrap();
                    let ld = s(&l[1]).parse::<i128>().unwrap();
                    let rn = s(&r[0]).parse::<i128>().unwrap();
                    let rd = s(&r[1]).parse::<i128>().unwrap();
                    assert_eq!((ln * rd - rn * ld) * 2, ld * rd);
                }
            }
        }
    } else if case == "missing" {
        let examples = arr(get(checked, "counterexamples"));
        assert!(!examples.is_empty());
        for example in examples {
            let pair = value(&result, example);
            assert_eq!(s(get(pair, "kind")), "completion_pair");
            let data = get(pair, "data");
            let first = value(
                &result,
                get(value(&result, get(data, "first_result")), "value"),
            );
            let second = value(
                &result,
                get(value(&result, get(data, "second_result")), "value"),
            );
            assert_ne!(first.value, second.value);
            assert!(arr(get(data, "fields")).iter().any(
                |f| s(get(f, "subject")) == "q" && s(get(f, "field")) == "Build.Part.quantity"
            ));
        }
    } else {
        assert!(!has(checked, "counterexamples"));
    }
    if case == "missing" {
        assert_eq!(s(get(answer(&result, "p"), "status")), "established");
    }
    if case != "observed" {
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        if case == "missing" {
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "subject")) == "q" && s(get(field, "field")) == "Build.Part.quantity"
            }));
        } else if case == "empty" {
            assert!(arr(get(plan, "requirements")).is_empty());
        } else if case == "unknown" {
            assert!(!arr(get(plan, "blockers")).is_empty());
        }
    }
    args.extend(["--out", "again", "--reuse", "out"]);
    let reused = cli::run(&dir, &args);
    let again = saved(
        &dir,
        &reused,
        if code == 2 { "partial" } else { "complete" },
        code,
    );
    assert!(warnings(&again).is_empty());
    for key in ["answers", "nodes"] {
        assert_eq!(
            get(&result, key).value,
            get(&again, key).value,
            "{ty}/{case}/{key}"
        );
    }
}

#[test]
fn required_numeric_tuple_laws_build_and_check() {
    for ty in ["Z", "Q"] {
        for case in [
            "held-flat",
            "held-nested",
            "refuted-flat",
            "refuted-nested",
            "later",
        ] {
            required_tuple_law_case(ty, case);
        }
    }
}

#[test]
fn required_numeric_tuple_finite_arguments() {
    for ty in ["Z", "Q"] {
        required_tuple_law_case(ty, "finite");
    }
}

#[test]
fn required_numeric_tuple_empty_domains() {
    for ty in ["Z", "Q"] {
        required_tuple_law_case(ty, "empty");
    }
}

#[test]
fn required_numeric_tuple_missing_observations() {
    for ty in ["Z", "Q"] {
        required_tuple_law_case(ty, "missing");
    }
}

#[test]
fn required_numeric_tuple_unknown_nonlinear() {
    for ty in ["Z", "Q"] {
        required_tuple_law_case(ty, "unknown");
    }
}

#[test]
fn required_numeric_tuple_helper_arguments() {
    for ty in ["Z", "Q"] {
        required_tuple_law_case(ty, "helper");
    }
}

#[test]
fn required_numeric_tuple_empty_guard_skips_unobserved_body() {
    for ty in ["Z", "Q"] {
        let body=format!("law required balanced(pair:({ty},({ty},{ty})),c:Part) when pair.0+1=pair.0:c.quantity=100;");
        let dir = required_tuple_inputs(
            &format!("required-tuple-empty-direct-{ty}"),
            ty,
            &body,
            true,
        );
        let requests = ["c=check(R.balanced,c=@v/q)", "n=needed($c)"];
        let run = asks(&dir, &requests);
        let result = saved(&dir, &run, "complete", 0);
        let checked = answer(&result, "c");
        assert_eq!(s(get(checked, "status")), "established");
        assert_eq!(s(get(checked, "applicability")), "not_applicable");
        assert!(!has(checked, "counterexamples"));
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        let args = [
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            requests[0],
            "--ask",
            requests[1],
            "--out",
            "again",
            "--reuse",
            "out",
        ];
        let reused = cli::run(&dir, &args);
        let again = saved(&dir, &reused, "complete", 0);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(get(&again, key).value, get(&result, key).value);
        }
    }
}

#[test]
fn required_numeric_tuple_observed_zero_and_fraction() {
    for ty in ["Z", "Q"] {
        required_tuple_law_case(ty, "observed");
    }
}
