//! 公開buildから後続の実評価までを、独立した三入力で検査する。
use crate::common::cli;
use archsig_common::json::JNode;
use cli::*;
use std::path::{Path, PathBuf};

const DEFINITION: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Build","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Build.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Build.Part","meaning":"部分。","parameters":[{"name":"owner","type":["Ref","Build.Root"],"meaning":"所属。"}],"fields":[{"name":"quantity","type":"Z","meaning":"数量。"}],"alignments":[]}]}]}"#;
const BODY: &str = "view amount(c:Part):Z=c.quantity;law required zero(c:Part):c.quantity=0;";
#[test]
fn partial_data_known_component_selects_checked_arm() {
    let definition = numeric_data_definition("Z").replace(r#""meaning":"数量。"}"#, r#""meaning":"数量。"},{"name":"payload","type":["Data","Build.Payload"],"meaning":"未観測の包装。"}"#)
        .replace(r#""declarations":["#, r#""declarations":[{"kind":"data","name":"Build.Flag","meaning":"選択。","constructors":[{"name":"Off","arguments":[],"meaning":"偽。"},{"name":"On","arguments":[],"meaning":"真。"}]},{"kind":"data","name":"Build.Pair","meaning":"包装と選択。","constructors":[{"name":"Join","arguments":[["Data","Build.Payload"],["Data","Build.Flag"]],"meaning":"組。"}]},"#);
    let dir = files_with_definition(
        "partial-data-arm",
        "law required short(c:Part):match Pair.Join(c.payload,Flag.Off){Join(Packed(_),On)=>false;_=>true;};law required uncertain(c:Part):match c.payload{Empty=>true;Packed(x)=>x=0;};",
        false,
        &definition,
    );
    let requests = [
        "b=check(R.short,c=@v/q)",
        "u=check(R.uncertain,c=@v/q)",
        "n=needed($u)",
    ];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "partial", 2);
    assert_eq!(s(get(answer(&result, "b"), "status")), "established");
    assert_eq!(s(get(answer(&result, "u"), "status")), "undetermined");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(
        arr(get(plan, "requirements"))
            .iter()
            .any(|r| s(get(get(r, "field"), "field")) == "Build.Part.payload")
    );
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace("Flag.Off", "Flag.On");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "changed",
        "--reuse",
        "out",
    ];
    for request in requests {
        args.extend(["--ask", request]);
    }
    let changed = cli::run(&dir, &args);
    let changed = saved(&dir, &changed, "partial", 2);
    assert_eq!(s(get(answer(&changed, "b"), "status")), "undetermined");
}
fn numeric_data_definition(ty: &str) -> String {
    DEFINITION.replace(r#""declarations":["#, &format!(r#""declarations":[{{"kind":"data","name":"Build.Payload","meaning":"数値を包む。","constructors":[{{"name":"Empty","arguments":[],"meaning":"空。"}},{{"name":"Packed","arguments":["{ty}"],"meaning":"数値。"}}]}},{{"kind":"data","name":"Build.Wrapper","meaning":"包装。","constructors":[{{"name":"Wrapped","arguments":[["Data","Build.Payload"]],"meaning":"包装。"}}]}},"#))
        .replace(r#""type":"Z""#, &format!(r#""type":"{ty}""#))
}
// 恒真のguardの記号的な判定。恒偽の側(空listのcount・自己との順序・list・helper)は
// inactive_constant_false_guards_keep_missing_body_outside_applicability の鎖で見る。
#[test]
fn logical_connective_guards_preserve_numeric_products() {
    // 前件が定数のimplies、and、右辺が定数のorの腕。
    known_numeric_product(
        "connectives",
        DEFINITION,
        "",
        "(false implies n*n=1) and n=n and (n=0 or true)",
        "n*c.quantity",
    );
}
#[test]
fn constant_order_guards_preserve_numeric_products() {
    // parameterどうしの定数差の順序比較。
    known_numeric_product("order-lt", DEFINITION, "", "n<n+1", "n*c.quantity");
}
#[test]
fn container_inequality_guards_preserve_numeric_products() {
    // option構成子の違いと、Textを含むtupleの記号的な不等。
    known_numeric_product(
        "containers",
        DEFINITION,
        "",
        r#"some(n)!=none<Z> and (n,"ready")!=(n,"done")"#,
        "n*c.quantity",
    );
}
#[test]
fn list_sum_guard_preserves_numeric_products() {
    // 明示listのsum(Zの相殺とQの和)。
    known_numeric_product(
        "symbolic-list-sum",
        DEFINITION,
        "",
        "sum(list<Z>[n,-n])=0 and sum(list<Q>[rat(1,2),rat(1,2)])=1",
        "n*c.quantity",
    );
}
#[test]
fn explicit_list_count_uses_shape_with_numeric_parameters() {
    // 要素に数値parameterを含む明示listのcountは、値でなく形(要素数)で決まる。
    known_numeric_product(
        "symbolic-list-count",
        DEFINITION,
        "",
        "count(list<Z>[n,n])=2",
        "n*c.quantity",
    );
}
#[test]
fn known_data_payload_match_preserves_numeric_products() {
    // data構成子をhelperのmatchで取り出した係数。
    let definition = numeric_data_definition("Z");
    known_numeric_product(
        "data-helper",
        &definition,
        "view unpack(p:Payload):Z=match p{Empty=>0;Packed(x)=>x;};",
        "",
        "unpack(Payload.Packed(n))*c.quantity",
    );
}
fn known_numeric_product(name: &str, definition: &str, helpers: &str, guard: &str, product: &str) {
    let when = if guard.is_empty() {
        String::new()
    } else {
        format!(" when {guard}")
    };
    let body = format!("{helpers}law required zero(c:Part,n:Z){when}:{product}=0;");
    let dir = files_with_definition(&format!("known-product-{name}"), &body, false, definition);
    let requests = [
        "a=build(R,on=@v/root)",
        "p=check(R.zero,on=$a.object,c=@v/p)",
        "q=check(R.zero,on=$a.object,c=@v/q)",
    ];
    let r = asks(&dir, &requests);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(s(get(answer(&j, "p"), "status")), "established", "{name}");
    assert_eq!(s(get(answer(&j, "q"), "status")), "refuted", "{name}");
}
#[test]
fn observed_parameter_products_keep_rational_coefficients() {
    // 未束縛parameterと観測値のhelperを通した積。直接の積は上のguardの試験が通る。
    let body =
        "view product(x:Z,y:Z):Z=x*y;law required zero(c:Part,n:Z,m:Z):product(n,c.quantity)=0;";
    let dir = files("products-reuse", body, false);
    let requests = [
        "b=build(R,on=@v/root)",
        "p=check(R.zero,on=$b.object,c=@v/p)",
        "q=check(R.zero,on=$b.object,c=@v/q)",
    ];
    let r = asks(&dir, &requests);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(s(get(answer(&j, "p"), "status")), "established");
    assert_eq!(s(get(answer(&j, "q"), "status")), "refuted");
}
#[test]
fn boolean_parameter_guard_keeps_numeric_products_and_applicability() {
    // 有限parameterの行ごとの適用性。有限型の扱いは型によらず同じ経路なのでBoolで見る。
    let body = "view off():Bool=false;view on():Bool=true;law required zero(c:Part,n:Z,b:Bool) when b:n*c.quantity=0;";
    let dir = files("boolean-product-reuse", body, false);
    let requests = [
        "a=build(R,on=@v/root)",
        "f=evaluate(R.off,on=$a.object)",
        "t=evaluate(R.on,on=$a.object)",
        "p=check(R.zero,on=$a.object,c=@v/p)",
        "q=check(R.zero,on=$a.object,c=@v/q)",
        "off=check(R.zero,on=$a.object,c=@v/q,b=$f.value)",
        "on=check(R.zero,on=$a.object,c=@v/q,b=$t.value)",
    ];
    let r = asks(&dir, &requests);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(s(get(answer(&j, "p"), "status")), "established");
    assert_eq!(s(get(answer(&j, "q"), "status")), "refuted");
    assert_eq!(s(get(answer(&j, "off"), "status")), "established");
    assert_eq!(s(get(answer(&j, "off"), "applicability")), "not_applicable");
    assert_eq!(s(get(answer(&j, "on"), "status")), "refuted");
}
#[test]
fn active_parameter_product_keeps_missing_observation_undetermined() {
    // 恒真guardでも本体が欠測を読めば、buildとqは未決。pは観測どおり成立。
    let body = "law required zero(c:Part,n:Z) when true:n*c.quantity=0;";
    let dir = files("active-product-true", body, true);
    let requests = [
        "b=build(R,on=@v/root)",
        "p=check(R.zero,on=$b.object,c=@v/p)",
        "q=check(R.zero,on=$b.object,c=@v/q)",
        "n=needed($b)",
    ];
    let r = asks(&dir, &requests);
    let j = saved(&dir, &r, "partial", 2);
    for id in ["b", "q"] {
        let answer = answer(&j, id);
        assert_eq!(s(get(answer, "status")), "undetermined");
        let reasons = arr(get(answer, "reasons"));
        assert!(!reasons.is_empty());
        assert!(
            reasons
                .iter()
                .all(|r| s(get(r, "code")) == "missing_observation")
        );
    }
    assert_eq!(s(get(answer(&j, "p"), "status")), "established");
    assert!(has(get(answer(&j, "b"), "outputs"), "object"));
    assert!(!has(get(answer(&j, "b"), "outputs"), "algebra"));
    let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
    assert!(
        arr(get(plan, "requirements"))
            .iter()
            .any(
                |r| s(get(get(r, "field"), "field")) == "Build.Part.quantity"
                    && s(get(get(r, "field"), "subject")) == "q"
            )
    );
}
#[test]
fn correlated_missing_products_decide_constant_differences() {
    let body =
        "view amount(c:Part):Z=c.quantity;law required zero(c:Part,n:Z):n*c.quantity=c.quantity*n;";
    let dir = files("correlated-missing-product", body, true);
    let requests = [
        "a=build(R,on=@v/root)",
        "q=check(R.zero,on=$a.object,c=@v/q)",
        "v=evaluate(R.amount,on=$a.object,c=@v/q)",
        "n=needed($v)",
    ];
    let r = asks(&dir, &requests);
    let j = saved(&dir, &r, "partial", 2);
    // 同じ未観測slotの積は相殺し、どの補完でも成立する。値そのものは未決のまま。
    assert_eq!(s(get(answer(&j, "q"), "status")), "established");
    assert_eq!(s(get(answer(&j, "v"), "status")), "undetermined");
    assert!(!has(get(answer(&j, "v"), "outputs"), "value"));
    assert_eq!(
        s(get(get(answer(&j, "q"), "scope"), "domain")),
        "all_completions"
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
}
#[test]
fn different_missing_product_slots_remain_independent() {
    let body = "law required equal(c:Part,d:Part,n:Z):n*c.quantity=n*d.quantity;";
    let dir = files("independent-missing-product", body, true);
    let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#",{"id":"xp","subject":"p","field":"Build.Part.quantity","value":"0","origin":"model"}"#,"").replace("p=0、q=1。", "pとqの数量は未観測。");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let r = asks(
        &dir,
        &[
            "a=build(R,on=@v/root)",
            "same=check(R.equal,on=$a.object,c=@v/q,d=@v/q)",
            "different=check(R.equal,on=$a.object,c=@v/p,d=@v/q)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    assert_eq!(s(get(answer(&j, "same"), "status")), "established");
    assert_eq!(s(get(answer(&j, "different"), "status")), "undetermined");
    let reasons = arr(get(answer(&j, "different"), "reasons"));
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
#[test]
fn missing_coefficient_does_not_hide_unsupported_integer_existential() {
    let dir = files(
        "existential-product-missing",
        "law required zero(c:Part):exists n:Z.n*n=c.quantity;",
        true,
    );
    let r = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "q=check(R.zero,on=$b.object,c=@v/q)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    for id in ["b", "q"] {
        let reasons = arr(get(answer(&j, id), "reasons"));
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
fn inactive_constant_false_guards_keep_missing_body_outside_applicability() {
    inactive_parameter_product_keeps_missing_body_outside_applicability(0);
}
#[test]
fn inactive_guard_keeps_the_same_missing_value_undetermined_in_a_view() {
    inactive_parameter_product_keeps_missing_body_outside_applicability(1);
}
#[test]
fn inactive_guard_reading_a_missing_slot_keeps_the_build_partial() {
    inactive_parameter_product_keeps_missing_body_outside_applicability(2);
}
fn inactive_parameter_product_keeps_missing_body_outside_applicability(row: usize) {
    // 恒偽のguardを並べる。どれか一つでも偽と決まらなければ、適用外が反証か未決へ変わる。
    // sum・option・tupleの記号的な判定は恒真の側(known_numeric_product)で見る。
    let chain = "false or inactive(n) or (count(list<Bool>[])>0) or (n<n) or (list<Z>[n,n+1]=list<Z>[n+1,n])";
    // (guard, guardが欠測slotを読むか, 同じ欠測値をviewで求めるか)
    let (guard, guard_reads, read_missing) = [
        (chain, false, false),
        ("false", false, true),
        ("c.quantity+1<=c.quantity", true, false),
    ][row];
    let view = if read_missing {
        "view amount(c:Part):Z=c.quantity;"
    } else {
        ""
    };
    let body = format!(
        "view inactive(n:Z):Bool=n+1=n;{view}law required zero(c:Part,n:Z) when {guard}:n*c.quantity=0;"
    );
    let dir = files(
        &format!("inactive-product-{guard_reads}-{read_missing}"),
        &body,
        true,
    );
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
}
#[test]
fn predicate_helper_guards_keep_missing_reads_separate_from_constant_truth() {
    let dir = files(
        "predicate-guard-missing",
        "view active(x:Z,y:Z):Bool=x=x;view zero():Z=0;view one():Z=1;law required equal(c:Part,n:Z) when active(n,c.quantity):n=0;",
        true,
    );
    let r = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "z=evaluate(R.zero,on=$b.object)",
            "o=evaluate(R.one,on=$b.object)",
            "p=check(R.equal,on=$b.object,c=@v/p,n=$z.value)",
            "q=check(R.equal,on=$b.object,c=@v/q,n=$o.value)",
            "n=needed($b)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    assert_eq!(s(get(answer(&j, "p"), "status")), "established");
    // 未観測yのどの補完でもguardは真。n=1の本体は反証できるが、読取りの欠測は残る。
    assert_eq!(s(get(answer(&j, "q"), "status")), "refuted");
    let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
    assert!(
        arr(get(plan, "requirements"))
            .iter()
            .any(|r| s(get(get(r, "field"), "field")) == "Build.Part.quantity")
    );
}
#[test]
fn parameter_predicate_helpers_keep_caller_bindings() {
    // 未束縛の数値parameterと観測の一次式。全称は反証、各束縛で成立と反証が分かれる。
    // helper内のlet nが呼出し側のnを捕獲すれば、成立と反証が入れ替わる。
    let dir = files(
        "predicate-helper-bindings",
        "view eq(x:Z,y:Z):Bool=let n=x in n=y;view flipped(m:Z,n:Z):Bool=eq(n,m);view one():Z=1;view two():Z=2;law required equal(c:Part,n:Z,m:Z):flipped(m,n+c.quantity);",
        false,
    );
    let requests = [
        "b=build(R,on=@v/root)",
        "i=evaluate(R.one,on=$b.object)",
        "j=evaluate(R.two,on=$b.object)",
        "all=check(R.equal,on=$b.object,c=@v/p)",
        "p=check(R.equal,on=$b.object,c=@v/p,n=$i.value,m=$i.value)",
        "q0=check(R.equal,on=$b.object,c=@v/q,n=$i.value,m=$i.value)",
        "q1=check(R.equal,on=$b.object,c=@v/q,n=$i.value,m=$j.value)",
    ];
    let r = asks(&dir, &requests);
    let j = saved(&dir, &r, "complete", 1);
    for (id, status) in [
        ("all", "refuted"),
        ("p", "established"),
        ("q0", "refuted"),
        ("q1", "established"),
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), status);
    }
}
#[test]
fn affine_parameter_families_feed_localization_and_diagnosis() {
    let dir = files(
        "affine-family-local",
        "law required zero(c:Part,n:Z):n+c.quantity=0; local each(c:Part) reads (c.owner,c.quantity);",
        false,
    );
    let r = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "l=localize($b.object)",
            "e=diagnose($l.system)",
            "s=diagnose($l.system,side=semantic)",
        ],
    );
    let j = saved(&dir, &r, "complete", 1);
    for id in ["e", "s"] {
        assert_eq!(s(get(answer(&j, id), "status")), "refuted", "{id}");
    }
}
#[test]
fn constant_numeric_families_build_without_samples() {
    // Zの恒等的な族は成立、Qの定数差の族は反証。同じbuildで両方を見る。
    let dir = files(
        "constant-family",
        "law required zfamily(c:Part,n:Z,m:Z):let a=n+m in a=n+m+0;law required qfamily(c:Part,n:Q,m:Q):let a=n+m in a=n+m+1;",
        false,
    );
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "z=check(R.zfamily,on=$b.object,c=@v/p)",
            "q=check(R.qfamily,on=$b.object,c=@v/p)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "z"), "status")), "established");
    assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
}
#[test]
fn parameter_families_coexist_with_closed_numeric_laws() {
    let dir = files(
        "parameter-closed",
        "law required zero(c:Part,n:Z):n=0;law required plain(c:Part):0=0;",
        false,
    );
    let requests = [
        "b=build(R,on=@v/root)",
        "q=check(R.zero,on=$b.object,c=@v/q)",
        "p=check(R.plain,on=$b.object,c=@v/p)",
    ];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "p"), "status")), "established");
}
#[test]
fn parameter_family_build_compares_identical_patterns() {
    let dir = files(
        "parameter-identical-patterns",
        "law required zero(c:Part,n:Z):n=0;",
        false,
    );
    let map = std::fs::read_to_string(dir.join("a.json")).unwrap()
        .replace(r#",{"id":"q","type":"Build.Part","origin":"model"}"#, "")
        .replace(r#",{"id":"oq","subject":"q","field":"Build.Part.owner","value":["v","root"],"origin":"model"}"#, "")
        .replace(r#",{"id":"xq","subject":"q","field":"Build.Part.quantity","value":"1","origin":"model"}"#, "");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "q=check(R.zero,on=$b.object,c=@v/p)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(s(get(answer(&result, "q"), "status")), "refuted");
}
#[test]
fn numeric_parameter_circuits_keep_pointwise_conditions() {
    // 束縛ごとの成立と反証の分かれ方は parameter_predicate_helpers_keep_caller_bindings でも見る。
    let dir = files(
        "parameter-circuit",
        "view zero():Z=0;view difference(n:Z,m:Z):Z=n-m;law required balanced(c:Part,n:Z,m:Z):2*difference(n,m)=0;",
        false,
    );
    let requests = [
        "b=build(R,on=@v/root)",
        "z=evaluate(R.zero,on=$b.object)",
        "all=check(R.balanced,on=$b.object,c=@v/q)",
        "zero=check(R.balanced,on=$b.object,c=@v/q,n=$z.value,m=$z.value)",
    ];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 1);
    for (id, status) in [("all", "refuted"), ("zero", "established")] {
        assert_eq!(s(get(answer(&result, id), "status")), status);
    }
    // Law parameterは環の新しい観測変数へ置換せず、各circuitのparameterに残す。
    let algebra = value(
        &result,
        get(get(answer(&result, "b"), "outputs"), "algebra"),
    );
    let equations = value(&result, get(algebra, "equations"));
    let base_row = &arr(get(equations, "objects"))[0];
    let presentation = value(&result, &arr(get(base_row, "presentations"))[0]);
    let ring = value(&result, get(presentation, "ring"));
    assert!(arr(get(ring, "variables")).is_empty());
    let detectors = arr(get(algebra, "circuits"));
    assert!(!detectors.is_empty());
    for detector in detectors {
        assert_eq!(arr(get(value(&result, detector), "parameters")).len(), 2);
    }
}
fn files(name: &str, body: &str, missing: bool) -> PathBuf {
    files_with_definition(name, body, missing, DEFINITION)
}
fn files_with_definition(name: &str, body: &str, missing: bool, definition: &str) -> PathBuf {
    let dir = workdir(name);
    let defs =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    let digest = &defs.vocabularies()["Build"].digest;
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
    let n = answer(&result, "n");
    assert_eq!(s(get(n, "status")), "established");
    assert_eq!(s(value(&result, get(get(n, "outputs"), "value"))), "1");
    assert_eq!(s(get(answer(&result, "ok"), "status")), "refuted");
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn missing_readings_keep_the_constructed_object_and_the_actual_needed_slot() {
    // Lawがなくても、viewの欠測はalgebraを止める。
    for (tag, body) in [("law", BODY), ("view", "view amount(c:Part):Z=c.quantity;")] {
        let dir = files(&format!("public-build-missing-{tag}"), body, true);
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
        assert_eq!(s(get(b, "status")), "undetermined", "{tag}");
        assert!(has(get(b, "outputs"), "object"));
        assert!(!has(get(b, "outputs"), "algebra"));
        let n = answer(&result, "n");
        assert_eq!(s(get(n, "status")), "undetermined");
        assert!(arr(get(n, "reasons")).iter().any(|r| {
            s(get(r, "code")) == "missing_observation"
                && arr(get(r, "missing")).iter().any(|p| {
                    s(get(p, "subject")) == "q" && s(get(p, "field")) == "Build.Part.quantity"
                })
        }));
        assert!(has(get(answer(&result, "plan"), "outputs"), "plan"));
        std::fs::remove_dir_all(dir).unwrap();
    }
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
        archsig_input::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())])
            .unwrap();
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Fp","2"]"#);
    let new =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    std::fs::write(dir.join("d.json"), definition).unwrap();
    for name in ["l.law", "a.json"] {
        let text = std::fs::read_to_string(dir.join(name)).unwrap().replace(
            &old.vocabularies()["Build"].digest,
            &new.vocabularies()["Build"].digest,
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
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
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
    assert!(!detectors.is_empty());
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
                assert!(matches!(
                    decision,
                    archsig_common::json::JValue::Bool(false)
                ));
            } else if matches!(decision, archsig_common::json::JValue::Bool(true)) {
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
        archsig_input::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())])
            .unwrap();
    let new =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    std::fs::write(dir.join("d.json"), definition).unwrap();
    for name in ["l.law", "a.json"] {
        let text = std::fs::read_to_string(dir.join(name)).unwrap().replace(
            &old.vocabularies()["Build"].digest,
            &new.vocabularies()["Build"].digest,
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
fn mixed_tuple_fields_and_lexical_aliases_preserve_each_scalar_component() {
    // let別名・helper・match束縛のLawと、非零rationalの正確な比較のLawを同じbuildで見る。
    // 観測は p=(0,1/2)、q=(1,1/2)。
    let body = "view passPair(x:(Z,Q)):(Z,Q)=match x {n=>n;};view amount(c:Part):Z=c.quantity.0;law required aliased(c:Part):let x=c.quantity in passPair(x)=(0,rat(1,2));law required fraction(c:Part):c.quantity=(0,rat(1,2));";
    let dir = files("public-build-mixed-tuple", body, false);
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Tuple","Z","Q"]"#);
    let old =
        archsig_input::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())])
            .unwrap();
    let new =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    std::fs::write(dir.join("d.json"), definition).unwrap();
    for name in ["l.law", "a.json"] {
        let text = std::fs::read_to_string(dir.join(name))
            .unwrap()
            .replace(
                &old.vocabularies()["Build"].digest,
                &new.vocabularies()["Build"].digest,
            )
            .replace(r#""value":"0""#, r#""value":["0",["1","2"]]"#)
            .replace(r#""value":"1""#, r#""value":["1",["1","2"]]"#);
        std::fs::write(dir.join(name), text).unwrap();
    }
    let run = asks(
        &dir,
        &[
            "b=build(R,on=@v/root)",
            "n=evaluate(R.amount,on=$b.object,c=@v/q)",
            "badaliased=check(R.aliased,on=$b.object,c=@v/q)",
            "goodaliased=check(R.aliased,on=$b.object,c=@v/p)",
            "badfraction=check(R.fraction,on=$b.object,c=@v/q)",
            "goodfraction=check(R.fraction,on=$b.object,c=@v/p)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    assert_eq!(s(get(answer(&result, "b"), "status")), "established");
    for law in ["aliased", "fraction"] {
        assert_eq!(
            s(get(answer(&result, &format!("bad{law}")), "status")),
            "refuted",
            "{law}"
        );
        assert_eq!(
            s(get(answer(&result, &format!("good{law}")), "status")),
            "established",
            "{law}"
        );
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
fn unsupported_integer_order_presentation_keeps_the_object_for_checks_and_localization() {
    let dir = files(
        "build-order-greater",
        "view amount(c:Part):Z=c.quantity; law required ordered(c:Part):c.quantity>2;",
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
        assert_eq!(
            s(get(get(reason, "details"), "method")),
            "integer_order_equation_presentation"
        );
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
        assert_eq!(s(get(answer(&result, id), "status")), "refuted");
    }
    assert_eq!(s(get(answer(&result, "l"), "status")), "established");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
    for reason in reasons {
        assert!(arr(get(plan, "blockers")).contains(reason));
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
        assert_eq!(r.code, if missing { 2 } else { 1 }, "{}", r.stdout);
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
            let mut subjects = vec![];
            for patch in arr(get(cover, "patches")) {
                let context = value(&j, patch);
                let locals = arr(get(context, "locals"));
                assert_eq!(locals.len(), 1);
                let binding = &arr(get(&locals[0], "bindings"))[0];
                subjects.push(s(&arr(value(&j, get(binding, "value")))[1]).to_owned());
            }
            subjects.sort();
            assert_eq!(subjects, vec!["p", "q"]);
            assert_eq!(s(get(answer(&j, "e"), "status")), "refuted");
            assert_eq!(s(get(answer(&j, "s"), "status")), "refuted");
        }
    }
}

#[test]
fn missing_owner_keeps_build_partial_and_needed() {
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
        let result = saved(
            &dir,
            &result_run,
            if missing { "partial" } else { "complete" },
            if missing { 2 } else { 0 },
        );
        let b = answer(&result, "b");
        assert_eq!(
            s(get(b, "status")),
            if missing {
                "undetermined"
            } else {
                "established"
            }
        );
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
    }
}

#[test]
fn numeric_tuple_view_families_build_and_evaluate() {
    let dir = files(
        "numeric-tuple-view",
        "law required balanced(c:Part):c.quantity=c.quantity;view combine(c:Part,pair:(Q,(Q,Q)),take:Bool):(Q,Z)=(if take then pair.0+pair.1.1 else pair.1.1-pair.0,c.quantity);view seed():(Q,(Q,Q))=(rat(1,2),(1,rat(3,2)));view no():Bool=false;",
        false,
    );
    // else腕は有理数の差 3/2-1/2 と観測pの値を返す。
    let requests = [
        "b=build(R,on=@v/root)",
        "s=evaluate(R.seed,on=$b.object)",
        "no=evaluate(R.no,on=$b.object)",
        "w=evaluate(R.combine,on=$b.object,c=@v/p,pair=$s.value,take=$no.value)",
    ];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 0);
    assert!(has(get(answer(&result, "b"), "outputs"), "algebra"));
    assert_eq!(
        value(&result, get(get(answer(&result, "w"), "outputs"), "value")).value,
        archsig_common::json::parse(br#"[["1","1"],"0"]"#)
            .unwrap()
            .value
    );
}

fn required_tuple_law_case(case: &str) {
    let expression = match case {
        "missing" => "pair.0+c.quantity=pair.0",
        "unknown" => "pair.0*pair.1.1=1",
        _ => "pair.0=pair.1.1",
    };
    let signature = if case == "missing" {
        "pair:(Z,(Z,Z)),c:Part"
    } else {
        "pair:(Z,(Z,Z)),c:Part,last:Z,more:(Z,Z)"
    };
    let body = format!("law required balanced({signature}):{expression};");
    let missing = case == "missing";
    let dir = files(&format!("required-tuple-{case}"), &body, missing);
    let code = if case == "refuted" { 1 } else { 2 };
    let mut requests = vec![
        "b=build(R,on=@v/root)",
        "c=check(R.balanced,on=$b.object,c=@v/q)",
        "n=needed($c)",
    ];
    if missing {
        requests.push("p=check(R.balanced,on=$b.object,c=@v/p)");
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
        if code == 1 { "refuted" } else { "undetermined" }
    );
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    match case {
        "refuted" => {
            // 反例は宣言順のLaw parameter束縛で、tupleの成分が食い違う値を持つ。
            let examples = arr(get(checked, "counterexamples"));
            assert!(!examples.is_empty());
            for example in examples {
                let data = get(value(&result, example), "data");
                let bindings = arr(get(data, "bindings"));
                let names: Vec<_> = bindings.iter().map(|b| s(get(b, "name"))).collect();
                assert_eq!(names, vec!["pair", "c", "last", "more"]);
                let pair = arr(value(&result, get(&bindings[0], "value")));
                assert_eq!(pair.len(), 2);
                assert_ne!(pair[0].value, arr(&pair[1])[1].value);
                let left = value(&result, get(value(&result, get(data, "left")), "value"));
                let right = value(&result, get(value(&result, get(data, "right")), "value"));
                assert_ne!(left.value, right.value);
            }
        }
        "missing" => {
            // 欠測は二つの補完の結果が食い違う組として示す。
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
                assert!(
                    arr(get(data, "fields"))
                        .iter()
                        .any(|f| s(get(f, "subject")) == "q"
                            && s(get(f, "field")) == "Build.Part.quantity")
                );
            }
            assert_eq!(s(get(answer(&result, "p"), "status")), "established");
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "subject")) == "q" && s(get(field, "field")) == "Build.Part.quantity"
            }));
        }
        _ => {
            assert!(!has(checked, "counterexamples"));
            assert!(!arr(get(plan, "blockers")).is_empty());
        }
    }
}

#[test]
fn required_numeric_tuple_laws_build_and_check() {
    required_tuple_law_case("refuted");
}

#[test]
fn required_numeric_tuple_missing_observations() {
    required_tuple_law_case("missing");
}

#[test]
fn required_numeric_tuple_unknown_nonlinear() {
    required_tuple_law_case("unknown");
}

#[test]
fn required_numeric_tuple_empty_guard_skips_unobserved_body() {
    let body = "law required balanced(pair:(Z,(Z,Z)),c:Part) when pair.0+1=pair.0:c.quantity=100;";
    let dir = files("required-tuple-empty-direct", body, true);
    let requests = ["c=check(R.balanced,c=@v/q)", "n=needed($c)"];
    let run = asks(&dir, &requests);
    let result = saved(&dir, &run, "complete", 0);
    let checked = answer(&result, "c");
    assert_eq!(s(get(checked, "status")), "established");
    assert_eq!(s(get(checked, "applicability")), "not_applicable");
    assert!(!has(checked, "counterexamples"));
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
}
