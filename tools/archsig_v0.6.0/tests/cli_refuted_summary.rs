//! 反証の日常表示は実値だけを上限付きで返す。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::json::JNode;
use cli::*;
use std::path::{Path, PathBuf};
const D: &str = include_str!("fixtures/counter.atoms.json");
const L: &str = include_str!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");
fn inputs(label: &str, law: &str, map: &str) -> PathBuf {
    let dir = workdir(label);
    for (name, text) in [("d.json", D), ("l.law", law), ("a.json", map)] {
        std::fs::write(dir.join(name), text).unwrap();
    }
    dir
}
fn execute(dir: &Path, asks: &[&str], saved: bool) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    if saved {
        args.extend(["--out", "saved"]);
    }
    let result = if saved {
        run(dir, &args)
    } else {
        without_file_changes(dir, || run(dir, &args))
    };
    assert!(result.stderr.is_empty());
    if !saved {
        for trace in [
            "\"node\":",
            "\"evidence\":",
            "\"rule\":",
            "\"scope\":",
            "\"dependencies\":",
        ] {
            assert!(!result.stdout.contains(trace), "{}", result.stdout);
        }
    }
    result
}
fn first(r: &Run) -> &JNode {
    &arr(get(&r.receipt, "answers"))[0]
}
fn value(node: &JNode) -> &JNode {
    get(node, "value")
}
fn example(answer: &JNode) -> &JNode {
    &arr(get(answer, "counterexamples"))[0]
}

#[test]
fn negative_counter_shows_subject_values_operator_and_atom_without_files() {
    let map = A.replace("\"value\": \"2\"", "\"value\": \"-3\"");
    let dir = inputs("summary-negative-values", L, &map);
    let asks = ["ok=check(CountCheck.nonnegative,s=@v/s)"];
    let r = execute(&dir, &asks, false);
    assert_eq!(r.code, 1, "{}", r.stdout);
    assert!(r.stdout.len() < 1500);
    let answer = first(&r);
    assert_eq!(s(get(answer, "status")), "refuted");
    assert_eq!(num(get(answer, "counterexamples_total")), 1);
    let e = example(answer);
    assert_eq!(s(get(e, "operator")), ">=");
    assert_eq!(s(value(get(e, "left"))), "-3");
    assert_eq!(s(value(get(e, "right"))), "0");
    let binding = &arr(get(e, "bindings"))[0];
    assert_eq!(s(get(binding, "name")), "s");
    let subject = arr(value(get(binding, "value")));
    assert_eq!((s(&subject[0]), s(&subject[1])), ("v", "s"));
    assert!(arr(get(e, "facts")).iter().any(|fact| {
        has(fact, "field")
            && s(get(fact, "snapshot")) == "v"
            && s(get(fact, "subject")) == "s"
            && s(get(fact, "field")) == "Counter.State.count"
            && s(get(fact, "atom")) == "count"
    }));
    // 保存形式は従来どおりノード参照で、summary専用欄を含まない。
    let saved = execute(&dir, &asks, true);
    let result = result_json(&dir, &saved);
    let answer = &arr(get(&result, "answers"))[0];
    assert!(!has(answer, "counterexamples_total"));
    let reference = &arr(get(answer, "counterexamples"))[0];
    assert!(has(reference, "node"));
    let node = arr(get(&result, "nodes"))
        .iter()
        .find(|n| get(n, "id").value == get(reference, "node").value)
        .unwrap();
    let data = get(value(node), "data");
    assert!(has(get(data, "left"), "node"));
    assert!(has(get(data, "right"), "node"));
    assert!(!has(data, "operator"));
    assert!(!has(data, "facts_total"));
}

#[test]
fn established_and_undetermined_summaries_keep_their_previous_fields() {
    let asks = ["ok=check(CountCheck.nonnegative,s=@v/s)"];
    let dir = inputs("summary-held-unchanged", L, A);
    let held = execute(&dir, &asks, false);
    let expected = archsig::json::parse(br#"{"answers":[{"applicability":"applicable","id":"ok","outputs":{},"question":"check","status":"established"}],"exit_code":0,"format":"archsig.summary/1","status":"complete"}"#).unwrap();
    assert_eq!(held.receipt.value, expected.value);
    let map = A.replace(r#"{"id": "count", "subject": "s", "field": "Counter.State.count", "value": "2", "origin": "model"}"#, "");
    let dir = inputs("summary-unknown-unchanged", L, &map);
    let unknown = execute(&dir, &asks, false);
    assert_eq!(unknown.code, 2);
    let answer = first(&unknown);
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(!has(answer, "counterexamples"));
    assert!(!has(answer, "counterexamples_total"));
    let reasons = arr(get(answer, "reasons"));
    assert!(
        reasons
            .iter()
            .any(|reason| s(get(reason, "code")) == "missing_observation")
    );
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
}

#[test]
fn many_refutations_show_first_three_and_the_full_total_in_existing_order() {
    let law = L.replace(
        "view amount",
        "law optional many(s:State): forall n in list<Z>[0,1,2,3,4] . s.count>=n; view amount",
    );
    let map = A.replace("\"value\": \"2\"", "\"value\": \"-3\"");
    let dir = inputs("summary-many-examples", &law, &map);
    let asks = ["no=check(CountCheck.many,s=@v/s)"];
    let r = execute(&dir, &asks, false);
    assert_eq!(r.code, 1, "{}", r.stdout);
    let answer = first(&r);
    assert_eq!(num(get(answer, "counterexamples_total")), 6); // 5 members and the whole forall.
    assert_eq!(arr(get(answer, "counterexamples")).len(), 3);
    for (e, expected) in arr(get(answer, "counterexamples"))
        .iter()
        .zip(["0", "1", "2"])
    {
        let n = arr(get(e, "bindings"))
            .iter()
            .find(|binding| s(get(binding, "name")) == "n")
            .unwrap();
        assert_eq!(s(value(get(n, "value"))), expected);
        assert!(!has(e, "operator")); // These compare false with required true, not the numeric operands.
    }
    assert!(r.stdout.len() < 4000);
    let saved = execute(&dir, &asks, true);
    assert_eq!(
        arr(get(
            &arr(get(&result_json(&dir, &saved), "answers"))[0],
            "counterexamples"
        ))
        .len(),
        6
    );
}

#[test]
fn bindings_and_facts_are_limited_with_totals_and_large_values_are_not_expanded() {
    let law = L.replace("view amount", "law optional all(a:State,b:State,c:State,d:State):a.count+b.count+c.count+d.count>=0; view amount");
    let subjects = (0..4)
        .map(|n| format!(r#"{{"id":"s{n}","type":"Counter.State","origin":"model"}}"#))
        .collect::<Vec<_>>()
        .join(",");
    let atoms = (0..4).map(|n| format!(r#"{{"id":"c{n}","subject":"s{n}","field":"Counter.State.count","value":"-3","origin":"model"}}"#)).collect::<Vec<_>>().join(",");
    let map = A.replace(r#"{"id": "s", "type": "Counter.State", "origin": "model"}"#, &subjects)
        .replace(r#"{"id": "count", "subject": "s", "field": "Counter.State.count", "value": "2", "origin": "model"}"#, &atoms);
    let dir = inputs("summary-limited-facts", &law, &map);
    let r = execute(
        &dir,
        &["no=check(CountCheck.all,a=@v/s0,b=@v/s1,c=@v/s2,d=@v/s3)"],
        false,
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let e = example(first(&r));
    assert_eq!(num(get(e, "bindings_total")), 4);
    assert_eq!(arr(get(e, "bindings")).len(), 3);
    assert!(num(get(e, "facts_total")) > 3);
    assert_eq!(arr(get(e, "facts")).len(), 3);

    let large = "日".repeat(1000);
    let law = L.replace(
        "view amount",
        &format!("law optional text(s:State):\"{large}\"=\"x\"; view amount"),
    );
    let subject = "s".repeat(400);
    let map = A
        .replace("\"s\"", &format!("\"{subject}\""))
        .replace("\"value\": \"2\"", "\"value\": \"-3\"");
    let dir = inputs("summary-bounded-text", &law, &map);
    let r = execute(
        &dir,
        &[
            &format!("no=check(CountCheck.text,s=@v/{subject})"),
            &format!("count=check(CountCheck.nonnegative,s=@v/{subject})"),
        ],
        false,
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let e = example(first(&r));
    assert_eq!(num(get(get(e, "left"), "value_bytes")), 3002);
    assert!(!has(get(e, "left"), "value"));
    let count = &arr(get(&r.receipt, "answers"))[1];
    assert!(
        arr(get(example(count), "facts"))
            .iter()
            .any(|fact| has(fact, "subject_bytes") && num(get(fact, "subject_bytes")) == 400)
    );
    assert!(r.stdout.len() < 2000);
}

#[test]
fn guarded_laws_and_value_comparisons_keep_the_actual_operand_pairs() {
    let law = L.replace("view amount", "law optional guarded(s:State) when true:s.count>=0; view next(s:State):Z=s.count+1; view amount");
    let map = A.replace("\"value\": \"2\"", "\"value\": \"-3\"");
    let dir = inputs("summary-comparison-pairs", &law, &map);
    let r = execute(
        &dir,
        &[
            "guarded=check(CountCheck.guarded,s=@v/s)",
            "n=evaluate(CountCheck.amount,s=@v/s)",
            "next=evaluate(CountCheck.next,s=@v/s)",
            "different=compare($n.value,to=$next.value,kind=value)",
        ],
        false,
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let answers = arr(get(&r.receipt, "answers"));
    let guarded = example(&answers[0]);
    assert!(!has(guarded, "operator"));
    assert_eq!(s(value(get(guarded, "left"))), "-3");
    assert_eq!(s(value(get(guarded, "right"))), "0");
    let different = example(&answers[3]);
    assert_eq!(s(value(get(different, "left"))), "-3");
    assert_eq!(s(value(get(different, "right"))), "-2");
    assert!(!has(different, "operator"));
}

#[test]
fn separating_pairs_show_existing_candidate_and_law_values() {
    let law = L.replace("view amount", "change choose(s:State,b:Bool)=s with{count=if b then 0 else 1}; view zero(s:State):Z=0; law optional iszero(s:State):s.count=0; view amount");
    let dir = inputs("summary-separating-pair", &law, A);
    let r = execute(
        &dir,
        &[
            "s=solve(CountCheck.nonnegative,on=@v/s,using=CountCheck.choose,s=@v/s)",
            "q=quotient(CountCheck.zero,on=$s.domain,s=@v/s,law=CountCheck.iszero)",
        ],
        false,
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let answers = arr(get(&r.receipt, "answers"));
    let e = example(&answers[1]);
    assert_eq!(s(get(e, "kind")), "separating_pair");
    assert_ne!(value(get(e, "left")).value, value(get(e, "right")).value);
    assert_ne!(value(get(e, "first")).value, value(get(e, "second")).value);
    assert!(!has(e, "bindings")); // No named bindings or Atom reads are stored in a separating pair.
    assert!(!has(e, "facts"));
    assert!(r.stdout.len() < 4000);
}
