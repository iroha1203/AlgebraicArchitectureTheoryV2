//! 公開される検査診断の固定文言と入力文字列を区別する。
mod common;
use archsig::json::JValue;
use common::cli::*;

const D: &str = include_str!("fixtures/counter.atoms.json");
const L: &str = include_str!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");

fn rejected(label: &str, law: &str, map: &str) -> Run {
    let dir = workdir(label);
    for (name, text) in [("d.json", D), ("l.law", law), ("a.json", map)] {
        std::fs::write(dir.join(name), text).unwrap();
    }
    let r = without_file_changes(&dir, || {
        run(
            &dir,
            &[
                "check",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--out",
                "out",
            ],
        )
    });
    assert_eq!(r.code, 65, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "invalid");
    assert!(r.stderr.is_empty());
    assert!(!has(&r.receipt, "result"));
    assert_eq!(arr(get(&r.receipt, "issues")).len(), 1);
    r
}

#[test]
fn archmap_reference_and_mode_errors_use_english_and_preserve_locations() {
    let alternative = A.replace(r#""origins": ["#, r#""origins": [{"id":"alternate","mode":"proposed","method":"manual","locations":[],"note":"alternative"}, "#);
    let cases = [
        (
            "type",
            A.replace(r#""type": "Counter.State""#, r#""type": "Counter.Missing""#),
            "/snapshots/0/subjects/0/type",
            "`Counter.Missing` is not an entity, arrow, or correspondence declaration",
        ),
        (
            "source",
            A.replace(
                r#""locations": []"#,
                r#""locations": [{"source":"missing-source","path":"counter.rs","span":[0,1]}]"#,
            ),
            "/origins/0/locations/0/source",
            "source `missing-source` does not exist",
        ),
        (
            "snapshot-origin",
            A.replace(
                r#""id": "v", "origin": "model""#,
                r#""id": "v", "origin": "missing-snapshot""#,
            ),
            "/snapshots/0/origin",
            "origin `missing-snapshot` does not exist",
        ),
        (
            "subject-origin",
            A.replace(
                r#""type": "Counter.State", "origin": "model""#,
                r#""type": "Counter.State", "origin": "missing-subject""#,
            ),
            "/snapshots/0/subjects/0/origin",
            "origin `missing-subject` does not exist",
        ),
        (
            "atom-origin",
            A.replace(
                r#""value": "2", "origin": "model""#,
                r#""value": "2", "origin": "missing-atom""#,
            ),
            "/snapshots/0/atoms/0/origin",
            "origin `missing-atom` does not exist",
        ),
        (
            "subject-mode",
            alternative.replace(
                r#""type": "Counter.State", "origin": "model""#,
                r#""type": "Counter.State", "origin": "alternate""#,
            ),
            "/snapshots/0/subjects/0/origin",
            "subject origin.mode differs from snapshot",
        ),
        (
            "atom-mode",
            alternative.replace(
                r#""value": "2", "origin": "model""#,
                r#""value": "2", "origin": "alternate""#,
            ),
            "/snapshots/0/atoms/0/origin",
            "Atom origin.mode differs from snapshot",
        ),
    ];
    for (label, map, pointer, message) in cases {
        assert_ne!(map, A);
        let r = rejected(&format!("english-validation-{label}"), L, &map);
        let issue = &arr(get(&r.receipt, "issues"))[0];
        assert_eq!(s(get(issue, "code")), "reference");
        let location = get(issue, "location");
        assert_eq!(s(get(location, "input")), "archmap");
        assert_eq!(s(get(location, "pointer")), pointer);
        assert!(matches!(&get(issue,"details").value,JValue::Obj(fields) if fields.is_empty()));
        assert_eq!(s(get(issue, "message")), message);
        assert!(s(get(issue, "message")).is_ascii());
    }
}

#[test]
fn map_and_term_application_arity_errors_use_english() {
    for (label, declaration, message) in [
        (
            "map",
            "view bad(f:Map<State,State>,s:State):State=f(s,s);",
            "Map application requires 1 arguments",
        ),
        (
            "term",
            "view bad(t:Term<(Z)->Z>):Z=t(1,2);",
            "Term application requires 1 arguments",
        ),
    ] {
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";reading R{{use vocabulary Counter version "1" digest "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11";{declaration}}}"#
        );
        let r = rejected(&format!("english-validation-arity-{label}"), &law, A);
        let issue = &arr(get(&r.receipt, "issues"))[0];
        assert_eq!(s(get(issue, "code")), "syntax");
        let location = get(issue, "location");
        assert_eq!(s(get(location, "input")), "law");
        assert_eq!(arr(get(location, "span")).len(), 2);
        assert!(matches!(&get(issue,"details").value,JValue::Obj(fields) if fields.is_empty()));
        assert_eq!(s(get(issue, "message")), message);
        assert!(s(get(issue, "message")).is_ascii());
    }
}

#[test]
fn user_supplied_non_ascii_values_remain_in_the_english_diagnostic() {
    let value = "利用者が書いた値";
    let map = A.replace(r#""value": "2""#, &format!(r#""value": "{value}""#));
    let r = rejected("english-validation-input-value", L, &map);
    let issue = &arr(get(&r.receipt, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "syntax");
    assert_eq!(
        s(get(get(issue, "location"), "pointer")),
        "/snapshots/0/atoms/0/value"
    );
    let message = s(get(issue, "message"));
    assert!(message.contains(value));
    assert!(message.replace(value, "").is_ascii());
}

#[test]
fn result_projection_errors_keep_their_usage_details_in_english() {
    let dir = workdir("english-validation-projection");
    let law = L.replace(
        "view amount(s: State): Z = s.count;",
        "view amount(s: State): Z = s.count; view pair(): (Z,Bool) = (1,true);",
    );
    assert_ne!(law, L);
    for (name, text) in [("d.json", D), ("l.law", law.as_str()), ("a.json", A)] {
        std::fs::write(dir.join(name), text).unwrap();
    }
    for (asks, argument, expected) in [
        (
            vec![
                "p=evaluate(CountCheck.pair)",
                "bad=evaluate(CountCheck.amount,s=$p.value[2])",
            ],
            "bind.s",
            "Tuple index is out of range",
        ),
        (
            vec![
                "b=build(CountCheck,on=@v/s)",
                "bad=localize($b.object.unknown)",
            ],
            "head",
            "this type does not expose this projection",
        ),
    ] {
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
        for ask in &asks {
            args.extend(["--ask", ask]);
        }
        let r = without_file_changes(&dir, || run(&dir, &args));
        assert_eq!(r.code, 64, "{}", r.stdout);
        assert!(r.stderr.is_empty());
        assert!(!has(&r.receipt, "result"));
        let issue = &arr(get(&r.receipt, "issues"))[0];
        assert_eq!(s(get(issue, "code")), "usage");
        assert_eq!(s(get(issue, "request")), "bad");
        assert_eq!(s(get(get(issue, "details"), "argument")), argument);
        let message = s(get(issue, "message"));
        assert!(message.contains(expected), "{message}");
        assert!(s(get(issue, "message")).is_ascii());
    }
}
