//! 元 byte span と、人が読む1始まりの Unicode scalar 位置。
use crate::common;
use archsig::json::{JNode, JValue};
use common::cli::*;

const D: &str = include_str!("fixtures/counter.atoms.json");
const L: &str = include_str!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");

fn invoke(
    label: &str,
    command: &str,
    definition: &[u8],
    law: &[u8],
    map: &[u8],
    ask: Option<&str>,
) -> (std::path::PathBuf, Run) {
    let dir = workdir(label);
    for (name, bytes) in [("d.json", definition), ("l.law", law), ("a.json", map)] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let mut args = vec![
        command,
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "out",
    ];
    if let Some(ask) = ask {
        for expression in ask.split(';') {
            args.extend(["--ask", expression]);
        }
    }
    let r = if label.starts_with("invalid-") {
        without_file_changes(&dir, || run(&dir, &args))
    } else {
        run(&dir, &args)
    };
    (dir, r)
}

fn position(location: &JNode, input: &str, span: (usize, usize), line: u64, column: u64) {
    assert_eq!(s(get(location, "input")), input);
    let got = arr(get(location, "span"));
    assert_eq!((num(&got[0]), num(&got[1])), (span.0 as u64, span.1 as u64));
    assert_eq!(num(get(location, "line")), line);
    assert_eq!(num(get(location, "column")), column);
}

#[test]
fn missing_semicolon_and_multibyte_law_errors_have_start_positions_in_both_commands() {
    let missing = L.replacen(";", "", 1);
    let unicode = "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\n\"日本🦀\" ?";
    for (tag, text, start, end, line, column) in [
        (
            "semicolon",
            missing.as_str(),
            missing.find("reading").unwrap(),
            missing.find("reading").unwrap() + 7,
            2,
            1,
        ),
        (
            "unicode",
            unicode,
            unicode.find('?').unwrap(),
            unicode.len(),
            2,
            7,
        ),
    ] {
        for command in ["check", "run"] {
            let (dir, r) = invoke(
                &format!("invalid-law-{tag}-{command}"),
                command,
                D.as_bytes(),
                text.as_bytes(),
                A.as_bytes(),
                (command == "run").then_some("v=evaluate(CountCheck.amount,s=@v/s)"),
            );
            notified(&dir, &r, "invalid", 65);
            let issue = &arr(get(&r.receipt, "issues"))[0];
            assert_eq!(s(get(issue, "code")), "syntax");
            position(get(issue, "location"), "law", (start, end), line, column);
        }
    }
}

#[test]
fn json_errors_count_scalars_and_preserve_definition_and_archmap_spans() {
    // CRLF advances one line; tab and combining accent each count one scalar.
    let definition = "{\r\n\t\"日本🦀e\u{301}\": ";
    let map = "{\n\"日本🦀\": !}";
    for command in ["check", "run"] {
        for (input, text, start, end, column) in [
            (
                "definition0",
                definition,
                definition.len(),
                definition.len(),
                11,
            ),
            (
                "archmap",
                map,
                map.find('!').unwrap(),
                map.find('!').unwrap() + 1,
                8,
            ),
        ] {
            let (dir, r) = invoke(
                &format!("invalid-json-{input}-{command}"),
                command,
                if input == "definition0" {
                    text.as_bytes()
                } else {
                    D.as_bytes()
                },
                L.as_bytes(),
                if input == "archmap" {
                    text.as_bytes()
                } else {
                    A.as_bytes()
                },
                (command == "run").then_some("v=evaluate(CountCheck.amount,s=@v/s)"),
            );
            notified(&dir, &r, "invalid", 65);
            let location = get(&arr(get(&r.receipt, "issues"))[0], "location");
            assert_eq!(s(get(location, "pointer")), "");
            position(location, input, (start, end), 2, column);
        }
    }
}

#[test]
fn invalid_utf8_uses_the_valid_prefix_and_pointer_only_errors_stay_pointer_only() {
    let mut law = "\n日本🦀".as_bytes().to_vec();
    let start = law.len();
    law.push(0xff);
    for command in ["check", "run"] {
        let (dir, r) = invoke(
            &format!("invalid-utf8-{command}"),
            command,
            D.as_bytes(),
            &law,
            A.as_bytes(),
            (command == "run").then_some("v=evaluate(CountCheck.amount,s=@v/s)"),
        );
        notified(&dir, &r, "invalid", 65);
        position(
            get(&arr(get(&r.receipt, "issues"))[0], "location"),
            "law",
            (start, start + 1),
            2,
            4,
        );
    }
    let bad_map = A.replace("Counter.State", "Counter.Missing");
    let (dir, r) = invoke(
        "invalid-pointer",
        "check",
        D.as_bytes(),
        L.as_bytes(),
        bad_map.as_bytes(),
        None,
    );
    notified(&dir, &r, "invalid", 65);
    let location = get(&arr(get(&r.receipt, "issues"))[0], "location");
    assert!(has(location, "pointer"));
    for key in ["span", "line", "column"] {
        assert!(!has(location, key));
    }
}

// Every saved Location is checked against the original input, including nested occurrences.
fn saved_positions(node: &JNode, law: &str) -> usize {
    let mut count = 0;
    match &node.value {
        JValue::Obj(fields) => {
            if has(node, "input") && has(node, "span") {
                assert_eq!(s(get(node, "input")), "law");
                let span = arr(get(node, "span"));
                let start = num(&span[0]) as usize;
                let prefix = &law[..start];
                let line = prefix.chars().filter(|c| *c == '\n').count() + 1;
                let column = prefix.rsplit('\n').next().unwrap().chars().count() + 1;
                position(
                    node,
                    "law",
                    (start, num(&span[1]) as usize),
                    line as u64,
                    column as u64,
                );
                count += 1;
            }
            for (_, child) in fields {
                count += saved_positions(child, law);
            }
        }
        JValue::Arr(items) => {
            for item in items {
                count += saved_positions(item, law);
            }
        }
        _ => {}
    }
    count
}

#[test]
fn check_metadata_keeps_spans_and_scalar_positions() {
    let law = L.replace(
        "  view amount",
        "  view label(): Text = \"日本🦀\"; view amount",
    );
    let (dir, r) = invoke(
        "saved-check-locations",
        "check",
        D.as_bytes(),
        law.as_bytes(),
        A.as_bytes(),
        None,
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert!(saved_positions(&result, &law) > 0);
    let declarations = arr(get(&result, "declarations"));
    let amount = declarations
        .iter()
        .find(|d| s(get(d, "name")) == "CountCheck.amount")
        .unwrap();
    let start = law.find("view amount").unwrap();
    let end = start + "view amount(s: State): Z = s.count;".len();
    position(get(amount, "location"), "law", (start, end), 4, 31);
}

#[test]
fn saved_run_source_expressions_have_positions_after_compaction() {
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary}
view label(): Text = "日本🦀"; local here(s:State) reads s;
}}
reading After {{{vocabulary}
view label(): Text = "日本🦀"; local here(t:State) reads t;
}}
"#
    );
    // 位置の確認には状態の数は要らないので、対応 u→w を外した状態4つの観測を使う。
    let map = include_str!("fixtures/object-configuration-map.archmap.json")
        .lines()
        .filter(|line| {
            !line.contains(r#""id":"u","type":"#)
                && !line.contains(r#""id":"w","type":"#)
                && !line.contains(r#""subject":"u""#)
                && !line.contains(r#""subject":"w""#)
        })
        .collect::<Vec<_>>()
        .join("\n")
        .replace(r#",[["v","u"],["v","w"]]"#, "")
        .replace(",\n]", "\n]");
    let (dir, r) = invoke(
        "saved-run-source-locations",
        "run",
        include_bytes!("fixtures/reservations.atoms.json"),
        law.as_bytes(),
        map.as_bytes(),
        Some(
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ),
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert!(saved_positions(&result, &law) >= 2);
    assert_eq!(
        std::fs::read(dir.join("out/inputs/law.law")).unwrap(),
        law.as_bytes()
    );
}
