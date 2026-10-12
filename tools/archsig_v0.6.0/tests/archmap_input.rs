//! ArchMap の JSON と版(入力仕様 §1)、AC5 の ArchMap 側(集合表の順、List の順と重複)。

mod common;
use archsig::archmap::check_archmap;
use archsig::canonical::sha256_digest;
use archsig::issue::{Code, Details, Location};
use common::*;

fn failure(map: &[u8]) -> archsig::issue::Issue {
    let law = ok(RESERVATIONS);
    check_archmap(map, &law).expect_err("落ちるはず").issue
}

#[test]
fn json_errors_are_rejected_with_their_position() {
    let mut bom = vec![0xEF, 0xBB, 0xBF];
    bom.extend_from_slice(RESERVATIONS_MAP.as_bytes());
    let i = failure(&bom);
    assert_eq!(
        (i.code, i.location.clone()),
        (
            Code::Syntax,
            Location::ArchMap {
                pointer: String::new(),
                span: Some((0, 3))
            }
        )
    );

    let mut bad = RESERVATIONS_MAP.as_bytes().to_vec();
    let at = RESERVATIONS_MAP.find("二つ").unwrap();
    bad[at] = 0xFF;
    let i = failure(&bad);
    assert_eq!(i.code, Code::Syntax);
    assert!(matches!(i.location, Location::ArchMap { span: Some((s, _)), .. } if s == at));

    let dup = RESERVATIONS_MAP.replacen(r#""sources": [],"#, r#""sources": [], "sources": [],"#, 1);
    let i = failure(dup.as_bytes());
    assert_eq!((i.code, pointer(&i)), (Code::DuplicateKey, "/sources"));

    let surrogate = RESERVATIONS_MAP.replacen("二つのシステム", "\\ud800", 1);
    assert_eq!(failure(surrogate.as_bytes()).code, Code::Syntax);

    let unknown =
        RESERVATIONS_MAP.replacen(r#""sources": [],"#, r#""sources": [], "extra": 1,"#, 1);
    let i = failure(unknown.as_bytes());
    assert_eq!((i.code, pointer(&i)), (Code::Syntax, "/extra"));

    let null = RESERVATIONS_MAP.replacen(r#""locations": [],"#, r#""locations": null,"#, 1);
    let i = failure(null.as_bytes());
    assert_eq!(
        (i.code, pointer(&i)),
        (Code::Syntax, "/origins/0/locations")
    );

    let missing = RESERVATIONS_MAP.replacen(r#""sources": [],"#, "", 1);
    assert_eq!(failure(missing.as_bytes()).code, Code::Syntax);
    let trailing = format!("{RESERVATIONS_MAP} {{}}");
    assert_eq!(failure(trailing.as_bytes()).code, Code::Syntax);
    let huge = RESERVATIONS_MAP.replacen(r#""sources": [],"#, r#""sources": [], "n": 1e999,"#, 1);
    assert_eq!(failure(huge.as_bytes()).code, Code::Syntax);
}

#[test]
fn unknown_versions_come_before_unknown_fields() {
    let future = RESERVATIONS_MAP
        .replace(
            r#""format": "archsig.archmap/1""#,
            r#""format": "archsig.archmap/2""#,
        )
        .replacen(
            r#""sources": [],"#,
            r#""sources": [], "future": {"anything": true},"#,
            1,
        );
    let i = failure(future.as_bytes());
    assert_eq!(i.code, Code::UnsupportedVersion);
    assert_eq!(
        i.details,
        Details::Version {
            found_format: "archsig.archmap/2".into(),
            found_semantics: Some("archsig/0.6.0".into())
        }
    );
    let semantics = RESERVATIONS_MAP.replacen(
        r#""semantics": "archsig/0.6.0""#,
        r#""semantics": "archsig/9""#,
        1,
    );
    assert_eq!(failure(semantics.as_bytes()).code, Code::UnsupportedVersion);
}

fn model(map: &str) -> String {
    map_ok(RESERVATIONS, map).model_digest
}

#[test]
fn set_tables_do_not_change_the_model_digest() {
    let base = map_ok(RESERVATIONS, RESERVATIONS_MAP);
    assert_eq!(
        base.bytes_digest,
        sha256_digest(RESERVATIONS_MAP.as_bytes())
    );
    // subject 表と Atom 表の順を逆にし、空白も変える。
    let mut lines: Vec<&str> = RESERVATIONS_MAP.lines().collect();
    let subjects: Vec<usize> = (0..lines.len())
        .filter(|&i| lines[i].contains("\"type\": \"Reservations."))
        .collect();
    let atoms: Vec<usize> = (0..lines.len())
        .filter(|&i| lines[i].contains("\"field\": "))
        .collect();
    let reorder = |idx: &[usize], lines: &mut Vec<&str>| {
        let texts: Vec<String> = idx
            .iter()
            .map(|&i| lines[i].trim().trim_end_matches(',').to_owned())
            .collect();
        let n = texts.len();
        for (k, &i) in idx.iter().enumerate() {
            let t = texts[n - 1 - k].clone();
            lines[i] = Box::leak(
                if k + 1 < n {
                    format!("      {t},")
                } else {
                    format!("      {t}")
                }
                .into_boxed_str(),
            );
        }
    };
    reorder(&subjects, &mut lines);
    reorder(&atoms, &mut lines);
    let reordered = lines.join("\n").replace("\"model\"}", "\"model\" }");
    assert_ne!(reordered, RESERVATIONS_MAP);
    let other = map_ok(RESERVATIONS, &reordered);
    assert_ne!(other.bytes_digest, base.bytes_digest);
    assert_eq!(other.model_digest, base.model_digest);
    // Set の値の順も model_digest を変えない。Map の行の順も同じ。
    let rows = RESERVATIONS_MAP.replace(
        r#"[[["v", "p"], ["v", "r"]], [["v", "q"], ["v", "s"]]]"#,
        r#"[[["v", "q"], ["v", "s"]], [["v", "p"], ["v", "r"]]]"#,
    );
    assert_eq!(model(&rows), base.model_digest);
    // 由来だけの変更は model_digest を変える。
    let note = RESERVATIONS_MAP.replace("成立・残差・修復は入力しない。", "注記を変えた。");
    assert_ne!(model(&note), base.model_digest);
}

const LISTS: &str = r#"law "archsig.law/1" semantics "archsig/0.6.0";
reading L { entity E { xs: List<Z>; ys: Set<Z>; t: Text; } }
"#;

fn list_doc(xs: &str, ys: &str, t: &str) -> String {
    let digest = ok(LISTS).vocabularies[0].digest.clone();
    format!(
        r#"{{"format":"archsig.archmap/1","semantics":"archsig/0.6.0","vocabularies":[{{"reading":"L","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"m","locations":[],"note":"n"}}],"snapshots":[{{"id":"s","origin":"o","subjects":[{{"id":"e","type":"L.E","origin":"o"}}],"atoms":[{{"id":"a","subject":"e","field":"L.E.xs","value":{xs},"origin":"o"}},{{"id":"b","subject":"e","field":"L.E.ys","value":{ys},"origin":"o"}},{{"id":"c","subject":"e","field":"L.E.t","value":{t},"origin":"o"}}]}}]}}"#
    )
}

#[test]
fn list_order_and_repetition_are_kept() {
    let a = map_ok(
        LISTS,
        &list_doc(r#"["1","2","2"]"#, r#"["1","2"]"#, r#""x""#),
    )
    .model_digest;
    let set_swapped = map_ok(
        LISTS,
        &list_doc(r#"["1","2","2"]"#, r#"["2","1"]"#, r#""x""#),
    )
    .model_digest;
    assert_eq!(a, set_swapped);
    let list_swapped = map_ok(
        LISTS,
        &list_doc(r#"["2","1","2"]"#, r#"["1","2"]"#, r#""x""#),
    )
    .model_digest;
    assert_ne!(a, list_swapped);
    let list_shorter =
        map_ok(LISTS, &list_doc(r#"["1","2"]"#, r#"["1","2"]"#, r#""x""#)).model_digest;
    assert_ne!(a, list_shorter);
}

/// Text の値は escape を解いた値で保持し、正規化しない。canonical bytes は仕様から独立に計算した値。
#[test]
fn text_values_keep_unicode_and_control_characters() {
    let doc = list_doc(r#"[]"#, r#"[]"#, r#""éé\u0001\n\"\\/\u007f😀""#);
    let c = map_ok(LISTS, &doc);
    let canonical = archsig::archmap::model_json(&c).canonical();
    assert!(
        canonical.contains("\"value\":\"\u{e9}e\u{301}\\u0001\\u000a\\\"\\\\/\u{7f}\u{1f600}\""),
        "{canonical}"
    );
    let nfc = list_doc(r#"[]"#, r#"[]"#, r#""éé\u0001\n\"\\/\u007f😀""#);
    assert_ne!(map_ok(LISTS, &nfc).model_digest, c.model_digest);
    assert_eq!(c.model_digest, EXPECTED_TEXT_DIGEST);
}

const EXPECTED_TEXT_DIGEST: &str =
    "sha256:cea0d02df67f808bfdd586ffa79e2a8fb772293764fd3d6f31b17c72d1b9491f";
