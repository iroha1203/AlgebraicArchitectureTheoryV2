//! AC4: Reservations の ArchMap の変種。補完の存在、Map の全域性、所属、端点不保存、語彙 binding。

mod common;
use archsig::archmap::Slot;
use archsig::issue::Code;
use common::*;

/// 一行の Atom を除く。
fn without(atom: &str) -> String {
    let line = RESERVATIONS_MAP
        .lines()
        .find(|l| l.contains(&format!("\"id\": \"{atom}\"")))
        .unwrap();
    let mut out = RESERVATIONS_MAP.replace(&format!("{line}\n"), "");
    // 最後の Atom を除いた場合は直前の行の末尾の `,` を外す。
    if line.trim_end().ends_with('}') && !line.trim_end().ends_with("},") {
        let i = out.rfind("},\n    ]").unwrap();
        out.replace_range(i..i + 2, "}");
    }
    out
}

fn with_value(atom: &str, value: &str) -> String {
    let line = RESERVATIONS_MAP
        .lines()
        .find(|l| l.contains(&format!("\"id\": \"{atom}\"")))
        .unwrap();
    let start = line.find("\"value\": ").unwrap() + 9;
    let end = line.rfind(", \"origin\"").unwrap();
    let mut new = line.to_owned();
    new.replace_range(start..end, value);
    RESERVATIONS_MAP.replace(line, &new)
}

#[test]
fn normative_archmaps_pass_with_their_law() {
    let c = map_ok(RESERVATIONS_DEFINITION, RESERVATIONS_MAP);
    assert!(missing_slots(&c).is_empty());
    assert_eq!(c.vocabularies.len(), 1);
    // retained は偽だが、静的検査は成立・反証を問わない。
    let e = map_ok(ENGINE_DEFINITION, ENGINE_MAP);
    assert!(missing_slots(&e).is_empty());
}

#[test]
fn unknown_owners_references_and_maps_have_completions() {
    for atom in [
        "r-free",
        "m-states",
        "p-owner",
        "e-from",
        "m-from",
        "e-owner",
        "m-reserves",
    ] {
        let c = map_ok(RESERVATIONS_DEFINITION, &without(atom));
        let missing = missing_slots(&c);
        assert_eq!(missing.len(), 1, "{atom}");
        assert_eq!(missing[0].0, "v");
    }
    let c = map_ok(RESERVATIONS_DEFINITION, &without("r-free"));
    assert_eq!(missing_slots(&c)[0].1, "r");
    assert_eq!(missing_slots(&c)[0].2, "Reservations.State.free");
    assert_eq!(field(&c, "v", "r", "free").slot, Slot::Missing);
}

#[test]
fn presentations_without_completion_are_inconsistent() {
    // e の owner が未知で、from は A、to は B の状態を指す。
    let split = without("e-owner").replace(
        r#""value": ["v", "q"], "origin": "model"}"#,
        r#""value": ["v", "r"], "origin": "model"}"#,
    );
    assert!(split.contains(
        r#""id": "e-to", "subject": "e", "field": "Reservations.Reserve.to", "value": ["v", "r"]"#
    ));
    let issue = map_err(RESERVATIONS_DEFINITION, &split);
    assert_eq!(issue.code, Code::InconsistentObservation, "{issue:?}");
    // m の from が未知で、states の key が A と B の状態にまたがる。
    let mixed = with_value(
        "m-states",
        r#"[[["v", "p"], ["v", "r"]], [["v", "r"], ["v", "s"]]]"#,
    );
    let mixed = mixed.replace(
        &RESERVATIONS_MAP
            .lines()
            .find(|l| l.contains("\"m-from\""))
            .unwrap()
            .to_owned(),
        "",
    );
    let issue = map_err(RESERVATIONS_DEFINITION, &mixed);
    assert_eq!(issue.code, Code::InconsistentObservation, "{issue:?}");
}

#[test]
fn known_invalid_references_and_partial_maps_are_rejected() {
    // 既知値だけで破れる全域性・所属は、補完が一つもない入力として拒否する。
    // 全域性違反: q の行がない。
    let partial = with_value("m-states", r#"[[["v", "p"], ["v", "r"]]]"#);
    let issue = map_err(RESERVATIONS_DEFINITION, &partial);
    assert_eq!(issue.code, Code::InconsistentObservation);
    assert!(pointer(&issue).ends_with("/value"), "{issue:?}");
    // 値が終域の族に属さない。
    let outside = with_value(
        "m-states",
        r#"[[["v", "p"], ["v", "r"]], [["v", "q"], ["v", "p"]]]"#,
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &outside).code,
        Code::InconsistentObservation
    );
    // 所属の合わない端点。
    let foreign = with_value("e-to", r#"["v", "r"]"#);
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &foreign).code,
        Code::InconsistentObservation
    );
    // 宣言型の違う参照、存在しない参照。
    assert_eq!(
        map_err(
            RESERVATIONS_DEFINITION,
            &with_value("e-to", r#"["v", "A"]"#)
        )
        .code,
        Code::Type
    );
    assert_eq!(
        map_err(
            RESERVATIONS_DEFINITION,
            &with_value("e-to", r#"["w", "q"]"#)
        )
        .code,
        Code::Reference
    );
    // key の重複。
    let dup = with_value(
        "m-states",
        r#"[[["v", "p"], ["v", "r"]], [["v", "p"], ["v", "s"]]]"#,
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &dup).code,
        Code::DuplicateKey
    );
    // 同じ値の Atom を二度置く。
    let line = RESERVATIONS_MAP
        .lines()
        .find(|l| l.contains("\"p-free\""))
        .unwrap();
    let twice = RESERVATIONS_MAP.replace(
        line,
        &format!("{line}\n{}", line.replace("p-free", "p-free-again")),
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &twice).code,
        Code::DuplicateFact
    );
}

#[test]
fn endpoint_breaking_maps_pass_the_static_check() {
    let swapped = with_value(
        "m-states",
        r#"[[["v", "p"], ["v", "s"]], [["v", "q"], ["v", "r"]]]"#,
    );
    map_ok(RESERVATIONS_DEFINITION, &swapped);
}

#[test]
fn vocabulary_bindings_are_matched_against_the_manifest() {
    let digest = "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
    let wrong = RESERVATIONS_MAP.replace(digest, &format!("sha256:{}", "0".repeat(64)));
    let issue = map_err(RESERVATIONS_DEFINITION, &wrong);
    assert_eq!(
        (issue.code, pointer(&issue)),
        (Code::VocabularyMismatch, "/vocabularies/0/digest")
    );
    let unbound = RESERVATIONS_MAP.replace(
        &format!(r#"[{{"namespace": "Reservations", "version": "1", "digest": "{digest}"}}]"#),
        "[]",
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &unbound).code,
        Code::VocabularyMismatch
    );
    let extra = RESERVATIONS_MAP.replace(
        &format!(r#"{{"namespace": "Reservations", "version": "1", "digest": "{digest}"}}"#),
        &format!(r#"{{"namespace": "Reservations", "version": "1", "digest": "{digest}"}}, {{"namespace": "Other", "version": "1", "digest": "{digest}"}}"#),
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &extra).code,
        Code::Reference
    );
    // 条件だけの変更は定義の binding を変えない。
    let law = RESERVATIONS.replace("law required retained", "law optional retained");
    ok(RESERVATIONS_DEFINITION, &law);
    map_ok(RESERVATIONS_DEFINITION, RESERVATIONS_MAP);
    // 定義の meaning を変えたときは古い digest に一致しない。
    let changed = RESERVATIONS_DEFINITION.replacen("予約", "予約の説明を変更した", 1);
    assert_ne!(changed, RESERVATIONS_DEFINITION);
    assert_eq!(
        map_err(&changed, RESERVATIONS_MAP).code,
        Code::VocabularyMismatch
    );
}

#[test]
fn subject_types_and_fields_come_from_the_vocabulary() {
    let bad_type = RESERVATIONS_MAP.replace(
        r#""type": "Reservations.System""#,
        r#""type": "Reservations.holdings""#,
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &bad_type).code,
        Code::Reference
    );
    let bad_field = RESERVATIONS_MAP.replace(
        "Reservations.State.free\", \"value\": \"2\"",
        "Reservations.State.cash\", \"value\": \"2\"",
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &bad_field).code,
        Code::Reference
    );
    let foreign_field = RESERVATIONS_MAP.replace(
        "Reservations.State.free\", \"value\": \"2\"",
        "Reservations.Reserve.from\", \"value\": \"2\"",
    );
    assert_eq!(
        map_err(RESERVATIONS_DEFINITION, &foreign_field).code,
        Code::Reference
    );
}
