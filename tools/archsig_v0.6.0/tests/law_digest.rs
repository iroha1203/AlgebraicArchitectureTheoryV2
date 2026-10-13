//! AC5(Law 側): bytes_digest・model_digest・語彙 digest の区別と、文字列を正規化しない canonical bytes。

mod common;
use archsig::canonical::sha256_digest;
use archsig::law::{lexer, model_canonical};
use common::*;

fn digests(src: &str) -> (String, String, Vec<String>) {
    let c = ok(RESERVATIONS_DEFINITION, src);
    (
        c.bytes_digest,
        c.model_digest,
        c.definitions
            .vocabularies
            .values()
            .map(|v| v.digest.clone())
            .collect(),
    )
}

#[test]
fn whitespace_and_comments_change_only_the_bytes_digest() {
    let base = digests(RESERVATIONS);
    let spaced = RESERVATIONS
        .replace(
            "reading Reservations {",
            "// 予約の語彙\nreading   Reservations\t{ // 末尾のコメント",
        )
        .replace(
            "e.to.free + e.to.held",
            "e.to.free // 二つの量\n      +   e.to.held",
        );
    assert_ne!(spaced, RESERVATIONS);
    let other = digests(&spaced);
    assert_ne!(other.0, base.0, "bytes_digest は変わる");
    assert_eq!(other.1, base.1, "model_digest は変わらない");
    assert_eq!(other.2, base.2, "語彙 digest は変わらない");
    assert_eq!(base.0, sha256_digest(RESERVATIONS.as_bytes()));
}

#[test]
fn conditions_change_the_model_digest_but_not_the_vocabulary() {
    let base = digests(RESERVATIONS);
    let changes = [
        RESERVATIONS.replace("e.to.free + e.to.held = e.from.free + e.from.held", "e.to.free = e.from.free"),
        RESERVATIONS.replace("law required retained", "law optional retained"),
        RESERVATIONS.replace("  local Held(s: State) reads s.held;\n", ""),
        RESERVATIONS.replace("  view holdings", "  view zero(): Z = 0;\n  relation same(a: Reserve) when false: path(a) = path(a);\n  view holdings"),
        RESERVATIONS.replace("change rebalance(s: State, d: Z) =", "change rebalance(s: State, d: Z) when d > 0 ="),
    ];
    for changed in &changes {
        assert_ne!(changed, RESERVATIONS);
        let d = digests(changed);
        assert_ne!(d.1, base.1, "model_digest は変わる");
        assert_eq!(d.2, base.2, "原始宣言を保つ変更で語彙 digest は変わらない");
    }
}

/// 文字列は escape を解いた値を保ち、NFC/NFD を同一視しない。制御文字は \u00xx。
const UNICODE_LAW: &str = "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading U { view t(): List<Text> = list<Text>[\"\u{e9}\", \"e\u{301}\", \"\\u0001\\n\\\"\\\\/\\u007f\", \"\\ud83d\\ude00\", \"\\/\"]; }\n";

const UNICODE_CANONICAL: &str = "{\"semantics\":\"archsig/0.6.0\",\"tokens\":[{\"kind\":\"name\",\"text\":\"law\"},{\"kind\":\"string\",\"text\":\"archsig.law/2\"},{\"kind\":\"name\",\"text\":\"semantics\"},{\"kind\":\"string\",\"text\":\"archsig/0.6.0\"},{\"kind\":\"symbol\",\"text\":\";\"},{\"kind\":\"name\",\"text\":\"reading\"},{\"kind\":\"name\",\"text\":\"U\"},{\"kind\":\"symbol\",\"text\":\"{\"},{\"kind\":\"name\",\"text\":\"view\"},{\"kind\":\"name\",\"text\":\"t\"},{\"kind\":\"symbol\",\"text\":\"(\"},{\"kind\":\"symbol\",\"text\":\")\"},{\"kind\":\"symbol\",\"text\":\":\"},{\"kind\":\"name\",\"text\":\"List\"},{\"kind\":\"symbol\",\"text\":\"<\"},{\"kind\":\"name\",\"text\":\"Text\"},{\"kind\":\"symbol\",\"text\":\">\"},{\"kind\":\"symbol\",\"text\":\"=\"},{\"kind\":\"name\",\"text\":\"list\"},{\"kind\":\"symbol\",\"text\":\"<\"},{\"kind\":\"name\",\"text\":\"Text\"},{\"kind\":\"symbol\",\"text\":\">\"},{\"kind\":\"symbol\",\"text\":\"[\"},{\"kind\":\"string\",\"text\":\"\u{e9}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"e\u{301}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"\\u0001\\u000a\\\"\\\\/\u{7f}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"\u{1f600}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"/\"},{\"kind\":\"symbol\",\"text\":\"]\"},{\"kind\":\"symbol\",\"text\":\";\"},{\"kind\":\"symbol\",\"text\":\"}\"}]}";

#[test]
fn canonical_bytes_and_digest_are_fixed_for_unicode_and_control_characters() {
    let tokens = lexer::lex(UNICODE_LAW.as_bytes()).unwrap();
    assert_eq!(model_canonical(&tokens), UNICODE_CANONICAL);
    let c = ok(EMPTY_DEFINITION, UNICODE_LAW);
    assert_eq!(
        c.model_digest,
        "sha256:f40552dcb0667d9f65aea50feca9ffc109077fe491405146fcc827124b5d1cfd"
    );
    let nfc = UNICODE_LAW.replace("e\u{301}", "\u{e9}");
    assert_eq!(
        ok(EMPTY_DEFINITION, &nfc).model_digest,
        "sha256:6c68acdc082ea6f21074f7d7734e61a8106a5eb337526230100710d9b8a2272c"
    );
}

/// 原始 manifest は独立定義の meaning・version・dependency を含む。
#[test]
fn manifest_has_every_field_in_canonical_form() {
    let c = ok(RESERVATIONS_DEFINITION, RESERVATIONS);
    let v = &c.definitions.vocabularies["Reservations"];
    assert_eq!(v.namespace, "Reservations");
    let text = v.manifest.canonical();
    assert_eq!(text, include_str!("fixtures/reservations.manifest.json"));
    assert_eq!(
        v.digest,
        "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff"
    );
    assert_eq!(v.digest, sha256_digest(text.as_bytes()));
}

#[test]
fn definition_meaning_and_version_change_vocabulary_identity_and_reject_old_imports() {
    use archsig::issue::Code;
    let base = definitions_ok(&[COUNTER_DEFINITION]);
    let changed =
        COUNTER_DEFINITION.replace("実装中の一つのカウンタ状態。", "変更したカウンタ状態。");
    assert_ne!(changed, COUNTER_DEFINITION);
    let c = definitions_ok(&[&changed]);
    assert_ne!(
        c.vocabularies["Counter"].digest,
        base.vocabularies["Counter"].digest
    );
    assert_eq!(err(&changed, COUNTER).code, Code::VocabularyMismatch);
    let version = COUNTER_DEFINITION.replace("\"version\": \"1\"", "\"version\": \"2\"");
    assert_ne!(version, COUNTER_DEFINITION);
    let c = definitions_ok(&[&version]);
    assert_ne!(
        c.vocabularies["Counter"].digest,
        base.vocabularies["Counter"].digest
    );
    assert_eq!(err(&version, COUNTER).code, Code::VocabularyMismatch);
}
