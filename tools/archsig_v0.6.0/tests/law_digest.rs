//! AC5(Law 側): bytes_digest・model_digest・語彙 digest の区別と、文字列を正規化しない canonical bytes。

mod common;
use archsig::canonical::sha256_digest;
use archsig::law::{lexer, model_canonical};
use common::*;

fn digests(src: &str) -> (String, String, Vec<String>) {
    let c = ok(src);
    (
        c.bytes_digest,
        c.model_digest,
        c.vocabularies.iter().map(|v| v.digest.clone()).collect(),
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
    let primitive = digests(
        &RESERVATIONS.replace("{ free: Z; held: Z; }", "{ free: Z; held: Z; note: Text; }"),
    );
    assert_ne!(primitive.2, base.2, "原始宣言の変更は語彙 digest を変える");
}

/// 文字列は escape を解いた値を保ち、NFC/NFD を同一視しない。制御文字は \u00xx。
const UNICODE_LAW: &str = "law \"archsig.law/1\" semantics \"archsig/0.6.0\";\nreading U { view t(): List<Text> = list<Text>[\"\u{e9}\", \"e\u{301}\", \"\\u0001\\n\\\"\\\\/\\u007f\", \"\\ud83d\\ude00\", \"\\/\"]; }\n";

const UNICODE_CANONICAL: &str = "{\"semantics\":\"archsig/0.6.0\",\"tokens\":[{\"kind\":\"name\",\"text\":\"law\"},{\"kind\":\"string\",\"text\":\"archsig.law/1\"},{\"kind\":\"name\",\"text\":\"semantics\"},{\"kind\":\"string\",\"text\":\"archsig/0.6.0\"},{\"kind\":\"symbol\",\"text\":\";\"},{\"kind\":\"name\",\"text\":\"reading\"},{\"kind\":\"name\",\"text\":\"U\"},{\"kind\":\"symbol\",\"text\":\"{\"},{\"kind\":\"name\",\"text\":\"view\"},{\"kind\":\"name\",\"text\":\"t\"},{\"kind\":\"symbol\",\"text\":\"(\"},{\"kind\":\"symbol\",\"text\":\")\"},{\"kind\":\"symbol\",\"text\":\":\"},{\"kind\":\"name\",\"text\":\"List\"},{\"kind\":\"symbol\",\"text\":\"<\"},{\"kind\":\"name\",\"text\":\"Text\"},{\"kind\":\"symbol\",\"text\":\">\"},{\"kind\":\"symbol\",\"text\":\"=\"},{\"kind\":\"name\",\"text\":\"list\"},{\"kind\":\"symbol\",\"text\":\"<\"},{\"kind\":\"name\",\"text\":\"Text\"},{\"kind\":\"symbol\",\"text\":\">\"},{\"kind\":\"symbol\",\"text\":\"[\"},{\"kind\":\"string\",\"text\":\"\u{e9}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"e\u{301}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"\\u0001\\u000a\\\"\\\\/\u{7f}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"\u{1f600}\"},{\"kind\":\"symbol\",\"text\":\",\"},{\"kind\":\"string\",\"text\":\"/\"},{\"kind\":\"symbol\",\"text\":\"]\"},{\"kind\":\"symbol\",\"text\":\";\"},{\"kind\":\"symbol\",\"text\":\"}\"}]}";

#[test]
fn canonical_bytes_and_digest_are_fixed_for_unicode_and_control_characters() {
    let tokens = lexer::lex(UNICODE_LAW.as_bytes()).unwrap();
    assert_eq!(model_canonical(&tokens), UNICODE_CANONICAL);
    let c = ok(UNICODE_LAW);
    assert_eq!(
        c.model_digest,
        "sha256:87db23edd3ff6175d8caa449944fe79ec8c3077bb93b176be844b484c7e4027c"
    );
    let nfc = UNICODE_LAW.replace("e\u{301}", "\u{e9}");
    assert_eq!(
        ok(&nfc).model_digest,
        "sha256:acd70eb520d5c457fb43751f0cd09a5b676558c01de639690fff1ecbd2a6b94d"
    );
}

/// 入力仕様 §4 から組み立てた Reservations の manifest。use・view・law・local・change は入らない。
const RESERVATIONS_MANIFEST: &str = "{\"declarations\":[{\"alignments\":[],\"fields\":[{\"name\":\"states\",\"type\":[\"Map\",[\"Owned\",\"Reservations.State\",\"from\"],[\"Owned\",\"Reservations.State\",\"to\"]]},{\"name\":\"reserves\",\"type\":[\"Map\",[\"Owned\",\"Reservations.Reserve\",\"from\"],[\"Owned\",\"Reservations.Reserve\",\"to\"]]}],\"kind\":\"correspondence\",\"name\":\"Reservations.Migration\",\"parameters\":[{\"name\":\"from\",\"type\":[\"Ref\",\"Reservations.System\"]},{\"name\":\"to\",\"type\":[\"Ref\",\"Reservations.System\"]}]},{\"alignments\":[],\"fields\":[],\"kind\":\"arrow\",\"name\":\"Reservations.Reserve\",\"parameters\":[{\"name\":\"owner\",\"type\":[\"Ref\",\"Reservations.System\"]},{\"name\":\"from\",\"type\":[\"Owned\",\"Reservations.State\",\"owner\"]},{\"name\":\"to\",\"type\":[\"Owned\",\"Reservations.State\",\"owner\"]}]},{\"alignments\":[],\"fields\":[{\"name\":\"free\",\"type\":\"Z\"},{\"name\":\"held\",\"type\":\"Z\"}],\"kind\":\"entity\",\"name\":\"Reservations.State\",\"parameters\":[{\"name\":\"owner\",\"type\":[\"Ref\",\"Reservations.System\"]}]},{\"alignments\":[],\"fields\":[],\"kind\":\"entity\",\"name\":\"Reservations.System\",\"parameters\":[]}],\"reading\":\"Reservations\",\"semantics\":\"archsig/0.6.0\"}";

#[test]
fn manifest_has_every_field_in_canonical_form() {
    let c = ok(RESERVATIONS);
    let v = &c.vocabularies[0];
    assert_eq!(v.reading, "Reservations");
    assert_eq!(v.manifest.canonical(), RESERVATIONS_MANIFEST);
    assert_eq!(v.digest, sha256_digest(RESERVATIONS_MANIFEST.as_bytes()));
}
