//! 原始定義の所属・対応・型適格性の小さい回帰確認。
mod common;
use archsig::issue::Code;
use common::law_definitions::*;
use common::*;
fn rejects_definition(src: &str, code: Code) {
    let f = archsig::definition::check_definitions(&[("definition0", src.as_bytes())])
        .expect_err("不正な原始定義");
    assert_eq!(f.issue.code, code);
    assert!(matches!(
        f.issue.location,
        archsig::issue::Location::Definition { .. }
    ));
}
#[test]
fn primitive_collisions_recursion_and_type_positions_are_rejected() {
    rejects_definition(DEF_00, Code::DuplicateId);
    rejects_definition(DEF_01, Code::DuplicateId);
    rejects_definition(DEF_02, Code::DuplicateId);
    rejects_definition(DEF_05, Code::Syntax);
    rejects_definition(DEF_11, Code::Cycle);
    rejects_definition(DEF_13, Code::Syntax);
    rejects_definition(DEF_14, Code::Syntax);
    rejects_definition(DEF_15, Code::Syntax);
    rejects_definition(DEF_16, Code::Syntax);
    rejects_definition(DEF_17, Code::Syntax);
    rejects_definition(DEF_19, Code::Syntax);
    rejects_definition(DEF_20, Code::Syntax);
    rejects_definition(DEF_21, Code::Syntax);
    rejects_definition(DEF_22, Code::Syntax);
    rejects_definition(DEF_26, Code::Syntax);
}
#[test]
fn alignment_moves_references_and_positions_quantities() {
    definitions_ok(&[DEF_50]);
    rejects_definition(DEF_52, Code::Type);
}
#[test]
fn correspondence_covers_every_owned_type_of_its_roots() {
    definitions_ok(&[DEF_54]);
    rejects_definition(DEF_56, Code::Syntax);
}
#[test]
fn correspondence_incomplete_owned_roster_is_rejected() {
    rejects_definition(DEF_57, Code::Syntax);
}

#[test]
fn correspondence_covers_owned_types_in_other_namespaces() {
    let src = include_str!("fixtures/owned-cross-namespace.atoms.json");
    rejects_definition(src, Code::Syntax);
}
