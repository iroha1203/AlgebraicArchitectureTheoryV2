//! 検査済みLawとArchMapの公開読取API。
use archsig::{archmap::check_archmap, definition::check_definitions, law::check_law};
const DEFINITIONS: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const LAW: &[u8] = include_bytes!("fixtures/counter.law");
const MAP: &[u8] = include_bytes!("fixtures/counter.archmap.json");

#[test]
fn checked_law_readers_preserve_arenas_types_declarations_and_identity() {
    let definitions = check_definitions(&[("definition0", DEFINITIONS)]).unwrap();
    let law = check_law(LAW, &definitions).unwrap();
    assert_eq!(law.bytes_digest(), archsig::canonical::sha256_digest(LAW));
    assert_eq!(
        law.model_digest(),
        archsig::law::model_digest(&archsig::law::lexer::lex(LAW).unwrap())
    );
    assert_eq!(law.definitions(), &definitions);
    assert!(law.declarations().contains_key("CountCheck.amount"));
    assert!(!law.infos().is_empty());
    assert!(!law.exprs().is_empty());
    assert_eq!(law.expr_types().len(), law.exprs().len());
    for (id, ty) in law.expr_types().iter().enumerate() {
        assert_eq!(law.expr_type(id), ty.as_ref());
    }
    assert!(law.expr_type(usize::MAX).is_none());
    let mut detached = law.declarations().clone();
    detached.clear();
    assert!(law.declarations().contains_key("CountCheck.amount"));
    let mut infos = law.infos().to_vec();
    infos.clear();
    assert!(!law.infos().is_empty());
}

#[test]
fn checked_archmap_readers_preserve_observations_provenance_and_identity() {
    let definitions = check_definitions(&[("definition0", DEFINITIONS)]).unwrap();
    let map = check_archmap(MAP, &definitions).unwrap();
    assert_eq!(map.bytes_digest(), archsig::canonical::sha256_digest(MAP));
    assert!(map.model_digest().starts_with("sha256:"));
    assert_eq!(
        map.vocabularies()["Counter"].digest,
        definitions.vocabularies()["Counter"].digest
    );
    assert!(map.sources().is_empty());
    assert_eq!(map.origins()[0].id, "model");
    assert_eq!(map.snapshots()[0].id, "v");
    assert_eq!(map.snapshots()[0].subjects[0].ty, "Counter.State");
    let mut detached = map.vocabularies().clone();
    detached.clear();
    assert_eq!(map.vocabularies().len(), 1);
}

#[test]
fn from_checked_rejects_valid_law_or_archmap_from_different_input_bytes() {
    use archsig::{
        control::Control,
        input::{CheckedInputs, InputSources, InputStatus},
    };
    for change_law in [true, false] {
        let definitions = check_definitions(&[("definition0", DEFINITIONS)]).unwrap();
        let other_law = String::from_utf8(LAW.to_vec())
            .unwrap()
            .replace(">= 0", ">= 1");
        let other_map = String::from_utf8(MAP.to_vec())
            .unwrap()
            .replace("\"value\": \"2\"", "\"value\": \"3\"");
        assert_ne!(other_law.as_bytes(), LAW);
        assert_ne!(other_map.as_bytes(), MAP);
        let law = check_law(
            if change_law {
                other_law.as_bytes()
            } else {
                LAW
            },
            &definitions,
        )
        .unwrap();
        let map = check_archmap(
            if change_law {
                MAP
            } else {
                other_map.as_bytes()
            },
            &definitions,
        )
        .unwrap();
        let sources =
            InputSources::from_bytes(vec![DEFINITIONS.to_vec()], LAW.to_vec(), MAP.to_vec());
        let failure =
            CheckedInputs::from_checked(sources, definitions, law, map, &Control::unlimited())
                .unwrap_err();
        assert_eq!(failure.status(), InputStatus::Invalid);
        assert_eq!(failure.declarations().is_empty(), change_law);
    }
}
