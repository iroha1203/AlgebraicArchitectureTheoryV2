use super::{Fact, FactData};
use archsig_common::canonical::Json;
use std::sync::Arc;
fn fact(snapshot: &str, subject: &str, field: Option<&str>, atom: Option<&str>) -> Fact {
    Fact::from(FactData {
        snapshot: snapshot.into(),
        subject: subject.into(),
        field: field.map(Into::into),
        atom: atom.map(Into::into),
    })
}
#[test]
fn fact_value_order_wire_debug_and_send_sync_survive_sharing() {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Fact>();
    assert_eq!(std::mem::size_of::<Fact>(), std::mem::size_of::<usize>());
    let fields = [
        ("s", "u", None, None),
        ("s", "u", Some("N.E.f"), None),
        ("s", "u", Some("N.E.f"), Some("a")),
        ("s", "u", Some("N.E.f"), Some("b")),
        ("s", "v", None, None),
        ("t", "u", None, None),
    ];
    for left in fields {
        for right in fields {
            let a = fact(left.0, left.1, left.2, left.3);
            let b = fact(right.0, right.1, right.2, right.3);
            assert_eq!(a == b, left == right);
            assert_eq!(a.cmp(&b), left.cmp(&right));
            if left == right {
                assert!(!Arc::ptr_eq(&a.0, &b.0));
                assert_eq!(a.wire(), b.wire());
            }
        }
    }
    let a = fact("s", "u", Some("N.E.f"), Some("a"));
    assert_eq!(
        a.wire(),
        Json::obj([
            ("snapshot", Json::str("s")),
            ("subject", Json::str("u")),
            ("field", Json::str("N.E.f")),
            ("atom", Json::str("a"))
        ])
    );
    let q = a.field.as_ref().unwrap();
    assert_eq!(q.namespace(), "N");
    assert_eq!(q.short(), "f");
    assert!(!q.is_owner());
    assert_eq!(
        format!("{:?}", fact("s", "u", None, None)),
        "Fact { snapshot: \"s\", subject: \"u\", field: None, atom: None }"
    );
}
#[test]
fn shared_fact_mutation_isolated_in_all_fields_and_unique_mutation_reuses_payload() {
    let original = fact("s", "u", Some("N.E.f"), Some("a"));
    let before = original.wire();
    let mut edited = original.clone();
    assert!(Arc::ptr_eq(&original.0, &edited.0));
    edited.snapshot = "t".into();
    edited.subject = "v".into();
    edited.field = Some("M.Other.owner".into());
    edited.atom = None;
    assert_eq!(original.wire(), before);
    assert!(!Arc::ptr_eq(&original.0, &edited.0));
    assert_eq!(original.field.as_ref().unwrap().namespace(), "N");
    assert!(edited.field.as_ref().unwrap().is_owner());
    assert_eq!(
        edited.wire(),
        Json::obj([
            ("snapshot", Json::str("t")),
            ("subject", Json::str("v")),
            ("field", Json::str("M.Other.owner"))
        ])
    );
    let unique = Arc::as_ptr(&edited.0);
    edited.atom = Some("b".into());
    assert_eq!(unique, Arc::as_ptr(&edited.0));
    let alias = edited.clone();
    edited.field = None;
    assert_eq!(alias.field.as_ref().unwrap().as_str(), "M.Other.owner");
    assert!(edited.field.is_none());
}

#[test]
fn consuming_unique_data_moves_strings_and_shared_data_keeps_alias_isolated() {
    let value = fact("s", "u", Some("N.E.f"), Some("a"));
    let snapshot_ptr = value.snapshot.as_ptr();
    let data = value.into_data();
    assert_eq!(snapshot_ptr, data.snapshot.as_ptr());
    let original = Fact::from(data);
    let before = original.wire();
    let mut consumed = original.clone().into_data();
    consumed.atom = None;
    consumed.subject = "v".into();
    assert_eq!(original.wire(), before);
    assert_eq!(consumed.subject, "v");
    assert!(consumed.atom.is_none());
}

#[test]
fn shared_payload_order_keeps_value_relations_sort_and_cow() {
    let original = fact("s", "u", Some("N.E.f"), Some("a"));
    let alias = original.clone();
    let independent = fact("s", "u", Some("N.E.f"), Some("a"));
    assert!(Arc::ptr_eq(&original.0, &alias.0));
    assert!(!Arc::ptr_eq(&original.0, &independent.0));
    let mut higher = original.clone();
    higher.atom = Some("z".into());
    let lower = fact("s", "t", Some("N.E.f"), Some("a"));
    let values = [&original, &alias, &independent, &higher, &lower];
    for a in values {
        for b in values {
            let expected = a.0.as_ref().cmp(b.0.as_ref());
            assert_eq!(a.cmp(b), expected);
            assert_eq!(a.partial_cmp(b), Some(expected));
            assert_eq!(a < b, expected.is_lt());
            assert_eq!(a <= b, expected.is_le());
            assert_eq!(a > b, expected.is_gt());
            assert_eq!(a >= b, expected.is_ge());
            assert_eq!(a == b, expected.is_eq());
        }
    }
    let mut unsorted = vec![
        higher.clone(),
        alias,
        lower.clone(),
        independent,
        original.clone(),
    ];
    unsorted.sort();
    assert_eq!(
        unsorted,
        vec![
            lower,
            original.clone(),
            original.clone(),
            original.clone(),
            higher
        ]
    );
    assert_eq!(original.atom.as_deref(), Some("a"));
}
