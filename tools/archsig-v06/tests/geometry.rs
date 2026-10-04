//! 設計 §6、マニュアル第4章: 読みが写す局所と、要素と Atom が属する局所。

use std::collections::BTreeSet;

use archsig::atom::parse_jsonl;
use archsig::geometry::{Geometry, local};
use archsig::law::{Reading, ReadingForm};

fn reading(form: ReadingForm) -> Reading {
    Reading { name: "r".to_string(), form, at: "test.law:1".to_string() }
}

#[test]
fn a_dir_reading_cuts_directories_from_the_top() {
    let r = reading(ReadingForm::Dir { depth: 2 });
    assert_eq!(local(&r, "shop/shipping/model/address.py").as_deref(), Some("shop/shipping"));
    // `n` 段に満たない所にあるファイルは、そのファイルのディレクトリを局所にする。
    assert_eq!(local(&r, "shop/main.py").as_deref(), Some("shop"));
}

#[test]
fn a_file_reading_makes_each_file_a_local() {
    assert_eq!(local(&reading(ReadingForm::File), "shop/shipping/service.py").as_deref(), Some("shop/shipping/service.py"));
}

#[test]
fn groups_are_tried_from_the_top() {
    let r = reading(ReadingForm::Groups {
        groups: vec![
            ("shipping".to_string(), vec!["shop/shipping/**".to_string(), "shop/address/**".to_string()]),
            ("rest".to_string(), vec!["**".to_string()]),
        ],
    });
    assert_eq!(local(&r, "shop/address/normalize.py").as_deref(), Some("shipping"));
    assert_eq!(local(&r, "shop/payment/service.py").as_deref(), Some("rest"));
    let only = reading(ReadingForm::Groups { groups: vec![("shipping".to_string(), vec!["shop/shipping/**".to_string()])] });
    assert_eq!(local(&only, "shop/payment/service.py"), None);
}

#[test]
fn a_channel_belongs_to_the_locals_of_its_senders_and_receivers() {
    let atoms = parse_jsonl(
        r#"{"kind": "defines", "subject": "shop.order.place", "value": "operation", "at": "shop/order/service.py:1@blob:aaaaaaa"}
{"kind": "sends", "subject": "shop.order.place", "object": "channel:queue:order-placed:amount", "value": "$o.total", "at": "shop/order/service.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "shop.payment.charge", "value": "operation", "at": "shop/payment/service.py:1@blob:bbbbbbb"}
{"kind": "receives", "subject": "shop.payment.charge", "object": "channel:queue:order-placed:amount", "value": "$amount", "at": "shop/payment/service.py:2@blob:bbbbbbb"}
{"kind": "defines", "subject": "lib.external", "value": "operation", "file": "vendor/lib.py", "at": "plan:p"}
"#,
        "test",
    )
    .unwrap();
    let r = reading(ReadingForm::Dir { depth: 2 });
    let g = Geometry::new(&r, &atoms, &atoms, &Default::default());
    let both: BTreeSet<String> = ["shop/order", "shop/payment"].iter().map(|s| s.to_string()).collect();
    assert_eq!(g.element_locals("channel:queue:order-placed:amount"), both);
    assert_eq!(g.element_locals("channel:queue:order-placed"), both);
    // 送る Atom は、送る操作の局所とチャネルの局所すべてに属する。
    assert_eq!(g.atom_locals(&atoms[1]), both);
    // 候補の中で定義した要素は `file` の局所に属する。定義を観測していない要素は、どの局所にも属さない。
    assert_eq!(g.element_locals("lib.external").into_iter().collect::<Vec<_>>(), ["vendor"]);
    assert!(g.element_locals("shop.unknown.f").is_empty());
}
