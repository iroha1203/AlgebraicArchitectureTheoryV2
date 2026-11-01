//! 複数の統合テストで一字一句同じだった補助関数。

use archsig::canonical::Json;
use archsig::control::{Checkpoint, Control};
use archsig::input::CheckedInputs;
use archsig::result::Signal;
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

pub fn add(a: &str, subject: &str, ty: &str) -> String {
    a.replace(
        "\"subjects\": [",
        &format!(
            "\"subjects\": [\n{{\"id\":\"{subject}\",\"type\":\"{ty}\",\"origin\":\"model\"}},"
        ),
    )
}

pub fn arr(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else {
        panic!("array: {j:?}")
    };
    v
}

pub fn array(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!() };
    a
}

pub fn data(tag: &str, args: Vec<Json>) -> Json {
    Json::obj([("tag", Json::str(tag)), ("args", Json::Arr(args))])
}

pub fn edit(map: &str, id: &str, before: &str, after: &str) -> String {
    let key = format!("\"id\":\"{id}\"");
    assert_eq!(map.lines().filter(|l| l.contains(&key)).count(), 1);
    map.lines()
        .map(|l| {
            if l.contains(&key) {
                assert!(l.contains(before));
                l.replace(before, after)
            } else {
                l.into()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn fact(snapshot: &str, subject: &str, field: &str) -> Json {
    Json::obj([
        ("snapshot", Json::str(snapshot)),
        ("subject", Json::str(subject)),
        ("field", Json::str(format!("Affine.Sample.{field}"))),
    ])
}

pub fn fp() -> Json {
    Json::Arr(vec![Json::str("Fp"), Json::str("5")])
}

pub fn get<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!("object") };
    &m[k]
}

pub fn links(j: &Json, rs: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => rs.push(txt(&m["node"]).into()),
        Json::Obj(m) => {
            for v in m.values() {
                links(v, rs);
            }
        }
        Json::Arr(v) => {
            for j in v {
                links(j, rs);
            }
        }
        _ => {}
    }
}

pub fn member_key(t: &Json, value: &Json) -> String {
    if let Json::Arr(parts) = t
        && parts.first() == Some(&Json::str("Set"))
    {
        let mut values = arr(value).iter().map(Json::canonical).collect::<Vec<_>>();
        values.sort();
        format!("{values:?}")
    } else {
        value.canonical()
    }
}

pub fn numbers(values: &[&str]) -> Json {
    Json::Arr(values.iter().map(|v| Json::str(*v)).collect())
}

pub fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(v) = j else {
        panic!("object: {j:?}")
    };
    v
}

pub fn object(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(x) = j else {
        panic!("object: {j:?}")
    };
    x
}

pub fn probe(point: Checkpoint, at: usize) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(move |current| {
        if current == point {
            seen.set(seen.get() + 1);
        }
        (seen.get() == at).then_some(Signal::Term)
    });
    (control, count)
}

pub fn q(n: &str, d: &str) -> Json {
    Json::Arr(vec![Json::str(n), Json::str(d)])
}

pub fn reached(ns: &BTreeMap<&str, &Json>, roots: &[&Json]) -> BTreeSet<String> {
    let mut todo = vec![];
    for root in roots {
        refs(root, &mut todo);
    }
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            refs(ns[id.as_str()], &mut todo);
        }
    }
    seen
}

pub fn reference(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
}

pub fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => {
            for value in m.values() {
                refs(value, out);
            }
        }
        Json::Arr(a) => {
            for value in a {
                refs(value, out);
            }
        }
        _ => {}
    }
}

pub fn remove(map: &str, id: &str) -> String {
    let key = format!("\"id\":\"{id}\"");
    assert_eq!(map.lines().filter(|l| l.contains(&key)).count(), 1);
    map.lines()
        .filter(|l| !l.contains(&key))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}

pub fn source<'a>(checked: &'a CheckedInputs, at: (usize, usize)) -> &'a [u8] {
    &checked.sources().law().bytes()[at.0..at.1]
}

pub fn stop_at(point: Checkpoint, at: usize, signal: Signal) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let c = Control::new(move |p| {
        if p == point {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= at).then_some(signal)
    });
    (c, count)
}

pub fn text(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("string: {j:?}")
    };
    v
}

pub fn tuple_type() -> Json {
    Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Z"),
        Json::str("Q"),
        fp(),
    ])
}

pub fn txt(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("string {j:?}")
    };
    v
}

pub fn ty(kind: &str, item: Json) -> Json {
    Json::Arr(vec![Json::str(kind), item])
}
