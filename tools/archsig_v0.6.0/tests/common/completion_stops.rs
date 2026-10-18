//! 実際に保持された補完caseからExpression停止点を特定する。再検査のprobeも数え、固定回数を仮定しない。
use archsig::{
    canonical::Json,
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    },
    result::Signal,
};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};
fn object(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(v) = j else { panic!("object") };
    v
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else { panic!("array") };
    v
}
fn string(j: &Json) -> &str {
    let Json::Str(v) = j else { panic!("string") };
    v
}
/// 最初に各wanted個の検査済みcaseが残り、whole証拠が未生成である実停止点を選ぶ。
/// 検索範囲は同じ入力の正常実行で実際に観測したExpression checkpointだけとする。
pub fn offsets(
    input: &InputSources,
    asks: &[&str],
    before: usize,
    total: usize,
    span: (usize, usize),
    wanted: &[usize],
) -> Vec<usize> {
    assert!(total > before);
    let mut found = BTreeMap::new();
    for offset in 1..=total - before {
        let at = before + offset;
        let expressions = Rc::new(Cell::new(0));
        let e = expressions.clone();
        let probes = Rc::new(Cell::new(0));
        let p = probes.clone();
        let frozen = Rc::new(Cell::new(None));
        let f = frozen.clone();
        let mut control = Control::new(Limits::default(), move |point| {
            p.set(p.get() + 1);
            if point == Checkpoint::Expression {
                e.set(e.get() + 1);
                if e.get() == at {
                    assert!(f.replace(Some(p.get())).is_none());
                    return Usage {
                        signal: Some(Signal::Term),
                        ..Usage::default()
                    };
                }
            }
            Usage::default()
        });
        let result = evaluate_observed_bytes(input.clone(), asks, &mut control).unwrap();
        assert_eq!(result.status(), "interrupted");
        assert_eq!(expressions.get(), at);
        assert_eq!(Some(probes.get()), frozen.get());
        let wire = result.wire();
        let root = object(&wire);
        let nodes = array(&root["nodes"]);
        let by: BTreeMap<_, _> = nodes
            .iter()
            .map(|n| (string(&object(n)["id"]), n))
            .collect();
        let mut ids = BTreeSet::new();
        let mut done = 0;
        let mut missing = 0;
        for n in nodes {
            let n = object(n);
            if n["type"] != Json::str("Evaluation") {
                continue;
            }
            let value = object(&n["value"]);
            let expression = object(by[string(&object(&value["expression"])["node"])]);
            let source = object(&expression["value"]);
            let location = object(&source["location"]);
            let at = array(&location["span"]);
            if at != [Json::Nat(span.0 as u64), Json::Nat(span.1 as u64)] {
                continue;
            }
            ids.insert(string(&n["id"]));
            if value.contains_key("value") {
                done += 1;
            } else {
                missing += 1;
            }
        }
        if missing == 0 || !wanted.contains(&done) || found.contains_key(&done) {
            continue;
        }
        let complete = nodes.iter().any(|n| {
            let n = object(n);
            if n["type"] != Json::str("Evidence") {
                return false;
            }
            let value = object(&n["value"]);
            let kind = string(&value["kind"]);
            if !["finite_exhaustion", "completion_pair"].contains(&kind) {
                return false;
            }
            let data = object(&value["data"]);
            if kind == "finite_exhaustion" {
                array(&data["instances"])
                    .iter()
                    .any(|r| ids.contains(string(&object(r)["node"])))
            } else {
                ["first_result", "second_result"]
                    .iter()
                    .any(|k| ids.contains(string(&object(&data[*k])["node"])))
            }
        });
        let current = array(&root["answers"])
            .iter()
            .find(|a| object(a)["id"] == Json::str("current"))
            .unwrap();
        if complete || !object(&object(current)["outputs"]).is_empty() {
            continue;
        }
        found.insert(done, offset);
        if found.len() == wanted.len() {
            break;
        }
    }
    wanted
        .iter()
        .map(|n| {
            *found.get(n).unwrap_or_else(|| {
                panic!("実Expression停止点で{n}個のcaseを保持できない: {found:?}")
            })
        })
        .collect()
}
