//! 結果(設計 §8、マニュアル第6章)。結論をサマリと詳細にまとめる。ファイルに書くのは `archmap` である。

use std::collections::BTreeMap;

use serde_json::{Value as Json, json};

use crate::engine::Finding;

/// 読む所: ソース、範囲、要素。
type NextKey = (Option<String>, Option<String>, Option<String>);

/// 実行 `run` の結論を、サマリと結論ごとの詳細にする。詳細の番号は 1 から。
pub fn summarize(run: &str, command: &str, findings: &[Finding], not_computed: &[String]) -> (Json, Vec<Json>) {
    let mut results = Vec::new();
    let mut details = Vec::new();
    // 沈黙の `next` は、読む所ごとにまとめる。
    let mut next: BTreeMap<NextKey, Vec<String>> = BTreeMap::new();
    for (i, f) in findings.iter().enumerate() {
        let id = format!("{run}/{}", i + 1);
        let mut row = json!({"id": id, "question": f.question, "law": f.law, "subject": f.subject, "outcome": f.outcome, "at": f.at});
        if let Some(k) = f.kind {
            row["kind"] = json!(k);
        }
        if let Some(r) = f.reason {
            row["reason"] = json!(r);
        }
        let mut detail = row.clone();
        detail["basis"] = f.basis.clone();
        detail["check"] = f.check.clone();
        detail["conditions"] = json!(f.conditions);
        detail["theory"] = json!(f.theory);
        let mut own: Vec<Json> = Vec::new();
        for n in &f.next {
            let j = next_json(n);
            if !own.contains(&j) {
                own.push(j);
            }
            let decides = next.entry((n.read.clone(), n.scope.clone(), n.element.clone())).or_default();
            if !decides.contains(&id) {
                decides.push(id.clone());
            }
        }
        detail["next"] = Json::Array(own);
        results.push(row);
        details.push(detail);
    }
    let next: Vec<Json> = next
        .into_iter()
        .map(|((read, scope, element), decides)| {
            let mut n = json!({"decides": decides});
            if let Some(r) = read {
                n["read"] = json!(r);
            }
            if let Some(s) = scope {
                n["scope"] = json!(s);
            }
            if let Some(e) = element {
                n["element"] = json!(e);
            }
            n
        })
        .collect();
    (json!({"run": run, "command": command, "results": results, "next": next, "not_computed": not_computed}), details)
}

fn next_json(s: &crate::structure::Silence) -> Json {
    let mut n = json!({});
    if let Some(r) = &s.read {
        n["read"] = json!(r);
    }
    if let Some(sc) = &s.scope {
        n["scope"] = json!(sc);
    }
    if let Some(e) = &s.element {
        n["element"] = json!(e);
    }
    n
}
