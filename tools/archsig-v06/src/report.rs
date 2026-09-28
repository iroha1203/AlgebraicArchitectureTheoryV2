//! 第6章の結果。サマリと、結論ごとの詳細。

use std::collections::BTreeMap;
use std::path::Path;

use serde_json::{Map, Value, json};

/// 一つの結論。
#[derive(Clone, Debug, Default)]
pub struct Finding {
    pub question: String,
    pub law: Option<String>,
    pub subject: String,
    pub outcome: String,
    pub kind: Option<String>,
    pub reason: Option<String>,
    pub at: Vec<String>,
    pub basis: Vec<Value>,
    pub check: Value,
    pub conditions: Vec<String>,
    pub theory: Vec<String>,
    /// 沈黙したとき、何を読めば決まるか。`(ソースか要素, 範囲)`。
    pub next: Vec<(String, String)>,
}

impl Finding {
    pub fn new(question: &str, law: Option<&str>, subject: &str) -> Finding {
        Finding {
            question: question.to_string(),
            law: law.map(str::to_string),
            subject: subject.to_string(),
            check: Value::Null,
            ..Finding::default()
        }
    }

    pub fn holds(mut self) -> Finding {
        self.outcome = "holds".to_string();
        self
    }

    pub fn fails(mut self, kind: &str) -> Finding {
        self.outcome = "fails".to_string();
        self.kind = Some(kind.to_string());
        self
    }

    pub fn silent(mut self, reason: &str) -> Finding {
        self.outcome = "silent".to_string();
        self.reason = Some(reason.to_string());
        self
    }

    fn summary(&self, id: &str) -> Value {
        let mut m = Map::new();
        m.insert("id".into(), json!(id));
        m.insert("question".into(), json!(self.question));
        if let Some(l) = &self.law {
            m.insert("law".into(), json!(l));
        }
        m.insert("subject".into(), json!(self.subject));
        m.insert("outcome".into(), json!(self.outcome));
        if let Some(k) = &self.kind {
            m.insert("kind".into(), json!(k));
        }
        if let Some(r) = &self.reason {
            m.insert("reason".into(), json!(r));
        }
        if !self.at.is_empty() {
            m.insert("at".into(), json!(self.at));
        }
        Value::Object(m)
    }

    fn detail(&self, id: &str) -> Value {
        let mut v = self.summary(id);
        let m = v.as_object_mut().unwrap();
        if !self.basis.is_empty() {
            m.insert("basis".into(), json!(self.basis));
        }
        if !self.check.is_null() {
            m.insert("check".into(), self.check.clone());
        }
        if !self.conditions.is_empty() {
            m.insert("conditions".into(), json!(self.conditions));
        }
        if !self.theory.is_empty() {
            m.insert("theory".into(), json!(self.theory));
        }
        if !self.next.is_empty() {
            let next: Vec<Value> = self.next.iter().map(|(r, s)| json!({"read": r, "scope": s})).collect();
            m.insert("next".into(), json!(next));
        }
        v
    }
}

/// 実行を `.archsig/runs/<r-id>/` に書き、サマリを返す。
pub fn write_run(archsig_dir: &Path, command: &str, findings: &[Finding], extra: Option<Value>) -> Result<Value, String> {
    let runs = archsig_dir.join("runs");
    std::fs::create_dir_all(&runs).map_err(|e| e.to_string())?;
    let n = std::fs::read_dir(&runs)
        .map_err(|e| e.to_string())?
        .filter_map(|e| e.ok())
        .filter_map(|e| e.file_name().to_str()?.strip_prefix("r-")?.parse::<u32>().ok())
        .max()
        .unwrap_or(0)
        + 1;
    let run = format!("r-{n:04}");
    let dir = runs.join(&run);
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let mut results = Vec::new();
    let mut next: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
    for (i, f) in findings.iter().enumerate() {
        let id = format!("{run}/{}", i + 1);
        results.push(f.summary(&id));
        let detail = serde_json::to_string_pretty(&f.detail(&id)).unwrap();
        std::fs::write(dir.join(format!("{}.json", i + 1)), detail).map_err(|e| e.to_string())?;
        for key in &f.next {
            next.entry(key.clone()).or_default().push(id.clone());
        }
    }
    let mut next: Vec<((String, String), Vec<String>)> = next.into_iter().collect();
    next.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(&b.0)));
    let next: Vec<Value> = next.into_iter().map(|((r, s), ids)| json!({"read": r, "scope": s, "decides": ids})).collect();
    let mut summary = json!({"run": run, "command": command, "results": results});
    if !next.is_empty() {
        summary["next"] = json!(next);
    }
    if let Some(Value::Object(extra)) = extra {
        for (k, v) in extra {
            summary[k] = v;
        }
    }
    std::fs::write(dir.join("summary.json"), serde_json::to_string_pretty(&summary).unwrap()).map_err(|e| e.to_string())?;
    Ok(summary)
}

pub fn show(archsig_dir: &Path, id: &str) -> Result<Value, String> {
    let (run, n) = id.split_once('/').ok_or("結果は r-0001/1 の形で指定する")?;
    let path = archsig_dir.join("runs").join(run).join(format!("{n}.json"));
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{id}: {e}"))?;
    serde_json::from_str(&text).map_err(|e| e.to_string())
}
