//! Atom から組み立てる要素、操作、局所。

use std::collections::{BTreeMap, BTreeSet};

use crate::atom::Atom;
use crate::law::{Reading, ReadingKind};
use crate::store;

/// 操作の中の一歩。書き込みか呼び出し。
#[derive(Clone, Debug)]
pub enum Step {
    Write(Atom),
    Call { atom: Atom, element: String },
}

#[derive(Clone, Debug, Default)]
pub struct Model {
    pub atoms: Vec<Atom>,
    /// 要素の名前から、その `defines`。
    pub defines: BTreeMap<String, Atom>,
    /// 操作の名前から、書き込みと呼び出しを順に並べたもの。
    pub steps: BTreeMap<String, Vec<Step>>,
    /// 呼び出しの名前から、その `passes`。
    pub passes: BTreeMap<String, Vec<Atom>>,
    /// 構造を読んだソース。
    pub read_structure: BTreeSet<String>,
    /// 意味ごとに、読んだソース。
    pub read_meaning: BTreeMap<String, BTreeSet<String>>,
}

impl Model {
    pub fn new(atoms: Vec<Atom>) -> Model {
        let mut m = Model::default();
        let mut per_op: BTreeMap<String, Vec<(u32, usize, Atom)>> = BTreeMap::new();
        for (i, a) in atoms.iter().enumerate() {
            match a.kind.as_str() {
                "defines" => {
                    m.defines.insert(a.subject.clone(), a.clone());
                }
                "writes" | "calls" => {
                    let line = a.location().and_then(|l| l.line).unwrap_or(0);
                    per_op.entry(a.subject.clone()).or_default().push((line, i, a.clone()));
                }
                "passes" => m.passes.entry(a.subject.clone()).or_default().push(a.clone()),
                "observed" => {
                    let scope = a.scope.clone().unwrap_or_default();
                    if scope == "structure" {
                        m.read_structure.insert(a.subject.clone());
                    } else if let Some(meaning) = scope.strip_prefix("meaning:") {
                        m.read_meaning.entry(meaning.to_string()).or_default().insert(a.subject.clone());
                    }
                }
                _ => {}
            }
        }
        for (op, mut list) in per_op {
            list.sort_by_key(|(line, i, _)| (*line, *i));
            let mut count: BTreeMap<String, usize> = BTreeMap::new();
            let steps = list
                .into_iter()
                .map(|(_, _, a)| {
                    if a.kind == "calls" {
                        let callee = a.object.clone().unwrap_or_default();
                        let n = count.entry(callee.clone()).or_default();
                        *n += 1;
                        let element = if *n == 1 { format!("{op}->{callee}") } else { format!("{op}->{callee}#{n}") };
                        Step::Call { atom: a, element }
                    } else {
                        Step::Write(a)
                    }
                })
                .collect();
            m.steps.insert(op, steps);
        }
        m.atoms = atoms;
        m
    }

    pub fn is_operation(&self, name: &str) -> bool {
        self.defines.get(name).is_some_and(|d| d.value.as_deref() == Some("operation"))
    }

    pub fn is_field(&self, name: &str) -> bool {
        self.defines.get(name).is_some_and(|d| d.value.as_deref() == Some("field"))
    }

    pub fn operations(&self) -> impl Iterator<Item = &String> {
        self.defines.iter().filter(|(_, d)| d.value.as_deref() == Some("operation")).map(|(n, _)| n)
    }

    pub fn params(&self, op: &str) -> BTreeMap<String, String> {
        self.defines.get(op).and_then(|d| d.params.clone()).unwrap_or_default()
    }

    /// 要素の名前すべて。定義した要素と、操作の引数。
    pub fn elements(&self) -> BTreeSet<String> {
        let mut out: BTreeSet<String> = self.defines.keys().cloned().collect();
        for op in self.operations() {
            for p in self.params(op).keys() {
                out.insert(format!("{op}.${p}"));
            }
        }
        out
    }

    /// 要素の型。フィールドは宣言した型、引数は操作の `params` の型。
    pub fn type_of(&self, element: &str) -> Option<String> {
        if let Some(d) = self.defines.get(element) {
            return d.ty.clone();
        }
        let (op, p) = element.rsplit_once(".$")?;
        self.params(op).get(p).cloned()
    }

    /// 要素を置くソース。候補の中で新しく定義した要素は `file`。
    pub fn source_of(&self, element: &str) -> Option<String> {
        let owner = element.split("->").next().unwrap_or(element);
        let owner = owner.split(".$").next().unwrap_or(owner);
        let d = self.defines.get(owner)?;
        if let Some(f) = &d.file {
            return Some(f.clone());
        }
        d.location().map(|l| l.path).filter(|p| !p.starts_with("plan:"))
    }

    /// 定義を読んでいない要素について、読めば決まりそうなソース。
    /// ソースのパスを `.` でつないだ名前が、要素の名前の頭に当たるものを選ぶ。
    pub fn unread_source_for(&self, element: &str, sources: &[String]) -> Option<String> {
        for s in sources {
            if self.read_structure.contains(s) {
                continue;
            }
            let stem = s.rsplit_once('.').map(|(a, _)| a).unwrap_or(s);
            let parts: Vec<&str> = stem.split('/').collect();
            for k in 0..parts.len() {
                let module = parts[k..].join(".");
                if element.starts_with(&format!("{module}.")) {
                    return Some(s.clone());
                }
            }
        }
        None
    }

    /// 意味 Atom。`(要素, 意味, 値)`。
    pub fn meanings(&self) -> impl Iterator<Item = &Atom> {
        self.atoms.iter().filter(|a| a.kind == "meaning")
    }

    pub fn has_meaning(&self, element: &str, meaning: &str) -> bool {
        self.meanings().any(|a| a.subject == element && a.meaning.as_deref() == Some(meaning))
    }
}

/// 読みで、ソースのパスを局所の名前にする。
pub fn local_of(reading: &Reading, path: &str) -> Option<String> {
    match &reading.kind {
        ReadingKind::File => Some(path.to_string()),
        ReadingKind::Dir(depth) => {
            let dirs: Vec<&str> = path.split('/').collect();
            let dirs = &dirs[..dirs.len().saturating_sub(1)];
            if dirs.is_empty() {
                return Some(".".to_string());
            }
            Some(dirs[..(*depth).min(dirs.len())].join("/"))
        }
        ReadingKind::Groups(groups) => {
            for (name, pats) in groups {
                if store::globs(pats).ok()?.is_match(path) {
                    return Some(name.clone());
                }
            }
            None
        }
    }
}
