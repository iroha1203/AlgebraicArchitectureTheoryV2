//! 幾何(設計 §6、マニュアル第4章)。読みと Atom から、局所と重なりを作る。

use std::collections::{BTreeMap, BTreeSet};

use globset::{GlobBuilder, GlobSetBuilder};

use crate::atom::{Atom, parse_location};
use crate::law::{Reading, ReadingForm};
use crate::structure::{Resolution, Silence, Structure};

/// 読み `reading` が、ソースのパス `path` を写す局所の名前。`groups` のどれにも当たらなければ None。
pub fn local(reading: &Reading, path: &str) -> Option<String> {
    match &reading.form {
        ReadingForm::Dir { depth } => {
            let dirs: Vec<&str> = path.split('/').collect();
            let dirs = &dirs[..dirs.len() - 1];
            // `n` 段に満たない所にあるファイルは、そのファイルのディレクトリを局所にする。
            let name = dirs[..dirs.len().min(*depth)].join("/");
            Some(if name.is_empty() { ".".to_string() } else { name })
        }
        ReadingForm::File => Some(path.to_string()),
        // 上から順に当てはめる。
        ReadingForm::Groups { groups } => groups
            .iter()
            .find(|(_, patterns)| {
                let mut b = GlobSetBuilder::new();
                for p in patterns {
                    if let Ok(g) = GlobBuilder::new(p).literal_separator(true).build() {
                        b.add(g);
                    }
                }
                b.build().is_ok_and(|set| set.is_match(path))
            })
            .map(|(name, _)| name.clone()),
    }
}

/// Atom が名指す要素。`subject`、`via`、`object`。`object` に `|` で並べた行き先は、それぞれを名指す。
pub fn named(a: &Atom) -> Vec<&str> {
    let mut out = vec![a.subject.as_str()];
    out.extend(a.via.iter().flatten().map(String::as_str));
    if let Some(o) = &a.object {
        out.extend(o.split('|').map(str::trim).filter(|t| !t.is_empty()));
    }
    out
}

/// 一つの読みの幾何。要素がどの局所に属するか。
pub struct Geometry<'a> {
    reading: &'a Reading,
    /// 要素を定義したソース。
    sources: BTreeMap<String, String>,
    /// チャネルとその項目が属する局所。
    channels: BTreeMap<String, BTreeSet<String>>,
    /// 定義がなく、`resolves` が外部でないソースを指す要素と、その沈黙(設計 §3.3)。属する局所が決まらない。
    unknown: BTreeMap<String, Silence>,
    /// `resolves` が外部だけを指す要素。外部の要素として、どの局所にも属さない。
    external: BTreeSet<String>,
}

impl<'a> Geometry<'a> {
    /// `defined` は要素の定義を探す Atom の列、`body` はチャネルを送り受けする操作を探す Atom の列。
    /// 候補の中で定義した要素は `file`、それ以外は `defines` の `at` のパスで定義される。
    pub fn new(reading: &'a Reading, defined: &[Atom], body: &[Atom]) -> Geometry<'a> {
        let mut g = Geometry { reading, sources: BTreeMap::new(), channels: BTreeMap::new(), unknown: BTreeMap::new(), external: BTreeSet::new() };
        for a in defined.iter().filter(|a| a.kind == "defines") {
            let path = match &a.file {
                Some(f) => Some(f.clone()),
                None => a.at.as_deref().filter(|at| !at.starts_with("plan:")).and_then(parse_location).map(|l| l.path),
            };
            if let Some(p) = path {
                g.sources.insert(a.subject.clone(), p);
            }
        }
        // 定義がなく、`resolves` が外部だけを指すのでない要素は、構造の解決のとおりに沈黙する(設計 §3.3)。
        let s = Structure::new(defined.iter().filter(|a| a.kind == "resolves" || a.kind == "observed").cloned().collect());
        for (n, r) in &s.resolves {
            if g.sources.contains_key(n) {
                continue;
            }
            match r {
                Resolution::External(_) => {
                    g.external.insert(n.clone());
                }
                _ => {
                    g.unknown.insert(n.clone(), s.undefined(n));
                }
            }
        }
        // チャネルとその項目は、そこへ送る操作と、そこから受け取る操作の局所すべてに属する。
        for a in body.iter().filter(|a| a.kind == "sends" || a.kind == "receives") {
            let item = a.object.clone().unwrap_or_default();
            let locals = g.element_locals(&a.subject);
            let parts: Vec<&str> = item.split(':').collect();
            if parts.len() >= 4 {
                g.channels.entry(parts[..parts.len() - 1].join(":")).or_default().extend(locals.iter().cloned());
            }
            g.channels.entry(item).or_default().extend(locals);
        }
        g
    }

    /// 要素が属する局所。要素は、それを定義したソースの局所に属する(`holder` で見る)。
    /// 定義を観測していない要素は、どの局所にも属さない。
    pub fn element_locals(&self, name: &str) -> BTreeSet<String> {
        if let Some(locals) = self.channels.get(name) {
            return locals.clone();
        }
        self.sources.get(self.holder(name)).and_then(|p| local(self.reading, p)).into_iter().collect()
    }

    /// 要素の局所を見る名前。引数と呼び出しの要素は持ち主の操作(`owner`)。
    /// 定義も `resolves` も持たない要素 `<頭>.<名前>`(型のフィールドやメソッド)は、頭の定義を観測しているか、頭の局所が決まらないとき、頭で見る。
    fn holder<'n>(&self, name: &'n str) -> &'n str {
        let o = owner(name);
        if self.sources.contains_key(o) || self.unknown.contains_key(o) || self.external.contains(o) {
            return o;
        }
        match o.rsplit_once('.') {
            Some((t, _)) if self.sources.contains_key(t) || self.unknown.contains_key(t) => t,
            _ => o,
        }
    }

    /// Atom が属する局所。名指す要素が属する局所すべて(マニュアル第4章)。
    pub fn atom_locals(&self, a: &Atom) -> BTreeSet<String> {
        named(a).into_iter().flat_map(|n| self.element_locals(n)).collect()
    }

    /// 候補の Atom `plan` を局所ごとに分ける(マニュアル第5章 問い7)。
    /// 候補の見出し(`plan`)は、どこにも入れない。局所の候補ごとに書き直す。
    pub fn split(&self, plan: &[Atom]) -> Split {
        let mut out = Split::default();
        for a in plan.iter().filter(|a| a.kind != "plan") {
            if let Some(q) = named(a).into_iter().find(|n| n.starts_with('?')) {
                out.questions.push((q.to_string(), a.clone()));
                continue;
            }
            // 定義がなく、`resolves` が外部でないソースを指す要素は、属する局所が決まらない(設計 §3.3)。
            if let Some((n, s)) = named(a).into_iter().find_map(|n| self.unknown.get(self.holder(n)).map(|s| (n, s))) {
                out.unknown.push((n.to_string(), s.clone()));
                continue;
            }
            let locals = self.atom_locals(a);
            match locals.len() {
                1 => {
                    let local = locals.into_iter().next().unwrap();
                    out.sequence.push((Some(local.clone()), a.clone()));
                    out.locals.entry(local).or_default().push(a.clone());
                }
                _ => {
                    out.sequence.push((None, a.clone()));
                    out.shared.push(a.clone());
                }
            }
        }
        out
    }
}

/// 候補を局所ごとに分けたもの。
#[derive(Default)]
pub struct Split {
    /// 局所の名前と、その局所だけに属する Atom。
    pub locals: BTreeMap<String, Vec<Atom>>,
    /// 共有の条件。二つ以上の局所に属する Atom と、どの局所にも属さない Atom。
    pub shared: Vec<Atom>,
    /// 候補の Atom を、候補に書いた順のまま、属する局所(共有の条件は None)と並べたもの。局所の候補を書き出すときに順を保つ。
    pub sequence: Vec<(Option<String>, Atom)>,
    /// `?` の名前と、それを名指す Atom。どの局所に属するかが決まらない。
    pub questions: Vec<(String, Atom)>,
    /// 定義がなく `resolves` が外部でないソースを指す要素と、その沈黙(設計 §3.3)。どの局所に属するかが決まらない。
    pub unknown: Vec<(String, Silence)>,
}

/// 要素を定義するソースを持つ要素。引数 `X.$p` は操作 `X`(マニュアル第4章)、呼び出しの要素 `A->B` は呼び出し元 `A`(設計 §4.4)。
fn owner(name: &str) -> &str {
    match (name.split_once("->"), name.split_once(".$")) {
        (Some((caller, _)), _) => caller,
        (None, Some((op, _))) => op,
        _ => name,
    }
}
