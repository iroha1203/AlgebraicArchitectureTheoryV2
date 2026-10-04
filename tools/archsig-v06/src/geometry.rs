//! 幾何(設計 §6、マニュアル第4章)。読みと Atom から、局所と重なりを作る。

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use globset::{GlobBuilder, GlobSetBuilder};

use crate::atom::Atom;
use crate::law::{Reading, ReadingForm};
use crate::structure::{Place, Silence, Structure, is_question, targets};

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

/// 一つの読みの幾何。要素がどの局所に属するか(設計 §6)。
pub struct Geometry<'a> {
    reading: &'a Reading,
    /// 候補を重ねた構造。
    after: &'a Structure,
    /// 変更前の構造。`removes` した要素と、対応の元の要素はここで見つかる。
    before: &'a Structure,
    /// 局所を求めている途中のチャネル。送り受けする操作がめぐっても、一度だけたどる。
    busy: RefCell<BTreeSet<String>>,
}

impl<'a> Geometry<'a> {
    /// `after` は候補を重ねた構造、`before` は変更前の構造。候補がなければ同じ構造を渡す。
    pub fn new(reading: &'a Reading, after: &'a Structure, before: &'a Structure) -> Geometry<'a> {
        Geometry { reading, after, before, busy: RefCell::new(BTreeSet::new()) }
    }

    /// 要素が属する局所。決まらなければ、その沈黙。どの局所にも属さなければ空。
    /// 局所の元は名前の解決のモジュールが返す(設計 §6)。ここでは、それを読みの局所に写すだけである。
    pub fn element_locals(&self, name: &str) -> Result<BTreeSet<String>, Silence> {
        // チャネルの送り受けがめぐっても、一度だけたどる。
        if !self.busy.borrow_mut().insert(name.to_string()) {
            return Ok(BTreeSet::new());
        }
        let r = self.locals(self.after.place(self.before, name));
        self.busy.borrow_mut().remove(name);
        r
    }

    /// 局所の元を、読みの局所に写す。
    fn locals(&self, place: Place) -> Result<BTreeSet<String>, Silence> {
        match place {
            Place::Sources(sources) => Ok(sources.iter().filter_map(|p| local(self.reading, p)).collect()),
            Place::Ambiguous(sources, silence) => {
                let locals: BTreeSet<String> = sources.iter().filter_map(|p| local(self.reading, p)).collect();
                if locals.len() == 1 { Ok(locals) } else { Err(silence) }
            }
            Place::Via(n) => self.element_locals(&n),
            Place::Operations(ops) => ops.iter().try_fold(BTreeSet::new(), |mut out, op| {
                out.extend(self.element_locals(op)?);
                Ok(out)
            }),
            Place::Nowhere => Ok(BTreeSet::new()),
            Place::Unknown(silence) => Err(silence),
            Place::Either(a, b) => match (self.locals(*a), self.locals(*b)) {
                (Err(e), _) | (_, Err(e)) => Err(e),
                (Ok(x), Ok(y)) => Ok(if x.is_empty() { y } else { x }),
            },
        }
    }

    /// 列の読み方で解いた場所のフィールドとその頭の局所。決まらなければ、決まらない名前とその沈黙。
    fn column_locals(&self, names: &[String]) -> Result<BTreeSet<String>, (String, Silence)> {
        let mut out = BTreeSet::new();
        for (n, place) in self.after.column_places(names) {
            out.extend(self.locals(place).map_err(|s| (n, s))?);
        }
        Ok(out)
    }

    /// Atom が属する局所。名指す要素が属する局所すべて(設計 §6)。決まらなければ、決まらない名前とその沈黙。
    /// 名指す要素は、`subject` と `object`(`corresponds` の `|` で並べた行き先はそれぞれ)を要素(名前)で解いた要素と、
    /// `reads`・`writes` の `object` と `via` の列を列の読み方で解いた場所のフィールドとその頭である。
    pub fn atom_locals(&self, a: &Atom) -> Result<BTreeSet<String>, (String, Silence)> {
        let mut out = self.element_locals(&a.subject).map_err(|s| (a.subject.clone(), s))?;
        match a.kind.as_str() {
            "reads" | "writes" => {
                let names: Vec<String> = a.via.iter().flatten().chain(a.object.as_ref()).cloned().collect();
                out.extend(self.column_locals(&names)?);
            }
            _ => {
                for n in a.object.iter().flat_map(|o| targets(o).0) {
                    out.extend(self.element_locals(&n).map_err(|s| (n.clone(), s))?);
                }
            }
        }
        Ok(out)
    }

    /// 候補の Atom `plan` を局所ごとに分ける(マニュアル第5章 問い7)。
    /// 候補の見出し(`plan`)は、どこにも入れない。局所の候補ごとに書き直す。
    pub fn split(&self, plan: &[Atom]) -> Split {
        let mut out = Split::default();
        for a in plan.iter().filter(|a| a.kind != "plan") {
            if let Some(q) = named(a).into_iter().find(|n| is_question(n)) {
                out.questions.push((q, a.clone()));
                continue;
            }
            let locals = match self.atom_locals(a) {
                Ok(l) => l,
                // 属する局所が決まらない。
                Err(unknown) => {
                    out.unknown.push(unknown);
                    continue;
                }
            };
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

/// Atom に書いた名前。`subject`、`object`(`|` で並べた行き先はそれぞれ)、`via`。
fn named(a: &Atom) -> Vec<String> {
    let mut out = vec![a.subject.clone()];
    out.extend(a.object.iter().flat_map(|o| targets(o).0));
    out.extend(a.via.iter().flatten().cloned());
    out
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
    /// 属する局所が決まらない名前と、その沈黙(設計 §6)。
    pub unknown: Vec<(String, Silence)>,
}
