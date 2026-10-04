//! 幾何(設計 §6、マニュアル第4章)。読みと Atom から、局所と重なりを作る。

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use globset::{GlobBuilder, GlobSetBuilder};

use crate::atom::Atom;
use crate::law::{Reading, ReadingForm};
use crate::structure::{Answer, Found, Reason, Silence, Structure, Unknown, Why, is_question, targets};

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
    pub fn element_locals(&self, name: &str) -> Result<BTreeSet<String>, Silence> {
        // チャネルとその項目は、送る操作と受け取る操作の局所すべてに属する。送り受けする操作は、候補を重ねた後の列から探す。
        if let Some(ops) = self.after.channel_operations(name) {
            if !self.busy.borrow_mut().insert(name.to_string()) {
                return Ok(BTreeSet::new());
            }
            let r = ops.iter().try_fold(BTreeSet::new(), |mut out, op| {
                out.extend(self.element_locals(op)?);
                Ok(out)
            });
            self.busy.borrow_mut().remove(name);
            return r;
        }
        let after = self.after.element(name);
        match &after {
            Ok(Answer::Element(f)) => return self.found(self.after, f),
            _ => {
                if let Ok(Answer::Element(f)) = self.before.element(name) {
                    return self.found(self.before, &f);
                }
            }
        }
        match after {
            Ok(_) => Ok(BTreeSet::new()),
            Err(u) => self.undecided(u),
        }
    }

    /// 決まった要素の局所。引数と呼び出しは持ち主の操作で見る。候補の中で定義し `file` のない要素は、変更前の構造で解いた定義した所。
    fn found(&self, s: &Structure, f: &Found) -> Result<BTreeSet<String>, Silence> {
        if matches!(f.kind.as_str(), "param" | "call")
            && let Some(o) = &f.owner
        {
            return self.element_locals(o);
        }
        if f.planned && f.defined.is_empty() {
            return match self.before.element(&f.name) {
                Ok(Answer::Element(g)) if !std::ptr::eq(s, self.before) => self.found(self.before, &g),
                _ => Ok(BTreeSet::new()),
            };
        }
        Ok(f.defined.iter().filter_map(|p| local(self.reading, p)).collect())
    }

    /// 要素(名前)が決まらないときの局所(設計 §6)。
    fn undecided(&self, u: Unknown) -> Result<BTreeSet<String>, Silence> {
        // 曖昧な要素は、定義した所がすべて一つの局所にあればその局所、なければ決まらない。
        if u.why == Why::Ambiguous {
            let locals: BTreeSet<String> = u.defined.iter().filter_map(|p| local(self.reading, p)).collect();
            return if locals.len() == 1 { Ok(locals) } else { Err(u.silence) };
        }
        // `<T>.<f>` が段で決まらないか、頭 `T` が曖昧で決まらないなら、`T` の局所。
        // `<T>.<f>` そのものの `resolves` で決まらなかったなら、その解決で見る(マニュアル第4章)。
        if let Some(stage) = &u.stage
            && !(stage.absent && (u.silence.read.is_some() || matches!(u.why, Why::Missing | Why::Undecided)))
        {
            return self.element_locals(&stage.ty);
        }
        // `unread` でソースを返すか、それ以外の `unresolved` なら、決まらない。読む所が名前だけの `unread` は、どの局所にも属さない。
        if u.silence.read.is_some() || u.silence.reason == Reason::Unresolved {
            return Err(u.silence);
        }
        Ok(BTreeSet::new())
    }

    /// 列の読み方で解いた場所のフィールドとその頭の局所。
    fn column_locals(&self, names: &[String]) -> Result<BTreeSet<String>, (String, Silence)> {
        let c = self.after.column(names);
        let mut out = BTreeSet::new();
        for n in c.ty.iter().chain(&c.walk.place) {
            out.extend(self.element_locals(n).map_err(|s| (n.clone(), s))?);
        }
        if let Some(u) = c.walk.stop {
            let at = names.get(c.walk.place.len()).or(names.last()).cloned().unwrap_or_default();
            out.extend(self.undecided(u).map_err(|s| (at, s))?);
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
