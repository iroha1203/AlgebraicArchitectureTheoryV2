//! 第4章の Law ファイル。

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, Default)]
pub struct LawSet {
    pub sources: Vec<String>,
    pub except: Vec<String>,
    pub readings: Vec<Reading>,
    pub fresh: Vec<String>,
    pub meanings: Vec<Meaning>,
    pub laws: Vec<Law>,
    pub defs: BTreeMap<String, Selector>,
    pub files: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Reading {
    pub name: String,
    pub kind: ReadingKind,
}

#[derive(Clone, Debug)]
pub enum ReadingKind {
    Dir(usize),
    File,
    Groups(Vec<(String, Vec<String>)>),
}

#[derive(Clone, Debug)]
pub struct Meaning {
    pub name: String,
    pub on: Vec<String>,
    pub to: Option<String>,
    pub values: Vec<String>,
    pub hint: String,
}

#[derive(Clone, Debug)]
pub struct Law {
    pub name: String,
    pub description: String,
    pub on: Option<String>,
    pub about: Option<String>,
    pub rule: Rule,
    pub origin: String,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub enum Rule {
    No(Selector),
    Each(Selector, Vec<Cond>),
    Agrees { convert: Vec<Convert> },
    ChangesCommute,
    ChangesKeep,
    Roundtrips { read: String, update: String },
}

impl Rule {
    pub fn form(&self) -> &'static str {
        match self {
            Rule::No(_) => "no",
            Rule::Each(..) => "each",
            Rule::Agrees { .. } => "agrees along",
            Rule::ChangesCommute => "changes commute",
            Rule::ChangesKeep => "changes keep",
            Rule::Roundtrips { .. } => "roundtrips",
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Convert {
    pub from: String,
    pub to: String,
    pub op: char,
    pub factor: String,
}

/// 要素の選び方。
#[derive(Clone, Debug, Default)]
pub struct Selector {
    pub kind: Option<String>,
    pub to: Option<String>,
    pub pattern: Option<String>,
    /// 意味の名前か `def` の名前。どちらかは Law ファイル全体を読んでから決める。
    pub name: Option<String>,
    pub conds: Vec<Cond>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub enum Cond {
    Rel(String, Selector),
    Has(String, Option<String>),
    Inside(String),
    Outside(String),
}

pub const ELEMENT_KINDS: &[&str] = &["operation", "type", "field", "param", "call", "channel"];
const REL_WORDS: &[&str] = &["writes", "reads", "calls", "sends", "receives", "reaches"];

impl LawSet {
    pub fn load_dir(dir: &Path) -> Result<LawSet, String> {
        let mut set = LawSet::default();
        let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
            .map_err(|e| format!("{}: {e}", dir.display()))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().is_some_and(|x| x == "law"))
            .collect();
        entries.sort();
        let mut seen = BTreeSet::new();
        for p in entries {
            set.load_file(&p, &mut seen)?;
        }
        set.resolve()?;
        Ok(set)
    }

    fn load_file(&mut self, path: &Path, seen: &mut BTreeSet<PathBuf>) -> Result<(), String> {
        let canon = path.canonicalize().unwrap_or(path.to_path_buf());
        if !seen.insert(canon) {
            return Ok(());
        }
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let origin = path.display().to_string();
        self.files.push(origin.clone());
        for (line, block) in blocks(&text) {
            let at = format!("{origin}:{line}");
            let head = lex(&block[0]).map_err(|e| format!("{at}: {e}"))?;
            let mut rest = Vec::new();
            for l in &block[1..] {
                rest.push(lex(l).map_err(|e| format!("{at}: {e}"))?);
            }
            let first = match head.first() {
                Some(Tok::Word(w)) => w.clone(),
                _ => return Err(format!("{at}: 宣言の語がない")),
            };
            match first.as_str() {
                "sources" => {
                    self.sources.extend(strings(&head[1..]).map_err(|e| format!("{at}: {e}"))?);
                    for r in &rest {
                        match r.first() {
                            Some(Tok::Word(w)) if w == "except" => {
                                self.except.extend(strings(&r[1..]).map_err(|e| format!("{at}: {e}"))?)
                            }
                            _ => return Err(format!("{at}: sources の下には except だけを書く")),
                        }
                    }
                }
                "include" => {
                    let s = strings(&head[1..]).map_err(|e| format!("{at}: {e}"))?;
                    for inc in s {
                        let p = path.parent().unwrap_or(Path::new(".")).join(inc);
                        self.load_file(&p, seen)?;
                    }
                }
                "fresh" => self.fresh.extend(strings(&head[1..]).map_err(|e| format!("{at}: {e}"))?),
                "reading" => self.readings.push(parse_reading(&head, &rest).map_err(|e| format!("{at}: {e}"))?),
                "meaning" => self.meanings.push(parse_meaning(&head, &rest).map_err(|e| format!("{at}: {e}"))?),
                "law" => {
                    let mut law = parse_law(&head, &rest).map_err(|e| format!("{at}: {e}"))?;
                    law.origin = at;
                    self.laws.push(law);
                }
                "def" => {
                    let name = word_at(&head, 1).ok_or(format!("{at}: def の名前がない"))?;
                    if head.get(2) != Some(&Tok::Sym("=")) {
                        return Err(format!("{at}: def には `=` が要る"));
                    }
                    let mut toks = head[3..].to_vec();
                    for r in &rest {
                        toks.extend(r.iter().cloned());
                    }
                    let mut c = Cursor { t: &toks, i: 0 };
                    let sel = c.selector().map_err(|e| format!("{at}: {e}"))?;
                    c.end().map_err(|e| format!("{at}: {e}"))?;
                    self.defs.insert(name, sel);
                }
                other => return Err(format!("{at}: 知らない宣言 `{other}`")),
            }
        }
        Ok(())
    }

    /// 名前の参照を確かめる。
    fn resolve(&mut self) -> Result<(), String> {
        let meanings: BTreeSet<String> = self.meanings.iter().map(|m| m.name.clone()).collect();
        let readings: BTreeSet<String> = self.readings.iter().map(|r| r.name.clone()).collect();
        for (name, sel) in &self.defs {
            check_selector(sel, &meanings, &BTreeMap::new()).map_err(|e| format!("def {name}: {e}"))?;
        }
        for law in &self.laws {
            let at = &law.origin;
            if let Some(r) = &law.on {
                if !readings.contains(r) {
                    return Err(format!("{at}: 読み `{r}` が宣言されていない"));
                }
            }
            if let Some(m) = &law.about {
                if !meanings.contains(m) {
                    return Err(format!("{at}: 意味 `{m}` が宣言されていない"));
                }
            }
            let needs_about = matches!(
                law.rule,
                Rule::Agrees { .. } | Rule::ChangesCommute | Rule::ChangesKeep | Rule::Roundtrips { .. }
            );
            if needs_about && law.about.is_none() {
                return Err(format!("{at}: {} の規則には about が要る", law.rule.form()));
            }
            match &law.rule {
                Rule::No(s) => check_selector(s, &meanings, &self.defs).map_err(|e| format!("{at}: {e}"))?,
                Rule::Each(s, conds) => {
                    check_selector(s, &meanings, &self.defs).map_err(|e| format!("{at}: {e}"))?;
                    for c in conds {
                        check_cond(c, &meanings, &self.defs).map_err(|e| format!("{at}: {e}"))?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn reading(&self, name: Option<&str>) -> Option<&Reading> {
        match name {
            Some(n) => self.readings.iter().find(|r| r.name == n),
            None => self.readings.first(),
        }
    }
}

fn check_selector(sel: &Selector, meanings: &BTreeSet<String>, defs: &BTreeMap<String, Selector>) -> Result<(), String> {
    if let Some(k) = &sel.kind {
        if !ELEMENT_KINDS.contains(&k.as_str()) {
            return Err(format!("要素の種類 `{k}` はない"));
        }
    }
    if let Some(n) = &sel.name {
        if !meanings.contains(n) && !defs.contains_key(n) {
            return Err(format!("`{n}` は意味の語彙にも def にもない"));
        }
    }
    for c in &sel.conds {
        check_cond(c, meanings, defs)?;
    }
    Ok(())
}

fn check_cond(c: &Cond, meanings: &BTreeSet<String>, defs: &BTreeMap<String, Selector>) -> Result<(), String> {
    match c {
        Cond::Rel(_, s) => check_selector(s, meanings, defs),
        Cond::Has(m, _) if !meanings.contains(m) => Err(format!("意味 `{m}` が宣言されていない")),
        _ => Ok(()),
    }
}

/// 字下げでまとめた宣言。行番号と、コメントを落とした行の列。
fn blocks(text: &str) -> Vec<(usize, Vec<String>)> {
    let mut out: Vec<(usize, Vec<String>)> = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        let line = strip_comment(raw);
        if line.trim().is_empty() {
            continue;
        }
        let indented = line.starts_with(' ') || line.starts_with('\t');
        match (indented, out.last_mut()) {
            (true, Some((_, b))) => b.push(line.trim().to_string()),
            _ => out.push((i + 1, vec![line.trim().to_string()])),
        }
    }
    out
}

fn strip_comment(line: &str) -> String {
    let mut in_str = false;
    for (i, c) in line.char_indices() {
        match c {
            '"' => in_str = !in_str,
            '#' if !in_str => return line[..i].to_string(),
            _ => {}
        }
    }
    line.to_string()
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Word(String),
    Str(String),
    Sym(&'static str),
}

fn lex(line: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '"' {
            let s = i + 1;
            i += 1;
            while i < chars.len() && chars[i] != '"' {
                i += 1;
            }
            if i >= chars.len() {
                return Err("閉じていない文字列".to_string());
            }
            out.push(Tok::Str(chars[s..i].iter().collect()));
            i += 1;
        } else if c == '-' && chars.get(i + 1) == Some(&'>') {
            out.push(Tok::Sym("->"));
            i += 2;
        } else if c.is_alphanumeric() || c == '_' || c == '^' {
            let s = i;
            while i < chars.len()
                && (chars[i].is_alphanumeric() || matches!(chars[i], '_' | '.' | '^') || chars[i] == '-' && chars.get(i + 1) != Some(&'>'))
            {
                i += 1;
            }
            out.push(Tok::Word(chars[s..i].iter().collect()));
        } else {
            let sym = match c {
                ',' => ",",
                '|' => "|",
                '=' => "=",
                '(' => "(",
                ')' => ")",
                ':' => ":",
                '*' => "*",
                '/' => "/",
                _ => return Err(format!("読めない文字 `{c}`")),
            };
            out.push(Tok::Sym(sym));
            i += 1;
        }
    }
    Ok(out)
}

fn word_at(t: &[Tok], i: usize) -> Option<String> {
    match t.get(i) {
        Some(Tok::Word(w)) => Some(w.clone()),
        _ => None,
    }
}

fn strings(t: &[Tok]) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    for (i, tok) in t.iter().enumerate() {
        match tok {
            Tok::Str(s) if i % 2 == 0 => out.push(s.clone()),
            Tok::Sym(",") if i % 2 == 1 => {}
            _ => return Err("パターンは \"…\" を `,` で並べて書く".to_string()),
        }
    }
    if out.is_empty() {
        return Err("パターンがない".to_string());
    }
    Ok(out)
}

fn parse_reading(head: &[Tok], rest: &[Vec<Tok>]) -> Result<Reading, String> {
    let name = word_at(head, 1).ok_or("reading の名前がない")?;
    if head.get(2) != Some(&Tok::Sym("=")) {
        return Err("reading には `=` が要る".to_string());
    }
    let form = word_at(head, 3).ok_or("読みの形がない")?;
    let kind = match form.as_str() {
        "dir" => {
            let depth = match &head[4..] {
                [Tok::Sym("("), Tok::Word(d), Tok::Sym(":"), Tok::Word(n), Tok::Sym(")")] if d == "depth" => {
                    n.parse::<usize>().map_err(|_| "depth は整数で書く")?
                }
                _ => return Err("dir は dir(depth: n) と書く".to_string()),
            };
            ReadingKind::Dir(depth)
        }
        "file" => ReadingKind::File,
        "groups" => {
            let mut groups = Vec::new();
            for r in rest {
                let g = word_at(r, 0).ok_or("groups の各行は `名前: \"パターン\"` と書く")?;
                if r.get(1) != Some(&Tok::Sym(":")) {
                    return Err("groups の各行は `名前: \"パターン\"` と書く".to_string());
                }
                groups.push((g, strings(&r[2..])?));
            }
            if groups.is_empty() {
                return Err("groups に局所がない".to_string());
            }
            ReadingKind::Groups(groups)
        }
        other => return Err(format!("読みの形 `{other}` はない")),
    };
    Ok(Reading { name, kind })
}

fn parse_meaning(head: &[Tok], rest: &[Vec<Tok>]) -> Result<Meaning, String> {
    let name = word_at(head, 1).ok_or("meaning の名前がない")?;
    if word_at(head, 2).as_deref() != Some("on") {
        return Err("meaning には on が要る".to_string());
    }
    let mut on = Vec::new();
    let mut to = None;
    let mut i = 3;
    while i < head.len() {
        match &head[i] {
            Tok::Word(w) if w == "to" => {
                match head.get(i + 1) {
                    Some(Tok::Str(s)) => to = Some(s.clone()),
                    _ => return Err("to の後にパターンがない".to_string()),
                }
                i += 2;
            }
            Tok::Word(w) if ELEMENT_KINDS.contains(&w.as_str()) => {
                on.push(w.clone());
                i += 1;
            }
            Tok::Sym(",") => i += 1,
            other => return Err(format!("meaning の on に読めない語 {other:?}")),
        }
    }
    if on.is_empty() {
        return Err("meaning の on に要素の種類がない".to_string());
    }
    let mut values = Vec::new();
    let mut hint = String::new();
    for r in rest {
        match r.first() {
            Some(Tok::Word(w)) if w == "values" => {
                for t in &r[1..] {
                    match t {
                        Tok::Word(v) => values.push(v.clone()),
                        Tok::Sym("|") => {}
                        _ => return Err("values は `a | b` と書く".to_string()),
                    }
                }
            }
            Some(Tok::Str(s)) if r.len() == 1 => hint = s.clone(),
            _ => return Err("meaning の下には values と観測の手がかりを書く".to_string()),
        }
    }
    Ok(Meaning { name, on, to, values, hint })
}

fn parse_law(head: &[Tok], rest: &[Vec<Tok>]) -> Result<Law, String> {
    let name = word_at(head, 1).ok_or("law の名前がない")?;
    let mut description = String::new();
    let mut on = None;
    let mut about = None;
    let mut rule_lines: Vec<&Vec<Tok>> = Vec::new();
    for r in rest {
        match r.first() {
            Some(Tok::Str(s)) if r.len() == 1 && rule_lines.is_empty() => description = s.clone(),
            Some(Tok::Word(w)) if w == "on" && rule_lines.is_empty() => on = word_at(r, 1),
            Some(Tok::Word(w)) if w == "about" && rule_lines.is_empty() => about = word_at(r, 1),
            _ => rule_lines.push(r),
        }
    }
    let first = rule_lines.first().ok_or("law に規則がない")?;
    let rule = match word_at(first, 0).as_deref() {
        Some("no") => {
            let mut toks = first[1..].to_vec();
            for r in &rule_lines[1..] {
                toks.extend(r.iter().cloned());
            }
            let mut c = Cursor { t: &toks, i: 0 };
            let s = c.selector()?;
            c.end()?;
            Rule::No(s)
        }
        Some("each") => {
            let mut c = Cursor { t: &first[1..], i: 0 };
            let s = c.selector()?;
            c.end()?;
            let mut conds = Vec::new();
            for r in &rule_lines[1..] {
                let mut c = Cursor { t: r, i: 0 };
                conds.extend(c.conds()?);
                c.end()?;
            }
            if conds.is_empty() {
                return Err("each の二行目に条件がない".to_string());
            }
            Rule::Each(s, conds)
        }
        Some("agrees") => {
            if first.len() != 3 || word_at(first, 1).as_deref() != Some("along") || word_at(first, 2).as_deref() != Some("flows") {
                return Err("agrees along flows と書く".to_string());
            }
            let mut convert = Vec::new();
            for r in &rule_lines[1..] {
                match r.as_slice() {
                    [Tok::Word(c), Tok::Word(from), Tok::Sym("->"), Tok::Word(to), Tok::Word(by), Tok::Sym(op), Tok::Word(f)]
                        if c == "convert" && by == "by" && (*op == "*" || *op == "/") =>
                    {
                        convert.push(Convert { from: from.clone(), to: to.clone(), op: op.chars().next().unwrap(), factor: f.clone() })
                    }
                    _ => return Err("convert は `convert a -> b by * 100` と書く".to_string()),
                }
            }
            Rule::Agrees { convert }
        }
        Some("changes") => match (word_at(first, 1).as_deref(), first.len()) {
            (Some("keep"), 2) => Rule::ChangesKeep,
            (Some("commute"), 4) if word_at(first, 2).as_deref() == Some("with") && word_at(first, 3).as_deref() == Some("operations") => {
                Rule::ChangesCommute
            }
            _ => return Err("changes commute with operations か changes keep と書く".to_string()),
        },
        Some("roundtrips") => match first.as_slice() {
            [Tok::Word(_), Tok::Word(r), Tok::Str(read), Tok::Word(u), Tok::Str(update)] if r == "read" && u == "update" => {
                Rule::Roundtrips { read: read.clone(), update: update.clone() }
            }
            _ => return Err("roundtrips read \"…\" update \"…\" と書く".to_string()),
        },
        _ => return Err("規則は no、each、agrees、changes、roundtrips のどれかで始める".to_string()),
    };
    Ok(Law { name, description, on, about, rule, origin: String::new() })
}

struct Cursor<'a> {
    t: &'a [Tok],
    i: usize,
}

impl Cursor<'_> {
    fn peek_word(&self) -> Option<&str> {
        match self.t.get(self.i) {
            Some(Tok::Word(w)) => Some(w.as_str()),
            _ => None,
        }
    }

    fn end(&self) -> Result<(), String> {
        if self.i < self.t.len() {
            return Err(format!("読めない続き {:?}", &self.t[self.i..]));
        }
        Ok(())
    }

    fn string(&mut self) -> Option<String> {
        match self.t.get(self.i) {
            Some(Tok::Str(s)) => {
                self.i += 1;
                Some(s.clone())
            }
            _ => None,
        }
    }

    /// `that` の条件を含まない要素の選び方。
    fn base(&mut self) -> Result<Selector, String> {
        let mut sel = Selector::default();
        if let Some(w) = self.peek_word() {
            if ELEMENT_KINDS.contains(&w) {
                sel.kind = Some(w.to_string());
                self.i += 1;
                if self.peek_word() == Some("to") {
                    self.i += 1;
                    sel.to = Some(self.string().ok_or("to の後にパターンがない")?);
                }
                sel.pattern = self.string();
                return Ok(sel);
            }
            if !is_keyword(w) {
                sel.name = Some(w.to_string());
                self.i += 1;
                return Ok(sel);
            }
        }
        sel.pattern = Some(self.string().ok_or("要素の選び方が読めない")?);
        Ok(sel)
    }

    fn selector(&mut self) -> Result<Selector, String> {
        let mut sel = self.base()?;
        if self.peek_word() == Some("that") {
            self.i += 1;
            sel.conds = self.conds()?;
            if sel.conds.is_empty() {
                return Err("that の後に条件がない".to_string());
            }
        }
        Ok(sel)
    }

    fn conds(&mut self) -> Result<Vec<Cond>, String> {
        let mut out = Vec::new();
        while let Some(w) = self.peek_word() {
            let w = w.to_string();
            if w == "and" {
                self.i += 1;
                continue;
            }
            self.i += 1;
            let c = if REL_WORDS.contains(&w.as_str()) {
                Cond::Rel(w, self.base()?)
            } else if w == "has" {
                let m = self.peek_word().ok_or("has の後に意味がない")?.to_string();
                self.i += 1;
                let v = match self.peek_word() {
                    Some(v) if !is_keyword(v) => {
                        let v = v.to_string();
                        self.i += 1;
                        Some(v)
                    }
                    _ => None,
                };
                Cond::Has(m, v)
            } else if w == "inside" {
                Cond::Inside(self.string().ok_or("inside の後に局所がない")?)
            } else if w == "outside" {
                Cond::Outside(self.string().ok_or("outside の後に局所がない")?)
            } else {
                return Err(format!("条件 `{w}` はない"));
            };
            out.push(c);
        }
        Ok(out)
    }
}

fn is_keyword(w: &str) -> bool {
    REL_WORDS.contains(&w) || matches!(w, "that" | "and" | "has" | "inside" | "outside" | "to")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_text(text: &str) -> LawSet {
        let dir = std::env::temp_dir().join(format!("archsig-law-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("a.law"), text).unwrap();
        let set = LawSet::load_dir(&dir).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        set
    }

    #[test]
    fn manual_chapter_4_example() {
        let set = parse_text(
            r#"# .archsig/law/shop.law

sources "shop/**"
  except "**/tests/**", "**/test_*.py"

reading module = dir(depth: 2)
reading service = groups
  commerce: "shop/order/**", "shop/shipping/**"
  money:    "shop/payment/**"
  rest:     "**"

fresh "shop.common.ids.new_*"

meaning payment-info on field
  "注文の支払いを特定する値。決済サービスの呼び出しに渡る値として使われているもの。"

meaning role on call to "mail.send"
  values identity-check | order-notice | incident
  "送るメールの役割。"

meaning unit on field
  values minor | major
  "金額の単位。"

law payment-follows-order
  "注文の型を変えても、決済情報は今の操作と同じように扱われる。"
  about payment-info
  changes commute with operations

law identity-mail-from-auth
  "本人確認のメールは auth から送る。"
  no call to "mail.send" that has role identity-check outside "shop/auth"

def payment-writer = operation that writes payment-info

law payment-writes-are-audited
  "決済情報を書き換える操作は、監査記録を残す。"
  each payment-writer
    calls "audit.record"

law amount-units-agree
  "金額は、単位をそろえてから渡す。"
  about unit
  agrees along flows
  convert major -> minor by * 100
"#,
        );
        assert_eq!(set.sources, vec!["shop/**"]);
        assert_eq!(set.except.len(), 2);
        assert_eq!(set.readings.len(), 2);
        assert_eq!(set.meanings[1].values, vec!["identity-check", "order-notice", "incident"]);
        assert_eq!(set.laws.len(), 4);
        assert!(matches!(set.laws[0].rule, Rule::ChangesCommute));
        match &set.laws[1].rule {
            Rule::No(s) => {
                assert_eq!(s.kind.as_deref(), Some("call"));
                assert_eq!(s.to.as_deref(), Some("mail.send"));
                assert_eq!(s.conds.len(), 2);
            }
            r => panic!("{r:?}"),
        }
        assert!(matches!(&set.laws[2].rule, Rule::Each(s, c) if s.name.as_deref() == Some("payment-writer") && c.len() == 1));
        assert!(matches!(&set.laws[3].rule, Rule::Agrees { convert } if convert[0].factor == "100"));
    }
}
