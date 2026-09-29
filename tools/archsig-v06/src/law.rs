//! 第4章の Law ファイル。ファイルは読まず、`archmap` から渡された中身を解く。
//! 字句と文法は設計 §4.1〜4.2、名前の解決は §4.3。

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

/// 読んだ Law ファイルすべて。解けなかった宣言と解決の誤りは `errors` に集める。
/// 誤りが一つでもあれば、この Law は使えない(設計 §4.3)。
#[derive(Clone, Debug, Default)]
pub struct LawSet {
    pub files: Vec<String>,
    /// `sources` の宣言。`except` はその宣言にだけ効く。
    pub sources: Vec<Sources>,
    pub readings: Vec<Reading>,
    pub fresh: Vec<String>,
    pub meanings: Vec<Meaning>,
    pub defs: Vec<Def>,
    pub laws: Vec<Law>,
    pub errors: Vec<LawError>,
}

#[derive(Clone, Debug, Default)]
pub struct Sources {
    pub include: Vec<String>,
    pub except: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Reading {
    pub name: String,
    pub form: ReadingForm,
    pub at: String,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ReadingForm {
    Dir { depth: usize },
    File,
    Groups { groups: Vec<(String, Vec<String>)> },
}

#[derive(Clone, Debug, Serialize)]
pub struct Meaning {
    pub name: String,
    pub on: Vec<String>,
    pub to: Option<String>,
    pub values: Vec<String>,
    pub hint: String,
    pub at: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct Def {
    pub name: String,
    pub selector: Selector,
    pub at: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct Law {
    pub name: String,
    pub description: String,
    pub on: Option<String>,
    pub about: Option<String>,
    pub rule: Rule,
    pub at: String,
}

/// 規則の五つの形。`form` の値はマニュアル第4章の呼び方。
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "form")]
pub enum Rule {
    #[serde(rename = "no")]
    No { select: Selector },
    #[serde(rename = "each")]
    Each { select: Selector, require: Vec<Cond> },
    #[serde(rename = "agrees along")]
    Agrees { convert: Vec<Convert> },
    #[serde(rename = "changes commute")]
    ChangesCommute,
    #[serde(rename = "changes keep")]
    ChangesKeep,
    #[serde(rename = "roundtrips")]
    Roundtrips { read: String, update: String },
}

impl Rule {
    pub fn form(&self) -> &'static str {
        match self {
            Rule::No { .. } => "no",
            Rule::Each { .. } => "each",
            Rule::Agrees { .. } => "agrees along",
            Rule::ChangesCommute => "changes commute",
            Rule::ChangesKeep => "changes keep",
            Rule::Roundtrips { .. } => "roundtrips",
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Convert {
    pub from: String,
    pub to: String,
    pub op: String,
    pub factor: String,
}

/// 要素の選び方。`name` は意味の語彙の名前か `def` の名前で、解決で `def` は展開する。
#[derive(Clone, Debug, Default, Serialize)]
pub struct Selector {
    pub kind: Option<String>,
    pub to: Option<String>,
    pub pattern: Option<String>,
    pub name: Option<String>,
    pub that: Vec<Cond>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "cond", rename_all = "snake_case")]
pub enum Cond {
    Rel { rel: String, target: Selector },
    Has { meaning: String, value: Option<String> },
    Inside { local: String },
    Outside { local: String },
}

#[derive(Clone, Debug, Serialize)]
pub struct LawError {
    pub at: String,
    pub message: String,
}

pub const ELEMENT_KINDS: &[&str] = &["operation", "type", "field", "param", "call", "channel"];
const REL_WORDS: &[&str] = &["writes", "reads", "calls", "sends", "receives", "reaches"];

impl LawSet {
    /// `entries` の Law ファイルを読む。`read` はリポジトリの中の相対パスから中身を返す。
    /// `include` は、取り込む側のファイルの場所から読み、一つのファイルを二度読まない。
    pub fn load(entries: &[String], read: &dyn Fn(&str) -> Result<String, String>) -> LawSet {
        let mut set = LawSet::default();
        let mut seen = BTreeSet::new();
        for e in entries {
            set.load_file(e, e, read, &mut seen);
        }
        set.resolve();
        set
    }

    fn error(&mut self, at: &str, message: impl Into<String>) {
        self.errors.push(LawError { at: at.to_string(), message: message.into() });
    }

    fn load_file(&mut self, path: &str, from: &str, read: &dyn Fn(&str) -> Result<String, String>, seen: &mut BTreeSet<String>) {
        let path = normalize(path);
        if !seen.insert(path.clone()) {
            return;
        }
        let text = match read(&path) {
            Ok(t) => t,
            Err(e) => return self.error(from, e),
        };
        self.files.push(path.clone());
        for (line, block) in blocks(&text) {
            let at = format!("{path}:{line}");
            if let Err(e) = self.declaration(&path, &at, &block, read, seen) {
                self.error(&at, e);
            }
        }
    }

    fn declaration(
        &mut self,
        path: &str,
        at: &str,
        block: &[String],
        read: &dyn Fn(&str) -> Result<String, String>,
        seen: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        let head = lex(&block[0])?;
        let rest = block[1..].iter().map(|l| lex(l)).collect::<Result<Vec<_>, _>>()?;
        match word_at(&head, 0).as_deref() {
            Some("sources") => {
                let mut decl = Sources { include: strings(&head[1..])?, except: Vec::new() };
                for r in &rest {
                    if word_at(r, 0).as_deref() != Some("except") {
                        return Err("sources の下には except だけを書く".to_string());
                    }
                    decl.except.extend(strings(&r[1..])?);
                }
                for p in decl.include.iter().chain(&decl.except) {
                    check_pattern(p)?;
                }
                self.sources.push(decl);
            }
            Some("include") => {
                no_body(&rest, "include")?;
                let dir = path.rsplit_once('/').map(|(d, _)| d).unwrap_or("");
                for inc in strings(&head[1..])? {
                    let target = if dir.is_empty() { inc } else { format!("{dir}/{inc}") };
                    self.load_file(&target, at, read, seen);
                }
            }
            Some("fresh") => {
                no_body(&rest, "fresh")?;
                let patterns = strings(&head[1..])?;
                for p in &patterns {
                    check_pattern(p)?;
                }
                self.fresh.extend(patterns);
            }
            Some("reading") => self.readings.push(parse_reading(&head, &rest, at)?),
            Some("meaning") => self.meanings.push(parse_meaning(&head, &rest, at)?),
            Some("law") => self.laws.push(parse_law(&head, &rest, at)?),
            Some("def") => {
                let name = word_at(&head, 1).ok_or("def の名前がない")?;
                if head.get(2) != Some(&Tok::Sym("=")) {
                    return Err("def には `=` が要る".to_string());
                }
                if !rest.is_empty() {
                    return Err("def は一行で書く".to_string());
                }
                let mut c = Cursor { t: &head[3..], i: 0 };
                let selector = c.selector()?;
                c.end()?;
                self.defs.push(Def { name, selector, at: at.to_string() });
            }
            Some(other) => return Err(format!("知らない宣言 `{other}`")),
            None => return Err("宣言の語がない".to_string()),
        }
        Ok(())
    }

    /// 設計 §4.3 の名前の解決。`def` を展開し、`on` を補い、誤りを `errors` に集める。
    fn resolve(&mut self) {
        let mut errors = Vec::new();
        duplicates(self.readings.iter().map(|r| (&r.name, &r.at)), "読み", &mut errors);
        duplicates(self.meanings.iter().map(|m| (&m.name, &m.at)), "意味", &mut errors);
        duplicates(self.defs.iter().map(|d| (&d.name, &d.at)), "def", &mut errors);
        duplicates(self.laws.iter().map(|l| (&l.name, &l.at)), "law", &mut errors);
        let mut meanings: BTreeMap<String, Meaning> = BTreeMap::new();
        for m in &self.meanings {
            meanings.entry(m.name.clone()).or_insert_with(|| m.clone());
        }
        let readings: BTreeSet<String> = self.readings.iter().map(|r| r.name.clone()).collect();
        let first_reading = self.readings.first().map(|r| r.name.clone());
        let def_names: BTreeSet<String> = self.defs.iter().map(|d| d.name.clone()).collect();
        let no_defs = BTreeMap::new();
        let mut defs = BTreeMap::new();
        for d in &mut self.defs {
            if meanings.contains_key(&d.name) {
                errors.push(LawError { at: d.at.clone(), message: format!("`{}` は意味の語彙にもある。def には別の名前を付ける", d.name) });
            }
            let mut ctx = Resolve { meanings: &meanings, defs: &no_defs, def_names: &def_names, in_def: true, errors: Vec::new(), at: &d.at };
            ctx.selector(&mut d.selector);
            if ctx.errors.is_empty() {
                defs.insert(d.name.clone(), d.selector.clone());
            }
            errors.extend(ctx.errors);
        }
        for law in &mut self.laws {
            let at = law.at.clone();
            let mut ctx = Resolve { meanings: &meanings, defs: &defs, def_names: &def_names, in_def: false, errors: Vec::new(), at: &at };
            match &law.on {
                Some(r) if !readings.contains(r) => ctx.error(format!("読み `{r}` が宣言されていない")),
                Some(_) => {}
                None => match &first_reading {
                    Some(r) => law.on = Some(r.clone()),
                    None => ctx.error("on を省いた Law が使う読みが、一つも宣言されていない".to_string()),
                },
            }
            let about = law.about.as_ref().and_then(|m| meanings.get(m));
            if let (Some(m), None) = (&law.about, about) {
                ctx.error(format!("意味 `{m}` が宣言されていない"));
            }
            let needs_about = matches!(law.rule, Rule::Agrees { .. } | Rule::ChangesCommute | Rule::ChangesKeep | Rule::Roundtrips { .. });
            if needs_about && law.about.is_none() {
                ctx.error(format!("{} の規則には about が要る", law.rule.form()));
            }
            match &mut law.rule {
                Rule::No { select } => ctx.selector(select),
                Rule::Each { select, require } => {
                    ctx.selector(select);
                    for c in require {
                        ctx.cond(c);
                    }
                }
                Rule::Agrees { convert } => {
                    if let Some(m) = about {
                        for c in convert.iter() {
                            for v in [&c.from, &c.to] {
                                if !m.values.contains(v) {
                                    ctx.error(format!("convert の `{v}` は意味 `{}` の values にない", m.name));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            errors.extend(ctx.errors);
        }
        self.errors.extend(errors);
    }
}

/// 同じ名前の二度目からの宣言を誤りとする。
fn duplicates<'a>(items: impl Iterator<Item = (&'a String, &'a String)>, what: &str, errors: &mut Vec<LawError>) {
    let mut seen = BTreeSet::new();
    for (name, at) in items {
        if !seen.insert(name) {
            errors.push(LawError { at: at.clone(), message: format!("{what} `{name}` が二度宣言されている") });
        }
    }
}

struct Resolve<'a> {
    meanings: &'a BTreeMap<String, Meaning>,
    /// 誤りなく解けた `def`。
    defs: &'a BTreeMap<String, Selector>,
    def_names: &'a BTreeSet<String>,
    /// `def` の右辺を解いているか。`def` の中では `def` を使えない。
    in_def: bool,
    errors: Vec<LawError>,
    at: &'a str,
}

impl Resolve<'_> {
    fn error(&mut self, message: String) {
        self.errors.push(LawError { at: self.at.to_string(), message });
    }

    /// 名前を確かめ、`def` の名前なら展開する。
    fn selector(&mut self, sel: &mut Selector) {
        if let Some(n) = sel.name.clone() {
            if self.in_def && self.def_names.contains(&n) {
                self.error(format!("def の中で def `{n}` は使えない"));
            } else if let Some(d) = self.defs.get(&n) {
                let mut that = d.that.clone();
                that.append(&mut sel.that);
                *sel = Selector { that: Vec::new(), ..d.clone() };
                for mut c in that.drain(..) {
                    self.cond(&mut c);
                    sel.that.push(c);
                }
                return;
            } else if !self.meanings.contains_key(&n) && !self.def_names.contains(&n) {
                self.error(format!("`{n}` は意味の語彙にも def にもない"));
            }
        }
        for c in &mut sel.that {
            self.cond(c);
        }
    }

    fn cond(&mut self, c: &mut Cond) {
        match c {
            Cond::Rel { target, .. } => self.selector(target),
            Cond::Has { meaning, value } => match self.meanings.get(meaning.as_str()) {
                None => self.error(format!("意味 `{meaning}` が宣言されていない")),
                Some(m) => match value {
                    Some(v) if !m.values.contains(v) => self.error(format!("値 `{v}` は意味 `{meaning}` の values にない")),
                    _ => {}
                },
            },
            _ => {}
        }
    }
}

/// 字下げした続きの行を持たない宣言。
fn no_body(rest: &[Vec<Tok>], what: &str) -> Result<(), String> {
    if rest.is_empty() { Ok(()) } else { Err(format!("{what} の下には何も書かない")) }
}

/// パスや名前のパターンが読めるか。`*` は `/` をまたがず、`**` はまたぐ。
fn check_pattern(p: &str) -> Result<(), String> {
    globset::GlobBuilder::new(p).literal_separator(true).build().map(|_| ()).map_err(|e| format!("パターン `{p}` が読めない: {e}"))
}

/// `a/./b/../c` を `a/c` にそろえる。
fn normalize(path: &str) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for p in path.split('/') {
        match p {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            _ => parts.push(p),
        }
    }
    parts.join("/")
}

fn parse_reading(head: &[Tok], rest: &[Vec<Tok>], at: &str) -> Result<Reading, String> {
    let name = word_at(head, 1).ok_or("reading の名前がない")?;
    if head.get(2) != Some(&Tok::Sym("=")) {
        return Err("reading には `=` が要る".to_string());
    }
    let form = match word_at(head, 3).as_deref() {
        Some("dir") => match &head[4..] {
            [Tok::Sym("("), Tok::Word(d), Tok::Sym(":"), Tok::Word(n), Tok::Sym(")")] if d == "depth" => {
                ReadingForm::Dir { depth: n.parse().map_err(|_| "depth は整数で書く")? }
            }
            _ => return Err("dir は dir(depth: n) と書く".to_string()),
        },
        Some("file") if head.len() == 4 => ReadingForm::File,
        Some("groups") if head.len() == 4 => {
            let mut groups = Vec::new();
            for r in rest {
                let g = word_at(r, 0).filter(|_| r.get(1) == Some(&Tok::Sym(":"))).ok_or("groups の各行は `名前: \"パターン\"` と書く")?;
                let patterns = strings(&r[2..])?;
                for p in &patterns {
                    check_pattern(p)?;
                }
                groups.push((g, patterns));
            }
            if groups.is_empty() {
                return Err("groups に局所がない".to_string());
            }
            ReadingForm::Groups { groups }
        }
        _ => return Err("読みの形は dir(depth: n)、file、groups のどれか".to_string()),
    };
    if !matches!(form, ReadingForm::Groups { .. }) && !rest.is_empty() {
        return Err("dir と file の読みの下には何も書かない".to_string());
    }
    Ok(Reading { name, form, at: at.to_string() })
}

fn parse_meaning(head: &[Tok], rest: &[Vec<Tok>], at: &str) -> Result<Meaning, String> {
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
            _ => return Err("meaning の on には要素の種類を書く".to_string()),
        }
    }
    if on.is_empty() {
        return Err("meaning の on に要素の種類がない".to_string());
    }
    let mut values = Vec::new();
    let mut hint = None;
    for r in rest {
        match r.first() {
            Some(Tok::Word(w)) if w == "values" => {
                if !values.is_empty() {
                    return Err("values は一度だけ書く".to_string());
                }
                if r.len() % 2 != 0 {
                    return Err("values は `a | b` と書く".to_string());
                }
                for (k, t) in r[1..].iter().enumerate() {
                    match t {
                        Tok::Word(v) if k % 2 == 0 => values.push(v.clone()),
                        Tok::Sym("|") if k % 2 == 1 => {}
                        _ => return Err("values は `a | b` と書く".to_string()),
                    }
                }
            }
            Some(Tok::Str(s)) if r.len() == 1 => {
                if hint.replace(s.clone()).is_some() {
                    return Err("観測の手がかりは一つだけ書く".to_string());
                }
            }
            _ => return Err("meaning の下には values と観測の手がかりを書く".to_string()),
        }
    }
    let hint = hint.ok_or("meaning に観測の手がかりがない")?;
    Ok(Meaning { name, on, to, values, hint, at: at.to_string() })
}

fn parse_law(head: &[Tok], rest: &[Vec<Tok>], at: &str) -> Result<Law, String> {
    let name = word_at(head, 1).filter(|_| head.len() == 2).ok_or("law は `law <名前>` と書く")?;
    let mut description = None;
    let mut on = None;
    let mut about = None;
    let mut rule_lines: Vec<&Vec<Tok>> = Vec::new();
    for r in rest {
        match r.first() {
            Some(Tok::Str(s)) if r.len() == 1 && rule_lines.is_empty() => {
                if description.replace(s.clone()).is_some() {
                    return Err("law の説明は一つだけ書く".to_string());
                }
            }
            Some(Tok::Word(w)) if (w == "on" || w == "about") && rule_lines.is_empty() => {
                let name = match r.as_slice() {
                    [_, Tok::Word(n)] => n.clone(),
                    _ => return Err(format!("{w} の後には名前を一つ書く")),
                };
                let slot = if w == "on" { &mut on } else { &mut about };
                if slot.replace(name).is_some() {
                    return Err(format!("{w} は一度だけ書く"));
                }
            }
            _ => rule_lines.push(r),
        }
    }
    let description = description.ok_or("law に説明がない")?;
    let first = rule_lines.first().ok_or("law に規則がない")?;
    let rule = match word_at(first, 0).as_deref() {
        Some("no") => {
            if rule_lines.len() > 1 {
                return Err("no の規則は一行で書く".to_string());
            }
            let mut c = Cursor { t: &first[1..], i: 0 };
            let select = c.selector()?;
            c.end()?;
            Rule::No { select }
        }
        Some("each") => {
            let mut c = Cursor { t: &first[1..], i: 0 };
            let select = c.selector()?;
            c.end()?;
            let mut require = Vec::new();
            for r in &rule_lines[1..] {
                let mut c = Cursor { t: r, i: 0 };
                require.extend(c.conds()?);
                c.end()?;
            }
            if require.is_empty() {
                return Err("each の二行目に条件がない".to_string());
            }
            Rule::Each { select, require }
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
                        if !(f.len() >= 2 && f.starts_with('1') && f[1..].chars().all(|c| c == '0')) {
                            return Err("convert の倍率は 10 の冪(10、100、1000 …)で書く".to_string());
                        }
                        convert.push(Convert { from: from.clone(), to: to.clone(), op: op.to_string(), factor: f.clone() })
                    }
                    _ => return Err("convert は `convert a -> b by * 100` と書く".to_string()),
                }
            }
            Rule::Agrees { convert }
        }
        Some("changes") => {
            if rule_lines.len() > 1 {
                return Err("changes の規則は一行で書く".to_string());
            }
            match (word_at(first, 1).as_deref(), first.len()) {
                (Some("keep"), 2) => Rule::ChangesKeep,
                (Some("commute"), 4) if word_at(first, 2).as_deref() == Some("with") && word_at(first, 3).as_deref() == Some("operations") => {
                    Rule::ChangesCommute
                }
                _ => return Err("changes commute with operations か changes keep と書く".to_string()),
            }
        }
        Some("roundtrips") => match first.as_slice() {
            [Tok::Word(_), Tok::Word(r), Tok::Str(read), Tok::Word(u), Tok::Str(update)] if r == "read" && u == "update" && rule_lines.len() == 1 => {
                Rule::Roundtrips { read: read.clone(), update: update.clone() }
            }
            _ => return Err("roundtrips read \"…\" update \"…\" と書く".to_string()),
        },
        _ => return Err("規則は no、each、agrees、changes、roundtrips のどれかで始める".to_string()),
    };
    Ok(Law { name, description, on, about, rule, at: at.to_string() })
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
            return Err("規則の続きが読めない".to_string());
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
            sel.that = self.conds()?;
            if sel.that.is_empty() {
                return Err("that の後に条件がない".to_string());
            }
        }
        Ok(sel)
    }

    fn conds(&mut self) -> Result<Vec<Cond>, String> {
        let mut out = Vec::new();
        while let Some(w) = self.peek_word() {
            let w = w.to_string();
            self.i += 1;
            if w == "and" {
                continue;
            }
            let c = if REL_WORDS.contains(&w.as_str()) {
                Cond::Rel { rel: w, target: self.base()? }
            } else if w == "has" {
                let meaning = self.peek_word().ok_or("has の後に意味がない")?.to_string();
                self.i += 1;
                let value = match self.peek_word() {
                    Some(v) if !is_keyword(v) => {
                        let v = v.to_string();
                        self.i += 1;
                        Some(v)
                    }
                    _ => None,
                };
                Cond::Has { meaning, value }
            } else if w == "inside" {
                Cond::Inside { local: self.string().ok_or("inside の後に局所がない")? }
            } else if w == "outside" {
                Cond::Outside { local: self.string().ok_or("outside の後に局所がない")? }
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


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn include_reads_each_file_once() {
        let files = |p: &str| -> Result<String, String> {
            match p {
                ".archsig/law/a.law" => Ok("sources \"shop/**\"\n  except \"**/tests/**\"\n\nmeaning m on field\n  \"#でない\"\n\ninclude \"sub/b.law\"\n".to_string()),
                ".archsig/law/sub/b.law" => Ok("meaning n on call to \"mail.send\"  # コメント\n  values x | y\n  \"手がかり\"\ninclude \"../a.law\"\n".to_string()),
                _ => Err(format!("ない: {p}")),
            }
        };
        let set = LawSet::load(&[".archsig/law/a.law".to_string()], &files);
        assert!(set.errors.is_empty(), "{:?}", set.errors);
        assert_eq!(set.files, vec![".archsig/law/a.law", ".archsig/law/sub/b.law"]);
        assert_eq!(set.sources[0].include, vec!["shop/**"]);
        assert_eq!(set.sources[0].except, vec!["**/tests/**"]);
        let names: Vec<&str> = set.meanings.iter().map(|m| m.name.as_str()).collect();
        assert_eq!(names, vec!["m", "n"]);
        assert_eq!(set.meanings[1].values, vec!["x", "y"]);
        assert_eq!(set.meanings[1].to.as_deref(), Some("mail.send"));
    }
}
