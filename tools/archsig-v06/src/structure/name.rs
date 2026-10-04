//! 名前の解決(設計 §3.3)。名前が指す要素と、その要素が何かを決める問い合わせは、ここにだけ置く。
//! 式の道と書き込みの場所、名指し、選択、書いた場所より先と本体の比べ、局所は、この問い合わせの答えだけを使う。

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::{Reason, Silence, Structure, locate, question};
use crate::atom::{Atom, parse_location};
use crate::expr::{self, Expr};

/// 名前の形(設計 §3.3 の表)。形だけで種類が決まる名前と、構造を見て決まる名前を分ける。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Form<'a> {
    /// `?` で始まる。
    Question,
    /// `<操作>.$<名前>`。
    Param { owner: &'a str, name: &'a str },
    /// `<呼び出し元>-><呼び出し先>`、`…#n`。
    Call { caller: &'a str },
    /// `channel:<種類>:<名前>`、`…:<項目>`。
    Channel,
    /// `local:` で始まる、局所ごとの意味 Atom の名前。要素の名前とは別の種類の名前である。
    Local,
    /// `<段>.<段>…`。操作、型、フィールド、または定義のない名前。構造を見て決める。
    Dotted,
}

/// 名前の形を読む。形は、ここだけで読む。
pub fn form(n: &str) -> Form<'_> {
    if n.starts_with('?') {
        return Form::Question;
    }
    if n.starts_with("channel:") {
        return Form::Channel;
    }
    if n.starts_with("local:") {
        return Form::Local;
    }
    if let Some((caller, _)) = n.split_once("->") {
        return Form::Call { caller };
    }
    if let Some((owner, name)) = n.split_once(".$") {
        return Form::Param { owner, name };
    }
    Form::Dotted
}

/// `:` で四つ以上に分かれる名前の、最後の項目を除いた名前(設計 §3.2)。
pub fn channel_of(item: &str) -> Option<&str> {
    let parts = item.split(':').count();
    (parts >= 4).then(|| item.rsplit_once(':').map(|(c, _)| c)).flatten()
}

pub fn is_question(n: &str) -> bool {
    form(n) == Form::Question
}

pub fn is_local(n: &str) -> bool {
    form(n) == Form::Local
}

/// 名前 `n` が `x` か、`x` の下の名前(`x.…`、`x->…`、`x.$…`)か(設計 §3.3)。
pub fn below(x: &str, n: &str) -> bool {
    n == x || n.strip_prefix(x).is_some_and(|rest| rest.starts_with('.') || rest.starts_with("->"))
}

/// 名前 `n` が `x` か、`x` から出る呼び出し(`x->…`)か。
pub fn from_operation(x: &str, n: &str) -> bool {
    n == x || n.strip_prefix(x).is_some_and(|rest| rest.starts_with("->"))
}

/// 名前 `n` が `x` か `x` から出る呼び出しなら、`x` の後の部分(`""` か `->…`)。
pub fn after_operation<'n>(x: &str, n: &'n str) -> Option<&'n str> {
    from_operation(x, n).then(|| &n[x.len()..])
}

/// 名前 `n` が操作 `x` の引数(`x.$…`)か。
pub fn param_of(x: &str, n: &str) -> bool {
    matches!(form(n), Form::Param { owner, .. } if owner == x)
}

/// 引数と呼び出しの持ち主の操作。それ以外の名前は、その名前のまま。
pub fn owner(n: &str) -> &str {
    match form(n) {
        Form::Param { owner, .. } => owner,
        Form::Call { caller } => caller,
        _ => n,
    }
}

pub fn param_name(op: &str, p: &str) -> String {
    format!("{op}.${p}")
}

/// 呼び出しの要素の名前。`order` は、その操作の中で同じ呼び出し先を呼ぶ何番目か(1から)。
pub fn call_name(caller: &str, callee: &str, order: usize) -> String {
    if order == 1 { format!("{caller}->{callee}") } else { format!("{caller}->{callee}#{order}") }
}

/// `corresponds` の行き先。`|` を含めば決めていない対応で、空の欄は捨てる(設計 §3.6)。
pub fn targets(object: &str) -> (Vec<String>, bool) {
    (object.split('|').map(|t| t.trim().to_string()).filter(|t| !t.is_empty()).collect(), object.contains('|'))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resolution {
    Source(String),
    External(String),
    /// 指す先の違う `resolves` が二つ以上ある。解決が決まらない。
    Undecided,
}

/// 決まった要素。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Found {
    /// 解いた要素の名前。
    pub name: String,
    /// `operation`、`type`、`field`、`param`、`call`、`channel` のどれか。
    pub kind: String,
    /// 定義した所(ソースのパス)。候補の中で定義した要素は `file`。`file` のない候補の定義では空。
    pub defined: BTreeSet<String>,
    /// 候補の中で定義した要素か。
    pub planned: bool,
    /// フィールドと引数の型。
    pub ty: Option<String>,
    /// 引数と呼び出しの持ち主の操作。
    pub owner: Option<String>,
    /// 操作の引数と型。
    pub params: BTreeMap<String, String>,
}

/// 名前の答え(設計 §3.3)。分からないときは `Unknown` を返す。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    Element(Found),
    /// 外部の要素。`resolves` が外部を指す、定義のない名前。パッケージを持つ。
    External(String),
    /// 名前だけの要素。字句どおりの名前をそのまま要素として扱う。
    Bare(String),
}

/// 分からない答えの別。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    /// `?` で始まる名前。
    Question,
    /// 定義を読んでいない。
    Unread,
    /// `resolves` の指すソースを読んだのに、定義がない。
    Missing,
    /// 指す先の違う `resolves` が二つ以上ある。
    Undecided,
    /// 定義はあるが決まらない(種類の違う `defines`、`value` のない `defines`、二か所の `defines`)。
    Ambiguous,
    /// それ以外(型でない要素を型として使う、外部の型のフィールドなど)。
    Other,
}

/// 段で決まらなかった所。型と名前。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage {
    pub ty: String,
    pub name: String,
    /// 頭と受け継がれる型がすべて決まり、どの型も名前を定義しないために決まらなかった(段の「なければ」)。
    pub absent: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unknown {
    pub silence: Silence,
    pub why: Why,
    pub stage: Option<Box<Stage>>,
    /// 曖昧な要素の定義した所。
    pub defined: BTreeSet<String>,
    /// 名前そのものの定義(`defines` か `resolves`)で決まらない答えか。頭、持ち主、段で決まらない答えは偽。
    pub itself: bool,
}

impl Unknown {
    fn new(silence: Silence, why: Why) -> Unknown {
        Unknown { silence, why, stage: None, defined: BTreeSet::new(), itself: false }
    }

    fn unresolved(why: Why) -> Unknown {
        Unknown::new(Silence::new(Reason::Unresolved), why)
    }

    /// 定義を読んでいない要素。読む所は要素の名前。どのソースを読むかは SKILL が決める。
    fn unread(name: &str) -> Unknown {
        Unknown::new(Silence { reason: Reason::Unread, read: None, element: Some(name.to_string()), scope: None }, Why::Unread)
    }

    fn at(self, ty: &str, name: &str, absent: bool) -> Unknown {
        Unknown { stage: Some(Box::new(Stage { ty: ty.to_string(), name: name.to_string(), absent })), itself: false, ..self }
    }

    /// 名前そのものの定義で決まらない答えにする。
    fn own(self) -> Unknown {
        Unknown { itself: true, ..self }
    }

    /// 頭、持ち主、型の答えを、その下の名前の答えにする。
    fn derived(self) -> Unknown {
        Unknown { itself: false, ..self }
    }
}

pub type Resolved = Result<Answer, Unknown>;

/// 構造の中の要素(設計 §3.2)。
#[derive(Clone, Debug, Default)]
struct Element {
    /// `defines` の `value` か、構造 Atom から作る種類。二つ以上あれば曖昧である。
    kinds: BTreeSet<String>,
    params: BTreeMap<String, String>,
    ty: Option<String>,
    /// `defines` を書いた場所(`at`)。
    defined: BTreeSet<String>,
    /// 候補の中の `defines` の `file`。
    file: Option<String>,
    /// `defines` を持つか。
    declared: bool,
}

impl Element {
    fn undecided(&self) -> bool {
        self.kinds.len() > 1 || self.kinds.contains("") || self.defined.len() > 1
    }

    /// 定義した所。候補の中の定義は `file`、それ以外は `at` のソース。
    fn sources(&self) -> BTreeSet<String> {
        self.defined
            .iter()
            .filter_map(|at| match &self.file {
                Some(f) if at.starts_with("plan:") => Some(f.clone()),
                _ if at.starts_with("plan:") => None,
                _ => parse_location(at).map(|l| l.path),
            })
            .collect()
    }

    fn planned(&self) -> bool {
        self.defined.iter().any(|at| at.starts_with("plan:"))
    }
}

/// 名前の解決が使う構造の中身。外からは問い合わせを通してだけ読む。
#[derive(Clone, Debug, Default)]
pub struct Names {
    elements: BTreeMap<String, Element>,
    resolves: BTreeMap<String, Resolution>,
    observed: BTreeSet<(String, String)>,
    /// 受け継ぐ型ごとの、受け継がれる型。
    inherits: BTreeMap<String, BTreeSet<String>>,
    /// 型として名指された名前(要素の型、引数の型、`inherits` の `object`)。
    typed: BTreeSet<String>,
    /// 候補が定義し直した読んでいない要素と、その変更前の沈黙(設計 §3.6)。
    redefined: BTreeMap<String, Unknown>,
    /// 候補が `removes` した要素。
    removes: BTreeSet<String>,
    /// チャネルと項目ごとの、送る操作と受け取る操作。
    channels: BTreeMap<String, BTreeSet<String>>,
    /// 答えを求めている途中の問い合わせ。問い合わせはめぐらない。
    busy: RefCell<BTreeSet<String>>,
}

impl Names {
    /// Atom の列から要素を作る(設計 §3.2)。`calls` は、呼び出しの要素の名前。
    pub(super) fn build(atoms: &[Atom], calls: &BTreeMap<usize, String>) -> Names {
        let mut s = Names::default();
        for a in atoms {
            match a.kind.as_str() {
                "defines" => {
                    let e = s.elements.entry(a.subject.clone()).or_default();
                    e.kinds.insert(a.value.clone().unwrap_or_default());
                    e.defined.insert(a.at.clone().unwrap_or_default());
                    e.declared = true;
                    if let Some(p) = &a.params {
                        e.params.extend(p.clone());
                        s.typed.extend(p.values().cloned());
                    }
                    if a.ty.is_some() {
                        e.ty = a.ty.clone();
                        s.typed.extend(a.ty.clone());
                    }
                    if a.file.is_some() {
                        e.file = a.file.clone();
                    }
                }
                // チャネルとその項目は、`sends` と `receives` に現れた名前から要素になる。
                "sends" | "receives" => {
                    let item = a.object.clone().unwrap_or_default();
                    if let Some(c) = channel_of(&item) {
                        s.elements.entry(c.to_string()).or_default().kinds.insert("channel".to_string());
                        s.channels.entry(c.to_string()).or_default().insert(a.subject.clone());
                    }
                    s.elements.entry(item.clone()).or_default().kinds.insert("channel".to_string());
                    s.channels.entry(item).or_default().insert(a.subject.clone());
                }
                "resolves" => {
                    let o = a.object.clone().unwrap_or_default();
                    let r = match o.strip_prefix("external:") {
                        Some(pkg) => Resolution::External(pkg.to_string()),
                        None => Resolution::Source(o),
                    };
                    match s.resolves.get(&a.subject) {
                        Some(x) if *x != r => {
                            s.resolves.insert(a.subject.clone(), Resolution::Undecided);
                        }
                        Some(_) => {}
                        None => {
                            s.resolves.insert(a.subject.clone(), r);
                        }
                    }
                }
                "inherits" => {
                    if let Some(o) = &a.object {
                        s.inherits.entry(a.subject.clone()).or_default().insert(o.clone());
                        s.typed.insert(o.clone());
                    }
                }
                "observed" => {
                    s.observed.insert((a.subject.clone(), a.scope.clone().unwrap_or_default()));
                }
                _ => {}
            }
        }
        // 引数は、操作の `params` から要素になる。
        let params: Vec<(String, String)> =
            s.elements.iter().flat_map(|(op, e)| e.params.iter().map(move |(p, t)| (param_name(op, p), t.clone()))).collect();
        for (name, ty) in params {
            let e = s.elements.entry(name).or_default();
            e.kinds.insert("param".to_string());
            e.ty = Some(ty);
        }
        for name in calls.values() {
            s.elements.entry(name.clone()).or_default().kinds.insert("call".to_string());
        }
        s
    }
}

impl Structure {
    /// 候補を重ねた構造に、定義し直した読んでいない要素と `removes` した要素の集合を持たせる(設計 §3.6)。
    pub(super) fn carry(&mut self, redefined: BTreeMap<String, Unknown>, removes: BTreeSet<String>) {
        self.names.redefined = redefined;
        self.names.removes = removes;
    }

    /// この構造に候補 `plan` を重ねた構造が持つ、定義し直した読んでいない要素と `removes` した要素の集合(設計 §3.6)。
    /// この構造が元の候補を重ねた構造なら、そのものを引き継ぐ。
    /// 定義し直した読んでいない要素は、候補が `defines` を書いた名前のうち、この構造に `defines` がなく、この構造が名指す名前であるもの。
    /// 変更前に外部の要素だったものは除き、候補の定義をその要素のすべてとする。
    pub(super) fn layered(&self, plan: &[Atom]) -> (BTreeMap<String, Unknown>, BTreeSet<String>) {
        let mut redefined = self.names.redefined.clone();
        let mentioned = self.mentioned();
        for n in plan.iter().filter(|a| a.kind == "defines").map(|a| &a.subject) {
            if redefined.contains_key(n) || self.declared(n) || !mentioned.contains(n) {
                continue;
            }
            match self.element(n) {
                Ok(Answer::External(_)) => {}
                Err(u) => {
                    redefined.insert(n.clone(), u);
                }
                Ok(_) => {
                    redefined.insert(n.clone(), Unknown::unread(n));
                }
            }
        }
        let mut removes = self.names.removes.clone();
        removes.extend(plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.clone()));
        (redefined, removes)
    }

    /// 候補が `removes` した要素を除いてたどる構造。変更前の構造で書いた場所より先をたどるときに使う(設計 §5.4)。
    pub fn with_removes(&self, removes: &BTreeSet<String>) -> Structure {
        let mut s = self.clone();
        s.names.removes.extend(removes.iter().cloned());
        s
    }

    /// ソース `source` の範囲 `scope` を読んだか。
    pub fn observed(&self, source: &str, scope: &str) -> bool {
        self.names.observed.contains(&(source.to_string(), scope.to_string()))
    }

    /// 名前そのものの解決(`resolves`)。
    pub fn resolution(&self, n: &str) -> Option<&Resolution> {
        self.names.resolves.get(n)
    }

    /// 名前が `defines` を持つか。
    pub fn declared(&self, n: &str) -> bool {
        self.names.elements.get(n).is_some_and(|e| e.declared)
    }

    /// 構造の要素の名前(定義した要素と、Atom から要素になる引数、呼び出し、チャネルとその項目)。
    pub fn element_names(&self) -> impl Iterator<Item = &String> {
        self.names.elements.keys()
    }

    /// 操作かもしれない要素(種類が操作か、決まらない)と、その引数の型と、二か所以上に定義したか。
    pub fn operations(&self) -> Vec<(&str, Vec<&str>, bool)> {
        self.names
            .elements
            .iter()
            .filter(|(_, e)| e.declared && (e.kinds.contains("operation") || e.kinds.contains("")))
            .map(|(n, e)| (n.as_str(), e.params.values().map(String::as_str).collect(), e.defined.len() > 1))
            .collect()
    }

    /// 送る操作と受け取る操作(チャネルとその項目)。
    pub fn channel_operations(&self, n: &str) -> Option<&BTreeSet<String>> {
        self.names.channels.get(n)
    }

    /// 要素(名前)。名前から、要素の種類、定義した所、型、持ち主を決める(設計 §3.3)。
    pub fn element(&self, n: &str) -> Resolved {
        let key = format!("e {n}");
        if !self.names.busy.borrow_mut().insert(key.clone()) {
            return Err(Unknown::unresolved(Why::Other));
        }
        let r = self.element_of(n);
        self.names.busy.borrow_mut().remove(&key);
        r
    }

    fn element_of(&self, n: &str) -> Resolved {
        match form(n) {
            // `?` で始まる名前は決まらない。読む所は、その名前を書いた Atom の場所(マニュアル第5章 問い8)。
            Form::Question => Err(Unknown::new(
                match self.atoms.iter().find(|a| a.subject == n || a.object.as_deref() == Some(n) || a.via.iter().flatten().any(|v| v == n)) {
                    Some(a) => locate(question(), a),
                    None => question(),
                },
                Why::Question,
            )),
            Form::Param { owner, name } => match self.element(owner).map_err(Unknown::derived)? {
                Answer::Element(op) if op.kind == "operation" => match op.params.get(name) {
                    Some(t) => Ok(Answer::Element(Found {
                        name: param_name(&op.name, name),
                        kind: "param".to_string(),
                        ty: Some(t.clone()),
                        owner: Some(op.name.clone()),
                        params: BTreeMap::new(),
                        ..op
                    })),
                    None => Err(Unknown::unresolved(Why::Other)),
                },
                Answer::External(pkg) => Ok(Answer::External(pkg)),
                _ => Err(Unknown::unresolved(Why::Other)),
            },
            Form::Call { caller } => {
                let owner = self.element(caller);
                let call = |f: &Found| Found {
                    name: n.to_string(),
                    kind: "call".to_string(),
                    defined: f.defined.clone(),
                    planned: f.planned,
                    ty: None,
                    owner: Some(f.name.clone()),
                    params: BTreeMap::new(),
                };
                // 構造にその呼び出しがあれば、持ち主は呼び出し元。なければ、持ち主の答えを返す。
                if self.names.elements.get(n).is_some_and(|e| e.kinds.contains("call")) {
                    return Ok(Answer::Element(match &owner {
                        Ok(Answer::Element(f)) => call(f),
                        _ => Found {
                            name: n.to_string(),
                            kind: "call".to_string(),
                            defined: BTreeSet::new(),
                            planned: false,
                            ty: None,
                            owner: Some(caller.to_string()),
                            params: BTreeMap::new(),
                        },
                    }));
                }
                match owner.map_err(Unknown::derived)? {
                    Answer::Element(f) => Ok(Answer::Element(call(&f))),
                    Answer::Bare(_) => Ok(Answer::Bare(n.to_string())),
                    other => Ok(other),
                }
            }
            // チャネルと項目は、`sends` か `receives` に現れていればそれ。定義した所は、送る操作と受け取る操作のそれすべて。
            Form::Channel if self.names.channels.contains_key(n) => {
                let mut defined = BTreeSet::new();
                for op in &self.names.channels[n] {
                    if let Ok(Answer::Element(f)) = self.element(op) {
                        defined.extend(f.defined);
                    }
                }
                Ok(Answer::Element(Found {
                    name: n.to_string(),
                    kind: "channel".to_string(),
                    defined,
                    planned: false,
                    ty: None,
                    owner: None,
                    params: BTreeMap::new(),
                }))
            }
            Form::Channel => self.by_resolves_or_head(n, None),
            Form::Local => Ok(Answer::Bare(n.to_string())),
            Form::Dotted => self.dotted(n),
        }
    }

    /// 頭。名前の前の段のうち、要素があるか(曖昧を含む)、`resolves` を持つか、型として名指された、いちばん長いもの。
    fn head<'n>(&self, n: &'n str) -> Option<(&'n str, &'n str)> {
        let mut end = n.len();
        while let Some(i) = n[..end].rfind('.') {
            let h = &n[..i];
            if self.names.elements.contains_key(h) || self.names.resolves.contains_key(h) || self.names.typed.contains(h) {
                return Some((h, &n[i + 1..]));
            }
            end = i;
        }
        None
    }

    fn dotted(&self, n: &str) -> Resolved {
        let head = self.head(n);
        // 5. 頭が型に決まれば、残りの最初の段を段(頭, 段)で解く。型に決まるときだけ、その型から続ける。
        if let Some((h, rest)) = head
            && let Ok(Answer::Element(t)) = self.element(h)
            && t.kind == "type"
        {
            let segments: Vec<&str> = rest.split('.').collect();
            let mut ty = t.name;
            for (i, seg) in segments.iter().enumerate() {
                let a = self.stage(&ty, seg)?;
                if i + 1 == segments.len() {
                    return Ok(a);
                }
                match a {
                    Answer::Element(f) if f.kind == "type" => ty = f.name,
                    _ => return Err(Unknown::unresolved(Why::Other)),
                }
            }
        }
        // 6. `defines` を持つ名前。
        if let Some(e) = self.names.elements.get(n).filter(|e| e.declared) {
            return self.decide(n, e);
        }
        self.by_resolves_or_head(n, head)
    }

    /// 規則 7 と 8。名前そのものの `resolves` で決め、なければ頭で決める。
    fn by_resolves_or_head(&self, n: &str, head: Option<(&str, &str)>) -> Resolved {
        if let Some(r) = self.names.resolves.get(n) {
            return self.resolved(r);
        }
        match head {
            Some((h, rest)) => match self.element(h) {
                Ok(Answer::External(pkg)) => Ok(Answer::External(pkg)),
                Ok(_) => Err(Unknown::unresolved(Why::Other)),
                // 頭が曖昧なら、頭の局所で見る(設計 §6)。
                Err(u) if u.why == Why::Ambiguous => Err(Unknown::unresolved(Why::Other).at(h, rest, false)),
                // 頭が型として名指されていれば頭の答えの読む所、そうでなければその名前を読む。
                Err(u) if self.names.typed.contains(h) => Err(u.derived()),
                Err(_) => Err(Unknown::unread(n)),
            },
            // 型として名指された名前は、手がかりがあるので定義を読む。手がかりのない名前は名前だけの要素である。
            None if self.names.typed.contains(n) => Err(Unknown::unread(n).own()),
            None => Ok(Answer::Bare(n.to_string())),
        }
    }

    /// `defines` から決める。曖昧なら決まらない。
    fn decide(&self, n: &str, e: &Element) -> Resolved {
        if e.undecided() {
            return Err(Unknown { defined: e.sources(), ..Unknown::unresolved(Why::Ambiguous).own() });
        }
        Ok(Answer::Element(Found {
            name: n.to_string(),
            kind: e.kinds.iter().next().cloned().unwrap_or_default(),
            defined: e.sources(),
            planned: e.planned(),
            ty: e.ty.clone(),
            owner: None,
            params: e.params.clone(),
        }))
    }

    /// 名前そのものの `resolves` で決める(規則 7)。
    fn resolved(&self, r: &Resolution) -> Resolved {
        match r {
            Resolution::Source(path) if self.observed(path, "structure") => Err(Unknown::unresolved(Why::Missing).own()),
            Resolution::Source(path) => Err(Unknown::new(
                Silence { reason: Reason::Unread, read: Some(path.clone()), element: None, scope: Some("structure".to_string()) },
                Why::Unread,
            )
            .own()),
            Resolution::External(pkg) => Ok(Answer::External(pkg.clone())),
            Resolution::Undecided => Err(Unknown::unresolved(Why::Undecided).own()),
        }
    }

    /// 段(型, 名前)。型 `t` の値の中の名前 `f` が、どの型で定義したどの要素かを決める(設計 §3.3)。
    pub fn stage(&self, t: &str, f: &str) -> Resolved {
        let key = format!("s {t} {f}");
        if !self.names.busy.borrow_mut().insert(key.clone()) {
            return Err(Unknown::unresolved(Why::Other));
        }
        let r = self.stage_of(t, f);
        self.names.busy.borrow_mut().remove(&key);
        r
    }

    fn stage_of(&self, t: &str, f: &str) -> Resolved {
        let ty = self.typed_element(t).map_err(Unknown::derived)?;
        // 候補が定義し直した読んでいない型は、変更前の沈黙で沈黙する。候補が直下に書いた `<T>.<f>` も同じである。
        if let Some(u) = self.names.redefined.get(&ty) {
            return Err(u.clone().at(&ty, f, false));
        }
        let name = format!("{ty}.{f}");
        match self.names.elements.get(&name).filter(|e| e.declared) {
            Some(e) => self.decide(&name, e).map_err(|u| u.at(&ty, f, false)),
            // どの型も `f` を定義しなければ、`<T>.<f>` そのものの `resolves` で決める。なければ `<T>.<f>` を読む。
            None => match self.names.resolves.get(&name) {
                Some(r) => self.resolved(r).map_err(|u| u.at(&ty, f, true)),
                None => Err(Unknown::unread(&name).at(&ty, f, true)),
            },
        }
    }

    /// 型に決まる要素。外部の要素は、型のフィールドが分からないので決まらない(読む所なし)。
    fn typed_element(&self, t: &str) -> Result<String, Unknown> {
        match self.element(t)? {
            Answer::Element(e) if e.kind == "type" => Ok(e.name),
            _ => Err(Unknown::unresolved(Why::Other)),
        }
    }

    /// 道(頭, [名前…])。場所(フィールドの要素の列)を作る(設計 §3.3)。最初に決まらなかった段で止まる。
    pub fn walk(&self, start: Start, names: &[String]) -> Walk {
        let mut w = Walk::default();
        let mut ty = match start {
            Start::Type(t) => t.to_string(),
            // 引数なら、要素(引数)の型から始める。
            Start::Param(p) => match self.element(p) {
                Ok(Answer::Element(e)) if e.kind == "param" => match e.ty {
                    Some(t) if is_question(&t) => {
                        w.stop = Some(self.question_type(e.owner.as_deref().unwrap_or(p)));
                        return w;
                    }
                    Some(t) => t,
                    None => {
                        w.stop = Some(Unknown::unresolved(Why::Other));
                        return w;
                    }
                },
                Ok(_) => {
                    w.stop = Some(Unknown::unresolved(Why::Other));
                    return w;
                }
                Err(u) => {
                    w.stop = Some(u);
                    return w;
                }
            },
        };
        for (i, n) in names.iter().enumerate() {
            if is_question(n) {
                w.stop = Some(Unknown::new(question(), Why::Question));
                return w;
            }
            w.stages.push(format!("{ty}.{n}"));
            w.types.push(ty.clone());
            match self.stage(&ty, n) {
                Ok(Answer::Element(e)) if e.kind == "field" => {
                    w.place.push(e.name.clone());
                    if i + 1 < names.len() {
                        match e.ty {
                            Some(t) if is_question(&t) => {
                                w.stop = Some(self.question_type(&e.name));
                                return w;
                            }
                            Some(t) => ty = t,
                            // 型のないフィールドの次は決まらない。
                            None => {
                                w.stop = Some(Unknown::unresolved(Why::Other));
                                return w;
                            }
                        }
                    }
                }
                Ok(_) => {
                    w.stop = Some(Unknown::unresolved(Why::Other));
                    return w;
                }
                Err(u) => {
                    w.stop = Some(u);
                    return w;
                }
            }
        }
        w
    }

    /// フィールドの型。型のないフィールドと、フィールドに決まらない名前は `unresolved`。
    /// `?` の型は決まらず、読む所はその型を書いた `defines` の場所(道と同じ)。
    pub fn field_type(&self, field: &str) -> Result<String, Unknown> {
        match self.element(field)? {
            Answer::Element(e) => match e.ty {
                Some(t) if is_question(&t) => Err(self.question_type(field)),
                Some(t) => Ok(t),
                None => Err(Unknown::unresolved(Why::Other)),
            },
            _ => Err(Unknown::unresolved(Why::Other)),
        }
    }

    /// 型が `?` のフィールドと引数は決まらない。読む所は、その型を書いた `defines` の場所。
    fn question_type(&self, owner: &str) -> Unknown {
        let s = match self.atoms.iter().find(|a| a.kind == "defines" && a.subject == owner) {
            Some(a) => locate(question(), a),
            None => question(),
        };
        Unknown::new(s, Why::Question)
    }

    /// 列の読み方。`reads`・`writes` の `via` と `object` の列を場所にする(設計 §3.3)。
    /// 各名前の最後の `.` の後がフィールドの名前、最初の名前の最後の `.` の前が頭である。二段目からの型の名前は使わない。
    pub fn column(&self, names: &[String]) -> Column {
        // 列の名前に `?` があれば、そこで決まらない。
        let known = names.iter().take_while(|n| !is_question(n)).count();
        let question = |mut c: Column| {
            if c.walk.stop.is_none() && known < names.len() {
                c.walk.stop = Some(Unknown::new(question(), Why::Question));
            }
            c
        };
        let Some(first) = names.first().filter(|_| known > 0) else {
            return question(Column::default());
        };
        let fields: Vec<String> = names[..known].iter().map(|n| n.rsplit_once('.').map_or(n.as_str(), |(_, f)| f).to_string()).collect();
        let head = first.rsplit_once('.').map(|(h, _)| h);
        let answer = match head {
            Some(h) => self.element(h),
            None => Ok(Answer::Bare(String::new())),
        };
        let mut c = Column { head: head.map(str::to_string), ..Column::default() };
        match answer {
            Ok(Answer::Element(t)) if t.kind == "type" => {
                c.ty = Some(t.name.clone());
                c.walk = self.walk(Start::Type(&t.name), &fields);
            }
            // 頭が名前だけの要素なら、列は字句どおりの名前の列である。各名前の答えは要素(名前)のものである。
            Ok(Answer::Bare(_)) => {
                for n in &names[..known] {
                    match self.element(n) {
                        Ok(Answer::Bare(_) | Answer::External(_)) => {}
                        Ok(Answer::Element(e)) if e.kind == "field" => {}
                        Ok(_) => {
                            c.walk.stop = Some(Unknown::unresolved(Why::Other));
                            break;
                        }
                        Err(u) => {
                            c.walk.stop = Some(u);
                            break;
                        }
                    }
                    c.walk.place.push(n.clone());
                }
            }
            // 外部の型のフィールドと、型でない要素のフィールドは分からない。読む所なし。
            Ok(_) => c.walk.stop = Some(Unknown::unresolved(Why::Other)),
            // 頭が分からなければ、最初の名前の答え(要素(名前))で決める。フィールドに決まれば、その型から残りを道で解く。
            Err(_) => match self.element(first) {
                Ok(Answer::Element(e)) if e.kind == "field" => {
                    let rest = &fields[1..];
                    let mut w = match (&e.ty, rest.is_empty()) {
                        (_, true) => Walk::default(),
                        (Some(t), false) if !is_question(t) => self.walk(Start::Type(t), rest),
                        (Some(_), false) => Walk { stop: Some(self.question_type(&e.name)), ..Walk::default() },
                        (None, false) => Walk { stop: Some(Unknown::unresolved(Why::Other)), ..Walk::default() },
                    };
                    w.place.insert(0, e.name);
                    c.walk = w;
                }
                Ok(_) => c.walk.stop = Some(Unknown::unresolved(Why::Other)),
                Err(u) => c.walk.stop = Some(u),
            },
        }
        question(c)
    }

    /// フィールド一覧(型)。型 `t` の値からたどれるフィールドの全体と、その型について分からないこと(設計 §3.3)。
    pub fn fields(&self, t: &str) -> Result<FieldList, Unknown> {
        let ty = match self.element(t)? {
            Answer::Element(e) if e.kind == "type" => e.name,
            // 外部の型は、フィールドを持たないとみなす(設計 §5.4)。
            Answer::External(_) => return Ok(FieldList { external: true, ..FieldList::default() }),
            _ => return Err(Unknown::unresolved(Why::Other)),
        };
        if let Some(u) = self.names.redefined.get(&ty) {
            return Err(u.clone());
        }
        let prefix = format!("{ty}.");
        // `<T>.<f>` の形の名前の `f`。
        let member = |n: &str| n.strip_prefix(&prefix).filter(|f| !f.is_empty() && !f.contains('.') && form(n) == Form::Dotted).map(str::to_string);
        let mut names: BTreeSet<String> = BTreeSet::new();
        // `defines` で種類がフィールドか決まらない名前。
        for (n, e) in self.names.elements.range(prefix.clone()..).take_while(|(n, _)| n.starts_with(&prefix)) {
            if e.declared && (e.kinds.contains("field") || e.undecided())
                && let Some(f) = member(n)
            {
                names.insert(f);
            }
        }
        // 構造が名指す `<T>.<f>` で `defines` のないもの。型として名指された名前と、`removes` した要素とその下の名前は見ない。
        for n in self.mentioned().range(prefix.clone()..).take_while(|n| n.starts_with(&prefix)) {
            if !self.declared(n)
                && !self.names.typed.contains(n)
                && !self.names.removes.iter().any(|x| below(x, n))
                && let Some(f) = member(n)
            {
                names.insert(f);
            }
        }
        let mut out = FieldList::default();
        for f in names {
            match self.stage(&ty, &f) {
                Ok(Answer::Element(e)) if e.kind == "field" => {
                    if !out.fields.contains(&e.name) {
                        out.fields.push(e.name);
                    }
                }
                Ok(_) => {}
                Err(u) => {
                    out.silence.get_or_insert(u.silence);
                }
            }
        }
        Ok(out)
    }

    /// 種類の問い合わせ。名前だけの要素は種類が決まらないので、その名前を読む所とする。
    pub fn kind(&self, n: &str) -> Result<String, Silence> {
        match self.element(n) {
            Ok(Answer::Element(e)) => Ok(e.kind),
            Ok(Answer::External(_)) => Err(Silence::new(Reason::Unresolved)),
            Ok(Answer::Bare(_)) => Err(Unknown::unread(n).silence),
            Err(u) => Err(u.silence),
        }
    }

    /// 構造が名指す名前(設計 §3.3)。`observed` と `imports` を除く Atom の `subject`・`object`・`via`、要素の型と引数の型、
    /// `value`・`when` の式の中の道の各段(決まらなかった段を含む)と呼び出す操作。
    pub fn mentioned(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        for a in self.atoms.iter().filter(|a| !matches!(a.kind.as_str(), "observed" | "imports")) {
            out.insert(a.subject.clone());
            out.extend(a.object.iter().cloned());
            out.extend(a.via.iter().flatten().cloned());
        }
        out.extend(self.names.typed.iter().cloned());
        for a in self.atoms.iter().filter(|a| a.is_structure()) {
            let op = owner(&a.subject);
            for text in [&a.value, &a.when].into_iter().flatten() {
                if let Ok(e) = expr::parse(text) {
                    self.expression_names(op, &e, &mut out);
                }
            }
        }
        out
    }

    /// 式の中で名指す名前。道の各段と、たどれた所までのフィールドと、呼び出す操作。
    fn expression_names(&self, op: &str, e: &Expr, out: &mut BTreeSet<String>) {
        match e {
            Expr::Path(p, fields) => {
                let w = self.walk(Start::Param(&param_name(op, p)), fields);
                out.extend(w.stages);
                out.extend(w.place);
            }
            Expr::Call(name, args) => {
                out.insert(name.clone());
                for a in args {
                    self.expression_names(op, a, out);
                }
            }
            Expr::Not(x) | Expr::Neg(x) => self.expression_names(op, x, out),
            Expr::TooLong(items) => {
                for x in items {
                    self.expression_names(op, x, out);
                }
            }
            Expr::Bin(_, a, b) => {
                self.expression_names(op, a, out);
                self.expression_names(op, b, out);
            }
            _ => {}
        }
    }
}

/// 道の頭。
#[derive(Clone, Copy, Debug)]
pub enum Start<'a> {
    /// 引数の名前(`<操作>.$<名前>`)。
    Param(&'a str),
    /// 型の名前。
    Type(&'a str),
}

/// 道の答え。決まった所までの場所、たどった段の名前(`<型>.<名前>`。決まらなかった段を含む)、最初に決まらなかった段の沈黙。
#[derive(Clone, Debug, Default)]
pub struct Walk {
    pub place: Vec<String>,
    pub stages: Vec<String>,
    /// 段ごとの型(`stages` と同じ並び)。
    pub types: Vec<String>,
    pub stop: Option<Unknown>,
}

/// 列の読み方の答え。
#[derive(Clone, Debug, Default)]
pub struct Column {
    /// 書いたとおりの頭(最初の名前の最後の `.` の前)。
    pub head: Option<String>,
    /// 頭が型に決まれば、その型の名前。
    pub ty: Option<String>,
    pub walk: Walk,
}

/// フィールド一覧の答え。
#[derive(Clone, Debug, Default)]
pub struct FieldList {
    pub fields: Vec<String>,
    /// 最初の沈黙。そのフィールドの先だけをたどらない印で、ほかのフィールドは返す。
    pub silence: Option<Silence>,
    /// 外部の型で、フィールドを持たないとみなした。
    pub external: bool,
}
