//! 名前の解決(設計 §3.3)。名前が指す要素と、その要素が何かを決める問い合わせは、ここにだけ置く。
//! 式の道と書き込みの場所、名指し、選択、書いた場所より先と本体の比べ、局所は、この問い合わせの答えだけを使う。

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::{Reason, Silence, Structure, locate, question};

#[cfg(test)]
mod laws;
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
fn channel_of(item: &str) -> Option<&str> {
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
enum Resolution {
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
    Bare,
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
    /// 候補が `removes` した要素かその下の名前で、この構造にない。消える要素は変更前の構造で見る(設計 §3.6、§6)。
    Removed,
    /// それ以外(型でない要素を型として使う、外部の型のフィールドなど)。
    Other,
}

/// 段で決まらなかった所。型と名前。
#[derive(Clone, Debug, PartialEq, Eq)]
struct Stage {
    ty: String,
    name: String,
    /// 頭と受け継がれる型がすべて決まり、どの型も名前を定義しないために決まらなかった(段の「なければ」)。
    absent: bool,
    /// 段の「なければ」で、`<T>.<f>` そのものの `resolves` で決まらなかった。
    resolved: bool,
}

impl Stage {
    /// 段の名前 `<型>.<名前>`。
    fn full_name(&self) -> String {
        format!("{}.{}", self.ty, self.name)
    }
}

/// 答えがどこで決まらなかったか。一つの答えは、このどれか一つだけを持つ。
#[derive(Clone, Debug, PartialEq, Eq)]
enum Origin {
    /// 名前そのものの定義(`defines` か `resolves`)で決まらない。
    Name,
    /// 頭か持ち主の答えから決まらない(その名前の局所は頭か持ち主で見る)。
    Head,
    /// 段(型, 名前)で決まらない。
    Stage(Box<Stage>),
    /// 名前の途中の段で決まらない(その先の型が決まらないので、名前の局所も決まらない)。段で止まったなら、その段。
    Inner(Option<Box<Stage>>),
    /// それ以外(`?` の名前、型でない要素など)。
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unknown {
    pub silence: Silence,
    pub why: Why,
    origin: Origin,
    /// 曖昧な要素の定義した所。答え(`Err`)を小さく保つために箱に入れる。
    #[allow(clippy::box_collection)]
    defined: Box<BTreeSet<String>>,
}

impl Unknown {
    fn new(silence: Silence, why: Why) -> Unknown {
        Unknown { silence, why, origin: Origin::Other, defined: Box::default() }
    }

    fn unresolved(why: Why) -> Unknown {
        Unknown::new(Silence::new(Reason::Unresolved), why)
    }

    /// 定義を読んでいない要素。読む所は要素の名前。どのソースを読むかは SKILL が決める。
    fn unread(name: &str) -> Unknown {
        Unknown::new(Silence { reason: Reason::Unread, read: None, element: Some(name.to_string()), scope: None }, Why::Unread)
    }

    fn at(self, ty: &str, name: &str, absent: bool) -> Unknown {
        let stage = Stage { ty: ty.to_string(), name: name.to_string(), absent, resolved: false };
        Unknown { origin: Origin::Stage(Box::new(stage)), ..self }
    }

    /// 段の「なければ」で、`<T>.<f>` そのものの `resolves` で決まらなかった答えにする。
    fn at_resolves(self, ty: &str, name: &str) -> Unknown {
        let stage = Stage { ty: ty.to_string(), name: name.to_string(), absent: true, resolved: true };
        Unknown { origin: Origin::Stage(Box::new(stage)), ..self }
    }

    /// 名前そのものの定義で決まらない答えにする。
    fn own(self) -> Unknown {
        Unknown { origin: Origin::Name, ..self }
    }

    /// 頭か持ち主で決まらない答えにする。
    fn headed(self) -> Unknown {
        Unknown { origin: Origin::Head, ..self }
    }

    /// 名前の途中の段で決まらない答えにする。
    fn partial(self) -> Unknown {
        let stage = match self.origin {
            Origin::Stage(s) | Origin::Inner(Some(s)) => Some(s),
            Origin::Inner(None) | Origin::Name | Origin::Head | Origin::Other => None,
        };
        Unknown { origin: Origin::Inner(stage), ..self }
    }

    /// 段で決まらなかったなら、その段(名前の途中の段を含む)。
    fn stage(&self) -> Option<&Stage> {
        match &self.origin {
            Origin::Stage(s) | Origin::Inner(Some(s)) => Some(s),
            Origin::Inner(None) | Origin::Name | Origin::Head | Origin::Other => None,
        }
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
    /// `defines` を書いた場所(`at`)と、候補の中の `defines` の `file`。
    defined: BTreeSet<(String, Option<String>)>,
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
            .filter_map(|(at, file)| match file {
                Some(f) if at.starts_with("plan:") => Some(f.clone()),
                _ if at.starts_with("plan:") => None,
                _ => parse_location(at).map(|l| l.path),
            })
            .collect()
    }

    fn planned(&self) -> bool {
        self.defined.iter().any(|(at, _)| at.starts_with("plan:"))
    }
}

/// 名前の解決が使う構造の中身。外からは問い合わせを通してだけ読む。
#[derive(Clone, Debug, Default)]
pub(super) struct Names {
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
    /// Atom の `subject` に現れる名前(`observed` を除く)。
    subjects: BTreeSet<String>,
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
            if a.kind != "observed" {
                s.subjects.insert(a.subject.clone());
            }
            match a.kind.as_str() {
                "defines" => {
                    let e = s.elements.entry(a.subject.clone()).or_default();
                    e.kinds.insert(a.value.clone().unwrap_or_default());
                    e.defined.insert((a.at.clone().unwrap_or_default(), a.file.clone()));
                    e.declared = true;
                    if let Some(p) = &a.params {
                        e.params.extend(p.clone());
                        s.typed.extend(p.values().cloned());
                    }
                    if a.ty.is_some() {
                        e.ty = a.ty.clone();
                        s.typed.extend(a.ty.clone());
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
                Ok(Answer::Element(_) | Answer::Bare) => {
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

    /// 名前が `defines` を持つか。
    fn declared(&self, n: &str) -> bool {
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
    fn channel_operations(&self, n: &str) -> Option<&BTreeSet<String>> {
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
        // 候補が消した名前は、変更後の構造では消えたので決まらない。読んでも決まらないので、読む所を返さない。
        // 段の名前は、頭が型なら段で、そうでなければ `defines` の手前で見る(`dotted`)。
        if form(n) != Form::Dotted && self.removed(n) {
            return Err(Unknown::unresolved(Why::Removed).own());
        }
        match form(n) {
            // `?` で始まる名前は決まらない。読む所は、その名前を書いた Atom の場所(マニュアル第5章 問い8)で、Atom を持つ使う側が付ける。
            Form::Question => Err(Unknown::new(question(), Why::Question)),
            Form::Param { owner, name } => match self.element(owner).map_err(Unknown::headed)? {
                Answer::Element(op) if op.kind == "operation" => match op.params.get(name) {
                    Some(t) => Ok(Answer::Element(Found {
                        name: param_name(&op.name, name),
                        kind: "param".to_string(),
                        ty: Some(t.clone()),
                        owner: Some(op.name.clone()),
                        params: BTreeMap::new(),
                        ..op
                    })),
                    None => Err(Unknown::unresolved(Why::Other).headed()),
                },
                Answer::External(pkg) => Ok(Answer::External(pkg)),
                Answer::Element(_) | Answer::Bare => Err(Unknown::unresolved(Why::Other).headed()),
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
                        // 持ち主が曖昧なら、定義した所は持ち主の曖昧な定義した所である。
                        Ok(Answer::External(_) | Answer::Bare) | Err(_) => Found {
                            name: n.to_string(),
                            kind: "call".to_string(),
                            defined: match &owner {
                                Err(u) if u.why == Why::Ambiguous => (*u.defined).clone(),
                                Ok(_) | Err(_) => BTreeSet::new(),
                            },
                            planned: false,
                            ty: None,
                            owner: Some(caller.to_string()),
                            params: BTreeMap::new(),
                        },
                    }));
                }
                match owner.map_err(Unknown::headed)? {
                    Answer::Element(f) => Ok(Answer::Element(call(&f))),
                    Answer::Bare => Ok(Answer::Bare),
                    Answer::External(pkg) => Ok(Answer::External(pkg)),
                }
            }
            // チャネルと項目は、`sends` か `receives` に現れていればそれ。定義した所は、送る操作と受け取る操作の定義した所すべてである。
            Form::Channel if self.names.channels.contains_key(n) => {
                let mut defined = BTreeSet::new();
                for op in self.names.channels.get(n).into_iter().flatten() {
                    match self.element(op) {
                        Ok(Answer::Element(o)) => defined.extend(o.defined),
                        Err(u) if u.why == Why::Ambiguous => defined.extend(*u.defined),
                        Ok(Answer::External(_) | Answer::Bare) | Err(_) => {}
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
            Form::Channel => self.by_resolves_or_head(n, None, None),
            Form::Local => Ok(Answer::Bare),
            Form::Dotted => self.dotted(n),
        }
    }

    /// 名前の頭か持ち主。引数と呼び出しは持ち主の操作、段の名前は規則 5 の頭である。
    fn head_of(&self, n: &str) -> Option<String> {
        match form(n) {
            Form::Param { owner, .. } | Form::Call { caller: owner } => Some(owner.to_string()),
            Form::Dotted => self.head(n).map(|(h, _)| h.to_string()),
            _ => None,
        }
    }

    /// 候補が `removes` した要素かその下の名前で、この構造に要素も Atom もないか。
    fn removed(&self, n: &str) -> bool {
        !self.names.elements.contains_key(n) && !self.names.subjects.contains(n) && self.names.removes.iter().any(|x| below(x, n))
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
        // 頭は一度だけ解く。
        let answer = head.map(|(h, _)| self.element(h));
        // 5. 頭が型に決まれば、残りの最初の段を段(頭, 段)で解く。型に決まるときだけ、その型から続ける。
        if let (Some((_, rest)), Some(Ok(Answer::Element(t)))) = (head, &answer)
            && t.kind == "type"
        {
            let segments: Vec<&str> = rest.split('.').collect();
            let mut ty = t.name.clone();
            for (i, seg) in segments.iter().enumerate() {
                let last = i + 1 == segments.len();
                let a = self.stage_on(&ty, seg).map_err(|u| if last { u } else { u.partial() })?;
                if last {
                    return Ok(a);
                }
                match a {
                    Answer::Element(f) if f.kind == "type" => ty = f.name,
                    Answer::Element(_) | Answer::External(_) | Answer::Bare => return Err(Unknown::unresolved(Why::Other).partial()),
                }
            }
        }
        // 候補が消した名前は消えたので決まらない。頭が分からなければ、頭の答えで決める(規則 8。頭が消えていれば、その答え)。
        if self.removed(n) && !matches!(answer, Some(Err(_))) {
            return Err(Unknown::unresolved(Why::Removed).own());
        }
        // 6. `defines` を持つ名前。
        if let Some(e) = self.names.elements.get(n).filter(|e| e.declared) {
            return self.decide(n, e);
        }
        self.by_resolves_or_head(n, head, answer)
    }

    /// 規則 7 と 8。名前そのものの `resolves` で決め、なければ頭(とその答え `answer`)で決める。
    fn by_resolves_or_head(&self, n: &str, head: Option<(&str, &str)>, answer: Option<Resolved>) -> Resolved {
        if let Some(r) = self.names.resolves.get(n) {
            return self.resolved(n, r);
        }
        match head {
            Some((h, rest)) => match answer.unwrap_or_else(|| self.element(h)) {
                Ok(Answer::External(pkg)) => Ok(Answer::External(pkg)),
                Ok(Answer::Element(_) | Answer::Bare) => Err(Unknown::unresolved(Why::Other).headed()),
                // 頭が曖昧なら、頭の局所で見る(設計 §6)。
                Err(u) if u.why == Why::Ambiguous => Err(Unknown::unresolved(Why::Other).at(h, rest, false)),
                // 頭が型として名指されていれば頭の答えの読む所、そうでなければその名前を読む。
                Err(u) if self.names.typed.contains(h) => Err(u.headed()),
                // 頭の答えの読む所は、型として名指されていない頭には使わない(モジュールの名前とファイルの対応は仮定しない)。
                // 名前が候補の消した名前なら、読んでも決まらないので、消えた答えにする。
                Err(_head) if self.removed(n) => Err(Unknown::unresolved(Why::Removed).headed()),
                Err(_head) => Err(Unknown::unread(n).headed()),
            },
            // 型として名指された名前は、手がかりがあるので定義を読む。手がかりのない名前は名前だけの要素である。
            None if self.names.typed.contains(n) => Err(Unknown::unread(n).own()),
            None => Ok(Answer::Bare),
        }
    }

    /// `defines` から決める。曖昧なら決まらない。
    fn decide(&self, n: &str, e: &Element) -> Resolved {
        if e.undecided() {
            return Err(Unknown { defined: Box::new(e.sources()), ..Unknown::unresolved(Why::Ambiguous).own() });
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

    /// 名前 `n` そのものの `resolves` で決める(規則 7)。
    fn resolved(&self, n: &str, r: &Resolution) -> Resolved {
        match r {
            // 解析器が解決できなかった行き先(`?` で始まる)は、決まらない。読む所は、その `resolves` の Atom の場所。
            Resolution::Source(path) if is_question(path) => {
                let s = match self.atoms.iter().find(|a| a.kind == "resolves" && a.subject == n && a.object.as_deref().is_some_and(is_question)) {
                    Some(a) => locate(question(), a),
                    None => question(),
                };
                Err(Unknown::new(s, Why::Question).own())
            }
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
        // 型が決まらなければ、その下の名前も決まらない(局所も決まらない)。
        let ty = self.typed_element(t).map_err(Unknown::partial)?;
        self.stage_on(&ty, f)
    }

    /// 型に決まった `ty` の段。
    fn stage_on(&self, ty: &str, f: &str) -> Resolved {
        let key = format!("s {ty} {f}");
        if !self.names.busy.borrow_mut().insert(key.clone()) {
            return Err(Unknown::unresolved(Why::Other));
        }
        let r = self.stage_of(ty, f);
        self.names.busy.borrow_mut().remove(&key);
        r
    }

    fn stage_of(&self, ty: &str, f: &str) -> Resolved {
        // 候補が定義し直した読んでいない型は、変更前の沈黙で沈黙する。候補が直下に書いた `<T>.<f>` も同じである。
        let name = format!("{ty}.{f}");
        if let Some(u) = self.names.redefined.get(ty) {
            // `<T>.<f>` そのものの `resolves` があれば、その解決で決める(規則 7)。
            return match self.names.resolves.get(&name) {
                Some(r) => self.resolved(&name, r).map_err(|u| u.at_resolves(ty, f)),
                None => Err(u.clone().at(ty, f, false)),
            };
        }
        // 候補が消した `<T>.<f>` は、変更後の構造では消えたので決まらない(段の「なければ」。名指しは段の名前で見る)。
        if self.removed(&name) {
            return Err(Unknown::unresolved(Why::Removed).at(ty, f, true));
        }
        match self.names.elements.get(&name).filter(|e| e.declared) {
            Some(e) => self.decide(&name, e).map_err(|u| u.at(ty, f, false)),
            // どの型も `f` を定義しなければ、`<T>.<f>` そのものの `resolves` で決める。なければ `<T>.<f>` を読む。
            None => match self.names.resolves.get(&name) {
                Some(r) => self.resolved(&name, r).map_err(|u| u.at_resolves(ty, f)),
                None => Err(Unknown::unread(&name).at(ty, f, true)),
            },
        }
    }

    /// 型に決まる要素。外部の要素は、型のフィールドが分からないので決まらない(読む所なし)。
    fn typed_element(&self, t: &str) -> Result<String, Unknown> {
        match self.element(t)? {
            Answer::Element(e) if e.kind == "type" => Ok(e.name),
            Answer::Element(_) | Answer::External(_) | Answer::Bare => Err(Unknown::unresolved(Why::Other)),
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
                Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) => {
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
                Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) => {
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
            Answer::External(_) | Answer::Bare => Err(Unknown::unresolved(Why::Other)),
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
            None => Ok(Answer::Bare),
        };
        let mut c = Column::default();
        match answer {
            Ok(Answer::Element(t)) if t.kind == "type" => {
                c.head = Some(t.name.clone());
                c.walk = self.walk(Start::Type(&t.name), &fields);
            }
            // 頭が名前だけの要素なら、列は字句どおりの名前の列である。各名前の答えは要素(名前)のものである。
            Ok(Answer::Bare) => {
                c.bare = true;
                for n in &names[..known] {
                    match self.element(n) {
                        Ok(Answer::Bare | Answer::External(_)) => {}
                        Ok(Answer::Element(e)) if e.kind == "field" => {}
                        Ok(Answer::Element(_)) => {
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
            // 頭が型に決まらないとき、最初の段は書いたとおりの頭と最初の名前である。
            Ok(Answer::Element(_) | Answer::External(_)) => {
                c.walk = Walk { stages: vec![first.clone()], types: head.into_iter().map(str::to_string).collect(), ..Walk::default() };
                c.walk.stop = Some(Unknown::unresolved(Why::Other));
            }
            // 頭が分からなければ、最初の名前の答え(要素(名前))で決める。フィールドに決まれば、その型から残りを道で解く。
            // 頭は名指す要素なので、列の局所は頭の局所を含む(設計 §6)。
            Err(_head) => {
                c.head = head.map(str::to_string);
                let mut w = Walk { stages: vec![first.clone()], types: head.into_iter().map(str::to_string).collect(), ..Walk::default() };
                match self.element(first) {
                    Ok(Answer::Element(e)) if e.kind == "field" => {
                        let rest = &fields[1..];
                        let more = match (&e.ty, rest.is_empty()) {
                            (_, true) => Walk::default(),
                            (Some(t), false) if !is_question(t) => self.walk(Start::Type(t), rest),
                            (Some(_), false) => Walk { stop: Some(self.question_type(&e.name)), ..Walk::default() },
                            (None, false) => Walk { stop: Some(Unknown::unresolved(Why::Other)), ..Walk::default() },
                        };
                        w.place.push(e.name);
                        w.place.extend(more.place);
                        w.stages.extend(more.stages);
                        w.types.extend(more.types);
                        w.stop = more.stop;
                    }
                    Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) => w.stop = Some(Unknown::unresolved(Why::Other)),
                    Err(u) => w.stop = Some(u),
                }
                c.walk = w;
            }
        }
        question(c)
    }

    /// フィールド一覧(型)。型 `t` の値からたどれるフィールドの全体と、その型について分からないこと(設計 §3.3)。
    pub fn fields(&self, t: &str) -> Result<FieldList, Unknown> {
        let ty = match self.element(t)? {
            Answer::Element(e) if e.kind == "type" => e.name,
            // 外部の型は、フィールドを持たないとみなす(設計 §5.4)。
            Answer::External(_) => return Ok(FieldList { external: true, ..FieldList::default() }),
            Answer::Element(_) | Answer::Bare => return Err(Unknown::unresolved(Why::Other)),
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
                // 操作、外部の要素、型は一覧に入れない。
                Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) => {}
                Err(u) => {
                    out.silence.get_or_insert(u.silence);
                }
            }
        }
        Ok(out)
    }

    /// 型の下の名前で、段(型, 名前)で決まらない答えなら、その沈黙(設計 §5.4 の比べる場所)。
    pub fn stage_silence(&self, n: &str) -> Option<Silence> {
        match self.element(n) {
            Err(u) => match u.origin {
                Origin::Stage(_) | Origin::Inner(_) => Some(u.silence),
                Origin::Name | Origin::Head | Origin::Other => None,
            },
            Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) => None,
        }
    }

    /// 種類の問い合わせ。名前だけの要素は種類が決まらないので、その名前を読む所とする。
    /// `?` で始まる名前は、Atom を持たないこの問い合わせでは、その名前が現れる最初の Atom の場所を読む所とする。
    pub fn kind(&self, n: &str) -> Result<String, Silence> {
        match self.element(n) {
            Ok(Answer::Element(e)) => Ok(e.kind),
            Ok(Answer::External(_)) => Err(Silence::new(Reason::Unresolved)),
            Ok(Answer::Bare) => Err(Unknown::unread(n).silence),
            Err(u) => Err(match self.atoms.iter().find(|a| a.subject == n || a.object.as_deref() == Some(n) || a.via.iter().flatten().any(|v| v == n)) {
                Some(a) if form(n) == Form::Question => locate(u.silence, a),
                Some(_) | None => u.silence,
            }),
        }
    }

    /// 構造が名指す名前(設計 §3.3)。`observed` と `imports` を除く Atom の `subject`・`object`・`via`、要素の型と引数の型、
    /// `value`・`when` の式の中の道の各段(決まらなかった段を含む)と呼び出す操作。
    fn mentioned(&self) -> BTreeSet<String> {
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
    stages: Vec<String>,
    /// 段ごとの型(`stages` と同じ並び)。
    types: Vec<String>,
    pub stop: Option<Unknown>,
}

/// 列の読み方の答え。
#[derive(Clone, Debug, Default)]
pub struct Column {
    /// 名指す頭(設計 §6)。頭が型に決まるか、分からなければ、その名前。
    head: Option<String>,
    pub walk: Walk,
    /// 頭が名前だけの要素で、場所が字句どおりの名前の列か。
    bare: bool,
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

/// 名指しの答え(設計 §3.6)。消える要素を名指せば、その名前を `gone` に持つ。名指す要素をたどれなかった所は、その沈黙を `gaps` に持つ
/// (`?` の沈黙の Atom の場所は、Atom を持つ側が付ける)。
#[derive(Clone, Debug, Default)]
pub struct Naming {
    pub gone: BTreeSet<String>,
    pub gaps: Vec<Silence>,
}

impl Naming {
    fn extend(&mut self, other: Naming) {
        self.gone.extend(other.gone);
        self.gaps.extend(other.gaps);
    }
}

/// 要素の局所の元(設計 §6)。幾何は、この答えを読みの局所に写すだけである。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    /// 定義した所(ソースのパス)。
    Sources(BTreeSet<String>),
    /// 曖昧な要素の定義した所。すべて一つの局所にあればその局所、なければ決まらない。
    Ambiguous(BTreeSet<String>, Silence),
    /// この要素の局所で見る(持ち主の操作、頭、段の型)。
    Via(String),
    /// 送る操作と受け取る操作の局所すべて(チャネルとその項目)。
    Operations(BTreeSet<String>),
    /// どの局所にも属さない。
    Nowhere,
    /// 決まらない。
    Unknown(Silence),
    /// 候補を重ねた構造と変更前の構造のどちらでも決まらない。どちらかで局所が決まらなければ決まらず、決まれば前者の局所(なければ後者の)。
    Either(Box<Place>, Box<Place>),
}

impl Structure {
    /// Atom の名前 `n` の名指し。`self` は変更後の構造、`prior` は変更前の構造、`gone` は消える要素かその下の名前かの判定。
    /// 決まった要素はその名前を、名前だけの要素、外部の要素、名前そのものの定義(`defines` か `resolves`)で決まらないだけの名前は、字句どおりの名前を名指す。
    /// 頭か持ち主が消える要素かその下の名前なら、その名前を名指す。段の「なければ」で決まらない名前は、段の名前か、変更前の構造で同じ名前を解いた要素を名指す。
    /// それ以外(`?` の名前と、頭、持ち主、段で決まらない名前)は、名指す要素が決まらない。
    pub fn name_naming(&self, prior: &Structure, gone: &dyn Fn(&str) -> bool, n: &str) -> Naming {
        let mut out = Naming::default();
        let u = match self.element(n) {
            Ok(Answer::Element(e)) => {
                if gone(&e.name) {
                    out.gone.insert(e.name);
                }
                return out;
            }
            Ok(Answer::Bare | Answer::External(_)) => {
                if gone(n) {
                    out.gone.insert(n.to_string());
                }
                return out;
            }
            Err(u) => u,
        };
        if u.origin == Origin::Name {
            if gone(n) {
                out.gone.insert(n.to_string());
            }
            return out;
        }
        if self.head_of(n).is_some_and(|h| gone(&h)) {
            out.gone.insert(n.to_string());
            return out;
        }
        if let Some(s) = u.stage().filter(|s| s.absent) {
            let stage = s.full_name();
            if gone(&stage) {
                out.gone.insert(stage);
                return out;
            }
            match prior.element(n) {
                Ok(Answer::Element(e)) if gone(&e.name) => {
                    out.gone.insert(e.name);
                    return out;
                }
                Err(b) => {
                    out.gaps.push(b.silence);
                    return out;
                }
                Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) => {}
            }
        }
        out.gaps.push(u.silence);
        out
    }

    /// `reads`・`writes` の `via` と `object` の列 `names` の名指し。列の読み方で解いた場所のフィールドとその頭を名指す。
    /// 頭が名前だけの要素の列では、各名前を名前の名指しで見る。
    pub fn column_naming(&self, prior: &Structure, gone: &dyn Fn(&str) -> bool, names: &[String]) -> Naming {
        let c = self.column(names);
        if !c.bare {
            return self.walked(&c.walk, || prior.column(names).walk, gone);
        }
        let mut out = Naming::default();
        for n in &c.walk.place {
            out.extend(self.name_naming(prior, gone, n));
        }
        // 列は止まった名前で決まらない。止まった名前が消える要素を名指すときだけ、そちらを名指す。
        if let Some(u) = c.walk.stop {
            let at = names.get(c.walk.place.len()).filter(|n| !is_question(n));
            match at.map(|n| self.name_naming(prior, gone, n)) {
                Some(n) if !n.gone.is_empty() => out.gone.extend(n.gone),
                Some(_) | None => out.gaps.push(u.silence),
            }
        }
        out
    }

    /// 式の中の道 `$p.f…`(引数 `param` からフィールドの名前 `fields`)の名指し。道の場所のフィールドを名指す。
    pub fn path_naming(&self, prior: &Structure, gone: &dyn Fn(&str) -> bool, param: &str, fields: &[String]) -> Naming {
        let mut out = self.walked(&self.walk(Start::Param(param), fields), || prior.walk(Start::Param(param), fields), gone);
        if gone(param) {
            out.gone.insert(param.to_string());
        }
        out
    }

    /// 道か列の答え `walk` が名指す要素。決まったフィールドと、消える型の段の名前(`<型>.<名前>`)。
    /// 止まった段がどの型も定義しないために決まらなければ、その段の名前か、変更前の構造の同じ道 `prior` のその段の要素を名指す。
    fn walked(&self, walk: &Walk, prior: impl FnOnce() -> Walk, gone: &dyn Fn(&str) -> bool) -> Naming {
        let mut out = Naming::default();
        out.gone.extend(walk.place.iter().filter(|n| gone(n)).cloned());
        // 段の型が消える要素かその下の名前なら、その段の名前も消える要素の下の名前である。
        out.gone.extend(walk.stages.iter().zip(&walk.types).filter(|(_, t)| gone(t)).map(|(n, _)| n.clone()));
        let Some(u) = &walk.stop else { return out };
        let i = walk.place.len();
        if u.stage().is_some_and(|s| s.absent) {
            if let Some(n) = walk.stages.get(i).filter(|n| gone(n)) {
                out.gone.insert(n.clone());
                return out;
            }
            let p = prior();
            if p.stages.get(i).is_some() && p.stages.get(i) == walk.stages.get(i) {
                match (p.place.get(i), &p.stop) {
                    (Some(e), _) if gone(e) => {
                        out.gone.insert(e.clone());
                        return out;
                    }
                    (None, Some(b)) => {
                        out.gaps.push(b.silence.clone());
                        return out;
                    }
                    (Some(_), _) | (None, None) => {}
                }
            }
        }
        out.gaps.push(u.silence.clone());
        out
    }

    /// 要素の局所の元(設計 §6)。`self` は候補を重ねた構造、`prior` は変更前の構造(候補がなければ同じ構造)。
    /// 候補を重ねた列で決まればその定義した所、曖昧ならその定義した所。決まらなければ(名前だけの要素を含む)変更前の構造で解いた定義した所。
    /// 変更前でも決まらなければ、二つの答えで決める。
    pub fn place(&self, prior: &Structure, n: &str) -> Place {
        // チャネルとその項目は、候補を重ねた後の列の送り受けする操作の局所すべてに属する。
        if let Some(ops) = self.channel_operations(n) {
            return Place::Operations(ops.clone());
        }
        // 候補の中で定義した要素は、その `file` の局所(`file` がなければ変更前の構造で解いた定義した所)。
        if let Some(e) = self.names.elements.get(n).filter(|e| e.declared && e.planned()) {
            let sources = e.sources();
            if e.undecided() {
                return Place::Ambiguous(sources, Silence::new(Reason::Unresolved));
            }
            if !sources.is_empty() || std::ptr::eq(self, prior) {
                return Place::Sources(sources);
            }
            return self.original_place(prior, n);
        }
        // `removes` した要素とその下の名前は、変更前の構造で定義した所が決まれば、それで見る(変更後の構造の答えより先)。
        let removed = self.names.removes.iter().any(|x| below(x, n));
        let here = match self.element(n) {
            Ok(Answer::Element(f)) if !removed => return self.found_place(prior, &f),
            // 外部の要素は、どの局所にも属さない。
            Ok(Answer::External(_)) if !removed => return Place::Nowhere,
            Err(u) if u.why == Why::Ambiguous && !removed => return self.unknown_place(n, u),
            Ok(Answer::Element(f)) => self.found_place(prior, &f),
            Err(u) => self.unknown_place(n, u),
            Ok(Answer::External(_) | Answer::Bare) => Place::Nowhere,
        };
        // 変更前の構造で定義した所が決まらなければ(外部の要素と名前だけの要素は定義した所を持たない)、変更後の答えで決める。
        match prior.element(n) {
            Ok(Answer::Element(f)) => prior.found_place(prior, &f),
            Ok(Answer::External(_) | Answer::Bare) => here,
            Err(u) => Place::Either(Box::new(here), Box::new(prior.unknown_place(n, u))),
        }
    }

    /// 決まった要素の局所の元。引数と呼び出しは持ち主の操作で見る。チャネルは送り受けする操作で見る(上)。
    /// 候補の中で定義し `file` のない要素は、変更前の構造で解いた定義した所。
    fn found_place(&self, prior: &Structure, f: &Found) -> Place {
        if matches!(f.kind.as_str(), "param" | "call")
            && let Some(o) = &f.owner
        {
            return Place::Via(o.clone());
        }
        if f.kind == "channel" {
            return Place::Nowhere;
        }
        if f.planned && f.defined.is_empty() {
            // 変更前の構造そのものが候補の中で定義した要素(元の候補で `file` なしに定義した要素)は、元の定義した所が決まらない。
            if std::ptr::eq(self, prior) {
                return Place::Unknown(Silence::new(Reason::Unresolved));
            }
            return self.original_place(prior, &f.name);
        }
        Place::Sources(f.defined.clone())
    }

    /// 候補の中で `file` なしに定義した要素 `n` の局所の元。変更前の構造で解いた定義した所(書き直した要素の元の定義)。
    /// 新しく定義する要素の局所は `file` で決まる(マニュアル第3章)。元の定義した所が決まらなければ、局所は決まらない。
    fn original_place(&self, prior: &Structure, n: &str) -> Place {
        match prior.element(n) {
            Ok(Answer::Element(g)) => prior.found_place(prior, &g),
            // 変更前に決まらない要素は、その答えの読む所で沈黙する。
            Err(u) => Place::Unknown(u.silence),
            Ok(Answer::External(_) | Answer::Bare) => Place::Unknown(Silence::new(Reason::Unresolved)),
        }
    }

    /// 要素(名前)が決まらないときの局所の元(設計 §6)。
    fn unknown_place(&self, n: &str, u: Unknown) -> Place {
        // 名前の途中の段で決まらなければ、その先の型が決まらないので、局所も決まらない。
        if let Origin::Inner(_) = u.origin {
            return Place::Unknown(u.silence);
        }
        if u.why == Why::Ambiguous {
            return Place::Ambiguous(*u.defined, u.silence);
        }
        // 候補が消した名前は、変更後の構造では何も言わない。局所は変更前の構造で見る(`place`)。
        if u.why == Why::Removed {
            return Place::Nowhere;
        }
        match &u.origin {
            // `<T>.<f>` が段で決まらないか、頭 `T` が曖昧で決まらないなら、`T` の局所。
            // `<T>.<f>` そのものの `resolves` で決まらなかったなら、その答えで決める(下。マニュアル第4章)。
            Origin::Stage(stage) if !stage.resolved => return Place::Via(stage.ty.clone()),
            // 名前そのものの定義でなく、頭か持ち主で決まらないなら、頭で見る。引数と呼び出しは持ち主の操作で見る(マニュアル第4章)。
            Origin::Head => {
                if let Some(h) = self.head_of(n) {
                    return Place::Via(h);
                }
            }
            Origin::Stage(_) | Origin::Name | Origin::Other | Origin::Inner(_) => {}
        }
        // `unread` でソースを返すか、それ以外の `unresolved` なら、決まらない。名前そのものの読む所が名前だけの `unread` は、どの局所にも属さない。
        if u.silence.read.is_some() || u.silence.reason == Reason::Unresolved {
            return Place::Unknown(u.silence);
        }
        Place::Nowhere
    }

    /// `reads`・`writes` の `via` と `object` の列を列の読み方で解いた場所のフィールドとその頭の、局所の元。
    /// 列が止まれば、止まった名前とその局所の元。名前は、決まらないときに返す名前である。
    pub fn column_places(&self, prior: &Structure, names: &[String]) -> Vec<(String, Place)> {
        let c = self.column(names);
        let mut out: Vec<(String, Place)> = c.walk.place.iter().map(|n| (n.clone(), Place::Via(n.clone()))).collect();
        if let Some(u) = c.walk.stop {
            let k = c.walk.place.len();
            let at = names.get(k).or(names.last()).cloned().unwrap_or_default();
            // 最初の名前の答えが決まらずに止まれば、その名前の局所の元(変更前の構造で解いた定義した所を含む)。
            // フィールドでない要素に決まって止まったなら、列は決まらない(下)。
            let first = k == 0
                && match self.element(&at) {
                    Err(_) => true,
                    Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) => false,
                };
            let p = if first { self.place(prior, &at) } else { self.unknown_place(&at, u.clone()) };
            out.push((at.clone(), p));
            // 止まった名前の後ろの名前は、型が決まらないので局所も決まらない。決まらない名前は、止まった名前として返す。
            if k + 1 < names.len() {
                out.push((at, Place::Unknown(u.silence)));
            }
        }
        // 頭は列の名前から導いた名指す要素なので、列の名前の後に並べる(決まらない名前は、書いた名前を先に返す。設計 §6)。
        out.extend(c.head.map(|h| (h.clone(), Place::Via(h))));
        out
    }
}
