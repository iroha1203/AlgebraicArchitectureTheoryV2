//! 名前の解決と宣言の署名の検査(Law 仕様 §§1–3)。

use super::ast::*;
use super::model::*;
use super::parser::Parser;
use crate::definition::{Binding, CheckedDefinitions, PrimitiveSignature};
use crate::issue::{Code, Issue, Location};
use crate::prime::is_prime;
use crate::types::Type;
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

pub type CResult<T> = Result<T, Box<Issue>>;

pub use crate::names::BUILTIN_OPS;

/// `.` 列の先頭からの最長一致で解決した宣言。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    Decl(String),
    Ctor { data: String, index: usize },
}

pub use crate::definition::DataProperties as DataProps;

/// 型の解決で使う文脈。
pub struct TypeCtx<'a> {
    pub reading: usize,
    /// 依存型の添字に使える parameter と型。
    pub index: &'a [Param],
    pub allow_path: bool,
    /// 参照を含まない値型だけを許す(Term の中、change の値 parameter)。
    pub ref_free: bool,
    /// Set/Map/Term/Path の型適格性を確かめる。
    pub validate: bool,
}

pub struct Checker {
    pub parser: Parser,
    /// Law の reading と分離した検査済み共通定義。
    pub definitions: Rc<CheckedDefinitions>,
    pub imports: Vec<BTreeSet<String>>,
    /// 観測 Term は Law の reading ではなく定義元の scope で読む。
    pub term_namespace: Option<String>,
    pub ast: Rc<Vec<Reading>>,
    pub reading_index: HashMap<String, usize>,
    pub aliases: Vec<HashMap<String, String>>,
    pub shorts: Vec<HashSet<String>>,
    pub decl_index: HashMap<String, (usize, usize)>,
    pub ctor_index: HashMap<String, (String, usize)>,
    pub sigs: HashMap<String, Signature>,
    pub data_props: HashMap<String, DataProps>,
    /// 現在の宣言で記録している名前の参照。
    pub refs: Vec<(Span, String)>,
    pub expr_types: Vec<Option<Type>>,
    pub view_edges: Vec<(String, String, Span)>,
    pub reading_edges: Vec<(usize, usize, Span)>,
    pub current_reading: usize,
    pub decl_refs: HashMap<String, Vec<(Span, String)>>,
    pub decl_exprs: HashMap<String, Vec<ResolvedExpression>>,
}

pub fn full(reading: &str, rest: &[&str]) -> String {
    let mut s = reading.to_owned();
    for r in rest {
        s.push('.');
        s.push_str(r);
    }
    s
}

pub fn syntax<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::Syntax, span, message)))
}

pub fn reference<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::Reference, span, message)))
}

pub fn duplicate<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::DuplicateId, span, message)))
}

pub fn cycle<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::Cycle, span, message)))
}

pub fn type_error<T>(
    span: Span,
    expected: &Type,
    actual: &Type,
    message: impl Into<String>,
) -> CResult<T> {
    Err(Box::new(Issue::law_type(span, expected, actual, message)))
}

impl Checker {
    pub fn with_definitions(
        parser: Parser,
        readings: Vec<Reading>,
        definitions: &CheckedDefinitions,
    ) -> Checker {
        let sigs = definitions
            .declarations
            .iter()
            .map(|(name, d)| (name.clone(), Signature::from_primitive(&d.signature)))
            .collect();
        let mut ctor_index = HashMap::new();
        for (name, d) in &definitions.declarations {
            if let PrimitiveSignature::Data { constructors } = &d.signature {
                for (i, ctor) in constructors.iter().enumerate() {
                    ctor_index.insert(full(name, &[&ctor.name]), (name.clone(), i));
                }
            }
        }
        Checker {
            parser,
            definitions: Rc::new(definitions.clone()),
            imports: Vec::new(),
            term_namespace: None,
            ast: Rc::new(readings),
            reading_index: HashMap::new(),
            aliases: Vec::new(),
            shorts: Vec::new(),
            decl_index: HashMap::new(),
            ctor_index,
            sigs,
            data_props: definitions.data_properties().into_iter().collect(),
            refs: Vec::new(),
            expr_types: Vec::new(),
            view_edges: Vec::new(),
            reading_edges: Vec::new(),
            current_reading: 0,
            decl_refs: HashMap::new(),
            decl_exprs: HashMap::new(),
        }
    }

    pub fn reading_name(&self, r: usize) -> &str {
        &self.ast[r].name.name
    }

    pub fn decl_ast(&self, full: &str) -> Option<&Decl> {
        let (r, d) = *self.decl_index.get(full)?;
        Some(&self.ast[r].decls[d])
    }

    pub fn decl_kind(&self, full: &str) -> Option<&'static str> {
        self.definitions
            .declarations
            .get(full)
            .map(|d| d.signature.kind())
            .or_else(|| self.decl_ast(full).map(|d| d.kind.name()))
    }

    // ---- 名前の表 ----

    /// reading・alias・Law 宣言の名前を集め、同じ scope と共通定義との完全名衝突を拒否する。
    pub fn collect_names(&mut self) -> CResult<()> {
        let ast = self.ast.clone();
        for (ri, r) in ast.iter().enumerate() {
            if self.reading_index.insert(r.name.name.clone(), ri).is_some() {
                return duplicate(
                    r.name.span,
                    format!("reading `{}` が重複している", r.name.name),
                );
            }
        }
        for (ri, r) in ast.iter().enumerate() {
            let mut scope: HashSet<String> = HashSet::new();
            let mut shorts = HashSet::new();
            let mut aliases = HashMap::new();
            for u in &r.uses {
                if !scope.insert(u.alias.name.clone()) {
                    return duplicate(
                        u.alias.span,
                        format!("名前 `{}` が重複している", u.alias.name),
                    );
                }
                let Some(&target) = self.reading_index.get(&u.reading.name) else {
                    return reference(
                        u.reading.span,
                        format!("reading `{}` が同梱されていない", u.reading.name),
                    );
                };
                if target == ri {
                    return cycle(u.reading.span, "reading が自分自身を use している");
                }
                self.reading_edges.push((ri, target, u.reading.span));
                aliases.insert(u.alias.name.clone(), u.reading.name.clone());
            }
            let mut imports = BTreeSet::new();
            for v in &r.vocabularies {
                if !imports.insert(v.namespace.name.clone()) {
                    return duplicate(v.namespace.span, "同じ namespace の import が重複している");
                }
                self.definitions.check_binding(&Binding {
                    namespace: v.namespace.name.clone(),
                    version: v.version.clone(),
                    digest: v.digest.clone(),
                    location: Location::Law { span: v.span },
                })?;
            }
            self.imports.push(imports);
            for (di, d) in r.decls.iter().enumerate() {
                check_decl_name(&d.name)?;
                if !scope.insert(d.name.name.clone()) {
                    return duplicate(
                        d.name.span,
                        format!("名前 `{}` が重複している", d.name.name),
                    );
                }
                shorts.insert(d.name.name.clone());
                let name = full(&r.name.name, &[&d.name.name]);
                if self.primitive_identifier_exists(&name) {
                    return duplicate(
                        d.name.span,
                        format!("完全名 `{name}` は原始定義と衝突している"),
                    );
                }
                self.decl_index.insert(name.clone(), (ri, di));
                match &d.kind {
                    DeclKind::Entity { .. }
                    | DeclKind::Arrow { .. }
                    | DeclKind::Correspondence { .. }
                    | DeclKind::Data { .. } => {
                        unreachable!("Law /2 の parser は原始宣言を受理しない")
                    }
                    DeclKind::View { params, .. }
                    | DeclKind::Law { params, .. }
                    | DeclKind::Local { params, .. }
                    | DeclKind::Change { params, .. }
                    | DeclKind::Relation { params, .. } => {
                        let mut seen = HashSet::new();
                        for f in params {
                            check_binding_name(&f.name)?;
                            if !seen.insert(f.name.name.clone()) {
                                return duplicate(
                                    f.name.span,
                                    format!("parameter `{}` が重複している", f.name.name),
                                );
                            }
                        }
                    }
                }
            }
            self.aliases.push(aliases);
            self.shorts.push(shorts);
        }
        Ok(())
    }

    /// 原始宣言、constructor、field の完全名は Law 宣言と共有する一意な名前空間。
    fn primitive_identifier_exists(&self, name: &str) -> bool {
        let definitions = &self.definitions;
        if definitions.declarations.contains_key(name) {
            return true;
        }
        if let Some((decl, member)) = name.rsplit_once('.') {
            if let Some(d) = definitions.declarations.get(decl) {
                return d.signature.field(member).is_some()
                    || matches!(&d.signature, PrimitiveSignature::Data { constructors }
                        if constructors.iter().any(|c| c.name == member));
            }
        }
        false
    }

    /// `.` 列の先頭を別名、自分の宣言、直接 import、完全名の候補へ展開する。
    fn expand(&self, reading: usize, parts: &[Ident]) -> Vec<String> {
        let head = &parts[0].name;
        let rest: Vec<&str> = parts[1..].iter().map(|p| p.name.as_str()).collect();
        let mut out = Vec::new();
        if let Some(namespace) = &self.term_namespace {
            // 観測 Term の短名は定義元だけ。依存 namespace は完全名で読む。
            let mut all = vec![head.as_str()];
            all.extend(rest.iter().copied());
            out.push(full(namespace, &all));
            if self.term_namespaces().contains(head) {
                out.push(full(head, &rest));
            }
            return out;
        }
        if let Some(target) = self.aliases[reading].get(head) {
            out.push(full(target, &rest));
        }
        if self.shorts[reading].contains(head) {
            let mut all = vec![head.as_str()];
            all.extend(rest.iter().copied());
            out.push(full(self.reading_name(reading), &all));
        }
        if self.reading_index.contains_key(head) {
            out.push(full(head, &rest));
        }
        for namespace in &self.imports[reading] {
            let mut all = vec![head.as_str()];
            all.extend(rest.iter().copied());
            out.push(full(namespace, &all));
            if namespace == head {
                out.push(full(head, &rest));
            }
        }
        out
    }

    fn term_namespaces(&self) -> BTreeSet<String> {
        let Some(namespace) = &self.term_namespace else {
            return BTreeSet::new();
        };
        let mut visible = BTreeSet::from([namespace.clone()]);
        let mut pending = vec![namespace.clone()];
        let definitions = &self.definitions;
        while let Some(n) = pending.pop() {
            for dependency in &definitions.vocabularies[&n].dependencies {
                if visible.insert(dependency.namespace.clone()) {
                    pending.push(dependency.namespace.clone());
                }
            }
        }
        visible
    }

    /// 明示的な原始名には Law の直接 import、観測 Term の短名には定義元を要求する。
    pub fn primitive_visible(&self, reading: usize, data: &str, short: bool) -> bool {
        let definitions = &self.definitions;
        let Some(d) = definitions.declarations.get(data) else {
            return true;
        };
        if let Some(namespace) = &self.term_namespace {
            if short {
                &d.namespace == namespace
            } else {
                self.term_namespaces().contains(&d.namespace)
            }
        } else {
            self.imports[reading].contains(&d.namespace)
        }
    }

    /// 最長一致の全候補を集め、一意なときだけ解決する。
    pub fn resolve_prefix(
        &mut self,
        reading: usize,
        parts: &[Ident],
    ) -> CResult<Option<(Target, usize)>> {
        for k in (1..=parts.len()).rev() {
            let mut hits: BTreeMap<String, Target> = BTreeMap::new();
            for name in self.expand(reading, &parts[..k]) {
                let target = if self.decl_index.contains_key(&name)
                    || self.definitions.declarations.contains_key(&name)
                {
                    if !self.primitive_visible(reading, &name, false) {
                        continue;
                    }
                    Target::Decl(name.clone())
                } else if let Some((data, index)) = self.ctor_index.get(&name) {
                    if !self.primitive_visible(reading, data, false) {
                        continue;
                    }
                    Target::Ctor {
                        data: data.clone(),
                        index: *index,
                    }
                } else {
                    continue;
                };
                hits.insert(name, target);
            }
            if hits.len() > 1 {
                return reference(
                    (parts[0].span.0, parts[k - 1].span.1),
                    "短名の解決先が複数ある。完全名で明記する",
                );
            }
            if let Some((name, target)) = hits.into_iter().next() {
                self.note_reading_edge(reading, &name, (parts[0].span.0, parts[k - 1].span.1));
                return Ok(Some((target, k)));
            }
        }
        Ok(None)
    }

    /// 原始 namespace と同名の reading を依存先と誤認しない。
    pub fn note_reading_edge(&mut self, reading: usize, name: &str, span: Span) {
        let decl = self
            .ctor_index
            .get(name)
            .map(|(d, _)| d.as_str())
            .unwrap_or(name);
        if let Some(&(target, _)) = self.decl_index.get(decl) {
            if target != reading {
                self.reading_edges.push((reading, target, span));
            }
        }
    }

    pub fn record(&mut self, span: Span, name: String) {
        self.refs.push((span, name));
    }

    // ---- 所属 ----

    /// entity/arrow の検査済み所属先。原始宣言の Law AST は作らない。
    pub fn owner_root(&self, name: &str) -> Option<String> {
        match &self.definitions.declarations.get(name)?.signature {
            PrimitiveSignature::Entity { owner, .. } => owner.clone(),
            PrimitiveSignature::Arrow { owner, .. } => Some(owner.clone()),
            _ => None,
        }
    }

    pub fn resolve_prefix_silent(
        &mut self,
        reading: usize,
        parts: &[Ident],
    ) -> Option<(Target, usize)> {
        let edges = self.reading_edges.len();
        let hit = self.resolve_prefix(reading, parts).ok().flatten();
        self.reading_edges.truncate(edges);
        hit
    }

    // ---- 型 ----

    pub fn resolve_type(&mut self, ast: &TypeAst, ctx: &TypeCtx) -> CResult<Type> {
        let t = stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            self.resolve_type_inner(ast, ctx)
        })?;
        if ctx.validate && ctx.ref_free && self.has_reference(&t) {
            return syntax(ast.span(), "ここには参照・Map・Path を含まない値型が必要");
        }
        Ok(t)
    }

    fn resolve_type_inner(&mut self, ast: &TypeAst, ctx: &TypeCtx) -> CResult<Type> {
        Ok(match ast {
            TypeAst::Builtin(b, _) => match b {
                Builtin::Unit => Type::Unit,
                Builtin::Bool => Type::Bool,
                Builtin::Z => Type::Z,
                Builtin::Q => Type::Q,
                Builtin::Text => Type::Text,
            },
            TypeAst::Fp { modulus, span } => {
                let n: BigUint = modulus.parse().expect("字句で10進整数を確認済み");
                if !is_prime(&n) {
                    return syntax(*span, format!("Fp の法 {modulus} は素数でない"));
                }
                Type::Fp(modulus.clone())
            }
            TypeAst::Named { name, index, span } => {
                self.resolve_named_type(name, index.as_ref(), *span, ctx)?
            }
            TypeAst::Tuple(items, _) => Type::Tuple(
                items
                    .iter()
                    .map(|t| self.resolve_type(t, ctx))
                    .collect::<CResult<_>>()?,
            ),
            TypeAst::List(t, _) => Type::List(Box::new(self.resolve_type(t, ctx)?)),
            TypeAst::Option(t, _) => Type::Option(Box::new(self.resolve_type(t, ctx)?)),
            TypeAst::Set(t, span) => {
                let inner = self.resolve_type(t, ctx)?;
                if ctx.validate && self.has_term_or_path(&inner) {
                    return syntax(*span, "Set の要素型は Term・Path を含まない");
                }
                Type::Set(Box::new(inner))
            }
            TypeAst::Map(a, b, span) => {
                let a = self.resolve_type(a, ctx)?;
                let b = self.resolve_type(b, ctx)?;
                if ctx.validate && (a.ref_target().is_none() || b.ref_target().is_none()) {
                    return syntax(*span, "Map の定義域・値域は参照型");
                }
                Type::Map(Box::new(a), Box::new(b))
            }
            TypeAst::Term(args, ret, span) => {
                let inner = TypeCtx {
                    reading: ctx.reading,
                    index: &[],
                    allow_path: false,
                    ref_free: false,
                    validate: ctx.validate,
                };
                let args = args
                    .iter()
                    .map(|t| self.resolve_type(t, &inner))
                    .collect::<CResult<Vec<_>>>()?;
                let ret = self.resolve_type(ret, &inner)?;
                if ctx.validate
                    && (args.iter().any(|t| self.has_reference(t)) || self.has_reference(&ret))
                {
                    return syntax(*span, "Term の引数・戻り型は参照・Map・Path を含まない値型");
                }
                Type::Term(args, Box::new(ret))
            }
            TypeAst::Path(a, b, span) => {
                if ctx.validate && !ctx.allow_path {
                    return syntax(*span, "Path は原始 field・data・Term の型に置けない");
                }
                let a = self.resolve_entity_name(a, ctx.reading)?;
                let b = self.resolve_entity_name(b, ctx.reading)?;
                Type::Path(a, b)
            }
        })
    }

    fn resolve_entity_name(&mut self, q: &QName, reading: usize) -> CResult<String> {
        match self.resolve_prefix(reading, &q.parts)? {
            Some((Target::Decl(n), k)) if k == q.parts.len() => {
                if self.decl_kind(&n) != Some("entity") {
                    return syntax(q.span(), format!("Path の端点 `{}` は entity", q.text()));
                }
                self.record(q.span(), n.clone());
                Ok(n)
            }
            _ => reference(q.span(), format!("型名 `{}` を解決できない", q.text())),
        }
    }

    fn resolve_named_type(
        &mut self,
        q: &QName,
        index: Option<&Ident>,
        span: Span,
        ctx: &TypeCtx,
    ) -> CResult<Type> {
        let target = match self.resolve_prefix(ctx.reading, &q.parts)? {
            Some((Target::Decl(n), k)) if k == q.parts.len() => n,
            _ => return reference(q.span(), format!("型名 `{}` を解決できない", q.text())),
        };
        let kind = self.decl_kind(&target).expect("解決済みの宣言");
        self.record(q.span(), target.clone());
        match (kind, index) {
            ("data", None) => Ok(Type::Data(target)),
            ("data", Some(_)) => syntax(span, "data 型に所属の添字は付けられない"),
            ("entity" | "arrow" | "correspondence", None) => Ok(Type::Ref(target)),
            ("entity" | "arrow", Some(i)) => {
                let Some(root) = self.owner_root(&target) else {
                    return syntax(span, format!("`{}` は所属先を持たない", q.text()));
                };
                let Some(p) = ctx.index.iter().find(|p| p.name == i.name) else {
                    return reference(
                        i.span,
                        format!("添字 `{}` は左にある parameter を指す", i.name),
                    );
                };
                let expected = Type::Ref(root);
                if p.ty.erase() != expected {
                    return type_error(
                        i.span,
                        &expected,
                        &p.ty,
                        "添字の parameter は所属先の根 entity の参照",
                    );
                }
                Ok(Type::Owned(target, i.name.clone()))
            }
            ("correspondence", Some(_)) => {
                syntax(span, "correspondence に所属の添字は付けられない")
            }
            _ => reference(q.span(), format!("`{}` は型ではない", q.text())),
        }
    }

    pub fn has_term_or_path(&self, t: &Type) -> bool {
        t.any(&mut |t| match t {
            Type::Term(..) | Type::Path(..) => true,
            Type::Data(d) => self.data_props.get(d).is_some_and(|p| p.term_or_path),
            _ => false,
        })
    }

    /// 参照・Map・Path を、data の定義を通して含むか。
    pub fn has_reference(&self, t: &Type) -> bool {
        t.any(&mut |t| match t {
            Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Path(..) => true,
            Type::Data(d) => self.data_props.get(d).is_some_and(|p| p.reference),
            _ => false,
        })
    }
}

/// 宣言名の規則。組込み演算名は宣言名に使えない。
pub fn check_decl_name(id: &Ident) -> CResult<()> {
    if BUILTIN_OPS.contains(&id.name.as_str()) {
        return syntax(
            id.span,
            format!("組込み演算名 `{}` は宣言名に使えない", id.name),
        );
    }
    Ok(())
}

pub fn check_binding_name(id: &Ident) -> CResult<()> {
    if BUILTIN_OPS.contains(&id.name.as_str()) {
        return syntax(
            id.span,
            format!("組込み演算名 `{}` は束縛名に使えない", id.name),
        );
    }
    Ok(())
}

/// 有向グラフの閉路の一点。自己辺は含まない。
pub fn find_cycle(edges: &BTreeMap<String, BTreeSet<String>>) -> Option<String> {
    fn visit(
        n: &str,
        edges: &BTreeMap<String, BTreeSet<String>>,
        state: &mut HashMap<String, u8>,
    ) -> Option<String> {
        match state.get(n) {
            Some(1) => return Some(n.to_owned()),
            Some(2) => return None,
            _ => {}
        }
        state.insert(n.to_owned(), 1);
        if let Some(next) = edges.get(n) {
            for m in next {
                if let Some(c) = visit(m, edges, state) {
                    return Some(c);
                }
            }
        }
        state.insert(n.to_owned(), 2);
        None
    }
    let mut state = HashMap::new();
    for n in edges.keys() {
        if let Some(c) = visit(n, edges, &mut state) {
            return Some(c);
        }
    }
    None
}

impl std::fmt::Debug for Checker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Checker")
            .field("declarations", &self.decl_index.len())
            .finish()
    }
}
