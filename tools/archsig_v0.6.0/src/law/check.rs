//! 名前の解決と宣言の署名の検査(Law 仕様 §§1–3)。

use super::ast::*;
use super::model::*;
use super::parser::Parser;
use crate::definition::{Binding, CheckedDefinitions, PrimitiveSignature};
use crate::issue::{Code, Issue, Location};
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
use crate::prime::is_prime_controlled;
use crate::types::Type;
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

pub type CResult<T, E = Box<Issue>> = Result<T, E>;

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

pub struct Checker<E = Box<Issue>> {
    pub parser: Parser<E>,
    pub(super) control: Control,
    pub(super) semantic_point: Checkpoint,
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

pub fn syntax<T, E: InputError>(span: Span, message: impl Into<String>) -> CResult<T, E> {
    Err(Box::new(Issue::law(Code::Syntax, span, message)).into())
}

pub fn reference<T, E: InputError>(span: Span, message: impl Into<String>) -> CResult<T, E> {
    Err(Box::new(Issue::law(Code::Reference, span, message)).into())
}

pub fn duplicate<T, E: InputError>(span: Span, message: impl Into<String>) -> CResult<T, E> {
    Err(Box::new(Issue::law(Code::DuplicateId, span, message)).into())
}

pub fn cycle<T, E: InputError>(span: Span, message: impl Into<String>) -> CResult<T, E> {
    Err(Box::new(Issue::law(Code::Cycle, span, message)).into())
}

impl<E: InputError> Checker<E> {
    pub(super) fn erase_type(&self, ty: &Type) -> CResult<Type, E> {
        ty.erase_controlled::<E>(&mut self.control.clone(), self.semantic_point)
    }
    pub(super) fn type_error<T>(
        &self,
        span: Span,
        expected: &Type,
        actual: &Type,
        message: impl Into<String>,
    ) -> CResult<T, E> {
        let message = message.into();
        let details: CResult<crate::issue::Details, E> = (|| {
            Ok(crate::issue::Details::Type {
                expected: self.erase_type(expected)?,
                actual: self.erase_type(actual)?,
            })
        })();
        let issue = match details {
            Ok(details) => Issue {
                code: Code::Type,
                message,
                location: Location::Law { span },
                details,
            },
            // The mismatch is already known. Finish only its display payload;
            // no additional semantic check or mathematical derivation is performed.
            Err(stop) if stop.is_budget_stop() => Issue::law_type(span, expected, actual, message),
            Err(stop) => return Err(stop),
        };
        Err(Box::new(issue).into())
    }
    pub fn with_definitions(
        parser: Parser<E>,
        readings: Vec<Reading>,
        definitions: &CheckedDefinitions,
        control: &mut Control,
        semantic_point: Checkpoint,
    ) -> CResult<Self, E> {
        E::checkpoint(control, semantic_point)?;
        let mut sigs = HashMap::new();
        for (name, d) in &definitions.declarations {
            E::checkpoint(control, semantic_point)?;
            sigs.insert(
                name.clone(),
                Signature::from_primitive::<E>(&d.signature, control, semantic_point)?,
            );
        }
        let mut ctor_index = HashMap::new();
        for (name, d) in &definitions.declarations {
            E::checkpoint(control, semantic_point)?;
            if let PrimitiveSignature::Data { constructors } = &d.signature {
                for (i, ctor) in constructors.iter().enumerate() {
                    E::checkpoint(control, semantic_point)?;
                    ctor_index.insert(full(name, &[&ctor.name]), (name.clone(), i));
                }
            }
        }
        let data_props = definitions
            .data_properties_controlled::<E>(control)?
            .into_iter()
            .collect();
        E::checkpoint(control, semantic_point)?;
        Ok(Checker {
            parser,
            control: control.clone(),
            semantic_point,
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
            data_props,
            refs: Vec::new(),
            expr_types: Vec::new(),
            view_edges: Vec::new(),
            reading_edges: Vec::new(),
            current_reading: 0,
            decl_refs: HashMap::new(),
            decl_exprs: HashMap::new(),
        })
    }

    pub(super) fn cooperate(&self) -> CResult<(), E> {
        E::checkpoint(&mut self.control.clone(), self.semantic_point)
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
    pub(super) fn collect_names_controlled(&mut self, control: &mut Control) -> Result<(), E> {
        let ast = self.ast.clone();
        for (ri, r) in ast.iter().enumerate() {
            self.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            if self.reading_index.insert(r.name.name.clone(), ri).is_some() {
                return duplicate(
                    r.name.span,
                    format!("reading `{}` が重複している", r.name.name),
                );
            }
        }
        for (ri, r) in ast.iter().enumerate() {
            self.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            let mut scope: HashSet<String> = HashSet::new();
            let mut shorts = HashSet::new();
            let mut aliases = HashMap::new();
            for u in &r.uses {
                self.cooperate()?;
                E::checkpoint(control, Checkpoint::LawIteration)?;
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
                self.cooperate()?;
                E::checkpoint(control, Checkpoint::LawIteration)?;
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
                self.cooperate()?;
                E::checkpoint(control, Checkpoint::LawIteration)?;
                check_decl_name::<E>(&d.name)?;
                if !scope.insert(d.name.name.clone()) {
                    return duplicate(
                        d.name.span,
                        format!("名前 `{}` が重複している", d.name.name),
                    );
                }
                shorts.insert(d.name.name.clone());
                let name = full(&r.name.name, &[&d.name.name]);
                if self.primitive_identifier_exists(&name)? {
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
                            self.cooperate()?;
                            E::checkpoint(control, Checkpoint::LawIteration)?;
                            check_binding_name::<E>(&f.name)?;
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
    fn primitive_identifier_exists(&self, name: &str) -> CResult<bool, E> {
        self.cooperate()?;
        let definitions = &self.definitions;
        if definitions.declarations.contains_key(name) {
            return Ok(true);
        }
        if let Some((decl, member)) = name.rsplit_once('.') {
            if let Some(d) = definitions.declarations.get(decl) {
                if let Some((params, fields)) = d.signature.record_fields() {
                    for field in params.iter().chain(fields) {
                        self.cooperate()?;
                        if field.name == member {
                            return Ok(true);
                        }
                    }
                }
                if let PrimitiveSignature::Data { constructors } = &d.signature {
                    for ctor in constructors {
                        self.cooperate()?;
                        if ctor.name == member {
                            return Ok(true);
                        }
                    }
                }
            }
        }
        Ok(false)
    }

    /// `.` 列の先頭を別名、自分の宣言、直接 import、完全名の候補へ展開する。
    fn expand(&self, reading: usize, parts: &[Ident]) -> CResult<Vec<String>, E> {
        let head = &parts[0].name;
        let rest: Vec<&str> = parts[1..].iter().map(|p| p.name.as_str()).collect();
        let mut out = Vec::new();
        if let Some(namespace) = &self.term_namespace {
            // 観測 Term の短名は定義元だけ。依存 namespace は完全名で読む。
            let mut all = vec![head.as_str()];
            all.extend(rest.iter().copied());
            out.push(full(namespace, &all));
            if self.term_namespaces()?.contains(head) {
                out.push(full(head, &rest));
            }
            return Ok(out);
        }
        if let Some(target) = self.aliases[reading].get(head) {
            // alias が先頭の意味を固定する。展開先が未解決でも元の reading 名へ戻さない。
            return Ok(vec![full(target, &rest)]);
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
            self.cooperate()?;
            let mut all = vec![head.as_str()];
            all.extend(rest.iter().copied());
            out.push(full(namespace, &all));
            if namespace == head {
                out.push(full(head, &rest));
            }
        }
        Ok(out)
    }

    fn term_namespaces(&self) -> CResult<BTreeSet<String>, E> {
        let Some(namespace) = &self.term_namespace else {
            return Ok(BTreeSet::new());
        };
        let mut visible = BTreeSet::from([namespace.clone()]);
        let mut pending = vec![namespace.clone()];
        let definitions = &self.definitions;
        while let Some(n) = pending.pop() {
            self.cooperate()?;
            for dependency in &definitions.vocabularies[&n].dependencies {
                self.cooperate()?;
                if visible.insert(dependency.namespace.clone()) {
                    pending.push(dependency.namespace.clone());
                }
            }
        }
        Ok(visible)
    }

    /// 明示的な原始名には Law の直接 import、観測 Term の短名には定義元を要求する。
    pub fn primitive_visible(&self, reading: usize, data: &str, short: bool) -> CResult<bool, E> {
        let definitions = &self.definitions;
        let Some(d) = definitions.declarations.get(data) else {
            return Ok(true);
        };
        Ok(if let Some(namespace) = &self.term_namespace {
            if short {
                &d.namespace == namespace
            } else {
                self.term_namespaces()?.contains(&d.namespace)
            }
        } else {
            self.imports[reading].contains(&d.namespace)
        })
    }

    fn target(&self, name: &str) -> Option<Target> {
        if self.decl_index.contains_key(name) || self.definitions.declarations.contains_key(name) {
            Some(Target::Decl(name.to_owned()))
        } else {
            self.ctor_index.get(name).map(|(data, index)| Target::Ctor {
                data: data.clone(),
                index: *index,
            })
        }
    }

    fn target_visible(&self, reading: usize, target: &Target) -> CResult<bool, E> {
        let name = match target {
            Target::Decl(name) => name,
            Target::Ctor { data, .. } => data,
        };
        self.primitive_visible(reading, name, false)
    }

    /// alias の頭部を先に展開し、その scope 内で最長 prefix を選ぶ。
    /// alias がなければ実在する完全名を短名へ再展開せず、それ以外の相対候補の曖昧性を検査する。
    pub fn resolve_prefix(
        &mut self,
        reading: usize,
        parts: &[Ident],
    ) -> CResult<Option<(Target, usize)>, E> {
        let aliased =
            self.term_namespace.is_none() && self.aliases[reading].contains_key(&parts[0].name);
        for k in (1..=parts.len()).rev() {
            self.cooperate()?;
            let span = (parts[0].span.0, parts[k - 1].span.1);
            let written = parts[..k]
                .iter()
                .map(|p| p.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            if !aliased && let Some(target) = self.target(&written) {
                if !self.target_visible(reading, &target)? {
                    return reference(span, format!("完全名 `{written}` をこの scope で使えない"));
                }
                self.note_reading_edge(reading, &written, span);
                return Ok(Some((target, k)));
            }
            let mut hits: BTreeMap<String, Target> = BTreeMap::new();
            for name in self.expand(reading, &parts[..k])? {
                self.cooperate()?;
                if let Some(target) = self.target(&name) {
                    if self.target_visible(reading, &target)? {
                        hits.insert(name, target);
                    }
                }
            }
            if hits.len() > 1 {
                return reference(span, "短名の解決先が複数ある。完全名で明記する");
            }
            if let Some((name, target)) = hits.into_iter().next() {
                self.note_reading_edge(reading, &name, span);
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
    ) -> CResult<Option<(Target, usize)>, E> {
        let edges = self.reading_edges.len();
        let hit = self.resolve_prefix(reading, parts);
        self.reading_edges.truncate(edges);
        match hit {
            Ok(hit) => Ok(hit),
            Err(error) if error.is_stopped() => Err(error),
            Err(_) => Ok(None),
        }
    }

    // ---- 型 ----

    pub fn resolve_type(&mut self, ast: &TypeAst, ctx: &TypeCtx) -> CResult<Type, E> {
        self.cooperate()?;
        let result = (|| {
            let t = stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
                self.resolve_type_inner(ast, ctx)
            })?;
            if ctx.validate && ctx.ref_free {
                self.reject_reference(
                    &t,
                    ast.span(),
                    "ここには参照・Map・Path を含まない値型が必要",
                )?;
            }
            Ok(t)
        })();
        E::finish(result, &mut self.control.clone(), self.semantic_point)
    }

    fn resolve_type_inner(&mut self, ast: &TypeAst, ctx: &TypeCtx) -> CResult<Type, E> {
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
                if !is_prime_controlled::<E>(&n, &mut self.control.clone(), self.semantic_point)? {
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
                    .collect::<CResult<_, E>>()?,
            ),
            TypeAst::List(t, _) => Type::List(Box::new(self.resolve_type(t, ctx)?)),
            TypeAst::Option(t, _) => Type::Option(Box::new(self.resolve_type(t, ctx)?)),
            TypeAst::Set(t, span) => {
                let inner = self.resolve_type(t, ctx)?;
                if ctx.validate {
                    self.reject_term_or_path(&inner, *span)?;
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
                    .collect::<CResult<Vec<_>, E>>()?;
                let ret = self.resolve_type(ret, &inner)?;
                if ctx.validate {
                    self.reject_reference(
                        &ret,
                        *span,
                        "Term の引数・戻り型は参照・Map・Path を含まない値型",
                    )?;
                    for ty in &args {
                        self.cooperate()?;
                        self.reject_reference(
                            ty,
                            *span,
                            "Term の引数・戻り型は参照・Map・Path を含まない値型",
                        )?;
                    }
                } else {
                    // This is an intermediate type observation, rather than rejection.
                    self.has_reference(&ret)?;
                    for ty in &args {
                        self.cooperate()?;
                        self.has_reference(ty)?;
                    }
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

    fn resolve_entity_name(&mut self, q: &QName, reading: usize) -> CResult<String, E> {
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
    ) -> CResult<Type, E> {
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
                let mut index_parameter = None;
                for parameter in ctx.index {
                    self.cooperate()?;
                    if parameter.name == i.name {
                        index_parameter = Some(parameter);
                        break;
                    }
                }
                let Some(p) = index_parameter else {
                    return reference(
                        i.span,
                        format!("添字 `{}` は左にある parameter を指す", i.name),
                    );
                };
                let expected = Type::Ref(root);
                if self.erase_type(&p.ty)? != expected {
                    return self.type_error(
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

    fn type_scan(
        &self,
        root: &Type,
        mut predicate: impl FnMut(&Type) -> CResult<bool, E>,
    ) -> CResult<bool, E> {
        let mut stack = vec![root];
        while let Some(ty) = stack.pop() {
            self.cooperate()?;
            let found = predicate(ty);
            if !matches!(found, Ok(false)) {
                return E::finish(found, &mut self.control.clone(), self.semantic_point);
            }
            match ty {
                Type::Tuple(items) => stack.extend(items),
                Type::List(t) | Type::Set(t) | Type::Option(t) => stack.push(t),
                Type::Map(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                Type::Term(args, ret) => {
                    stack.extend(args);
                    stack.push(ret);
                }
                _ => {}
            }
            self.cooperate()?;
        }
        self.cooperate()?;
        Ok(false)
    }
    fn type_any(&self, root: &Type, mut predicate: impl FnMut(&Type) -> bool) -> CResult<bool, E> {
        self.type_scan(root, |ty| Ok(predicate(ty)))
    }
    pub(super) fn reject_type_component(
        &self,
        root: &Type,
        mut forbidden: impl FnMut(&Type) -> bool,
        span: Span,
        message: &str,
    ) -> CResult<(), E> {
        self.type_scan(root, |ty| {
            if forbidden(ty) {
                syntax(span, message)
            } else {
                Ok(false)
            }
        })?;
        Ok(())
    }
    pub(super) fn reject_reference(
        &self,
        root: &Type,
        span: Span,
        message: &str,
    ) -> CResult<(), E> {
        self.reject_type_component(
            root,
            |ty| match ty {
                Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Path(..) => true,
                Type::Data(name) => self.data_props.get(name).is_some_and(|p| p.reference),
                _ => false,
            },
            span,
            message,
        )
    }
    pub(super) fn require_numeric(
        &self,
        root: &Type,
        span: Span,
        expected: &Type,
        actual: &Type,
        message: &str,
    ) -> CResult<(), E> {
        self.type_scan(root, |ty| {
            if !matches!(ty, Type::Z | Type::Q | Type::Fp(_) | Type::Tuple(_)) {
                self.type_error(span, expected, actual, message)
            } else {
                Ok(false)
            }
        })?;
        Ok(())
    }
    pub(super) fn reject_term_or_path(&self, root: &Type, span: Span) -> CResult<(), E> {
        self.reject_type_component(
            root,
            |ty| match ty {
                Type::Term(..) | Type::Path(..) => true,
                Type::Data(name) => self.data_props.get(name).is_some_and(|p| p.term_or_path),
                _ => false,
            },
            span,
            "Set の要素型は Term・Path を含まない",
        )
    }
    pub(super) fn signature_field(
        &self,
        signature: &Signature,
        name: &str,
    ) -> CResult<Option<Param>, E> {
        if let Some((parameters, members)) = signature.record_fields() {
            for field in parameters.iter().chain(members) {
                self.cooperate()?;
                if field.name == name {
                    return Ok(Some(field.clone()));
                }
            }
        }
        Ok(None)
    }
    pub fn has_reference(&self, t: &Type) -> CResult<bool, E> {
        self.type_any(t, |t| match t {
            Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Path(..) => true,
            Type::Data(d) => self.data_props.get(d).is_some_and(|p| p.reference),
            _ => false,
        })
    }
}

/// 宣言名の規則。組込み演算名は宣言名に使えない。
pub fn check_decl_name<E: InputError>(id: &Ident) -> CResult<(), E> {
    if BUILTIN_OPS.contains(&id.name.as_str()) {
        return syntax(
            id.span,
            format!("組込み演算名 `{}` は宣言名に使えない", id.name),
        );
    }
    Ok(())
}

pub fn check_binding_name<E: InputError>(id: &Ident) -> CResult<(), E> {
    if BUILTIN_OPS.contains(&id.name.as_str()) {
        return syntax(
            id.span,
            format!("組込み演算名 `{}` は束縛名に使えない", id.name),
        );
    }
    Ok(())
}

/// 有向グラフの閉路の一点。自己辺は含まない。
pub fn find_cycle<E: InputError>(
    edges: &BTreeMap<String, BTreeSet<String>>,
    control: &mut Control,
) -> CResult<Option<String>, E> {
    fn visit<E: InputError>(
        n: &str,
        edges: &BTreeMap<String, BTreeSet<String>>,
        state: &mut HashMap<String, u8>,
        control: &mut Control,
    ) -> CResult<Option<String>, E> {
        E::checkpoint(control, Checkpoint::LawCycle)?;
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            match state.get(n) {
                Some(1) => return Ok(Some(n.to_owned())),
                Some(2) => return Ok(None),
                _ => {}
            }
            state.insert(n.to_owned(), 1);
            if let Some(next) = edges.get(n) {
                for m in next {
                    E::checkpoint(control, Checkpoint::LawCycle)?;
                    if let Some(c) = visit::<E>(m, edges, state, control)? {
                        return Ok(Some(c));
                    }
                }
            }
            state.insert(n.to_owned(), 2);
            E::checkpoint(control, Checkpoint::LawCycle)?;
            Ok(None)
        })
    }
    let mut state = HashMap::new();
    for n in edges.keys() {
        E::checkpoint(control, Checkpoint::LawCycle)?;
        if let Some(c) = visit::<E>(n, edges, &mut state, control)? {
            return Ok(Some(c));
        }
    }
    E::checkpoint(control, Checkpoint::LawCycle)?;
    Ok(None)
}

impl<E> std::fmt::Debug for Checker<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Checker")
            .field("declarations", &self.decl_index.len())
            .finish()
    }
}
