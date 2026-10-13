//! 既存 v0.6.0 原始型検査への内部 adapter。位置 handle は入力 byte span ではない。
use super::*;
use crate::law::{ast, check::Checker, model::Signature, parser::Parser};
use crate::types::Type;
use std::collections::BTreeSet;

pub(super) fn check(defs: &mut CheckedDefinitions) -> Result<(), Box<Issue>> {
    // 明示された依存の循環は、binding の digest 照合より先に検査する。
    let mut done = BTreeSet::new();
    for n in defs.vocabularies.keys() {
        dag(n, defs, &mut BTreeSet::new(), &mut done)?
    }
    for v in defs.vocabularies.values() {
        for b in &v.dependencies {
            defs.check_binding(b)?
        }
    }
    // 型/align の明示参照は、自分または直接 dependency の namespace に限る。
    for d in defs.declarations.values() {
        let v = &defs.vocabularies[&d.namespace];
        for (loc, target) in &d.references {
            let ns = target.split('.').next().expect("完全名を検査済み");
            if ns != d.namespace && !v.dependencies.iter().any(|b| b.namespace == ns) {
                return Err(Box::new(Issue {
                    code: Code::Reference,
                    message: format!("namespace `{ns}` の dependency がない"),
                    location: loc.clone(),
                    details: Details::Empty,
                }));
            }
        }
        // Ref と Data は wire タグ自身も検査する。Law の Named 型に落とす前に行う。
        if let Some((p, f)) = d.signature.record_fields() {
            for field in p.iter().chain(f) {
                category(&field.ty, &child_location(&field.location, "type"), defs)?;
            }
        }
        if let PrimitiveSignature::Data { constructors } = &d.signature {
            for c in constructors {
                for (i, t) in c.arguments.iter().enumerate() {
                    category(
                        t,
                        &child_location(&child_location(&c.location, "arguments"), &i.to_string()),
                        defs,
                    )?;
                }
            }
        }
    }
    let (mut checker, handles) = adapter(defs);
    let result = checker
        .collect_names()
        .and_then(|()| checker.check_primitives());
    if let Err(mut issue) = result {
        if let Location::Law { span } = &issue.location {
            issue.location = handles.get(span.0).cloned().unwrap_or_else(|| {
                defs.vocabularies
                    .values()
                    .next()
                    .expect("定義あり")
                    .location
                    .clone()
            })
        }
        return Err(issue);
    }
    for (name, d) in &mut defs.declarations {
        match (&mut d.signature, &checker.sigs[name]) {
            (
                PrimitiveSignature::Entity { owner, .. },
                Signature::Entity {
                    owner: resolved, ..
                },
            ) => *owner = resolved.clone(),
            (
                PrimitiveSignature::Arrow {
                    owner, endpoint, ..
                },
                Signature::Arrow {
                    owner: r,
                    endpoint: e,
                    ..
                },
            ) => {
                *owner = r.clone();
                *endpoint = e.clone()
            }
            (
                PrimitiveSignature::Correspondence {
                    from,
                    to,
                    maps,
                    implicit,
                    ..
                },
                Signature::Correspondence {
                    from: f,
                    to: t,
                    maps: m,
                    implicit: i,
                    ..
                },
            ) => {
                *from = f.clone();
                *to = t.clone();
                *maps = m.clone();
                *implicit = i.clone()
            }
            _ => {}
        }
    }
    Ok(())
}
fn child_location(parent: &Location, token: &str) -> Location {
    let Location::Definition { input, pointer, .. } = parent else {
        unreachable!()
    };
    location(input, &crate::json::pointer_push(pointer, token))
}
fn category(t: &Type, loc: &Location, defs: &CheckedDefinitions) -> Result<(), Box<Issue>> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || category_inner(t, loc, defs))
}
fn category_inner(t: &Type, loc: &Location, defs: &CheckedDefinitions) -> Result<(), Box<Issue>> {
    match t {
        Type::Data(n) | Type::Ref(n) | Type::Owned(n, _) => {
            if let Some(d) = defs.declarations.get(n) {
                if matches!(t, Type::Data(_))
                    != matches!(d.signature, PrimitiveSignature::Data { .. })
                {
                    return Err(Box::new(Issue {
                        code: Code::Syntax,
                        message: "Ref/Data の型タグと参照先の宣言種別が異なる".into(),
                        location: child_location(loc, "1"),
                        details: Details::Empty,
                    }));
                }
            }
        }
        Type::Tuple(ts) => {
            for (i, t) in ts.iter().enumerate() {
                category(t, &child_location(loc, &(i + 1).to_string()), defs)?
            }
        }
        Type::List(t) | Type::Set(t) | Type::Option(t) => {
            category(t, &child_location(loc, "1"), defs)?
        }
        Type::Map(a, b) => {
            category(a, &child_location(loc, "1"), defs)?;
            category(b, &child_location(loc, "2"), defs)?
        }
        Type::Term(args, ret) => {
            let al = child_location(loc, "1");
            for (i, t) in args.iter().enumerate() {
                category(t, &child_location(&al, &i.to_string()), defs)?
            }
            category(ret, &child_location(loc, "2"), defs)?
        }
        _ => {}
    }
    Ok(())
}
fn dag(
    n: &str,
    defs: &CheckedDefinitions,
    active: &mut BTreeSet<String>,
    done: &mut BTreeSet<String>,
) -> Result<(), Box<Issue>> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        dag_inner(n, defs, active, done)
    })
}
fn dag_inner(
    n: &str,
    defs: &CheckedDefinitions,
    active: &mut BTreeSet<String>,
    done: &mut BTreeSet<String>,
) -> Result<(), Box<Issue>> {
    if done.contains(n) {
        return Ok(());
    }
    active.insert(n.into());
    let Some(v) = defs.vocabularies.get(n) else {
        return Ok(());
    };
    for b in &v.dependencies {
        if active.contains(&b.namespace) {
            return Err(Box::new(Issue {
                code: Code::Cycle,
                message: "Atom 定義の依存が循環している".into(),
                location: b.location.clone(),
                details: Details::Empty,
            }));
        }
        if defs.vocabularies.contains_key(&b.namespace) {
            dag(&b.namespace, defs, active, done)?
        }
    }
    active.remove(n);
    done.insert(n.into());
    Ok(())
}
struct Handles {
    locations: Vec<Location>,
}
impl Handles {
    fn span(&mut self, l: &Location) -> ast::Span {
        let i = self.locations.len();
        self.locations.push(l.clone());
        (i, i + 1)
    }
    fn child(&mut self, l: &Location, p: &str) -> ast::Span {
        let Location::Definition { input, pointer, .. } = l else {
            unreachable!()
        };
        self.span(&location(input, &crate::json::pointer_push(pointer, p)))
    }
    fn ident(&mut self, name: &str, span: ast::Span) -> ast::Ident {
        ast::Ident {
            name: name.into(),
            span,
            tok: span.0,
        }
    }
    fn qname(&mut self, name: &str, span: ast::Span) -> ast::QName {
        ast::QName {
            parts: name.split('.').map(|s| self.ident(s, span)).collect(),
        }
    }
    fn ty(&mut self, t: &Type, l: &Location) -> ast::TypeAst {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || self.ty_inner(t, l))
    }
    fn ty_inner(&mut self, t: &Type, l: &Location) -> ast::TypeAst {
        let s = self.span(l);
        let child = |i: usize| {
            let Location::Definition { input, pointer, .. } = l else {
                unreachable!()
            };
            location(input, &crate::json::pointer_push(pointer, &i.to_string()))
        };
        match t {
            Type::Unit => ast::TypeAst::Builtin(ast::Builtin::Unit, s),
            Type::Bool => ast::TypeAst::Builtin(ast::Builtin::Bool, s),
            Type::Z => ast::TypeAst::Builtin(ast::Builtin::Z, s),
            Type::Q => ast::TypeAst::Builtin(ast::Builtin::Q, s),
            Type::Text => ast::TypeAst::Builtin(ast::Builtin::Text, s),
            Type::Fp(n) => ast::TypeAst::Fp {
                modulus: n.clone(),
                span: s,
            },
            Type::Ref(n) | Type::Data(n) | Type::Owned(n, _) => {
                let ns = self.child(l, "1");
                let name = self.qname(n, ns);
                let index = if let Type::Owned(_, p) = t {
                    let ps = self.child(l, "2");
                    Some(self.ident(p, ps))
                } else {
                    None
                };
                ast::TypeAst::Named {
                    name,
                    index,
                    span: s,
                }
            }
            Type::Tuple(items) => ast::TypeAst::Tuple(
                items
                    .iter()
                    .enumerate()
                    .map(|(i, t)| self.ty(t, &child(i + 1)))
                    .collect(),
                s,
            ),
            Type::List(t) => ast::TypeAst::List(Box::new(self.ty(t, &child(1))), s),
            Type::Set(t) => ast::TypeAst::Set(Box::new(self.ty(t, &child(1))), s),
            Type::Option(t) => ast::TypeAst::Option(Box::new(self.ty(t, &child(1))), s),
            Type::Map(a, b) => ast::TypeAst::Map(
                Box::new(self.ty(a, &child(1))),
                Box::new(self.ty(b, &child(2))),
                s,
            ),
            Type::Term(args, ret) => {
                let args_loc = child(1);
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, t)| {
                        let Location::Definition { input, pointer, .. } = &args_loc else {
                            unreachable!()
                        };
                        self.ty(
                            t,
                            &location(input, &crate::json::pointer_push(pointer, &i.to_string())),
                        )
                    })
                    .collect();
                ast::TypeAst::Term(args, Box::new(self.ty(ret, &child(2))), s)
            }
            Type::Path(..) => unreachable!("原始 JSON 型は Path を受理しない"),
        }
    }
    fn fields(&mut self, fields: &[Field]) -> Vec<ast::Field> {
        fields
            .iter()
            .map(|f| {
                let span = self.child(&f.location, "name");
                let name = self.ident(&f.name, span);
                let Location::Definition { input, pointer, .. } = &f.location else {
                    unreachable!()
                };
                let ty = self.ty(
                    &f.ty,
                    &location(input, &crate::json::pointer_push(pointer, "type")),
                );
                ast::Field { name, ty }
            })
            .collect()
    }
    fn decl(&mut self, d: &PrimitiveDeclaration) -> ast::Decl {
        let span = self.span(&d.location);
        let ns = self.child(&d.location, "name");
        let name = self.ident(d.name.split('.').nth(1).expect("完全名"), ns);
        let kind = match &d.signature {
            PrimitiveSignature::Entity {
                parameters, fields, ..
            } => ast::DeclKind::Entity {
                params: self.fields(parameters),
                members: self.fields(fields),
            },
            PrimitiveSignature::Arrow {
                parameters, fields, ..
            } => ast::DeclKind::Arrow {
                params: self.fields(parameters),
                members: self.fields(fields),
            },
            PrimitiveSignature::Correspondence {
                parameters,
                fields,
                alignments,
                ..
            } => {
                let alignments = alignments
                    .iter()
                    .map(|a| {
                        let ss = self.child(&a.location, "source");
                        let ts = self.child(&a.location, "target");
                        ast::Alignment {
                            source: self.qname(&a.source, ss),
                            target: self.qname(&a.target, ts),
                        }
                    })
                    .collect();
                ast::DeclKind::Correspondence {
                    params: self.fields(parameters),
                    members: self.fields(fields),
                    alignments,
                }
            }
            PrimitiveSignature::Data { constructors } => ast::DeclKind::Data {
                constructors: constructors
                    .iter()
                    .map(|c| {
                        let span = self.span(&c.location);
                        let cs = self.child(&c.location, "name");
                        let name = self.ident(&c.name, cs);
                        let Location::Definition { input, pointer, .. } = &c.location else {
                            unreachable!()
                        };
                        let args = c
                            .arguments
                            .iter()
                            .enumerate()
                            .map(|(i, t)| {
                                self.ty(t, &location(input, &format!("{pointer}/arguments/{i}")))
                            })
                            .collect();
                        ast::Constructor { name, args, span }
                    })
                    .collect(),
            },
        };
        ast::Decl { name, kind, span }
    }
}
/// 有効な原始定義を既存式検査器へ接続する内部文脈。表示 JSON から復元しない。
pub(crate) fn context(defs: &CheckedDefinitions) -> Checker {
    let (mut checker, _) = adapter(defs);
    checker.collect_names().expect("原始定義の名前は検査済み");
    checker.check_primitives().expect("原始型は検査済み");
    checker
}
fn adapter(defs: &CheckedDefinitions) -> (Checker, Vec<Location>) {
    let mut h = Handles {
        locations: Vec::new(),
    };
    let mut readings = Vec::new();
    for v in defs.vocabularies.values() {
        let span = h.span(&v.location);
        let name = h.ident(&v.namespace, span);
        let decls = defs
            .declarations
            .values()
            .filter(|d| d.namespace == v.namespace)
            .map(|d| h.decl(d))
            .collect();
        readings.push(ast::Reading {
            name,
            uses: Vec::new(),
            decls,
            span,
        })
    }
    (
        Checker::new(Parser::new(Vec::new(), 0), readings),
        h.locations,
    )
}
