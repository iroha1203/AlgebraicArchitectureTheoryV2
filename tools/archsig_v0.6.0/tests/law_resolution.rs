//! AC3: 解決の追跡。短形と明示形、既定規則、暗黙 align、constructor metadata、Location。

mod common;
use archsig::law::CheckedLaw;
use archsig::law::model::{DeclarationInfo, ExpressionKind, SuppliedRule};
use archsig::types::Type;
use common::*;

const SHORT: &str = "  law required conserved(e: Reserve):\n    e.to.free + e.to.held = e.from.free + e.from.held;\n";
const EXPLICIT: &str = "  law required conserved(e: Reservations.Reserve) when true:\n    e.to.free + e.to.held = e.from.free + e.from.held;\n";

fn info<'a>(c: &'a CheckedLaw, name: &str) -> &'a DeclarationInfo {
    c.infos
        .iter()
        .find(|i| i.name == name)
        .unwrap_or_else(|| panic!("{name}"))
}

#[test]
fn short_and_explicit_forms_resolve_to_the_same_meaning() {
    assert!(RESERVATIONS.contains(SHORT));
    let explicit_src = RESERVATIONS.replace(SHORT, EXPLICIT);
    let short = ok(RESERVATIONS);
    let explicit = ok(&explicit_src);
    assert_eq!(short.vocabularies, explicit.vocabularies);
    assert_ne!(short.model_digest, explicit.model_digest);
    assert_ne!(short.bytes_digest, explicit.bytes_digest);

    let s = info(&short, "Reservations.conserved");
    let e = info(&explicit, "Reservations.conserved");
    assert_eq!(
        s.parameters,
        vec![("e".to_owned(), Type::Ref("Reservations.Reserve".into()))]
    );
    assert_eq!(s.parameters, e.parameters);
    assert_eq!(s.role, e.role);
    let names = |i: &DeclarationInfo| {
        i.references
            .iter()
            .map(|(_, n)| n.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(names(s), names(e));
    assert_eq!(s.dependencies, e.dependencies);

    // 型の短名と完全名は、それぞれの元の出現を指す。
    assert_eq!(span_text(RESERVATIONS, s.references[0].0), "Reserve");
    assert_eq!(
        span_text(&explicit_src, e.references[0].0),
        "Reservations.Reserve"
    );

    // 短形は guard_true を補い、明示形は型付きの guard 式を持つ。
    assert_eq!(s.supplied, vec![SuppliedRule::GuardTrue { span: s.span }]);
    assert!(e.supplied.is_empty());
    let kinds = |i: &DeclarationInfo| {
        i.expressions
            .iter()
            .map(|x| (x.kind, x.ty.clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(kinds(s), vec![(ExpressionKind::Body, Type::Bool)]);
    assert_eq!(
        kinds(e),
        vec![
            (ExpressionKind::Guard, Type::Bool),
            (ExpressionKind::Body, Type::Bool)
        ]
    );
    assert_eq!(span_text(&explicit_src, e.expressions[0].span), "true");
    assert_eq!(
        span_text(RESERVATIONS, s.expressions[0].span),
        span_text(&explicit_src, e.expressions[1].span)
    );
    assert_eq!(span_text(RESERVATIONS, s.span), SHORT.trim());
    assert_eq!(span_text(&explicit_src, e.span), EXPLICIT.trim());

    // 他の宣言の解決結果は変わらない。
    let shape = |c: &CheckedLaw| {
        c.infos
            .iter()
            .map(|i| (i.name.clone(), i.kind, i.parameters.clone(), names(i)))
            .collect::<Vec<_>>()
    };
    assert_eq!(shape(&short), shape(&explicit));
}

#[test]
fn reading_records_declared_or_support_locals() {
    let c = ok(RESERVATIONS);
    let r = info(&c, "Reservations");
    assert_eq!(
        r.supplied,
        vec![SuppliedRule::LocalDeclared { span: r.span }]
    );
    assert_eq!(
        span_text(RESERVATIONS, r.span),
        RESERVATIONS[RESERVATIONS.find("reading").unwrap()..].trim_end()
    );
    let without = reading("entity S; entity A(owner: S) { x: Z; } law required l(a: A): a.x = 0;");
    let c = ok(&without);
    let r = info(&c, "R");
    assert_eq!(
        r.supplied,
        vec![SuppliedRule::LocalSupport { span: r.span }]
    );
}

#[test]
fn implicit_alignment_is_recorded_apart_from_explicit_alignment() {
    let c = ok(RESERVATIONS);
    let m = info(&c, "Reservations.Migration");
    let SuppliedRule::SameNameAlignment { pairs, span } = &m.supplied[0] else {
        panic!()
    };
    assert_eq!(*span, m.span);
    let expected: Vec<(String, String)> = [
        "Reserve.from",
        "Reserve.owner",
        "Reserve.to",
        "State.free",
        "State.held",
        "State.owner",
    ]
    .iter()
    .map(|f| (format!("Reservations.{f}"), format!("Reservations.{f}")))
    .collect();
    assert_eq!(*pairs, expected);
    // 暗黙の同名対応は語彙 manifest の alignments に入らない。
    assert!(
        c.vocabularies[0]
            .manifest
            .canonical()
            .contains(r#""alignments":[]"#)
    );

    // 同じ型の間で明記した align は manifest に入り、その field は同名対応から外れる。
    let swapped = ok(&reading(
        "entity S; entity A(owner: S) { x: Z; y: Z; }
         correspondence Swap(from: S, to: S) {
           items: Map<A[from], A[to]>;
           align A.x = A.y;
           align R.A.y = R.A.x;
         }",
    ));
    let sw = info(&swapped, "R.Swap");
    let SuppliedRule::SameNameAlignment { pairs, .. } = &sw.supplied[0] else {
        panic!()
    };
    assert_eq!(
        *pairs,
        vec![("R.A.owner".to_owned(), "R.A.owner".to_owned())]
    );
    let manifest = swapped.vocabularies[0].manifest.canonical();
    assert!(manifest.contains(
        r#""alignments":[{"source":"R.A.x","target":"R.A.y"},{"source":"R.A.y","target":"R.A.x"}]"#
    ));
}

#[test]
fn constructors_have_their_own_metadata() {
    let c = ok(ENGINE);
    let lit = info(&c, "Engine.Expr.Lit");
    assert_eq!(lit.kind, "data");
    assert_eq!(lit.parameters, vec![("arg0".to_owned(), Type::Z)]);
    assert_eq!(span_text(ENGINE, lit.span), "Lit(Z)");
    let add = info(&c, "Engine.Expr.Add");
    let expr = Type::Data("Engine.Expr".into());
    assert_eq!(
        add.parameters,
        vec![("arg0".to_owned(), expr.clone()), ("arg1".to_owned(), expr)]
    );
    assert_eq!(add.dependencies, ["Engine.Expr"]);
    assert!(info(&c, "Engine.Expr.Var").parameters.is_empty());
    let data = info(&c, "Engine.Expr");
    assert_eq!(
        span_text(ENGINE, data.span),
        "data Expr = Lit(Z) | Var | Add(Expr, Expr);"
    );
    // pattern と式の constructor は、元の名前の出現を指す。
    let translate = info(&c, "Engine.translate");
    let plus = translate
        .references
        .iter()
        .find(|(_, n)| n == "Engine.IR.Plus")
        .unwrap();
    assert_eq!(span_text(ENGINE, plus.0), "Plus");
    let lit_pattern = translate
        .references
        .iter()
        .find(|(_, n)| n == "Engine.Expr.Lit")
        .unwrap();
    assert_eq!(span_text(ENGINE, lit_pattern.0), "Lit");
}

#[test]
fn references_through_parentheses_point_at_the_name() {
    let src = reading(
        "data D = C(Z);
         view f(x: Z): Z = x;
         view g(): Z = ((f))( 1 ) + ( /* */ f)(2);
         view h(): D = (D.C)(1);
         view k(): D = ( R.D.C )(2);",
    );
    let src = src.replace("/* */", "");
    let c = ok(&src);
    let g = info(&c, "R.g");
    assert_eq!(g.references.len(), 2);
    for (span, name) in &g.references {
        assert_eq!(name, "R.f");
        assert_eq!(span_text(&src, *span), "f");
    }
    let h = info(&c, "R.h");
    assert_eq!(
        h.references
            .iter()
            .map(|(s, n)| (span_text(&src, *s), n.as_str()))
            .collect::<Vec<_>>(),
        [("D", "R.D"), ("D.C", "R.D.C")]
    );
    let k = info(&c, "R.k");
    assert_eq!(
        k.references
            .iter()
            .map(|(s, _)| span_text(&src, *s))
            .collect::<Vec<_>>(),
        ["D", "R.D.C"]
    );
}

/// 全 Location が入力の実在箇所を指し、名前の出現は解決先の最後の名前で終わる。
fn assert_locations(src: &str, c: &CheckedLaw) {
    let valid = |span: (usize, usize)| {
        assert!(span.0 <= span.1 && span.1 <= src.len(), "{span:?}");
        assert!(
            src.is_char_boundary(span.0) && src.is_char_boundary(span.1),
            "{span:?}"
        );
    };
    for i in &c.infos {
        valid(i.span);
        assert!(!span_text(src, i.span).trim().is_empty());
        for (span, name) in &i.references {
            valid(*span);
            let text: String = span_text(src, *span)
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            let last = text.rsplit('.').next().unwrap();
            assert_eq!(
                Some(last),
                name.rsplit('.').next(),
                "{} が `{text}` を指す",
                name
            );
        }
        for e in &i.expressions {
            valid(e.span);
            assert!(!span_text(src, e.span).trim().is_empty());
        }
        for s in &i.supplied {
            let span = match s {
                SuppliedRule::GuardTrue { span }
                | SuppliedRule::LocalDeclared { span }
                | SuppliedRule::LocalSupport { span }
                | SuppliedRule::SameNameAlignment { span, .. } => *span,
            };
            assert_eq!(span, i.span, "既定規則の位置は元の宣言全体");
        }
    }
}

#[test]
fn every_location_points_into_the_bundled_input() {
    for src in [RESERVATIONS, ENGINE, &RESERVATIONS.replace(SHORT, EXPLICIT)] {
        let c = ok(src);
        assert_locations(src, &c);
    }
    let unicode = reading(
        "view t(): Text = \"日本語の文字列\"; view u(): Z = count(list<Text>[\"é\", t()]);",
    );
    assert_locations(&unicode, &ok(&unicode));
}

#[test]
fn declarations_are_listed_by_full_name_with_expression_types() {
    let c = ok(RESERVATIONS);
    let names: Vec<_> = c.infos.iter().map(|i| i.name.as_str()).collect();
    let mut sorted = names.clone();
    sorted.sort();
    assert_eq!(names, sorted);
    assert_eq!(names.len(), 12);
    let transfer = info(&c, "Reservations.Transfer");
    let pair = Type::Tuple(vec![Type::Z, Type::Z]);
    assert_eq!(
        transfer
            .expressions
            .iter()
            .map(|e| e.ty.clone())
            .collect::<Vec<_>>(),
        [pair.clone(), pair]
    );
    let rebalance = info(&c, "Reservations.rebalance");
    assert_eq!(
        rebalance.expressions[0].ty,
        Type::Ref("Reservations.State".into())
    );
    let reserve = info(&c, "Reservations.Reserve");
    assert_eq!(
        reserve.parameters[1].1,
        Type::Owned("Reservations.State".into(), "owner".into())
    );
}

/// 宣言の原式から辿れる式。呼出し先の名前(view・constructor・固定演算の名前)は値ではないので除く。
fn reachable(c: &CheckedLaw) -> Vec<(archsig::law::ast::ExprId, bool)> {
    use archsig::law::ast::{ExprKind, QuantDomain, QuantSplit};
    use archsig::law::model::Signature;
    let mut roots = Vec::new();
    for d in c.declarations.values() {
        match &d.signature {
            Signature::View { body, .. } => roots.push(*body),
            Signature::Law { guard, body, .. } | Signature::Change { guard, body, .. } => {
                roots.extend(guard.iter().copied());
                roots.push(*body);
            }
            Signature::Local { guard, reads, .. } => {
                roots.extend(guard.iter().copied());
                roots.extend(reads.iter().copied());
            }
            Signature::Relation {
                guard, left, right, ..
            } => {
                roots.extend(guard.iter().copied());
                roots.extend([*left, *right]);
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    let mut stack: Vec<(usize, bool)> = roots.into_iter().map(|r| (r, true)).collect();
    while let Some((id, value)) = stack.pop() {
        out.push((id, value));
        let mut push = |e: usize| stack.push((e, true));
        match &c.exprs[id].kind {
            ExprKind::Let { value, body, .. } => [*value, *body].into_iter().for_each(&mut push),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => [*cond, *then_branch, *else_branch]
                .into_iter()
                .for_each(&mut push),
            ExprKind::Match { scrutinee, arms } => {
                push(*scrutinee);
                arms.iter().for_each(|a| push(a.body));
            }
            ExprKind::Quant { split, .. } => match split {
                QuantSplit::Fixed { domain, body } => {
                    if let QuantDomain::In(d) = domain {
                        push(*d);
                    }
                    push(*body);
                }
                other => panic!("区切りが確定していない量化: {other:?}"),
            },
            ExprKind::Binary { lhs, rhs, .. } => [*lhs, *rhs].into_iter().for_each(&mut push),
            ExprKind::Unary { operand, .. }
            | ExprKind::Group(operand)
            | ExprKind::Some(operand) => push(*operand),
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => push(*base),
            ExprKind::Call { callee, args } => {
                let mut name = *callee;
                while let ExprKind::Group(inner) = c.exprs[name].kind {
                    name = inner;
                }
                let is_name = matches!(c.exprs[name].kind, ExprKind::ThenOp)
                    || matches!(c.exprs[name].kind, ExprKind::Dotted(_))
                        && c.expr_type(name).is_none();
                if !is_name {
                    push(*callee);
                }
                args.iter().copied().for_each(&mut push);
            }
            ExprKind::With { base, updates } => {
                push(*base);
                updates.iter().for_each(|(_, e)| push(*e));
            }
            ExprKind::Tuple(items)
            | ExprKind::ListLit { items, .. }
            | ExprKind::SetLit { items, .. } => items.iter().copied().for_each(&mut push),
            ExprKind::SetComp {
                elem,
                domain,
                filter,
                ..
            } => {
                push(*elem);
                push(*domain);
                filter.iter().copied().for_each(&mut push);
            }
            ExprKind::Fn { body, .. } => push(*body),
            ExprKind::Family { owner, .. } => push(*owner),
            _ => {}
        }
    }
    out
}

#[test]
fn resolved_expressions_are_kept_in_memory_with_their_types() {
    let quants = reading(
        "entity S; entity A(owner: S) { x: Z; kids: Set<A>; pair: (Set<Z>, Z); }
         law required b(p: A): forall k in p.kids . k.x = p.x;
         law required c(p: A): exists n in p.pair.0 . n = p.pair.1;
         law required e(p: A): forall t: A . t.x = t.x;
         law required f(p: A): forall t: R.S . forall u: A[t] . u.x = u.x;
         view g(p: A): Set<Z> = set{ k.x | k in p.kids where forall j in k.kids . j.x > 0 };",
    );
    for src in [RESERVATIONS, ENGINE, quants.as_str()] {
        let c = ok(src);
        for (id, _) in reachable(&c) {
            assert!(
                c.expr_type(id).is_some(),
                "型のない式 `{}`",
                span_text(src, c.exprs[id].span)
            );
        }
    }
    // retained の量化は、域 State[m.from] と本体 holdings(m.states(s)) = holdings(s) に分かれる。
    let c = ok(RESERVATIONS);
    let archsig::law::model::Signature::Law { body, .. } =
        &c.declarations["Reservations.retained"].signature
    else {
        panic!()
    };
    let archsig::law::ast::ExprKind::Quant {
        split:
            archsig::law::ast::QuantSplit::Fixed {
                domain,
                body: inner,
            },
        ..
    } = &c.exprs[*body].kind
    else {
        panic!("量化")
    };
    let archsig::law::ast::QuantDomain::In(d) = domain else {
        panic!("域は式")
    };
    assert_eq!(span_text(RESERVATIONS, c.exprs[*d].span), "State[m.from]");
    assert_eq!(
        span_text(RESERVATIONS, c.exprs[*inner].span),
        "holdings(m.states(s)) = holdings(s)"
    );
    assert_eq!(
        c.expr_type(*d),
        Some(&Type::Set(Box::new(Type::Ref("Reservations.State".into()))))
    );
}
