//! AC3: 解決の追跡。短形と明示形、既定規則、暗黙 align、constructor metadata、Location。

mod common;
use archsig::law::CheckedLaw;
use archsig::law::model::{DeclarationInfo, ExpressionKind, SuppliedRule};
use archsig::types::Type;
use common::law_definitions::*;
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
    let short = ok(RESERVATIONS_DEFINITION, RESERVATIONS);
    let explicit = ok(RESERVATIONS_DEFINITION, &explicit_src);
    assert_eq!(
        short.definitions.vocabularies,
        explicit.definitions.vocabularies
    );
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
    let c = ok(RESERVATIONS_DEFINITION, RESERVATIONS);
    let r = info(&c, "Reservations");
    assert_eq!(
        r.supplied,
        vec![SuppliedRule::LocalDeclared { span: r.span }]
    );
    assert_eq!(
        span_text(RESERVATIONS, r.span),
        RESERVATIONS[RESERVATIONS.find("reading").unwrap()..].trim_end()
    );
    let without = reading(
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
law required l(a: A): a.x = 0;"#,
    );
    let c = ok(DEF_08, &without);
    let r = info(&c, "R");
    assert_eq!(
        r.supplied,
        vec![SuppliedRule::LocalSupport { span: r.span }]
    );
}

#[test]
fn implicit_alignment_is_recorded_apart_from_explicit_alignment() {
    use archsig::definition::PrimitiveSignature;
    let c = ok(RESERVATIONS_DEFINITION, RESERVATIONS);
    let m = &c.definitions.declarations["Reservations.Migration"];
    let PrimitiveSignature::Correspondence { implicit, .. } = &m.signature else {
        panic!()
    };
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
    assert_eq!(*implicit, expected);
    assert_eq!(
        m.location,
        archsig::issue::Location::Definition {
            input: "definition0".into(),
            pointer: "/vocabularies/0/declarations/0".into(),
            span: None
        }
    );
    assert!(
        c.definitions.vocabularies["Reservations"]
            .manifest
            .canonical()
            .contains(r#""alignments":[]"#)
    );
    let swapped = definitions_ok(&[DEF_35]);
    let sw = &swapped.declarations["R.Swap"];
    let PrimitiveSignature::Correspondence {
        implicit,
        alignments,
        ..
    } = &sw.signature
    else {
        panic!()
    };
    assert_eq!(
        *implicit,
        vec![("R.A.owner".to_owned(), "R.A.owner".to_owned())]
    );
    assert_eq!(
        alignments
            .iter()
            .map(|a| (a.source.as_str(), a.target.as_str()))
            .collect::<Vec<_>>(),
        [("R.A.x", "R.A.y"), ("R.A.y", "R.A.x")]
    );
    for a in alignments {
        assert!(matches!(
            a.location,
            archsig::issue::Location::Definition { .. }
        ));
    }
}

#[test]
fn constructors_have_their_own_metadata() {
    use archsig::definition::PrimitiveSignature;
    let c = ok(ENGINE_DEFINITION, ENGINE);
    let data = &c.definitions.declarations["Engine.Expr"];
    let PrimitiveSignature::Data { constructors } = &data.signature else {
        panic!()
    };
    let lit = &constructors[0];
    assert_eq!(lit.name, "Lit");
    assert_eq!(lit.arguments, vec![Type::Z]);
    assert_eq!(
        lit.location,
        archsig::issue::Location::Definition {
            input: "definition0".into(),
            pointer: "/vocabularies/0/declarations/1/constructors/0".into(),
            span: None
        }
    );
    assert_eq!(constructors[1].name, "Var");
    assert!(constructors[1].arguments.is_empty());
    assert_eq!(
        constructors[2].arguments,
        vec![
            Type::Data("Engine.Expr".into()),
            Type::Data("Engine.Expr".into())
        ]
    );
    assert_eq!(data.dependencies, ["Engine.Expr"]);
    assert_eq!(
        data.location,
        archsig::issue::Location::Definition {
            input: "definition0".into(),
            pointer: "/vocabularies/0/declarations/1".into(),
            span: None
        }
    );
    use archsig::canonical::Json;
    let rows = archsig::result::primitive_declarations_wire(data);
    let obj = |j: &Json| {
        if let Json::Obj(_) = j {
        } else {
            panic!()
        }
    };
    rows.iter().for_each(obj);
    let Json::Obj(lit_wire) = &rows[1] else {
        panic!()
    };
    assert_eq!(lit_wire["name"], Json::str("Engine.Expr.Lit"));
    assert_eq!(lit_wire["kind"], Json::str("data"));
    assert_eq!(
        lit_wire["parameters"],
        Json::Arr(vec![Json::obj([
            ("name", Json::str("arg0")),
            ("type", Type::Z.wire())
        ])])
    );
    assert_eq!(
        lit_wire["location"],
        archsig::result::location_wire(&lit.location)
    );
    assert_eq!(lit_wire["vocabularies"], Json::Arr(vec![]));
    let Json::Obj(add_wire) = &rows[3] else {
        panic!()
    };
    assert_eq!(
        add_wire["parameters"],
        Json::Arr(vec![
            Json::obj([
                ("name", Json::str("arg0")),
                ("type", Type::Data("Engine.Expr".into()).wire())
            ]),
            Json::obj([
                ("name", Json::str("arg1")),
                ("type", Type::Data("Engine.Expr".into()).wire())
            ])
        ])
    );
    assert_eq!(
        add_wire["dependencies"],
        Json::Arr(vec![Json::str("Engine.Expr")])
    );
    let translate = info(&c, "Engine.translate");
    for (name, text) in [("Engine.IR.Plus", "Plus"), ("Engine.Expr.Lit", "Lit")] {
        let r = translate
            .references
            .iter()
            .find(|(_, n)| n == name)
            .unwrap();
        assert_eq!(span_text(ENGINE, r.0), text);
    }
}

#[test]
fn references_through_parentheses_point_at_the_name() {
    let src = reading(
        r#"use vocabulary R version "1" digest "sha256:fc16a746d9bbf546e29b15de1761fc4bdb4547c1a3a764f41cbad994f79967c8";
view f(x: Z): Z = x;
         view g(): Z = ((f))( 1 ) + ( /* */ f)(2);
         view h(): D = (D.C)(1);
         view k(): D = ( R.D.C )(2);"#,
    );
    let src = src.replace("/* */", "");
    let c = ok(DEF_36, &src);
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
    for (def, src) in [
        (RESERVATIONS_DEFINITION, RESERVATIONS),
        (ENGINE_DEFINITION, ENGINE),
        (
            RESERVATIONS_DEFINITION,
            RESERVATIONS.replace(SHORT, EXPLICIT).as_str(),
        ),
    ] {
        let c = ok(def, src);
        assert_locations(src, &c);
    }
    let unicode = reading(
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view t(): Text = "日本語の文字列"; view u(): Z = count(list<Text>["é", t()]);"#,
    );
    assert_locations(&unicode, &ok(DEF_04, &unicode));
}

#[test]
fn declarations_are_listed_by_full_name_with_expression_types() {
    let c = ok(RESERVATIONS_DEFINITION, RESERVATIONS);
    let names: Vec<_> = c.infos.iter().map(|i| i.name.as_str()).collect();
    let mut sorted = names.clone();
    sorted.sort();
    assert_eq!(names, sorted);
    assert_eq!(names.len(), 8);
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
    let reserve = &c.definitions.declarations["Reservations.Reserve"];
    assert_eq!(
        reserve.signature.field("from").unwrap().ty,
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
        r#"use vocabulary R version "1" digest "sha256:73fd11199856d7666429e6aaebf6f4ff127f0b686b02d02ef79222cd411f67c0";
law required b(p: A): forall k in p.kids . k.x = p.x;
         law required c(p: A): exists n in p.pair.0 . n = p.pair.1;
         law required e(p: A): forall t: A . t.x = t.x;
         law required f(p: A): forall t: R.S . forall u: A[t] . u.x = u.x;
         view g(p: A): Set<Z> = set{ k.x | k in p.kids where forall j in k.kids . j.x > 0 };"#,
    );
    for (def, src) in [
        (RESERVATIONS_DEFINITION, RESERVATIONS),
        (ENGINE_DEFINITION, ENGINE),
        (DEF_31, quants.as_str()),
    ] {
        let c = ok(def, src);
        for (id, _) in reachable(&c) {
            assert!(
                c.expr_type(id).is_some(),
                "型のない式 `{}`",
                span_text(src, c.exprs[id].span)
            );
        }
    }
    // retained の量化は、域 State[m.from] と本体 holdings(m.states(s)) = holdings(s) に分かれる。
    let c = ok(RESERVATIONS_DEFINITION, RESERVATIONS);
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

const SCOPE_DEFINITION: &str = include_str!("fixtures/law-scope.atoms.json");
const IMPORT_A: &str = r#"use vocabulary A version "1" digest "sha256:da3d613a3c0971fa5e60be83a68f5ce8a26864e768b8e789ec4c742cb282415f";"#;
const IMPORT_B: &str = r#"use vocabulary B version "1" digest "sha256:848963f024e20d44d51d63c159cecdd22c8d8eee87047480b83b97b0345870c9";"#;

#[test]
fn counter_readings_share_one_primitive_type_and_keep_direct_imports() {
    let c = ok(COUNTER_DEFINITION, COUNTER);
    assert_eq!(c.definitions.declarations.len(), 1);
    assert!(!c.declarations.contains_key("Counter.State"));
    for n in [
        "CountCheck.amount",
        "CountCheck.nonnegative",
        "CountAudit.bounded",
    ] {
        assert_eq!(
            info(&c, n).parameters[0].1,
            Type::Ref("Counter.State".into())
        );
    }
    for n in ["CountCheck", "CountAudit"] {
        let r = info(&c, n);
        assert_eq!(r.vocabularies.len(), 1);
        assert_eq!(r.vocabularies[0].namespace, "Counter");
        let archsig::issue::Location::Law { span } = r.vocabularies[0].location else {
            panic!()
        };
        assert!(span_text(COUNTER, span).starts_with("use vocabulary Counter"));
    }
    assert!(
        c.infos
            .iter()
            .filter(|i| i.kind != "reading")
            .all(|i| i.vocabularies.is_empty())
    );
}

#[test]
fn direct_import_is_required_for_full_names_but_not_signature_dependencies() {
    let indirect = reading(&format!("{IMPORT_A} view v(h: Holder): Z = h.other.x;"));
    let c = ok(SCOPE_DEFINITION, &indirect);
    assert!(
        info(&c, "R.v")
            .references
            .iter()
            .any(|(_, n)| n == "B.State.x")
    );
    for body in [
        "view v(s: B.State): Z = s.x;",
        "view v(): B.D = B.D.C(1);",
        "view v(): Term<(Z) -> B.D> = fn(n: Z) => B.D.C(n);",
    ] {
        let src = reading(&format!("{IMPORT_A} {body}"));
        assert_eq!(
            err(SCOPE_DEFINITION, &src).code,
            archsig::issue::Code::Reference
        );
        let src = reading(&format!("{IMPORT_A} {IMPORT_B} {body}"));
        ok(SCOPE_DEFINITION, &src);
    }
}

#[test]
fn ambiguous_short_names_require_full_names_and_imports_are_sorted() {
    let src = reading(&format!("{IMPORT_B} {IMPORT_A} view v(s: State): Z = s.x;"));
    assert_eq!(
        err(SCOPE_DEFINITION, &src).code,
        archsig::issue::Code::Reference
    );
    let src = src.replace("s: State", "s: A.State");
    let c = ok(SCOPE_DEFINITION, &src);
    assert_eq!(
        info(&c, "R")
            .vocabularies
            .iter()
            .map(|v| v.namespace.as_str())
            .collect::<Vec<_>>(),
        ["A", "B"]
    );
    assert_eq!(info(&c, "R.v").parameters[0].1, Type::Ref("A.State".into()));
    let duplicate = reading(&format!("{IMPORT_A} {IMPORT_A}"));
    assert_eq!(
        err(SCOPE_DEFINITION, &duplicate).code,
        archsig::issue::Code::DuplicateId
    );
}

#[test]
fn namespace_reading_name_is_allowed_but_full_declaration_collision_is_rejected() {
    let valid = format!("{HEADER}reading A {{ {IMPORT_A} view amount(s: State): Z = s.x; }}");
    ok(SCOPE_DEFINITION, &valid);
    let collision = format!("{HEADER}reading A {{ {IMPORT_A} view State(): Z = 1; }}");
    assert_eq!(
        err(SCOPE_DEFINITION, &collision).code,
        archsig::issue::Code::DuplicateId
    );
}

#[test]
fn unused_imports_are_checked_and_retained() {
    let src = reading(&format!("{IMPORT_A} {IMPORT_B}"));
    let c = ok(SCOPE_DEFINITION, &src);
    assert_eq!(info(&c, "R").vocabularies.len(), 2);
    for (from, to, code) in [
        (
            "vocabulary A",
            "vocabulary Missing",
            archsig::issue::Code::Reference,
        ),
        (
            "version \"1\"",
            "version \"2\"",
            archsig::issue::Code::VocabularyMismatch,
        ),
        (
            "sha256:da3d613a3c0971fa5e60be83a68f5ce8a26864e768b8e789ec4c742cb282415f",
            "sha256:0000000000000000000000000000000000000000000000000000000000000000",
            archsig::issue::Code::VocabularyMismatch,
        ),
    ] {
        let bad = src.replacen(from, to, 1);
        assert_ne!(bad, src);
        let issue = err(SCOPE_DEFINITION, &bad);
        assert_eq!(issue.code, code);
        let archsig::issue::Location::Law { span } = issue.location else {
            panic!()
        };
        assert!(span_text(&bad, span).contains("use vocabulary"));
    }
}

const BEFORE_AFTER: &str = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {
  use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
  law required nonnegative(s: State): s.free >= 0;
}
reading After {
  use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
  law required nonnegative(t: State): t.free >= 5;
}
"#;

#[test]
fn before_after_variants_are_valid_without_cross_reading_preservation() {
    let variants = [
        BEFORE_AFTER.to_owned(),
        BEFORE_AFTER.replace("nonnegative(t:", "bounded(t:"),
        BEFORE_AFTER.replace("nonnegative(t: State)", "nonnegative(t: State, limit: Z)"),
        BEFORE_AFTER.replace("law required nonnegative(t:", "law optional nonnegative(t:"),
    ];
    for src in variants {
        let c = ok(RESERVATIONS_DEFINITION, &src);
        let before = info(&c, "Before.nonnegative");
        let after = c
            .infos
            .iter()
            .find(|i| i.name == "After.nonnegative" || i.name == "After.bounded")
            .unwrap();
        assert_eq!(before.parameters[0].1, after.parameters[0].1);
        assert_eq!(
            before.parameters[0].1,
            Type::Ref("Reservations.State".into())
        );
        assert_eq!(span_text(&src, before.expressions[0].span), "s.free >= 0");
        assert_eq!(span_text(&src, after.expressions[0].span), "t.free >= 5");
        assert_eq!(c.definitions.declarations.len(), 4);
        assert_ne!(before.span, after.span);
    }
}

const QUALIFIED_PRIMITIVES: &str = include_str!("fixtures/qualified-primitive.atoms.json");
const QUALIFIED_COUNTER_IMPORT: &str = r#"use vocabulary Counter version "1" digest "sha256:cd681e7b88cd6339d41fb5dad43c2f9ccc33687856841da9924ccc4ab06ebff5";"#;
const QUALIFIED_OTHER_IMPORT: &str = r#"use vocabulary Other version "1" digest "sha256:03c2763098a3408a17a02cebff915af95c2a68c9d77c8b514e1ede7d6e74622a";"#;

#[test]
fn full_primitive_names_precede_relative_constructor_candidates() {
    let src = format!(
        "{HEADER}reading Helpers {{ {QUALIFIED_COUNTER_IMPORT} view amount(s: Counter.State): Z = s.count; }}\nreading R {{ {QUALIFIED_COUNTER_IMPORT} use Helpers as H; view direct(s: Counter.State): Z = s.count; view via_alias(s: Counter.State): Z = H.amount(s); view tag(): Counter.Counter = Counter.Counter.State; }}"
    );
    let c = ok(QUALIFIED_PRIMITIVES, &src);
    assert!(c.definitions.declarations.contains_key("Counter.State"));
    assert!(c.definitions.declarations.contains_key("Counter.Counter"));
    for name in ["Helpers.amount", "R.direct", "R.via_alias"] {
        let i = info(&c, name);
        assert_eq!(
            i.parameters,
            [("s".to_owned(), Type::Ref("Counter.State".into()))]
        );
        let r = i
            .references
            .iter()
            .find(|(_, n)| n == "Counter.State")
            .unwrap();
        assert_eq!(span_text(&src, r.0), "Counter.State");
    }
    let via_alias = info(&c, "R.via_alias");
    let r = via_alias
        .references
        .iter()
        .find(|(_, n)| n == "Helpers.amount")
        .unwrap();
    assert_eq!(span_text(&src, r.0), "H.amount");
    assert_eq!(info(&c, "R").dependencies, ["Helpers"]);
    let direct = info(&c, "R.direct");
    assert!(
        direct
            .references
            .iter()
            .any(|(span, n)| n == "Counter.State.count" && span_text(&src, *span) == "count")
    );
    let tag = info(&c, "R.tag");
    assert_eq!(tag.returns, Some(Type::Data("Counter.Counter".into())));
    let r = tag
        .references
        .iter()
        .find(|(_, n)| n == "Counter.Counter.State")
        .unwrap();
    assert_eq!(span_text(&src, r.0), "Counter.Counter.State");
    // 完全名を直接使う reading は、実在する語彙でも直接importする。
    let missing = reading("view v(s: Counter.State): Z = s.count;");
    assert_eq!(
        err(QUALIFIED_PRIMITIVES, &missing).code,
        archsig::issue::Code::Reference
    );
}

#[test]
fn short_primitive_ambiguity_stays_reference_after_full_name_priority() {
    let src = reading(&format!(
        "{QUALIFIED_COUNTER_IMPORT} {QUALIFIED_OTHER_IMPORT} view v(s: State): Z = s.count;"
    ));
    let issue = err(QUALIFIED_PRIMITIVES, &src);
    assert_eq!(issue.code, archsig::issue::Code::Reference);
    let archsig::issue::Location::Law { span } = issue.location else {
        panic!()
    };
    assert_eq!(span_text(&src, span), "State");
    let src = src.replace("s: State", "s: Counter.State");
    let c = ok(QUALIFIED_PRIMITIVES, &src);
    assert_eq!(
        info(&c, "R.v").parameters[0].1,
        Type::Ref("Counter.State".into())
    );
}

#[test]
fn reading_alias_precedes_same_named_reading_full_names() {
    let src = format!(
        "{HEADER}reading A {{ view f(): Z = 1; }} reading B {{ view f(): Z = 2; }} reading R {{ use B as A; view g(): Z = A.f(); }}"
    );
    let c = ok(EMPTY_DEFINITION, &src);
    let g = info(&c, "R.g");
    assert_eq!(g.dependencies, ["B.f"]);
    assert_eq!(g.references.len(), 1);
    assert_eq!(g.references[0].1, "B.f");
    assert_eq!(span_text(&src, g.references[0].0), "A.f");
    assert_eq!(span_text(&src, g.expressions[0].span), "A.f()");
    let r = info(&c, "R");
    assert_eq!(r.dependencies, ["B"]);
    assert_eq!(r.references.len(), 1);
    assert_eq!(r.references[0].1, "B");
    assert_eq!(span_text(&src, r.references[0].0), "B");
    // 定数の原式は独立した宣言に保持し、呼出しの解決先だけを選ぶ。
    assert_eq!(span_text(&src, info(&c, "A.f").expressions[0].span), "1");
    assert_eq!(span_text(&src, info(&c, "B.f").expressions[0].span), "2");
}

#[test]
fn missing_alias_member_does_not_fall_back_to_raw_reading() {
    let src = format!(
        "{HEADER}reading A {{ view f(): Z = 1; }} reading B {{ view other(): Z = 2; }} reading R {{ use B as A; view g(): Z = A.f(); }}"
    );
    let issue = err(EMPTY_DEFINITION, &src);
    assert_eq!(issue.code, archsig::issue::Code::Reference);
    let archsig::issue::Location::Law { span } = issue.location else {
        panic!()
    };
    assert_eq!(span_text(&src, span), "A.f");
}

#[test]
fn reading_alias_shadows_primitive_namespace_after_variable_projection() {
    let src = format!(
        "{HEADER}reading B {{ view f(): Z = 2; }} reading R {{ {QUALIFIED_COUNTER_IMPORT} use B as Counter; view g(s: State): Z = Counter.f() + s.count; view projected(Counter: State): Z = Counter.count; }}"
    );
    let c = ok(QUALIFIED_PRIMITIVES, &src);
    let g = info(&c, "R.g");
    assert_eq!(g.parameters[0].1, Type::Ref("Counter.State".into()));
    let alias = g.references.iter().find(|(_, name)| name == "B.f").unwrap();
    assert_eq!(span_text(&src, alias.0), "Counter.f");
    assert_eq!(info(&c, "R").dependencies, ["B"]);
    let projected = info(&c, "R.projected");
    assert_eq!(projected.parameters[0].0, "Counter");
    assert_eq!(projected.parameters[0].1, Type::Ref("Counter.State".into()));
    let field = projected
        .references
        .iter()
        .find(|(_, name)| name == "Counter.State.count")
        .unwrap();
    assert_eq!(span_text(&src, field.0), "count");
    assert!(!projected.dependencies.contains(&"B.count".to_owned()));

    // 短名の原始型には直接importが要る。reading aliasはその代わりにならない。
    let missing_import = src.replace(QUALIFIED_COUNTER_IMPORT, "");
    assert_eq!(
        err(QUALIFIED_PRIMITIVES, &missing_import).code,
        archsig::issue::Code::Reference
    );
    // namespaceと同じaliasも展開後の名前だけを解決し、原始完全名へ戻らない。
    for (body, original) in [
        ("view bad(s: Counter.State): Z = s.count;", "Counter.State"),
        (
            "view bad(): Z = Counter.Counter.State;",
            "Counter.Counter.State",
        ),
    ] {
        let src = format!(
            "{HEADER}reading B {{ }} reading R {{ {QUALIFIED_COUNTER_IMPORT} use B as Counter; {body} }}"
        );
        let issue = err(QUALIFIED_PRIMITIVES, &src);
        assert_eq!(issue.code, archsig::issue::Code::Reference);
        let archsig::issue::Location::Law { span } = issue.location else {
            panic!()
        };
        assert_eq!(span_text(&src, span), original);
    }
}
