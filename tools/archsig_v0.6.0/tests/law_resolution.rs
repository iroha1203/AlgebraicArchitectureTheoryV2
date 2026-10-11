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
