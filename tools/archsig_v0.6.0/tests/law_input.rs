//! Law の読込みの順序(UTF-8・字句、版、文法、宣言)と、量化の区切り。

mod common;
use archsig::issue::{Code, Details, Location};
use archsig::law::check_law;
use common::law_definitions::*;
use common::*;

fn failure(bytes: &[u8]) -> archsig::law::LawFailure {
    check_law(bytes, &definitions_ok(&[EMPTY_DEFINITION])).expect_err("落ちるはず")
}

fn span_of(issue: &archsig::issue::Issue) -> (usize, usize) {
    let Location::Law { span } = issue.location else {
        panic!("Law の位置")
    };
    span
}

#[test]
fn encoding_errors_come_first() {
    let mut bom = vec![0xEF, 0xBB, 0xBF];
    bom.extend_from_slice(RESERVATIONS.as_bytes());
    let f = failure(&bom);
    assert_eq!((f.issue.code, span_of(&f.issue)), (Code::Syntax, (0, 3)));
    assert_eq!(f.model_digest, None);

    let mut bad = RESERVATIONS.as_bytes().to_vec();
    let at = RESERVATIONS.find("Reservations").unwrap();
    bad[at] = 0xFF;
    let f = failure(&bad);
    assert_eq!(
        (f.issue.code, span_of(&f.issue)),
        (Code::Syntax, (at, at + 1))
    );
}

#[test]
fn unknown_versions_are_unsupported_before_the_grammar_is_read() {
    let future = "law \"archsig.law/3\" semantics \"archsig/0.6.0\";\nreading X { future @Thing <- 007 \"\\ud800\"; }\n";
    let f = failure(future.as_bytes());
    assert_eq!(f.issue.code, Code::UnsupportedVersion);
    assert_eq!(
        f.issue.details,
        Details::Version {
            found_format: "archsig.law/3".into(),
            found_semantics: Some("archsig/0.6.0".into())
        }
    );
    assert_eq!(span_of(&f.issue), (0, future.find(';').unwrap() + 1));
    let semantics = RESERVATIONS.replace("\"archsig/0.6.0\"", "\"archsig/0.7.0\"");
    assert_eq!(
        failure(semantics.as_bytes()).issue.code,
        Code::UnsupportedVersion
    );
    // 版の文字列は escape を解いて比べる。
    let escaped = RESERVATIONS.replace("\"archsig.law/2\"", "\"archsig.law\\/2\"");
    ok(RESERVATIONS_DEFINITION, &escaped);
    // header 自体が読めなければ構文エラー。
    assert_eq!(failure(b"law \"archsig.law/1\";").issue.code, Code::Syntax);
    assert_eq!(failure(HEADER.as_bytes()).issue.code, Code::Syntax);
    assert_eq!(
        failure(format!("{HEADER}reading A {{ entity S; }} junk").as_bytes())
            .issue
            .code,
        Code::Syntax
    );
}

#[test]
fn quantifier_separator_is_chosen_by_the_domain_type() {
    let c = ok(
        DEF_31,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:73fd11199856d7666429e6aaebf6f4ff127f0b686b02d02ef79222cd411f67c0";
law required a(s: S): forall a in A[s] . a.x >= 0;
         law required b(p: A): forall k in p.kids . k.x = p.x;
         law required c(p: A): exists n in p.pair.0 . n = p.pair.1;
         law required d(p: A): forall k in p.kids . 0 <= k.x;
         law required e(p: A): forall t: A . t.x = t.x;
         law required f(p: A): forall t: R.S . forall u: A[t] . u.x = u.x;"#,
        ),
    );
    let b = c.infos.iter().find(|i| i.name == "R.b").unwrap();
    let names: Vec<_> = b.references.iter().map(|(_, n)| n.as_str()).collect();
    assert_eq!(names, ["R.A", "R.A.kids", "R.A.x", "R.A.x"]);
    // 量化の域と本体の区切りがどの位置でも List/Set にならなければ型エラー。
    let issue = err(
        DEF_08,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
law required l(p: A): forall k in p.x . k = 0;"#,
        ),
    );
    assert_eq!(issue.code, Code::Type);
}

/// 区切りの `.` の前後が観測族・if・let・数値射影でも、型の正しい量化を受理する。
#[test]
fn quantifier_bodies_and_domains_of_any_shape_are_accepted() {
    let c = ok(
        DEF_32,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:45c6422582c2180d5e0a7021e79ff8797d17ea7199f92e49695ebf52ffc9e22c";
law optional a(): exists s: S . A[s] = set<A>{};
         law optional b(w: W): forall s in w.roots . A[s] = A[s];
         law optional c(s: S): forall a in A[s] . A[s] = A[s];
         law optional d(p: (Z, Z)): forall t: S . p.0 = 1;
         law required e(s: S): forall x in if s.b then s.xs else s.ys . x = 1;
         law required f(s: S): forall x in let ys = s.xs in ys . x = 1;
         law optional g(): exists s: R.S . R.A[s] = set<A>{};
         law optional h(s: S): forall x in s.xs . forall y in s.ys . (x, y).0 = x;

         law optional i(): forall p: Path<A, A> . p = p;
         law optional j(): exists m: Map<A, A> . true;
         law optional k(): forall p: Option<Path<A, A>> . true;
         law optional l(): forall m in list<Map<A, A>>[] . (m, 1).1 = 1;
         view n(xs: List<Z>): (Bool, Z) = (forall x in xs . x > 0, 1);"#,
        ),
    );
    let e = c.infos.iter().find(|i| i.name == "R.e").unwrap();
    assert_eq!(e.expressions[0].ty, archsig::types::Type::Bool);
    // let の右辺の量化は let の区切りの `in` を越えない。
    ok(
        DEF_33,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:c59925ec8392dde0e4b250d6ba92796ce765e80ce96fb86ee43cbc7040dcdaef";
view q(n: Z): Bool = n > 0;
         view v(s: A, xs: List<Z>): Bool = let b = forall x in xs . q(x) in b and s.flag;
         law required l(s: A, xs: List<A>): let b = forall t in xs . t.flag in b and s.flag;
         view w(s: A, xs: List<Z>, c: Bool): Bool = let b = if c then true else forall x in xs . q(x) in b and s.flag;"#,
        ),
    );
    // 型名が二通りに読めるときは最も長い名前を選ぶ。
    let order = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Order {
use vocabulary Order version "1" digest "sha256:869f5c9c07e3c778e53cea986f1620194fc94caa4553cd40ff8128b8a3466224";
law required l(): forall x: Order.Line . x.q >= 0;
}
"#;
    ok(DEF_42, &order);
    let nested = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading A {
use vocabulary A version "1" digest "sha256:5a6911b16cba7815de2ba42ac5e7bc7be03c97fd110c9d8399ac89be08acf14c";

}
reading R {
use vocabulary A version "1" digest "sha256:5a6911b16cba7815de2ba42ac5e7bc7be03c97fd110c9d8399ac89be08acf14c";
use vocabulary R version "1" digest "sha256:fa0a1c1f666167afd37ccb8dfb7efd709fcbf23090931f28e272e52cb9448106";
law required k(): forall x: A.B . x = x;
}
"#;
    let c = ok(DEF_45, &nested);
    let k = c.infos.iter().find(|i| i.name == "R.k").unwrap();
    assert!(k.dependencies.contains(&"A.B".to_owned()));
    // 域が List/Set になる区切りがない量化は拒否する。
    let issue = err(
        DEF_34,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:608157eaa053d5d13461ae3567f77049880672c92aa6c62808d1e717aa392645";
law required l(s: S): forall x in s.n . x = 1;"#,
        ),
    );
    assert_eq!(issue.code, Code::Type);
}

#[test]
fn old_law_and_embedded_primitives_are_rejected() {
    let old = RESERVATIONS.replace("archsig.law/2", "archsig.law/1");
    assert_eq!(failure(old.as_bytes()).issue.code, Code::UnsupportedVersion);
    for body in ["entity S;", "arrow M;", "data D = C;", "correspondence M;"] {
        let src = reading(body);
        let f = failure(src.as_bytes());
        assert_eq!(f.issue.code, Code::Syntax);
        assert!(span_of(&f.issue).1 <= src.len());
    }
}
