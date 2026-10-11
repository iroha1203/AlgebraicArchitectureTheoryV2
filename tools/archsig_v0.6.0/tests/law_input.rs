//! Law の読込みの順序(UTF-8・字句、版、文法、宣言)と、深い入れ子の入力。

mod common;
use archsig::issue::{Code, Details, Location};
use archsig::law::check_law;
use common::*;
use std::time::{Duration, Instant};

fn failure(bytes: &[u8]) -> archsig::law::LawFailure {
    check_law(bytes).expect_err("落ちるはず")
}

fn span_of(issue: &archsig::issue::Issue) -> (usize, usize) {
    let Location::Law { span } = issue.location;
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
    let at = RESERVATIONS.find("System").unwrap();
    bad[at] = 0xFF;
    let f = failure(&bad);
    assert_eq!(
        (f.issue.code, span_of(&f.issue)),
        (Code::Syntax, (at, at + 1))
    );
}

#[test]
fn unknown_versions_are_unsupported_before_the_grammar_is_read() {
    let future = "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading X { future @Thing <- 007 \"\\ud800\"; }\n";
    let f = failure(future.as_bytes());
    assert_eq!(f.issue.code, Code::UnsupportedVersion);
    assert_eq!(
        f.issue.details,
        Details::Version {
            found_format: "archsig.law/2".into(),
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
    let escaped = RESERVATIONS.replace("\"archsig.law/1\"", "\"archsig.law\\/1\"");
    ok(&escaped);
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

fn within(limit: Duration, f: impl FnOnce()) {
    let start = Instant::now();
    f();
    assert!(start.elapsed() < limit, "{:?}", start.elapsed());
}

/// 深い入れ子の正しい Law を、通常の大きさのスタックを持つ呼出し側から検査し、結果を捨てる。
#[test]
fn deeply_nested_valid_input_is_checked_without_crashing() {
    let n = 100_000;
    let parens = reading(&format!(
        "view f(): Z = {}0{};",
        "(".repeat(n),
        ")".repeat(n)
    ));
    let negs = reading(&format!("view g(): Z = {}1;", "- ".repeat(n)));
    let implies = reading(&format!(
        "law optional h(): {}true;",
        "true implies ".repeat(n)
    ));
    let field = reading(&format!(
        "entity E {{ f: {}Z{}; }}",
        "List<".repeat(n),
        ">".repeat(n)
    ));
    let lists = reading(&format!(
        "view k(): {}Z{} = list<{}Z{}>[];",
        "List<".repeat(n),
        ">".repeat(n),
        "List<".repeat(n - 1),
        ">".repeat(n - 1)
    ));
    let mut pattern = String::from("_");
    for _ in 0..n {
        pattern = format!("Node({pattern})");
    }
    let patterns = reading(&format!(
        "data T = Leaf | Node(T); view p(t: T): Z = match t {{ {pattern} => 1; _ => 0; }};"
    ));
    // 文脈の型を探す読み、data の再帰の検査、correspondence の型の運搬も深さに耐える。
    let m = 400_000;
    let compared = reading(&format!(
        "law optional l(x: Z): {}1{} = x;",
        "(".repeat(m),
        ")".repeat(m)
    ));
    let negated = reading(&format!("law optional l(x: Z): {}1 = x;", "- ".repeat(m)));
    let tree = reading(&format!(
        "data T = L | N({}T{});",
        "List<".repeat(m),
        ">".repeat(m)
    ));
    let moved = reading(&format!(
        "entity S; entity A(owner: S) {{ f: {}Z{}; }} correspondence M(from: S, to: S) {{ xs: Map<A[from], A[to]>; }}",
        "List<".repeat(m),
        ">".repeat(m)
    ));
    for src in [
        parens, negs, implies, field, lists, patterns, compared, negated, tree, moved,
    ] {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(move || {
                within(Duration::from_secs(60), || {
                    let c = ok(&src);
                    assert!(!c.infos.is_empty());
                })
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[test]
fn nested_quantifier_splits_stay_fast() {
    let depth = 40;
    let mut body = String::from("true");
    for i in (1..=depth).rev() {
        body = format!("forall a{i} in a{}.kids . {body}", i - 1);
    }
    let src = reading(&format!(
        "entity S; entity A(owner: S) {{ kids: Set<A>; }} law required l(a0: A): {body};"
    ));
    within(Duration::from_secs(20), || {
        ok(&src);
    });
    let mut typed = String::from("true");
    for i in (1..=depth).rev() {
        typed = format!("forall t{i}: R.A . t{i}.kids = t{i}.kids and ({typed})");
    }
    let src = reading(&format!(
        "entity S; entity A(owner: S) {{ kids: Set<A>; }} law required l(): {typed};"
    ));
    within(Duration::from_secs(20), || {
        ok(&src);
    });
}

#[test]
fn quantifier_separator_is_chosen_by_the_domain_type() {
    let c = ok(&reading(
        "entity S; entity A(owner: S) { x: Z; kids: Set<A>; pair: (Set<Z>, Z); }
         law required a(s: S): forall a in A[s] . a.x >= 0;
         law required b(p: A): forall k in p.kids . k.x = p.x;
         law required c(p: A): exists n in p.pair.0 . n = p.pair.1;
         law required d(p: A): forall k in p.kids . 0 <= k.x;
         law required e(p: A): forall t: A . t.x = t.x;
         law required f(p: A): forall t: R.S . forall u: A[t] . u.x = u.x;",
    ));
    let b = c.infos.iter().find(|i| i.name == "R.b").unwrap();
    let names: Vec<_> = b.references.iter().map(|(_, n)| n.as_str()).collect();
    assert_eq!(names, ["R.A", "R.A.kids", "R.A.x", "R.A.x"]);
    // 量化の域と本体の区切りがどの位置でも List/Set にならなければ型エラー。
    let issue = err(&reading(
        "entity S; entity A(owner: S) { x: Z; } law required l(p: A): forall k in p.x . k = 0;",
    ));
    assert_eq!(issue.code, Code::Type);
}

/// 区切りの `.` の前後が観測族・if・let・数値射影でも、型の正しい量化を受理する。
#[test]
fn quantifier_bodies_and_domains_of_any_shape_are_accepted() {
    let c = ok(&reading(
        "entity S { xs: Set<Z>; ys: Set<Z>; b: Bool; } entity A(owner: S) { x: Z; } entity W { roots: Set<S>; }
         law optional a(): exists s: S . A[s] = set<A>{};
         law optional b(w: W): forall s in w.roots . A[s] = A[s];
         law optional c(s: S): forall a in A[s] . A[s] = A[s];
         law optional d(p: (Z, Z)): forall t: S . p.0 = 1;
         law required e(s: S): forall x in if s.b then s.xs else s.ys . x = 1;
         law required f(s: S): forall x in let ys = s.xs in ys . x = 1;
         law optional g(): exists s: R.S . R.A[s] = set<A>{};
         law optional h(s: S): forall x in s.xs . forall y in s.ys . (x, y).0 = x;
         arrow M(owner: S, from: A[owner], to: A[owner]);
         law optional i(): forall p: Path<A, A> . p = p;
         law optional j(): exists m: Map<A, A> . true;
         law optional k(): forall p: Option<Path<A, A>> . true;
         law optional l(): forall m in list<Map<A, A>>[] . (m, 1).1 = 1;
         view n(xs: List<Z>): (Bool, Z) = (forall x in xs . x > 0, 1);",
    ));
    let e = c.infos.iter().find(|i| i.name == "R.e").unwrap();
    assert_eq!(e.expressions[0].ty, archsig::types::Type::Bool);
    // let の右辺の量化は let の区切りの `in` を越えない。
    ok(&reading(
        "entity S; entity A(owner: S) { flag: Bool; x: Z; } view q(n: Z): Bool = n > 0;
         view v(s: A, xs: List<Z>): Bool = let b = forall x in xs . q(x) in b and s.flag;
         law required l(s: A, xs: List<A>): let b = forall t in xs . t.flag in b and s.flag;
         view w(s: A, xs: List<Z>, c: Bool): Bool = let b = if c then true else forall x in xs . q(x) in b and s.flag;",
    ));
    // 型名が二通りに読めるときは最も長い名前を選ぶ。
    let order = format!(
        "{HEADER}reading Order {{ entity Order; entity Line(owner: Order) {{ q: Z; }} law required l(): forall x: Order.Line . x.q >= 0; }}"
    );
    ok(&order);
    let nested = format!(
        "{HEADER}reading A {{ data B = Leaf | Node(B); }} reading R {{ data A = Only; law required k(): forall x: A.B . x = x; }}"
    );
    let c = ok(&nested);
    let k = c.infos.iter().find(|i| i.name == "R.k").unwrap();
    assert!(k.dependencies.contains(&"A.B".to_owned()));
    // 域が List/Set になる区切りがない量化は拒否する。
    let issue = err(&reading(
        "entity S { n: Z; } law required l(s: S): forall x in s.n . x = 1;",
    ));
    assert_eq!(issue.code, Code::Type);
}
