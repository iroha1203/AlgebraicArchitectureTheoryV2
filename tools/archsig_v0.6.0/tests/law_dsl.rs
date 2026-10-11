//! AC2: DSL 全体の検査。両規範例、全構文の正例、各種の負例。

mod common;
use archsig::issue::Code;
use archsig::types::Type;
use common::*;

#[test]
fn normative_examples_pass_and_bind_their_vocabulary() {
    let r = ok(RESERVATIONS);
    assert_eq!(r.vocabularies.len(), 1);
    assert_eq!(
        r.vocabularies[0].digest,
        "sha256:ede3c701fddea98a6ebf3d31406a0d684dc01256e3ee14a0fb151250b5f05ea1"
    );
    let e = ok(ENGINE);
    assert_eq!(
        e.vocabularies[0].digest,
        "sha256:e7e9c16c66de4d4d6d7143af7c9f88a6ef29f0d7510e4bc844b37eb406a8da27"
    );
    // 構造再帰の view と、非アフィンな全整数量化の law を受理する。
    let preserves = e
        .infos
        .iter()
        .find(|i| i.name == "Engine.preserves")
        .unwrap();
    assert_eq!(preserves.expressions[0].ty, Type::Bool);
    let translate = e
        .infos
        .iter()
        .find(|i| i.name == "Engine.translate")
        .unwrap();
    assert!(
        translate
            .dependencies
            .contains(&"Engine.translate".to_owned())
    );
}

/// use/alias、align、relation/Path、Term、全 container・数値型を一つの Law で使う。
const WIDE: &str = r#"law "archsig.law/1" semantics "archsig/0.6.0";
reading Base {
  entity Sys;
  data Kind = Small | Large(Z);
  data Tree = Leaf | Node(Tree, List<Tree>, Option<Tree>, (Tree, Z));
  entity Item(owner: Sys) {
    qty: Z; price: Q; tag: Text; flag: Bool; nothing: Unit; residue: Fp(7);
    tags: List<Text>; ids: Set<Z>; maybe: Option<Z>; pair: (Z, Q);
    code: Term<(Z, Z) -> Z>; kind: Kind; tree: Tree; peers: Set<Item>; next: Option<Item[owner]>;
  }
  arrow Move(owner: Sys, from: Item[owner], to: Item[owner]) { cost: Z; }
  correspondence Same(from: Sys, to: Sys) {
    items: Map<Item[from], Item[to]>;
    moves: Map<Move[from], Move[to]>;
  }
  view q(i: Item): Q = i.price + rat(1, 2) * rat(-3, 4);
  view f(i: Item): Fp(7) = i.residue * 3 + 6 - i.residue;
  view apply(i: Item, x: Z): Z = i.code(x, 1);
  view square(): Term<(Z) -> Z> = fn(y: Z) => y * y + 1;
  view counts(i: Item): (Z, Z) = (count(i.tags), sum(i.ids));
  view doubled(i: Item): Set<Z> = set{ x * 2 | x in i.ids where x > 0 };
  view options(): List<Option<Z>> = list<Option<Z>>[none<Z>, some(1)];
  view pairs(): Set<(Z, Text)> = set<(Z, Text)>{(1, "a"), (2, "b")};
  view tagged(i: Item): Bool = "x" in i.tags and i.flag;
  view members(s: Sys): Z = count(Item[s]);
  view size(t: Tree): Z = match t { Leaf => 0; Node(l, cs, o, p) => size(l) + count(cs) + p.1; };
  view kindv(i: Item): Z = match i.kind { Small => 0; Large(n) => n; };
  view lets(i: Item): Z = let a = i.qty in let b = a * a in if b > 10 then b else a;
  view first(i: Item): Z = i.pair.0;
  view unitv(i: Item): Unit = i.nothing;
  law required nonaffine(x: Z): x * x >= 0;
  law optional infinite(i: Item): forall x: Z . exists y: Z . y = x * i.qty;
  law optional ordered(i: Item) when i.flag: i.price < rat(5, 1) implies not (i.qty <= 0);
  local Qty(i: Item) when i.flag reads i.qty, i.pair.1;
  change bump(i: Item, d: Z, k: Kind) when d != 0 = i with { qty = i.qty + d, kind = k };
}
reading Paths {
  entity Sys;
  entity St(owner: Sys) { v: Z; }
  arrow Step(owner: Sys, from: St[owner], to: St[owner]);
  view loop(s: St): Path<St, St> = identity(s);
  view ends(a: Step): Option<Path<St, St>> = some(path(a));
  view walk(a: Step, b: Step): Path<St, St> = then(path(a), path(b));
  relation swap(a: Step, b: Step) when target(path(a)) = source(path(b)):
    then(path(a), path(b)) = then(path(b), path(a));
}
reading Port {
  use Base as B;
  entity Sys2;
  entity Acc(owner: Sys2) { bal: Z; }
  entity Root3;
  entity Ledger(owner: Root3) { total: Z; }
  correspondence Move(from: Sys2, to: Root3) {
    accs: Map<Acc[from], Ledger[to]>;
    align Acc.owner = Ledger.owner;
    align Acc.bal = Ledger.total;
  }
  view total(s: B.Sys): Z = sum(set{ i.qty | i in B.Item[s] });
  law optional direct(i: Base.Item): i.qty = i.qty;
}
"#;

#[test]
fn every_construct_type_checks() {
    let c = ok(WIDE);
    let info = |n: &str| {
        c.infos
            .iter()
            .find(|i| i.name == n)
            .unwrap_or_else(|| panic!("{n}"))
    };
    assert_eq!(info("Base.q").returns, Some(Type::Q));
    assert_eq!(info("Base.f").returns, Some(Type::Fp("7".into())));
    assert_eq!(
        info("Paths.ends").returns,
        Some(Type::Option(Box::new(Type::Path(
            "Paths.St".into(),
            "Paths.St".into()
        ))))
    );
    let swap = info("Paths.swap");
    let kinds: Vec<_> = swap
        .expressions
        .iter()
        .map(|e| format!("{:?}", e.kind))
        .collect();
    assert_eq!(kinds, ["Guard", "RelationLeft", "RelationRight"]);
    // 別名による参照は use の参照先へ解決し、reading の依存に残る。
    assert_eq!(info("Port").dependencies, ["Base"]);
    assert!(
        info("Port.total")
            .dependencies
            .contains(&"Base.Item".to_owned())
    );
    // 明記した align は manifest に入り、暗黙の同名対応は入らない。
    let port = c.vocabularies.iter().find(|v| v.reading == "Port").unwrap();
    let text = port.manifest.canonical();
    assert!(text.contains(r#"{"source":"Port.Acc.bal","target":"Port.Ledger.total"}"#));
    let base = c.vocabularies.iter().find(|v| v.reading == "Base").unwrap();
    assert!(base.manifest.canonical().contains(r#""alignments":[]"#));
}

fn rejects(body: &str, code: Code) {
    let src = reading(body);
    let issue = err(&src);
    assert_eq!(issue.code, code, "{body}\n=> {:?}", issue);
    let archsig::issue::Location::Law { span } = issue.location;
    assert!(span.1 <= src.len() && span.0 <= span.1, "{span:?}");
}

const ITEM: &str = "entity Sys; entity Item(owner: Sys) { qty: Z; tag: Text; } data Tree = Leaf | Node(Tree, Tree);";

#[test]
fn name_collisions_are_rejected() {
    rejects("entity A; entity A;", Code::DuplicateId);
    rejects("entity A { x: Z; x: Z; }", Code::DuplicateId);
    rejects("data D = C | C;", Code::DuplicateId);
    rejects(
        &format!("{ITEM} view v(i: Item, i: Item): Z = 0;"),
        Code::DuplicateId,
    );
    rejects(
        &format!("{ITEM} view v(i: Item): Z = let i = 1 in i;"),
        Code::DuplicateId,
    );
    rejects(
        &format!("{ITEM} view v(i: Item): Z = let a = 1 in let a = 2 in a;"),
        Code::DuplicateId,
    );
    rejects(
        &format!("{ITEM} law required l(i: Item): forall i: Z . i = i;"),
        Code::DuplicateId,
    );
    rejects("view count(): Z = 0;", Code::Syntax);
    rejects("view v(sum: Z): Z = sum;", Code::Syntax);
    rejects("entity then;", Code::Syntax);
    let two = format!("{HEADER}reading A {{ use B as X; entity X; }} reading B {{ entity S; }}");
    assert_eq!(err(&two).code, Code::DuplicateId);
}

/// 仕様が別の scope とする名前は重なってよい。`.` 列は候補の最長一致で解決する。
#[test]
fn names_in_different_scopes_may_coincide() {
    let c = ok(&format!(
        "{HEADER}reading R {{ entity R {{ x: Z; }} data D = sum | path(Z); view v(r: R): Z = r.x; view w(r: R.R): D = sum; \
         view m(n: Z): Z = match n {{ _ => 0; }}; view k(d: D): Z = match d {{ sum => 0; path(z) => z; }}; }}\n\
         reading count {{ use R as target; view u(r: target.R): Z = R.v(r); }}"
    ));
    assert!(c.infos.iter().any(|i| i.name == "R.R"));
    assert!(c.infos.iter().any(|i| i.name == "count.u"));
    // arrow の owner・from・to は body に置いてもよい。
    ok(&reading(
        "entity S; entity A(owner: S); arrow M(owner: S) { from: A[owner]; to: A[owner]; }",
    ));
}

#[test]
fn cycles_are_rejected() {
    let mutual = format!(
        "{HEADER}reading A {{ use B as Y; entity S; }} reading B {{ use A as X; entity T; }}"
    );
    assert_eq!(err(&mutual).code, Code::Cycle);
    let direct = format!(
        "{HEADER}reading A {{ view a(): Z = B.b(); }} reading B {{ view b(): Z = A.a(); }}"
    );
    assert_eq!(err(&direct).code, Code::Cycle);
    let own = format!("{HEADER}reading A {{ use A as Me; entity S; }}");
    assert_eq!(err(&own).code, Code::Cycle);
    rejects("data A = A0 | A1(B); data B = B0 | B1(A);", Code::Cycle);
    rejects(
        "view a(x: Z): Z = b(x); view b(x: Z): Z = a(x);",
        Code::Cycle,
    );
}

#[test]
fn type_mismatches_are_rejected() {
    rejects(
        &format!("{ITEM} law required l(i: Item): i.qty = \"x\";"),
        Code::Type,
    );
    rejects("view v(): Z = true;", Code::Type);
    rejects(&format!("{ITEM} view v(i: Item): Z = i.tag;"), Code::Type);
    rejects("view v(): Q = rat(1, 2) + 1 < 2;", Code::Type);
    rejects("view v(x: Fp(5)): Bool = x < x;", Code::Type);
    rejects(
        &format!("{ITEM} view v(t: Tree): Z = match t {{ Leaf => 0; Node(a, b) => true; }};"),
        Code::Type,
    );
    rejects("view v(): Fp(5) = 5;", Code::Syntax);
    rejects(
        "entity S; entity A(owner: S); entity B(owner: S); arrow E(owner: S, from: A[owner], to: A[owner]); arrow F(owner: S, from: B[owner], to: B[owner]); view w(e: E, f: F): Path<A, B> = then(path(e), path(f));",
        Code::Type,
    );
}

#[test]
fn invalid_recursion_is_rejected() {
    rejects("view f(n: Z): Z = f(n);", Code::Cycle);
    rejects(&format!("{ITEM} view g(t: Tree): Z = g(t);"), Code::Cycle);
    rejects(
        &format!(
            "{ITEM} view g(t: Tree): Z = match t {{ Leaf => 0; Node(a, b) => match a {{ Leaf => 0; Node(c, d) => g(c); }}; }};"
        ),
        Code::Cycle,
    );
    rejects(
        &format!(
            "{ITEM} view g(n: Z, t: Tree): Z = match t {{ Leaf => n; Node(a, b) => g(n, Node(a, b)); }};"
        ),
        Code::Cycle,
    );
    rejects("data Bad = B0 | B1(Set<Bad>);", Code::Syntax);
    rejects("data Bad = B0 | B1(Term<(Z) -> Bad>);", Code::Syntax);
    rejects("data Empty = E(Empty);", Code::Syntax);
}

#[test]
fn capture_and_impure_terms_are_rejected() {
    rejects(
        "view c(x: Z): Term<(Z) -> Z> = fn(y: Z) => x + y;",
        Code::Reference,
    );
    rejects(
        &format!("{ITEM} view c(): Term<(Item) -> Z> = fn(i: Item) => i.qty;"),
        Code::Syntax,
    );
    rejects(
        &format!("{ITEM} view h(): Z = 0; view c(): Term<(Z) -> Z> = fn(y: Z) => h();"),
        Code::Reference,
    );
    rejects(
        "view c(): Term<(Z) -> Term<(Z) -> Z>> = fn(y: Z) => fn(z: Z) => y;",
        Code::Reference,
    );
    rejects(
        &format!("{ITEM} view c(s: Sys): Term<(Z) -> Z> = fn(y: Z) => count(Item[s]);"),
        Code::Reference,
    );
}

#[test]
fn types_in_invalid_positions_are_rejected() {
    rejects(
        "entity S; entity A(owner: S) { p: Path<A, A>; }",
        Code::Syntax,
    );
    rejects("data D = D0(Path<D, D>);", Code::Syntax);
    rejects(
        "view s(): Set<Term<(Z) -> Z>> = set<Term<(Z) -> Z>>{};",
        Code::Syntax,
    );
    rejects(
        "data T = T0(Term<(Z) -> Z>); view s(): Set<T> = set<T>{};",
        Code::Syntax,
    );
    rejects("entity E { m: Map<Z, Z>; }", Code::Syntax);
    rejects("entity E { x: Fp(4); }", Code::Syntax);
    rejects("entity S; entity E { f: Term<(S) -> Z>; }", Code::Syntax);
    rejects("data D = D0; entity E(o: D) { x: D[o]; }", Code::Syntax);
    rejects(
        "entity S; entity A(owner: S) { x: Z; } change c(a: A, b: A) = a with { x = 1 };",
        Code::Syntax,
    );
    rejects(
        "entity S; entity A(owner: S) { x: Z; } change c(a: A, b: Option<A>) = a with { x = 1 };",
        Code::Syntax,
    );
    rejects(
        "entity S; entity A(owner: S) { x: Z; } view v(a: A): A = a with { x = 1 };",
        Code::Syntax,
    );
    rejects(
        "entity S; entity A(owner: S) { x: Z; } change c(a: A) = a with { owner = a.owner };",
        Code::Syntax,
    );
    rejects(
        "entity S; entity A(owner: S); arrow M(owner: S, from: A[owner], to: A[owner]) { k: Z; } change c(m: M) = m with { k = 1 };",
        Code::Syntax,
    );
}

#[test]
fn non_affine_and_infinite_laws_type_check_without_algorithms() {
    let c = ok(&reading(
        "entity S; entity A(owner: S) { x: Z; y: Q; }
         law required cubic(a: A): a.x * a.x * a.x = a.x;
         law optional all(a: A): forall n: Z . forall m: Z . n * m * a.x = m * n * a.x;
         law optional rational(a: A): exists r: Q . r * r = a.y;",
    ));
    assert_eq!(c.infos.iter().filter(|i| i.kind == "law").count(), 3);
}

#[test]
fn empty_families_do_not_skip_type_checking() {
    rejects(
        "entity S; entity A(owner: S) { x: Z; } law required l(s: S): forall a in A[s] . a.x = true;",
        Code::Type,
    );
    rejects(
        "entity S; entity A(owner: S) { x: Z; } law required l(s: S): exists a in A[s] . a.missing = 0;",
        Code::Reference,
    );
    rejects(
        "law required l(): forall x in list<Z>[] . x = \"s\";",
        Code::Type,
    );
    rejects(
        "law optional unused(): if true then true else 1 = \"one\";",
        Code::Type,
    );
    rejects(
        "data D = D0 | D1(Z); view v(d: D): Z = match d { D0 => 0; D1(n) => n + true; };",
        Code::Type,
    );
}

#[test]
fn malformed_syntax_is_rejected() {
    rejects("view v(x: Z): Bool = 1 < x < 2;", Code::Syntax);
    rejects(
        "entity S; entity A(owner: S); view v(s: S): Set<A> = (A)[s];",
        Code::Syntax,
    );
    rejects(
        "data D = D0 | D1; view v(d: D): Z = match d { D0 => 0; };",
        Code::Syntax,
    );
    rejects(
        "data D = D0 | D1; view v(d: D): Z = match d { _ => 0; D0 => 1; };",
        Code::Syntax,
    );
    rejects(
        "data D = D0 | D1; view v(d: D): Z = match d { D0 => 0; D1 => 1; _ => 2; };",
        Code::Syntax,
    );
    rejects(
        "data D = D0 | D1; view v(d: D): Z = match d { D0 => 0; D0 => 1; _ => 2; };",
        Code::Syntax,
    );
    rejects("view v(): Z = (then);", Code::Syntax);
    rejects("view v(): Z = 01;", Code::Syntax);
    rejects("view v(): Text = \"a\u{1}\";", Code::Syntax);
    rejects("view v(): Text = \"\\ud800\";", Code::Syntax);
    rejects("view v(): Z = unknown;", Code::Reference);
    rejects("entity E { in: Z; }", Code::Syntax);
}

/// correspondence が覆う owned 型は、その reading から参照できる reading の中で決まる。
#[test]
fn correspondence_cover_is_relative_to_its_reading() {
    let src = format!(
        "{HEADER}reading A {{ entity S; entity St(owner: S) {{ v: Z; }} correspondence M(from: S, to: S) {{ sts: Map<St[from], St[to]>; }} }}\n\
         reading B {{ use A as P; entity Extra(owner: P.S) {{ w: Z; }} }}"
    );
    ok(&src);
    let inside = format!(
        "{HEADER}reading A {{ entity S; entity St(owner: S) {{ v: Z; }} entity Extra(owner: S); correspondence M(from: S, to: S) {{ sts: Map<St[from], St[to]>; }} }}"
    );
    assert_eq!(err(&inside).code, Code::Syntax);
}
