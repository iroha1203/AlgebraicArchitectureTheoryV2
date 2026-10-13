//! AC2: DSL 全体の検査。両規範例、全構文の正例、各種の負例。

mod common;
use archsig::issue::Code;
use archsig::types::Type;
use common::law_definitions::*;
use common::*;

#[test]
fn normative_examples_pass_and_bind_their_vocabulary() {
    let r = ok(RESERVATIONS_DEFINITION, RESERVATIONS);
    assert_eq!(r.definitions.vocabularies.len(), 1);
    assert_eq!(
        r.definitions.vocabularies["Reservations"].digest,
        "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff"
    );
    let e = ok(ENGINE_DEFINITION, ENGINE);
    assert_eq!(
        e.definitions.vocabularies["Engine"].digest,
        "sha256:5c45e2e06c365a98e8d85aa0046ef16d0da903644cecc7f3e3a4dadb87a84d4c"
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
const WIDE: &str = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Base {
use vocabulary Base version "1" digest "sha256:e6a239ba843b42cb4d6aeb611af0407434eb92c60929390fb62289161040ecfc";
view q(i: Item): Q = i.price + rat(1, 2) * -rat(3, 4);
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
use vocabulary Paths version "1" digest "sha256:36473a82447ef032aeda77b9e55941723fcd8c46c29a02efcce7aae91d2108ee";
view loop(s: St): Path<St, St> = identity(s);
  view ends(a: Step): Option<Path<St, St>> = some(path(a));
  view walk(a: Step, b: Step): Path<St, St> = then(path(a), path(b));
  relation swap(a: Step, b: Step) when target(path(a)) = source(path(b)):
    then(path(a), path(b)) = then(path(b), path(a));
}
reading Port {
use vocabulary Base version "1" digest "sha256:e6a239ba843b42cb4d6aeb611af0407434eb92c60929390fb62289161040ecfc";
use vocabulary Port version "1" digest "sha256:d2edb18a2ab6d18acd6a54e0ac23ed6b3349099beb9440698f1796484f79d1eb";
use Base as B;





  view total(s: Base.Sys): Z = sum(set{ i.qty | i in Base.Item[s] });
  law optional direct(i: Base.Item): i.qty = i.qty;
view alias(i: Base.Item): Q = B.q(i);
}
"#;

#[test]
fn every_construct_type_checks() {
    let c = ok(WIDE_DEFINITION, WIDE);
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
    let port = &c.definitions.vocabularies["Port"];
    let text = port.manifest.canonical();
    assert!(text.contains(r#""source":"Port.Acc.bal","target":"Port.Ledger.total""#));
    let base = &c.definitions.vocabularies["Base"];
    assert!(base.manifest.canonical().contains(r#""alignments":[]"#));
}

fn rejects(definition: &str, body: &str, code: Code) {
    let src = reading(body);
    let issue = err(definition, &src);
    assert_eq!(issue.code, code, "{body}\n=> {:?}", issue);
    let archsig::issue::Location::Law { span } = issue.location else {
        panic!("Law の位置")
    };
    assert!(span.1 <= src.len() && span.0 <= span.1, "{span:?}");
}

#[test]
fn name_collisions_are_rejected() {
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view v(i: Item, i: Item): Z = 0;"#,
        Code::DuplicateId,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view v(i: Item): Z = let i = 1 in i;"#,
        Code::DuplicateId,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view v(i: Item): Z = let a = 1 in let a = 2 in a;"#,
        Code::DuplicateId,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
law required l(i: Item): forall i: Z . i = i;"#,
        Code::DuplicateId,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view count(): Z = 0;"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(sum: Z): Z = sum;"#,
        Code::Syntax,
    );
    let two = format!("{HEADER}reading A {{ use B as X; view X(): Z = 0; }} reading B {{ }}");
    assert_eq!(err(EMPTY_DEFINITION, &two).code, Code::DuplicateId);
}

/// 仕様が別の scope とする名前は重なってよい。`.` 列は候補の最長一致で解決する。
#[test]
fn names_in_different_scopes_may_coincide() {
    let c = ok(
        DEF_48,
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading R {
use vocabulary R version "1" digest "sha256:cd820d457df3188c76cc5ff7294ffac9c304673048c2c3642d7759cf2718fc05";
view v(r: R): Z = r.x; view w(r: R.R): D = sum; view m(n: Z): Z = match n { _ => 0; }; view k(d: D): Z = match d { sum => 0; path(z) => z; };
}
reading count {
use vocabulary R version "1" digest "sha256:cd820d457df3188c76cc5ff7294ffac9c304673048c2c3642d7759cf2718fc05";
use vocabulary count version "1" digest "sha256:e73dea95163bedd38e8e4bb397fa5755a0d70c3ac58515975788eeebe1b0ea66";
use R as target; view u(r: R.R): Z = target.v(r);
}
"#,
    );
    assert!(c.definitions.declarations.contains_key("R.R"));
    assert!(c.infos.iter().any(|i| i.name == "count.u"));
    // 移設した arrow の owner・from・to は定義に保持する。
    ok(
        DEF_27,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:52c8a421955952bd1a52f1b6275692455900337b0acbe112fccd81c691eacd6d";
"#,
        ),
    );
}

/// 変数名と衝突する constructor の短名は、pattern でも修飾して書く。
#[test]
fn constructor_short_names_colliding_with_variables_are_qualified() {
    rejects(
        DEF_06,
        r#"use vocabulary R version "1" digest "sha256:c255627d975d859b823949ecba2cb6f731b2cbd74e31de5d370916f1f5c07f24";
view v(D0: Z, d: D): Z = match d { D0 => D0; _ => 1; };"#,
        Code::Syntax,
    );
    rejects(
        DEF_07,
        r#"use vocabulary R version "1" digest "sha256:dd35e0b7430b831c606c9d0fd259ea5c3d869fed09e5629f61b99c9178f0844a";
view v(D0: Z, d: D): Z = match d { D0(n) => n; _ => 1; };"#,
        Code::Syntax,
    );
    ok(
        DEF_06,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:c255627d975d859b823949ecba2cb6f731b2cbd74e31de5d370916f1f5c07f24";
view v(D0: Z, d: D): Z = match d { D.D0 => D0; _ => 1; };"#,
        ),
    );
}

#[test]
fn change_needs_an_entity_as_its_first_parameter() {
    ok(
        DEF_08,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c(a: A) = (a) with { x = 1 };"#,
        ),
    );
    ok(
        DEF_08,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c(a: A, d: Z) = if d > 0 then a with { x = d } else a with { x = 0 };
         change e(a: A, d: Z) when d != 0 = let n = d + 1 in a with { x = n };
         change f(a: A, d: Z) when d > 0 = if d = 1 then a with { x = 1 } else (a with { x = 2 });"#,
        ),
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c(a: A, d: Z) = if d > 0 then a with { x = 1 } else a;"#,
        Code::Syntax,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c() = a with { x = 1 };"#,
        Code::Syntax,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c() when true = a with { x = 1 };"#,
        Code::Syntax,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c(n: Z) = n with { x = 1 };"#,
        Code::Syntax,
    );
}

#[test]
fn nested_patterns_over_single_constructors_cover_their_branch() {
    ok(
        DEF_28,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:f547b9c69a989640fd643a962496f1ade0958571e51ce32e3dca557e8b741580";
view f(w: W): Z = match w { W0(U0) => 1; };"#,
        ),
    );
    ok(
        DEF_29,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:e7ac4e678e09a39fe7302f33fdcba09aee1c61122d0200213b06aa4d038bc388";
view f(w: W): Z = match w { W0(U0(a, b)) => a; W1 => 0; };"#,
        ),
    );
    rejects(
        DEF_09,
        r#"use vocabulary R version "1" digest "sha256:883c258627c1e1a0abacc9b148ccff90d21eab1e5de236e4e0b534e6979cd2a9";
view f(w: W): Z = match w { W0(U0) => 1; };"#,
        Code::Syntax,
    );
    ok(
        DEF_09,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:883c258627c1e1a0abacc9b148ccff90d21eab1e5de236e4e0b534e6979cd2a9";
view f(w: W): Z = match w { W0(U0) => 1; _ => 0; };"#,
        ),
    );
    // 入れ子の pattern で覆っていても、末尾の `_` は受ける。
    ok(
        DEF_28,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:f547b9c69a989640fd643a962496f1ade0958571e51ce32e3dca557e8b741580";
view f(w: W): Z = match w { W0(U0) => 1; _ => 0; };"#,
        ),
    );
    rejects(
        DEF_10,
        r#"use vocabulary R version "1" digest "sha256:09f6cbf9f745c9e6283cc513971483e3c3a69ecebe9bbb49c9cf6062485cf303";
view f(w: W): Z = match w { W0(n) => n; _ => 0; };"#,
        Code::Syntax,
    );
}

#[test]
fn cycles_are_rejected() {
    let mutual = format!("{HEADER}reading A {{ use B as Y; }} reading B {{ use A as X; }}");
    assert_eq!(err(EMPTY_DEFINITION, &mutual).code, Code::Cycle);
    let direct = format!(
        "{HEADER}reading A {{ view a(): Z = B.b(); }} reading B {{ view b(): Z = A.a(); }}"
    );
    assert_eq!(err(EMPTY_DEFINITION, &direct).code, Code::Cycle);
    let own = format!("{HEADER}reading A {{ use A as Me; }}");
    assert_eq!(err(EMPTY_DEFINITION, &own).code, Code::Cycle);
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view a(x: Z): Z = b(x); view b(x: Z): Z = a(x);"#,
        Code::Cycle,
    );
}

#[test]
fn type_mismatches_are_rejected() {
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
law required l(i: Item): i.qty = "x";"#,
        Code::Type,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Z = true;"#,
        Code::Type,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view v(i: Item): Z = i.tag;"#,
        Code::Type,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Q = rat(1, 2) + 1 < 2;"#,
        Code::Type,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Q = rat(-3, 4);"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Q = rat((3), 4);"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(x: Z): Q = rat(x, 4);"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Q = rat(3, 0);"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(x: Fp(5)): Bool = x < x;"#,
        Code::Type,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view v(t: Tree): Z = match t { Leaf => 0; Node(a, b) => true; };"#,
        Code::Type,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Fp(5) = 5;"#,
        Code::Syntax,
    );
    rejects(
        DEF_12,
        r#"use vocabulary R version "1" digest "sha256:8eeae677bb3c10680172d98822b46fd1a4d96168743146b6ba7ab03327c43f2f";
view w(e: E, f: F): Path<A, B> = then(path(e), path(f));"#,
        Code::Type,
    );
}

#[test]
fn invalid_recursion_is_rejected() {
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view f(n: Z): Z = f(n);"#,
        Code::Cycle,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view g(t: Tree): Z = g(t);"#,
        Code::Cycle,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view g(t: Tree): Z = match t { Leaf => 0; Node(a, b) => match a { Leaf => 0; Node(c, d) => g(c); }; };"#,
        Code::Cycle,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view g(n: Z, t: Tree): Z = match t { Leaf => n; Node(a, b) => g(n, Node(a, b)); };"#,
        Code::Cycle,
    );
}

#[test]
fn capture_and_impure_terms_are_rejected() {
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view c(x: Z): Term<(Z) -> Z> = fn(y: Z) => x + y;"#,
        Code::Reference,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view c(): Term<(Item) -> Z> = fn(i: Item) => i.qty;"#,
        Code::Syntax,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view h(): Z = 0; view c(): Term<(Z) -> Z> = fn(y: Z) => h();"#,
        Code::Reference,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view c(): Term<(Z) -> Term<(Z) -> Z>> = fn(y: Z) => fn(z: Z) => y;"#,
        Code::Reference,
    );
    rejects(
        DEF_03,
        r#"use vocabulary R version "1" digest "sha256:8b3d6fe0b9d32c10cb3b500b3ea95bf03f2e586ba558f6ca069ef11c76aacae6";
view c(s: Sys): Term<(Z) -> Z> = fn(y: Z) => count(Item[s]);"#,
        Code::Reference,
    );
}

#[test]
fn types_in_invalid_positions_are_rejected() {
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view s(): Set<Term<(Z) -> Z>> = set<Term<(Z) -> Z>>{};"#,
        Code::Syntax,
    );
    rejects(
        DEF_18,
        r#"use vocabulary R version "1" digest "sha256:6f950c5ef9a13531ece68725bcd2f0315e1fd8937e7e2a1f883a9bf3b94aba54";
view s(): Set<T> = set<T>{};"#,
        Code::Syntax,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c(a: A, b: A) = a with { x = 1 };"#,
        Code::Syntax,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c(a: A, b: Option<A>) = a with { x = 1 };"#,
        Code::Syntax,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
view v(a: A): A = a with { x = 1 };"#,
        Code::Syntax,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
change c(a: A) = a with { owner = a.owner };"#,
        Code::Syntax,
    );
    rejects(
        DEF_23,
        r#"use vocabulary R version "1" digest "sha256:25e9f01bef8ffe1efcdf7ed71084a333af41dcd9f4f34639fd227b87e1892388";
change c(m: M) = m with { k = 1 };"#,
        Code::Syntax,
    );
}

#[test]
fn non_affine_and_infinite_laws_type_check_without_algorithms() {
    let c = ok(
        DEF_30,
        &reading(
            r#"use vocabulary R version "1" digest "sha256:ad41743d0ff47e1f20c34047ac0d7314644262bdfb88e483d1a4eb4eeda7e099";
law required cubic(a: A): a.x * a.x * a.x = a.x;
         law optional all(a: A): forall n: Z . forall m: Z . n * m * a.x = m * n * a.x;
         law optional rational(a: A): exists r: Q . r * r = a.y;"#,
        ),
    );
    assert_eq!(c.infos.iter().filter(|i| i.kind == "law").count(), 3);
}

#[test]
fn empty_families_do_not_skip_type_checking() {
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
law required l(s: S): forall a in A[s] . a.x = true;"#,
        Code::Type,
    );
    rejects(
        DEF_08,
        r#"use vocabulary R version "1" digest "sha256:cfc86fe1f3a8c1cfa269bd0706696a31909f583b350f1fe953a34952802c0dbb";
law required l(s: S): exists a in A[s] . a.missing = 0;"#,
        Code::Reference,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
law required l(): forall x in list<Z>[] . x = "s";"#,
        Code::Type,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
law optional unused(): if true then true else 1 = "one";"#,
        Code::Type,
    );
    rejects(
        DEF_24,
        r#"use vocabulary R version "1" digest "sha256:19f7f3bb9efe12d46eeaecbf989c03ccddf8f16c3addf6a627be4372dec8b7be";
view v(d: D): Z = match d { D0 => 0; D1(n) => n + true; };"#,
        Code::Type,
    );
}

#[test]
fn malformed_syntax_is_rejected() {
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(x: Z): Bool = 1 < x < 2;"#,
        Code::Syntax,
    );
    rejects(
        DEF_25,
        r#"use vocabulary R version "1" digest "sha256:48493aff068490823c9f6433b51bff4c61010a323fc2128bf288e94f7f35812a";
view v(s: S): Set<A> = (A)[s];"#,
        Code::Syntax,
    );
    rejects(
        DEF_06,
        r#"use vocabulary R version "1" digest "sha256:c255627d975d859b823949ecba2cb6f731b2cbd74e31de5d370916f1f5c07f24";
view v(d: D): Z = match d { D0 => 0; };"#,
        Code::Syntax,
    );
    rejects(
        DEF_06,
        r#"use vocabulary R version "1" digest "sha256:c255627d975d859b823949ecba2cb6f731b2cbd74e31de5d370916f1f5c07f24";
view v(d: D): Z = match d { _ => 0; D0 => 1; };"#,
        Code::Syntax,
    );
    rejects(
        DEF_06,
        r#"use vocabulary R version "1" digest "sha256:c255627d975d859b823949ecba2cb6f731b2cbd74e31de5d370916f1f5c07f24";
view v(d: D): Z = match d { D0 => 0; D1 => 1; _ => 2; };"#,
        Code::Syntax,
    );
    rejects(
        DEF_06,
        r#"use vocabulary R version "1" digest "sha256:c255627d975d859b823949ecba2cb6f731b2cbd74e31de5d370916f1f5c07f24";
view v(d: D): Z = match d { D0 => 0; D0 => 1; _ => 2; };"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Z = (then);"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Z = 01;"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Text = "a";"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Text = "\ud800";"#,
        Code::Syntax,
    );
    rejects(
        DEF_04,
        r#"use vocabulary R version "1" digest "sha256:77f55ae72a0d8d023c0aa5ed4ea09caaf02ae3c7edccc90610e3fe537d727d39";
view v(): Z = unknown;"#,
        Code::Reference,
    );
}
