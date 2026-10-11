use archsig::{canonical, law};
use serde_json::json;
const RESERVATIONS: &[u8] = include_bytes!("fixtures/reservations.law");
const ENGINE: &[u8] = include_bytes!("fixtures/engine.law");
#[test]
fn normative_manifest_bindings() {
    for (source, expected) in [
        (
            ENGINE,
            "sha256:e7e9c16c66de4d4d6d7143af7c9f88a6ef29f0d7510e4bc844b37eb406a8da27",
        ),
        (
            RESERVATIONS,
            "sha256:ede3c701fddea98a6ebf3d31406a0d684dc01256e3ee14a0fb151250b5f05ea1",
        ),
    ] {
        let p = law::check(source).unwrap();
        assert_eq!(p.vocabularies[0]["digest"], expected);
    }
}
#[test]
fn canonical_control_characters_and_unicode() {
    let v = json!({"é":"e\u{301}\n\t\u{0}\"\\/","a":true});
    assert_eq!(
        canonical::bytes(&v),
        b"{\"a\":true,\"\xc3\xa9\":\"e\xcc\x81\\u000a\\u0009\\u0000\\\"\\\\/\"}"
    );
    assert_eq!(
        canonical::model_digest(&v),
        "sha256:544f8744b459443134036c2e7c36ebe388a861d00ecb59a9ef960c623c5760ac"
    );
}
#[test]
fn source_locations_are_real() {
    let p = law::check(ENGINE).unwrap();
    for d in &p.declarations {
        let span = d["location"]["span"].as_array().unwrap();
        let (a, b) = (
            span[0].as_u64().unwrap() as usize,
            span[1].as_u64().unwrap() as usize,
        );
        assert!(a < b && b <= ENGINE.len());
        assert!(std::str::from_utf8(&ENGINE[a..b]).is_ok());
    }
}
fn check(body: &str) -> archsig::model::Checked<law::Program> {
    law::check(
        format!("law \"archsig.law/1\" semantics \"archsig/0.6.0\"; reading R {{ {body} }}")
            .as_bytes(),
    )
}
#[test]
fn valid_expression_and_type_surface() {
    for source in [
        "entity E { u: Unit; b: Bool; z: Z; q: Q; p: Fp(7); t: Text; tuple: (Z,Bool); listvalue: List<Z>; setvalue: Set<Bool>; optional: Option<Z>; term: Term<(Z)->Z>; }", // reserved field is replaced below
        "entity E; view f(x:Z): Z = let y = x * x in y + 1; law required all(): forall z:Z . f(z) >= 0;",
        "entity E; view f(): Set<Z> = set {x + 1 | x in list<Z>[1,2] where x > 0};",
        "entity E; view f(): Term<(Z)->Z> = fn(x:Z) => x * x; view g(): Z = f()(3);",
        "entity Root; entity State(owner:Root) { x:Z; } arrow Step(owner:Root,from:State[owner],to:State[owner]); view walk(e:Step): Option<Path<State,State>> = some(path(e)); relation refl(e:Step): then(identity(e.from),path(e)) = path(e);",
        "data Tree = Leaf | Branch(List<Tree>); entity E { tree:Tree; }",
        "view f(): Q = rat(-2,3); view g(): Fp(7) = 4; view t(): (Q,Q) = (1,2);",
        "view f(): Z = sum(list<Z>[]); view g(): Bool = none<Z> = none<Z>;",
    ] {
        let source = source.replace("optional:", "optionvalue:");
        check(&source).unwrap_or_else(|e| panic!("{source}: {e:?}"));
    }
}
#[test]
fn rejects_unused_invalid_declarations_and_branches() {
    for source in [
        "view f(x:Z):Z = if true then x else false;",
        "view f(x:Z):Z = let x = 1 in x;",
        "view f(x:Z):Term<(Z)->Z> = fn(y:Z) => x + y;",
        "data D = Loop(D);",
        "data D = A | Loop(Set<D>);",
        "data A = A0 | ToB(B); data B = B0 | ToA(A);",
        "view f():Z=g(); view g():Z=f();",
        "data D=A|B; view f(d:D):Z=match d { A=>0; };",
        "data D=A|B; view f(d:D):Z=match d { A=>0; A=>1; B=>2; };",
        "data D=A|Next(D); view f(d:D):Z=match d { A=>0; Next(x)=>f(d); };",
        "entity E { xs:Set<Term<(Z)->Z>>; }",
        "entity E { p:Path<E,E>; }",
        "entity E; view f(e:E):Z = e.unknown;",
        "entity E; law required f():Bool;",
        "view f():Fp(4)=0;",
        "view f():Fp(7)=7;",
        "view f():Z=1<2<3;",
        "entity E { x:Z; } view f(e:E):E=e with{x=0};",
        "entity E; change f(e:E,other:E)=e with{};",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
}
#[test]
fn comments_and_whitespace_only_change_byte_digest() {
    let changed = std::str::from_utf8(ENGINE)
        .unwrap()
        .replace("reading Engine", "// 語彙\nreading   Engine");
    let a = law::check(ENGINE).unwrap();
    let b = law::check(changed.as_bytes()).unwrap();
    assert_ne!(
        canonical::digest(ENGINE),
        canonical::digest(changed.as_bytes())
    );
    assert_eq!(a.model_digest, b.model_digest);
    assert_eq!(a.vocabularies, b.vocabularies);
}
#[test]
fn explicit_guard_retains_original_location_and_binding() {
    let short = std::str::from_utf8(RESERVATIONS).unwrap();
    let explicit = short.replace(
        "conserved(e: Reserve):",
        "conserved(e: Reservations.Reserve) when true:",
    );
    let a = law::check(RESERVATIONS).unwrap();
    let b = law::check(explicit.as_bytes()).unwrap();
    assert_eq!(a.vocabularies, b.vocabularies);
    let find = |p: &law::Program| {
        p.declarations
            .iter()
            .find(|d| d["name"] == "Reservations.conserved")
            .unwrap()
            .clone()
    };
    let (a, b) = (find(&a), find(&b));
    assert_eq!(a["parameters"], b["parameters"]);
    assert_eq!(a["resolution"]["expressions"][0]["type"], "Bool");
    assert_eq!(a["resolution"]["supplied"][0]["rule"], "guard_true");
    assert!(b["resolution"]["supplied"].as_array().unwrap().is_empty());
    assert_eq!(b["resolution"]["expressions"][0]["kind"], "guard");
}
#[test]
fn aliases_and_explicit_alignments() {
    let source=b"law \"archsig.law/1\" semantics \"archsig/0.6.0\"; reading Base { entity Root; entity State(owner:Root){x:Z;} } reading R { use Base as B; entity Root; entity Point(owner:Root){y:Z;} correspondence M(from:B.Root,to:Root){ points:Map<B.State[from],Point[to]>; align B.State.owner=Point.owner; align B.State.x=Point.y; } view f(owner:Z):Z=owner; }";
    let p = law::check(source).unwrap();
    assert_eq!(p.vocabularies.len(), 2);
    let manifest = &p.vocabularies[1]["manifest"];
    let m = manifest["declarations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["name"] == "R.M")
        .unwrap();
    assert_eq!(
        m["alignments"],
        json!([{"source":"Base.State.owner","target":"R.Point.owner"},{"source":"Base.State.x","target":"R.Point.y"}])
    );
    assert!(law::check(&source.iter().copied().collect::<Vec<_>>()).is_ok());
}
#[test]
fn fixed_canonical_digest() {
    // SHA-256 of the canonical bytes below, independent of serialized implementation output.
    assert_eq!(
        canonical::model_digest(&json!({"b":2,"a":1})),
        "sha256:43258cff783fe7036d8a43033f830adfc60ec037382473548ac742b888292777"
    );
}
#[test]
fn unknown_versions_precede_unknown_declarations() {
    let e =
        law::check(b"law \"future/2\" semantics \"archsig/0.7.0\"; future Something;").unwrap_err();
    assert_eq!(e.code, "unsupported_version");
}
#[test]
fn failure_spans_preserve_bytes() {
    for source in [
        b"\xef\xbb\xbf".as_slice(),
        b"\xff",
        b"law \"\\ud800\" semantics \"archsig/0.6.0\"; reading R {}",
    ] {
        assert_eq!(law::check(source).unwrap_err().code, "syntax");
    }
}
#[test]
fn declaration_metadata_and_default_rules() {
    let p = law::check(ENGINE).unwrap();
    let ctor = p
        .declarations
        .iter()
        .find(|d| d["name"] == "Engine.Expr.Add")
        .unwrap();
    assert_eq!(
        ctor["parameters"],
        json!([{"name":"arg0","type":["Data","Engine.Expr"]},{"name":"arg1","type":["Data","Engine.Expr"]}])
    );
    let p = check("entity E;").unwrap();
    assert_eq!(
        p.declarations[0]["resolution"]["supplied"][0]["rule"],
        "local_support"
    );
    let p = law::check(RESERVATIONS).unwrap();
    let m = p
        .declarations
        .iter()
        .find(|d| d["name"] == "Reservations.Migration")
        .unwrap();
    assert_eq!(
        m["resolution"]["supplied"][0]["rule"],
        "same_name_alignment"
    );
    assert_eq!(
        m["resolution"]["supplied"][0]["pairs"]
            .as_array()
            .unwrap()
            .len(),
        6
    );
    let reading = p
        .declarations
        .iter()
        .find(|d| d["name"] == "Reservations")
        .unwrap();
    assert_eq!(
        reading["resolution"]["supplied"][0]["rule"],
        "local_declared"
    );
}
#[test]
fn changing_conditions_keeps_primitive_vocabulary() {
    let changed = std::str::from_utf8(RESERVATIONS).unwrap().replace(
        "= e.from.free + e.from.held",
        "= e.from.free + e.from.held + 1",
    );
    let a = law::check(RESERVATIONS).unwrap();
    let b = law::check(changed.as_bytes()).unwrap();
    assert_eq!(a.vocabularies, b.vocabularies);
    assert_ne!(a.model_digest, b.model_digest);
}
#[test]
fn cross_reading_cycles_and_name_collisions_are_rejected() {
    for source in [
        "reading A { use B as Other; } reading B { use A as Other; }",
        "reading A { entity E; } reading B { use A as E; entity E; }",
        "reading A { entity E; entity E; }",
        "reading A { entity Root; entity State(owner:Root){x:Z;} correspondence M(from:Root,to:Root){} }",
        "reading A { entity E { a:Z; b:List<E[a]>; } }",
    ] {
        let s = format!("law \"archsig.law/1\" semantics \"archsig/0.6.0\"; {source}");
        assert!(law::check(s.as_bytes()).is_err(), "{source}");
    }
}
