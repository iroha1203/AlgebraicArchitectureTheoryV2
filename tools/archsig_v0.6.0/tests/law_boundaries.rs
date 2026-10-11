use archsig::{law, model::Checked};
use serde_json::json;
fn source(body: &str) -> String {
    format!("law \"archsig.law/1\" semantics \"archsig/0.6.0\"; reading R {{ {body} }}")
}
fn check(body: &str) -> Checked<law::Program> {
    law::check(source(body).as_bytes())
}

#[test]
fn strings_keep_their_token_kind_in_every_parser_context() {
    for text in [
        "true", "false", "reading", "(", ")", "in", ".", "fn", "unit", "set",
    ] {
        check(&format!(
            "view f():Text={};",
            serde_json::to_string(text).unwrap()
        ))
        .unwrap();
        check(&format!(
            "view f():Text=let x={} in x;",
            serde_json::to_string(text).unwrap()
        ))
        .unwrap();
    }
    assert!(check("view f():Bool=\"true\";").is_err());
    assert!(
        law::check(b"law \"archsig.law/1\" semantics \"archsig/0.6.0\"; \"reading\" R {entity E;}")
            .is_err()
    );
}
#[test]
fn invalid_family_alignment_and_later_arrow_return_issues_without_panicking() {
    for body in [
        "data D=C; view f():Bool=forall x in D.C[unit] . true;",
        "entity Root; data D=C; correspondence M(from:Root,to:Root){align D.C.foo=D.C.foo;}",
        "entity Root; entity E(owner:Root); view f(e:Bad):Path<E,E> = path(e); arrow Bad(owner:Root);",
    ] {
        assert!(
            std::panic::catch_unwind(|| check(body)).unwrap().is_err(),
            "{body}"
        );
    }
}
#[test]
fn lexical_capture_cannot_become_constructor_resolution() {
    assert!(check("data D=C; view f(C:D):Term<()->D> = fn()=>C;").is_err());
    assert!(check("data D=C(Z); view f(C:Term<(Z)->D>):Term<()->D> = fn()=>C(1);").is_err());
    check("data D=C; view f(C:D):Term<()->D> = fn()=>D.C;").unwrap();
    assert!(check("view f():Term<(Z)->Z> = fn(sum:Z)=>1;").is_err());
}
#[test]
fn pure_terms_reject_reference_domains_and_function_calls() {
    for body in [
        "entity E; view f():Term<()->Bool> = fn()=>forall xs:List<E> . count(xs)=0;",
        "entity E; view f():Term<()->Bool> = fn()=>forall xs:Option<E> . true;",
        "view f():Term<(Term<(Z)->Z>)->Z> = fn(t:Term<(Z)->Z>)=>t(1);",
        "view f():Term<()->Z> = fn()=>(fn(x:Z)=>x)(1);",
    ] {
        assert!(check(body).is_err(), "{body}");
    }
    check("view f():Term<()->Bool> = fn()=>forall xs:List<Z> . count(xs)>=0;").unwrap();
}
#[test]
fn dependent_call_return_uses_actual_owners_simultaneously() {
    let common = "entity Root;entity State(owner:Root);view ident(r:Root,s:State[r]):State[r]=s;";
    check(&format!(
        "{common}view valid(q:Root,s:State[q]):State[q]=ident(q,s);"
    ))
    .unwrap();
    assert!(
        check(&format!(
            "{common}view leak(r:Root,q:Root,s:State[q]):State[r]=ident(q,s);"
        ))
        .is_err()
    );
    check("entity Root;entity S(owner:Root);view f(r:Root,q:Root,s:S[r]):S[r]=s;view g(q:Root,r:Root,s:S[q]):S[q]=f(q,r,s);").unwrap();
}
#[test]
fn nested_patterns_require_real_coverage_and_reachable_wildcards() {
    for body in [
        "data B=T|F;data D=C(B);view f(d:D):Z=match d{C(B.T)=>1;};",
        "data D=A|Next(D);view f(d:D):Z=match d{A=>0;Next(D.A)=>1;};",
        "data D=A|B;view f(d:D):Z=match d{A=>1;B=>2;_=>3;};",
        "data D=C(Z);view f(d:D):Z=match d{C(_(x))=>1;};",
        "data B=T|F;data D=C(B);view f(d:D):Z=match d{C(T)=>1;};",
    ] {
        assert!(check(body).is_err(), "{body}");
    }
    check("data B=T|F;data D=C(B);view f(d:D):Z=match d{C(B.T)=>1;_=>2;};").unwrap();
    check("data B=T;data D=C(B);view f(d:D):Z=match d{C(B.T)=>1;};").unwrap();
}
#[test]
fn named_quantifiers_and_full_comprehension_expressions_parse() {
    check("entity E;law required all():forall e:E . true;").unwrap();
    check("data D=C;law required all():forall d:R . D . d=d;").unwrap();
    check("view f():Set<Bool> = set {x<1 or x=2 | x in list<Z>[1,2] where true};").unwrap();
}
#[test]
fn alignment_syntax_and_completed_target_uniqueness_are_checked() {
    assert!(check("entity E{align Missing.x=Missing.y;}").is_err());
    assert!(check("entity Root;entity S(owner:Root){x:Z;y:Z;}correspondence M(from:Root,to:Root){states:Map<S[from],S[to]>;align S.x=S.y;}").is_err());
    check("entity Root;entity S(owner:Root){x:Z;y:Z;}correspondence M(from:Root,to:Root){states:Map<S[from],S[to]>;align S.x=S.y;align S.y=S.x;}").unwrap();
}
#[test]
fn constructor_dependencies_include_direct_and_self_references_once() {
    let p = check("data A=Zero;data B=Wrap(A)|Node(B,B);").unwrap();
    for (name, want) in [("R.B.Wrap", json!(["R.A"])), ("R.B.Node", json!(["R.B"]))] {
        assert_eq!(
            p.declarations.iter().find(|d| d["name"] == name).unwrap()["dependencies"],
            want
        );
    }
}
#[test]
fn family_locations_preserve_spaced_and_commented_names() {
    for name in ["R . S", "R // comment\n . S"] {
        let text = source(&format!(
            "entity Root;entity S(owner:Root);view f(r:Root):Set<S> = {name}[r];"
        ));
        let p = law::check(text.as_bytes()).unwrap();
        let d = p.declarations.iter().find(|d| d["name"] == "R.f").unwrap();
        let r = d["resolution"]["references"]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| {
                r["name"] == "R.S"
                    && text[r["location"]["span"][0].as_u64().unwrap() as usize
                        ..r["location"]["span"][1].as_u64().unwrap() as usize]
                        == *name
            })
            .expect("original QName location");
        assert_eq!(r["name"], "R.S");
    }
}
