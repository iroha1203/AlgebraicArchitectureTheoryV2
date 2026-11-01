//! 既知の空の有限Law族は、欠測や未実装ではなく恒真の制約族である。
use crate::common::cli;
use archsig_common::json::JNode;
use cli::*;
fn node<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
#[test]
fn empty_finite_law_family_localizes_and_diagnoses_without_inventing_instances() {
    let dir = workdir("empty-finite-local");
    let definitions=include_str!("fixtures/counter.atoms.json").replace("\"declarations\": [",r#""declarations": [{"kind":"entity","name":"Counter.Empty","meaning":"空の有限対象族。","parameters":[],"fields":[],"alignments":[]},"#);
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let digest = &checked.vocabularies()["Counter"].digest;
    let old = archsig_input::definition::check_definitions(&[(
        "definition0",
        include_bytes!("fixtures/counter.atoms.json"),
    )])
    .unwrap();
    let map = include_str!("fixtures/counter.archmap.json")
        .replace(&old.vocabularies()["Counter"].digest, digest);
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading R{{use vocabulary Counter version \"1\" digest \"{digest}\";law required vac(s:State,e:Empty):s.count=s.count;}}"
    );
    for (name, bytes) in [
        ("d.json", definitions.as_bytes()),
        ("l.law", law.as_bytes()),
        ("a.json", map.as_bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let r = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "c=check(R.vac,s=@v/s)",
            "--ask",
            "a=build(R,on=@v/s)",
            "--ask",
            "l=localize($a.object,law=R.vac,s=@v/s)",
            "--ask",
            "d=diagnose($l.system,side=equation,degree=1)",
            "--out",
            "out",
        ],
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let j = result_json(&dir, &r);
    let answers = arr(get(&j, "answers"));
    assert_eq!(answers.len(), 4);
    for a in answers {
        assert_eq!(s(get(a, "status")), "established");
    }
    let local = node(&j, get(get(&answers[2], "outputs"), "system"));
    let system = get(local, "value");
    assert!(arr(get(system, "laws")).is_empty());
    let contexts = arr(get(system, "contexts"));
    assert_eq!(contexts.len(), 1);
    let states = arr(get(system, "equation_states"));
    assert_eq!(states.len(), 1);
    let solutions = get(node(&j, get(&states[0], "solutions")), "value");
    let values = arr(get(get(solutions, "representation"), "values"));
    assert_eq!(values.len(), 1);
    assert!(arr(get(node(&j, &values[0]), "value")).is_empty());
    let diagnostic = get(
        node(&j, get(get(&answers[3], "outputs"), "diagnostic")),
        "value",
    );
    assert_eq!(s(get(diagnostic, "kind")), "finite_matching");
    assert!(arr(get(&j, "issues")).is_empty());
}
