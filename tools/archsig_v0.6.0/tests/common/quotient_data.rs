use super::*;
mod fixture {
    include!("finite_data_quotient.rs");
}
fn data_input(name: &str, body: &str) -> std::path::PathBuf {
    let sources = fixture::sources("", body);
    let dir = workdir(name);
    for (name, bytes) in [
        ("d.json", sources.definitions()[0].bytes()),
        ("l.law", sources.law().bytes()),
        ("a.json", sources.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
#[test]
fn finite_data_quotient_keeps_constructor_identity_and_reuses() {
    let dir = data_input(
        "quotient-data-cli",
        "view tag(s:State):Token=if s.x then Token.Left(s.y) else Token.Right(s.y);view visible(s:State):Token=if s.x then Token.Left(s.y) else Token.Empty;law optional held(s:State):Token.Left(s.x)=Token.Left(s.x);law optional hidden(s:State):Token.Left(s.y)=Token.Left(s.y);",
    );
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "all=quotient(Pair.tag,on=$s.domain,s=@v/s)",
        "good=quotient(Pair.visible,on=$s.domain,s=@v/s,law=Pair.held)",
        "bad=quotient(Pair.visible,on=$s.domain,s=@v/s,law=Pair.hidden)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 1, "{}", first.stdout);
    let result = result_json(&dir, &first);
    let answers = arr(get(&result, "answers"));
    exact_fibers(
        &result,
        1,
        vec![
            vec![(false, false)],
            vec![(false, true)],
            vec![(true, false)],
            vec![(true, true)],
        ],
    );
    for index in [2, 3] {
        exact_fibers(
            &result,
            index,
            vec![
                vec![(false, false), (false, true)],
                vec![(true, false)],
                vec![(true, true)],
            ],
        );
    }
    assert_eq!(s(get(&answers[2], "status")), "established");
    assert_eq!(s(get(&answers[3], "status")), "refuted");
    let data = get(
        get(
            node(&result, &arr(get(&answers[3], "counterexamples"))[0]),
            "value",
        ),
        "data",
    );
    let points = [
        pair(get(node(&result, get(data, "first")), "value")),
        pair(get(node(&result, get(data, "second")), "value")),
    ];
    assert_eq!(points, [(false, false), (false, true)]);
    let repeated = execute(&dir, "reused", &asks, Some("out"));
    assert_eq!(repeated.code, 1, "{}", repeated.stdout);
    let reused = result_json(&dir, &repeated);
    for key in ["answers", "nodes"] {
        assert_eq!(get(&result, key).value, get(&reused, key).value);
    }
    let path = dir.join(s(get(&first.receipt, "result")));
    let saved = std::fs::read_to_string(&path).unwrap();
    let damaged = saved.replacen("\"tag\":\"Left\"", "\"tag\":\"Right\"", 1);
    assert_ne!(saved, damaged);
    std::fs::write(path, damaged).unwrap();
    let rejected = execute(&dir, "rejected", &asks, Some("out"));
    assert_eq!(rejected.code, 1, "{}", rejected.stdout);
    let rebuilt = result_json(&dir, &rejected);
    assert!(
        warnings(&rebuilt)
            .iter()
            .any(|r| s(get(r, "code")) == "usage")
    );
    for key in ["answers", "nodes"] {
        assert_eq!(get(&result, key).value, get(&rebuilt, key).value);
    }
}

#[test]
fn finite_data_quotient_preserves_nested_values_and_law_binding_order() {
    use archsig_common::control::Control;
    use archsig_computation::observed::evaluate::evaluate_observed_bytes;
    let singletons = vec![
        vec![(false, false)],
        vec![(false, true)],
        vec![(true, false)],
        vec![(true, true)],
    ];
    let tagged = vec![
        vec![(false, false), (false, true)],
        vec![(true, false)],
        vec![(true, true)],
    ];
    let mixed = vec![
        vec![(false, false)],
        vec![(false, true), (true, false)],
        vec![(true, true)],
    ];
    let cases = [
        (
            "Token",
            "if s.x then Token.Left(s.y) else Token.Right(s.y)",
            singletons.clone(),
        ),
        (
            "Token",
            "if s.x then Token.Left(s.y) else Token.Empty",
            tagged.clone(),
        ),
        ("Token", "Token.Both(s.x,s.y)", singletons.clone()),
        (
            "Packet",
            "Packet.Wrap((none<Token>,list<Token>[],set<Token>{Token.Left(s.x),Token.Left(s.y)}))",
            mixed.clone(),
        ),
        (
            "Packet",
            "Packet.Wrap((some(Token.Empty),list<Token>[Token.Left(s.x),Token.Left(s.y)],set<Token>{}))",
            singletons.clone(),
        ),
        (
            "Option<List<Token>>",
            "if s.x then some(list<Token>[Token.Left(s.y)]) else none<List<Token>>",
            tagged.clone(),
        ),
        (
            "Tree",
            "Tree.Branch(Tree.Leaf(s.x),Tree.Leaf(s.y))",
            singletons.clone(),
        ),
        (
            "Tree",
            "Tree.Packed((Tree.End,some(Tree.Leaf(s.x)),list<Tree>[Tree.Leaf(s.y)]))",
            singletons.clone(),
        ),
        (
            "Set<Tree>",
            "set<Tree>{Tree.Leaf(s.x),Tree.Leaf(s.y)}",
            mixed,
        ),
        (
            "Tree",
            "if s.x then Tree.Branch(Tree.Leaf(s.y),Tree.End) else Tree.End",
            tagged,
        ),
    ];
    for (ty, body, expected) in cases {
        let body = format!(
            "view shape(s:State):{ty} = {body};law optional held(s:State):shape(s)=shape(s);law optional hidden(s:State,z:Bool,a:Bool):Token.Both(s.x,s.y)=Token.Both(z,a);"
        );
        let result = evaluate_observed_bytes(
            fixture::sources("", &body),
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "good=quotient(Pair.shape,on=$s.domain,s=@v/s,law=Pair.held)",
                "bad=quotient(Pair.shape,on=$s.domain,s=@v/s,law=Pair.hidden)",
            ],
            &Control::unlimited(),
        )
        .unwrap();
        let wire = archsig_common::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        assert_eq!(s(get(&answers[1], "status")), "established");
        for index in [1, 2] {
            exact_fibers(&wire, index, expected.clone());
        }
        let nontrivial = expected.iter().any(|class| class.len() > 1);
        assert_eq!(
            s(get(&answers[2], "status")),
            if nontrivial { "refuted" } else { "established" }
        );
        if nontrivial {
            let data = get(
                get(node(&wire, &arr(get(&answers[2], "evidence"))[0]), "value"),
                "data",
            );
            let points = [
                pair(get(node(&wire, get(data, "first")), "value")),
                pair(get(node(&wire, get(data, "second")), "value")),
            ];
            assert!(points[0] < points[1]);
            assert!(
                expected
                    .iter()
                    .any(|class| class.contains(&points[0]) && class.contains(&points[1]))
            );
            for (side, reference) in arr(get(data, "law_values")).iter().enumerate() {
                let family = arr(get(node(&wire, reference), "value"));
                assert_eq!(family.len(), 4);
                let mut keys = vec![];
                for entry in family {
                    let entry = arr(entry);
                    let key = arr(&entry[0]);
                    assert_eq!(key.len(), 3);
                    assert_eq!(s(&arr(&key[0])[0]), "v");
                    assert_eq!(s(&arr(&key[0])[1]), "s");
                    let boolean = |v: &JNode| match v.value {
                        JValue::Bool(b) => b,
                        _ => panic!("Bool"),
                    };
                    let (z, a) = (boolean(&key[1]), boolean(&key[2]));
                    keys.push((z, a));
                    let operands = arr(get(&entry[1], "some"));
                    for (operand, expected) in operands.iter().zip([points[side], (z, a)]) {
                        assert_eq!(s(get(operand, "tag")), "Both");
                        assert_eq!(pair(get(operand, "args")), expected);
                    }
                }
                keys.sort();
                assert_eq!(
                    keys,
                    vec![(false, false), (false, true), (true, false), (true, true)]
                );
            }
        }
    }
}
