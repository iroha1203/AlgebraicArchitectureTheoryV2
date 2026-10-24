//! 対象族の保存を公開mapと、その後の利用まで検査する。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::json::JNode;
use cli::*;
use std::path::{Path, PathBuf};

fn inputs(name: &str) -> PathBuf {
    let dir = workdir(name);
    for (name, bytes) in [
        (
            "d.json",
            include_bytes!("fixtures/reservations.atoms.json").as_slice(),
        ),
        (
            "a.json",
            include_bytes!("fixtures/configuration-operation.archmap.json").as_slice(),
        ),
        (
            "l.law",
            include_bytes!("fixtures/public-compose.law").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn asks(dir: &Path, requests: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        "out",
        "--time-ms",
        "120000",
    ];
    for request in requests {
        args.extend(["--ask", request]);
    }
    run(dir, &args)
}
fn answer<'a>(result: &'a JNode, id: &str) -> &'a JNode {
    arr(get(result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn value<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    get(node(result, reference), "value")
}

#[test]
fn object_map_keeps_all_objects_generators_and_public_source_consumption() {
    let dir = inputs("public-object-map");
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
            "base=map(Reservations.Migration,on=@v/m,reading=Alternative)",
            "same=compare($m.operation,to=$base.operation,kind=action)",
            "built=build(Alternative,on=$m.map.source.base.subject)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    for id in ["m", "base", "same", "built"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    let reference = get(get(answer(&result, "m"), "outputs"), "map");
    assert_eq!(s(get(node(&result, reference), "type")), "ObjectAlgebraMap");
    let map = value(&result, reference);
    assert_eq!(arr(get(map, "object_maps")).len(), 3);
    assert_eq!(arr(get(map, "operation_maps")).len(), 3);
    let state_pair = arr(get(map, "declarations"))
        .iter()
        .find(|p| s(get(p, "source")) == "Reservations.State")
        .unwrap();
    assert_eq!(s(get(state_pair, "target")), "Reservations.State");
    assert_eq!(arr(get(state_pair, "parameters")).len(), 1);
    assert_eq!(
        arr(&arr(get(state_pair, "parameters"))[0])
            .iter()
            .map(s)
            .collect::<Vec<_>>(),
        ["owner", "owner"]
    );
    for field in ["Reservations.State.free", "Reservations.State.held"] {
        assert!(
            arr(get(state_pair, "fields"))
                .iter()
                .any(|p| arr(p).iter().map(s).collect::<Vec<_>>() == [field, field])
        );
    }
    assert!(!arr(get(node(&result, reference), "conditions")).is_empty());
    for row in arr(get(map, "object_maps")) {
        let map_node = node(&result, get(row, "map"));
        let conditions = arr(get(map_node, "conditions"));
        assert!(!conditions.is_empty());
        for condition in conditions {
            assert_eq!(
                s(get(get(node(&result, condition), "judgment"), "status")),
                "established"
            );
        }
    }
    let proposition = value(
        &result,
        get(get(answer(&result, "m"), "outputs"), "proposition"),
    );
    let label = &arr(get(proposition, "operands"))[0];
    assert_eq!(s(value(&result, label)), "object_algebra_map");
    for side in ["source", "target"] {
        let algebra = value(&result, get(map, side));
        assert_eq!(arr(get(algebra, "objects")).len(), 3);
        assert_eq!(arr(get(get(algebra, "operations"), "generators")).len(), 3);
    }
    for (from, to) in [
        ("d.json", "inputs/definitions/0.json"),
        ("a.json", "inputs/archmap.json"),
        ("l.law", "inputs/law.law"),
    ] {
        assert_eq!(
            std::fs::read(dir.join(from)).unwrap(),
            std::fs::read(dir.join("out").join(to)).unwrap()
        );
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn missing_declaration_keeps_the_configuration_operation_after_refutation() {
    let dir = inputs("public-object-map-missing-declaration");
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Reservations,to_reading=Alternative,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "plan=needed($m)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    assert_eq!(s(get(answer(&result, "plan"), "status")), "established");
    get(get(answer(&result, "m"), "outputs"), "operation");
    let outputs = get(answer(&result, "m"), "outputs");
    let archsig::json::JValue::Obj(fields) = &outputs.value else {
        panic!()
    };
    assert!(!fields.iter().any(|(name, _)| name == "map"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn mapped_target_drives_named_reading_build_evaluation_and_check() {
    let dir = inputs("public-object-map-target");
    std::fs::write(
        dir.join("a.json"),
        include_bytes!("fixtures/object-configuration-map.archmap.json"),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
            "b=build(Reservations,on=$m.map.target.base.subject)",
            "n=evaluate(Reservations.holdings,on=$b.object,s=@v/r)",
            "ok=check(Reservations.conserved,on=$b.object,e=@v/f)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    for id in ["m", "b", "n", "ok"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(arr(get(map, "object_maps")).len(), 4);
    assert_eq!(arr(get(map, "operation_maps")).len(), 1);
    let n = value(&result, get(get(answer(&result, "n"), "outputs"), "value"));
    assert_eq!(arr(n).iter().map(s).collect::<Vec<_>>(), ["4", "0"]);
    let component = value(&result, get(&arr(get(map, "object_maps"))[0], "target"));
    let subject = value(&result, get(component, "subject"));
    assert_eq!(arr(subject).iter().map(s).collect::<Vec<_>>(), ["v", "B"]);
    for row in arr(get(map, "operation_maps")) {
        let proposition = value(&result, get(row, "naturality"));
        assert_eq!(s(get(proposition, "predicate")), "naturality");
        let operands = arr(get(proposition, "operands"));
        let lhs = value(&result, &operands[0]);
        let rhs = value(&result, &operands[1]);
        assert_eq!(get(lhs, "images"), get(rhs, "images"));
        assert_eq!(arr(get(lhs, "images")).len(), 39);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn reuse_recomputes_object_maps_and_rejects_an_omitted_object() {
    let dir = inputs("public-object-map-reuse");
    let request = "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)";
    let first = asks(&dir, &[request]);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let original = result_json(&dir, &first);
    let repeat = |out: &str| {
        run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
                "--out",
                out,
                "--reuse",
                "out",
                "--time-ms",
                "120000",
                "--ask",
                request,
            ],
        )
    };
    let reused = repeat("reused");
    assert_eq!(reused.code, 0, "{}", reused.stdout);
    let result = result_json(&dir, &reused);
    assert!(arr(get(get(&result, "reuse"), "rejected")).is_empty());
    let map = value(
        &original,
        get(get(answer(&original, "m"), "outputs"), "map"),
    );
    let row = &arr(get(map, "object_maps"))[1];
    // 改変するのは今回のCLIが書いた保存出力だけ。入力三点は変更しない。
    let row_text = format!(
        "{{\"map\":{{\"node\":\"{}\"}},\"source\":{{\"node\":\"{}\"}},\"target\":{{\"node\":\"{}\"}}}}",
        s(get(get(row, "map"), "node")),
        s(get(get(row, "source"), "node")),
        s(get(get(row, "target"), "node"))
    );
    let file = dir.join("out/result.json");
    let before = std::fs::read_to_string(&file).unwrap();
    let pattern = format!(",{row_text}");
    assert!(before.contains(&pattern));
    std::fs::write(file, before.replacen(&pattern, "", 1)).unwrap();
    let rejected = repeat("rejected");
    assert_eq!(rejected.code, 0, "{}", rejected.stdout);
    let result = result_json(&dir, &rejected);
    assert!(!arr(get(get(&result, "reuse"), "rejected")).is_empty());
    assert_eq!(num(get(get(&result, "reuse"), "accepted_nodes")), 0);
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(arr(get(map, "object_maps")).len(), 3);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn interruption_during_additional_transport_keeps_the_checked_operation() {
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    };
    use archsig::result::Signal;
    for mode in 0..4 {
        let mut control = Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |p| {
                let stop = p == Checkpoint::ConfigurationTransportGenerator;
                Usage {
                    elapsed_ms: u128::from(stop && mode == 0),
                    memory_mib: u128::from(stop && mode == 1),
                    signal: if stop {
                        match mode {
                            2 => Some(Signal::Int),
                            3 => Some(Signal::Term),
                            _ => None,
                        }
                    } else {
                        None
                    },
                }
            },
        );
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],
                include_bytes!("fixtures/public-compose.law").to_vec(),
                include_bytes!("fixtures/configuration-operation.archmap.json").to_vec(),
            ),
            &["m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)"],
            &mut control,
        )
        .unwrap();
        assert_eq!(result.status(), "interrupted");
        let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let a = answer(&wire, "m");
        assert_eq!(s(get(a, "status")), "undetermined");
        assert!(has(get(a, "outputs"), "operation"));
        assert!(has(get(a, "outputs"), "candidate"));
        assert!(!has(get(a, "outputs"), "map"));
        assert!(!has(get(a, "outputs"), "proposition"));
        assert!(control.stop_reason().is_some());
    }
}
