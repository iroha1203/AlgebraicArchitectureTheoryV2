//! 公開Architectureの根を選び、同じ共有評価器で値とLawを読む。
mod common;
#[path = "common/architecture_environment.rs"]
mod fixture;
use archsig::json::JNode;
use common::cli::*;
use std::path::{Path, PathBuf};
fn inputs(name: &str, extra: &str, map: Option<&str>) -> PathBuf {
    let dir = workdir(name);
    let input = fixture::input(extra, map);
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn asks(dir: &Path, qs: &[&str]) -> Run {
    asks_at(dir, qs, "out", None)
}
fn asks_at(dir: &Path, qs: &[&str], out: &str, reuse: Option<&str>) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        out,
    ];
    if let Some(reuse) = reuse {
        args.extend(["--reuse", reuse]);
    }
    for q in qs {
        args.extend(["--ask", q]);
    }
    run(dir, &args)
}
fn answer<'a>(j: &'a JNode, id: &str) -> &'a JNode {
    arr(get(j, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn value<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    get(node(j, r), "value")
}
#[test]
fn public_architecture_on_scopes_root_families_and_retains_the_actual_environment_ref() {
    let dir = inputs("architecture-on-first", "", None);
    let qs = [
        "before=check(Reservations.small,on=$m.candidate.source)",
        fixture::MAP,
        "observed=evaluate(Reservations.smallStates)",
        "source=evaluate(Reservations.smallStates,on=$m.candidate.source)",
        "target=evaluate(Reservations.smallStates,on=$m.candidate.target)",
        "after=check(Reservations.small,on=$m.candidate.target)",
        "no=evaluate(Reservations.no,on=$m.candidate.target)",
    ];
    let r = asks(&dir, &qs);
    assert_eq!(r.code, 1, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "complete");
    let j = result_json(&dir, &r);
    assert_eq!(
        arr(get(&j, "answers"))
            .iter()
            .map(|a| s(get(a, "id")))
            .collect::<Vec<_>>(),
        ["before", "m", "observed", "source", "target", "after", "no"]
    );
    for (id, expected) in [("observed", false), ("source", true), ("target", false)] {
        assert_eq!(
            value(&j, get(get(answer(&j, id), "outputs"), "value")),
            &archsig::json::parse(if expected { b"true" } else { b"false" }).unwrap(),
            "{id}"
        );
    }
    assert_eq!(s(get(answer(&j, "before"), "status")), "established");
    assert_eq!(s(get(answer(&j, "after"), "status")), "refuted");
    assert_eq!(s(get(answer(&j, "no"), "status")), "established");
    assert_eq!(
        value(&j, get(get(answer(&j, "no"), "outputs"), "value")),
        &archsig::json::parse(b"false").unwrap()
    );
    for (request, text) in arr(get(&j, "requests")).iter().zip(qs) {
        assert_eq!(s(get(request, "text")), text);
    }
    let explicit = arr(get(&j, "requests"))
        .iter()
        .find(|r| s(get(r, "id")) == "source")
        .unwrap();
    assert!(arr(get(explicit, "defaults")).is_empty());
    let candidate = value(&j, get(get(answer(&j, "m"), "outputs"), "candidate"));
    for (id, side) in [
        ("before", "source"),
        ("source", "source"),
        ("target", "target"),
        ("after", "target"),
    ] {
        let evaluation = value(&j, get(get(answer(&j, id), "outputs"), "evaluation"));
        assert_eq!(get(evaluation, "environment"), get(candidate, side), "{id}");
    }
    let observed = value(
        &j,
        get(get(answer(&j, "observed"), "outputs"), "evaluation"),
    );
    assert!(!has(observed, "environment"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn public_architecture_environment_projection_keeps_external_bindings_and_scalar_and_composite_domains()
 {
    let dir = inputs(
        "architecture-on-domains",
        r#"
view external(a:System):Bool=forall s:State[a] . s.free+s.held=4;
view composite():Bool=forall xs:Set<State> . forall s in xs . s.free+s.held=2;
view named(on:State):Z=on.free;
law required product(a:System,s:State):a=a and s.free+s.held=2;
law optional guarded(s:State) when false:false;
law required dependent(a:System,s:State[a]):s.free+s.held=2;
"#,
        None,
    );
    let r = asks(
        &dir,
        &[
            fixture::MAP,
            "a=evaluate(Reservations.smallStates,on=$m.candidate.source)",
            "b=evaluate(Reservations.smallStates,on=$a.evaluation.environment)",
            "external=evaluate(Reservations.external,a=@v/B,on=$m.candidate.source)",
            "composite=evaluate(Reservations.composite,on=$m.candidate.source)",
            "named=evaluate(Reservations.named,bind.on=@v/r,on=$m.candidate.source)",
            "symbolic=check(Reservations.symbolic,on=$m.candidate.source)",
            "product=check(Reservations.product,on=$m.candidate.source)",
            "guard=check(Reservations.guarded,on=$m.candidate.source)",
            "dependent=check(Reservations.dependent,on=$m.candidate.source)",
        ],
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let j = result_json(&dir, &r);
    for (id, expected) in [
        ("a", true),
        ("b", true),
        ("external", true),
        ("composite", false),
    ] {
        assert_eq!(
            value(&j, get(get(answer(&j, id), "outputs"), "value")),
            &archsig::json::parse(if expected { b"true" } else { b"false" }).unwrap(),
            "{id}"
        );
    }
    assert_eq!(
        s(value(&j, get(get(answer(&j, "named"), "outputs"), "value"))),
        "4"
    );
    for id in ["symbolic", "product", "guard", "dependent"] {
        assert_eq!(s(get(answer(&j, id), "status")), "established", "{id}");
    }
    let evaluation = value(&j, get(get(answer(&j, "product"), "outputs"), "evaluation"));
    let root = value(&j, get(get(answer(&j, "m"), "outputs"), "candidate"));
    assert_eq!(get(evaluation, "environment"), get(root, "source"));
    // Product has 1 root × 2 states, not the complete ArchMap's 2 × 4.
    assert_eq!(
        arr(get(&arr(get(evaluation, "parts"))[0], "children")).len(),
        2
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn public_architecture_on_usage_and_cycles_publish_no_output() {
    let bad = [
        "v=evaluate(Reservations.no,on=@v/A)",
        "v=evaluate(Reservations.no,on=$m)",
        "v=evaluate(Reservations.no,on=$m.operation)",
        "v=evaluate(Reservations.no,on=$m.candidate.source.overrides)",
        "v=evaluate(Reservations.no,on=$missing.candidate.source)",
        "v=evaluate(Reservations.no,on=$m.candidate.source,on=$m.candidate.target)",
        "v=evaluate(Reservations.no,other=$m.candidate.source)",
        "v=evaluate(Reservations.no,on=$v.evaluation.environment)",
    ];
    for (i, q) in bad.iter().enumerate() {
        let dir = inputs(&format!("architecture-on-usage-{i}"), "", None);
        let r = asks(&dir, &[fixture::MAP, q]);
        assert_eq!(r.code, 64, "{q}: {}", r.stdout);
        assert!(!r.stdout.is_empty());
        assert!(!dir.join("out").exists(), "{q}");
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn public_architecture_missing_environment_is_a_projection_condition_with_needed_and_independent_value()
 {
    let dir = inputs("architecture-on-projection", "", None);
    let r = asks(
        &dir,
        &[
            "a=evaluate(Reservations.no)",
            "b=evaluate(Reservations.no,on=$a.evaluation.environment)",
            "c=evaluate(Reservations.no,on=$b.evaluation.environment)",
            "n=needed($b)",
            "independent=evaluate(Reservations.no)",
        ],
    );
    assert_eq!(r.code, 2, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_eq!(s(get(&j, "status")), "partial");
    assert_eq!(s(get(answer(&j, "independent"), "status")), "established");
    assert_eq!(s(get(answer(&j, "b"), "status")), "undetermined");
    let reasons = arr(get(answer(&j, "b"), "reasons"));
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "condition_failed")
    );
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    assert_eq!(s(get(answer(&j, "c"), "status")), "undetermined");
    assert!(has(get(answer(&j, "n"), "outputs"), "plan"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn public_architecture_missing_value_and_owner_keep_original_slots_and_allow_available_environment()
{
    for (atom, unknown) in [("p-free", true), ("p-owner", false)] {
        let map = fixture::remove_atom(atom);
        let dir = inputs(&format!("architecture-missing-{atom}"), "", Some(&map));
        let r = asks(
            &dir,
            &[
                fixture::MAP,
                "a=evaluate(Reservations.smallStates,on=$m.candidate.source)",
                "b=evaluate(Reservations.no,on=$a.evaluation.environment)",
                "n=needed($a)",
                "independent=evaluate(Reservations.no)",
            ],
        );
        assert_eq!(r.code, 2, "{atom}: {}", r.stdout);
        let j = result_json(&dir, &r);
        assert_eq!(s(get(answer(&j, "a"), "status")), "undetermined");
        assert_eq!(s(get(answer(&j, "independent"), "status")), "established");
        assert_eq!(
            s(get(answer(&j, "b"), "status")),
            if unknown {
                "established"
            } else {
                "undetermined"
            }
        );
        let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
        let serialized = fixture::owned(plan).canonical();
        assert!(
            serialized.contains(if unknown {
                "Reservations.State.free"
            } else {
                "Reservations.State.owner"
            }),
            "{atom}: {serialized}"
        );
        assert!(serialized.contains("\"p\""));
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn public_architecture_root_domains_exclude_other_snapshots_and_empty_families_remain_true() {
    use archsig::canonical::Json;
    let duplicate = fixture::changed_map(|j| {
        let Json::Arr(snapshots) = fixture::field(j, "snapshots") else {
            panic!("snapshots")
        };
        let mut second = fixture::owned(
            &archsig::json::parse(
                snapshots[0]
                    .canonical()
                    .replace("\"v\"", "\"w\"")
                    .as_bytes(),
            )
            .unwrap(),
        );
        let Json::Arr(atoms) = fixture::field(&mut second, "atoms") else {
            panic!("atoms")
        };
        for a in atoms {
            let id = fixture::field(a, "id");
            let Json::Str(v) = id else { panic!("id") };
            *v = format!("w-{v}");
        }
        snapshots.push(second);
    });
    let empty = fixture::changed_map(|j| {
        for atom in fixture::atoms(j) {
            let Json::Obj(o) = atom else { panic!("atom") };
            if let Some(Json::Str(field)) = o.get("field") {
                if field.starts_with("Reservations.Migration.") {
                    let empty = field.ends_with(".states") || field.ends_with(".reserves");
                    *o.get_mut("value").unwrap() = if empty {
                        Json::Arr(vec![])
                    } else {
                        Json::Arr(vec![Json::str("v"), Json::str("A")])
                    };
                }
            }
            if ["p-owner", "q-owner", "e-owner", "h-owner", "k-owner"]
                .iter()
                .any(|id| o.get("id") == Some(&Json::str(*id)))
            {
                *o.get_mut("value").unwrap() = Json::Arr(vec![Json::str("v"), Json::str("B")]);
            }
        }
    });
    for (name, map, map_ask, count) in [
        ("snapshots", duplicate, fixture::MAP, 2usize),
        (
            "empty",
            empty,
            "m=map(Reservations.Migration,on=@v/z,reading=Reservations)",
            0usize,
        ),
    ] {
        let dir = inputs(&format!("architecture-domain-{name}"), "", Some(&map));
        let r = asks(
            &dir,
            &[
                map_ask,
                "a=evaluate(Reservations.smallStates,on=$m.candidate.source)",
                "c=check(Reservations.small,on=$m.candidate.source)",
            ],
        );
        assert!(matches!(r.code, 0 | 1), "{name}: {}", r.stdout);
        let j = result_json(&dir, &r);
        assert_eq!(
            value(&j, get(get(answer(&j, "a"), "outputs"), "value")),
            &archsig::json::parse(b"true").unwrap(),
            "{name}"
        );
        assert_eq!(s(get(answer(&j, "c"), "status")), "established");
        let evaluation = value(&j, get(get(answer(&j, "c"), "outputs"), "evaluation"));
        assert_eq!(
            arr(get(&arr(get(evaluation, "parts"))[0], "children")).len(),
            count,
            "{name}"
        );
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn public_architecture_reuse_recomputes_current_root_value_and_rejects_dangling_environment() {
    use archsig::canonical::Json;
    let dir = inputs("architecture-on-reuse", "", None);
    let source = [
        fixture::MAP,
        "a=evaluate(Reservations.smallStates,on=$m.candidate.source)",
    ];
    let target = [
        fixture::MAP,
        "a=evaluate(Reservations.smallStates,on=$m.candidate.target)",
    ];
    let previous = asks_at(&dir, &source, "previous", None);
    assert_eq!(previous.code, 0, "{}", previous.stdout);
    let previous_bytes = std::fs::read(dir.join("previous/result.json")).unwrap();
    for (label, qs, expected) in [("same", &source, true), ("target", &target, false)] {
        let plain = asks_at(&dir, qs, &format!("plain-{label}"), None);
        let reused = asks_at(&dir, qs, &format!("reused-{label}"), Some("previous"));
        assert_eq!(plain.code, 0, "{}", plain.stdout);
        assert_eq!(reused.code, 0, "{}", reused.stdout);
        let a = result_json(&dir, &plain);
        let b = result_json(&dir, &reused);
        for field in ["requests", "answers", "nodes", "inputs"] {
            assert_eq!(get(&a, field), get(&b, field), "{label} {field}");
        }
        assert_eq!(
            value(&b, get(get(answer(&b, "a"), "outputs"), "value")),
            &archsig::json::parse(if expected { b"true" } else { b"false" }).unwrap()
        );
        assert_eq!(num(get(get(&b, "reuse"), "accepted_nodes")), 0);
    }
    let mut forged = fixture::owned(&archsig::json::parse(&previous_bytes).unwrap());
    let Json::Arr(nodes) = fixture::field(&mut forged, "nodes") else {
        panic!("nodes")
    };
    let mut changed = false;
    for n in nodes {
        let Json::Obj(o) = n else { panic!("node") };
        if let Some(Json::Obj(value)) = o.get_mut("value") {
            if let Some(environment) = value.get_mut("environment") {
                *environment = Json::obj([("node", Json::str("n999999"))]);
                changed = true;
                break;
            }
        }
    }
    assert!(changed);
    std::fs::create_dir(dir.join("forged")).unwrap();
    std::fs::write(dir.join("forged/result.json"), forged.canonical()).unwrap();
    let reused = asks_at(&dir, &source, "rejected", Some("forged"));
    assert_eq!(reused.code, 0, "{}", reused.stdout);
    let j = result_json(&dir, &reused);
    assert!(!arr(get(get(&j, "reuse"), "rejected")).is_empty());
    assert_eq!(
        value(&j, get(get(answer(&j, "a"), "outputs"), "value")),
        &archsig::json::parse(b"true").unwrap()
    );
    let changed = fixture::changed_map(|j| {
        for a in fixture::atoms(j) {
            let Json::Obj(o) = a else { panic!("atom") };
            if o.get("id") == Some(&Json::str("p-free")) {
                *o.get_mut("value").unwrap() = Json::str("99");
            }
        }
    });
    std::fs::write(dir.join("a.json"), changed).unwrap();
    let current = asks_at(&dir, &source, "current", Some("previous"));
    assert_eq!(current.code, 0, "{}", current.stdout);
    let j = result_json(&dir, &current);
    assert_eq!(
        value(&j, get(get(answer(&j, "a"), "outputs"), "value")),
        &archsig::json::parse(b"false").unwrap()
    );
    assert_eq!(
        std::fs::read(dir.join("previous/result.json")).unwrap(),
        previous_bytes
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn public_architecture_existing_output_is_rejected_without_touching_siblings() {
    let dir = inputs("architecture-on-delivery", "", None);
    std::fs::create_dir(dir.join("out")).unwrap();
    std::fs::write(dir.join("out/keep"), b"existing").unwrap();
    std::fs::create_dir(dir.join("unrelated.tmp")).unwrap();
    std::fs::write(dir.join("unrelated.tmp/keep"), b"another-run").unwrap();
    let r = asks(
        &dir,
        &[
            fixture::MAP,
            "a=evaluate(Reservations.smallStates,on=$m.candidate.source)",
        ],
    );
    assert_eq!(r.code, 64, "{}", r.stdout);
    assert!(!r.stdout.is_empty());
    assert_eq!(std::fs::read(dir.join("out/keep")).unwrap(), b"existing");
    assert_eq!(
        std::fs::read(dir.join("unrelated.tmp/keep")).unwrap(),
        b"another-run"
    );
    assert!(!dir.join("out/result.json").exists());
    std::fs::remove_dir_all(dir).unwrap();
}

struct DeliveryIo {
    fail: bool,
}
impl archsig::run::Io for DeliveryIo {
    fn create_dir(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::create_dir(p)
    }
    fn write(&mut self, p: &Path, b: &[u8]) -> std::io::Result<()> {
        if self.fail && p.ends_with("result.json") {
            Err(std::io::ErrorKind::PermissionDenied.into())
        } else {
            std::fs::write(p, b)
        }
    }
    fn flush(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::File::open(p)?.sync_all()
    }
    fn rename_noreplace(&mut self, a: &Path, b: &Path) -> std::io::Result<()> {
        rustix::fs::renameat_with(
            rustix::fs::CWD,
            a,
            rustix::fs::CWD,
            b,
            rustix::fs::RenameFlags::NOREPLACE,
        )
        .map_err(std::io::Error::from)
    }
    fn remove_dir_all(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::remove_dir_all(p)
    }
}
struct DeliverySignal(Option<archsig::result::Signal>);
impl archsig::run::Signals for DeliverySignal {
    fn freeze(&mut self) -> Option<archsig::result::Signal> {
        self.0
    }
}
#[test]
fn public_architecture_delivery_cancellation_protects_unfinished_work_and_retains_verified_results()
{
    for mode in 0..5 {
        let dir = inputs(&format!("architecture-delivery-{mode}"), "", None);
        std::fs::create_dir(dir.join("other-run.tmp")).unwrap();
        std::fs::write(dir.join("other-run.tmp/keep"), b"untouched").unwrap();
        let args = archsig::run::RunArgs {
            inputs: archsig::run::CheckArgs {
                atom_definitions: vec![dir.join("d.json")],
                law: dir.join("l.law"),
                archmap: Some(dir.join("a.json")),
                out: dir.join("out"),
            },
            asks: vec![
                fixture::MAP.into(),
                "a=evaluate(Reservations.smallStates,on=$m.candidate.source)".into(),
            ],
            reuse: None,
            time_ms: None,
            memory_mib: None,
        };
        let signal = match mode {
            1 => Some(archsig::result::Signal::Int),
            2 => Some(archsig::result::Signal::Term),
            _ => None,
        };
        let mut control = if mode >= 3 {
            archsig::observed::control::Control::new(
                archsig::observed::control::Limits::default(),
                move |_| archsig::observed::control::Usage {
                    signal: Some(if mode == 3 {
                        archsig::result::Signal::Int
                    } else {
                        archsig::result::Signal::Term
                    }),
                    ..archsig::observed::control::Usage::default()
                },
            )
        } else {
            archsig::observed::control::Control::unlimited()
        };
        let outcome = archsig::run::run_requests(
            &mut DeliveryIo { fail: mode == 0 },
            &mut DeliverySignal(signal),
            &args,
            std::time::Instant::now(),
            &mut control,
        );
        assert_eq!(
            outcome.exit_code,
            if mode == 0 {
                74
            } else if mode == 1 || mode == 3 {
                130
            } else {
                143
            }
        );
        if mode == 0 || mode >= 3 {
            assert!(!dir.join("out").exists());
        }
        assert_eq!(
            std::fs::read(dir.join("other-run.tmp/keep")).unwrap(),
            b"untouched"
        );
        let receipt = archsig::json::parse(outcome.receipt().as_bytes()).unwrap();
        if mode == 0 || mode >= 3 {
            assert!(!has(&receipt, "result"));
        } else {
            let saved =
                archsig::json::parse(&std::fs::read(dir.join("out/result.json")).unwrap()).unwrap();
            assert_eq!(s(get(&saved, "status")), "interrupted");
            assert_eq!(s(get(answer(&saved, "a"), "status")), "established");
            assert_eq!(
                value(&saved, get(get(answer(&saved, "a"), "outputs"), "value")),
                &archsig::json::parse(b"true").unwrap()
            );
            let candidate = value(
                &saved,
                get(get(answer(&saved, "m"), "outputs"), "candidate"),
            );
            let evaluation = value(
                &saved,
                get(get(answer(&saved, "a"), "outputs"), "evaluation"),
            );
            assert_eq!(get(evaluation, "environment"), get(candidate, "source"));
        }
        assert!(std::fs::read_dir(&dir).unwrap().all(|e| {
            !e.unwrap()
                .file_name()
                .to_string_lossy()
                .contains(".archsig-")
        }));
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn explicit_architecture_scope_is_retained_for_constants_calls_universal_and_family_evaluations() {
    let dir = inputs(
        "architecture-scope",
        r#"
view nested():Bool=no();
view universal():Bool=forall z:Z . z=z;
law required numeric(z:Z):z=z;
law required finite(s:State):true;
law required dependentScope(a:System,s:State[a]):true;
"#,
        None,
    );
    let qs = [
        "m=map(Reservations.Migration,on=@v/m,reading=Reservations,to_reading=Alternative)",
        "constant=evaluate(Reservations.no,on=$m.candidate.target)",
        "nested=evaluate(Reservations.nested,on=$m.candidate.target)",
        "universal=evaluate(Reservations.universal,on=$m.candidate.target)",
        "numeric=check(Reservations.numeric,on=$m.candidate.target)",
        "finite=check(Reservations.finite,on=$m.candidate.target)",
        "dependent=check(Reservations.dependentScope,on=$m.candidate.target)",
        "bound=evaluate(Reservations.holdings,s=@v/p,on=$m.candidate.target)",
        "observed=evaluate(Reservations.no)",
    ];
    let r = asks(&dir, &qs);
    assert_eq!(r.code, 0, "{}", r.stdout);
    let j = result_json(&dir, &r);
    let assert_scope = |scope: &JNode| {
        assert!(
            arr(get(scope, "snapshots")).iter().any(|x| s(x) == "v"),
            "{scope:?}"
        );
        assert!(
            arr(get(scope, "modes"))
                .iter()
                .any(|x| s(x) == "specification"),
            "{scope:?}"
        );
        for reading in ["Reservations", "Alternative"] {
            assert!(
                arr(get(scope, "readings")).iter().any(|x| s(x) == reading),
                "{reading}: {scope:?}"
            );
        }
    };
    for id in [
        "constant",
        "nested",
        "universal",
        "numeric",
        "finite",
        "dependent",
        "bound",
    ] {
        let a = answer(&j, id);
        assert_scope(get(a, "scope"));
        assert_scope(get(node(&j, get(get(a, "outputs"), "evaluation")), "scope"));
    }
    let constant = node(
        &j,
        get(get(answer(&j, "constant"), "outputs"), "evaluation"),
    );
    assert!(arr(get(constant, "support")).is_empty());
    let primitive = node(&j, get(get(answer(&j, "constant"), "outputs"), "value"));
    assert!(arr(get(primitive, "support")).is_empty());
    let observed = get(answer(&j, "observed"), "scope");
    assert!(arr(get(observed, "snapshots")).is_empty());
    assert!(arr(get(observed, "modes")).is_empty());
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn available_environment_root_binds_independently_of_the_producer_value() {
    for (atom, supplied) in [("p-free", true), ("p-owner", false)] {
        let map = fixture::remove_atom(atom);
        let dir = inputs(
            &format!("architecture-root-projection-{atom}"),
            "view rootEq(a:System):Bool=a=a; law required boundRoot(a:System,b:Bool):a=a and b=b;",
            Some(&map),
        );
        let r = asks(
            &dir,
            &[
                fixture::MAP,
                "a=evaluate(Reservations.smallStates,on=$m.candidate.source)",
                "root=evaluate(Reservations.rootEq,a=$a.evaluation.environment.root)",
                "scoped=evaluate(Reservations.rootEq,a=$a.evaluation.environment.root,on=$m.candidate.source)",
                "family=check(Reservations.boundRoot,a=$a.evaluation.environment.root)",
                "n=needed($root)",
                "origin=evaluate(Reservations.no)",
                "omitted=evaluate(Reservations.rootEq,a=$origin.evaluation.environment.root)",
                "independent=evaluate(Reservations.no)",
            ],
        );
        assert_eq!(r.code, 2, "{}", r.stdout);
        let j = result_json(&dir, &r);
        assert_eq!(s(get(answer(&j, "a"), "status")), "undetermined");
        for id in ["root", "scoped", "family"] {
            let a = answer(&j, id);
            assert_eq!(
                s(get(a, "status")),
                if supplied {
                    "established"
                } else {
                    "undetermined"
                },
                "{atom}/{id}"
            );
            if supplied {
                assert!(arr(get(a, "reasons")).is_empty());
                let evaluation = value(&j, get(get(a, "outputs"), "evaluation"));
                assert_eq!(
                    value(&j, get(evaluation, "value")),
                    &archsig::json::parse(b"true").unwrap()
                );
                if id == "family" {
                    assert_eq!(
                        arr(get(&arr(get(evaluation, "parts"))[0], "children")).len(),
                        2
                    );
                }
            } else {
                let reasons = fixture::owned(get(a, "reasons")).canonical();
                assert!(reasons.contains("dependency_blocked"));
                assert!(reasons.contains("Reservations.State.owner"));
            }
        }
        let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
        let serialized = fixture::owned(plan).canonical();
        assert_eq!(serialized.contains("Reservations.State.owner"), !supplied);
        // neededは元の依存先の未観測も列挙するが、確定rootのblockerは増やさない。
        assert_eq!(serialized.contains("Reservations.State.free"), supplied);
        assert_eq!(arr(get(plan, "blockers")).is_empty(), supplied);
        let omitted = fixture::owned(get(answer(&j, "omitted"), "reasons")).canonical();
        assert!(omitted.contains("condition_failed"));
        assert_eq!(s(get(answer(&j, "independent"), "status")), "established");
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn unbound_root_law_retains_internal_owned_quantification_and_partial_bindings() {
    let dir = inputs(
        "architecture-nested-owner-family",
        r#"
view yes():Bool=true;
law required nestedOwner(x:System):forall s:State[x] . s.free+s.held=2;
law required partiallyBound(x:System,b:Bool):forall s:State[x] . (s.free+s.held=2 and b);
law optional guardedOwner(x:System) when forall s:State[x] . s.free+s.held=2 : true;
"#,
        None,
    );
    let r = asks(
        &dir,
        &[
            fixture::MAP,
            "source=check(Reservations.nestedOwner,on=$m.candidate.source)",
            "target=check(Reservations.nestedOwner,on=$m.candidate.target)",
            "observed=check(Reservations.nestedOwner)",
            "truth=evaluate(Reservations.yes)",
            "falsity=evaluate(Reservations.no)",
            "partial=check(Reservations.partiallyBound,b=$truth.value,on=$m.candidate.source)",
            "bad=check(Reservations.partiallyBound,b=$falsity.value,on=$m.candidate.source)",
            "guard=check(Reservations.guardedOwner,on=$m.candidate.source)",
            "external=check(Reservations.nestedOwner,x=@v/B,on=$m.candidate.source)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_eq!(s(get(&r.receipt, "status")), "complete");
    for (id, status, rows) in [
        ("source", "established", 1),
        ("target", "refuted", 1),
        ("observed", "refuted", 2),
        ("partial", "established", 1),
        ("bad", "refuted", 1),
        ("guard", "established", 1),
    ] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), status, "{id}");
        let evaluation = value(&j, get(get(a, "outputs"), "evaluation"));
        assert_eq!(
            arr(get(&arr(get(evaluation, "parts"))[0], "children")).len(),
            rows,
            "{id}"
        );
    }
    assert_eq!(s(get(answer(&j, "external"), "status")), "refuted");
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn unbound_owned_quantification_preserves_missing_fields_and_independent_results() {
    for (atom, field) in [
        ("p-free", "Reservations.State.free"),
        ("p-owner", "Reservations.State.owner"),
    ] {
        let map = fixture::remove_atom(atom);
        let dir = inputs(
            &format!("architecture-nested-owner-{atom}"),
            "law required nestedOwner(x:System):forall s:State[x] . s.free+s.held=2;",
            Some(&map),
        );
        let r = asks(
            &dir,
            &[
                fixture::MAP,
                "a=check(Reservations.nestedOwner,on=$m.candidate.source)",
                "n=needed($a)",
                "keep=evaluate(Reservations.no)",
            ],
        );
        assert_eq!(r.code, 2, "{}", r.stdout);
        let j = result_json(&dir, &r);
        assert_eq!(s(get(answer(&j, "a"), "status")), "undetermined");
        assert_eq!(s(get(answer(&j, "keep"), "status")), "established");
        assert!(fixture::owned(&j).canonical().contains(field));
        let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
        assert!(
            fixture::owned(get(plan, "requirements"))
                .canonical()
                .contains(field)
        );
        assert!(
            !fixture::owned(get(&j, "issues"))
                .canonical()
                .contains("internal")
        );
        std::fs::remove_dir_all(dir).unwrap();
    }
}
