use crate::{canonical::Json, control::quiet, observed::evaluate::evaluate_observed_bytes};
mod owner_delivery_sources {
    include!("../../tests/common/owner_delivery_sources.rs");
}
use owner_delivery_sources::owner_sources;
#[test]
fn finite_owner_partial_delivery_keeps_io_and_signal_precedence() {
    use crate::run::{CheckArgs, Io, RunArgs, Signals, run_requests};
    use std::{io, path::Path};
    struct RefuseIo(usize);
    impl Io for RefuseIo {
        fn create_dir(&mut self, _: &Path) -> io::Result<()> {
            self.0 += 1;
            Err(io::ErrorKind::PermissionDenied.into())
        }
        fn write(&mut self, _: &Path, _: &[u8]) -> io::Result<()> {
            unreachable!("create failed")
        }
        fn flush(&mut self, _: &Path) -> io::Result<()> {
            unreachable!("create failed")
        }
        fn rename_noreplace(&mut self, _: &Path, _: &Path) -> io::Result<()> {
            unreachable!("create failed")
        }
        fn remove_dir_all(&mut self, _: &Path) -> io::Result<()> {
            Ok(())
        }
    }
    struct Freeze(Option<crate::result::Signal>);
    impl Signals for Freeze {
        fn freeze(&mut self) -> Option<crate::result::Signal> {
            self.0.take()
        }
    }
    let baseline = evaluate_observed_bytes(
        owner_sources(false),
        &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        &quiet(),
    )
    .unwrap();
    assert!(!baseline.has_internal_issue());
    assert_eq!(
        baseline.prepared().inputs().archmap().snapshots()[0]
            .subjects
            .iter()
            .filter(|subject| subject.ty == "Pattern.Root")
            .count(),
        2
    );
    assert_eq!(baseline.status(), "partial");
    let Json::Obj(ref wire) = baseline.wire() else {
        panic!("record")
    };
    let Json::Arr(answers) = &wire["answers"] else {
        panic!("answers")
    };
    let Json::Obj(answer) = &answers[0] else {
        panic!("answer")
    };
    let Json::Obj(outputs) = &answer["outputs"] else {
        panic!("outputs")
    };
    assert!(!outputs.contains_key("repair"));
    assert!(!outputs.contains_key("object"));
    let source = baseline.prepared().inputs().sources();
    let dir = std::env::temp_dir().join(format!(
        "archsig-owner-delivery-precedence-internal-{}",
        std::process::id(),
    ));
    std::fs::create_dir(&dir).expect("隔離したテスト入力の保存先");
    for (name, bytes) in [
        ("d.json", source.definitions()[0].bytes()),
        ("l.law", source.law().bytes()),
        ("a.json", source.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let args = |out| RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec![dir.join("d.json")],
            law: dir.join("l.law"),
            archmap: Some(dir.join("a.json")),
            out,
        },
        asks: vec!["r=repair(Selected.valid,on=@v/root,using=Selected.choose)".into()],
        reuse: None,
    };
    let mut io = RefuseIo(0);
    let result = run_requests(
        &mut io,
        &mut Freeze(None),
        &args(Some(dir.join("out"))),
        &quiet(),
    );
    assert!(
        io.0 > 0,
        "partial mathematical result reaches explicit save"
    );
    assert_eq!(result.exit_code, 74);
    assert!(result.result.is_none());
    assert!(!dir.join("out").exists());
    for (signal, code) in [
        (crate::result::Signal::Int, 130),
        (crate::result::Signal::Term, 143),
    ] {
        let mut io = RefuseIo(0);
        let result = run_requests(&mut io, &mut Freeze(Some(signal)), &args(None), &quiet());
        assert_eq!(result.exit_code, code);
        assert!(result.result.is_none());
        assert_eq!(io.0, 0);
    }
    std::fs::remove_dir_all(&dir).unwrap();
}
