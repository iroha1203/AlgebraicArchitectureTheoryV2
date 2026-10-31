//! 公開RunArgsとCLI解析が、同じ検証済み予算をControlへ渡すことを確かめる。
use archsig::{
    control::{Checkpoint, Control, Limits, Resource, StopReason, Usage},
    run::{Budget, CheckArgs, Command, RunArgs, parse_args},
};
use std::ffi::OsString;

fn args() -> RunArgs {
    RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec!["d.json".into()],
            law: "l.law".into(),
            archmap: Some("a.json".into()),
            out: None,
        },
        asks: vec!["n=evaluate(Fixed.current,s=@v/s)".into()],
        reuse: None,
        time_ms: None,
        memory_mib: None,
    }
}

fn cli(flag: &str, text: &str) -> Result<RunArgs, archsig::run::UsageError> {
    let words = [
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--ask",
        "n=evaluate(Fixed.current,s=@v/s)",
        flag,
        text,
    ]
    .map(OsString::from);
    match parse_args(&words)? {
        Command::Run(args) => Ok(args),
        _ => panic!("run command"),
    }
}

#[test]
fn direct_api_and_cli_reject_invalid_budgets_before_constructing_run_args() {
    for text in [
        "0",
        "-1",
        "not-a-number",
        "",
        "01",
        "+1",
        "1.0",
        "1e2",
        " 1",
        "1 ",
        "１",
        "999999999999999999999999999999999999999999999x",
    ] {
        assert!(
            text.parse::<Budget>().is_err(),
            "direct API accepted {text:?}"
        );
        for flag in ["--time-ms", "--memory-mib"] {
            let error = cli(flag, text).unwrap_err();
            assert_eq!(error.argument, flag);
            assert_eq!(
                error.message,
                format!("budget `{text}` must be an integer matching [1-9][0-9]*")
            );
        }
    }
}

#[test]
fn direct_api_and_cli_preserve_exact_and_unreachable_limits() {
    for (text, measured) in [
        ("1", Some(1)),
        ("128", Some(128)),
        (
            "340282366920938463463374607431768211454",
            Some(u128::MAX - 1),
        ),
        ("340282366920938463463374607431768211455", Some(u128::MAX)),
        ("340282366920938463463374607431768211456", None),
        (
            "9999999999999999999999999999999999999999999999999999999999999999999",
            None,
        ),
    ] {
        for (flag, resource) in [
            ("--time-ms", Resource::TimeMs),
            ("--memory-mib", Resource::MemoryMib),
        ] {
            let mut direct = args();
            let budget = text.parse::<Budget>().unwrap();
            if resource == Resource::TimeMs {
                direct.time_ms = Some(budget);
            } else {
                direct.memory_mib = Some(budget);
            }
            assert_eq!(cli(flag, text).unwrap(), direct);
            let limits = direct.limits();
            assert_eq!(
                limits,
                Limits {
                    time_ms: if resource == Resource::TimeMs {
                        measured
                    } else {
                        None
                    },
                    memory_mib: if resource == Resource::MemoryMib {
                        measured
                    } else {
                        None
                    },
                }
            );
            // 到達不能な上限をu128::MAXへ丸めると、このprobeで誤停止する。
            let mut control = Control::new(limits, move |_| Usage {
                elapsed_ms: if resource == Resource::TimeMs {
                    u128::MAX
                } else {
                    0
                },
                memory_mib: if resource == Resource::MemoryMib {
                    u128::MAX
                } else {
                    0
                },
                signal: None,
            });
            match measured {
                Some(limit) => assert_eq!(
                    control.checkpoint(Checkpoint::InputBundle),
                    Err(StopReason::BudgetExhausted {
                        resource,
                        limit,
                        observed: u128::MAX
                    })
                ),
                None => assert_eq!(control.checkpoint(Checkpoint::InputBundle), Ok(())),
            }
        }
    }
    assert_eq!(args().limits(), Limits::default());
}
