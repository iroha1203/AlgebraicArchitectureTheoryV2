//! `archsig digest --atom-definition D ...`: 語彙 manifest と canonical SHA-256 digest を出力する。

use super::{CommandOutput, input_status, read_bounded, stopped};
use crate::cli::{DigestArgs, emit_progress};
use crate::run::{Signals, output};
use archsig_common::canonical::{Json, JsonObject};
use archsig_common::control::{CheckFailure, Control};
use archsig_input::definition::check_definitions_controlled;
use archsig_input::result::ResultIssue;

pub fn execute(
    args: &DigestArgs,
    max_file_bytes: u64,
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<CommandOutput, crate::run::Outcome> {
    emit_progress(&format!(
        "digest: reading {} atom definition file(s)",
        args.atom_definitions.len()
    ));
    let mut raw_files = Vec::with_capacity(args.atom_definitions.len());
    for (idx, path) in args.atom_definitions.iter().enumerate() {
        let bytes = read_bounded(path, max_file_bytes, signals)?;
        raw_files.push((format!("definition{idx}"), bytes));
    }

    let file_refs: Vec<(&str, &[u8])> = raw_files
        .iter()
        .map(|(id, bytes)| (id.as_str(), bytes.as_slice()))
        .collect();

    emit_progress("digest: checking definitions and computing vocabulary digests");
    let checked = match check_definitions_controlled(&file_refs, control) {
        Ok(checked) => checked,
        Err(CheckFailure::Stopped(sig)) => return Err(stopped(signals, sig)),
        Err(CheckFailure::Input(failure)) => {
            let (status, code) = input_status(failure.issue.code);
            return Err(output::notify(
                signals,
                status,
                code,
                control.stop_reason(),
                vec![ResultIssue::Input(failure.issue).wire()],
            ));
        }
    };

    let inputs_json: Vec<Json> = checked
        .inputs()
        .iter()
        .map(|id| {
            let mut obj = JsonObject::from([
                ("id".into(), Json::str(&id.input)),
                ("bytes_digest".into(), Json::str(&id.bytes_digest)),
            ]);
            if let Some(md) = &id.model_digest {
                obj.insert("model_digest".into(), Json::str(md));
            }
            Json::Obj(obj)
        })
        .collect();

    let vocabs_json: Vec<Json> = checked
        .vocabularies()
        .values()
        .map(|v| {
            let deps = v.dependencies.iter().map(|b| b.wire()).collect();
            Json::obj([
                ("namespace", Json::str(&v.namespace)),
                ("version", Json::str(&v.version)),
                ("digest", Json::str(&v.digest)),
                ("dependencies", Json::Arr(deps)),
                ("manifest", v.manifest.clone()),
            ])
        })
        .collect();

    let doc = Json::obj([
        ("format", Json::str("archsig.digest/1")),
        ("semantics", Json::str(archsig_input::law::SEMANTICS)),
        ("inputs", Json::Arr(inputs_json)),
        ("vocabularies", Json::Arr(vocabs_json)),
    ]);

    Ok(CommandOutput {
        json: doc,
        exit_code: 0,
    })
}
