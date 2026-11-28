//! `archsig inspect --atom-definition D [--law L] [--archmap A]` の検査・要約出力。

use super::{CommandOutput, input_status, read_bounded, stopped};
use crate::cli::{InspectInputsArgs, emit_progress};
use crate::run::{Signals, output};
use archsig_common::canonical::{Json, JsonObject};
use archsig_common::control::{CheckFailure, Control};
use archsig_input::archmap::{Slot, check_archmap_controlled};
use archsig_input::definition::check_definitions_controlled;
use archsig_input::law::check_law_controlled;
use archsig_input::law::shigure::CheckedShigureDecls;
use archsig_input::result::ResultIssue;
use std::collections::BTreeMap;

pub fn execute(
    args: &InspectInputsArgs,
    max_file_bytes: u64,
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<CommandOutput, crate::run::Outcome> {
    emit_progress(&format!(
        "inspect: reading {} atom definition file(s)",
        args.atom_definitions.len()
    ));
    let mut def_bytes = Vec::with_capacity(args.atom_definitions.len());
    for (idx, path) in args.atom_definitions.iter().enumerate() {
        let bytes = read_bounded(path, max_file_bytes, signals)?;
        def_bytes.push((format!("definition{idx}"), bytes));
    }
    let law_bytes = match &args.law {
        Some(path) => Some(read_bounded(path, max_file_bytes, signals)?),
        None => None,
    };
    let map_bytes = match &args.archmap {
        Some(path) => Some(read_bounded(path, max_file_bytes, signals)?),
        None => None,
    };

    let def_refs: Vec<(&str, &[u8])> = def_bytes
        .iter()
        .map(|(id, bytes)| (id.as_str(), bytes.as_slice()))
        .collect();
    emit_progress("inspect: checking definitions");
    let definitions = match check_definitions_controlled(&def_refs, control) {
        Ok(d) => d,
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

    let checked_law = if let Some(bytes) = &law_bytes {
        emit_progress("inspect: checking law declarations");
        match check_law_controlled(bytes, &definitions, control) {
            Ok(law) => Some(law),
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
        }
    } else {
        None
    };

    let checked_map = if let Some(bytes) = &map_bytes {
        emit_progress("inspect: checking archmap");
        match check_archmap_controlled(bytes, &definitions, control) {
            Ok(map) => Some(map),
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
        }
    } else {
        None
    };

    let vocabs: Vec<Json> = definitions
        .vocabularies()
        .values()
        .map(|v| {
            Json::obj([
                ("namespace", Json::str(&v.namespace)),
                ("version", Json::str(&v.version)),
                ("digest", Json::str(&v.digest)),
            ])
        })
        .collect();

    let primitives: Vec<Json> = definitions
        .declarations()
        .values()
        .map(|d| {
            let field_names = d
                .signature
                .record_fields()
                .map(|(params, fields)| {
                    params
                        .iter()
                        .chain(fields.iter())
                        .map(|f| Json::str(&f.name))
                        .collect()
                })
                .unwrap_or_default();
            Json::obj([
                ("name", Json::str(&d.name)),
                ("namespace", Json::str(&d.namespace)),
                ("kind", Json::str(d.signature.kind())),
                ("fields", Json::Arr(field_names)),
            ])
        })
        .collect();

    let mut root = JsonObject::from([
        ("format".into(), Json::str("archsig.inspect/1")),
        ("semantics".into(), Json::str(archsig_input::law::SEMANTICS)),
        ("vocabularies".into(), Json::Arr(vocabs)),
        ("primitives".into(), Json::Arr(primitives)),
    ]);

    if let Some(law) = &checked_law {
        let decls: Vec<Json> = law
            .infos()
            .iter()
            .map(|info| {
                let mut obj = JsonObject::from([
                    ("name".into(), Json::str(&info.name)),
                    ("kind".into(), Json::str(info.kind)),
                ]);
                if let Some(ret) = &info.returns {
                    obj.insert("returns".into(), ret.wire());
                }
                Json::Obj(obj)
            })
            .collect();
        root.insert("declarations".into(), Json::Arr(decls));
        root.insert(
            "shigure_declarations".into(),
            shigure_decls_json(law.shigure()),
        );
    }

    if let Some(map) = &checked_map {
        let sources: Vec<Json> = map
            .sources()
            .iter()
            .map(|s| {
                Json::obj([
                    ("id", Json::str(&s.id)),
                    ("uri", Json::str(&s.uri)),
                    ("revision", Json::str(&s.revision)),
                    ("digest", Json::str(&s.digest)),
                ])
            })
            .collect();
        let origins: Vec<Json> = map
            .origins()
            .iter()
            .map(|o| {
                let mut obj = JsonObject::from([
                    ("id".into(), Json::str(&o.id)),
                    ("mode".into(), Json::str(o.mode.wire())),
                    ("method".into(), Json::str(&o.method)),
                ]);
                if let Some(kind) = o.kind {
                    obj.insert("kind".into(), Json::str(kind.wire()));
                }
                Json::Obj(obj)
            })
            .collect();

        let mut missing_slots = Vec::new();
        let snapshots: Vec<Json> = map
            .snapshots()
            .iter()
            .map(|snap| {
                let subjects: Vec<Json> = snap
                    .subjects
                    .iter()
                    .map(|subj| {
                        let mut known_fields = Vec::new();
                        let mut missing_fields = Vec::new();
                        for field in &subj.fields {
                            match &field.slot {
                                Slot::Known { atom, origin, .. } => {
                                    known_fields.push(Json::obj([
                                        ("field", Json::str(&field.name)),
                                        ("type", field.ty.wire()),
                                        ("atom", Json::str(atom)),
                                        ("origin", Json::str(origin)),
                                    ]));
                                }
                                Slot::Missing => {
                                    missing_fields.push(Json::obj([
                                        ("field", Json::str(&field.name)),
                                        ("type", field.ty.wire()),
                                    ]));
                                    missing_slots.push(Json::obj([
                                        ("snapshot", Json::str(&snap.id)),
                                        ("subject", Json::str(&subj.id)),
                                        ("type", Json::str(&subj.ty)),
                                        ("field", Json::str(&field.name)),
                                        ("field_type", field.ty.wire()),
                                    ]));
                                }
                            }
                        }
                        Json::obj([
                            ("id", Json::str(&subj.id)),
                            ("type", Json::str(&subj.ty)),
                            ("origin", Json::str(&subj.origin)),
                            ("known_fields", Json::Arr(known_fields)),
                            ("missing_fields", Json::Arr(missing_fields)),
                        ])
                    })
                    .collect();
                Json::obj([
                    ("id", Json::str(&snap.id)),
                    ("origin", Json::str(&snap.origin)),
                    ("subjects", Json::Arr(subjects)),
                ])
            })
            .collect();

        root.insert("sources".into(), Json::Arr(sources));
        root.insert("origins".into(), Json::Arr(origins));
        root.insert("snapshots".into(), Json::Arr(snapshots));
        root.insert("missing_slots".into(), Json::Arr(missing_slots));
    }

    Ok(CommandOutput {
        json: Json::Obj(root),
        exit_code: 0,
    })
}

fn shigure_decls_json(decls: &CheckedShigureDecls) -> Json {
    fn names<V>(map: &BTreeMap<String, V>) -> Vec<Json> {
        map.keys().map(Json::str).collect()
    }
    let categories: [(&str, Vec<Json>); 20] = [
        ("presentations", names(&decls.presentations)),
        ("comparisons", names(&decls.comparisons)),
        ("change_specs", names(&decls.change_specs)),
        ("eval_conditions", names(&decls.eval_conditions)),
        ("tasks", names(&decls.tasks)),
        ("diagrams", names(&decls.diagrams)),
        ("paths", names(&decls.paths)),
        ("transfers", names(&decls.transfers)),
        ("families", names(&decls.families)),
        ("robustness_tasks", names(&decls.robustness_tasks)),
        ("chevalley_tasks", names(&decls.chevalley_tasks)),
        ("observation_tasks", names(&decls.observation_tasks)),
        ("lift_tasks", names(&decls.lift_tasks)),
        ("artin_tasks", names(&decls.artin_tasks)),
        ("diagnostics_tasks", names(&decls.diagnostics_tasks)),
        ("atlas_tasks", names(&decls.atlas_tasks)),
        ("occurrence_tasks", names(&decls.occurrence_tasks)),
        ("partial_tasks", names(&decls.partial_tasks)),
        ("revision_tasks", names(&decls.revision_tasks)),
        ("multisource_tasks", names(&decls.multisource_tasks)),
    ];
    let total_count: usize = categories.iter().map(|(_, v)| v.len()).sum();
    let mut obj = JsonObject::from([("total_count".into(), Json::Nat(total_count as u64))]);
    for (key, vals) in categories {
        obj.insert(key.into(), Json::Arr(vals));
    }
    Json::Obj(obj)
}
