//! ArchMap の canonical JSON(入力仕様 §4)。集合表と Set/Map 値を正規化する。

use super::{CheckedArchMap, FORMAT, Origin, SEMANTICS, Slot, Snapshot, Source, Subject};
use crate::{
    canonical::Json,
    issue::Issue,
    json::InputError,
    observed::control::{Checkpoint, Control},
};
use std::collections::BTreeMap;

/// 集合表を ID・namespace 名順へ、Set・Map の値を canonical 値順へ並べた ArchMap。
pub fn model_json(a: &CheckedArchMap) -> Json {
    model_json_controlled::<Box<Issue>>(a, &mut Control::unlimited())
        .expect("unlimited ArchMap canonicalization")
}

pub(crate) fn model_json_controlled<E: InputError>(
    a: &CheckedArchMap,
    control: &mut Control,
) -> Result<Json, E> {
    let point = Checkpoint::ArchMapCanonical;
    E::checkpoint(control, point)?;
    let mut sources: Vec<&Source> = Vec::new();
    for source in &a.sources {
        E::checkpoint(control, point)?;
        sources.push(source);
        E::checkpoint(control, point)?;
    }
    sources.sort_by(|x, y| x.id.cmp(&y.id));
    E::checkpoint(control, point)?;
    let mut origins: Vec<&Origin> = Vec::new();
    for origin in &a.origins {
        E::checkpoint(control, point)?;
        origins.push(origin);
        E::checkpoint(control, point)?;
    }
    origins.sort_by(|x, y| x.id.cmp(&y.id));
    E::checkpoint(control, point)?;
    let mut snapshots: Vec<&Snapshot> = Vec::new();
    for snapshot in &a.snapshots {
        E::checkpoint(control, point)?;
        snapshots.push(snapshot);
        E::checkpoint(control, point)?;
    }
    snapshots.sort_by(|x, y| x.id.cmp(&y.id));
    E::checkpoint(control, point)?;
    let mut vocabularies = Vec::new();
    for binding in a.vocabularies.values() {
        E::checkpoint(control, point)?;
        vocabularies.push(binding.wire());
        E::checkpoint(control, point)?;
    }
    let mut source_json = Vec::new();
    for source in sources {
        E::checkpoint(control, point)?;
        source_json.push(Json::obj([
            ("id", Json::str(source.id.clone())),
            ("uri", Json::str(source.uri.clone())),
            ("revision", Json::str(source.revision.clone())),
            ("digest", Json::str(source.digest.clone())),
        ]));
        E::checkpoint(control, point)?;
    }
    let mut origin_json = Vec::new();
    for origin in origins {
        E::checkpoint(control, point)?;
        let mut object = BTreeMap::new();
        object.insert("id".to_owned(), Json::str(origin.id.clone()));
        object.insert("mode".to_owned(), Json::str(origin.mode.wire()));
        object.insert("method".to_owned(), Json::str(origin.method.clone()));
        let mut locations = Vec::new();
        for location in &origin.locations {
            E::checkpoint(control, point)?;
            let mut value = BTreeMap::new();
            value.insert("source".to_owned(), Json::str(location.source.clone()));
            value.insert("path".to_owned(), Json::str(location.path.clone()));
            if let Some((start, end)) = location.span {
                value.insert(
                    "span".to_owned(),
                    Json::Arr(vec![Json::Nat(start), Json::Nat(end)]),
                );
            }
            locations.push(Json::Obj(value));
            E::checkpoint(control, point)?;
        }
        object.insert("locations".to_owned(), Json::Arr(locations));
        if let Some(note) = &origin.note {
            object.insert("note".to_owned(), Json::str(note.clone()));
        }
        origin_json.push(Json::Obj(object));
        E::checkpoint(control, point)?;
    }
    let mut snapshot_json = Vec::new();
    for snapshot in snapshots {
        E::checkpoint(control, point)?;
        let mut subjects: Vec<&Subject> = Vec::new();
        for subject in &snapshot.subjects {
            E::checkpoint(control, point)?;
            subjects.push(subject);
            E::checkpoint(control, point)?;
        }
        subjects.sort_by(|x, y| x.id.cmp(&y.id));
        E::checkpoint(control, point)?;
        let mut atoms: Vec<(String, Json)> = Vec::new();
        for subject in &snapshot.subjects {
            E::checkpoint(control, point)?;
            for field in &subject.fields {
                E::checkpoint(control, point)?;
                if let Slot::Known {
                    atom,
                    origin,
                    value,
                    ..
                } = &field.slot
                {
                    atoms.push((
                        atom.clone(),
                        Json::obj([
                            ("id", Json::str(atom.clone())),
                            ("subject", Json::str(subject.id.clone())),
                            ("field", Json::str(field.name.clone())),
                            ("value", value.canonical_json_controlled::<E>(control)?),
                            ("origin", Json::str(origin.clone())),
                        ]),
                    ));
                }
                E::checkpoint(control, point)?;
            }
            E::checkpoint(control, point)?;
        }
        atoms.sort_by(|x, y| x.0.cmp(&y.0));
        E::checkpoint(control, point)?;
        let mut subject_json = Vec::new();
        for subject in subjects {
            E::checkpoint(control, point)?;
            subject_json.push(Json::obj([
                ("id", Json::str(subject.id.clone())),
                ("type", Json::str(subject.ty.clone())),
                ("origin", Json::str(subject.origin.clone())),
            ]));
            E::checkpoint(control, point)?;
        }
        let mut atom_json = Vec::new();
        for (_, atom) in atoms {
            E::checkpoint(control, point)?;
            atom_json.push(atom);
            E::checkpoint(control, point)?;
        }
        snapshot_json.push(Json::obj([
            ("id", Json::str(snapshot.id.clone())),
            ("origin", Json::str(snapshot.origin.clone())),
            ("subjects", Json::Arr(subject_json)),
            ("atoms", Json::Arr(atom_json)),
        ]));
        E::checkpoint(control, point)?;
    }
    let json = Json::obj([
        ("format", Json::str(FORMAT)),
        ("semantics", Json::str(SEMANTICS)),
        ("vocabularies", Json::Arr(vocabularies)),
        ("sources", Json::Arr(source_json)),
        ("origins", Json::Arr(origin_json)),
        ("snapshots", Json::Arr(snapshot_json)),
    ]);
    E::checkpoint(control, point)?;
    Ok(json)
}
