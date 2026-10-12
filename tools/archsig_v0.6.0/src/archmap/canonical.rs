//! ArchMap の canonical JSON(入力仕様 §4)。集合表と Set/Map 値を正規化する。

use super::{CheckedArchMap, FORMAT, Origin, SEMANTICS, Slot, Snapshot, Source, Subject};
use crate::canonical::Json;
use std::collections::BTreeMap;

/// 集合表を ID・reading 名順へ、Set・Map の値を canonical 値順へ並べた ArchMap。
pub fn model_json(a: &CheckedArchMap) -> Json {
    let mut sources: Vec<&Source> = a.sources.iter().collect();
    sources.sort_by(|x, y| x.id.cmp(&y.id));
    let mut origins: Vec<&Origin> = a.origins.iter().collect();
    origins.sort_by(|x, y| x.id.cmp(&y.id));
    let mut snapshots: Vec<&Snapshot> = a.snapshots.iter().collect();
    snapshots.sort_by(|x, y| x.id.cmp(&y.id));
    let vocabularies = a
        .vocabularies
        .iter()
        .map(|(r, d)| {
            Json::obj([
                ("reading", Json::str(r.clone())),
                ("digest", Json::str(d.clone())),
            ])
        })
        .collect();
    let sources = sources
        .into_iter()
        .map(|s| {
            Json::obj([
                ("id", Json::str(s.id.clone())),
                ("uri", Json::str(s.uri.clone())),
                ("revision", Json::str(s.revision.clone())),
                ("digest", Json::str(s.digest.clone())),
            ])
        })
        .collect();
    let origins = origins
        .into_iter()
        .map(|o| {
            let mut m = BTreeMap::new();
            m.insert("id".to_owned(), Json::str(o.id.clone()));
            m.insert("mode".to_owned(), Json::str(o.mode.wire()));
            m.insert("method".to_owned(), Json::str(o.method.clone()));
            m.insert(
                "locations".to_owned(),
                Json::Arr(
                    o.locations
                        .iter()
                        .map(|l| {
                            let mut m = BTreeMap::new();
                            m.insert("source".to_owned(), Json::str(l.source.clone()));
                            m.insert("path".to_owned(), Json::str(l.path.clone()));
                            if let Some((s, e)) = l.span {
                                m.insert(
                                    "span".to_owned(),
                                    Json::Arr(vec![Json::Nat(s), Json::Nat(e)]),
                                );
                            }
                            Json::Obj(m)
                        })
                        .collect(),
                ),
            );
            if let Some(n) = &o.note {
                m.insert("note".to_owned(), Json::str(n.clone()));
            }
            Json::Obj(m)
        })
        .collect();
    let snapshots = snapshots
        .into_iter()
        .map(|s| {
            let mut subjects: Vec<&Subject> = s.subjects.iter().collect();
            subjects.sort_by(|x, y| x.id.cmp(&y.id));
            let mut atoms: Vec<(String, Json)> = Vec::new();
            for sub in &s.subjects {
                for f in &sub.fields {
                    if let Slot::Known {
                        atom,
                        origin,
                        value,
                        ..
                    } = &f.slot
                    {
                        atoms.push((
                            atom.clone(),
                            Json::obj([
                                ("id", Json::str(atom.clone())),
                                ("subject", Json::str(sub.id.clone())),
                                ("field", Json::str(f.name.clone())),
                                ("value", value.canonical_json()),
                                ("origin", Json::str(origin.clone())),
                            ]),
                        ));
                    }
                }
            }
            atoms.sort_by(|x, y| x.0.cmp(&y.0));
            Json::obj([
                ("id", Json::str(s.id.clone())),
                ("origin", Json::str(s.origin.clone())),
                (
                    "subjects",
                    Json::Arr(
                        subjects
                            .into_iter()
                            .map(|x| {
                                Json::obj([
                                    ("id", Json::str(x.id.clone())),
                                    ("type", Json::str(x.ty.clone())),
                                    ("origin", Json::str(x.origin.clone())),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "atoms",
                    Json::Arr(atoms.into_iter().map(|(_, j)| j).collect()),
                ),
            ])
        })
        .collect();
    Json::obj([
        ("format", Json::str(FORMAT)),
        ("semantics", Json::str(SEMANTICS)),
        ("vocabularies", Json::Arr(vocabularies)),
        ("sources", Json::Arr(sources)),
        ("origins", Json::Arr(origins)),
        ("snapshots", Json::Arr(snapshots)),
    ])
}
