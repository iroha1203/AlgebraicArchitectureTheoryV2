//! 保存結果には値の参照グラフを残し、導出グラフを公開しない。
use super::{Node, NodeType};
use crate::{
    canonical::Json,
    observed::control::{Checkpoint, Control, StopReason},
};
use std::collections::{BTreeMap, BTreeSet};

fn refs(value: &Json, into: &mut BTreeSet<String>) {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Obj(fields) => {
            if fields.len() == 1
                && let Some(Json::Str(id)) = fields.get("node")
            {
                into.insert(id.clone());
            } else {
                for value in fields.values() {
                    refs(value, into);
                }
            }
        }
        Json::Arr(items) => {
            for value in items {
                refs(value, into);
            }
        }
        _ => {}
    });
}
fn rename(value: &mut Json, ids: &BTreeMap<String, String>) {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Obj(fields) => {
            if fields.len() == 1
                && let Some(Json::Str(id)) = fields.get_mut("node")
            {
                *id = ids[id].clone();
            } else {
                for value in fields.values_mut() {
                    rename(value, ids);
                }
            }
        }
        Json::Arr(items) => {
            for value in items {
                rename(value, ids);
            }
        }
        _ => {}
    });
}
fn retain_examples(fields: &mut BTreeMap<String, Json>, examples: &BTreeSet<String>) {
    let Some(mut evidence) = fields.remove("evidence") else {
        return;
    };
    let Json::Arr(values) = &mut evidence else {
        unreachable!()
    };
    values.retain(|value| {
        let Json::Obj(reference) = value else {
            return false;
        };
        matches!(reference.get("node"), Some(Json::Str(id)) if examples.contains(id))
    });
    if !values.is_empty() {
        fields.insert("counterexamples".into(), evidence);
    }
}
pub(super) fn compact(
    result: &mut Json,
    native: &[Node],
    control: &mut Control,
    point: Checkpoint,
) -> Result<(), StopReason> {
    let Json::Obj(document) = result else {
        unreachable!()
    };
    let mut old = document.remove("nodes").unwrap();
    let Json::Arr(old) = &mut old else {
        unreachable!()
    };
    let examples = old
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            if native[index].ty != NodeType::Evidence {
                return None;
            }
            let Json::Obj(fields) = node else {
                unreachable!()
            };
            let Some(Json::Obj(value)) = fields.get("value") else {
                return None;
            };
            matches!(value.get("kind"), Some(Json::Str(kind)) if matches!(kind.as_str(),
            "counterexample" | "completion_pair" | "separating_pair"))
            .then(|| format!("n{index}"))
        })
        .collect();
    let Json::Arr(answers) = document.get_mut("answers").unwrap() else {
        unreachable!()
    };
    for answer in answers {
        let Json::Obj(answer) = answer else {
            unreachable!()
        };
        retain_examples(answer, &examples);
    }
    for (index, node) in old.iter_mut().enumerate() {
        control.checkpoint(point)?;
        let Json::Obj(fields) = node else {
            unreachable!()
        };
        for key in ["rule", "arguments", "evidence", "scope", "support"] {
            fields.remove(key);
        }
        if let Some(Json::Obj(judgment)) = fields.get_mut("judgment") {
            retain_examples(judgment, &examples);
        }
        if native[index].ty == NodeType::Evidence {
            fields.insert("type".into(), Json::str("Counterexample"));
        }
        if let Some(Json::Obj(value)) = fields.get_mut("value") {
            match native[index].ty {
                NodeType::Construction(_) => {
                    value.remove("construction");
                }
                NodeType::Evidence => {
                    value.remove("evaluation");
                }
                _ => {}
            }
        }
    }
    let mut reachable = BTreeSet::new();
    for value in document.values() {
        refs(value, &mut reachable);
    }
    // 部分結果の理由には後続の診断への参照もある。到達順を計算順と同一視しない。
    let mut pending: Vec<_> = reachable.iter().cloned().collect();
    while let Some(id) = pending.pop() {
        control.checkpoint(point)?;
        let index: usize = id.strip_prefix('n').unwrap().parse().unwrap();
        let mut children = BTreeSet::new();
        refs(&old[index], &mut children);
        for child in children {
            if reachable.insert(child.clone()) {
                pending.push(child);
            }
        }
    }
    let mut ids: BTreeMap<_, _> = reachable
        .iter()
        .map(|id| (id.clone(), id.clone()))
        .collect();
    let mut values = BTreeMap::<String, String>::new();
    let mut nodes = Vec::new();
    for (index, mut node) in std::mem::take(old).into_iter().enumerate() {
        control.checkpoint(point)?;
        let old_id = format!("n{index}");
        if !reachable.contains(&old_id) {
            continue;
        }
        rename(&mut node, &ids);
        let shared = matches!(
            native[index].ty,
            NodeType::Value(_)
                | NodeType::Vector(_)
                | NodeType::ModuleMap(_, _)
                | NodeType::Domain
                | NodeType::Construction(
                    super::super::construction_result::ConstructionType::StateMap
                )
        );
        let Json::Obj(fields) = &mut node else {
            unreachable!()
        };
        fields.remove("id");
        let key = shared.then(|| node.canonical());
        if let Some(existing) = key.as_ref().and_then(|key| values.get(key)) {
            ids.insert(old_id, existing.clone());
            continue;
        }
        let Json::Obj(fields) = &mut node else {
            unreachable!()
        };
        fields.insert("id".into(), Json::str(&old_id));
        if let Some(key) = key {
            values.insert(key, old_id.clone());
        }
        nodes.push(node);
    }
    let numbered: BTreeMap<String, String> = nodes
        .iter()
        .enumerate()
        .map(|(index, node)| {
            let Json::Obj(fields) = node else {
                unreachable!()
            };
            let Json::Str(id) = &fields["id"] else {
                unreachable!()
            };
            (id.clone(), format!("n{index}"))
        })
        .collect();
    for id in ids.values_mut() {
        *id = numbered[id].clone();
    }
    for node in &mut nodes {
        rename(node, &ids);
        let Json::Obj(fields) = node else {
            unreachable!()
        };
        let Json::Str(id) = fields.get_mut("id").unwrap() else {
            unreachable!()
        };
        *id = numbered[id].clone();
    }
    for value in document.values_mut() {
        rename(value, &ids);
    }
    document.insert("nodes".into(), Json::Arr(nodes));
    Ok(())
}
