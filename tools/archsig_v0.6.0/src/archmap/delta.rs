//! Snapshotの略記を展開し、全量入力と同じ検査へ渡す。
use super::*;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

struct Patch<T> {
    put: Vec<T>,
    remove: Vec<String>,
}
enum Input<'a> {
    Full(RawSnapshot<'a>),
    Delta {
        id: String,
        origin: String,
        pointer: String,
        base: String,
        subjects: Patch<RawSubject>,
        atoms: Patch<RawAtom<'a>>,
    },
}
impl Input<'_> {
    fn id(&self) -> &str {
        match self {
            Self::Full(s) => &s.id,
            Self::Delta { id, .. } => id,
        }
    }
}
fn subjects<E: InputError>(
    items: &[JNode],
    ptr: &str,
    c: &mut Control,
) -> Result<Vec<RawSubject>, E> {
    let mut result = vec![];
    let mut ids = HashSet::new();
    for (i, node) in items.iter().enumerate() {
        E::checkpoint(c, Checkpoint::ArchMapIteration)?;
        let p = format!("{ptr}/{i}");
        let o = Obj::<E>::new(node, &p, &["id", "type", "origin"], &[], c)?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err(issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("duplicate subject `{id}`"),
            )
            .into());
        }
        let ty = o.string("type")?;
        qname::<E>(
            &ty,
            c,
            Some(&|| syntax(&format!("{p}/type"), "type must be a fully qualified declaration name")),
        )?;
        result.push(RawSubject {
            id,
            ty,
            origin: o.id("origin")?,
            pointer: p,
        });
    }
    Ok(result)
}
fn atoms<'a, E: InputError>(
    items: &'a [JNode],
    ptr: &str,
    c: &mut Control,
) -> Result<Vec<RawAtom<'a>>, E> {
    let mut result = vec![];
    let mut ids = HashSet::new();
    for (i, node) in items.iter().enumerate() {
        E::checkpoint(c, Checkpoint::ArchMapIteration)?;
        let p = format!("{ptr}/{i}");
        let o = Obj::<E>::new(
            node,
            &p,
            &["id", "subject", "field", "value", "origin"],
            &[],
            c,
        )?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err(issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("duplicate Atom `{id}`"),
            )
            .into());
        }
        let field = o.string("field")?;
        qname::<E>(
            &field,
            c,
            Some(&|| syntax(&format!("{p}/field"), "field must be a fully qualified name")),
        )?;
        result.push(RawAtom {
            id,
            subject: o.id("subject")?,
            field,
            value: o.req("value")?.0,
            rebases: vec![],
            origin: o.id("origin")?,
            pointer: p,
        });
    }
    Ok(result)
}
fn patch<'a, T, E: InputError>(
    field: Option<(&'a JNode, String)>,
    c: &mut Control,
    read: impl FnOnce(&'a [JNode], &str, &mut Control) -> Result<Vec<T>, E>,
    id: impl Fn(&T) -> &str,
) -> Result<Patch<T>, E> {
    let Some((node, p)) = field else {
        return Ok(Patch {
            put: vec![],
            remove: vec![],
        });
    };
    let o = Obj::<E>::new(node, &p, &[], &["put", "remove"], c)?;
    let put = if o.get("put")?.is_some() {
        let (items, ptr) = o.array("put")?;
        read(items, &ptr, c)?
    } else {
        vec![]
    };
    let mut remove = vec![];
    let mut seen = BTreeSet::new();
    for value in &put {
        E::checkpoint(c, Checkpoint::ArchMapIteration)?;
        seen.insert(id(value).to_owned());
    }
    if o.get("remove")?.is_some() {
        let (items, ptr) = o.array("remove")?;
        for (i, node) in items.iter().enumerate() {
            E::checkpoint(c, Checkpoint::ArchMapIteration)?;
            let p = format!("{ptr}/{i}");
            let name = as_string(node, &p)?;
            identifier::<E>(&name, true, c, Some(&|| syntax(&p, "deletion target must be an Id")))?;
            if !seen.insert(name.clone()) {
                return Err(issue(Code::DuplicateId, &p, "cannot modify or delete the same ID more than once").into());
            }
            remove.push(name);
        }
    }
    Ok(Patch { put, remove })
}
pub(super) fn read_snapshots<'a, E: InputError>(
    items: &'a [JNode],
    ptr: &str,
    c: &mut Control,
) -> Result<Vec<RawSnapshot<'a>>, E> {
    let mut inputs = vec![];
    let mut ids = BTreeMap::new();
    for (i, node) in items.iter().enumerate() {
        E::checkpoint(c, Checkpoint::ArchMapIteration)?;
        let p = format!("{ptr}/{i}");
        let delta = match &node.value {
            JValue::Obj(entries) => field::<E>(entries, "base", c)?.is_some(),
            _ => false,
        };
        let o = if delta {
            Obj::<E>::new(
                node,
                &p,
                &["id", "origin", "base"],
                &["subjects", "atoms"],
                c,
            )?
        } else {
            Obj::<E>::new(node, &p, &["id", "origin", "subjects", "atoms"], &[], c)?
        };
        let id = o.id("id")?;
        if ids.insert(id.clone(), i).is_some() {
            return Err(issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("duplicate snapshot `{id}`"),
            )
            .into());
        }
        let origin = o.id("origin")?;
        let input = if delta {
            Input::Delta {
                id,
                origin,
                pointer: p,
                base: o.id("base")?,
                subjects: patch(o.get("subjects")?, c, subjects::<E>, |v| &v.id)?,
                atoms: patch(o.get("atoms")?, c, atoms::<E>, |v| &v.id)?,
            }
        } else {
            let (subs, sp) = o.array("subjects")?;
            let subjects = subjects::<E>(subs, &sp, c)?;
            let (ats, ap) = o.array("atoms")?;
            Input::Full(RawSnapshot {
                id,
                origin,
                pointer: p,
                subjects,
                atoms: atoms::<E>(ats, &ap, c)?,
            })
        };
        inputs.push(Some(input));
    }
    // 表の順序に意味を持たせず、再帰を使わず基準から展開する。
    let mut children = vec![vec![]; inputs.len()];
    let mut ready = VecDeque::new();
    for (i, input) in inputs.iter().enumerate() {
        E::checkpoint(c, Checkpoint::ArchMapIteration)?;
        match input.as_ref().expect("未展開入力") {
            Input::Full(_) => ready.push_back(i),
            Input::Delta { base, pointer, .. } => {
                let parent = ids.get(base).ok_or_else(|| {
                    E::from(issue(
                        Code::Reference,
                        &format!("{pointer}/base"),
                        format!("base snapshot `{base}` does not exist"),
                    ))
                })?;
                children[*parent].push(i);
            }
        }
    }
    let mut expanded: Vec<Option<RawSnapshot<'a>>> = (0..inputs.len()).map(|_| None).collect();
    while let Some(i) = ready.pop_front() {
        E::checkpoint(c, Checkpoint::ArchMapIteration)?;
        let input = inputs[i].take().expect("展開は一度だけ");
        let snapshot = match input {
            Input::Full(snapshot) => snapshot,
            Input::Delta {
                id,
                origin,
                pointer,
                base,
                subjects,
                atoms,
            } => {
                let parent = expanded[ids[&base]].as_ref().expect("基準を先に展開");
                let mut subject_table = BTreeMap::new();
                for s in &parent.subjects {
                    E::checkpoint(c, Checkpoint::ArchMapIteration)?;
                    subject_table.insert(s.id.clone(), s.clone());
                }
                let mut removed = BTreeSet::new();
                for name in subjects.remove {
                    E::checkpoint(c, Checkpoint::ArchMapIteration)?;
                    if subject_table.remove(&name).is_none() {
                        return Err(issue(
                            Code::Reference,
                            &format!("{pointer}/subjects/remove"),
                            format!("subject `{name}` to delete does not exist"),
                        )
                        .into());
                    }
                    removed.insert(name);
                }
                for s in subjects.put {
                    E::checkpoint(c, Checkpoint::ArchMapIteration)?;
                    subject_table.insert(s.id.clone(), s);
                }
                let mut atom_table = BTreeMap::new();
                for atom in &parent.atoms {
                    E::checkpoint(c, Checkpoint::ArchMapIteration)?;
                    if removed.contains(&atom.subject) {
                        continue;
                    }
                    let mut atom = atom.clone();
                    atom.rebases.push((base.clone(), id.clone()));
                    atom_table.insert(atom.id.clone(), atom);
                }
                for name in atoms.remove {
                    E::checkpoint(c, Checkpoint::ArchMapIteration)?;
                    if atom_table.remove(&name).is_none() {
                        return Err(issue(
                            Code::Reference,
                            &format!("{pointer}/atoms/remove"),
                            format!("Atom `{name}` to delete does not exist"),
                        )
                        .into());
                    }
                }
                for atom in atoms.put {
                    E::checkpoint(c, Checkpoint::ArchMapIteration)?;
                    atom_table.insert(atom.id.clone(), atom);
                }
                RawSnapshot {
                    id,
                    origin,
                    pointer,
                    subjects: subject_table.into_values().collect(),
                    atoms: atom_table.into_values().collect(),
                }
            }
        };
        expanded[i] = Some(snapshot);
        for &child in &children[i] {
            E::checkpoint(c, Checkpoint::ArchMapIteration)?;
            ready.push_back(child);
        }
    }
    if let Some(input) = inputs.iter().flatten().next() {
        return Err(issue(
            Code::Reference,
            ptr,
            format!("cyclic base references involving snapshot `{}`", input.id()),
        )
        .into());
    }
    E::checkpoint(c, Checkpoint::ArchMapIteration)?;
    Ok(expanded
        .into_iter()
        .map(|s| s.expect("全基準展開済み"))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::control::{CheckFailure, Limits, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};

    #[test]
    fn delta_expansion_obeys_the_shared_stop_at_each_iteration() {
        let root=crate::json::parse(br#"[{"id":"v","origin":"o","subjects":[{"id":"r","type":"V.Root","origin":"o"}],"atoms":[]},{"id":"w","origin":"o","base":"v"},{"id":"x","origin":"o","base":"w"}]"#).unwrap();
        let JValue::Arr(items) = &root.value else {
            panic!()
        };
        let run = |at: Option<usize>| {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let mut control = Control::new(Limits::default(), move |point| {
                if point == Checkpoint::ArchMapIteration {
                    count.set(count.get() + 1);
                }
                Usage {
                    signal: at.filter(|n| *n == count.get()).map(|_| Signal::Term),
                    ..Usage::default()
                }
            });
            let result =
                read_snapshots::<CheckFailure<Box<Issue>>>(items, "/snapshots", &mut control);
            (result, seen.get())
        };
        let (complete, count) = run(None);
        assert_eq!(complete.unwrap().len(), 3);
        for at in 1..=count {
            assert!(
                matches!(run(Some(at)).0, Err(CheckFailure::Stopped(_))),
                "checkpoint {at}"
            );
        }
    }
}
