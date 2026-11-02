use super::*;
use archsig_common::canonical::sha256_digest;

fn index(node: &JNode) -> Result<BTreeMap<&str, &JNode>> {
    let mut result = BTreeMap::new();
    for item in arr(node)? {
        let id = token(field(item, "id")?)?;
        if result.insert(id, item).is_some() {
            return Err(invalid(format!("duplicate id: {id}")));
        }
    }
    Ok(result)
}
fn lookup<'a>(index: &BTreeMap<&str, &'a JNode>, id: &str) -> Result<&'a JNode> {
    index
        .get(id)
        .copied()
        .ok_or_else(|| invalid(format!("missing reference: {id}")))
}

pub(super) fn expand(
    map: &JNode,
    selected: &[String],
    files: &BTreeMap<String, PathBuf>,
) -> Result<String> {
    let sources = index(field(map, "sources")?)?;
    let origins = index(field(map, "origins")?)?;
    let snapshots = index(field(map, "snapshots")?)?;
    let mut atoms = Vec::new();
    let mut used_origins = Vec::new();
    let mut expanded_origins = Vec::new();
    let mut used_sources: Vec<(&str, &JNode, String)> = Vec::new();
    for selector in selected {
        let (snapshot, atom_id) = selector
            .split_once('/')
            .ok_or_else(|| invalid("invalid atom selector"))?;
        let snapshot_node = lookup(&snapshots, snapshot)?;
        let atom_index = index(field(snapshot_node, "atoms")?)?;
        let atom = lookup(&atom_index, atom_id)?;
        atoms.push(augmented(
            atom,
            &[("snapshot", Json::str(snapshot).canonical())],
        )?);
        let origin_id = token(field(atom, "origin")?)?;
        if used_origins.contains(&origin_id) {
            continue;
        }
        let origin = lookup(&origins, origin_id)?;
        let mut locations = Vec::new();
        for location in arr(field(origin, "locations")?)? {
            let source_id = token(field(location, "source")?)?;
            if !used_sources.iter().any(|(id, _, _)| *id == source_id) {
                let source = lookup(&sources, source_id)?;
                let path = files
                    .get(source_id)
                    .ok_or_else(|| invalid(format!("missing source binding: {source_id}")))?;
                let bytes = read(path)?;
                let text = String::from_utf8(bytes)
                    .map_err(|_| invalid(format!("source is not UTF-8: {source_id}")))?;
                if token(field(source, "digest")?)? != sha256_digest(text.as_bytes()) {
                    return Err(invalid(format!("source digest mismatch: {source_id}")));
                }
                used_sources.push((source_id, source, text));
            }
            let (_, _, text) = used_sources
                .iter()
                .find(|(id, _, _)| *id == source_id)
                .expect("source inserted above");
            let span = obj(location)?
                .iter()
                .find(|(key, _)| key == "span")
                .map(|(_, node)| node);
            let (start, end) = if let Some(span) = span {
                let parts = arr(span)?;
                let offset = |node: &JNode| -> Result<usize> {
                    if let JValue::Num(n) = &node.value {
                        if n == "-0" {
                            return Ok(0);
                        }
                        if n.bytes().all(|b| b.is_ascii_digit())
                            && let Ok(n) = n.parse()
                        {
                            return Ok(n);
                        }
                    }
                    Err(invalid(format!("invalid byte span: {origin_id}")))
                };
                if parts.len() != 2 {
                    return Err(invalid(format!("invalid byte span: {origin_id}")));
                }
                (offset(&parts[0])?, offset(&parts[1])?)
            } else {
                (0, text.len())
            };
            let excerpt = text
                .get(start..end)
                .ok_or_else(|| invalid(format!("invalid UTF-8 byte span: {origin_id}")))?;
            locations.push(augmented(
                location,
                &[
                    ("resolved_span", format!("[{start},{end}]")),
                    ("excerpt", Json::str(excerpt).canonical()),
                ],
            )?);
        }
        used_origins.push(origin_id);
        expanded_origins.push(augmented(
            origin,
            &[("locations", format!("[{}]", locations.join(",")))],
        )?);
    }
    Ok(object([
        ("atoms", format!("[{}]", atoms.join(","))),
        ("origins", format!("[{}]", expanded_origins.join(","))),
        ("sources", format!("[{}]", used_sources.iter().map(|(_,node,_)| encode(node)).collect::<Vec<_>>().join(","))),
        ("verification", Json::str("Local bytes match declared file digests and spans. Revision provenance, reading coverage, meaning and Law fidelity are not verified.").canonical()),
    ]))
}
