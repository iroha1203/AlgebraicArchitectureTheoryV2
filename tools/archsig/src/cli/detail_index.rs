fn default_detail_index_path(packet_path: &Path) -> PathBuf {
    let stem = packet_path
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("archsig-analysis-packet");
    let file_name = format!("{stem}-detail-index.json");
    packet_path.with_file_name(file_name)
}

struct CompactRefContext {
    detail_ref_base: String,
    next_ref_set: usize,
    ref_set_by_hash: BTreeMap<u64, Vec<String>>,
    ref_sets: BTreeMap<String, CompactRefSet>,
}

struct CompactRefSet {
    item_count: usize,
    sample_refs: Vec<String>,
    refs: Vec<String>,
    json_pointers: Vec<String>,
}

impl CompactRefContext {
    fn new(detail_ref_base: String) -> Self {
        Self {
            detail_ref_base,
            next_ref_set: 1,
            ref_set_by_hash: BTreeMap::new(),
            ref_sets: BTreeMap::new(),
        }
    }

    fn intern_ref_set(
        &mut self,
        refs: Vec<String>,
        json_pointer: String,
    ) -> (String, usize, Vec<String>) {
        let hash = hash_refs(&refs);
        let ref_set_id = self
            .ref_set_by_hash
            .get(&hash)
            .and_then(|candidate_ids| {
                candidate_ids.iter().find_map(|candidate_id| {
                    self.ref_sets
                        .get(candidate_id)
                        .filter(|candidate| candidate.refs == refs)
                        .map(|_| candidate_id.clone())
                })
            })
            .unwrap_or_else(|| {
                let id = format!("refset:{:06}", self.next_ref_set);
                self.next_ref_set += 1;
                self.ref_set_by_hash
                    .entry(hash)
                    .or_default()
                    .push(id.clone());
                self.ref_sets.insert(
                    id.clone(),
                    CompactRefSet {
                        item_count: refs.len(),
                        sample_refs: refs
                            .iter()
                            .take(COMPACT_REF_SAMPLE_COUNT)
                            .cloned()
                            .collect(),
                        refs,
                        json_pointers: Vec::new(),
                    },
                );
                id
            });
        let ref_set = self
            .ref_sets
            .get_mut(&ref_set_id)
            .expect("interned ref set must exist");
        ref_set.json_pointers.push(json_pointer);
        (ref_set_id, ref_set.item_count, ref_set.sample_refs.clone())
    }

    fn detail_ref(&self, ref_set_id: &str) -> String {
        format!("{}#{}", self.detail_ref_base, ref_set_id)
    }

    fn detail_index_value(&self) -> serde_json::Value {
        let mut dictionary_by_ref = BTreeMap::<String, usize>::new();
        let mut ref_dictionary = Vec::<String>::new();
        for ref_set in self.ref_sets.values() {
            for ref_value in &ref_set.refs {
                if !dictionary_by_ref.contains_key(ref_value) {
                    let index = ref_dictionary.len();
                    dictionary_by_ref.insert(ref_value.clone(), index);
                    ref_dictionary.push(ref_value.clone());
                }
            }
        }
        let ref_sets = self
            .ref_sets
            .iter()
            .map(|(ref_set_id, ref_set)| {
                let ref_indexes = ref_set
                    .refs
                    .iter()
                    .filter_map(|ref_value| dictionary_by_ref.get(ref_value).copied())
                    .collect::<Vec<_>>();
                serde_json::json!({
                    "refSetId": ref_set_id,
                    "refCount": ref_set.item_count,
                    "jsonPointers": ref_set.json_pointers,
                    "refIndexes": ref_indexes,
                })
            })
            .collect::<Vec<_>>();
        serde_json::json!({
            "schemaVersion": "archsig-analysis-detail-index-v0",
            "indexKind": "deduplicated-string-ref-set-dictionary",
            "compactThreshold": COMPACT_REF_ARRAY_THRESHOLD,
            "refSetCount": self.ref_sets.len(),
            "refDictionary": ref_dictionary,
            "refSets": ref_sets,
            "nonConclusions": [
                "detail index preserves full string reference sets omitted from the compact analysis packet",
                "refSets[].refIndexes indexes into refDictionary and preserves ref order inside each set",
                "detail refs are evidence navigation aids, not theorem evidence or source completeness proof"
            ]
        })
    }
}

fn compact_ref_arrays(
    value: &mut serde_json::Value,
    json_pointer: &mut Vec<String>,
    compact: &mut CompactRefContext,
) {
    match value {
        serde_json::Value::Array(items)
            if items.len() > COMPACT_REF_ARRAY_THRESHOLD
                && items.iter().all(serde_json::Value::is_string) =>
        {
            let refs = items
                .iter()
                .filter_map(serde_json::Value::as_str)
                .map(str::to_string)
                .collect::<Vec<_>>();
            let pointer = json_pointer_string(json_pointer);
            let (ref_set_id, ref_count, sample_refs) = compact.intern_ref_set(refs, pointer);
            *value = serde_json::json!({
                "schemaVersion": "archsig-detail-ref-v0",
                "refSetId": ref_set_id,
                "refCount": ref_count,
                "sampleRefs": sample_refs,
                "detailRef": compact.detail_ref(&ref_set_id),
            });
        }
        serde_json::Value::Array(items) => {
            for (index, item) in items.iter_mut().enumerate() {
                json_pointer.push(index.to_string());
                compact_ref_arrays(item, json_pointer, compact);
                json_pointer.pop();
            }
        }
        serde_json::Value::Object(map) => {
            for (key, child) in map.iter_mut() {
                json_pointer.push(json_pointer_escape(key));
                compact_ref_arrays(child, json_pointer, compact);
                json_pointer.pop();
            }
        }
        _ => {}
    }
}

fn hash_refs(refs: &[String]) -> u64 {
    let mut hasher = DefaultHasher::new();
    refs.hash(&mut hasher);
    hasher.finish()
}

fn json_pointer_string(segments: &[String]) -> String {
    if segments.is_empty() {
        String::new()
    } else {
        format!("/{}", segments.join("/"))
    }
}

fn attach_detail_index_ref(packet_value: &mut serde_json::Value, compact: &CompactRefContext) {
    if let serde_json::Value::Object(map) = packet_value {
        map.insert(
            "detailIndexRef".to_string(),
            serde_json::json!({
                "schemaVersion": "archsig-analysis-detail-index-ref-v0",
                "artifactKind": "archsig-analysis-detail-index",
                "path": compact.detail_ref_base,
                "refSetCount": compact.ref_sets.len(),
                "compactThreshold": COMPACT_REF_ARRAY_THRESHOLD,
                "detailRefFormat": "<path>#<refSetId>"
            }),
        );
    }
}

fn json_pointer_escape(key: &str) -> String {
    key.replace('~', "~0").replace('/', "~1")
}

fn write_json_minified<T: serde::Serialize>(
    out: Option<PathBuf>,
    value: &T,
) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer(&mut file, value)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer(&mut handle, value)?;
            writeln!(handle)?;
        }
    }
    Ok(())
}
