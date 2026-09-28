//! `.archsig/` の読み書きと、ソースの版。

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use globset::{Glob, GlobSet, GlobSetBuilder};

use crate::atom::{self, Atom};
use crate::law::LawSet;

pub struct Store {
    pub root: PathBuf,
}

impl Store {
    /// 今の場所から上へたどって `.archsig/` を探す。
    pub fn find(start: &Path) -> Result<Store, String> {
        let mut dir = start.canonicalize().map_err(|e| format!("{}: {e}", start.display()))?;
        loop {
            if dir.join(".archsig").is_dir() {
                return Ok(Store { root: dir });
            }
            if !dir.pop() {
                return Err(".archsig/ が見つからない".to_string());
            }
        }
    }

    pub fn dir(&self) -> PathBuf {
        self.root.join(".archsig")
    }

    pub fn laws(&self) -> Result<LawSet, String> {
        LawSet::load_dir(&self.dir().join("law"))
    }

    /// ArchMap。ソースのファイルごとの JSON Lines をすべて読む。
    pub fn map(&self) -> Result<Vec<Atom>, String> {
        let dir = self.dir().join("map");
        let mut out = Vec::new();
        if !dir.is_dir() {
            return Ok(out);
        }
        let mut files: Vec<PathBuf> = walkdir::WalkDir::new(&dir)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file() && e.path().extension().is_some_and(|x| x == "jsonl"))
            .map(|e| e.into_path())
            .collect();
        files.sort();
        for f in files {
            let text = std::fs::read_to_string(&f).map_err(|e| format!("{}: {e}", f.display()))?;
            out.extend(atom::parse_jsonl(&text, &f.display().to_string())?);
        }
        Ok(out)
    }

    fn map_file(&self, source: &str) -> PathBuf {
        self.dir().join("map").join(format!("{source}.jsonl"))
    }

    /// Law の `sources` に当たる、今のソースのファイル。
    pub fn sources(&self, laws: &LawSet) -> Result<Vec<String>, String> {
        let include = globs(&laws.sources)?;
        let exclude = globs(&laws.except)?;
        let mut out = Vec::new();
        for e in walkdir::WalkDir::new(&self.root)
            .into_iter()
            .filter_entry(|e| e.file_name() != ".git" && e.file_name() != ".archsig")
            .filter_map(|e| e.ok())
        {
            if !e.file_type().is_file() {
                continue;
            }
            let rel = e.path().strip_prefix(&self.root).unwrap().to_string_lossy().replace('\\', "/");
            if include.is_match(&rel) && !exclude.is_match(&rel) {
                out.push(rel);
            }
        }
        out.sort();
        Ok(out)
    }

    /// ソースの今の版。git の blob hash と同じ値。ファイルがなければ None。
    pub fn version(&self, path: &str) -> Option<String> {
        let bytes = std::fs::read(self.root.join(path)).ok()?;
        Some(format!("blob:{}", blob_hash(&bytes)))
    }

    fn with_version(&self, at: &str, path: &str) -> Result<String, String> {
        let v = self.version(path).ok_or(format!("ソースがない: {path}"))?;
        Ok(format!("{at}@{v}"))
    }

    /// 消えたソースを ArchMap から外す。
    pub fn drop_source(&self, source: &str) -> Result<bool, String> {
        let file = self.map_file(source);
        if !file.exists() {
            return Ok(false);
        }
        std::fs::remove_file(&file).map_err(|e| format!("{}: {e}", file.display()))?;
        Ok(true)
    }

    /// 取り出した Atom を ArchMap に書く。ソースと観測の範囲ごとに、元の Atom を置き換える。
    pub fn record(&self, atoms: Vec<Atom>) -> Result<Vec<(String, String, usize)>, String> {
        let mut groups: BTreeMap<(String, String), Vec<Atom>> = BTreeMap::new();
        for mut a in atoms {
            a.validate()?;
            let scope = a.scope_name().ok_or(format!("{} は ArchMap に書けない", a.kind))?;
            let loc = a.location().ok_or(format!("at がない: {}", a.subject))?;
            if loc.path.starts_with("plan:") {
                return Err(format!("候補の Atom は ArchMap に書けない: {}", a.subject));
            }
            if loc.version.is_none() {
                a.at = Some(self.with_version(a.at.as_deref().unwrap(), &loc.path)?);
            }
            if let Some(uses) = a.uses.take() {
                let mut filled = Vec::new();
                for u in uses {
                    match atom::parse_location(&u) {
                        Some(l) if l.version.is_none() => filled.push(self.with_version(&u, &l.path)?),
                        _ => filled.push(u),
                    }
                }
                a.uses = Some(filled);
            }
            groups.entry((loc.path, scope)).or_default().push(a);
        }
        let mut report = Vec::new();
        let mut by_file: BTreeMap<String, Vec<(String, Vec<Atom>)>> = BTreeMap::new();
        for ((path, scope), atoms) in groups {
            by_file.entry(path).or_default().push((scope, atoms));
        }
        for (path, scopes) in by_file {
            let file = self.map_file(&path);
            let mut kept: Vec<Atom> = if file.exists() {
                let text = std::fs::read_to_string(&file).map_err(|e| e.to_string())?;
                atom::parse_jsonl(&text, &file.display().to_string())?
            } else {
                Vec::new()
            };
            for (scope, mut atoms) in scopes {
                kept.retain(|a| a.scope_name().as_deref() != Some(scope.as_str()));
                let n = atoms.iter().filter(|a| a.kind != "observed").count();
                if !atoms.iter().any(|a| a.kind == "observed") {
                    let first = &atoms[0];
                    let version = first.location().and_then(|l| l.version).unwrap_or_default();
                    atoms.insert(
                        0,
                        Atom {
                            kind: "observed".to_string(),
                            subject: path.clone(),
                            scope: Some(scope.clone()),
                            at: Some(format!("{path}@{version}")),
                            by: first.by.clone(),
                            ..Atom::default()
                        },
                    );
                }
                kept.extend(atoms);
                report.push((path.clone(), scope, n));
            }
            std::fs::create_dir_all(file.parent().unwrap()).map_err(|e| e.to_string())?;
            std::fs::write(&file, atom::to_jsonl(&kept)).map_err(|e| e.to_string())?;
        }
        Ok(report)
    }
}

/// 古い範囲と、読んでいない範囲。
pub fn status(store: &Store) -> Result<serde_json::Value, String> {
    use serde_json::json;
    let laws = store.laws()?;
    let sources = store.sources(&laws)?;
    let map = store.map()?;
    let mut observed: BTreeMap<(String, String), String> = BTreeMap::new();
    for a in map.iter().filter(|a| a.kind == "observed") {
        let version = a.location().and_then(|l| l.version).unwrap_or_default();
        observed.insert((a.subject.clone(), a.scope.clone().unwrap_or_default()), version);
    }
    let current = |path: &str, version: &str| store.version(path).filter(|c| same_version(c, version));
    let mut stale = Vec::new();
    for ((path, scope), version) in &observed {
        if current(path, version).is_none() {
            stale.push(json!({"source": path, "scope": scope, "observed": version, "current": store.version(path)}));
        }
    }
    for a in map.iter().filter(|a| a.kind == "meaning") {
        for u in a.uses.iter().flatten() {
            let Some(loc) = atom::parse_location(u) else { continue };
            let Some(v) = loc.version else { continue };
            if current(&loc.path, &v).is_none() {
                stale.push(json!({
                    "source": a.location().map(|l| l.path),
                    "scope": format!("meaning:{}", a.meaning.as_deref().unwrap_or("")),
                    "element": a.subject,
                    "use": u,
                }));
            }
        }
    }
    let mut unread = Vec::new();
    for s in &sources {
        let mut scopes = Vec::new();
        let wanted = std::iter::once("structure".to_string()).chain(laws.meanings.iter().map(|m| format!("meaning:{}", m.name)));
        for sc in wanted {
            if !observed.contains_key(&(s.clone(), sc.clone())) {
                scopes.push(sc);
            }
        }
        if !scopes.is_empty() {
            unread.push(json!({"source": s, "scopes": scopes}));
        }
    }
    Ok(json!({"sources": sources.len(), "stale": stale, "unread": unread}))
}

pub fn globs(patterns: &[String]) -> Result<GlobSet, String> {
    let mut b = GlobSetBuilder::new();
    for p in patterns {
        b.add(Glob::new(p).map_err(|e| format!("{p}: {e}"))?);
    }
    b.build().map_err(|e| e.to_string())
}

/// 版どうしが同じか。短く書いた hash は前方一致で比べる。
pub fn same_version(a: &str, b: &str) -> bool {
    let (a, b) = (a.trim_start_matches("blob:"), b.trim_start_matches("blob:"));
    let n = a.len().min(b.len());
    n >= 7 && a[..n] == b[..n]
}

fn blob_hash(bytes: &[u8]) -> String {
    let mut data = format!("blob {}\0", bytes.len()).into_bytes();
    data.extend_from_slice(bytes);
    sha1(&data).iter().map(|b| format!("{b:02x}")).collect()
}

fn sha1(data: &[u8]) -> [u8; 20] {
    let mut h: [u32; 5] = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
    let mut msg = data.to_vec();
    let bits = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bits.to_be_bytes());
    for chunk in msg.chunks(64) {
        let mut w = [0u32; 80];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([chunk[4 * i], chunk[4 * i + 1], chunk[4 * i + 2], chunk[4 * i + 3]]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let [mut a, mut b, mut c, mut d, mut e] = h;
        for (i, wi) in w.iter().enumerate() {
            let (f, k) = match i {
                0..=19 => ((b & c) | (!b & d), 0x5A827999),
                20..=39 => (b ^ c ^ d, 0x6ED9EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDC),
                _ => (b ^ c ^ d, 0xCA62C1D6),
            };
            let t = a.rotate_left(5).wrapping_add(f).wrapping_add(e).wrapping_add(k).wrapping_add(*wi);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = t;
        }
        for (x, y) in h.iter_mut().zip([a, b, c, d, e]) {
            *x = x.wrapping_add(y);
        }
    }
    let mut out = [0u8; 20];
    for (i, x) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&x.to_be_bytes());
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn git_blob_hash() {
        // `printf 'hello\n' | git hash-object --stdin`
        assert_eq!(super::blob_hash(b"hello\n"), "ce013625030ba8dba906f756967f9e9ca394464a");
        assert_eq!(super::blob_hash(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391");
    }
}
