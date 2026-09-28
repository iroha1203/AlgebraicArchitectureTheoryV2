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
    /// `.archsig/` を置いたリポジトリの根。
    pub fn open(root: &Path) -> Result<Store, String> {
        if !root.join(".archsig").is_dir() {
            return Err(format!("{} に .archsig/ がない", root.display()));
        }
        Ok(Store { root: root.to_path_buf() })
    }

    pub fn dir(&self) -> PathBuf {
        self.root.join(".archsig")
    }

    /// `.archsig/law/` の `.law` ファイルを名前順に読む。
    pub fn laws(&self) -> Result<LawSet, String> {
        let dir = self.dir().join("law");
        let mut entries: Vec<String> = std::fs::read_dir(&dir)
            .map_err(|e| format!("{}: {e}", dir.display()))?
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().is_some_and(|x| x == "law"))
            .map(|e| format!(".archsig/law/{}", e.file_name().to_string_lossy()))
            .collect();
        entries.sort();
        let read = |p: &str| std::fs::read_to_string(self.root.join(p)).map_err(|e| format!("{p}: {e}"));
        LawSet::load(&entries, &read)
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

    /// 局所ごとの意味 Atom の `at` が指す、局所のディレクトリか。
    fn is_dir(&self, path: &str) -> bool {
        self.root.join(path).is_dir()
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
            let scope = a.scope_name().ok_or(format!("{} は ArchMap に書けない: {}", a.kind, a.subject))?;
            a.at = a.at.map(|at| at.trim_start_matches("./").to_string());
            let mut loc = a.location().ok_or(format!("at がない: {}", a.subject))?;
            loc.path = relative(&loc.path)?;
            if loc.version.is_none() && !self.is_dir(&loc.path) {
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
                    let at = match first.location().and_then(|l| l.version) {
                        Some(v) => format!("{path}@{v}"),
                        None => path.clone(),
                    };
                    atoms.insert(
                        0,
                        Atom {
                            kind: "observed".to_string(),
                            subject: path.clone(),
                            scope: Some(scope.clone()),
                            at: Some(at),
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
        // 局所ごとの意味 Atom は版を持たない。古いかは uses で決まる。
        if store.is_dir(path) {
            continue;
        }
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
                    "source": loc.path,
                    "scope": format!("meaning:{}", a.meaning.as_deref().unwrap_or("")),
                    "observed": v,
                    "current": store.version(&loc.path),
                    "element": a.subject,
                    "use": u,
                }));
            }
        }
    }
    let mut unread = Vec::new();
    for s in &sources {
        let mut scopes = Vec::new();
        let wanted = std::iter::once("structure".to_string()).chain(laws.meanings.iter().map(|m| format!("meaning:{m}")));
        for sc in wanted {
            if !observed.contains_key(&(s.clone(), sc.clone())) {
                scopes.push(sc);
            }
        }
        if !scopes.is_empty() {
            unread.push(json!({"source": s, "scopes": scopes}));
        }
    }
    Ok(json!({"stale": stale, "unread": unread}))
}

/// `at` のパスを、リポジトリの根からの相対パスにそろえる。
fn relative(path: &str) -> Result<String, String> {
    let p = path.trim_start_matches("./").trim_end_matches('/');
    if p.is_empty() || p.starts_with('/') || p.split('/').any(|c| c == "..") {
        return Err(format!("at のパスは、リポジトリの中の相対パスで書く: {path}"));
    }
    Ok(p.to_string())
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
    n >= 7 && a.is_char_boundary(n) && b.is_char_boundary(n) && a[..n] == b[..n]
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
