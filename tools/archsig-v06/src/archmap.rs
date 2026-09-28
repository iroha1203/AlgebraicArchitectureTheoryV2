//! `.archsig/` の読み書きと、ソースの版。

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use globset::{GlobBuilder, GlobSet, GlobSetBuilder};

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
    /// 局所ごとの意味 Atom は `.archsig/local/` にある。
    pub fn map(&self) -> Result<Vec<Atom>, String> {
        let mut out = Vec::new();
        let mut files: Vec<PathBuf> = ["map", "local"]
            .iter()
            .map(|d| self.dir().join(d))
            .filter(|d| d.is_dir())
            .flat_map(|d| walkdir::WalkDir::new(d).into_iter().filter_map(|e| e.ok()))
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

    /// ソースの ArchMap のファイルは `.archsig/map/<ソース>.jsonl`。
    /// 局所ごとの意味 Atom は、ソースとぶつからないように `.archsig/local/<読み>/<局所>.jsonl` に置く。
    fn map_file(&self, place: &Place) -> PathBuf {
        match place {
            Place::Source(path) => self.dir().join("map").join(format!("{path}.jsonl")),
            Place::Local { reading, local } => self.dir().join("local").join(reading).join(format!("{local}.jsonl")),
        }
    }

    /// Law の `sources` に当たる、今のソースのファイル。
    pub fn sources(&self, laws: &LawSet) -> Result<Vec<String>, String> {
        let decls = laws
            .sources
            .iter()
            .map(|d| Ok((globs(&d.include)?, globs(&d.except)?)))
            .collect::<Result<Vec<_>, String>>()?;
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
            if decls.iter().any(|(include, exclude)| include.is_match(&rel) && !exclude.is_match(&rel)) {
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


    /// `at` の形の場所のパスをそろえ、版がなければ今のソースの版を補う。
    fn versioned(&self, at: &str) -> Result<String, String> {
        let mut loc = atom::parse_location(at).ok_or(format!("場所が読めない: {at}"))?;
        loc.path = relative(&loc.path)?;
        if loc.version.is_none() {
            loc.version = Some(self.version(&loc.path).ok_or(format!("ソースがない: {}", loc.path))?);
        }
        Ok(loc.to_at())
    }

    /// 消えたソースを ArchMap から外す。外したら、そろえたソースのパスを返す。
    pub fn drop_source(&self, source: &str) -> Result<Option<String>, String> {
        let source = relative(source)?;
        let file = self.map_file(&Place::Source(source.clone()));
        if !file.exists() {
            return Ok(None);
        }
        std::fs::remove_file(&file).map_err(|e| format!("{}: {e}", file.display()))?;
        Ok(Some(source))
    }

    /// 取り出した Atom を ArchMap に書く。ソースと観測の範囲ごとに、元の Atom を置き換える。
    /// 局所ごとの意味 Atom は、ソースの代わりに局所の名前ごとに置き換える。
    pub fn record(&self, atoms: Vec<Atom>) -> Result<Vec<(String, String, usize)>, String> {
        let mut groups: BTreeMap<(Place, String), Vec<Atom>> = BTreeMap::new();
        for mut a in atoms {
            let scope = a.scope_name().ok_or(format!("{} は ArchMap に書けない: {}", a.kind, a.subject))?;
            if let Some(uses) = a.uses.take() {
                a.uses = Some(uses.iter().map(|u| self.versioned(u)).collect::<Result<_, _>>()?);
            }
            let place = if is_local(&a) {
                let (reading, local) = local_name(&a.subject)?;
                a.subject = format!("local:{reading}:{local}");
                if let Some(at) = a.at.take() {
                    let mut loc = atom::parse_location(&at).ok_or(format!("場所が読めない: {at}"))?;
                    loc.path = relative(&loc.path)?;
                    a.at = Some(loc.to_at());
                }
                Place::Local { reading, local }
            } else {
                let at = a.at.as_deref().ok_or(format!("at がない: {}", a.subject))?;
                a.at = Some(self.versioned(at)?);
                if a.kind == "observed" {
                    a.subject = relative(&a.subject)?;
                }
                Place::Source(a.location().unwrap().path)
            };
            groups.entry((place, scope)).or_default().push(a);
        }
        let mut report = Vec::new();
        let mut by_file: BTreeMap<Place, Vec<(String, Vec<Atom>)>> = BTreeMap::new();
        for ((place, scope), atoms) in groups {
            by_file.entry(place).or_default().push((scope, atoms));
        }
        for (place, scopes) in by_file {
            let file = self.map_file(&place);
            let mut kept: Vec<Atom> = if file.exists() {
                let text = std::fs::read_to_string(&file).map_err(|e| e.to_string())?;
                atom::parse_jsonl(&text, &file.display().to_string())?
            } else {
                Vec::new()
            };
            for (scope, mut atoms) in scopes {
                kept.retain(|a| a.scope_name().as_deref() != Some(scope.as_str()));
                let n = atoms.iter().filter(|a| a.kind != "observed").count();
                if let (Place::Source(path), false) = (&place, atoms.iter().any(|a| a.kind == "observed")) {
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
                report.push((place.name(), scope, n));
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
                // 観測し直す範囲は、意味 Atom の範囲。版は、変わった使用箇所のソースのもの。
                let source = if is_local(a) { a.subject.clone() } else { a.location().map(|l| l.path).unwrap_or_default() };
                stale.push(json!({
                    "source": source,
                    "scope": format!("meaning:{}", a.meaning.as_deref().unwrap_or("")),
                    "element": a.subject,
                    "use": u,
                    "observed": v,
                    "current": store.version(&loc.path),
                }));
            }
        }
    }
    let key = |v: &serde_json::Value| ["source", "scope", "element", "use"].map(|k| v[k].as_str().unwrap_or("").to_string());
    stale.sort_by_key(key);
    let meanings: std::collections::BTreeSet<&String> = laws.meanings.iter().collect();
    let mut unread = Vec::new();
    for s in &sources {
        let mut scopes = Vec::new();
        let wanted = std::iter::once("structure".to_string()).chain(meanings.iter().map(|m| format!("meaning:{m}")));
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

/// ArchMap の中の置き場所。ソースと局所は別の名前の空間にある。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Place {
    Source(String),
    Local { reading: String, local: String },
}

impl Place {
    /// 出力で使う名前。ソースはパス、局所は `local:<読み>:<局所>`。
    fn name(&self) -> String {
        match self {
            Place::Source(path) => path.clone(),
            Place::Local { reading, local } => format!("local:{reading}:{local}"),
        }
    }
}

/// 局所ごとの意味 Atom か。
fn is_local(a: &Atom) -> bool {
    a.kind == "meaning" && a.subject.starts_with("local:")
}

/// パスを、リポジトリの根からの相対パスにそろえる。`./` と空の区切りを落とし、`..` をたどる。
fn relative(path: &str) -> Result<String, String> {
    let outside = || format!("パスは、リポジトリの中の相対パスで書く: {path}");
    if path.starts_with('/') {
        return Err(outside());
    }
    let mut parts: Vec<&str> = Vec::new();
    for c in path.split('/') {
        match c {
            "" | "." => {}
            ".." => {
                parts.pop().ok_or_else(outside)?;
            }
            _ => parts.push(c),
        }
    }
    if parts.is_empty() {
        return Err(outside());
    }
    Ok(parts.join("/"))
}

/// 局所ごとの意味 Atom の名前 `local:<読み>:<局所>` を、読みと局所に分ける。局所の名前はパスと同じくそろえる。
fn local_name(subject: &str) -> Result<(String, String), String> {
    let rest = subject.strip_prefix("local:").unwrap_or(subject);
    match rest.split_once(':') {
        Some((reading, local)) if !matches!(reading, "" | "." | "..") && !reading.contains('/') => {
            Ok((reading.to_string(), relative(local)?))
        }
        _ => Err(format!("局所ごとの意味 Atom は local:<読み>:<局所> と書く: {subject}")),
    }
}

/// パスのパターン。`*` は `/` をまたがず、`**` はまたぐ。
pub fn globs(patterns: &[String]) -> Result<GlobSet, String> {
    let mut b = GlobSetBuilder::new();
    for p in patterns {
        b.add(GlobBuilder::new(p).literal_separator(true).build().map_err(|e| format!("{p}: {e}"))?);
    }
    b.build().map_err(|e| e.to_string())
}

/// 版どうしが同じか。短く書いた hash は前方一致で比べる。
pub fn same_version(a: &str, b: &str) -> bool {
    let (a, b) = (a.trim_start_matches("blob:"), b.trim_start_matches("blob:"));
    let n = a.len().min(b.len());
    n >= 7 && a.as_bytes()[..n].eq_ignore_ascii_case(&b.as_bytes()[..n])
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

    #[test]
    fn versions_compare_by_prefix_ignoring_case() {
        assert!(super::same_version("blob:ce01362503", "CE01362"));
        assert!(!super::same_version("blob:ce01362503", "ce0136"));
    }
}
