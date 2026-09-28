//! `.archsig/` の読み書き、ソースの版、git。

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

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

    /// コミット時点の ArchMap。
    pub fn map_at(&self, commit: &str) -> Result<Vec<Atom>, String> {
        let list = self.git(&["ls-tree", "-r", "--name-only", commit, "--", ".archsig/map"])?;
        let mut out = Vec::new();
        for path in list.lines().filter(|l| l.ends_with(".jsonl")) {
            let text = self.git(&["show", &format!("{commit}:{path}")])?;
            out.extend(atom::parse_jsonl(&text, &format!("{commit}:{path}"))?);
        }
        Ok(out)
    }

    fn map_file(&self, source: &str) -> PathBuf {
        self.dir().join("map").join(format!("{source}.jsonl"))
    }

    pub fn plan_dir(&self, name: &str) -> PathBuf {
        self.dir().join("plans").join(name)
    }

    /// 候補。`plans/<名前>/` の直下の JSON Lines を名前順に読む。
    pub fn plan(&self, name: &str) -> Result<Vec<Atom>, String> {
        let dir = self.plan_dir(name);
        let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
            .map_err(|e| format!("候補 {name}: {e}"))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.is_file() && p.extension().is_some_and(|x| x == "jsonl"))
            .collect();
        files.sort();
        let mut out = Vec::new();
        for f in files {
            let text = std::fs::read_to_string(&f).map_err(|e| format!("{}: {e}", f.display()))?;
            out.extend(atom::parse_jsonl(&text, &f.display().to_string())?);
        }
        if !out.iter().any(|a| a.kind == "plan") {
            return Err(format!("候補 {name} に plan の行がない"));
        }
        Ok(out)
    }

    pub fn git(&self, args: &[&str]) -> Result<String, String> {
        let out = Command::new("git")
            .arg("-C")
            .arg(&self.root)
            .args(args)
            .output()
            .map_err(|e| format!("git: {e}"))?;
        if !out.status.success() {
            return Err(format!("git {}: {}", args.join(" "), String::from_utf8_lossy(&out.stderr).trim()));
        }
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
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
                let v = self.version(&loc.path).ok_or(format!("ソースがない: {}", loc.path))?;
                a.at = Some(format!("{}@{v}", a.at.as_deref().unwrap()));
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
