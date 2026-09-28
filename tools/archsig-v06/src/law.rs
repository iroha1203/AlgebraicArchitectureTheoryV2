//! 第4章の Law ファイル。ファイルは読まず、`archmap` から渡された字句を解く。

use std::collections::BTreeSet;

/// Law ファイルの宣言のうち、今の計算が使うもの。
#[derive(Clone, Debug, Default)]
pub struct LawSet {
    pub sources: Vec<String>,
    pub except: Vec<String>,
    /// 意味の語彙の名前。
    pub meanings: Vec<String>,
}

impl LawSet {
    /// `entries` の Law ファイルを読む。`read` はリポジトリの中の相対パスから中身を返す。
    /// `include` は、取り込む側のファイルの場所から読み、一つのファイルを二度読まない。
    pub fn load(entries: &[String], read: &dyn Fn(&str) -> Result<String, String>) -> Result<LawSet, String> {
        let mut set = LawSet::default();
        let mut seen = BTreeSet::new();
        for e in entries {
            set.load_file(e, read, &mut seen)?;
        }
        Ok(set)
    }

    fn load_file(&mut self, path: &str, read: &dyn Fn(&str) -> Result<String, String>, seen: &mut BTreeSet<String>) -> Result<(), String> {
        let path = normalize(path);
        if !seen.insert(path.clone()) {
            return Ok(());
        }
        let text = read(&path)?;
        for (line, block) in blocks(&text) {
            let at = format!("{path}:{line}");
            let head = lex(&block[0]).map_err(|e| format!("{at}: {e}"))?;
            match word_at(&head, 0).as_deref() {
                Some("sources") => {
                    self.sources.extend(strings(&head[1..]).map_err(|e| format!("{at}: {e}"))?);
                    for l in &block[1..] {
                        let r = lex(l).map_err(|e| format!("{at}: {e}"))?;
                        if word_at(&r, 0).as_deref() != Some("except") {
                            return Err(format!("{at}: sources の下には except だけを書く"));
                        }
                        self.except.extend(strings(&r[1..]).map_err(|e| format!("{at}: {e}"))?);
                    }
                }
                Some("include") => {
                    let dir = path.rsplit_once('/').map(|(d, _)| d).unwrap_or("");
                    for inc in strings(&head[1..]).map_err(|e| format!("{at}: {e}"))? {
                        let target = if dir.is_empty() { inc } else { format!("{dir}/{inc}") };
                        self.load_file(&target, read, seen)?;
                    }
                }
                Some("meaning") => self.meanings.push(word_at(&head, 1).ok_or(format!("{at}: meaning の名前がない"))?),
                _ => {}
            }
        }
        Ok(())
    }
}

/// `a/./b/../c` を `a/c` にそろえる。
fn normalize(path: &str) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for p in path.split('/') {
        match p {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            _ => parts.push(p),
        }
    }
    parts.join("/")
}

/// 字下げでまとめた宣言。行番号と、コメントを落とした行の列。
fn blocks(text: &str) -> Vec<(usize, Vec<String>)> {
    let mut out: Vec<(usize, Vec<String>)> = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        let line = strip_comment(raw);
        if line.trim().is_empty() {
            continue;
        }
        let indented = line.starts_with(' ') || line.starts_with('\t');
        match (indented, out.last_mut()) {
            (true, Some((_, b))) => b.push(line.trim().to_string()),
            _ => out.push((i + 1, vec![line.trim().to_string()])),
        }
    }
    out
}

fn strip_comment(line: &str) -> String {
    let mut in_str = false;
    for (i, c) in line.char_indices() {
        match c {
            '"' => in_str = !in_str,
            '#' if !in_str => return line[..i].to_string(),
            _ => {}
        }
    }
    line.to_string()
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Word(String),
    Str(String),
    Sym(&'static str),
}

fn lex(line: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '"' {
            let s = i + 1;
            i += 1;
            while i < chars.len() && chars[i] != '"' {
                i += 1;
            }
            if i >= chars.len() {
                return Err("閉じていない文字列".to_string());
            }
            out.push(Tok::Str(chars[s..i].iter().collect()));
            i += 1;
        } else if c == '-' && chars.get(i + 1) == Some(&'>') {
            out.push(Tok::Sym("->"));
            i += 2;
        } else if c.is_alphanumeric() || c == '_' || c == '^' {
            let s = i;
            while i < chars.len()
                && (chars[i].is_alphanumeric() || matches!(chars[i], '_' | '.' | '^') || chars[i] == '-' && chars.get(i + 1) != Some(&'>'))
            {
                i += 1;
            }
            out.push(Tok::Word(chars[s..i].iter().collect()));
        } else {
            let sym = match c {
                ',' => ",",
                '|' => "|",
                '=' => "=",
                '(' => "(",
                ')' => ")",
                ':' => ":",
                '*' => "*",
                '/' => "/",
                _ => return Err(format!("読めない文字 `{c}`")),
            };
            out.push(Tok::Sym(sym));
            i += 1;
        }
    }
    Ok(out)
}

fn word_at(t: &[Tok], i: usize) -> Option<String> {
    match t.get(i) {
        Some(Tok::Word(w)) => Some(w.clone()),
        _ => None,
    }
}

fn strings(t: &[Tok]) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    for (i, tok) in t.iter().enumerate() {
        match tok {
            Tok::Str(s) if i % 2 == 0 => out.push(s.clone()),
            Tok::Sym(",") if i % 2 == 1 => {}
            _ => return Err("パターンは \"…\" を `,` で並べて書く".to_string()),
        }
    }
    if out.is_empty() {
        return Err("パターンがない".to_string());
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sources_meanings_and_include() {
        let files = |p: &str| -> Result<String, String> {
            match p {
                ".archsig/law/a.law" => Ok("sources \"shop/**\"\n  except \"**/tests/**\"\n\nmeaning m on field\n  \"#でない\"\n\ninclude \"sub/b.law\"\n".to_string()),
                ".archsig/law/sub/b.law" => Ok("meaning n on call to \"mail.send\"  # コメント\n  values x | y\n  \"手がかり\"\ninclude \"../a.law\"\n".to_string()),
                _ => Err(format!("ない: {p}")),
            }
        };
        let set = LawSet::load(&[".archsig/law/a.law".to_string()], &files).unwrap();
        assert_eq!(set.sources, vec!["shop/**"]);
        assert_eq!(set.except, vec!["**/tests/**"]);
        assert_eq!(set.meanings, vec!["m", "n"]);
    }
}
