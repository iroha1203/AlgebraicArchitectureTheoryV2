//! 明示プロジェクトマニフェスト（`--project PATH`, `archsig.project/1`）の読込・検査。
//!
//! 暗黙のファイル探索は行わず、明示指定されたマニフェスト内の相対パスだけを
//! マニフェストファイルの親ディレクトリ基準で解決する。

use archsig_common::issue::{Code, Details, Issue, Location};
use archsig_common::json::{JNode, JValue, parse_with_max_depth};
use archsig_common::limits::DEFAULT_MAX_JSON_DEPTH;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// 明示プロジェクトマニフェストの形式識別子。
pub const PROJECT_FORMAT: &str = "archsig.project/1";

/// 解析・検証済みのプロジェクトマニフェスト。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectManifest {
    pub atom_definitions: Vec<PathBuf>,
    pub law: PathBuf,
    pub archmap: Option<PathBuf>,
    pub asks: Vec<String>,
    pub max_file_bytes: Option<u64>,
    pub shigure_limits: BTreeMap<String, u64>,
}

/// JSON バイト列から `archsig.project/1` を検証付きで読み込む。
pub fn parse_project_manifest(
    bytes: &[u8],
    manifest_path: &Path,
) -> Result<ProjectManifest, Box<Issue>> {
    let base_dir = manifest_path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let root = parse_with_max_depth(bytes, DEFAULT_MAX_JSON_DEPTH).map_err(|mut err| {
        relocate_as_manifest(&mut err);
        err
    })?;
    let fields = expect_obj(&root, "", "project manifest root must be a JSON object")?;

    let mut format: Option<&str> = None;
    let mut semantics: Option<&str> = None;
    let mut atom_definitions_node: Option<&JNode> = None;
    let mut law_node: Option<&JNode> = None;
    let mut archmap_node: Option<&JNode> = None;
    let mut asks_node: Option<&JNode> = None;
    let mut max_file_bytes_node: Option<&JNode> = None;
    let mut shigure_limits_node: Option<&JNode> = None;

    for (key, value) in fields {
        let pointer = format!("/{key}");
        match key.as_str() {
            "format" => {
                format = Some(expect_nonempty_str(
                    value,
                    &pointer,
                    "`format` must be a non-empty string",
                )?);
            }
            "semantics" => {
                semantics = Some(expect_nonempty_str(
                    value,
                    &pointer,
                    "`semantics` must be a non-empty string",
                )?);
            }
            "atom_definitions" => atom_definitions_node = Some(value),
            "law" => law_node = Some(value),
            "archmap" => archmap_node = Some(value),
            "asks" => asks_node = Some(value),
            "max_file_bytes" => max_file_bytes_node = Some(value),
            "shigure_limits" => shigure_limits_node = Some(value),
            other => {
                return Err(manifest_issue(
                    Code::Syntax,
                    pointer,
                    None,
                    format!("unknown field `{other}` in project manifest"),
                ));
            }
        }
    }

    let format_str = format.ok_or_else(|| {
        manifest_issue(
            Code::Syntax,
            "/format",
            None,
            "project manifest requires `format`",
        )
    })?;
    if format_str != PROJECT_FORMAT {
        let code = if format_str.starts_with("archsig.project/") {
            Code::UnsupportedVersion
        } else {
            Code::Syntax
        };
        return Err(Box::new(Issue {
            code,
            message: format!(
                "unsupported project manifest format `{format_str}` (expected `{PROJECT_FORMAT}`)"
            ),
            location: Location::Definition {
                input: "project".to_owned(),
                pointer: "/format".to_owned(),
                span: None,
            },
            details: Details::Version {
                found_format: format_str.to_owned(),
                found_semantics: semantics.map(str::to_owned),
            },
        }));
    }

    let semantics_str = semantics.ok_or_else(|| {
        manifest_issue(
            Code::Syntax,
            "/semantics",
            None,
            "project manifest requires `semantics`",
        )
    })?;
    if semantics_str != crate::law::SEMANTICS {
        return Err(Box::new(Issue {
            code: Code::UnsupportedVersion,
            message: format!(
                "unsupported project semantics `{semantics_str}` (expected `{}`)",
                crate::law::SEMANTICS
            ),
            location: Location::Definition {
                input: "project".to_owned(),
                pointer: "/semantics".to_owned(),
                span: None,
            },
            details: Details::Version {
                found_format: format_str.to_owned(),
                found_semantics: Some(semantics_str.to_owned()),
            },
        }));
    }

    let defs_node = atom_definitions_node.ok_or_else(|| {
        manifest_issue(
            Code::Syntax,
            "/atom_definitions",
            None,
            "project manifest requires `atom_definitions`",
        )
    })?;
    let JValue::Arr(def_items) = &defs_node.value else {
        return Err(manifest_issue(
            Code::Type,
            "/atom_definitions",
            None,
            "`atom_definitions` must be an array of paths",
        ));
    };
    if def_items.is_empty() {
        return Err(manifest_issue(
            Code::Syntax,
            "/atom_definitions",
            None,
            "`atom_definitions` must contain at least one path",
        ));
    }
    let mut atom_definitions = Vec::with_capacity(def_items.len());
    for (idx, item) in def_items.iter().enumerate() {
        let pointer = format!("/atom_definitions/{idx}");
        let raw = expect_nonempty_str(
            item,
            &pointer,
            "`atom_definitions` entries must be non-empty strings",
        )?;
        atom_definitions.push(resolve_manifest_path(base_dir, raw));
    }

    let law_node = law_node.ok_or_else(|| {
        manifest_issue(
            Code::Syntax,
            "/law",
            None,
            "project manifest requires `law`",
        )
    })?;
    let raw_law = expect_nonempty_str(law_node, "/law", "`law` must be a non-empty string")?;
    let law = resolve_manifest_path(base_dir, raw_law);

    let archmap = match archmap_node {
        Some(node) => {
            let raw =
                expect_nonempty_str(node, "/archmap", "`archmap` must be a non-empty string")?;
            Some(resolve_manifest_path(base_dir, raw))
        }
        None => None,
    };

    let asks = match asks_node {
        Some(node) => {
            let JValue::Arr(items) = &node.value else {
                return Err(manifest_issue(
                    Code::Type,
                    "/asks",
                    None,
                    "`asks` must be an array of question strings",
                ));
            };
            let mut out = Vec::with_capacity(items.len());
            for (idx, item) in items.iter().enumerate() {
                let pointer = format!("/asks/{idx}");
                let ask = expect_nonempty_str(
                    item,
                    &pointer,
                    "`asks` entries must be non-empty strings",
                )?;
                out.push(ask.to_owned());
            }
            out
        }
        None => Vec::new(),
    };

    let max_file_bytes = match max_file_bytes_node {
        Some(node) => Some(expect_positive_u64(
            node,
            "/max_file_bytes",
            "`max_file_bytes` must be a positive integer",
        )?),
        None => None,
    };

    let mut shigure_limits = BTreeMap::new();
    if let Some(node) = shigure_limits_node {
        let entries = expect_obj(
            node,
            "/shigure_limits",
            "`shigure_limits` must be an object mapping limit names to positive integers",
        )?;
        for (name, val_node) in entries {
            let pointer = format!("/shigure_limits/{name}");
            if name.is_empty() {
                return Err(manifest_issue(
                    Code::Syntax,
                    pointer,
                    None,
                    "`shigure_limits` keys must be non-empty",
                ));
            }
            let val = expect_positive_u64(
                val_node,
                &pointer,
                "`shigure_limits` values must be positive integers",
            )?;
            shigure_limits.insert(name.clone(), val);
        }
    }

    Ok(ProjectManifest {
        atom_definitions,
        law,
        archmap,
        asks,
        max_file_bytes,
        shigure_limits,
    })
}

fn resolve_manifest_path(base_dir: &Path, raw: &str) -> PathBuf {
    let p = Path::new(raw);
    if p.is_absolute() || base_dir == Path::new(".") {
        p.to_path_buf()
    } else {
        base_dir.join(p)
    }
}

fn relocate_as_manifest(issue: &mut Issue) {
    let (pointer, span) = match &issue.location {
        Location::ArchMap { pointer, span } => (pointer.clone(), *span),
        Location::Definition { pointer, span, .. } => (pointer.clone(), *span),
        Location::Law { span } => (String::new(), Some(*span)),
    };
    issue.location = Location::Definition {
        input: "project".to_owned(),
        pointer,
        span,
    };
}

fn manifest_issue(
    code: Code,
    pointer: impl Into<String>,
    span: Option<(usize, usize)>,
    message: impl Into<String>,
) -> Box<Issue> {
    Box::new(Issue {
        code,
        message: message.into(),
        location: Location::Definition {
            input: "project".to_owned(),
            pointer: pointer.into(),
            span,
        },
        details: Details::Empty,
    })
}

fn expect_obj<'a>(
    node: &'a JNode,
    pointer: &str,
    msg: &str,
) -> Result<&'a [(String, JNode)], Box<Issue>> {
    match &node.value {
        JValue::Obj(entries) => Ok(entries),
        _ => Err(manifest_issue(Code::Type, pointer, None, msg)),
    }
}

fn expect_nonempty_str<'a>(
    node: &'a JNode,
    pointer: &str,
    msg: &str,
) -> Result<&'a str, Box<Issue>> {
    match &node.value {
        JValue::Str(s) if !s.is_empty() => Ok(s.as_str()),
        _ => Err(manifest_issue(Code::Type, pointer, None, msg)),
    }
}

fn expect_positive_u64(node: &JNode, pointer: &str, msg: &str) -> Result<u64, Box<Issue>> {
    match &node.value {
        JValue::Num(raw) => raw
            .parse::<u64>()
            .ok()
            .filter(|&n| n > 0)
            .ok_or_else(|| manifest_issue(Code::Type, pointer, None, msg)),
        _ => Err(manifest_issue(Code::Type, pointer, None, msg)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_valid_manifest_and_resolves_relative_paths_only() {
        let raw = r#"{
            "format": "archsig.project/1",
            "semantics": "archsig/0.6.0",
            "atom_definitions": ["defs/core.atoms.json", "/abs/extra.atoms.json"],
            "law": "specs/main.law",
            "archmap": "obs/app.archmap.json",
            "asks": ["q1=evaluate(A.x, s=@s/a)"],
            "max_file_bytes": 1048576,
            "shigure_limits": {
                "max_gb_steps": 128
            }
        }"#;
        let parsed =
            parse_project_manifest(raw.as_bytes(), Path::new("proj/archsig.json")).unwrap();
        assert_eq!(
            parsed.atom_definitions,
            vec![
                PathBuf::from("proj/defs/core.atoms.json"),
                PathBuf::from("/abs/extra.atoms.json"),
            ]
        );
        assert_eq!(parsed.law, PathBuf::from("proj/specs/main.law"));
        assert_eq!(
            parsed.archmap,
            Some(PathBuf::from("proj/obs/app.archmap.json"))
        );
        assert_eq!(parsed.asks, vec!["q1=evaluate(A.x, s=@s/a)"]);
        assert_eq!(parsed.max_file_bytes, Some(1_048_576));
        assert_eq!(parsed.shigure_limits.get("max_gb_steps"), Some(&128));
    }

    #[test]
    fn rejects_unsupported_versions_unknown_fields_and_invalid_values() {
        let bad_sem = r#"{
            "format": "archsig.project/1",
            "semantics": "archsig/0.5.0",
            "atom_definitions": ["d.json"],
            "law": "l.law"
        }"#;
        let err = parse_project_manifest(bad_sem.as_bytes(), Path::new("p.json")).unwrap_err();
        assert_eq!(err.code, Code::UnsupportedVersion);

        let bad_fmt = r#"{
            "format": "archsig.project/99",
            "semantics": "archsig/0.6.0",
            "atom_definitions": ["d.json"],
            "law": "l.law"
        }"#;
        let err = parse_project_manifest(bad_fmt.as_bytes(), Path::new("p.json")).unwrap_err();
        assert_eq!(err.code, Code::UnsupportedVersion);

        let unknown = r#"{
            "format": "archsig.project/1",
            "semantics": "archsig/0.6.0",
            "atom_definitions": ["d.json"],
            "law": "l.law",
            "extra": true
        }"#;
        let err = parse_project_manifest(unknown.as_bytes(), Path::new("p.json")).unwrap_err();
        assert_eq!(err.code, Code::Syntax);

        let empty_defs = r#"{
            "format": "archsig.project/1",
            "semantics": "archsig/0.6.0",
            "atom_definitions": [],
            "law": "l.law"
        }"#;
        let err = parse_project_manifest(empty_defs.as_bytes(), Path::new("p.json")).unwrap_err();
        assert_eq!(err.code, Code::Syntax);

        let zero_limit = r#"{
            "format": "archsig.project/1",
            "semantics": "archsig/0.6.0",
            "atom_definitions": ["d.json"],
            "law": "l.law",
            "max_file_bytes": 0
        }"#;
        let err = parse_project_manifest(zero_limit.as_bytes(), Path::new("p.json")).unwrap_err();
        assert_eq!(err.code, Code::Type);
    }
}
