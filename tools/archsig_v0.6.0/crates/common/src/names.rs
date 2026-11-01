//! 原始定義と Law が共有する名前の字句制約。
pub const RESERVED: &[&str] = &[
    "law",
    "semantics",
    "reading",
    "use",
    "as",
    "vocabulary",
    "version",
    "digest",
    "entity",
    "arrow",
    "correspondence",
    "align",
    "data",
    "view",
    "required",
    "optional",
    "local",
    "reads",
    "change",
    "relation",
    "when",
    "let",
    "in",
    "if",
    "then",
    "else",
    "match",
    "forall",
    "exists",
    "not",
    "implies",
    "or",
    "and",
    "with",
    "true",
    "false",
    "unit",
    "list",
    "set",
    "where",
    "none",
    "some",
    "fn",
    "Unit",
    "Bool",
    "Z",
    "Q",
    "Text",
    "Fp",
    "List",
    "Set",
    "Option",
    "Map",
    "Term",
    "Path",
];

pub const BUILTIN_OPS: &[&str] = &[
    "rat", "count", "sum", "path", "identity", "then", "source", "target",
];
pub fn is_reserved(name: &str) -> bool {
    RESERVED.contains(&name)
}

/// 入力検査で分解した名前。元の綴りと所属・末尾名を一緒に保持する。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct QualifiedName {
    full: String,
    namespace_end: usize,
    member_start: usize,
    owner_field: bool,
}
impl QualifiedName {
    pub fn parse(full: String) -> Self {
        let namespace_end = full.find('.').unwrap_or(0);
        let member_start = full.rfind('.').map_or(0, |i| i + 1);
        let owner_field = &full[member_start..] == "owner";
        Self {
            full,
            namespace_end,
            member_start,
            owner_field,
        }
    }
    pub fn as_str(&self) -> &str {
        &self.full
    }
    pub fn namespace(&self) -> &str {
        &self.full[..self.namespace_end]
    }
    pub fn short(&self) -> &str {
        &self.full[self.member_start..]
    }
    pub fn owner(&self) -> Option<&str> {
        self.member_start
            .checked_sub(1)
            .map(|end| &self.full[..end])
    }
    pub fn is_owner(&self) -> bool {
        self.owner_field
    }
}
impl std::hash::Hash for QualifiedName {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.full, state);
    }
}
impl std::ops::Deref for QualifiedName {
    type Target = str;
    fn deref(&self) -> &str {
        self.as_str()
    }
}
impl std::fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.full.fmt(f)
    }
}
impl std::borrow::Borrow<str> for QualifiedName {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}
impl AsRef<str> for QualifiedName {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}
impl From<String> for QualifiedName {
    fn from(value: String) -> Self {
        Self::parse(value)
    }
}
impl From<&str> for QualifiedName {
    fn from(value: &str) -> Self {
        Self::parse(value.to_owned())
    }
}
impl From<QualifiedName> for String {
    fn from(value: QualifiedName) -> Self {
        value.full
    }
}
impl From<&QualifiedName> for String {
    fn from(value: &QualifiedName) -> Self {
        value.full.clone()
    }
}
impl PartialEq<str> for QualifiedName {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl PartialEq<&str> for QualifiedName {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}
impl PartialEq<String> for QualifiedName {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other
    }
}
impl PartialEq<QualifiedName> for String {
    fn eq(&self, other: &QualifiedName) -> bool {
        self == other.as_str()
    }
}

impl std::borrow::Borrow<String> for QualifiedName {
    fn borrow(&self) -> &String {
        &self.full
    }
}

#[cfg(test)]
mod qualified_tests {
    use super::QualifiedName;

    #[test]
    fn borrowed_hash_lookup_preserves_the_name_key() {
        let mut names = std::collections::HashMap::new();
        names.insert(QualifiedName::from("Mesh.Part.owner"), 7);
        assert_eq!(names.get("Mesh.Part.owner"), Some(&7));
        assert_eq!(names.get(&String::from("Mesh.Part.owner")), Some(&7));
        assert_eq!(names.get("Mesh.Part.value"), None);
    }

    #[test]
    fn parsed_parts_preserve_the_original_spelling_and_owner_role() {
        for (text, namespace, owner, short, owner_field) in [
            ("Mesh.Part.owner", "Mesh", Some("Mesh.Part"), "owner", true),
            ("Mesh.Part.value", "Mesh", Some("Mesh.Part"), "value", false),
            ("Mesh.Part", "Mesh", Some("Mesh"), "Part", false),
            ("value", "", None, "value", false),
            ("名.型.値", "名", Some("名.型"), "値", false),
        ] {
            let name = QualifiedName::from(text);
            assert_eq!(name.as_str(), text);
            assert_eq!(name.namespace(), namespace);
            assert_eq!(name.owner(), owner);
            assert_eq!(name.short(), short);
            assert_eq!(name.is_owner(), owner_field);
            assert_eq!(String::from(name), text);
        }
    }
}
