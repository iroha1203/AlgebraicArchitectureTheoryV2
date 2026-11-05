//! Scalar Data の family と constructor の構文的一致を所有する。
use archsig_common::{internal, internal::InternalError, names::QualifiedName};

#[repr(transparent)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct DataConstructor(QualifiedName);

impl DataConstructor {
    pub(crate) fn new(expected_family: &str, name: QualifiedName) -> Result<Self, InternalError> {
        if expected_family.is_empty()
            || name.owner() != Some(expected_family)
            || name.short().is_empty()
        {
            return Err(internal!("Data値のfamily・正規constructor形式が違う"));
        }
        Ok(Self(name))
    }

    pub(crate) fn family(&self) -> &str {
        // new が owner の存在を検査し、共有参照と Clone はその不変条件を保つ。
        self.0
            .owner()
            .expect("validated Data constructor has an owner")
    }

    pub(crate) fn short(&self) -> &str {
        self.0.short()
    }

    pub(crate) fn name(&self) -> &QualifiedName {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seals_exact_owner_and_nonempty_member_without_law_lookup() {
        for (family, name) in [
            ("F", "F.C"),
            ("V.Deep.Tree", "V.Deep.Tree.Leaf"),
            ("Unknown", "Unknown.F"),
            ("V..Tree", "V..Tree.C"),
        ] {
            let constructor = DataConstructor::new(family, name.into()).unwrap();
            assert_eq!(constructor.family(), family);
            assert_eq!(constructor.name().as_str(), name);
            assert_eq!(constructor.short(), name.rsplit('.').next().unwrap());
            assert!(constructor == constructor.clone());
        }
        for (family, name) in [
            ("G", "F.C"),
            ("", "F.C"),
            ("", ".C"),
            ("F", ".C"),
            ("F", "C"),
            ("F", "F."),
        ] {
            assert!(DataConstructor::new(family, name.into()).is_err());
        }
    }

    #[test]
    fn factory_matches_previous_shape_condition() {
        for (family, name) in [
            ("F", "F.C"),
            ("Unknown", "Unknown.F"),
            ("F.", "F..C"),
            ("F", "F..C"),
            ("F", "F.C.D"),
            ("F.C", "F.C.D"),
            ("", ".C"),
            ("F", "C"),
            ("F", "F."),
            ("G", "F.C"),
        ] {
            let previous = !family.is_empty()
                && name
                    .strip_prefix(family)
                    .and_then(|suffix| suffix.strip_prefix('.'))
                    .is_some_and(|member| !member.is_empty() && !member.contains('.'));
            assert_eq!(
                DataConstructor::new(family, name.into()).is_ok(),
                previous,
                "family={family:?}, name={name:?}"
            );
        }
    }
}
