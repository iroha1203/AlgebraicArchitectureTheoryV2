//! 原始所属とConfigurationから、読取り適用域と完全な有限query patternを作る。
use super::maps::ObjectIdentity;
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircuitQuery<'a> {
    Atom {
        atom: &'a FactPointer,
        present: bool,
    },
    Relation {
        left: &'a FactPointer,
        right: &'a FactPointer,
        present: bool,
    },
    Identification {
        left: &'a FactPointer,
        right: &'a FactPointer,
        present: bool,
    },
}
/// U順のmembershipと、U×Uの辞書順の二つの関係を保持する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitPattern {
    universe: Vec<FactPointer>,
    membership: Vec<bool>,
    relations: Vec<bool>,
    identifications: Vec<bool>,
}
impl CircuitPattern {
    pub fn universe(&self) -> &[FactPointer] {
        &self.universe
    }
    pub fn membership(&self) -> &[bool] {
        &self.membership
    }
    pub fn relations(&self) -> &[bool] {
        &self.relations
    }
    pub fn identifications(&self) -> &[bool] {
        &self.identifications
    }
    /// Atom、全順序対Relation、全順序対Identificationの順。U外の値を追加しない。
    pub fn queries(&self) -> impl Iterator<Item = CircuitQuery<'_>> {
        let n = self.universe.len();
        self.universe
            .iter()
            .zip(&self.membership)
            .map(|(atom, present)| CircuitQuery::Atom {
                atom,
                present: *present,
            })
            .chain(self.universe.iter().enumerate().flat_map(move |(i, left)| {
                self.universe
                    .iter()
                    .enumerate()
                    .map(move |(j, right)| CircuitQuery::Relation {
                        left,
                        right,
                        present: self.relations[i * n + j],
                    })
            }))
            .chain(self.universe.iter().enumerate().flat_map(move |(i, left)| {
                self.universe.iter().enumerate().map(move |(j, right)| {
                    CircuitQuery::Identification {
                        left,
                        right,
                        present: self.identifications[i * n + j],
                    }
                })
            }))
    }
    fn key(&self, control: &mut Control) -> Result<Vec<bool>, ConstructionFailure> {
        let mut key = Vec::new();
        for section in [&self.membership, &self.relations, &self.identifications] {
            for bit in section {
                check(control)?;
                key.push(*bit);
            }
        }
        Ok(key)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationProfile {
    object: ObjectIdentity,
    configuration: ConfigurationCandidate,
    domain: SubjectDomain,
    membership: Option<ConditionalSubject>,
    pattern: Option<CircuitPattern>,
}
impl ConfigurationProfile {
    pub fn object(&self) -> &ObjectIdentity {
        &self.object
    }
    pub fn configuration(&self) -> &ConfigurationCandidate {
        &self.configuration
    }
    /// この候補行が対象となる場合の読取り適用域。
    pub fn domain(&self) -> &SubjectDomain {
        &self.domain
    }
    pub fn membership(&self) -> Option<&ConditionalSubject> {
        self.membership.as_ref()
    }
    pub fn pattern(&self) -> Option<&CircuitPattern> {
        self.pattern.as_ref()
    }
}
/// 同じpatternの行を群にしても、対象や読取りのidentityを統合しない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationProfiles {
    construction: ConfigurationConstruction,
    profiles: Vec<ConfigurationProfile>,
    known_classes: Vec<Vec<usize>>,
}
impl ConfigurationProfiles {
    pub fn construction(&self) -> &ConfigurationConstruction {
        &self.construction
    }
    /// baseが先頭、残りは部分対象のcanonical順。所属未決の候補行も含む。
    pub fn profiles(&self) -> &[ConfigurationProfile] {
        &self.profiles
    }
    pub fn known_classes(&self) -> &[Vec<usize>] {
        &self.known_classes
    }
    pub fn is_complete(&self) -> bool {
        self.construction.local_domain.is_complete()
            && self
                .profiles
                .iter()
                .all(|p| p.membership.is_none() && p.pattern.is_some())
    }
    pub fn classes(&self) -> Option<&[Vec<usize>]> {
        self.is_complete().then_some(&self.known_classes)
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let root = self.construction.root();
        if self
            != &construct_profiles(
                inputs,
                self.construction.reading(),
                &root.snapshot,
                &root.subject,
                control,
            )?
        {
            return Err(ConstructionFailure::Inconsistent(
                "適用域・query pattern・対象群が現在入力と違う".into(),
            ));
        }
        check(control)
    }
}
fn check(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::ConfigurationProfile)
        .map_err(Into::into)
}
fn pattern(
    configuration: &Configuration,
    universe: &[FactPointer],
    control: &mut Control,
) -> Result<CircuitPattern, ConstructionFailure> {
    check(control)?;
    let n = universe.len();
    let pairs = n
        .checked_mul(n)
        .ok_or_else(|| ConstructionFailure::Inconsistent("queryの順序対が大きすぎる".into()))?;
    pairs
        .checked_mul(2)
        .and_then(|p| p.checked_add(n))
        .ok_or_else(|| ConstructionFailure::Inconsistent("query表が大きすぎる".into()))?;
    let mut family = BTreeSet::new();
    for fact in configuration.family() {
        check(control)?;
        family.insert(fact);
    }
    let mut index = BTreeMap::new();
    let mut atoms = Vec::new();
    let mut membership = Vec::new();
    for (i, fact) in universe.iter().enumerate() {
        check(control)?;
        index.insert(fact, i);
        atoms.push(fact.clone());
        membership.push(family.contains(fact));
    }
    let mut matrices = Vec::new();
    for relation in [configuration.relations(), configuration.identifications()] {
        let mut present = BTreeSet::new();
        for (a, b) in relation {
            check(control)?;
            if let (Some(i), Some(j)) = (index.get(a), index.get(b)) {
                present.insert((*i, *j));
            }
        }
        let mut matrix = Vec::new();
        for (i, a) in membership.iter().enumerate() {
            for (j, b) in membership.iter().enumerate() {
                check(control)?;
                matrix.push(*a && *b && present.contains(&(i, j)));
            }
        }
        matrices.push(matrix);
    }
    check(control)?;
    let identifications = matrices
        .pop()
        .ok_or_else(|| ConstructionFailure::Inconsistent("identification queryがない".into()))?;
    let relations = matrices
        .pop()
        .ok_or_else(|| ConstructionFailure::Inconsistent("relation queryがない".into()))?;
    Ok(CircuitPattern {
        universe: atoms,
        membership,
        relations,
        identifications,
    })
}
/// 完全query patternと読取り適用域を生成する。読みの互換性やObjectAlgebraの成立とは別の構成。
pub fn construct_profiles(
    inputs: &CheckedInputs,
    reading: &str,
    snapshot: &str,
    root: &str,
    control: &mut Control,
) -> Result<ConfigurationProfiles, ConstructionFailure> {
    check(control)?;
    let construction = construct(inputs, reading, snapshot, root, control)?;
    let mut profiles = Vec::new();
    let base_pattern = construction
        .base()
        .configuration()
        .map(|c| pattern(c, construction.universe(), control))
        .transpose()?;
    profiles.push(ConfigurationProfile {
        object: ObjectIdentity::selected(reading, construction.root(), construction.root()),
        configuration: construction.base().clone(),
        domain: construction.local_domain().clone(),
        membership: None,
        pattern: base_pattern,
    });
    let mut parts = BTreeMap::new();
    for component in construction.components() {
        check(control)?;
        parts.insert(
            component.subject().clone(),
            (component.candidate().clone(), None),
        );
    }
    let mut index = BTreeMap::new();
    for snapshot in &inputs.archmap().snapshots {
        check(control)?;
        for subject in &snapshot.subjects {
            check(control)?;
            index.insert((subject.snapshot.as_str(), subject.id.as_str()), subject);
        }
    }
    for condition in construction.local_domain().conditional() {
        check(control)?;
        if !condition.is_entity() {
            continue;
        }
        let f = condition.subject();
        let selected = index
            .get(&(f.snapshot.as_str(), f.subject.as_str()))
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent("条件付き対象のsubjectがない".into())
            })?;
        let candidate = configuration(
            inputs,
            &[selected],
            &index,
            BTreeSet::from([condition.owner_slot().clone()]),
            control,
        )?;
        parts.insert(f.clone(), (candidate, Some(condition.clone())));
    }
    let ordered = canonical_facts(parts.keys().cloned().collect(), control)?;
    for subject in ordered {
        check(control)?;
        let (candidate, condition) = parts
            .remove(&subject)
            .ok_or_else(|| ConstructionFailure::Inconsistent("部分対象候補がない".into()))?;
        let pattern = if condition.is_none() {
            candidate
                .configuration()
                .map(|c| pattern(c, construction.universe(), control))
                .transpose()?
        } else {
            None
        };
        profiles.push(ConfigurationProfile {
            object: ObjectIdentity::selected(reading, construction.root(), &subject),
            configuration: candidate,
            domain: SubjectDomain {
                known: vec![subject],
                conditional: vec![],
            },
            membership: condition,
            pattern,
        });
    }
    let mut groups: BTreeMap<Vec<bool>, Vec<usize>> = BTreeMap::new();
    for (i, p) in profiles.iter().enumerate() {
        check(control)?;
        if let Some(pattern) = p.pattern() {
            groups.entry(pattern.key(control)?).or_default().push(i);
        }
    }
    let mut classes = Vec::new();
    for group in groups.into_values() {
        check(control)?;
        classes.push(group);
    }
    classes.sort_by_key(|members| members[0]);
    check(control)?;
    Ok(ConfigurationProfiles {
        construction,
        profiles,
        known_classes: classes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn relation_queries_require_both_endpoints_in_family() {
        let a = FactPointer {
            snapshot: "v".into(),
            subject: "a".into(),
            field: None,
            atom: None,
        };
        let b = FactPointer {
            snapshot: "v".into(),
            subject: "b".into(),
            field: None,
            atom: None,
        };
        let pairs = vec![
            (a.clone(), a.clone()),
            (a.clone(), b.clone()),
            (b.clone(), a.clone()),
            (b.clone(), b.clone()),
        ];
        let c = Configuration {
            family: vec![a.clone()],
            requirements: vec![],
            relations: pairs.clone(),
            identifications: pairs,
        };
        let p = pattern(&c, &[a, b], &mut Control::unlimited()).unwrap();
        assert_eq!(p.membership(), [true, false]);
        assert_eq!(p.relations(), [true, false, false, false]);
        assert_eq!(p.identifications(), [true, false, false, false]);
        assert_eq!(p.queries().count(), 10);
    }
    #[test]
    fn current_inputs_reject_forged_profiles_domains_patterns_and_classes() {
        let d = include_bytes!("../../tests/fixtures/configuration-profile.atoms.json");
        let definitions = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &definitions.vocabularies["Profile"].digest;
        let l = include_str!("../../tests/fixtures/configuration-profile.law")
            .replace("@PROFILE_DIGEST@", digest);
        let a = include_str!("../../tests/fixtures/configuration-profile.archmap.json")
            .replace("@PROFILE_DIGEST@", digest);
        let i = crate::observed::input::check_inputs(
            crate::observed::input::InputSources::from_bytes(
                vec![d.to_vec()],
                l.into_bytes(),
                a.into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap();
        let original =
            construct_profiles(&i, "ProfileRead", "v", "A", &mut Control::unlimited()).unwrap();
        for kind in 0..8 {
            let mut forged = original.clone();
            match kind {
                0 => {
                    forged.profiles[0].domain.known.pop();
                }
                1 => {
                    forged.profiles[0].pattern.as_mut().unwrap().membership[0] ^= true;
                }
                2 => {
                    forged.profiles[0].pattern.as_mut().unwrap().relations[0] ^= true;
                }
                3 => {
                    forged.profiles[0].pattern.as_mut().unwrap().identifications[0] ^= true;
                }
                4 => {
                    forged.known_classes[0].pop();
                }
                5 => {
                    forged.profiles.pop();
                }
                6 => {
                    forged.profiles[1].object = forged.profiles[0].object.clone();
                }
                _ => {
                    forged.profiles[1].membership = Some(ConditionalSubject {
                        subject: forged.profiles[1].object.subject().clone(),
                        owner_slot: FactPointer {
                            snapshot: "v".into(),
                            subject: "p".into(),
                            field: Some("Profile.Part.owner".into()),
                            atom: None,
                        },
                        owner: forged.construction.root().clone(),
                        entity: true,
                    });
                }
            }
            assert!(
                matches!(
                    forged.recheck(&i, &mut Control::unlimited()),
                    Err(ConstructionFailure::Inconsistent(_))
                ),
                "{kind}"
            );
        }
    }
}
