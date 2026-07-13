import Formal.AG.Atom.Family

namespace AAT.AG

universe u

/-- I.定義4.1: an Atom configuration `C = (F, R, E)`. -/
structure AtomConfiguration (U : AtomCarrier.{u}) where
  family : AtomFamily U
  relation : U.Atom -> U.Atom -> Prop
  identification : U.Atom -> U.Atom -> Prop

namespace AtomConfiguration

/-- Extensionality of configurations by family, relation, and identification. -/
@[ext] theorem ext {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (hfamily : C.family = D.family)
    (hrelation : ∀ a b, C.relation a b ↔ D.relation a b)
    (hidentification : ∀ a b, C.identification a b ↔ D.identification a b) :
    C = D := by
  cases C with
  | mk familyC relationC identificationC =>
      cases D with
      | mk familyD relationD identificationD =>
          cases hfamily
          congr 1
          · funext a b
            exact propext (hrelation a b)
          · funext a b
            exact propext (hidentification a b)

/-- I.定義4.4: configuration inclusion on family, relation, and identification data. -/
def Subconfiguration {U : AtomCarrier.{u}}
    (C' C : AtomConfiguration U) : Prop :=
  C'.family.Subset C.family ∧
    (∀ {a b}, C'.relation a b -> C.relation a b) ∧
      (∀ {a b}, C'.identification a b -> C.identification a b)

/-- I.定義4.1: relation and identification data are supported by the family. -/
def FamilySupported {U : AtomCarrier.{u}} (C : AtomConfiguration U) : Prop :=
  (∀ {a b}, C.relation a b -> C.family.mem a ∧ C.family.mem b) ∧
    (∀ {a b}, C.identification a b -> C.family.mem a ∧ C.family.mem b)

/-- I.定義4.2: a molecule is a selected configuration restricted from a parent. -/
structure Molecule {U : AtomCarrier.{u}} (C : AtomConfiguration U) where
  configuration : AtomConfiguration U
  isSubconfiguration : configuration.Subconfiguration C
  finite : Prop
  finite_holds : finite

namespace Subconfiguration

/-- I.定義4.4: subconfiguration is reflexive. -/
theorem refl {U : AtomCarrier.{u}} (C : AtomConfiguration U) :
    C.Subconfiguration C := by
  constructor
  · intro atom hAtom
    exact hAtom
  constructor
  · intro a b hRel
    exact hRel
  · intro a b hId
    exact hId

/-- I.定義4.4: subconfiguration is transitive. -/
theorem trans {U : AtomCarrier.{u}} {C1 C2 C3 : AtomConfiguration U}
    (h12 : C1.Subconfiguration C2)
    (h23 : C2.Subconfiguration C3) :
    C1.Subconfiguration C3 := by
  constructor
  · intro atom hAtom
    exact h23.1 (h12.1 hAtom)
  constructor
  · intro a b hRel
    exact h23.2.1 (h12.2.1 hRel)
  · intro a b hId
    exact h23.2.2 (h12.2.2 hId)

/-- I.定義4.4: subconfiguration forms a preorder relation. -/
theorem preorder {U : AtomCarrier.{u}} :
    (∀ C : AtomConfiguration U, C.Subconfiguration C) ∧
      (∀ {C1 C2 C3 : AtomConfiguration U},
        C1.Subconfiguration C2 ->
        C2.Subconfiguration C3 ->
        C1.Subconfiguration C3) :=
  ⟨refl, fun h12 h23 => trans h12 h23⟩

end Subconfiguration

namespace Molecule

/-- peer-review hardening I-3: a molecule is concretely finite when its selected family has a list cover. -/
def ListFinite {U : AtomCarrier.{u}} {C : AtomConfiguration U}
    (M : Molecule C) : Prop :=
  M.configuration.family.ListFinite

/-- I.定義4.2: a molecule inherits the family subset of its parent configuration. -/
theorem family_subset_parent {U : AtomCarrier.{u}} {C : AtomConfiguration U}
    (M : Molecule C) :
    M.configuration.family.Subset C.family :=
  M.isSubconfiguration.1

/-- I.定義4.2: the finite marker recorded by a molecule. -/
theorem finite_marker {U : AtomCarrier.{u}} {C : AtomConfiguration U}
    (M : Molecule C) :
    M.finite :=
  M.finite_holds

/--
peer-review hardening I-3: explicit list-finite evidence is the preferred finite reading for
new molecules; the legacy marker remains available for frozen declarations.
-/
theorem listFinite_has_cover {U : AtomCarrier.{u}} {C : AtomConfiguration U}
    (M : Molecule C) (h : M.ListFinite) :
    ∃ atoms : List U.Atom,
      ∀ atom, M.configuration.family.mem atom -> atom ∈ atoms :=
  h

end Molecule

end AtomConfiguration

end AAT.AG
