import Formal.AG.Atom.Atom

namespace AAT.AG

universe u

/-- I.公理A3: the five visible coordinates carried by two atoms agree. -/
def SameCoordinates (U : AtomCarrier.{u}) (a b : U.Atom) : Prop :=
  U.kind a = U.kind b ∧
    U.axis a = U.axis b ∧
    U.subject a = U.subject b ∧
    U.predicate a = U.predicate b ∧
    U.payload a = U.payload b

/--
I.公理A8 Essential Uniqueness.

An extraction doctrine is a typed source reading together with a canonical
`atomize` function into the selected family carrier. The source-side fields are
opaque at PRD-1/R1 level; later PRD steps can refine them without changing the
uniqueness theorem below.
-/
structure ExtractionDoctrine (U : AtomCarrier.{u}) (Family : Type u) where
  Source : Type u
  Vocabulary : Type u
  SemanticReading : Type u
  Resolution : Type u
  sourceSemantics : Source -> Type u
  normalize : Source -> Source
  atomize : Source -> Family

namespace ExtractionDoctrine

/--
I.公理A8: the canonical family selected by a doctrine is unique because
`atomize` is a function.
-/
theorem atomize_unique {U : AtomCarrier.{u}} {Family : Type u}
    (D : ExtractionDoctrine U Family) (source : D.Source)
    {F G : Family}
    (hF : F = D.atomize source) (hG : G = D.atomize source) : F = G := by
  rw [hF, hG]

end ExtractionDoctrine

/-- I.公理A8: a coarse projection used to read a family at lower resolution. -/
structure CoarseProjection (Family CoarseFamily : Type u) where
  pi : Family -> CoarseFamily

/--
I.公理A0-A8 as a parameterized package over an AG Atom carrier.

The package records the extra carriers needed by the Part I tower without
importing Classic AAT. Law and observation fields have no map returning
`U.Atom`, while operations act on families and therefore preserve atom-origin
at the type level.
-/
structure AtomAxiomSystem (U : AtomCarrier.{u}) where
  primitiveExistence : Nonempty U.Atom
  singleFact : U.Atom -> Prop
  singleFact_holds : ∀ atom, singleFact atom
  predicateStability : ∀ a b, SameCoordinates U a b ↔ a = b
  Family : Type u
  Configuration : Type u
  compose : Family -> Configuration
  Law : Type u
  lawHolds : Law -> Configuration -> Prop
  ObservationDomain : Type u
  Observation : Type u
  observe : ObservationDomain -> Observation
  Operation : Type u
  operate : Operation -> Family -> Family
  Doctrine : Type u
  doctrine : Doctrine -> ExtractionDoctrine U Family

namespace AtomAxiomSystem

/-- I.公理A0: at least one primitive atom exists in the selected universe. -/
theorem primitive_exists {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) :
    ∃ _atom : U.Atom, True :=
  S.primitiveExistence.elim fun atom => ⟨atom, trivial⟩

/-- I.公理A1: coordinates are total because they are projections on `AtomCarrier`. -/
theorem typing_total {U : AtomCarrier.{u}} (_S : AtomAxiomSystem U)
    (atom : U.Atom) :
    (∃ kind, U.kind atom = kind) ∧
      (∃ axis, U.axis atom = axis) ∧
      (∃ subject, U.subject atom = subject) ∧
      (∃ predicate, U.predicate atom = predicate) ∧
      (∃ payload, U.payload atom = payload) :=
by
  constructor
  · exact ⟨U.kind atom, rfl⟩
  constructor
  · exact ⟨U.axis atom, rfl⟩
  constructor
  · exact ⟨U.subject atom, rfl⟩
  constructor
  · exact ⟨U.predicate atom, rfl⟩
  · exact ⟨U.payload atom, rfl⟩

/-- I.公理A3: five-coordinate agreement is equivalent to atom equality. -/
theorem eq_iff_sameCoordinates {U : AtomCarrier.{u}} (S : AtomAxiomSystem U)
    {a b : U.Atom} :
    a = b ↔ SameCoordinates U a b :=
  (S.predicateStability a b).symm

/-- I.公理A3: extensionality for AG atoms. -/
theorem ext {U : AtomCarrier.{u}} (S : AtomAxiomSystem U)
    {a b : U.Atom} (h : SameCoordinates U a b) : a = b :=
  (S.predicateStability a b).mp h

/-- I.公理A4: composition is the configured map from families to configurations. -/
def configurationOf {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) :
    S.Family -> S.Configuration :=
  S.compose

/-- I.公理A7: operations preserve atom-origin by returning another family. -/
def operateFamily {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) :
    S.Operation -> S.Family -> S.Family :=
  S.operate

/-- I.公理A8: doctrine-specific canonical family uniqueness. -/
theorem doctrine_family_unique {U : AtomCarrier.{u}} (S : AtomAxiomSystem U)
    (doctrine : S.Doctrine) (source : (S.doctrine doctrine).Source)
    {F G : S.Family}
    (hF : F = (S.doctrine doctrine).atomize source)
    (hG : G = (S.doctrine doctrine).atomize source) : F = G :=
  ExtractionDoctrine.atomize_unique (S.doctrine doctrine) source hF hG

end AtomAxiomSystem

end AAT.AG
