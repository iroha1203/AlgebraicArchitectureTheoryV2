import Formal.AG.Atom.Family

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
I.公理A8 Essential Uniqueness: the data used to read atoms from a source.

The selected vocabulary, semantic reading, resolution, and normalized source
semantics all contribute to `ExtractionDoctrine.extracts`.

Implementation notes: this structure records the inputs and admissibility
relations of Part I, Definitions 10.1 and 10.4A. It deliberately does not store
an atom family or an `atomize` function: the canonical family is constructed
extensionally from `extracts`, so essential uniqueness is proved rather than
supplied as data. The former presentation with an abstract family carrier was
rejected because it did not produce an actual `AtomFamily U` and reduced A8 to
equality with a preselected output.
-/
structure ExtractionDoctrine (U : AtomCarrier.{u}) where
  Source : Type u
  Vocabulary : Type u
  SemanticReading : Type u
  Resolution : Type u
  /-- The selected vocabulary value. -/
  vocabulary : Vocabulary
  /-- The selected semantic reading value. -/
  semanticReading : SemanticReading
  /-- The selected extraction resolution. -/
  resolution : Resolution
  /-- Vocabulary-level admission of an atom. -/
  vocabularyAllows : Vocabulary -> U.Atom -> Prop
  /-- Semantic admission of an atom from a normalized source. -/
  semanticAllows : SemanticReading -> Source -> U.Atom -> Prop
  /-- Resolution-level admission of an atom from a normalized source. -/
  resolutionAllows : Resolution -> Source -> U.Atom -> Prop
  sourceSemantics : Source -> U.Atom -> Prop
  normalize : Source -> Source

namespace ExtractionDoctrine

/--
I.定義10.4A: an atom is extracted exactly when every selected reading admits it.

Implementation notes: this conjunction exposes every material component of an
extraction doctrine to proof use. An opaque relation field was rejected because
it would leave vocabulary, semantic, resolution, and normalization data
mathematically inert.
-/
def extracts {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) (atom : U.Atom) : Prop :=
  D.vocabularyAllows D.vocabulary atom ∧
    D.semanticAllows D.semanticReading (D.normalize source) atom ∧
    D.resolutionAllows D.resolution (D.normalize source) atom ∧
    D.sourceSemantics (D.normalize source) atom

/--
Extraction is exactly simultaneous admission by the selected vocabulary,
semantic reading, resolution, and normalized source semantics.
-/
theorem extracts_iff {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) (atom : U.Atom) :
    D.extracts source atom ↔
      D.vocabularyAllows D.vocabulary atom ∧
        D.semanticAllows D.semanticReading (D.normalize source) atom ∧
        D.resolutionAllows D.resolution (D.normalize source) atom ∧
        D.sourceSemantics (D.normalize source) atom :=
  Iff.rfl

/--
I.定義10.4A: construct the canonical atom family extracted from a source.

Implementation notes: the family is the characteristic predicate `extracts`.
Selecting an opaque family and separately asserting its correctness was
rejected because correctness and uniqueness would then be stored premises.
-/
def atomize {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) : AtomFamily U where
  mem atom := D.extracts source atom

/-- Membership in the canonical atomization is exactly source extraction. -/
theorem atomize_mem_iff {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) (atom : U.Atom) :
    (D.atomize source).mem atom ↔ D.extracts source atom :=
  Iff.rfl

/--
I.定義10.4A: a family realizes the extraction relation for a source.

Implementation notes: the pointwise biconditional is the extensional
presentation appropriate to predicate-valued `AtomFamily`. Equality with the
canonical family was rejected as the primitive relation because it would make
essential uniqueness a restatement of the relation's definition.
-/
def Atomizes {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source)
    (family : AtomFamily U) : Prop :=
  ∀ atom, family.mem atom ↔ D.extracts source atom

/-- Any realizing family has membership exactly when the doctrine extracts the atom. -/
theorem mem_iff_extracts_of_atomizes {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) (family : AtomFamily U)
    (h : D.Atomizes source family) (atom : U.Atom) :
    family.mem atom ↔ D.extracts source atom :=
  h atom

/-- I.定理10.5: the canonical family realizes its source extraction relation. -/
theorem atomize_holds {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) :
    D.Atomizes source (D.atomize source) := by
  intro atom
  rfl

/--
I.定理10.5 Essential Uniqueness: two families realizing one source are equal.
-/
theorem atomize_unique {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source)
    {F G : AtomFamily U}
    (hF : D.Atomizes source F) (hG : D.Atomizes source G) :
    F = G := by
  cases F with
  | mk f =>
      cases G with
      | mk g =>
          congr 1
          funext atom
          exact propext ((hF atom).trans (hG atom).symm)

/-- I.定理10.5: every realizing family equals the canonical atomization. -/
theorem eq_atomize {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source)
    {F : AtomFamily U} (hF : D.Atomizes source F) :
    F = D.atomize source :=
  D.atomize_unique source hF (D.atomize_holds source)

end ExtractionDoctrine

/-- I.公理A8: a coarse projection used to read a family at lower resolution. -/
structure CoarseProjection (Family CoarseFamily : Type u) where
  pi : Family -> CoarseFamily

/--
I.公理A0-A3 as the primitive foundation package over an AG Atom carrier.

Implementation notes: the package retains only primitive existence and the
five-coordinate extensionality principle. Family extraction, composition,
operations, laws, and observations belong to the separate core reading that
constructs the Part I tower. The former abstract tower carriers were rejected
because they did not provide the actual `AtomFamily`, configuration, and object
required by downstream generation. A `singleFact` predicate was also rejected:
with a proof for every atom it carried no information beyond the atom's typed
coordinate tuple.
-/
structure AtomAxiomSystem (U : AtomCarrier.{u}) where
  primitiveExistence : Nonempty U.Atom
  predicateStability : ∀ a b, SameCoordinates U a b ↔ a = b

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

end AtomAxiomSystem

end AAT.AG
