import Formal.AG.Atom.Axioms
import Formal.AG.Examples.FiniteModel
import Formal.Util.AssertStandardAxioms
import Mathlib.Data.Set.Finite.Basic

/-!
# Semantic-dependence profile for the two-phase obstruction theorem

This module discharges stage E0 of
`G-102-aat-two-phase-obstruction`.  It replaces only the semantic-reading
component of an `ExtractionDoctrine`, derives the structural/semantic phase of
a source--Atom pair from extraction invariance across a declared family, and
constructs a finite family on `FiniteModel` in which both phases occur.

## Implementation notes

`SemanticVariant` stores exactly the pair named by the GOAL: a selected semantic
reading and its semantic-admissibility predicate.  All other doctrine data are
copied by `replaceSemantic`.  A phase label or a proof that a pair is structural
is deliberately not stored: phase membership is computed propositionally from
`ExtractionDoctrine.extracts`.

The finite witness changes semantic admissibility to the constant-true
predicate.  This predicate is specified before, and independently of, either
phase witness.  The existing `FiniteModel` extraction calculation then proves
that `componentA` is invariant while `componentC` changes truth value.  A
singleton family was rejected because it would make every pair structural.
-/

namespace AAT.AG.TwoPhase

universe u

/-- A source--Atom pair whose extraction phase is tested. -/
abbrev ExtractionPair {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :=
  D.Source × U.Atom

/--
The replaceable semantic component of an extraction doctrine.

No extraction result, phase label, or conclusion-side property is stored here.
-/
structure SemanticVariant {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) where
  /-- The selected semantic-reading value. -/
  semanticReading : D.SemanticReading
  /-- The semantic-admissibility predicate selected with that reading. -/
  semanticAllows : D.SemanticReading → D.Source → U.Atom → Prop

namespace SemanticVariant

/-- The original semantic component of a doctrine, packaged as a variant. -/
def original {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    SemanticVariant D where
  semanticReading := D.semanticReading
  semanticAllows := D.semanticAllows

/--
Replace only a doctrine's semantic-reading value and admissibility predicate.

Vocabulary, resolution, normalization, and source semantics are definitionally
the original doctrine data.
-/
def replaceSemantic {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D) : ExtractionDoctrine U where
  Source := D.Source
  Vocabulary := D.Vocabulary
  SemanticReading := D.SemanticReading
  Resolution := D.Resolution
  vocabulary := D.vocabulary
  semanticReading := variant.semanticReading
  resolution := D.resolution
  vocabularyAllows := D.vocabularyAllows
  semanticAllows := variant.semanticAllows
  resolutionAllows := D.resolutionAllows
  sourceSemantics := D.sourceSemantics
  normalize := D.normalize

/-- Replacing a doctrine by its original semantic component preserves extraction. -/
@[simp]
theorem replaceSemantic_original_extracts_iff
    {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) (atom : U.Atom) :
    (original D).replaceSemantic.extracts source atom ↔ D.extracts source atom :=
  Iff.rfl

end SemanticVariant

/--
A declared semantic-reading family containing the original doctrine component.

The membership proof also supplies the required nonemptiness, so a redundant
nonempty field is not included.
-/
structure DeclaredSemanticFamily {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) where
  /-- Declared variants over which extraction invariance is tested. -/
  members : Set (SemanticVariant D)
  /-- The doctrine's own semantic component belongs to the family. -/
  original_mem : SemanticVariant.original D ∈ members

namespace DeclaredSemanticFamily

/-- Every declared family is nonempty because it contains the original variant. -/
theorem nonempty {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) : family.members.Nonempty :=
  ⟨SemanticVariant.original D, family.original_mem⟩

/--
A pair is structural when extraction truth is invariant under every declared
semantic replacement.
-/
def Structural {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (pair : ExtractionPair D) : Prop :=
  ∀ variant, variant ∈ family.members →
    (variant.replaceSemantic.extracts pair.1 pair.2 ↔
      D.extracts pair.1 pair.2)

/-- A pair is semantic precisely when the declared family can change extraction truth. -/
def Semantic {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (pair : ExtractionPair D) : Prop :=
  ¬ family.Structural pair

/-- No external label intervenes in the structural classification. -/
theorem structural_iff_family_invariant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (pair : ExtractionPair D) :
    family.Structural pair ↔
      ∀ variant, variant ∈ family.members →
        (variant.replaceSemantic.extracts pair.1 pair.2 ↔
          D.extracts pair.1 pair.2) :=
  Iff.rfl

/-- Semanticity is witnessed by an actual variant that changes extraction truth. -/
theorem semantic_iff_exists_variant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (pair : ExtractionPair D) :
    family.Semantic pair ↔
      ∃ variant, variant ∈ family.members ∧
        ¬ (variant.replaceSemantic.extracts pair.1 pair.2 ↔
          D.extracts pair.1 pair.2) := by
  classical
  simp [Semantic, Structural]

/-- Every pair lies in exactly one of the two derived phases. -/
theorem structural_or_semantic
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (pair : ExtractionPair D) :
    family.Structural pair ∨ family.Semantic pair :=
  Classical.em (family.Structural pair)

/-- The two derived phases cannot overlap. -/
theorem not_structural_and_semantic
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (pair : ExtractionPair D) :
    ¬ (family.Structural pair ∧ family.Semantic pair) :=
  fun h => h.2 h.1

end DeclaredSemanticFamily

namespace FiniteDependencyProfile

open FiniteModel

/-- The finite-model doctrine used by the E0 firing witness. -/
abbrev doctrine : ExtractionDoctrine FiniteModel.carrier :=
  FiniteModel.extractionDoctrine

/--
A concrete semantic variant that admits every source--Atom pair.

Its definition depends only on the finite doctrine's semantic component types,
not on the desired phase classification.
-/
def permissiveVariant : SemanticVariant doctrine where
  semanticReading := PUnit.unit
  semanticAllows := fun _reading _source _atom => True

/-- The two-element declared family consisting of the original and permissive variants. -/
def family : DeclaredSemanticFamily doctrine where
  members := {SemanticVariant.original doctrine, permissiveVariant}
  original_mem := by simp

/-- The declared E0 witness family is genuinely finite. -/
theorem family_finite : family.members.Finite := by
  simp [family]

/-- The permissive replacement extracts every finite-model pair. -/
theorem permissive_extracts (source : doctrine.Source)
    (atom : FiniteModel.carrier.Atom) :
    permissiveVariant.replaceSemantic.extracts source atom := by
  simp [permissiveVariant, SemanticVariant.replaceSemantic,
    ExtractionDoctrine.extracts, FiniteModel.extractionDoctrine]

/-- The permissive semantic component is not the original component. -/
theorem permissiveVariant_ne_original :
    permissiveVariant ≠ SemanticVariant.original doctrine := by
  intro h
  have hExtracts := permissive_extracts
    ExtractionSource.withoutComponentC FiniteAtom.componentC
  rw [h] at hExtracts
  exact FiniteModel.componentC_not_extracted_withoutComponentC
    (by simpa using hExtracts)

/--
`componentA` is structural: both members of the nontrivial family extract it
from the selected source.
-/
theorem componentA_structural :
    family.Structural
      (ExtractionSource.withoutComponentC, FiniteAtom.componentA) := by
  intro variant hvariant
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hvariant
  rcases hvariant with rfl | rfl
  · exact Iff.rfl
  · constructor
    · intro _h
      exact FiniteModel.componentA_extracted_withoutComponentC
    · intro _h
      exact permissive_extracts
        ExtractionSource.withoutComponentC FiniteAtom.componentA

/--
`componentC` is semantic: the permissive variant extracts it while the original
finite doctrine does not.
-/
theorem componentC_semantic :
    family.Semantic
      (ExtractionSource.withoutComponentC, FiniteAtom.componentC) := by
  apply (family.semantic_iff_exists_variant
    (ExtractionSource.withoutComponentC, FiniteAtom.componentC)).2
  refine ⟨permissiveVariant, ?_, ?_⟩
  · simp [family]
  · intro hiff
    exact FiniteModel.componentC_not_extracted_withoutComponentC
      (hiff.mp (permissive_extracts
        ExtractionSource.withoutComponentC FiniteAtom.componentC))

/-- Both derived phases occur in one finite, non-singleton declared family. -/
theorem both_phases_nonempty :
    (∃ pair : ExtractionPair doctrine, family.Structural pair) ∧
      (∃ pair : ExtractionPair doctrine, family.Semantic pair) :=
  ⟨⟨(ExtractionSource.withoutComponentC, FiniteAtom.componentA),
      componentA_structural⟩,
    ⟨(ExtractionSource.withoutComponentC, FiniteAtom.componentC),
      componentC_semantic⟩⟩

end FiniteDependencyProfile

end AAT.AG.TwoPhase

#assert_standard_axioms_only AAT.AG.TwoPhase
