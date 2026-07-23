import Formal.AG.SemanticRepair.SagaComparison
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory
open Opposite

universe u v w x y z r

/-! ## X.§8 boundary theorems for semantic repair SAGA -/

/--
X.定理8.2: the law-independent conclusion group of theorem 7.5 is available
without any law-equation premise.
-/
theorem generatedSAGA_lawIndependentConclusions_withoutLawPremise
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    {U : AtomCarrier.{r}}
    {A : ArchitectureObject U}
    (S : Site.AATSite A)
    (F : Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate : data.TrueSheafConditionCertificate S F cover)
    (gluingData : Site.AATGluingData S F cover)
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (comparison :
      SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K) :
    Nonempty
      (SemanticRepairGeneratedLawIndependentConclusions
        data S F cover gluingData comparison) := by
  rcases
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package
      data S F cover certificate gluingData comparison with
    ⟨package73⟩
  exact
    ⟨{ groundedGlobalGluingPackage := ⟨package73⟩
       sheafConditionFor := package73.sheafConditionFor
       descent := package73.descent
       uniqueGlobalSection := package73.uniqueGlobalSection
       globalCoherent_iff_coverRelativeH1Zero :=
         package73.globalCoherent_iff_coverRelativeH1Zero
       boundedAdditiveH1Zero_iff_coverRelativeH1Zero :=
         package73.boundedAdditiveH1Zero_iff_coverRelativeH1Zero
       torsorTrivialization := package73.torsorTrivialization_of_h1Zero }⟩

/--
X.定理8.4 typed comparison target.

The target carrier is explicit data.  This structure is intentionally below
any zero verdict or descent theorem.
-/
structure SemanticRepairTypedComparisonTarget
    (Source : Type u) (Target : Type v) : Type (max u v) where
  toTarget : Source -> Target

/-- X.定理8.4 data-relative zero-preservation comparison. -/
structure SemanticRepairTypedZeroComparison
    (Source : Type u) (Target : Type v)
    (sourceZero : Source -> Prop) (targetZero : Target -> Prop) :
    Type (max u v) where
  target : SemanticRepairTypedComparisonTarget Source Target
  zero_preserved :
    forall source, sourceZero source -> targetZero (target.toTarget source)

/--
X.定理8.4: zero preservation is a theorem of supplied comparison data.

Auxiliary restatement: this projects the `zero_preserved` field of the
supplied comparison.  It documents that the comparison is data — it is not an
independent zero-preservation theorem, and carries no content beyond its
input.
-/
theorem typedZeroComparison_preserves_zero
    {Source : Type u} {Target : Type v}
    {sourceZero : Source -> Prop} {targetZero : Target -> Prop}
    (comparison :
      SemanticRepairTypedZeroComparison Source Target sourceZero targetZero)
    (source : Source) :
    sourceZero source -> targetZero (comparison.target.toTarget source) :=
  comparison.zero_preserved source

/--
X.定理8.4 counterexample layer: no typed comparison can target an empty
carrier from a selected inhabited source.

Role division (#3722): this is the minimal auxiliary type-level layer.  The
spec-facing main counterexample lives on the circle entity with its nonzero
cover-relative `H^1` class:
`Examples.SemanticRepairPart10.circleTypedComparisonTarget_impossible_forEmptyCoefficient`.
-/
theorem typedComparisonTarget_not_unconditional_for_emptyTarget :
    IsEmpty (SemanticRepairTypedComparisonTarget PUnit Empty) := by
  refine ⟨?_⟩
  intro comparison
  exact Empty.elim (comparison.toTarget PUnit.unit)

/--
X.定理8.4 carrier non-uniformity witness: a singleton carrier and the
nontrivial `ZMod 2` carrier are materially different comparison targets.
-/
theorem typedComparisonTarget_carrier_nonuniformity_punit_zmod2 :
    Nonempty (SemanticRepairTypedComparisonTarget PUnit (ZMod 2)) ∧
      Nontrivial (ZMod 2) := by
  constructor
  · exact ⟨{ toTarget := fun _ => 0 }⟩
  · infer_instance

/-- X.定理8.5 typed refinement comparison with explicit zero preservation. -/
structure SemanticRepairRefinementZeroComparison
    (Coarse : Type u) (Fine : Type v)
    (coarseZero : Coarse -> Prop) (fineZero : Fine -> Prop) :
    Type (max u v) where
  pullback : Coarse -> Fine
  zero_preserved :
    forall coarse, coarseZero coarse -> fineZero (pullback coarse)

/--
X.定理8.5: refinement zero preservation is data-relative.

Auxiliary restatement: this projects the `zero_preserved` field of the
supplied comparison.  It documents that the refinement comparison is data —
it is not an independent zero-preservation theorem, and carries no content
beyond its input.
-/
theorem refinementZeroComparison_preserves_zero
    {Coarse : Type u} {Fine : Type v}
    {coarseZero : Coarse -> Prop} {fineZero : Fine -> Prop}
    (comparison :
      SemanticRepairRefinementZeroComparison Coarse Fine coarseZero fineZero)
    (coarse : Coarse) :
    coarseZero coarse -> fineZero (comparison.pullback coarse) :=
  comparison.zero_preserved coarse

/--
X.定理8.5: a coarse-zero / fine-nonzero witness blocks any supplied
zero-preserving refinement comparison.
-/
theorem refinementZeroComparison_blocks_coarseZero_fineNonzero
    {Coarse : Type u} {Fine : Type v}
    {coarseZero : Coarse -> Prop} {fineZero : Fine -> Prop}
    (comparison :
      SemanticRepairRefinementZeroComparison Coarse Fine coarseZero fineZero)
    (coarse : Coarse)
    (hcoarse : coarseZero coarse)
    (hfineNonzero : ¬ fineZero (comparison.pullback coarse)) :
    False :=
  hfineNonzero (comparison.zero_preserved coarse hcoarse)

/--
X.定理8.5 counterexample layer: a coarse point that is always zero and a fine
point that is never zero allow no unconditional zero-preserving refinement
comparison.

Role division (#3722): this is the minimal auxiliary type-level layer.  The
spec-facing main counterexample runs from the lawful singleton complex to the
circle complex:
`Examples.SemanticRepairPart10.circleRefinementZeroComparison_not_unconditional_onCircle`.
-/
theorem refinementZeroComparison_not_unconditional_for_coarseZero_fineNonzero :
    IsEmpty
      (SemanticRepairRefinementZeroComparison
        PUnit PUnit (fun _ => True) (fun _ => False)) := by
  refine ⟨?_⟩
  intro comparison
  exact
    refinementZeroComparison_blocks_coarseZero_fineNonzero
      comparison PUnit.unit trivial (by intro h; exact h)

end SemanticRepair
end AAT.AG
