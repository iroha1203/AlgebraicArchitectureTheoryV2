import Formal.AG.SemanticRepair.SagaComparison

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory
open Opposite

universe u v w x y z r

/-! ## X.§8 boundary theorems for semantic repair SAGA -/

/-- X.定理8.1: pointwise zero reading for the generated degree-zero cochain. -/
def GeneratedSourceC0PointwiseZero
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G) : Prop :=
  forall i : D.Chart, D.interpret i = 0

/--
X.定理8.1: Cech-zero reading for the generated degree-zero cochain.

At this boundary level the generated Cech-zero predicate is the selected
restriction evaluator produced by the law-equation grounding surface.  It is a
degree-zero conclusion only; it does not include residual-zero, H1-zero,
descent, or global-coherence conclusions.
-/
def GeneratedSourceC0CechZero
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G) : Prop :=
  D.GeneratedRestrictionEvaluator

/-- X.定理8.1 package: law fulfillment generates only degree-zero zero readings. -/
structure GeneratedSourceC0ZeroPackage
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G) : Type (u + 1) where
  pointwiseZero : GeneratedSourceC0PointwiseZero D
  cechZero : GeneratedSourceC0CechZero D

/-- X.定理8.1: displayed law satisfaction gives pointwise zero. -/
theorem displayedRequiredLawsHoldOn_constructs_generatedSourceC0_pointwiseZero
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    GeneratedSourceC0PointwiseZero D :=
  D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds

/-- X.定理8.1: displayed law satisfaction gives the generated Cech-zero reading. -/
theorem displayedRequiredLawsHoldOn_constructs_generatedSourceC0_cechZero
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    GeneratedSourceC0CechZero D :=
  D.displayedRequiredLawsHoldOn_constructs_restrictionEvaluator hholds

/-- X.定理8.1: degree-zero law-generated zero package. -/
theorem displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    Nonempty (GeneratedSourceC0ZeroPackage D) :=
  ⟨{ pointwiseZero :=
        displayedRequiredLawsHoldOn_constructs_generatedSourceC0_pointwiseZero
          D hholds,
      cechZero :=
        displayedRequiredLawsHoldOn_constructs_generatedSourceC0_cechZero
          D hholds }⟩

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
       higherObstructionsVanish :=
         ⟨package73.nonabelianTorsorTrivial,
           package73.higherCoherenceVanishes,
           package73.stackEffectivelyVanishes⟩ }⟩

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

/-- X.定理8.4: zero preservation is a theorem of supplied comparison data. -/
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
-/
theorem typedComparisonTarget_not_unconditional_for_emptyTarget :
    IsEmpty (SemanticRepairTypedComparisonTarget PUnit Empty) := by
  refine ⟨?_⟩
  intro comparison
  exact Empty.elim (comparison.toTarget PUnit.unit)

/-- X.定理8.5 typed refinement comparison with explicit zero preservation. -/
structure SemanticRepairRefinementZeroComparison
    (Coarse : Type u) (Fine : Type v)
    (coarseZero : Coarse -> Prop) (fineZero : Fine -> Prop) :
    Type (max u v) where
  pullback : Coarse -> Fine
  zero_preserved :
    forall coarse, coarseZero coarse -> fineZero (pullback coarse)

/-- X.定理8.5: refinement zero preservation is data-relative. -/
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

/--
X.§8 fail-closed boundary: cover-relative H1 grounding still requires an
explicit comparison object.
-/
theorem coverRelativeH1Boundary_requires_explicit_comparison_provenance
    {additive : SemanticRepairAdditiveH1Surface.{y, x, z}}
    {U : AtomCarrier.{r}}
    {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {cover : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex cover Ob}
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Nonempty (SemanticRepairCoverRelativeH1Comparison additive K) :=
  ⟨comparison⟩

/--
X.§8 fail-closed boundary: cover-level provenance is not cochain realization
provenance; the latter remains explicit data.
-/
theorem coverRelativeH1Boundary_requires_explicit_cochainRealization_provenance
    {additive : SemanticRepairAdditiveH1Surface.{y, x, z}}
    {U : AtomCarrier.{r}}
    {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {cover : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex cover Ob}
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) :=
  ⟨realization⟩

end SemanticRepair
end AAT.AG
