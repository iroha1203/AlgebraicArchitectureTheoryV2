import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonInjectivity
import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonSurjectivity
import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonNaturality
import Formal.Util.AssertStandardAxioms

/-!
# Bijectivity of the generated comparison on cohomology

This module combines the two reviewed exact-block arguments through the fixed
condition package.  It then transports their pointwise bijectivity across the
finite direct sum and the Cycle 13 naturality square to the actual global
generated comparison map.

The main result concerns the canonical `generatedComparisonH1Map` itself.  No
inverse, dimension equality, or alternate conjugate map is supplied as data.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution DirectSum TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-- The fixed C0--C6 package makes the actual generated comparison map on each
exact source-generated block bijective. -/
theorem generatedBlockComparisonH1Map_bijective [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC : M.ConditionC laws hcoarse hfine)
    (label : LawValueLabel laws) :
    Function.Bijective
      (M.generatedBlockComparisonH1Map laws hcoarse hfine label) := by
  exact ⟨M.generatedBlockComparisonH1Map_injective laws hcoarse hfine label
      hC.c0 (hC.c1 label) (hC.c2 label) hC.c6,
    M.generatedBlockComparisonH1Map_surjective laws hcoarse hfine label
      (hC.c2 label) (hC.c3 label) (hC.c4 label) hC.c5⟩

/-- Pointwise exact-block bijectivity makes the existing componentwise finite
direct-sum comparison map bijective. -/
theorem generatedBlockComparisonH1DirectSumMap_bijective [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC : M.ConditionC laws hcoarse hfine) :
    Function.Bijective
      (M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine) := by
  let coarseEquiv :=
    DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label =>
        (coarse.lawValueBlockComplex laws hcoarse label).H1)
  let fineEquiv :=
    DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label =>
        (fine.lawValueBlockComplex laws hfine label).H1)
  constructor
  · intro left right hequal
    apply coarseEquiv.injective
    funext label
    apply
      (M.generatedBlockComparisonH1Map_bijective laws hcoarse hfine hC
        label).1
    have hcomponent := congrArg (fun classes => fineEquiv classes label) hequal
    simpa only [M.generatedBlockComparisonH1DirectSumMap_component] using
      hcomponent
  · intro fineClasses
    let preimage :
        (label : LawValueLabel laws) →
          (coarse.lawValueBlockComplex laws hcoarse label).H1 :=
      fun label =>
        Classical.choose
          ((M.generatedBlockComparisonH1Map_bijective laws hcoarse hfine hC
            label).2 (fineEquiv fineClasses label))
    have hpreimage (label : LawValueLabel laws) :
        M.generatedBlockComparisonH1Map laws hcoarse hfine label
            (preimage label) =
          fineEquiv fineClasses label :=
      Classical.choose_spec
        ((M.generatedBlockComparisonH1Map_bijective laws hcoarse hfine hC
          label).2 (fineEquiv fineClasses label))
    refine ⟨coarseEquiv.symm preimage, ?_⟩
    apply fineEquiv.injective
    funext label
    rw [M.generatedBlockComparisonH1DirectSumMap_component]
    rw [coarseEquiv.apply_symm_apply]
    exact hpreimage label

/-- Under the fixed C0--C6 package, the actual global generated comparison
map on G-102 cohomology is bijective. -/
theorem generatedComparisonH1Map_bijective [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC : M.ConditionC laws hcoarse hfine) :
    Function.Bijective
      (M.generatedComparisonH1Map laws hcoarse hfine) := by
  let coarseEquiv := coarse.lawGeneratedH1BlockEquiv laws hcoarse
  let fineEquiv := fine.lawGeneratedH1BlockEquiv laws hfine
  let blockMap := M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine
  have hblock : Function.Bijective blockMap :=
    M.generatedBlockComparisonH1DirectSumMap_bijective laws hcoarse hfine hC
  have hnatural
      (coarseClass : (coarse.lawGeneratedComplex laws hcoarse).H1) :
      fineEquiv
          (M.generatedComparisonH1Map laws hcoarse hfine coarseClass) =
        blockMap (coarseEquiv coarseClass) := by
    have hpoint := LinearMap.congr_fun
      (M.generatedComparisonH1Map_block_naturality laws hcoarse hfine)
      coarseClass
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hpoint
  constructor
  · intro left right hequal
    apply coarseEquiv.injective
    apply hblock.1
    calc
      blockMap (coarseEquiv left) =
          fineEquiv
            (M.generatedComparisonH1Map laws hcoarse hfine left) :=
        (hnatural left).symm
      _ = fineEquiv
            (M.generatedComparisonH1Map laws hcoarse hfine right) := by
        rw [hequal]
      _ = blockMap (coarseEquiv right) := hnatural right
  · intro fineClass
    obtain ⟨coarseBlocks, hcoarseBlocks⟩ := hblock.2 (fineEquiv fineClass)
    refine ⟨coarseEquiv.symm coarseBlocks, ?_⟩
    apply fineEquiv.injective
    calc
      fineEquiv
          (M.generatedComparisonH1Map laws hcoarse hfine
            (coarseEquiv.symm coarseBlocks)) =
          blockMap (coarseEquiv (coarseEquiv.symm coarseBlocks)) :=
        hnatural _
      _ = blockMap coarseBlocks := by rw [coarseEquiv.apply_symm_apply]
      _ = fineEquiv fineClass := hcoarseBlocks

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
