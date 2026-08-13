import ResearchLean.AG.UniformInvariance.ASubnerveReduction
import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonNaturality
import Formal.Util.AssertStandardAxioms

/-!
# Global and blockwise bijectivity

This module proves the second reduction conjunct in U0 of
`G-107-aat-uniform-invariance-characterization`: the actual global generated
comparison on `H¹` is bijective exactly when every actual source-generated
law-value-block comparison is bijective.

The proof first establishes the corresponding statement for the existing
componentwise finite direct-sum map.  It then transports that equivalence
through the reviewed G-104 global block decompositions and naturality square.
No `ConditionC`, inverse map, rank equality, or alternative conjugate
comparison is supplied as data.
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

/-- The existing componentwise map on the finite direct sum is bijective
exactly when its actual block map is bijective at every source-generated
label. -/
theorem generatedBlockComparisonH1DirectSumMap_bijective_iff
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    Function.Bijective
        (M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine) ↔
      ∀ label : LawValueLabel laws,
        Function.Bijective
          (M.generatedBlockComparisonH1Map laws hcoarse hfine label) := by
  classical
  let coarseEquiv :=
    DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label =>
        (coarse.lawValueBlockComplex laws hcoarse label).H1)
  let fineEquiv :=
    DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label =>
        (fine.lawValueBlockComplex laws hfine label).H1)
  let blockMap :=
    M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine
  constructor
  · intro hblockMap label
    constructor
    · intro left right hequal
      let leftBlocks := coarseEquiv.symm (Pi.single label left)
      let rightBlocks := coarseEquiv.symm (Pi.single label right)
      have hmaps : blockMap leftBlocks = blockMap rightBlocks := by
        apply fineEquiv.injective
        funext current
        rw [M.generatedBlockComparisonH1DirectSumMap_component,
          M.generatedBlockComparisonH1DirectSumMap_component]
        change
          M.generatedBlockComparisonH1Map laws hcoarse hfine current
              ((coarseEquiv leftBlocks) current) =
            M.generatedBlockComparisonH1Map laws hcoarse hfine current
              ((coarseEquiv rightBlocks) current)
        rw [coarseEquiv.apply_symm_apply, coarseEquiv.apply_symm_apply]
        by_cases hcurrent : current = label
        · subst current
          simpa only [Pi.single_eq_same] using hequal
        · rw [Pi.single_eq_of_ne hcurrent, Pi.single_eq_of_ne hcurrent,
            map_zero]
      have hblocks : leftBlocks = rightBlocks := hblockMap.1 hmaps
      have hcomponent :=
        congrArg (fun blocks => (coarseEquiv blocks) label) hblocks
      change
        (coarseEquiv (coarseEquiv.symm (Pi.single label left))) label =
          (coarseEquiv (coarseEquiv.symm (Pi.single label right))) label
        at hcomponent
      rw [coarseEquiv.apply_symm_apply, coarseEquiv.apply_symm_apply,
        Pi.single_eq_same, Pi.single_eq_same] at hcomponent
      exact hcomponent
    · intro target
      let targetBlocks := fineEquiv.symm (Pi.single label target)
      obtain ⟨sourceBlocks, hsource⟩ := hblockMap.2 targetBlocks
      refine ⟨(coarseEquiv sourceBlocks) label, ?_⟩
      have hcomponent :=
        congrArg (fun blocks => (fineEquiv blocks) label) hsource
      change
        (fineEquiv (blockMap sourceBlocks)) label =
          (fineEquiv (fineEquiv.symm (Pi.single label target))) label
        at hcomponent
      rw [M.generatedBlockComparisonH1DirectSumMap_component,
        fineEquiv.apply_symm_apply, Pi.single_eq_same] at hcomponent
      exact hcomponent
  · intro hcomponents
    constructor
    · intro left right hequal
      apply coarseEquiv.injective
      funext label
      apply (hcomponents label).1
      have hcomponent := congrArg (fun classes => fineEquiv classes label) hequal
      simpa only [M.generatedBlockComparisonH1DirectSumMap_component] using
        hcomponent
    · intro fineClasses
      let preimage :
          (label : LawValueLabel laws) →
            (coarse.lawValueBlockComplex laws hcoarse label).H1 :=
        fun label =>
          Classical.choose
            ((hcomponents label).2 (fineEquiv fineClasses label))
      have hpreimage (label : LawValueLabel laws) :
          M.generatedBlockComparisonH1Map laws hcoarse hfine label
              (preimage label) =
            fineEquiv fineClasses label :=
        Classical.choose_spec
          ((hcomponents label).2 (fineEquiv fineClasses label))
      refine ⟨coarseEquiv.symm preimage, ?_⟩
      apply fineEquiv.injective
      funext label
      rw [M.generatedBlockComparisonH1DirectSumMap_component]
      rw [coarseEquiv.apply_symm_apply]
      exact hpreimage label

/-- The actual global generated `H¹` comparison is bijective exactly when
every actual source-generated block `H¹` comparison is bijective. -/
theorem generatedComparisonH1Map_bijective_iff_blocks [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    Function.Bijective
        (M.generatedComparisonH1Map laws hcoarse hfine) ↔
      ∀ label : LawValueLabel laws,
        Function.Bijective
          (M.generatedBlockComparisonH1Map laws hcoarse hfine label) := by
  let coarseEquiv := coarse.lawGeneratedH1BlockEquiv laws hcoarse
  let fineEquiv := fine.lawGeneratedH1BlockEquiv laws hfine
  let globalMap := M.generatedComparisonH1Map laws hcoarse hfine
  let blockMap := M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine
  have hnatural
      (coarseClass : (coarse.lawGeneratedComplex laws hcoarse).H1) :
      fineEquiv (globalMap coarseClass) =
        blockMap (coarseEquiv coarseClass) := by
    have hpoint := LinearMap.congr_fun
      (M.generatedComparisonH1Map_block_naturality laws hcoarse hfine)
      coarseClass
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hpoint
  have hglobal_iff_directSum :
      Function.Bijective globalMap ↔ Function.Bijective blockMap := by
    constructor
    · intro hglobal
      have hleft :
          Function.Bijective (fun coarseClass =>
            fineEquiv (globalMap coarseClass)) :=
        fineEquiv.bijective.comp hglobal
      rw [show (fun coarseClass => fineEquiv (globalMap coarseClass)) =
          (fun coarseClass => blockMap (coarseEquiv coarseClass)) from
        funext hnatural] at hleft
      exact
        (Function.Bijective.of_comp_iff blockMap coarseEquiv.bijective).1
          (by simpa only [Function.comp_apply] using hleft)
    · intro hblock
      have hright :
          Function.Bijective (fun coarseClass =>
            blockMap (coarseEquiv coarseClass)) :=
        hblock.comp coarseEquiv.bijective
      rw [show (fun coarseClass => blockMap (coarseEquiv coarseClass)) =
          (fun coarseClass => fineEquiv (globalMap coarseClass)) from
        (funext hnatural).symm] at hright
      exact
        (Function.Bijective.of_comp_iff' fineEquiv.bijective globalMap).1
          (by simpa only [Function.comp_apply] using hright)
  exact hglobal_iff_directSum.trans
    (M.generatedBlockComparisonH1DirectSumMap_bijective_iff laws hcoarse hfine)

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
