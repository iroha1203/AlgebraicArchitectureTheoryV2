import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparison
import Formal.Util.AssertStandardAxioms

/-!
# Quotient-level naturality of the law-value block comparison

This module completes the block decomposition of the generated comparison map
required by `G-104-aat-resolution-invariance`.  The comparison on the finite
direct sum is built componentwise from the actual G-102 `h1Map` of each exact
source-generated law-value block.  It is not defined by conjugating the global
map with the block equivalences.

The degree-one component theorem from Cycle 12 gives the cycle-level bridge.
Together with the representative formula from Cycle 11 and the reviewed G-102
`h1Map_mk`, this proves the representative component formula and then the full
quotient-level naturality square.
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

/-!
The map below is generated from the per-label G-102 maps.  In particular, its
definition does not mention either global `lawGeneratedH1BlockEquiv`.
-/

/-- The finite direct sum of the generated comparison maps on exact blocks. -/
def generatedBlockComparisonH1DirectSumMap [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (⨁ label : LawValueLabel laws,
      (coarse.lawValueBlockComplex laws hcoarse label).H1) →ₗ[ℚ]
    (⨁ label : LawValueLabel laws,
      (fine.lawValueBlockComplex laws hfine label).H1) := by
  let productMap :
      ((label : LawValueLabel laws) →
        (coarse.lawValueBlockComplex laws hcoarse label).H1) →ₗ[ℚ]
      ((label : LawValueLabel laws) →
        (fine.lawValueBlockComplex laws hfine label).H1) :=
    { toFun := fun classes label =>
        M.generatedBlockComparisonH1Map laws hcoarse hfine label
          (classes label)
      map_add' := by
        intro left right
        funext label
        exact map_add (M.generatedBlockComparisonH1Map laws hcoarse hfine label)
          (left label) (right label)
      map_smul' := by
        intro scalar classes
        funext label
        exact map_smul
          (M.generatedBlockComparisonH1Map laws hcoarse hfine label)
          scalar (classes label) }
  exact
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label =>
        (fine.lawValueBlockComplex laws hfine label).H1)).symm.toLinearMap.comp
      (productMap.comp
        (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun label =>
            (coarse.lawValueBlockComplex laws hcoarse label).H1)).toLinearMap)

/-- Evaluation of the direct-sum map is the actual G-102 map on that label. -/
@[simp]
theorem generatedBlockComparisonH1DirectSumMap_component [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (classes : ⨁ label : LawValueLabel laws,
      (coarse.lawValueBlockComplex laws hcoarse label).H1)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current =>
        (fine.lawValueBlockComplex laws hfine current).H1)
      (M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine
        classes)) label =
      M.generatedBlockComparisonH1Map laws hcoarse hfine label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current =>
            (coarse.lawValueBlockComplex laws hcoarse current).H1)
          classes) label) := by
  unfold generatedBlockComparisonH1DirectSumMap
  dsimp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  exact congrFun
    ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current =>
        (fine.lawValueBlockComplex laws hfine current).H1)).apply_symm_apply _)
    label

/-- The global cycle map and the generated block cycle map agree at each label. -/
theorem generatedComparisonCyclesMap_block_component [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cycle : LinearMap.ker (coarse.lawGeneratedComplex laws hcoarse).d1)
    (label : LawValueLabel laws) :
    (fine.lawGeneratedBlockCyclesEquiv laws hfine
      ((M.generatedComparisonHom laws hcoarse hfine).cyclesMap cycle)) label =
      (M.generatedBlockComparisonHom laws hcoarse hfine label).cyclesMap
        ((coarse.lawGeneratedBlockCyclesEquiv laws hcoarse cycle) label) := by
  apply Subtype.ext
  change
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => fine.EdgeBlockCoordinate laws hfine current → ℚ)
      (fine.edgeCochainBlockEquiv laws hfine
        (M.generatedPullback1 laws hcoarse hfine cycle.1))) label =
      M.generatedBlockPullback1 laws hcoarse hfine label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => coarse.EdgeBlockCoordinate laws hcoarse current → ℚ)
          (coarse.edgeCochainBlockEquiv laws hcoarse cycle.1)) label)
  exact M.generatedPullback1_block_component laws hcoarse hfine cycle.1 label

/-- On a global quotient representative, the fine block component is obtained
by applying the actual block `h1Map` to the coarse block representative. -/
theorem generatedComparisonH1Map_mk_block_component [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cycle : LinearMap.ker (coarse.lawGeneratedComplex laws hcoarse).d1)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current =>
        (fine.lawValueBlockComplex laws hfine current).H1)
      (fine.lawGeneratedH1BlockEquiv laws hfine
        (M.generatedComparisonH1Map laws hcoarse hfine
          ((LinearMap.range
            (coarse.lawGeneratedComplex laws hcoarse).boundaryToCycles).mkQ
            cycle)))) label =
      M.generatedBlockComparisonH1Map laws hcoarse hfine label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current =>
            (coarse.lawValueBlockComplex laws hcoarse current).H1)
          (coarse.lawGeneratedH1BlockEquiv laws hcoarse
            ((LinearMap.range
              (coarse.lawGeneratedComplex laws hcoarse).boundaryToCycles).mkQ
              cycle))) label) := by
  change
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current =>
        (fine.lawValueBlockComplex laws hfine current).H1)
      (fine.lawGeneratedH1BlockEquiv laws hfine
        ((M.generatedComparisonHom laws hcoarse hfine).h1Map
          ((LinearMap.range
            (coarse.lawGeneratedComplex laws hcoarse).boundaryToCycles).mkQ
            cycle)))) label = _
  rw [ThreeCochainComplex.Hom.h1Map_mk,
    fine.lawGeneratedH1BlockEquiv_mk_component,
    coarse.lawGeneratedH1BlockEquiv_mk_component]
  change
    (LinearMap.range
      (fine.lawValueBlockComplex laws hfine label).boundaryToCycles).mkQ
      ((fine.lawGeneratedBlockCyclesEquiv laws hfine
        ((M.generatedComparisonHom laws hcoarse hfine).cyclesMap cycle)) label) =
    (M.generatedBlockComparisonHom laws hcoarse hfine label).h1Map
      ((LinearMap.range
        (coarse.lawValueBlockComplex laws hcoarse label).boundaryToCycles).mkQ
        ((coarse.lawGeneratedBlockCyclesEquiv laws hcoarse cycle) label))
  rw [ThreeCochainComplex.Hom.h1Map_mk,
    M.generatedComparisonCyclesMap_block_component]

/-- The global generated comparison map is the finite direct sum of the actual
block comparison maps under the canonical Cycle 11 `H^1` equivalences. -/
theorem generatedComparisonH1Map_block_naturality [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (fine.lawGeneratedH1BlockEquiv laws hfine).toLinearMap.comp
        (M.generatedComparisonH1Map laws hcoarse hfine) =
      (M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine).comp
        (coarse.lawGeneratedH1BlockEquiv laws hcoarse).toLinearMap := by
  ext cycle label
  change
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current =>
        (fine.lawValueBlockComplex laws hfine current).H1)
      (fine.lawGeneratedH1BlockEquiv laws hfine
        (M.generatedComparisonH1Map laws hcoarse hfine
          ((LinearMap.range
            (coarse.lawGeneratedComplex laws hcoarse).boundaryToCycles).mkQ
            cycle)))) label =
      (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current =>
          (fine.lawValueBlockComplex laws hfine current).H1)
        (M.generatedBlockComparisonH1DirectSumMap laws hcoarse hfine
          (coarse.lawGeneratedH1BlockEquiv laws hcoarse
            ((LinearMap.range
              (coarse.lawGeneratedComplex laws hcoarse).boundaryToCycles).mkQ
              cycle)))) label
  rw [M.generatedBlockComparisonH1DirectSumMap_component]
  exact M.generatedComparisonH1Map_mk_block_component laws hcoarse hfine
    cycle label

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
