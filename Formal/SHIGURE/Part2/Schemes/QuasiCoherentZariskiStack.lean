import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Formal.SHIGURE.Part2.Schemes.OpenCoverDescentEquivalence

/-! # The Zariski stack of quasi-coherent modules -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor

noncomputable section

universe t u

variable {X : Scheme.{u}} (cover : Scheme.OpenCover.{t} X)

private abbrev OpenIndices := Set.range (fun i : cover.I₀ => (cover.f i).opensRange)

private def representative (U : OpenIndices cover) : cover.I₀ := U.property.choose

private theorem representative_range (U : OpenIndices cover) :
    (cover.f (representative cover U)).opensRange = U.val := U.property.choose_spec

private def smallOpenCover : Scheme.OpenCover.{u} X where
  toPreZeroHypercover := cover.toPreZeroHypercover.restrictIndex (representative cover)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun U => cover.map_prop (representative cover U)⟩
    obtain ⟨i, y, hy⟩ := cover.exists_eq x
    let U : OpenIndices cover := ⟨(cover.f i).opensRange, ⟨i, rfl⟩⟩
    have hx : x ∈ (cover.f (representative cover U)).opensRange := by
      rw [representative_range]
      exact ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hx
    exact ⟨U, z, hz⟩

private theorem smallOpenCover_sieve :
    Sieve.generate (smallOpenCover cover).presieve₀ = Sieve.generate cover.presieve₀ := by
  apply le_antisymm
  · exact Sieve.generate_mono (cover.toPreZeroHypercover.presieve₀_restrictIndex_le (representative cover))
  · rw [Sieve.generate_le_iff]
    intro W g hg
    obtain ⟨i⟩ := hg
    let U : OpenIndices cover := ⟨(cover.f i).opensRange, ⟨i, rfl⟩⟩
    have same : Set.range (cover.f i) = Set.range (cover.f (representative cover U)) :=
      congrArg (fun V : X.Opens => (V : Set X)) (representative_range cover U).symm
    let a := IsOpenImmersion.isoOfRangeEq (cover.f i) (cover.f (representative cover U)) same
    exact ⟨_, a.hom, (smallOpenCover cover).f U, ⟨U⟩, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

/-- The same equivalence holds for an original open covering family of any
index universe. Using one chart for each image open preserves its sieve. -/
theorem openCoverComparison_isEquivalence_anySize :
    (quasiCoherentModulesPseudofunctor.toDescentData cover.f).IsEquivalence := by
  let small := smallOpenCover cover
  apply (isStackFor_ofArrows_iff quasiCoherentModulesPseudofunctor cover.f).1
  apply (quasiCoherentModulesPseudofunctor.isStackFor_iff_of_sieve_eq (smallOpenCover_sieve cover)).1
  exact (isStackFor_ofArrows_iff quasiCoherentModulesPseudofunctor small.f).2
    (openCoverComparisonEquivalence small).isEquivalence_functor

/-- Geometric quasi-coherent modules with all module maps form a stack for
Zariski covers, by their compatible sections and local module maps. -/
theorem quasiCoherentModules_isZariskiStack :
    quasiCoherentModulesPseudofunctor.{u}.IsStack Scheme.zariskiTopology := by
  apply IsStack.of_precoverage (J := Scheme.zariskiPrecoverage)
  intro X R hR
  let cover : Scheme.OpenCover.{u + 1} X :=
    ⟨R.preZeroHypercover, R.presieve₀_preZeroHypercover.symm ▸ hR⟩
  have eq : cover.presieve₀ = R := R.presieve₀_preZeroHypercover
  rw [← eq]
  exact (isStackFor_ofArrows_iff quasiCoherentModulesPseudofunctor cover.f).2
    (openCoverComparison_isEquivalence_anySize cover)

end

end SHIGURE.SchemeDescent
