import Formal.SHIGURE.Part2.Schemes.Effective.CombinedSolutions
import Formal.SHIGURE.Part2.Schemes.FppfGlobalFromAffineSingleton

/-! # Gluing the combined family using an effective localizing cover -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v w

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

private def choosePreimage {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (effective : F.IsEquivalence) (d : B) : Σ m : A, F.obj m ≅ d := by
  letI : F.EssSurj := effective.essSurj
  exact ⟨F.objPreimage d, F.objObjPreimageIso d⟩

variable {X : Scheme.{u}} (E : FppfCover.{u,w} X) (C : FppfCover.{u,v} X)
  (D : FppfModuleDescentData C)
  (L : ∀ i : E.I₀, EffectiveLocalSolution D (E.f i))

set_option maxHeartbeats 750000 in
/-- If the second family has effective descent, the combined local-solution
datum comes from a global module. The second family is a covering refinement
of the combined family. -/
def combinedSolutionsGlobal
    (effective : (fppfModuleComparison E).IsEquivalence) :
    Σ M : Q.obj (.mk (op X)),
      (Q.toDescentData (combinedFppfCover E C).f).obj M ≅ combinedSolutionsDatum E C D L := by
  let U := combinedFppfCover E C
  letI : Q.IsPrestack fppfTopology := quasiCoherentModules_isFppfPrestack
  have smaller : E.presieve₀ ≤ U.presieve₀ := by
    change _ ≤ (E.toPreZeroHypercover.sum C.toPreZeroHypercover).presieve₀
    rw [PreZeroHypercover.presieve₀_sum]
    exact le_sup_left
  have stackE : Q.IsStackFor E.presieve₀ := (Q.isStackFor_ofArrows_iff E.f).2 effective
  have stackU : Q.IsStackFor U.presieve₀ :=
    IsStackFor.of_le Q stackE (fppfCover_sieve_mem E) smaller
  have effectiveU : (Q.toDescentData U.f).IsEquivalence :=
    (Q.isStackFor_ofArrows_iff U.f).1 stackU
  exact choosePreimage (Q.toDescentData U.f) effectiveU (combinedSolutionsDatum E C D L)

end

end SHIGURE.SchemeDescent
