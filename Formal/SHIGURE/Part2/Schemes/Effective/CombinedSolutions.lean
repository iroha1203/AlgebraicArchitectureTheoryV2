import Formal.SHIGURE.Part2.Schemes.Effective.LocalDatumActual
import Formal.SHIGURE.Part2.Schemes.Effective.CanonicalSolution

/-! # The family combining local solutions with the original cover -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v w

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X : Scheme.{u}} (E : FppfCover.{u,w} X) (C : FppfCover.{u,v} X)

/-- Disjoint union of two fppf covering families, retaining every original
component and structural map. -/
def combinedFppfCover : FppfCover.{u,max w v} X where
  toPreZeroHypercover := E.toPreZeroHypercover.sum C.toPreZeroHypercover
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, ?_⟩
    · obtain ⟨i, y, hy⟩ := E.exists_eq x
      exact ⟨Sum.inl i, y, hy⟩
    · intro j
      cases j with
      | inl i => exact E.map_prop i
      | inr i => exact C.map_prop i

variable (D : FppfModuleDescentData C)
  (L : ∀ i : E.I₀, EffectiveLocalSolution D (E.f i))

/-- The chosen local solutions and the datum's own component solutions,
indexed by the disjoint union of the two original families. -/
def combinedLocalSolutions :
    ∀ i : (combinedFppfCover E C).I₀,
      EffectiveLocalSolution D ((combinedFppfCover E C).f i)
  | .inl i => L i
  | .inr i => canonicalComponentSolution D i

/-- The combined solutions determine descent data, including all transitions
between a chosen local solution and an original component. -/
def combinedSolutionsDatum : Q.DescentData (combinedFppfCover E C).f :=
  localSolutionsActualDatum D (combinedFppfCover E C) (combinedLocalSolutions E C D L)

end

end SHIGURE.SchemeDescent
