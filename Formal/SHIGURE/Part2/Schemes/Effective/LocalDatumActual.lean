import Formal.SHIGURE.Part2.Schemes.Effective.LocalDatum
import Formal.SHIGURE.Part2.Schemes.Effective.OverlapPull

/-! # Actual descent data formed by local solutions -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v w

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X : Scheme.{u}} {cover : FppfCover.{u,v} X}
  (D : FppfModuleDescentData cover) (E : FppfCover.{u,w} X)
  (L : ∀ i : E.I₀, EffectiveLocalSolution D (E.f i))

/-- Local solutions form an actual descent datum on the second fppf family;
pullback naturality is proved using the original family's full faithfulness. -/
def localSolutionsActualDatum : Q.DescentData E.f :=
  localSolutionsDatum D E L (fun {_T _T'} p q q' _hq i j a b ha hb a' b' ha' hb' pa pb =>
    (L i).transitionAt_pull (L j) q a b ha hb p q' a' b' pa pb ha' hb')

end

end SHIGURE.SchemeDescent
