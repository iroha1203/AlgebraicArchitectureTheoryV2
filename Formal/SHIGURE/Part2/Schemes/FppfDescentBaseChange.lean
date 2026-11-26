import Formal.SHIGURE.Part2.Schemes.FppfDescentData

/-! # Restricting fppf module descent data to a new base scheme -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u

variable {X Y : Scheme.{u}} (cover : FppfCover X) (g : Y ⟶ X)

/-- Change the base using the actual pullback schemes of the fppf charts. -/
def fppfDescentBaseChange : FppfModuleDescentData cover ⥤
    FppfModuleDescentData (cover.pullback₁ g) :=
  Pseudofunctor.DescentData.pullFunctor quasiCoherentModulesPseudofunctor
    (f := cover.f) (p := g) (f' := (cover.pullback₁ g).f)
    (α := id) (p' := fun i => cover.pullbackHom g i) (cover.pullbackHom_map g)

/-- A globally defined module restricts to the same descent datum by either
pulling back the global module or restricting its datum. -/
def fppfComparisonBaseChange :
    fppfModuleComparison cover ⋙ fppfDescentBaseChange cover g ≅
      (quasiCoherentModulesPseudofunctor.map g.op.toLoc).toFunctor ⋙
        fppfModuleComparison (cover.pullback₁ g) :=
  Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    quasiCoherentModulesPseudofunctor (cover.pullbackHom_map g)

end

end SHIGURE.SchemeDescent
