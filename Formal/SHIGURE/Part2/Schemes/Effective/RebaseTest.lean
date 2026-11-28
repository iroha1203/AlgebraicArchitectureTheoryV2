import Formal.SHIGURE.Part2.Schemes.Effective.LocalOverlap
import Formal.SHIGURE.Part2.Schemes.Effective.TestComparison

/-! # Transporting local test comparisons along equality of base arrows -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y W : Scheme.{u}} {cover : FppfCover.{u,v} X}
  {D : FppfModuleDescentData cover} {g g' : Y ⟶ X}
  (L : EffectiveLocalSolution D g) (e : g = g') {i : cover.I₀}
  (a : W ⟶ Y) (b : W ⟶ cover.X i) (comm : a ≫ g = b ≫ cover.f i)

namespace EffectiveLocalSolution

/-- A change of the base-arrow proof preserves the local test comparison. -/
theorem rebase_testHom :
    (Q.map a.op.toLoc).toFunctor.map (eqToIso (L.rebase_module e)).inv ≫
      (L.rebase e).testHom a b (by rw [← e]; exact comm) = L.testHom a b comm := by
  cases e
  change (Q.map a.op.toLoc).toFunctor.map (𝟙 L.module) ≫ L.testHom a b comm = L.testHom a b comm
  rw [(Q.map a.op.toLoc).toFunctor.map_id]
  exact Category.id_comp _

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
