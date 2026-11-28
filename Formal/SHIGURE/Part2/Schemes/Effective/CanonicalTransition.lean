import Formal.SHIGURE.Part2.Schemes.Effective.CanonicalSolution
import Formal.SHIGURE.Part2.Schemes.Effective.OverlapPull
import Formal.SHIGURE.Part2.Schemes.Effective.DescentChartCompatibility

/-! # The canonical local solutions recover the original transitions -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v

private theorem identityTriangle {C : Type*} [Category C] {A B : C}
    (u m z d : A ⟶ B) (r : B ⟶ B)
    (hu : u = m) (hr : r = 𝟙 B) (hz : z = d) (triangle : u ≫ r = z) : m = d := by
  simpa only [hu, hr, hz, Category.comp_id] using triangle

variable {X T : Scheme.{u}} {cover : FppfCover.{u,v} X}
  (D : FppfModuleDescentData cover) {i j : cover.I₀}
  (q : T ⟶ X) (a : T ⟶ cover.X i) (b : T ⟶ cover.X j)
  (ha : a ≫ cover.f i = q) (hb : b ≫ cover.f j = q)

/-- The transition constructed from the canonical solutions is the original
transition, on every test scheme and for every pair of components. -/
theorem canonicalComponent_transitionAt :
    ((canonicalComponentSolution D i).transitionAt (canonicalComponentSolution D j)
      q a b ha hb).hom = D.hom q a b ha hb := by
  let L := canonicalComponentSolution D i
  let K := canonicalComponentSolution D j
  have base : 𝟙 T ≫ q = b ≫ cover.f j := (Category.id_comp q).trans hb.symm
  let m := (L.transitionAt K q a b ha hb).hom
  let u := pullHom (F := quasiCoherentModulesPseudofunctor) (M₁ := D.obj i) (M₂ := D.obj j)
    (f₁ := a) (f₂ := b) m (𝟙 T) a b (Category.id_comp a) (Category.id_comp b)
  let r := K.testHom b b rfl
  let z := L.testHom a b (ha.trans hb.symm)
  have hu : u = m := pullHom_id (F := quasiCoherentModulesPseudofunctor)
    (M₁ := D.obj i) (M₂ := D.obj j) (f₁ := a) (f₂ := b) m
  have hr : r = 𝟙 _ := (canonicalComponent_testHom D j b b rfl).trans
    (D.hom_self (b ≫ cover.f j) b rfl)
  have hz : z = D.hom q a b ha hb :=
    (canonicalComponent_testHom D i a b (ha.trans hb.symm)).trans
      (descentHom_reindex D ha a b rfl (hb.trans ha.symm))
  have triangle := L.transitionAt_testHom_along K q a b ha hb (𝟙 T) b base a b
    (Category.id_comp a) (Category.id_comp b)
  exact identityTriangle u m z _ r hu hr hz triangle

end

end SHIGURE.SchemeDescent
