import Formal.SHIGURE.Part2.Schemes.Effective.LocalOverlap

/-! # Descent data from compatible local solutions -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v w

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X : Scheme.{u}} {cover : FppfCover.{u,v} X}
  (D : FppfModuleDescentData cover) (E : FppfCover.{u,w} X)
  (L : ∀ i : E.I₀, EffectiveLocalSolution D (E.f i))

/-- The specified local solutions give descent data when their comparisons
commute with pullback. The same-base comparisons already satisfy the identity
and triple-composition equations; pullback naturality is the remaining input. -/
def localSolutionsDatum
    (natural : ∀ {T T' : Scheme.{u}} (p : T' ⟶ T) (q : T ⟶ X) (q' : T' ⟶ X)
      (_hq : p ≫ q = q') (i j : E.I₀) (a : T ⟶ E.X i) (b : T ⟶ E.X j)
      (ha : a ≫ E.f i = q) (hb : b ≫ E.f j = q)
      (a' : T' ⟶ E.X i) (b' : T' ⟶ E.X j)
      (ha' : a' ≫ E.f i = q') (hb' : b' ≫ E.f j = q')
      (pa : p ≫ a = a') (pb : p ≫ b = b'),
      pullHom ((L i).transitionAt (L j) q a b ha hb).hom p a' b' pa pb =
        ((L i).transitionAt (L j) q' a' b' ha' hb').hom) :
    Q.DescentData E.f where
  obj i := (L i).module
  hom _ q i j a b ha hb := ((L i).transitionAt (L j) q a b ha hb).hom
  pullHom_hom _ _ p q q' hq i j a b ha hb a' b' pa pb :=
    natural p q q' hq i j a b ha hb a' b'
      (by rw [← pa, Category.assoc, ha, hq])
      (by rw [← pb, Category.assoc, hb, hq]) pa pb
  hom_self _ q i a ha := (L i).transitionAt_self q a ha
  hom_comp _ q i j k a b c ha hb hc :=
    (L i).transitionAt_comp (L j) (L k) q a b c ha hb hc

end

end SHIGURE.SchemeDescent
