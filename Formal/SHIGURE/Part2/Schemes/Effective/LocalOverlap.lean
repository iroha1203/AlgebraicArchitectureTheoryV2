import Formal.SHIGURE.Part2.Schemes.Effective.DirectPull

/-! # Comparisons of local solutions on common test schemes -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X : Scheme.{u}} {cover : FppfCover.{u,v} X} {D : FppfModuleDescentData cover}

namespace EffectiveLocalSolution

variable {Y : Scheme.{u}} {g g' : Y ⟶ X}

/-- Changing a base arrow by equality transports the solution. -/
def rebase (L : EffectiveLocalSolution D g) (e : g = g') : EffectiveLocalSolution D g' :=
  e ▸ L

/-- Transporting the base arrow leaves the underlying module unchanged. -/
theorem rebase_module (L : EffectiveLocalSolution D g) (e : g = g') :
    (L.rebase e).module = L.module := by
  cases e
  rfl

set_option maxHeartbeats 750000 in
/-- Compare two solutions on any common test scheme over the base. -/
def transitionAt {Y' T : Scheme.{u}} {g' : Y' ⟶ X}
    (L : EffectiveLocalSolution D g) (K : EffectiveLocalSolution D g')
    (q : T ⟶ X) (s : T ⟶ Y) (t : T ⟶ Y')
    (es : s ≫ g = q) (et : t ≫ g' = q) :
    (Q.map s.op.toLoc).toFunctor.obj L.module ≅
      (Q.map t.op.toLoc).toFunctor.obj K.module := by
  let L' := (L.directPull s).rebase es
  let K' := (K.directPull t).rebase et
  exact (eqToIso ((L.directPull s).rebase_module es)).symm ≪≫ L'.transition K' ≪≫
    eqToIso ((K.directPull t).rebase_module et)

set_option maxHeartbeats 750000 in
/-- The comparisons of three solutions on the same test scheme compose. -/
theorem transitionAt_comp {Y' Y'' T : Scheme.{u}} {g' : Y' ⟶ X} {g'' : Y'' ⟶ X}
    (L : EffectiveLocalSolution D g) (K : EffectiveLocalSolution D g')
    (N : EffectiveLocalSolution D g'') (q : T ⟶ X) (s : T ⟶ Y)
    (t : T ⟶ Y') (r : T ⟶ Y'') (es : s ≫ g = q) (et : t ≫ g' = q)
    (er : r ≫ g'' = q) :
    (L.transitionAt K q s t es et).hom ≫ (K.transitionAt N q t r et er).hom =
      (L.transitionAt N q s r es er).hom := by
  simp only [transitionAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun f => (eqToIso ((L.directPull s).rebase_module es)).inv ≫ f ≫
      (eqToIso ((N.directPull r).rebase_module er)).hom)
    (transition_comp ((L.directPull s).rebase es) ((K.directPull t).rebase et) ((N.directPull r).rebase er))

/-- A solution compared to itself on the same test chart gives the identity. -/
theorem transitionAt_self {T : Scheme.{u}} (L : EffectiveLocalSolution D g)
    (q : T ⟶ X) (s : T ⟶ Y) (es : s ≫ g = q) :
    (L.transitionAt L q s s es es).hom = 𝟙 _ := by
  simp only [transitionAt, Iso.trans_hom, Iso.symm_hom, transition_self,
    Category.id_comp, Iso.inv_hom_id]

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
