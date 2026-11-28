import Formal.SHIGURE.Part2.Schemes.Effective.BaseChange
import Formal.SHIGURE.Part2.Schemes.FppfGlobalFromAffineSingleton

/-! # Restriction of local solutions of an fppf descent datum

A solution records its comparison to the restricted datum. Restricting it to
another base uses the actual iterated-pullback comparison. Two solutions on
one base have a unique comparison, because morphisms satisfy fppf descent.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y : Scheme.{u}} {cover : FppfCover.{u,v} X}
  (D : FppfModuleDescentData cover) (g : Y ⟶ X)

/-- A local module together with its comparison to the specified datum. -/
structure EffectiveLocalSolution where
  module : Q.obj (.mk (op Y))
  comparison : (fppfModuleComparison (cover.pullback₁ g)).obj module ≅
    (fppfDescentBaseChange cover g).obj D

namespace EffectiveLocalSolution

variable {D g}

private def preimagePair {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (d : B) (effective : F.IsEquivalence) : Σ m : A, F.obj m ≅ d := by
  letI : F.EssSurj := effective.essSurj
  exact ⟨F.objPreimage d, F.objObjPreimageIso d⟩

/-- Effective comparison on the pulled-back family constructs a local
solution, including its isomorphism with the given descent datum. -/
def ofEquivalence
    (effective : (fppfModuleComparison (cover.pullback₁ g)).IsEquivalence) :
    EffectiveLocalSolution D g := by
  let F := fppfModuleComparison (cover.pullback₁ g)
  let d := (fppfDescentBaseChange cover g).obj D
  let witness := preimagePair F d effective
  exact ⟨witness.1, witness.2⟩

set_option maxHeartbeats 750000 in
/-- A solution restricts along any further base change. -/
def pull (L : EffectiveLocalSolution D g) {Z : Scheme.{u}} (h : Z ⟶ Y) :
    EffectiveLocalSolution D (h ≫ g) := by
  let E := compositeBaseChangeCharts cover g h
  letI : E.IsEquivalence := compositeBaseChangeCharts_isEquivalence cover g h
  let ff := Functor.FullyFaithful.ofFullyFaithful E
  let N := (Q.map h.op.toLoc).toFunctor.obj L.module
  refine ⟨N, ff.preimageIso ?_⟩
  exact (compositeBaseChangeCharts_comparison cover g h).app N ≪≫
    (fppfComparisonBaseChange (cover.pullback₁ g) h).symm.app L.module ≪≫
    (fppfDescentBaseChange (cover.pullback₁ g) h).mapIso L.comparison ≪≫
    (fppfDescentBaseChange_composite cover g h).app D

set_option maxHeartbeats 750000 in
/-- Two solutions of the same datum over the same base are canonically
isomorphic, using full faithfulness on the actual pulled-back fppf family. -/
def transition (L K : EffectiveLocalSolution D g) : L.module ≅ K.module :=
  (fppfModuleComparison_fullyFaithful (cover.pullback₁ g)).preimageIso
    (L.comparison ≪≫ K.comparison.symm)

set_option maxHeartbeats 500000 in
/-- On each pulled-back component the transition identifies the two
comparisons with the original datum. -/
theorem transition_component (L K : EffectiveLocalSolution D g) (i : cover.I₀) :
    (Q.map ((cover.pullback₁ g).f i).op.toLoc).toFunctor.map (L.transition K).hom ≫
      K.comparison.hom.hom i = L.comparison.hom.hom i := by
  have image : (fppfModuleComparison (cover.pullback₁ g)).map (L.transition K).hom =
      (L.comparison ≪≫ K.comparison.symm).hom := by
    simp only [transition, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage]
  have component := congrArg (fun f => f.hom i) image
  have inverse : K.comparison.inv.hom i ≫ K.comparison.hom.hom i = 𝟙 _ := by
    change (K.comparison.inv ≫ K.comparison.hom).hom i = _
    rw [Iso.inv_hom_id]
    rfl
  change (Q.map ((cover.pullback₁ g).f i).op.toLoc).toFunctor.map (L.transition K).hom =
    L.comparison.hom.hom i ≫ K.comparison.inv.hom i at component
  rw [component, Category.assoc, inverse, Category.comp_id]

set_option maxHeartbeats 500000 in
/-- The canonical comparisons satisfy the triple-overlap composition law. -/
theorem transition_comp (L K N : EffectiveLocalSolution D g) :
    (L.transition K).hom ≫ (K.transition N).hom = (L.transition N).hom := by
  let ff := fppfModuleComparison_fullyFaithful (cover.pullback₁ g)
  apply ff.map_injective
  simp only [transition, Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 500000 in
/-- A solution compares to itself by the identity. -/
theorem transition_self (L : EffectiveLocalSolution D g) :
    (L.transition L).hom = 𝟙 _ := by
  let ff := fppfModuleComparison_fullyFaithful (cover.pullback₁ g)
  apply ff.map_injective
  simp only [transition, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id]
  exact ((fppfModuleComparison (cover.pullback₁ g)).map_id _).symm

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
