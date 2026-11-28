import Formal.SHIGURE.Part2.Schemes.Effective.CombinedGluing
import Formal.SHIGURE.Part2.Schemes.Effective.CanonicalTransition

/-! # Recovering the original datum from the combined family -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v w

private def restrictIdx {K : Type*} [Category K]
    (F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{u,u+1})
    {ι : Type v} {κ : Type w} {S : K} {U : ι → K}
    (f : ∀ i, U i ⟶ S) (α : κ → ι) (A : F.DescentData f) :
    F.DescentData (fun j => f (α j)) where
  obj j := A.obj (α j)
  hom _ q i j a b ha hb := A.hom (i₁ := α i) (i₂ := α j) q a b ha hb
  pullHom_hom _ _ r q q' hq i j a b ha hb a' b' ea eb :=
    A.pullHom_hom r q q' hq (i₁ := α i) (i₂ := α j) a b ha hb a' b' ea eb
  hom_self _ q i a h := A.hom_self q (i := α i) a h
  hom_comp _ q i j k a b c ha hb hc := A.hom_comp q (i₁ := α i) (i₂ := α j) (i₃ := α k) a b c ha hb hc

private def restrictIdxFunctor {K : Type*} [Category K]
    (F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{u,u+1})
    {ι : Type v} {κ : Type w} {S : K} {U : ι → K}
    (f : ∀ i, U i ⟶ S) (α : κ → ι) :
    F.DescentData f ⥤ F.DescentData (fun j => f (α j)) where
  obj := restrictIdx F f α
  map φ := by
    refine { hom := fun i => φ.hom (α i), comm := ?_ }
    intro T q i j a b ha hb
    exact φ.comm (i₁ := α i) (i₂ := α j) q a b ha hb
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem restrictIdx_compare {K : Type*} [Category K]
    (F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{u,u+1})
    {ι : Type v} {κ : Type w} {S : K} {U : ι → K}
    (f : ∀ i, U i ⟶ S) (α : κ → ι) (M : F.obj (.mk (op S))) :
    restrictIdx F f α ((F.toDescentData f).obj M) =
      (F.toDescentData (fun j => f (α j))).obj M := rfl

private def globalOnIdx {K : Type*} [Category K]
    (F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{u,u+1})
    {ι : Type v} {κ : Type w} {S : K} {U : ι → K}
    (f : ∀ i, U i ⟶ S) (α : κ → ι) (M : F.obj (.mk (op S)))
    (A : F.DescentData f) (e : (F.toDescentData f).obj M ≅ A) :
    (F.toDescentData (fun j => f (α j))).obj M ≅ restrictIdx F f α A :=
  (eqToIso (restrictIdx_compare F f α M)).symm ≪≫ (restrictIdxFunctor F f α).mapIso e

private theorem datum_ext_fields {K : Type*} [Category K]
    {F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{u,u+1}}
    {ι : Type v} {S : K} {U : ι → K} {f : ∀ i, U i ⟶ S}
    (A B : F.DescentData f) (ho : A.obj = B.obj) (ht : HEq (@A.hom) (@B.hom)) : A = B := by
  cases A with
  | mk ao ah ap ai ac =>
    cases B with
    | mk bo bh bp bi bc =>
      change ao = bo at ho
      cases ho
      change HEq ah bh at ht
      have h : ah = bh := eq_of_heq ht
      cases h
      rfl

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X : Scheme.{u}} (E : FppfCover.{u,w} X) (C : FppfCover.{u,v} X)
  (D : FppfModuleDescentData C)
  (L : ∀ i : E.I₀, EffectiveLocalSolution D (E.f i))

private theorem combinedInrHomFormula {T : Scheme.{u}} {i j : C.I₀}
    (q : T ⟶ X) (a : T ⟶ C.X i) (b : T ⟶ C.X j)
    (ha : a ≫ C.f i = q) (hb : b ≫ C.f j = q) :
    (combinedSolutionsDatum E C D L).hom (i₁ := Sum.inr i) (i₂ := Sum.inr j) q a b ha hb =
      ((canonicalComponentSolution D i).transitionAt (canonicalComponentSolution D j) q a b ha hb).hom := rfl

private theorem combinedInrHom {T : Scheme.{u}} {i j : C.I₀}
    (q : T ⟶ X) (a : T ⟶ C.X i) (b : T ⟶ C.X j)
    (ha : a ≫ C.f i = q) (hb : b ≫ C.f j = q) :
    (combinedSolutionsDatum E C D L).hom (i₁ := Sum.inr i) (i₂ := Sum.inr j) q a b ha hb =
      D.hom q a b ha hb :=
  (combinedInrHomFormula E C D L q a b ha hb).trans (canonicalComponent_transitionAt D q a b ha hb)

set_option maxHeartbeats 750000 in
/-- A global module realizing the combined datum realizes the original datum
on every original component and every test overlap. -/
def originalDatumFromCombined
    (M : Q.obj (.mk (op X)))
    (e : (Q.toDescentData (combinedFppfCover E C).f).obj M ≅ combinedSolutionsDatum E C D L) :
    (fppfModuleComparison C).obj M ≅ D := by
  let U := combinedFppfCover E C
  let α : C.I₀ → U.I₀ := fun i => Sum.inr i
  let A := restrictIdx Q U.f α (combinedSolutionsDatum E C D L)
  have ho : A.obj = D.obj := rfl
  have ht : HEq (@A.hom) (@D.hom) := by
    apply heq_of_eq
    funext T q i j a b ha hb
    exact combinedInrHom E C D L q a b ha hb
  have same : A = D := datum_ext_fields A D ho ht
  exact globalOnIdx Q U.f α M (combinedSolutionsDatum E C D L) e ≪≫ eqToIso same

set_option maxHeartbeats 750000 in
/-- Effective descent for the original family is local on the base for an
already effective fppf family. -/
theorem fppfComparison_isEquivalence_of_local
    (effective : (fppfModuleComparison E).IsEquivalence)
    (localEffective : ∀ i, (fppfModuleComparison (C.pullback₁ (E.f i))).IsEquivalence) :
    (fppfModuleComparison C).IsEquivalence := by
  let F := fppfModuleComparison C
  let ff := fppfModuleComparison_fullyFaithful C
  letI : F.Faithful := ff.faithful
  letI : F.Full := ff.full
  letI : F.EssSurj := ⟨fun D => by
    let L (i : E.I₀) : EffectiveLocalSolution D (E.f i) :=
      EffectiveLocalSolution.ofEquivalence (localEffective i)
    let witness := combinedSolutionsGlobal E C D L effective
    exact ⟨witness.1, ⟨originalDatumFromCombined E C D L witness.1 witness.2⟩⟩⟩
  exact { }

end

end SHIGURE.SchemeDescent
