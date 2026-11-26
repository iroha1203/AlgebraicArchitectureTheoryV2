import Formal.SHIGURE.Part2.Schemes.AffineDescentCoefficientMaps
import Formal.SHIGURE.Part2.Schemes.DescentComparisons

/-! # Recovering geometric maps from compatible coefficient maps -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite TensorProduct

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "B₂" => B ⊗[A] B

private abbrev bund (i : Fin 2) : CommRingCat.of B ⟶ CommRingCat.of B₂ :=
  CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom

private theorem reflect_transported_square {C : Type*} [Category C]
    {X Y U V X' Y' U' V' : C} (a : X ≅ X') (b : Y ≅ Y') (c : U ≅ U') (d : V ≅ V')
    (x : X ⟶ U) (y : Y ⟶ V) (x' : X' ⟶ U') (y' : Y' ⟶ V')
    (s : X' ⟶ Y') (t : U' ⟶ V')
    (left : x ≫ c.hom = a.hom ≫ x') (right : y ≫ d.hom = b.hom ≫ y')
    (comm : x' ≫ t = s ≫ y') :
    x ≫ (c.hom ≫ t ≫ d.inv) = (a.hom ≫ s ≫ b.inv) ≫ y := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, d.inv_hom_id, Category.comp_id]
  have r : b.inv ≫ y ≫ d.hom = y' := by rw [right, b.inv_hom_id_assoc]
  rw [r, ← Category.assoc x c.hom, left, Category.assoc, comm]


private theorem descentHom_reindexBase {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {X T : C} {I : Type*} {U : I → C}
    {covers : ∀ i, U i ⟶ X} (D : F.DescentData covers)
    {i j : I} (a : T ⟶ U i) (b : T ⟶ U j)
    {q q' : T ⟶ X} (same : q = q') (e₀ : a ≫ covers i = q) (e₁ : b ≫ covers j = q) :
    D.hom q a b e₀ e₁ = D.hom q' a b (e₀.trans same) (e₁.trans same) := by
  subst q'
  rfl

set_option maxHeartbeats 675000 in
private theorem affineDoubleTransition_hom_compBase (D : AffineSingletonDescentData A B) :
    D.hom (affineDoubleProjection A B 0 ≫ affineScalarMap A B) (i₁ := ()) (i₂ := ())
      (affineDoubleProjection A B 0) (affineDoubleProjection A B 1)
      rfl (affineDouble_isPullback A B).w.symm = (affineDoubleTransition A B D).hom :=
  descentHom_reindexBase D (affineDoubleProjection A B 0) (affineDoubleProjection A B 1)
    (affineDoubleProjection_base A B 0) rfl (affineDouble_isPullback A B).w.symm

variable {D E : AffineSingletonDescentData A B}

set_option maxHeartbeats 850000 in
/-- A coefficient map commuting with the two scalar pullbacks gives a
geometric map between the associated module charts on the entire datum. -/
def affineTildeDescentMapOfScalar
    (h : affineDescentCoefficientModule D ⟶ affineDescentCoefficientModule E)
    (comm : (ModuleCat.extendScalars (bund (A := A) (B := B) 0).hom).map h ≫
      (affineDescentScalarExtensionIso E).hom =
      (affineDescentScalarExtensionIso D).hom ≫
      (ModuleCat.extendScalars (bund (A := A) (B := B) 1).hom).map h) :
    affineTildeDescentData D ⟶ affineTildeDescentData E where
  hom := fun _ => (affineTildeFunctor (CommRingCat.of B)).map h
  comm := by
    let P := affinePullbackFunctor (bund (A := A) (B := B) 0)
    let Q := affinePullbackFunctor (bund (A := A) (B := B) 1)
    let L := affineTildePullbackIso (bund (A := A) (B := B) 0)
    let R := affineTildePullbackIso (bund (A := A) (B := B) 1)
    let T := affineTildeFunctor (CommRingCat.of B₂)
    let M := affineDescentCoefficientModule D
    let N := affineDescentCoefficientModule E
    let H := (affineTildeFunctor (CommRingCat.of B)).map h
    let H₀ := (ModuleCat.extendScalars (bund (A := A) (B := B) 0).hom).map h
    let H₁ := (ModuleCat.extendScalars (bund (A := A) (B := B) 1).hom).map h
    let d := (affineDescentScalarExtensionIso D).hom
    let e := (affineDescentScalarExtensionIso E).hom
    have sq : P.map H ≫ (affineDoubleTransition A B (affineTildeDescentData E)).hom =
        (affineDoubleTransition A B (affineTildeDescentData D)).hom ≫ Q.map H := by
      rw [affineTildeDescentData_double E, affineTildeDescentData_double D]
      have left : P.map H ≫ (L.app N).hom = (L.app M).hom ≫ T.map H₀ := L.hom.naturality h
      have right : Q.map H ≫ (R.app N).hom = (R.app M).hom ≫ T.map H₁ := R.hom.naturality h
      have overlap : T.map H₀ ≫ T.map e = T.map d ≫ T.map H₁ := by
        rw [← T.map_comp, ← T.map_comp]
        exact congrArg T.map comm
      exact reflect_transported_square (L.app M) (R.app M) (L.app N) (R.app N)
        (P.map H) (Q.map H) (T.map H₀) (T.map H₁) (T.map d) (T.map e) left right overlap
    intro U q i j a b eq₀ eq₁
    exact descentHom_comm_of_pullbacks
      (D₁ := affineTildeDescentData D) (D₂ := affineTildeDescentData E)
      (V := fun _ _ => Spec (CommRingCat.of B₂))
      (p₁ := fun _ _ => affineDoubleProjection A B 0)
      (p₂ := fun _ _ => affineDoubleProjection A B 1)
      (fun _ _ => affineDouble_isPullback A B) (fun _ => H)
      (fun () () => by
        rw [affineDoubleTransition_hom_compBase (affineTildeDescentData E),
          affineDoubleTransition_hom_compBase (affineTildeDescentData D)]
        exact sq) q a b eq₀ eq₁

/-- Undo the associated-module presentations on the source and target charts. -/
def affineDescentMapOfScalar
    (h : affineDescentCoefficientModule D ⟶ affineDescentCoefficientModule E)
    (comm : (ModuleCat.extendScalars (bund (A := A) (B := B) 0).hom).map h ≫
      (affineDescentScalarExtensionIso E).hom =
      (affineDescentScalarExtensionIso D).hom ≫
      (ModuleCat.extendScalars (bund (A := A) (B := B) 1).hom).map h) : D ⟶ E :=
  (affineTildeDescentDataIso D).inv ≫ affineTildeDescentMapOfScalar h comm ≫ (affineTildeDescentDataIso E).hom

set_option maxHeartbeats 575000 in
/-- The recovered geometric map has the original coefficient map. -/
theorem affineDescentCoefficientMap_ofScalar
    (h : affineDescentCoefficientModule D ⟶ affineDescentCoefficientModule E)
    (comm : (ModuleCat.extendScalars (bund (A := A) (B := B) 0).hom).map h ≫
      (affineDescentScalarExtensionIso E).hom =
      (affineDescentScalarExtensionIso D).hom ≫
      (ModuleCat.extendScalars (bund (A := A) (B := B) 1).hom).map h) :
    affineDescentCoefficientMap (affineDescentMapOfScalar h comm) = h := by
  let T := affineTildeEquivalence (CommRingCat.of B)
  let d := affineDescentCoefficientChart D
  let e := affineDescentCoefficientChart E
  let k := affineDescentMapOfScalar h comm
  apply T.fullyFaithfulFunctor.map_injective
  apply (cancel_mono e.hom).1
  change T.functor.map (T.inverse.map (k.hom ())) ≫ e.hom = T.functor.map h ≫ e.hom
  rw [show T.functor.map (T.inverse.map (k.hom ())) ≫ e.hom = d.hom ≫ k.hom () from
    T.counitIso.hom.naturality (k.hom ())]
  change d.hom ≫ (d.inv ≫ T.functor.map h ≫ e.hom) = T.functor.map h ≫ e.hom
  exact d.hom_inv_id_assoc _

/-- A geometric singleton descent morphism is determined by its coefficient map. -/
theorem affineDescentCoefficientMap_injective :
    Function.Injective (affineDescentCoefficientMap (D := D) (E := E)) := by
  intro f g equal
  let T := affineTildeEquivalence (CommRingCat.of B)
  have chart : f.hom () = g.hom () := T.fullyFaithfulInverse.map_injective equal
  apply Pseudofunctor.DescentData.Hom.ext
  funext i
  cases i
  exact chart

end

end SHIGURE.SchemeDescent
