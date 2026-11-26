import Formal.SHIGURE.Part2.Schemes.AffineDescentAssociated

/-! # Coefficient maps of geometric affine descent data -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules TensorProduct SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "B₂" => B ⊗[A] B

/-- The bundled ring homomorphism for the indexed affine overlap projection of Appendix B.3. -/
private abbrev bund (i : Fin 2) : CommRingCat.of B ⟶ CommRingCat.of B₂ :=
  CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom

variable {D E : AffineSingletonDescentData A B}

/-- The coefficient module map induced by a geometric descent morphism. -/
def affineDescentCoefficientMap (m : D ⟶ E) :
    affineDescentCoefficientModule D ⟶ affineDescentCoefficientModule E :=
  (affineTildeEquivalence (CommRingCat.of B)).inverse.map (m.hom ())

/-- Transport the B.3 square to the coefficient chart through its tilde comparisons. -/
private theorem transport_square {C : Type*} [Category C]
    {X Y U V X' Y' U' V' : C} (a : X ≅ X') (b : Y ≅ Y') (c : U ≅ U') (d : V ≅ V')
    (x : X ⟶ U) (y : Y ⟶ V) (x' : X' ⟶ U') (y' : Y' ⟶ V')
    (s : X' ⟶ Y') (t : U' ⟶ V')
    (left : x ≫ c.hom = a.hom ≫ x') (right : y ≫ d.hom = b.hom ≫ y')
    (comm : x ≫ (c.hom ≫ t ≫ d.inv) = (a.hom ≫ s ≫ b.inv) ≫ y) : x' ≫ t = s ≫ y' := by
  have cancel : b.inv ≫ y ≫ d.hom = y' := by rw [right, b.inv_hom_id_assoc]
  apply (cancel_epi a.hom).1
  have h := congrArg (· ≫ d.hom) comm
  simp only [Category.assoc, d.inv_hom_id, Category.comp_id, cancel] at h
  rw [← Category.assoc x c.hom, left, Category.assoc] at h
  exact h

set_option maxHeartbeats 850000 in
/-- A geometric map preserves the scalar comparison on the double tensor algebra. -/
theorem affineDescentCoefficientMap_comm (m : D ⟶ E) :
    (ModuleCat.extendScalars (bund (A := A) (B := B) 0).hom).map (affineDescentCoefficientMap m) ≫
      (affineDescentScalarExtensionIso E).hom =
    (affineDescentScalarExtensionIso D).hom ≫
      (ModuleCat.extendScalars (bund (A := A) (B := B) 1).hom).map (affineDescentCoefficientMap m) := by
  let F := affineTildeEquivalence (CommRingCat.of B)
  let J := affineTildeEquivalence (CommRingCat.of B₂)
  let T := affineTildeFunctor (CommRingCat.of B₂)
  let M := affineDescentCoefficientModule D
  let N := affineDescentCoefficientModule E
  let g := m.hom ()
  let h := affineDescentCoefficientMap m
  let d := affineTildeDescentDataIso D
  let e := affineTildeDescentDataIso E
  let lifted := d.hom ≫ m ≫ e.inv
  let p := affinePullbackFunctor (bund (A := A) (B := B) 0)
  let q := affinePullbackFunctor (bund (A := A) (B := B) 1)
  let l := affineTildePullbackIso (bund (A := A) (B := B) 0)
  let r := affineTildePullbackIso (bund (A := A) (B := B) 1)
  let b := Spec.map (CommRingCat.ofHom (algebraMap A B₂))
  let δ := (affineDescentScalarExtensionIso D).hom
  let ε := (affineDescentScalarExtensionIso E).hom
  let H := F.functor.map h
  let H₀ := (ModuleCat.extendScalars (bund (A := A) (B := B) 0).hom).map h
  let H₁ := (ModuleCat.extendScalars (bund (A := A) (B := B) 1).hom).map h
  have chart : lifted.hom () = H := by
    change (F.counitIso.app (D.obj ())).hom ≫ g ≫ (F.counitIso.app (E.obj ())).inv = H
    have natural : H ≫ (F.counitIso.app (E.obj ())).hom = (F.counitIso.app (D.obj ())).hom ≫ g :=
      F.counitIso.hom.naturality g
    apply (cancel_mono (F.counitIso.app (E.obj ())).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact natural.symm
  have comm : p.map H ≫ (affineDoubleTransition A B (affineTildeDescentData E)).hom =
      (affineDoubleTransition A B (affineTildeDescentData D)).hom ≫ q.map H := by
    change p.map H ≫ _ = _ ≫ q.map H
    rw [← chart]
    exact lifted.comm b (i₁ := ()) (i₂ := ()) (affineDoubleProjection A B 0)
      (affineDoubleProjection A B 1) (affineDoubleProjection_base A B 0) (affineDoubleProjection_base A B 1)
  rw [affineTildeDescentData_double E, affineTildeDescentData_double D] at comm
  have left : p.map H ≫ (l.app N).hom = (l.app M).hom ≫ T.map H₀ := l.hom.naturality h
  have right : q.map H ≫ (r.app N).hom = (r.app M).hom ≫ T.map H₁ := r.hom.naturality h
  have step : T.map H₀ ≫ T.map ε = T.map δ ≫ T.map H₁ :=
    transport_square (l.app M) (r.app M) (l.app N) (r.app N)
      (p.map H) (q.map H) (T.map H₀) (T.map H₁) (T.map δ) (T.map ε) left right comm
  apply J.fullyFaithfulFunctor.map_injective
  change T.map (H₀ ≫ ε) = T.map (δ ≫ H₁)
  rw [T.map_comp, T.map_comp]
  exact step

set_option maxHeartbeats 650000 in
/-- The overlap equation for every geometric morphism is precisely the
coefficient overlap equation in the ordered tensor modules. -/
theorem affineDescentCoefficientOverlap_preserves (m : D ⟶ E) :
    let M := affineDescentCoefficientModule D
    let N := affineDescentCoefficientModule E
    letI : Module A M := Module.compHom _ (algebraMap A B)
    letI : Module A N := Module.compHom _ (algebraMap A B)
    letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    ∀ x : M ⊗[A] B,
      ((affineDescentCoefficientMap m).hom.restrictScalars A).lTensor B
        (affineDescentCoefficientOverlap D x) =
      affineDescentCoefficientOverlap E (((affineDescentCoefficientMap m).hom.restrictScalars A).rTensor B x) := by
  let M := affineDescentCoefficientModule D
  let N := affineDescentCoefficientModule E
  letI : Module A M := Module.compHom _ (algebraMap A B)
  letI : Module A N := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact scalarOverlapIso_comm (A := A) (B := B) (M := M) (N := N)
    (affineDescentScalarExtensionIso D) (affineDescentScalarExtensionIso E)
    (affineDescentCoefficientMap m) (affineDescentCoefficientMap_comm m)


end

end SHIGURE.SchemeDescent
