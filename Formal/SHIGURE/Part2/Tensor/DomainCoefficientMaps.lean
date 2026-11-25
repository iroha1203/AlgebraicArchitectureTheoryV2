import Formal.SHIGURE.Part2.Tensor.DomainNativeMaps

/-!
# Coefficient maps on the prescribed tensor submodules

The coefficient map on an input tensor is the actual map on its scalar
extension coordinates. Each extended submodule inherits that map, and
the partial values commute with the induced change on the domain.
-/

open CategoryTheory PiTensorProduct TensorProduct SHIGURE.TensorRealization
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k R S K : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
variable {M N : K → ModuleCat.{u} k} {Γ : List K}

/-- Transport a typed input tensor along the given coefficient algebra map. -/
def mapInputCoefficients (f : R →ₐ[k] S) :
    InputTensor R (extendCarriers k M R) Γ →ₛₗ[f.toRingHom] InputTensor S (extendCarriers k M S) Γ :=
  (inputTensorBaseChange k M S Γ).toLinearMap.comp
    ((mapCoefficients f).comp (inputTensorBaseChange k M R Γ).symm.toLinearMap)

variable {D : Type u} [AddCommGroup D] [Module k D]

/-- The coefficient map on input tensors carries the extended inclusion square to itself. -/
theorem mapInputCoefficients_extendDomainMap (f : R →ₐ[k] S)
    (a : D →ₗ[k] InputTensor k M Γ) (x : R ⊗[k] D) :
    mapInputCoefficients f (extendDomainMap R a x) = extendDomainMap S a (mapCoefficients f x) := by
  change inputTensorBaseChange k M S Γ (mapCoefficients f
      ((inputTensorBaseChange k M R Γ).symm (inputTensorBaseChange k M R Γ (a.baseChange R x)))) =
    inputTensorBaseChange k M S Γ (a.baseChange S (mapCoefficients f x))
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (inputTensorBaseChange k M S Γ) (LinearMap.rTensor_baseChange f x a)

/-- Changing coefficients commutes with the input tensor map induced by extended carrier maps. -/
theorem mapInputCoefficients_inputMap (f : R →ₐ[k] S) (g : ∀ s, M s →ₗ[k] N s)
    (x : InputTensor R (extendCarriers k M R) Γ) :
    mapInputCoefficients f (PiTensorProduct.map (fun i : TensorPosition Γ => (g i.1).baseChange R) x) =
      PiTensorProduct.map (fun i : TensorPosition Γ => (g i.1).baseChange S) (mapInputCoefficients f x) := by
  let m := PiTensorProduct.map (fun i : TensorPosition Γ => g i.1)
  let y := (inputTensorBaseChange k M R Γ).symm x
  let z := mapCoefficients f y
  have hR := DFunLike.congr_fun (inputTensorBaseChange_map (R := R) (Γ := Γ) g) y
  have hS := DFunLike.congr_fun (inputTensorBaseChange_map (R := S) (Γ := Γ) g) z
  change PiTensorProduct.map (fun i : TensorPosition Γ => (g i.1).baseChange R)
    (inputTensorBaseChange k M R Γ y) = inputTensorBaseChange k N R Γ (m.baseChange R y) at hR
  change PiTensorProduct.map (fun i : TensorPosition Γ => (g i.1).baseChange S)
    (inputTensorBaseChange k M S Γ z) = inputTensorBaseChange k N S Γ (m.baseChange S z) at hS
  rw [LinearEquiv.apply_symm_apply] at hR
  change inputTensorBaseChange k N S Γ (mapCoefficients f ((inputTensorBaseChange k N R Γ).symm
    (PiTensorProduct.map (fun i : TensorPosition Γ => (g i.1).baseChange R) x))) =
    PiTensorProduct.map (fun i : TensorPosition Γ => (g i.1).baseChange S) (inputTensorBaseChange k M S Γ z)
  rw [hR, hS, LinearEquiv.symm_apply_apply]
  exact congrArg (inputTensorBaseChange k N S Γ) (LinearMap.rTensor_baseChange f y m)

/-- The coefficient map restricts to each actual image submodule. -/
def mapExtendedDomainCoefficients (f : R →ₐ[k] S) (a : D →ₗ[k] InputTensor k M Γ) :
    extendedDomain R a →ₛₗ[f.toRingHom] extendedDomain S a :=
  ((mapInputCoefficients f).comp (extendedDomain R a).subtype).codRestrict _ (by
    intro x
    obtain ⟨d, hd⟩ := x.property
    refine ⟨mapCoefficients f d, ?_⟩
    exact (mapInputCoefficients_extendDomainMap f a d).symm.trans (congrArg _ hd))

/-- Partial values commute with coefficient maps on the whole extended domain. -/
theorem mapCoefficients_extendTypedPartial {V : Type u} [AddCommGroup V] [Module k V]
    (f : R →ₐ[k] S) (a : D →ₗ[k] InputTensor k M Γ) (value : D →ₗ[k] V)
    (h : UniversallyInjective a) (x : extendedDomain R a) :
    mapCoefficients f (extendTypedPartial R a value h x) =
      extendTypedPartial S a value h (mapExtendedDomainCoefficients f a x) := by
  obtain ⟨d, hd⟩ := x.property
  have dR : x = ⟨extendDomainMap R a d, ⟨d, rfl⟩⟩ := Subtype.ext hd.symm
  have dS : mapExtendedDomainCoefficients f a x =
      ⟨extendDomainMap S a (mapCoefficients f d), ⟨mapCoefficients f d, rfl⟩⟩ :=
    Subtype.ext ((congrArg (mapInputCoefficients f) hd.symm).trans (mapInputCoefficients_extendDomainMap f a d))
  conv_lhs => rw [dR, extendTypedPartial_apply]
  rw [dS, extendTypedPartial_apply]
  exact LinearMap.rTensor_baseChange f d value

end SHIGURE.TensorRealization

namespace SHIGURE.TensorDomainStructure.NaturalDomainHom

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
variable {sig : Signature.{u}} {A B : Diagrams k sig} {hA : A.AdmitsBaseChange} {hB : B.AdmitsBaseChange}

/-- Carrier naturality determines the commutative coefficient square on every typed input. -/
theorem naturalInput (g : NaturalDomainHom hA hB) (f : R →ₐ[k] S) (Γ : List sig.SortType)
    (x : InputTensor R (extendCarriers k A.carrier R) Γ) :
    mapInputCoefficients f (inputMap (forgetHom (g.app R)) Γ x) =
      inputMap (forgetHom (g.app S)) Γ (mapInputCoefficients f x) := by
  rw [← g.ofNative_native]
  change mapInputCoefficients f
      (PiTensorProduct.map (fun i : TensorPosition Γ => ((extendHom R hA hB g.native).val i.1).hom) x) =
    PiTensorProduct.map (fun i : TensorPosition Γ => ((extendHom S hA hB g.native).val i.1).hom)
      (mapInputCoefficients f x)
  simp only [extendHom_onSort]
  exact mapInputCoefficients_inputMap f (fun s => (g.native.val s).hom) x

/-- The actual coefficients commute with the preservation factor on each relation submodule. -/
theorem naturalRelation (g : NaturalDomainHom hA hB) (f : R →ₐ[k] S) (r : sig.Rel)
    (x : (extend R A hA).rel r) :
    mapExtendedDomainCoefficients f (B.rel r).subtype
      (factorThrough (inputMap (forgetHom (g.app R)) _) ((readLinearArrow (g.app R)).relation r) x) =
    factorThrough (inputMap (forgetHom (g.app S)) _) ((readLinearArrow (g.app S)).relation r)
      (mapExtendedDomainCoefficients f (A.rel r).subtype x) :=
  Subtype.ext (g.naturalInput f (sig.relInputs r) x.val)

/-- The actual coefficients commute with the preservation factor on each partial domain. -/
theorem naturalPartialDomain (g : NaturalDomainHom hA hB) (f : R →ₐ[k] S) (p : sig.Partial)
    (x : (extend R A hA).dom p) :
    mapExtendedDomainCoefficients f (B.dom p).subtype
      (factorThrough (inputMap (forgetHom (g.app R)) _) ((readLinearArrow (g.app R)).domain p) x) =
    factorThrough (inputMap (forgetHom (g.app S)) _) ((readLinearArrow (g.app S)).domain p)
      (mapExtendedDomainCoefficients f (A.dom p).subtype x) :=
  Subtype.ext (g.naturalInput f (sig.partialArity p).inputs x.val)

end SHIGURE.TensorDomainStructure.NaturalDomainHom
