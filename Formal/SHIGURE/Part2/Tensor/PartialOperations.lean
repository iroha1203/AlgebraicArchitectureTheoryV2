import Formal.SHIGURE.Part2.Realizations.TensorCoefficientExtension
import Formal.SHIGURE.Part2.Tensor.ScalarChange

/-!
# Coefficient extension on a partial domain

The image of the extended inclusion is expressed in the actual input
tensor over the new coefficients. Typed tuples are defined precisely
when their pure tensor lies in that image.
-/

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k R K : Type u} [CommRing k] [CommRing R] [Algebra k R]
variable {M : K → ModuleCat.{u} k} {Γ : List K}
variable {D N : Type u} [AddCommGroup D] [Module k D] [AddCommGroup N] [Module k N]

/-- The true input tensor receives the chosen domain by scalar extension. -/
def extendDomainMap (R : Type u) [CommRing R] [Algebra k R]
    (ι : D →ₗ[k] InputTensor k M Γ) :
    (R ⊗[k] D) →ₗ[R] InputTensor R (extendCarriers k M R) Γ :=
  (inputTensorBaseChange k M R Γ).toLinearMap.comp (ι.baseChange R)

/-- The declared domain of the changed operation is the image of the changed inclusion. -/
abbrev extendedDomain (R : Type u) [CommRing R] [Algebra k R]
    (ι : D →ₗ[k] InputTensor k M Γ) :=
  LinearMap.range (extendDomainMap R ι)

/-- The extension of a universally injective inclusion into the actual input tensor is injective. -/
theorem extendDomainMap_injective (ι : D →ₗ[k] InputTensor k M Γ) (h : UniversallyInjective ι) :
    Function.Injective (extendDomainMap R ι) :=
  (inputTensorBaseChange k M R Γ).injective.comp (h R)

/-- Extend the partial value on the image domain using its unique preimage in the scalar extension. -/
def extendTypedPartial (R : Type u) [CommRing R] [Algebra k R]
    (ι : D →ₗ[k] InputTensor k M Γ) (p : D →ₗ[k] N) (h : UniversallyInjective ι) :
    extendedDomain R ι →ₗ[R] R ⊗[k] N :=
  (p.baseChange R).comp
    (LinearEquiv.ofInjective (extendDomainMap R ι) (extendDomainMap_injective ι h)).symm.toLinearMap

/-- At an image point the extended value is the scalar extension of the original value. -/
theorem extendTypedPartial_apply (ι : D →ₗ[k] InputTensor k M Γ) (p : D →ₗ[k] N)
    (h : UniversallyInjective ι) (x : R ⊗[k] D) :
    extendTypedPartial R ι p h ⟨extendDomainMap R ι x, ⟨x, rfl⟩⟩ = p.baseChange R x :=
  congrArg (p.baseChange R)
    ((LinearEquiv.ofInjective (extendDomainMap R ι) (extendDomainMap_injective ι h)).symm_apply_apply x)

/-- A tuple is defined when its pure tensor is in the actual extended domain. -/
abbrev TensorDomainTuples (R : Type u) [CommRing R] [Algebra k R]
    (ι : D →ₗ[k] InputTensor k M Γ) :=
  {x : ∀ i : TensorPosition Γ, extendCarriers k M R i.1 //
    PiTensorProduct.tprod R x ∈ extendedDomain R ι}

/-- Evaluate the new partial operation on a tuple whose pure tensor lies in its domain. -/
def extendedPartialValue (R : Type u) [CommRing R] [Algebra k R]
    (ι : D →ₗ[k] InputTensor k M Γ) (p : D →ₗ[k] N) (h : UniversallyInjective ι)
    (x : TensorDomainTuples R ι) : R ⊗[k] N :=
  extendTypedPartial R ι p h ⟨PiTensorProduct.tprod R x.val, x.property⟩

/-- Every representative in the extended domain gives the same partial value. -/
theorem extendedPartialValue_eq (ι : D →ₗ[k] InputTensor k M Γ) (p : D →ₗ[k] N)
    (h : UniversallyInjective ι) (x : TensorDomainTuples R ι) (d : R ⊗[k] D)
    (hd : extendDomainMap R ι d = PiTensorProduct.tprod R x.val) :
    extendedPartialValue R ι p h x = p.baseChange R d := by
  have e : (⟨PiTensorProduct.tprod R x.val, x.property⟩ : extendedDomain R ι) =
      ⟨extendDomainMap R ι d, ⟨d, rfl⟩⟩ :=
    Subtype.ext hd.symm
  exact (congrArg (extendTypedPartial R ι p h) e).trans (extendTypedPartial_apply ι p h d)

/-- A tuple in the original domain extends to a defined tuple and the unit
tensor of its original partial value. -/
theorem extendedPartialValue_unit (ι : D →ₗ[k] InputTensor k M Γ) (p : D →ₗ[k] N)
    (h : UniversallyInjective ι) (x : ∀ i : TensorPosition Γ, M i.1) (d : D)
    (hd : ι d = PiTensorProduct.tprod k x) :
    ∃ y : TensorDomainTuples R ι,
      y.val = (fun i => (1 : R) ⊗ₜ[k] x i) ∧ extendedPartialValue R ι p h y = (1 : R) ⊗ₜ[k] p d := by
  let value (i : TensorPosition Γ) : extendCarriers k M R i.1 := (1 : R) ⊗ₜ[k] x i
  have hdR : extendDomainMap R ι ((1 : R) ⊗ₜ[k] d) = PiTensorProduct.tprod R value := by
    change inputTensorBaseChange k M R Γ (ι.baseChange R ((1 : R) ⊗ₜ[k] d)) = _
    rw [LinearMap.baseChange_tmul, hd, inputTensorBaseChange_unit_tprod]
    rfl
  exact ⟨⟨value, ⟨(1 : R) ⊗ₜ[k] d, hdR⟩⟩, rfl,
    (extendedPartialValue_eq ι p h _ _ hdR).trans (LinearMap.baseChange_tmul p 1 d)⟩

end SHIGURE.TensorRealization
