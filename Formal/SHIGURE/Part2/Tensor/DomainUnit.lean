import Formal.SHIGURE.Part2.Tensor.DomainBaseChange
import Formal.SHIGURE.Part2.Tensor.CoefficientCoherence

/-!
# Reading specified submodules at the coefficient unit

The carrier unit identifies the whole input tensor at the base ring.
It transports each identified submodule and its linear value map to the
original domain and value, giving an isomorphism of primitive diagrams.
-/

open CategoryTheory PiTensorProduct TensorProduct SHIGURE.TensorRealization
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorDomainStructure

variable {k K : Type u} [CommRing k] {M : K → ModuleCat.{u} k} {Γ : List K}

/-- The input linear equivalence induced by the carrier unit at each typed position. -/
def unitInputEquiv : InputTensor k (extendCarriers k M k) Γ ≃ₗ[k] InputTensor k M Γ :=
  PiTensorProduct.congr (fun i : TensorPosition Γ => (scalarUnit (k := k) (M := M i.1)))

private theorem unitInputEquiv_domain (P : Submodule k (InputTensor k M Γ)) (x : k ⊗[k] P) :
    unitInputEquiv (extendDomainMap k P.subtype x) = (scalarUnit x : P).val := by
  change ((PiTensorProduct.map (fun i : TensorPosition Γ => (scalarUnit (k := k) (M := M i.1)).toLinearMap)).comp
    ((inputTensorBaseChange k M k Γ).toLinearMap.comp (P.subtype.baseChange k))) x = _
  rw [← LinearMap.comp_assoc, inputTensorBaseChange_scalarUnit, scalarUnit_natural]
  rfl

/-- The carrier unit restricts to a linear equivalence between the actual extended image and its native submodule. -/
def unitSubmodule (P : Submodule k (InputTensor k M Γ)) : extendedDomain k P.subtype ≃ₗ[k] P := by
  let e := unitInputEquiv (M := M) (Γ := Γ)
  have forward (x : extendedDomain k P.subtype) : e x.val ∈ P := by
    obtain ⟨z, hz⟩ := x.property
    rw [← hz, unitInputEquiv_domain]
    exact (scalarUnit z : P).property
  have backward (x : P) : e.symm x.val ∈ extendedDomain k P.subtype := by
    refine ⟨scalarUnit.symm x, e.injective ?_⟩
    rw [unitInputEquiv_domain, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine LinearEquiv.ofLinear (factorThrough e.toLinearMap forward)
    (factorThrough e.symm.toLinearMap backward) ?_ ?_
  · exact LinearMap.ext fun x => Subtype.ext (e.apply_symm_apply x.val)
  · exact LinearMap.ext fun x => Subtype.ext (e.symm_apply_apply x.val)

/-- The extended value map agrees with the native map under the unit on its domain and output. -/
theorem unitSubmodule_partial {V : Type u} [AddCommGroup V] [Module k V]
    (P : Submodule k (InputTensor k M Γ)) (value : P →ₗ[k] V) (h : UniversallyInjective P.subtype)
    (x : extendedDomain k P.subtype) :
    scalarUnit (extendTypedPartial k P.subtype value h x) = value (unitSubmodule P x) := by
  obtain ⟨d, hd⟩ := x.property
  have dom : unitSubmodule P x = scalarUnit d := by
    apply Subtype.ext
    change unitInputEquiv x.val = _
    rw [← hd, unitInputEquiv_domain]
  have eval : extendTypedPartial k P.subtype value h x = value.baseChange k d :=
    (congrArg (extendTypedPartial k P.subtype value h) (Subtype.ext hd.symm)).trans
      (extendTypedPartial_apply P.subtype value h d)
  rw [dom, eval]
  exact DFunLike.congr_fun (scalarUnit_natural value) d

variable {sig : Signature.{u}}

/-- At the base coefficient, the scalar unit recovers the entire tensor diagram with its specified domains. -/
def domainScalarUnit (A : Diagrams k sig) (hA : A.AdmitsBaseChange) :
    (show Diagrams k sig from extend k A hA) ≅ A := by
  let E : Diagrams k sig := extend k A hA
  let e := structureScalarUnit A.toTensorStructure
  have forwardRel (r : sig.Rel) (x : E.rel r) : inputMap e.hom (sig.relInputs r) x.val ∈ A.rel r :=
    (unitSubmodule (A.rel r) x).property
  have forwardDom (p : sig.Partial) (x : E.dom p) : inputMap e.hom (sig.partialArity p).inputs x.val ∈ A.dom p :=
    (unitSubmodule (A.dom p) x).property
  have backwardRel (r : sig.Rel) (x : A.rel r) : inputMap e.inv (sig.relInputs r) x.val ∈ E.rel r :=
    ((unitSubmodule (A.rel r)).symm x).property
  have backwardDom (p : sig.Partial) (x : A.dom p) : inputMap e.inv (sig.partialArity p).inputs x.val ∈ E.dom p :=
    ((unitSubmodule (A.dom p)).symm x).property
  have forwardValue (p : sig.Partial) (x : E.dom p) :
      e.hom.onSort _ (E.partialValue p x) = A.partialValue p (factorThrough (inputMap e.hom _) (forwardDom p) x) :=
    unitSubmodule_partial (A.dom p) (A.partialValue p) (hA p) x
  have backwardValue (p : sig.Partial) (x : A.dom p) :
      e.inv.onSort _ (A.partialValue p x) = E.partialValue p (factorThrough (inputMap e.inv _) (backwardDom p) x) := by
    apply scalarUnit.injective
    change scalarUnit (scalarUnit.symm (A.partialValue p x)) =
      scalarUnit (E.partialValue p ((unitSubmodule (A.dom p)).symm x))
    rw [LinearEquiv.apply_symm_apply]
    have h := unitSubmodule_partial (A.dom p) (A.partialValue p) (hA p) ((unitSubmodule (A.dom p)).symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨homOfLinearMaps e.hom forwardRel forwardDom forwardValue,
    homOfLinearMaps e.inv backwardRel backwardDom backwardValue, ?_, ?_⟩
  · apply hom_ext
    intro s
    exact LinearMap.ext fun x => scalarUnit.symm_apply_apply x
  · apply hom_ext
    intro s
    exact LinearMap.ext fun x => scalarUnit.apply_symm_apply x

end SHIGURE.TensorDomainStructure
