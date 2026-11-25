import Formal.SHIGURE.Part2.Tensor.DomainStructures
import Formal.SHIGURE.Part2.Tensor.CoefficientFunctor
import Formal.SHIGURE.Part2.Tensor.PartialOperations

/-!
# Scalar extension on the primitive submodule diagrams

The scalar extension of each selected domain is its image in the new
input tensor. Universal injectivity identifies its value map with the
base change of the original linear map on the domain.
-/

open CategoryTheory PiTensorProduct TensorProduct SHIGURE.TensorRealization
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k R K : Type u} [CommRing k] [CommRing R] [Algebra k R]
variable {M N : K → ModuleCat.{u} k} {Γ : List K}

private theorem extendedInputMap_ext {P : Type u} [AddCommGroup P] [Module R P]
    {f g : R ⊗[k] InputTensor k M Γ →ₗ[R] P}
    (h : ∀ x : (i : TensorPosition Γ) → M i.1,
      f ((1 : R) ⊗ₜ[k] tprod k x) = g ((1 : R) ⊗ₜ[k] tprod k x)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul r y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod a x =>
      rw [← TensorProduct.smul_tmul (R := k) (R' := k) a r (tprod k x)]
      have hr : (a • r) ⊗ₜ[k] tprod k x = (a • r) • ((1 : R) ⊗ₜ[k] tprod k x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hr, map_smul, map_smul, h x]
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

/-- Base change of the input square is comparison of the actual extended carrier maps. -/
theorem inputTensorBaseChange_map (f : ∀ s, M s →ₗ[k] N s) :
    (PiTensorProduct.map (fun i : TensorPosition Γ => (f i.1).baseChange R)).comp
        (inputTensorBaseChange k M R Γ).toLinearMap =
      (inputTensorBaseChange k N R Γ).toLinearMap.comp
        ((PiTensorProduct.map (fun i : TensorPosition Γ => f i.1)).baseChange R) := by
  apply extendedInputMap_ext (M := M) (Γ := Γ) (R := R)
    (P := InputTensor R (extendCarriers k N R) Γ)
  intro x
  change (PiTensorProduct.map (fun i : TensorPosition Γ => (f i.1).baseChange R))
      (inputTensorBaseChange k M R Γ ((1 : R) ⊗ₜ[k] tprod k x)) =
    inputTensorBaseChange k N R Γ
      (((PiTensorProduct.map (fun i : TensorPosition Γ => f i.1)).baseChange R) ((1 : R) ⊗ₜ[k] tprod k x))
  rw [inputTensorBaseChange_unit_tprod, LinearMap.baseChange_tmul, PiTensorProduct.map_tprod,
    PiTensorProduct.map_tprod, inputTensorBaseChange_unit_tprod]
  simp only [LinearMap.baseChange_tmul]

/-- The carrier unit maps induce the scalar unit on the entire input tensor. -/
theorem inputTensorBaseChange_scalarUnit :
    (PiTensorProduct.map (fun i : TensorPosition Γ => (scalarUnit (k := k) (M := M i.1)).toLinearMap)).comp
        (inputTensorBaseChange k M k Γ).toLinearMap =
      (scalarUnit (k := k) (M := InputTensor k M Γ)).toLinearMap := by
  apply extendedInputMap_ext (M := M) (Γ := Γ)
  intro x
  change (PiTensorProduct.map (fun i : TensorPosition Γ => (scalarUnit (k := k) (M := M i.1)).toLinearMap))
      (inputTensorBaseChange k M k Γ ((1 : k) ⊗ₜ[k] tprod k x)) = scalarUnit ((1 : k) ⊗ₜ[k] tprod k x)
  rw [inputTensorBaseChange_unit_tprod, PiTensorProduct.map_tprod, scalarUnit_tmul, one_smul]
  congr 1
  funext i
  change scalarUnit ((1 : k) ⊗ₜ[k] x i) = _
  rw [scalarUnit_tmul, one_smul]

/-- A factorization of an input map through selected modules remains a factorization after scalar extension. -/
theorem extendDomainMap_factor {D E : Type u} [AddCommGroup D] [Module k D] [AddCommGroup E] [Module k E]
    (f : ∀ s, M s →ₗ[k] N s) (a : D →ₗ[k] InputTensor k M Γ) (b : E →ₗ[k] InputTensor k N Γ)
    (d : D →ₗ[k] E) (h : b.comp d = (PiTensorProduct.map (fun i : TensorPosition Γ => f i.1)).comp a) :
    (extendDomainMap R b).comp (d.baseChange R) =
      (PiTensorProduct.map (fun i : TensorPosition Γ => (f i.1).baseChange R)).comp (extendDomainMap R a) := by
  simp only [extendDomainMap, LinearMap.comp_assoc, ← LinearMap.baseChange_comp, h]
  rw [LinearMap.baseChange_comp, ← LinearMap.comp_assoc, ← inputTensorBaseChange_map, LinearMap.comp_assoc]

end SHIGURE.TensorRealization

namespace SHIGURE.TensorDomainStructure

variable {k : Type u} [CommRing k] {sig : Signature.{u}}

/-- A native partial domain can be evaluated after all scalar extensions when its inclusion stays injective. -/
def AdmitsBaseChange (A : TensorDomainStructure k sig) : Prop :=
  ∀ p, UniversallyInjective (A.dom p).subtype

/-- Construction 4.8 on all the specified submodules as well as on the total operations and quantities. -/
def extend (R : Type u) [CommRing R] [Algebra k R]
    (A : TensorDomainStructure k sig) (hA : A.AdmitsBaseChange) : TensorDomainStructure R sig where
  toTensorStructure := extendStructure k R A.toTensorStructure
  rel r := extendedDomain R (A.rel r).subtype
  dom p := extendedDomain R (A.dom p).subtype
  partialValue p := extendTypedPartial R (A.dom p).subtype (A.partialValue p) (hA p)

variable (R : Type u) [CommRing R] [Algebra k R]
variable {A B : Diagrams k sig} (hA : A.AdmitsBaseChange) (hB : B.AdmitsBaseChange)

private theorem extendedFactor_mem (f : A.toTensorStructure ⟶ B.toTensorStructure)
    {Γ : List sig.SortType} {P : Submodule k (InputTensor k A.carrier Γ)}
    {Q : Submodule k (InputTensor k B.carrier Γ)} (g : P →ₗ[k] Q)
    (h : Q.subtype.comp g = (inputMap f Γ).comp P.subtype)
    (x : extendedDomain R P.subtype) :
    PiTensorProduct.map (fun i : TensorPosition Γ => (f.onSort i.1).baseChange R) x.val ∈
      extendedDomain R Q.subtype := by
  obtain ⟨d, hd⟩ := x.property
  refine ⟨g.baseChange R d, ?_⟩
  have commute := congrArg (fun m => m d) (extendDomainMap_factor (R := R) f.onSort P.subtype Q.subtype g h)
  exact commute.trans (congrArg _ hd)

/-- Scalar extension preserves the factorization through relations and the partial-value diagrams. -/
def extendHom (f : A ⟶ B) :
    (show Diagrams R sig from extend R A hA) ⟶ (show Diagrams R sig from extend R B hB) := by
  let f₀ := forgetHom f
  let fR := extendStructureMap R f₀
  have rel r (x : (extend R A hA).rel r) : inputMap fR (sig.relInputs r) x.val ∈ (extend R B hB).rel r := by
    obtain ⟨g, hg⟩ := rel_factor f r
    exact extendedFactor_mem R f₀ g hg x
  have dom p (x : (extend R A hA).dom p) : inputMap fR (sig.partialArity p).inputs x.val ∈ (extend R B hB).dom p := by
    obtain ⟨g, hg, _⟩ := dom_factor f p
    exact extendedFactor_mem R f₀ g hg x
  refine homOfLinearMaps fR rel dom ?_
  intro p x
  obtain ⟨d, hd⟩ := x.property
  obtain ⟨g, hg, hv⟩ := dom_factor f p
  have compare := congrArg (fun m => m d)
    (extendDomainMap_factor (R := R) f₀.onSort (A.dom p).subtype (B.dom p).subtype g hg)
  let y := factorThrough (inputMap fR _) (dom p) x
  have hy : extendDomainMap R (B.dom p).subtype (g.baseChange R d) = y.val :=
    compare.trans (congrArg _ hd)
  have evalA : (extend R A hA).partialValue p x = (A.partialValue p).baseChange R d :=
    (congrArg (extendTypedPartial R (A.dom p).subtype (A.partialValue p) (hA p))
      (Subtype.ext hd.symm)).trans (extendTypedPartial_apply _ _ _ _)
  have evalB : (extend R B hB).partialValue p y = (B.partialValue p).baseChange R (g.baseChange R d) :=
    (congrArg (extendTypedPartial R (B.dom p).subtype (B.partialValue p) (hB p))
      (Subtype.ext hy.symm)).trans (extendTypedPartial_apply _ _ _ _)
  change fR.onSort _ ((extend R A hA).partialValue p x) = (extend R B hB).partialValue p y
  rw [evalA, evalB]
  have e := congrArg (fun m : A.dom p →ₗ[k] _ => m.baseChange R) hv
  change ((B.partialValue p).comp g).baseChange R = ((f₀.onSort _).comp (A.partialValue p)).baseChange R at e
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at e
  exact (congrArg (fun m => m d) e).symm

/-- The diagram extension reads the scalar extension of the original carrier map. -/
theorem extendHom_onSort (f : A ⟶ B) (s : sig.SortType) :
    ((extendHom R hA hB f).val s).hom = ((f.val s).hom).baseChange R :=
  rfl

/-- Coefficient extension preserves the identity of a structure with specified domains. -/
theorem extendHom_id : extendHom R hA hA (𝟙 A) = 𝟙 (show Diagrams R sig from extend R A hA) := by
  apply hom_ext
  intro s
  rw [extendHom_onSort]
  exact LinearMap.baseChange_id

/-- Coefficient extension preserves composition of the full primitive diagrams. -/
theorem extendHom_comp {D : Diagrams k sig} (hD : D.AdmitsBaseChange) (f : A ⟶ B) (g : B ⟶ D) :
    extendHom R hA hD (f ≫ g) = extendHom R hA hB f ≫ extendHom R hB hD g := by
  apply hom_ext
  intro s
  rw [extendHom_onSort]
  change (((g.val s).hom).comp ((f.val s).hom)).baseChange R =
    ((extendHom R hB hD g).val s).hom.comp ((extendHom R hA hB f).val s).hom
  rw [extendHom_onSort, extendHom_onSort, LinearMap.baseChange_comp]

end SHIGURE.TensorDomainStructure
