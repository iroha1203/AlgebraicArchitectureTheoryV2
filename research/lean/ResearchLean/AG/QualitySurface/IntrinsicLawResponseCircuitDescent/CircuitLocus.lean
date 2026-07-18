import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Equalizer
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.LinearRepair

/-!
# Affine circuit locus

This file proves the affine module theorem underlying the G-08 circuit locus.
For a finite projective operation module and a protected response map whose
image and cokernel are projective, the kernel is finite projective and its
canonical tensor-to-kernel map is an equivalence after every scalar extension.
The cokernel support is then identified with residue-field normalized-repair
failure and, through `LinearRepair`, with a target-containing support-minimal
circuit.

## Implementation notes

The forward kernel comparison is fixed to mathlib's canonical
`LinearMap.tensorKer`. Projective splittings are used only to prove that map
bijective; choosing a splitting as the comparison map would lose the required
canonical provenance. The response family is represented by `LinearMap.pi`
because the protected labels are finite, rather than by a custom response
matrix wrapper. Support is read through mathlib's residue-field tensor
characterization and then connected to the reviewed `LinearRepair` API;
storing a repair or circuit certificate in a new structure would make the
conclusion an input and is therefore deliberately avoided.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent
namespace CircuitLocus

open LinearMap

universe uR uE uF

variable {R : Type uR} {E : Type uE} {F : Type uF}
variable [CommRing R] [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]

/-- A projective-lifting API helper that chooses a section of the range
restriction. Its projective-range premise is the split-regularity direction
hypothesis; the chosen section is not a comparison certificate. -/
noncomputable def rangeSection (f : E →ₗ[R] F) [Module.Projective R f.range] :
    f.range →ₗ[R] E :=
  Classical.choose <| Module.projective_lifting_property f.rangeRestrict LinearMap.id
    (LinearMap.range_eq_top.mp f.range_rangeRestrict)

/-- The API law for `rangeSection`: composing with the range restriction is
the identity. This exposes the lifting-property construction without requiring
downstream proofs to unfold it. -/
theorem rangeSection_spec (f : E →ₗ[R] F) [Module.Projective R f.range] :
    f.rangeRestrict ∘ₗ rangeSection f = LinearMap.id :=
  Classical.choose_spec <| Module.projective_lifting_property f.rangeRestrict LinearMap.id
    (LinearMap.range_eq_top.mp f.range_rangeRestrict)

/-- The projection onto the kernel induced by the projective range splitting.
This is an API construction for the C0a kernel theorem, not the scalar
base-change map. -/
noncomputable def kernelProjection (f : E →ₗ[R] F) [Module.Projective R f.range] :
    E →ₗ[R] f.ker where
  toFun e := ⟨e - rangeSection f (f.rangeRestrict e), by
    rw [LinearMap.mem_ker, map_sub]
    have h := DFunLike.congr_fun (rangeSection_spec f) (f.rangeRestrict e)
    exact sub_eq_zero.mpr (congrArg Subtype.val h).symm⟩
  map_add' x y := by
    apply Subtype.ext
    dsimp
    simp only [map_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    dsimp
    simp only [map_smul]
    exact (smul_sub r x (rangeSection f (f.rangeRestrict x))).symm

/-- The kernel projection retracts the canonical kernel subtype. This is the
split-submodule API used by the finite and projective kernel results. -/
theorem kernelProjection_comp_subtype (f : E →ₗ[R] F) [Module.Projective R f.range] :
    kernelProjection f ∘ₗ f.ker.subtype = LinearMap.id := by
  ext x
  change x.1 - rangeSection f (f.rangeRestrict x.1) = x.1
  have hx : f.rangeRestrict x.1 = 0 := by
    apply Subtype.ext
    exact x.2
  rw [hx, map_zero, sub_zero]

/-- C0a accepted result: the kernel of a map from a finite module is finite
when the map range is projective. The projective-range premise supplies the
split used to construct the finite quotient. -/
theorem kernel_finite (f : E →ₗ[R] F) [Module.Finite R E]
    [Module.Projective R f.range] : Module.Finite R f.ker := by
  apply Module.Finite.of_surjective (kernelProjection f)
  intro x
  exact ⟨x, DFunLike.congr_fun (kernelProjection_comp_subtype f) x⟩

/-- C0a accepted result: a split kernel of a map from a projective module is
projective. Projectivity of the range supplies the splitting. -/
theorem kernel_projective (f : E →ₗ[R] F) [Module.Projective R E]
    [Module.Projective R f.range] : Module.Projective R f.ker :=
  Module.Projective.of_split f.ker.subtype (kernelProjection f)
    (kernelProjection_comp_subtype f)

/-- A projective-lifting API helper that chooses a section of the quotient by
a submodule. It is used to split the response-map image inclusion after scalar
extension. -/
noncomputable def quotientSection (p : Submodule R F)
    [Module.Projective R (F ⧸ p)] : (F ⧸ p) →ₗ[R] F :=
  Classical.choose <| Module.projective_lifting_property p.mkQ LinearMap.id
    (Submodule.mkQ_surjective p)

/-- The API law for `quotientSection`: quotienting after the chosen lift is the
identity. -/
theorem quotientSection_spec (p : Submodule R F)
    [Module.Projective R (F ⧸ p)] :
    p.mkQ ∘ₗ quotientSection p = LinearMap.id :=
  Classical.choose_spec <| Module.projective_lifting_property p.mkQ LinearMap.id
    (Submodule.mkQ_surjective p)

/-- The projection onto a submodule obtained from a projective quotient. For a
response-map range this supplies the image-inclusion splitting used in the
surjectivity proof for canonical kernel base change. -/
noncomputable def submoduleProjection (p : Submodule R F)
    [Module.Projective R (F ⧸ p)] : F →ₗ[R] p where
  toFun y := ⟨y - quotientSection p (p.mkQ y), by
    apply (Submodule.Quotient.mk_eq_zero
      (p := p) (x := y - quotientSection p (p.mkQ y))).mp
    rw [Submodule.Quotient.mk_sub]
    change p.mkQ y - p.mkQ (quotientSection p (p.mkQ y)) = 0
    have h := DFunLike.congr_fun (quotientSection_spec p) (p.mkQ y)
    exact sub_eq_zero.mpr h.symm⟩
  map_add' x y := by
    apply Subtype.ext
    dsimp
    simp only [map_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    dsimp
    simp only [map_smul]
    exact (smul_sub r x (quotientSection p (p.mkQ x))).symm

/-- The submodule projection retracts the canonical subtype inclusion. -/
theorem submoduleProjection_comp_subtype (p : Submodule R F)
    [Module.Projective R (F ⧸ p)] :
    submoduleProjection p ∘ₗ p.subtype = LinearMap.id := by
  ext x
  change x.1 - quotientSection p (p.mkQ x.1) = x.1
  have hx : p.mkQ x.1 = 0 :=
    (Submodule.Quotient.mk_eq_zero (p := p) (x := x.1)).mpr x.2
  rw [hx, map_zero, sub_zero]

/-- The source decomposes as its kernel component plus its chosen range
component. This API lemma supplies the computation used after scalar
extension. -/
theorem kernel_decomposition (f : E →ₗ[R] F) [Module.Projective R f.range] :
    f.ker.subtype ∘ₗ kernelProjection f + rangeSection f ∘ₗ f.rangeRestrict =
      LinearMap.id := by
  ext x
  simp [kernelProjection]

variable (A : Type*) [CommRing A] [Algebra R A]

/-- C0a accepted construction: the forward scalar-extension comparison for a
kernel, fixed to mathlib's canonical `LinearMap.tensorKer`. It has no supplied
comparison or inverse certificate. -/
noncomputable def kernelBaseChangeMap (f : E →ₗ[R] F) :
    TensorProduct R A f.ker →ₗ[A] (f.baseChange A).ker :=
  f.tensorKer A A

/-- The canonical kernel base-change map is injective when the original range
is projective. The proof transports the kernel splitting through tensor. -/
theorem kernelBaseChangeMap_injective (f : E →ₗ[R] F)
    [Module.Projective R f.range] :
    Function.Injective (kernelBaseChangeMap A f) := by
  intro x y hxy
  have hcoe : f.ker.subtype.lTensor A x = f.ker.subtype.lTensor A y := by
    have h := congrArg Subtype.val hxy
    change ((f.tensorKer A A x : (f.baseChange A).ker) :
      TensorProduct R A E) =
      ((f.tensorKer A A y : (f.baseChange A).ker) : TensorProduct R A E) at h
    simpa only [LinearMap.tensorKer_coe] using h
  have hleft := congrArg (fun z ↦ (kernelProjection f).lTensor A z) hcoe
  simpa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    kernelProjection_comp_subtype] using hleft

/-- Base change preserves injectivity of a range subtype when the quotient is
projective. This is the image-splitting API used by kernel-base-change
surjectivity. -/
theorem rangeSubtype_baseChange_injective (f : E →ₗ[R] F)
    [Module.Projective R (F ⧸ f.range)] :
    Function.Injective (f.range.subtype.baseChange A) := by
  intro x y hxy
  have hleft := congrArg (fun z ↦ (submoduleProjection f.range).baseChange A z) hxy
  simpa [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    submoduleProjection_comp_subtype] using hleft

/-- The canonical kernel base-change map is surjective when the range and its
quotient are projective. Both projective premises are used through their
source-level splittings. -/
theorem kernelBaseChangeMap_surjective (f : E →ₗ[R] F)
    [Module.Projective R f.range] [Module.Projective R (F ⧸ f.range)] :
    Function.Surjective (kernelBaseChangeMap A f) := by
  intro x
  refine ⟨(kernelProjection f).baseChange A x.1, ?_⟩
  apply Subtype.ext
  have hrr : f.rangeRestrict.baseChange A x.1 = 0 := by
    apply rangeSubtype_baseChange_injective A f
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    change f.baseChange A x.1 = 0
    exact x.2
  have hdecomp := congrArg (fun g : E →ₗ[R] E ↦ g.baseChange A)
    (kernel_decomposition f)
  have happ := DFunLike.congr_fun hdecomp x.1
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_comp,
    LinearMap.baseChange_id, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, hrr, map_zero, add_zero] at happ
  change (f.tensorKer A A ((kernelProjection f).baseChange A x.1) :
    TensorProduct R A E) = x.1
  rw [LinearMap.tensorKer_coe]
  simpa only [LinearMap.baseChange_eq_ltensor] using happ

/-- C0a accepted result: mathlib's canonical kernel base-change map is a
linear equivalence for every commutative scalar extension under the two split
regularity direction hypotheses. -/
noncomputable def kernelBaseChangeEquiv (f : E →ₗ[R] F)
    [Module.Projective R f.range] [Module.Projective R (F ⧸ f.range)] :
    TensorProduct R A f.ker ≃ₗ[A] (f.baseChange A).ker :=
  LinearEquiv.ofBijective (kernelBaseChangeMap A f)
    ⟨kernelBaseChangeMap_injective A f, kernelBaseChangeMap_surjective A f⟩

/-- Right-exactness API: the scalar extension of a scalar-map cokernel is
nontrivial exactly when the base-changed scalar map is not surjective. -/
theorem tensor_responseCokernel_nontrivial_iff_not_surjective
    (s : E →ₗ[R] R) :
    Nontrivial (TensorProduct R A (R ⧸ LinearMap.range s)) ↔
      ¬ Function.Surjective (s.baseChange A) := by
  let e := lTensor.equiv A s.exact_map_mkQ_range
    (Submodule.mkQ_surjective (LinearMap.range s))
  rw [← e.nontrivial_congr, Submodule.Quotient.nontrivial_iff]
  simpa only [LinearMap.baseChange_eq_ltensor] using
    not_congr (LinearMap.range_eq_top :
      LinearMap.range (LinearMap.lTensor A s) = ⊤ ↔
        Function.Surjective (LinearMap.lTensor A s))

/-- C0a accepted support comparison: a prime belongs to the response
cokernel's support exactly when the residue-field base change of the scalar
response is not surjective. -/
theorem mem_support_responseCokernel_iff (s : E →ₗ[R] R)
    (p : PrimeSpectrum R) :
    p ∈ Module.support R (R ⧸ LinearMap.range s) ↔
      ¬ Function.Surjective (s.baseChange p.asIdeal.ResidueField) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact tensor_responseCokernel_nontrivial_iff_not_surjective
    p.asIdeal.ResidueField s

/-- The scalar-valued response on a tensor fiber, using the canonical
tensor-unit equivalence rather than a selected coordinate identification. -/
noncomputable def residueScalarMap (s : E →ₗ[R] R) :
    TensorProduct R A E →ₗ[A] A :=
  (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap.comp
    (s.baseChange A)

/-- A scalar-valued base-changed response is surjective exactly when it takes
the value one. This API lemma packages the normalization witness. -/
theorem residueScalarMap_surjective_iff_exists_one (s : E →ₗ[R] R) :
    Function.Surjective (s.baseChange A) ↔
      ∃ x, residueScalarMap A s x = 1 := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs ((TensorProduct.AlgebraTensorModule.rid R A A).symm 1)
    refine ⟨x, ?_⟩
    simp [residueScalarMap, hx]
  · rintro ⟨x, hx⟩ y
    let e := TensorProduct.AlgebraTensorModule.rid R A A
    obtain ⟨z, hz⟩ : ∃ z, residueScalarMap A s z = e y := by
      refine ⟨(e y) • x, ?_⟩
      simp [map_smul, hx]
    refine ⟨z, e.injective ?_⟩
    exact hz

section ResponseFamily

variable {L : Type*}

/-- The protected response map is the canonical finite product of the
protected labeled functionals. Finiteness comes from `P : Finset L`; no
response matrix is supplied. -/
def protectedResponseMap (response : L → Module.Dual R E) (P : Finset L) :
    E →ₗ[R] (P → R) :=
  LinearMap.pi (fun p : P ↦ response p.1)

/-- The target response restricted canonically to the generated protected
kernel. This is the C0a scalar map whose cokernel support is studied. -/
def targetOnProtectedKernel (response : L → Module.Dual R E)
    (P : Finset L) (target : L) :
    (protectedResponseMap response P).ker →ₗ[R] R :=
  (response target).comp (protectedResponseMap response P).ker.subtype

/-- The labeled response on a scalar-extension fiber, obtained from
`residueScalarMap` and hence from the original response functional. -/
noncomputable def fiberResponse (response : L → Module.Dual R E)
    (label : L) : Module.Dual A (TensorProduct R A E) :=
  residueScalarMap A (response label)

/-- The base-changed protected response agrees with the finite product of the
fiber responses after the canonical finite-product tensor equivalence. -/
theorem protectedResponseMap_baseChange_comp_piScalarRight
    (response : L → Module.Dual R E) (P : Finset L) :
    (TensorProduct.piScalarRightHom R A A P).comp
        ((protectedResponseMap response P).baseChange A) =
      LinearMap.pi (fun p : P ↦ fiberResponse A response p.1) := by
  classical
  ext a e
  simp [protectedResponseMap, fiberResponse, residueScalarMap]

/-- Evaluation of the target-on-kernel response commutes with the canonical
kernel base-change equivalence. The range/cokernel projectivity premises are
the split-regularity direction hypotheses used to build that equivalence. -/
theorem residueScalarMap_targetOnProtectedKernel
    (response : L → Module.Dual R E) (P : Finset L) (target : L)
    [Module.Projective R (protectedResponseMap response P).range]
    [Module.Projective R ((P → R) ⧸ (protectedResponseMap response P).range)]
    (x : TensorProduct R A (protectedResponseMap response P).ker) :
    residueScalarMap A (targetOnProtectedKernel response P target) x =
      fiberResponse A response target
        ((kernelBaseChangeEquiv A (protectedResponseMap response P) x).1) := by
  simp only [residueScalarMap, targetOnProtectedKernel, fiberResponse,
    kernelBaseChangeEquiv, LinearMap.comp_apply,
    LinearMap.baseChange_eq_ltensor]
  congr 1
  simp only [LinearEquiv.ofBijective_apply]
  change (LinearMap.lTensor A
      ((response target).comp (protectedResponseMap response P).ker.subtype)) x =
    LinearMap.lTensor A (response target)
      ((kernelBaseChangeMap A (protectedResponseMap response P) x).1)
  rw [kernelBaseChangeMap]
  have hcoe := LinearMap.tensorKer_coe
    (S := A) (M := A) (f := protectedResponseMap response P) x
  calc
    _ = LinearMap.lTensor A (response target)
          (LinearMap.lTensor A
            (protectedResponseMap response P).ker.subtype x) :=
      LinearMap.lTensor_comp_apply
        (M := A) (f := (protectedResponseMap response P).ker.subtype)
        (g := response target) x
    _ = _ := congrArg
      (fun z : TensorProduct R A E ↦ LinearMap.lTensor A (response target) z)
      hcoe.symm

variable {K : Type*} [Field K] [Algebra R K]

/-- C0a accepted result: an actual normalized repair vector in the fiber is
equivalent to a scalar-one witness on the base-changed protected kernel. The
repair is constructed through finite-product and kernel-base-change APIs. -/
theorem exists_fiber_normalizedRepair_iff_exists_scalarOnKernel
    (response : L → Module.Dual R E) (P : Finset L) (target : L)
    [Module.Projective R (protectedResponseMap response P).range]
    [Module.Projective R ((P → R) ⧸ (protectedResponseMap response P).range)] :
    (∃ repair : TensorProduct R K E,
        (∀ p : P, fiberResponse K response p.1 repair = 0) ∧
          fiberResponse K response target repair = 1) ↔
      ∃ x : TensorProduct R K (protectedResponseMap response P).ker,
        residueScalarMap K (targetOnProtectedKernel response P target) x = 1 := by
  classical
  let f := protectedResponseMap response P
  let e := kernelBaseChangeEquiv K f
  constructor
  · rintro ⟨repair, hprotected, htarget⟩
    have hfamily : LinearMap.pi (fun p : P ↦ fiberResponse K response p.1) repair = 0 := by
      ext p
      exact hprotected p
    have hcomp := DFunLike.congr_fun
      (protectedResponseMap_baseChange_comp_piScalarRight K response P) repair
    have hpiHom : TensorProduct.piScalarRightHom R K K P
        ((protectedResponseMap response P).baseChange K repair) = 0 := by
      rw [LinearMap.comp_apply] at hcomp
      rw [hcomp, hfamily]
    have hzero : (protectedResponseMap response P).baseChange K repair = 0 := by
      apply (TensorProduct.piScalarRight R K K P).injective
      simpa [TensorProduct.piScalarRight_apply] using hpiHom
    let y : (f.baseChange K).ker := ⟨repair, hzero⟩
    refine ⟨e.symm y, ?_⟩
    rw [residueScalarMap_targetOnProtectedKernel]
    simpa [e, f, y] using htarget
  · rintro ⟨x, hx⟩
    let repair : TensorProduct R K E :=
      (kernelBaseChangeEquiv K (protectedResponseMap response P) x).1
    have hfamily : LinearMap.pi (fun p : P ↦ fiberResponse K response p.1) repair = 0 := by
      rw [← protectedResponseMap_baseChange_comp_piScalarRight K response P]
      simp [repair]
    refine ⟨repair, ?_, ?_⟩
    · intro p
      have hp := congrFun hfamily p
      simpa using hp
    · rw [← residueScalarMap_targetOnProtectedKernel K response P target x]
      exact hx

/-- C0a accepted result: response-cokernel support at a prime is equivalent to
failure of an actual normalized repair in its residue-field fiber. The
projectivity premises provide the two canonical comparison theorems used in
the proof. -/
theorem mem_support_responseCokernel_iff_no_fiber_normalizedRepair
    (response : L → Module.Dual R E) (P : Finset L) (target : L)
    [Module.Projective R (protectedResponseMap response P).range]
    [Module.Projective R ((P → R) ⧸ (protectedResponseMap response P).range)]
    (p : PrimeSpectrum R) :
    p ∈ Module.support R
        (R ⧸ LinearMap.range (targetOnProtectedKernel response P target)) ↔
      ¬ ∃ repair : TensorProduct R p.asIdeal.ResidueField E,
        (∀ label : P,
          fiberResponse p.asIdeal.ResidueField response label.1 repair = 0) ∧
        fiberResponse p.asIdeal.ResidueField response target repair = 1 := by
  rw [mem_support_responseCokernel_iff,
    residueScalarMap_surjective_iff_exists_one,
    ← exists_fiber_normalizedRepair_iff_exists_scalarOnKernel]

end ResponseFamily


/-- C0a accepted circuit-locus result: the support of the response cokernel is
exactly the existence locus of a target-containing support-minimal residue-field
dependence. The projectivity premises are split-regularity direction
hypotheses, and the finite circuit extraction is supplied by the reviewed L0
API. The conclusion includes both the singleton loop and nonloop cases. -/
theorem mem_support_responseCokernel_iff_exists_supportMinimalCircuit
    (response : L → Module.Dual R E) (P : Finset L) (target : L)
    (htarget : target ∉ P)
    [Module.Projective R (protectedResponseMap response P).range]
    [Module.Projective R ((P → R) ⧸ (protectedResponseMap response P).range)]
    (p : PrimeSpectrum R) :
    p ∈ Module.support R
        (R ⧸ LinearMap.range (targetOnProtectedKernel response P target)) ↔
      ∃ C : Set L,
        LinearRepair.IsSupportMinimalDependence
          (K := p.asIdeal.ResidueField)
          (fiberResponse p.asIdeal.ResidueField response) C ∧
        target ∈ C ∧ C ⊆ insert target (P : Set L) := by
  rw [mem_support_responseCokernel_iff_no_fiber_normalizedRepair]
  change (¬ ∃ repair,
      LinearRepair.IsNormalizedRepair
        (fiberResponse p.asIdeal.ResidueField response) P target repair) ↔ _
  rw [LinearRepair.not_exists_normalizedRepair_iff_mem_protectedResponseSpan,
    LinearRepair.protectedResponseSpan_eq_protectedSpan]
  exact LinearRepair.mem_protectedSpan_iff_exists_supportMinimalDependence
    (fiberResponse p.asIdeal.ResidueField response) (P : Set L)
    P.finite_toSet target (by simpa using htarget)

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.CircuitLocus

end CircuitLocus
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface
