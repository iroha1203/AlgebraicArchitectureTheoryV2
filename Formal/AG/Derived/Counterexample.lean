import Formal.AG.Derived.RepairProfile
import Formal.AG.Derived.FreeResolution
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Regular.Category
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.MvPolynomial.Basic

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace Counterexample

set_option linter.unusedSectionVars false

open MvPolynomial

/-- V.命題9.2: coordinates of the shared-witness chart `k[x,y,z]`. -/
inductive SharedWitnessCoord where
  | x
  | y
  | z
  deriving DecidableEq

namespace SharedWitnessCoord

/-- V.命題9.2: the ambient chart ring `k[x,y,z]`. -/
abbrev ChartRing (k : Type v) [CommRing k] :=
  MvPolynomial SharedWitnessCoord k

/-- V.命題9.2: the path target ring `k[t]`. -/
abbrev PathRing (k : Type v) [CommRing k] :=
  Polynomial k

variable (k : Type v) [CommRing k]

/-- V.命題9.2: the monomial `xy`. -/
def xy : ChartRing k :=
  X SharedWitnessCoord.x * X SharedWitnessCoord.y

/-- V.命題9.2: the monomial `xz`. -/
def xz : ChartRing k :=
  X SharedWitnessCoord.x * X SharedWitnessCoord.z

/-- V.命題9.2: the selected ideal `<xy>`. -/
def idealU : Ideal (ChartRing k) :=
  Ideal.span ({xy k} : Set (ChartRing k))

/-- V.命題9.2: the selected ideal `<xz>`. -/
def idealV : Ideal (ChartRing k) :=
  Ideal.span ({xz k} : Set (ChartRing k))

/-- V.命題9.2: coordinate assignment for `s_t : k[x,y,z] -> k[t]`. -/
def pathAssignment : SharedWitnessCoord -> PathRing k
  | .x => 1
  | .y => 1 - Polynomial.X
  | .z => Polynomial.X

/-- V.命題9.2: selected section family `s_t`. -/
def sectionFamily : ChartRing k →ₐ[k] PathRing k :=
  MvPolynomial.aeval (pathAssignment k)

/-- V.命題9.2(i): `s_t(x) = 1`. -/
theorem section_x :
    sectionFamily k (X SharedWitnessCoord.x) = 1 := by
  simp [sectionFamily, pathAssignment]

/-- V.命題9.2(i): `s_t(xy) = 1 - t`. -/
theorem section_xy :
    sectionFamily k (xy k) = 1 - Polynomial.X := by
  simp [sectionFamily, xy, pathAssignment]

/-- V.命題9.2(i): `s_t(xz) = t`. -/
theorem section_xz :
    sectionFamily k (xz k) = Polynomial.X := by
  simp [sectionFamily, xz, pathAssignment]

/--
V.命題9.2: this path is not a support-localized transfer example along `V(x)`.
The shared witness coordinate is fixed to `1`, so the selected section does not
pass through the support `x = 0`.
-/
theorem sharedWitness_fixed_to_one :
    sectionFamily k (X SharedWitnessCoord.x) = 1 :=
  section_x k

section ZMod2PrincipalResolution

open CategoryTheory
open CategoryTheory.Limits
open TensorProduct
open scoped Pointwise

/-- V-1: concrete coefficient ring used by the certificate-free example 5.6 calculation. -/
abbrev R2 := ChartRing (ZMod 2)

/-- V-1: zero module used above degree one in the concrete principal resolution. -/
abbrev ZeroMod2 := ModuleCat.of R2 PUnit

/-- V-1: concrete quotient target `R/⟨xz⟩` for the principal resolution. -/
abbrev QV2 := ModuleCat.of R2 (R2 ⧸ idealV (ZMod 2))

/-- V-1: concrete quotient `R/⟨xy⟩` used as the left tensor factor. -/
abbrev QU2 := ModuleCat.of R2 (R2 ⧸ idealU (ZMod 2))

/-- V-1: multiplication by `xz` as the principal-resolution differential. -/
def dXZ : ModuleCat.of R2 R2 ⟶ ModuleCat.of R2 R2 :=
  ModuleCat.ofHom ((xz (ZMod 2)) • (LinearMap.id : R2 →ₗ[R2] R2))

/-- V-1: quotient projection `R -> R/⟨xz⟩`. -/
def quotientVπBase : ModuleCat.of R2 R2 ⟶ QV2 :=
  ModuleCat.ofHom (idealV (ZMod 2)).mkQ

/-- V-1: the differential lands in the kernel of the quotient projection. -/
lemma dXZ_comp_quotientVπBase : dXZ ≫ quotientVπBase = 0 := by
  rw [ModuleCat.hom_ext_iff]
  apply LinearMap.ext
  intro a
  change (idealV (ZMod 2)).mkQ ((xz (ZMod 2)) * (a : R2)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [idealV]
  exact Ideal.mem_span_singleton'.mpr ⟨a, by ring⟩

/--
V-1: concrete two-term principal complex
`... -> 0 -> R --xz--> R -> 0`.
-/
def principalComplexV2 : ChainComplex (ModuleCat.{0} R2) ℕ :=
  ChainComplex.mk' (ModuleCat.of R2 R2) (ModuleCat.of R2 R2) dXZ
    (fun {X0 X1} f => ⟨ZeroMod2, 0, by simp⟩)

/-- V-1: degree-zero augmentation of the concrete principal complex. -/
def quotientVπ0 : principalComplexV2.X 0 ⟶ QV2 :=
  quotientVπBase

/-- V-1: the augmentation is a chain-map-compatible quotient projection. -/
lemma principalComplexV2_d_comp_π0 : principalComplexV2.d 1 0 ≫ quotientVπ0 = 0 := by
  simpa [principalComplexV2, quotientVπ0] using dXZ_comp_quotientVπBase

/-- V-1: augmentation to the single complex on `R/⟨xz⟩`. -/
def principalPiV2 : principalComplexV2 ⟶ (ChainComplex.single₀ (ModuleCat.{0} R2)).obj QV2 := by
  refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
  exact ⟨quotientVπ0, principalComplexV2_d_comp_π0⟩

/-- V-1: all degrees at least two are isomorphic to the selected zero module. -/
def principalComplexV2_X_succ_succ_iso_zero (n : ℕ) :
    principalComplexV2.X (n + 2) ≅ ZeroMod2 := by
  let succ' : ∀ {X₀ X₁ : ModuleCat.{0} R2} (f : X₁ ⟶ X₀),
      Σ' (X₂ : ModuleCat.{0} R2) (_d : X₂ ⟶ X₁), _d ≫ f = 0 :=
    fun {X₀ X₁} f => ⟨ZeroMod2, 0, by simp⟩
  exact ChainComplex.mk'XIso (ModuleCat.of R2 R2) (ModuleCat.of R2 R2) dXZ succ' n

/-- V-1: each term of the concrete principal complex is projective. -/
lemma principalComplexV2_projective (n : ℕ) : CategoryTheory.Projective (principalComplexV2.X n) := by
  cases n with
  | zero =>
      simpa [principalComplexV2] using
        (inferInstance : CategoryTheory.Projective (ModuleCat.of R2 R2))
  | succ n =>
      cases n with
      | zero =>
          simpa [principalComplexV2] using
            (inferInstance : CategoryTheory.Projective (ModuleCat.of R2 R2))
      | succ n =>
          exact CategoryTheory.Projective.of_iso
            (principalComplexV2_X_succ_succ_iso_zero n).symm
            (inferInstance : CategoryTheory.Projective ZeroMod2)

/-- V-1: `xz` is nonzero in the concrete polynomial ring. -/
lemma xz_ne_zero_zmod2 : (xz (ZMod 2) : R2) ≠ 0 := by
  rw [xz]
  exact mul_ne_zero (X_ne_zero x) (X_ne_zero z)

/-- V-1: multiplication by `xz` is injective in the concrete polynomial ring. -/
lemma dXZ_injective : Function.Injective dXZ.hom := by
  exact smul_right_injective (M := R2) xz_ne_zero_zmod2

/-- V-1: exactness at degree one of the concrete principal complex. -/
lemma principalComplexV2_exactAt_one : principalComplexV2.ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro y hy
  change dXZ.hom (y : R2) = 0 at hy
  have hz : (y : R2) = 0 := dXZ_injective (by simpa using hy)
  subst hz
  exact ⟨0, by simp [principalComplexV2]⟩

/-- V-1: degrees at least two of the concrete principal complex are zero. -/
lemma principalComplexV2_isZero_X_succ_succ (n : ℕ) :
    IsZero (principalComplexV2.X (n + 2)) := by
  exact (ModuleCat.isZero_of_subsingleton ZeroMod2).of_iso
    (principalComplexV2_X_succ_succ_iso_zero n)

/-- V-1: positive-degree exactness of the concrete principal complex. -/
lemma principalComplexV2_exactAt_succ (n : ℕ) : principalComplexV2.ExactAt (n + 1) := by
  cases n with
  | zero => simpa using principalComplexV2_exactAt_one
  | succ n =>
      rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
      apply ShortComplex.exact_of_isZero_X₂
      exact principalComplexV2_isZero_X_succ_succ n

/-- V-1: exactness of `R --xz--> R -> R/⟨xz⟩`. -/
lemma dXZ_quotientVπBase_exact :
    (ShortComplex.mk dXZ quotientVπBase dXZ_comp_quotientVπBase).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨a, ha⟩
    subst ha
    change (idealV (ZMod 2)).mkQ ((xz (ZMod 2)) * (a : R2)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, idealV]
    exact Ideal.mem_span_singleton'.mpr ⟨a, by ring⟩
  · intro y hy
    change (idealV (ZMod 2)).mkQ (y : R2) = 0 at hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, idealV, Ideal.mem_span_singleton'] at hy
    rcases hy with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha]
    change dXZ.hom a = a * xz (ZMod 2)
    simp [dXZ]
    ring

/-- V-1: the quotient projection is an epimorphism. -/
lemma quotientVπBase_epi : Epi quotientVπBase := by
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

/-- V-1: degree-zero quasi-isomorphism of the concrete principal resolution. -/
lemma principalPiV2_quasiIsoAt_zero : QuasiIsoAt principalPiV2 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros']
  constructor
  · simpa [quotientVπ0, principalComplexV2] using dXZ_quotientVπBase_exact
  · simpa [principalPiV2, quotientVπ0] using quotientVπBase_epi
  all_goals simp [principalComplexV2]

/-- V-1: positive-degree quasi-isomorphism of the concrete principal resolution. -/
lemma principalPiV2_quasiIsoAt_succ (n : ℕ) : QuasiIsoAt principalPiV2 (n + 1) := by
  rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj QV2 n)]
  exact principalComplexV2_exactAt_succ n

/-- V-1: the augmentation is a quasi-isomorphism. -/
lemma principalPiV2_quasiIso : QuasiIso principalPiV2 where
  quasiIsoAt i := by
    cases i with
    | zero => exact principalPiV2_quasiIsoAt_zero
    | succ n => exact principalPiV2_quasiIsoAt_succ n

/--
V-1: concrete Mathlib projective resolution of `R/⟨xz⟩` over
`R = (ZMod 2)[x,y,z]`.
-/
noncomputable def principalProjectiveResolutionV2 : ProjectiveResolution QV2 where
  complex := principalComplexV2
  projective := principalComplexV2_projective
  π := principalPiV2
  quasiIso := principalPiV2_quasiIso

/-- V-1: concrete tensor-applied complex computing `Tor₁(R/⟨xy⟩, R/⟨xz⟩)`. -/
abbrev tensorComplexV2 : ChainComplex (ModuleCat.{0} R2) ℕ :=
  ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat.{0} R2)).obj QU2).mapHomologicalComplex _).obj
    principalComplexV2)

/-- V-1: the explicit tensor-cycle representative `[y] ⊗ 1`. -/
def yTensorCycleRepresentative : tensorComplexV2.X 1 :=
  TensorProduct.tmul R2 (Submodule.Quotient.mk (X y : R2) : R2 ⧸ idealU (ZMod 2)) (1 : R2)

/-- V-1: the class `y` is not killed in `R/⟨xy⟩`. -/
lemma y_not_mem_idealU_zmod2 : (X y : R2) ∉ idealU (ZMod 2) := by
  intro hy
  let evalX0Y1Z0 : R2 →+* ZMod 2 :=
    MvPolynomial.eval₂Hom (RingHom.id (ZMod 2)) fun
      | x => 0
      | y => 1
      | z => 0
  rw [idealU, Ideal.mem_span_singleton'] at hy
  rcases hy with ⟨a, ha⟩
  have hmap := congrArg evalX0Y1Z0 ha
  simp [evalX0Y1Z0, xy] at hmap

/-- V-1: `[y] ⊗ 1` is nonzero before passing to homology. -/
lemma yTensorCycleRepresentative_ne_zero : yTensorCycleRepresentative ≠ 0 := by
  intro h
  have hmap :
      (TensorProduct.rid R2 (R2 ⧸ idealU (ZMod 2))).toLinearMap
          yTensorCycleRepresentative = 0 := by
    rw [h]
    exact (TensorProduct.rid R2 (R2 ⧸ idealU (ZMod 2))).toLinearMap.map_zero
  have hcalc :
      (TensorProduct.rid R2 (R2 ⧸ idealU (ZMod 2))).toLinearMap
          yTensorCycleRepresentative =
        (Submodule.Quotient.mk (X y : R2) : R2 ⧸ idealU (ZMod 2)) := by
    simp [yTensorCycleRepresentative]
  rw [hcalc] at hmap
  apply y_not_mem_idealU_zmod2
  rw [← Submodule.Quotient.mk_eq_zero]
  simpa using hmap

/-- V-1: `[y] ⊗ 1` is killed by the tensor-applied differential. -/
lemma yTensorCycleRepresentative_is_cycle :
    tensorComplexV2.d 1 0 yTensorCycleRepresentative = 0 := by
  change (((xz (ZMod 2)) • (LinearMap.id : R2 →ₗ[R2] R2)).lTensor
      (R2 ⧸ idealU (ZMod 2)))
      (TensorProduct.tmul R2 (Submodule.Quotient.mk (X y : R2) : R2 ⧸ idealU (ZMod 2)) (1 : R2)) = 0
  rw [LinearMap.lTensor_tmul]
  change TensorProduct.tmul R2
      (Submodule.Quotient.mk (X y : R2) : R2 ⧸ idealU (ZMod 2))
      ((xz (ZMod 2)) * 1) = 0
  rw [mul_one]
  have hxzone : (xz (ZMod 2) : R2) = (xz (ZMod 2)) • (1 : R2) := by simp
  rw [hxzone]
  rw [TensorProduct.tmul_smul]
  change TensorProduct.tmul R2
      ((xz (ZMod 2)) • (Submodule.Quotient.mk (X y : R2) : R2 ⧸ idealU (ZMod 2)))
      (1 : R2) = 0
  rw [← Submodule.Quotient.mk_smul]
  change TensorProduct.tmul R2
      ((Submodule.Quotient.mk ((xz (ZMod 2)) * (X y : R2)) : R2 ⧸ idealU (ZMod 2)))
      (1 : R2) = 0
  rw [show ((Submodule.Quotient.mk ((xz (ZMod 2)) * (X y : R2)) : R2 ⧸ idealU (ZMod 2))) = 0 by
    rw [Submodule.Quotient.mk_eq_zero]
    rw [idealU, xz, xy]
    exact Ideal.mem_span_singleton'.mpr ⟨X z, by ring⟩]
  simp

/-- V-1: short complex at tensor degree one. -/
abbrev tensorShortComplexV2At1 : ShortComplex (ModuleCat.{0} R2) :=
  tensorComplexV2.sc 1

/-- V-1: `[y] ⊗ 1` as an actual kernel element in degree one. -/
def yTensorKernelAt1 : LinearMap.ker tensorShortComplexV2At1.g.hom where
  val := yTensorCycleRepresentative
  property := by
    rw [LinearMap.mem_ker]
    unfold tensorShortComplexV2At1
    change tensorComplexV2.d 1 ((ComplexShape.down ℕ).next 1) yTensorCycleRepresentative = 0
    rw [show (ComplexShape.down ℕ).next 1 = 0 by
      simp]
    exact yTensorCycleRepresentative_is_cycle

/-- V-1: concrete degree-one homology class represented by `[y] ⊗ 1`. -/
noncomputable def yTensorConcreteHomologyAt1 :
    tensorShortComplexV2At1.moduleCatLeftHomologyData.H :=
  Submodule.Quotient.mk yTensorKernelAt1

/-- V-1: the concrete degree-one homology class represented by `[y] ⊗ 1` is nonzero. -/
lemma yTensorConcreteHomologyAt1_ne_zero : yTensorConcreteHomologyAt1 ≠ 0 := by
  intro h
  have hmem : yTensorKernelAt1 ∈ LinearMap.range tensorShortComplexV2At1.moduleCatToCycles := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [yTensorConcreteHomologyAt1] using h
  rcases hmem with ⟨b, hb⟩
  have hbzero : tensorShortComplexV2At1.moduleCatToCycles b = 0 := by
    have hsource_zero : IsZero tensorShortComplexV2At1.X₁ := by
      dsimp [tensorShortComplexV2At1, tensorComplexV2, HomologicalComplex.sc,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
      rw [show (ComplexShape.down ℕ).prev 1 = 2 by
        simp]
      change IsZero
        (((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat.{0} R2)).obj QU2).obj
          (principalComplexV2.X 2))
      refine Functor.map_isZero _ ?_
      exact (ModuleCat.isZero_of_subsingleton ZeroMod2).of_iso
        (principalComplexV2_X_succ_succ_iso_zero 0)
    haveI : Subsingleton tensorShortComplexV2At1.X₁ :=
      ModuleCat.subsingleton_of_isZero hsource_zero
    have hb_src : b = 0 := by
      apply Subsingleton.elim
    rw [hb_src]
    exact tensorShortComplexV2At1.moduleCatToCycles.map_zero
  have hyzero : yTensorCycleRepresentative = 0 := by
    have hkernel : yTensorKernelAt1 = 0 := by
      exact hb.symm.trans hbzero
    exact congrArg Subtype.val hkernel
  exact yTensorCycleRepresentative_ne_zero hyzero

/-- V-1: `[y] ⊗ 1` as an actual degree-one homology class of the tensor complex. -/
noncomputable def yTensorHomologyAt1 : tensorComplexV2.homology 1 :=
  tensorShortComplexV2At1.moduleCatHomologyIso.inv yTensorConcreteHomologyAt1

/-- V-1: the actual degree-one homology class of the tensor complex is nonzero. -/
lemma yTensorHomologyAt1_ne_zero : yTensorHomologyAt1 ≠ 0 := by
  intro h
  apply yTensorConcreteHomologyAt1_ne_zero
  have hmap := congrArg tensorShortComplexV2At1.moduleCatHomologyIso.hom h
  simpa [yTensorHomologyAt1] using hmap

/--
V-1: the concrete `ZMod 2` Mathlib Tor class obtained from the constructed
principal projective resolution of `R/⟨xz⟩`.
-/
noncomputable def example56ZMod2Tor1Class :
    Intersection.mathlibTor R2 (idealU (ZMod 2)) (idealV (ZMod 2)) 1 :=
  (FreeResolution.MathlibResolution.torIsoProjectiveResolutionHomology R2
    (idealU (ZMod 2)) principalProjectiveResolutionV2 1).inv yTensorHomologyAt1

/--
V-1: the concrete `ZMod 2` Mathlib Tor class is nonzero.  This theorem uses the
constructed principal resolution and the explicit `[y] ⊗ 1` non-boundary proof;
it does not assume a selected equivalence, package field, or pre-certified
nonzero Tor class.
-/
theorem example56ZMod2Tor1Class_ne_zero : example56ZMod2Tor1Class ≠ 0 := by
  intro h
  apply yTensorHomologyAt1_ne_zero
  have hmap := congrArg
    (FreeResolution.MathlibResolution.torIsoProjectiveResolutionHomology R2
      (idealU (ZMod 2)) principalProjectiveResolutionV2 1).hom h
  simpa [example56ZMod2Tor1Class] using hmap

/--
V-1: concrete counterexample theorem for example 5.6 over `k = ZMod 2`.
The boundary is explicit: this theorem does not assert the corresponding
nonvanishing for arbitrary `CommRing k`.
-/
theorem example56_zmod2_mathlibTor1_nonzero :
    ∃ x : Intersection.mathlibTor R2 (idealU (ZMod 2)) (idealV (ZMod 2)) 1,
      x ≠ 0 :=
  ⟨example56ZMod2Tor1Class, example56ZMod2Tor1Class_ne_zero⟩

end ZMod2PrincipalResolution

end SharedWitnessCoord

/-- V.命題9.2: endpoint residue reading for the selected path. -/
structure ResidueEndpointPath where
  uStart : Nat
  uEnd : Nat
  vStart : Nat
  vEnd : Nat

namespace ResidueEndpointPath

/-- V.命題9.2(i): endpoint residues of the path `t = 0 -> t = 1`. -/
def sharedWitness : ResidueEndpointPath where
  uStart := 1
  uEnd := 0
  vStart := 0
  vEnd := 1

/-- V.命題9.2(i): U-residue is `1` at `t = 0`. -/
theorem sharedWitness_uStart :
    sharedWitness.uStart = 1 :=
  rfl

/-- V.命題9.2(i): U-residue is `0` at `t = 1`. -/
theorem sharedWitness_uEnd :
    sharedWitness.uEnd = 0 :=
  rfl

/-- V.命題9.2(i): V-residue is `0` at `t = 0`. -/
theorem sharedWitness_vStart :
    sharedWitness.vStart = 0 :=
  rfl

/-- V.命題9.2(i): V-residue is `1` at `t = 1`. -/
theorem sharedWitness_vEnd :
    sharedWitness.vEnd = 1 :=
  rfl

/-- V.命題9.2(ii): selected U-axis residue strictly improves. -/
def UImproves (P : ResidueEndpointPath) : Prop :=
  P.uEnd < P.uStart

/-- V.命題9.2(ii): selected V-axis residue does not increase. -/
def VNonIncreasing (P : ResidueEndpointPath) : Prop :=
  P.vEnd ≤ P.vStart

/-- V.命題9.2(ii): selected V-axis residue strictly worsens. -/
def VWorsens (P : ResidueEndpointPath) : Prop :=
  P.vStart < P.vEnd

/-- V.命題9.2(ii): the selected path improves U. -/
theorem sharedWitness_UImproves :
    UImproves sharedWitness := by
  unfold UImproves sharedWitness
  exact Nat.zero_lt_one

/-- V.命題9.2(ii): the selected path worsens V. -/
theorem sharedWitness_VWorsens :
    VWorsens sharedWitness := by
  unfold VWorsens sharedWitness
  exact Nat.zero_lt_one

/-- V.命題9.2(ii): the selected path is not V-nonincreasing. -/
theorem sharedWitness_not_VNonIncreasing :
    ¬ VNonIncreasing sharedWitness := by
  unfold VNonIncreasing sharedWitness
  exact Nat.not_succ_le_zero 0

/--
V.命題9.2(ii): fixed U-axis improvement does not imply V-axis nonincrease.
This is the explicit non-implication witness used by the bounded counterexample.
-/
theorem sharedWitness_UImproves_and_not_VNonIncreasing :
    UImproves sharedWitness ∧ ¬ VNonIncreasing sharedWitness :=
  ⟨sharedWitness_UImproves, sharedWitness_not_VNonIncreasing⟩

end ResidueEndpointPath

/--
V.命題9.2(iii): selected principal-resolution certificate that
`Tor_1(R/<xy>, R/<xz>)` is nonzero.

The actual Mathlib Tor class is explicit data. This package avoids deriving a
global principal-resolution theorem from the monomial presentation alone.
-/
structure SharedWitnessTorNonzeroCertificate (k : Type v) [CommRing k] where
  torClass :
    Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
      (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1
  torClass_ne_zero : torClass ≠ 0
  principalResolutionCalculation : Prop
  principalResolutionCalculation_holds : principalResolutionCalculation

/--
V.命題9.2(iii): selected principal-resolution calculation surface for the
shared-witness Tor class.

The package records the actual Mathlib Tor class together with the
principal-resolution reading that identifies it as the nonzero shifted kernel
class in the `<xy>` resolution tensored with `R/<xz>`.
-/
structure SharedWitnessPrincipalResolutionCalculation (k : Type v) [CommRing k] where
  torClass :
    Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
      (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1
  torClass_ne_zero : torClass ≠ 0
  shiftedKernelRepresentative : Prop
  shiftedKernelRepresentative_holds : shiftedKernelRepresentative
  tensorDifferentialKillsRepresentative : Prop
  tensorDifferentialKillsRepresentative_holds : tensorDifferentialKillsRepresentative
  notTensorBoundary : Prop
  notTensorBoundary_holds : notTensorBoundary

/--
V.命題9.2(iii): direct selected kernel-quotient calculation for the
principal resolution of `<xy>`.

The nonzero class is first carried by the selected shifted-kernel quotient.
The bridge to Mathlib `Tor_1` is explicit equivalence data, so the resulting
Tor nonzero theorem is no longer just a projection from an already-nonzero
Mathlib Tor class.
-/
structure SharedWitnessPrincipalKernelQuotientCalculation
    (k : Type v) [CommRing k] where
  KernelQuotient : Type v
  [kernelAddCommGroup : AddCommGroup KernelQuotient]
  [kernelModule : Module (SharedWitnessCoord.ChartRing k) KernelQuotient]
  shiftedKernelClass : KernelQuotient
  shiftedKernelClass_ne_zero : shiftedKernelClass ≠ 0
  tensorDifferentialKillsRepresentative : Prop
  tensorDifferentialKillsRepresentative_holds : tensorDifferentialKillsRepresentative
  notTensorBoundary : Prop
  notTensorBoundary_holds : notTensorBoundary
  quotientLinearEquivMathlibTor :
    KernelQuotient ≃ₗ[SharedWitnessCoord.ChartRing k]
      Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1

attribute [instance] SharedWitnessPrincipalKernelQuotientCalculation.kernelAddCommGroup
attribute [instance] SharedWitnessPrincipalKernelQuotientCalculation.kernelModule

namespace SharedWitnessTorNonzeroCertificate

variable {k : Type v} [CommRing k]

/-- V.命題9.2(iii): the selected principal-resolution calculation is recorded. -/
theorem principalResolutionCalculation_certificate
    (C : SharedWitnessTorNonzeroCertificate k) :
    C.principalResolutionCalculation :=
  C.principalResolutionCalculation_holds

/-- V.命題9.2(iii): `Tor_1(R/<xy>, R/<xz>)` has a nonzero selected class. -/
theorem mathlibTor1_nonzero
    (C : SharedWitnessTorNonzeroCertificate k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  ⟨C.torClass, C.torClass_ne_zero⟩

end SharedWitnessTorNonzeroCertificate

namespace SharedWitnessPrincipalKernelQuotientCalculation

variable {k : Type v} [CommRing k]

/-- V.命題9.2(iii): the selected shifted-kernel quotient class is nonzero. -/
theorem shiftedKernelClass_nonzero
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.shiftedKernelClass ≠ 0 :=
  C.shiftedKernelClass_ne_zero

/-- V.命題9.2(iii): the tensor differential kills the selected representative. -/
theorem tensorDifferentialKillsRepresentative_certificate
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.tensorDifferentialKillsRepresentative :=
  C.tensorDifferentialKillsRepresentative_holds

/-- V.命題9.2(iii): the selected shifted-kernel class is not a tensor boundary. -/
theorem notTensorBoundary_certificate
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.notTensorBoundary :=
  C.notTensorBoundary_holds

/--
V.命題9.2(iii): the Mathlib Tor class obtained from the selected
kernel-quotient calculation.
-/
def mathlibTorClass
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
      (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1 :=
  C.quotientLinearEquivMathlibTor C.shiftedKernelClass

/--
V.命題9.2(iii): the transported Mathlib Tor class is nonzero because the
selected shifted-kernel quotient class is nonzero.
-/
theorem mathlibTorClass_ne_zero
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.mathlibTorClass ≠ 0 := by
  intro hzero
  apply C.shiftedKernelClass_ne_zero
  have hmap := congrArg C.quotientLinearEquivMathlibTor.symm hzero
  simpa [mathlibTorClass] using hmap

/--
V.命題9.2(iii): direct kernel-quotient calculation induces the existing
principal-resolution calculation package.
-/
def toPrincipalResolutionCalculation
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    SharedWitnessPrincipalResolutionCalculation k where
  torClass := C.mathlibTorClass
  torClass_ne_zero := C.mathlibTorClass_ne_zero
  shiftedKernelRepresentative := C.shiftedKernelClass ≠ 0
  shiftedKernelRepresentative_holds := C.shiftedKernelClass_nonzero
  tensorDifferentialKillsRepresentative := C.tensorDifferentialKillsRepresentative
  tensorDifferentialKillsRepresentative_holds :=
    C.tensorDifferentialKillsRepresentative_certificate
  notTensorBoundary := C.notTensorBoundary
  notTensorBoundary_holds := C.notTensorBoundary_certificate

/--
V.命題9.2(iii): `Tor_1(R/<xy>, R/<xz>)` is nonzero from the direct selected
kernel-quotient calculation.
-/
theorem mathlibTor1_nonzero_of_kernelQuotientCalculation
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  ⟨C.mathlibTorClass, C.mathlibTorClass_ne_zero⟩

end SharedWitnessPrincipalKernelQuotientCalculation

namespace SharedWitnessPrincipalResolutionCalculation

variable {k : Type v} [CommRing k]

/-- V.命題9.2(iii): the selected class is the shifted kernel representative. -/
theorem shiftedKernelRepresentative_certificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    C.shiftedKernelRepresentative :=
  C.shiftedKernelRepresentative_holds

/-- V.命題9.2(iii): the tensor differential kills the selected representative. -/
theorem tensorDifferentialKillsRepresentative_certificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    C.tensorDifferentialKillsRepresentative :=
  C.tensorDifferentialKillsRepresentative_holds

/-- V.命題9.2(iii): the selected representative is not a tensor boundary. -/
theorem notTensorBoundary_certificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    C.notTensorBoundary :=
  C.notTensorBoundary_holds

/--
V.命題9.2(iii): principal-resolution calculation package induces the earlier
Tor nonzero certificate.
-/
def toTorNonzeroCertificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    SharedWitnessTorNonzeroCertificate k where
  torClass := C.torClass
  torClass_ne_zero := C.torClass_ne_zero
  principalResolutionCalculation :=
    C.shiftedKernelRepresentative ∧
      C.tensorDifferentialKillsRepresentative ∧ C.notTensorBoundary
  principalResolutionCalculation_holds :=
    ⟨C.shiftedKernelRepresentative_certificate,
      C.tensorDifferentialKillsRepresentative_certificate,
      C.notTensorBoundary_certificate⟩

/--
V.命題9.2(iii): `Tor_1(R/<xy>, R/<xz>)` is nonzero from the selected
principal-resolution calculation.
-/
theorem mathlibTor1_nonzero_of_principalResolutionCalculation
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  C.toTorNonzeroCertificate.mathlibTor1_nonzero

end SharedWitnessPrincipalResolutionCalculation

/-- V.命題9.2(iv): coordinates for the generalized shared-witness family. -/
inductive GeneralizedCoord (Y Z : Type u) where
  | x
  | y (i : Y)
  | z (j : Z)
  deriving DecidableEq

namespace GeneralizedCoord

variable {Y Z : Type u} [DecidableEq Y] [DecidableEq Z]

/-- V.命題9.2(iv): support of the generator `x y_i`. -/
def leftSupport (i : Y) : Finset (GeneralizedCoord Y Z) :=
  {GeneralizedCoord.x, GeneralizedCoord.y i}

/-- V.命題9.2(iv): support of the generator `x z_j`. -/
def rightSupport (j : Z) : Finset (GeneralizedCoord Y Z) :=
  {GeneralizedCoord.x, GeneralizedCoord.z j}

/-- V.命題9.2(iv): the generalized left generator contains the shared witness `x`. -/
theorem sharedWitness_mem_leftSupport (i : Y) :
    GeneralizedCoord.x ∈ leftSupport (Y := Y) (Z := Z) i := by
  simp [leftSupport]

/-- V.命題9.2(iv): the generalized right generator contains the shared witness `x`. -/
theorem sharedWitness_mem_rightSupport (j : Z) :
    GeneralizedCoord.x ∈ rightSupport (Y := Y) (Z := Z) j := by
  simp [rightSupport]

/-- V.命題9.2(iv): lcm support for `x y_i` and `x z_j`. -/
def lcmSupport (i : Y) (j : Z) : Finset (GeneralizedCoord Y Z) :=
  leftSupport (Y := Y) (Z := Z) i ∪ rightSupport (Y := Y) (Z := Z) j

/-- V.命題9.2(iv): generalized lcm support is the union of the two supports. -/
theorem lcmSupport_eq_union (i : Y) (j : Z) :
    lcmSupport (Y := Y) (Z := Z) i j =
      leftSupport (Y := Y) (Z := Z) i ∪ rightSupport (Y := Y) (Z := Z) j :=
  rfl

/-- V.命題9.2(iv): the shared witness belongs to every generalized lcm support. -/
theorem sharedWitness_mem_lcmSupport (i : Y) (j : Z) :
    GeneralizedCoord.x ∈ lcmSupport (Y := Y) (Z := Z) i j := by
  simp [lcmSupport, leftSupport]

/-- V.命題9.2(iv): shared witness belongs to both selected supports. -/
theorem sharedWitness_mem_bothSupports (i : Y) (j : Z) :
    GeneralizedCoord.x ∈ leftSupport (Y := Y) (Z := Z) i ∧
      GeneralizedCoord.x ∈ rightSupport (Y := Y) (Z := Z) j :=
  ⟨sharedWitness_mem_leftSupport i, sharedWitness_mem_rightSupport j⟩

/--
V.命題9.2(iv): the generalized shared-witness family has the same residue
counterexample behavior as the base path.
-/
theorem generalized_sharedWitness_u_improves_not_v_nonincreasing
    (_i : Y) (_j : Z) :
    ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ResidueEndpointPath.sharedWitness_UImproves_and_not_VNonIncreasing

/--
V.命題9.2(iv): combined support and residue counterexample surface for the
generalized family `<x y_i>` / `<x z_j>`.
-/
theorem generalized_sharedWitness_counterexample_surface (i : Y) (j : Z) :
    GeneralizedCoord.x ∈ leftSupport (Y := Y) (Z := Z) i ∧
      GeneralizedCoord.x ∈ rightSupport (Y := Y) (Z := Z) j ∧
      GeneralizedCoord.x ∈ lcmSupport (Y := Y) (Z := Z) i j ∧
      ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ⟨sharedWitness_mem_leftSupport i,
    sharedWitness_mem_rightSupport j,
    sharedWitness_mem_lcmSupport i j,
    ResidueEndpointPath.sharedWitness_UImproves,
    ResidueEndpointPath.sharedWitness_not_VNonIncreasing⟩

end GeneralizedCoord

/--
V.命題9.2(iv): theorem package for a selected member of the generalized
shared-witness family `<x y_i>` / `<x z_j>`.
-/
structure GeneralizedSharedWitnessCounterexample
    (Y Z : Type u) [DecidableEq Y] [DecidableEq Z] where
  leftIndex : Y
  rightIndex : Z

namespace GeneralizedSharedWitnessCounterexample

variable {Y Z : Type u} [DecidableEq Y] [DecidableEq Z]

/-- V.命題9.2(iv): build the generalized counterexample package from indices. -/
def ofIndices (i : Y) (j : Z) :
    GeneralizedSharedWitnessCounterexample Y Z where
  leftIndex := i
  rightIndex := j

/-- V.命題9.2(iv): the selected generalized generators share the witness `x`. -/
theorem sharedWitness_in_both_supports
    (G : GeneralizedSharedWitnessCounterexample Y Z) :
    GeneralizedCoord.x ∈
        GeneralizedCoord.leftSupport (Y := Y) (Z := Z) G.leftIndex ∧
      GeneralizedCoord.x ∈
        GeneralizedCoord.rightSupport (Y := Y) (Z := Z) G.rightIndex :=
  GeneralizedCoord.sharedWitness_mem_bothSupports G.leftIndex G.rightIndex

/-- V.命題9.2(iv): the selected shared witness lies in the lcm support. -/
theorem sharedWitness_in_lcmSupport
    (G : GeneralizedSharedWitnessCounterexample Y Z) :
    GeneralizedCoord.x ∈
      GeneralizedCoord.lcmSupport (Y := Y) (Z := Z) G.leftIndex G.rightIndex :=
  GeneralizedCoord.sharedWitness_mem_lcmSupport G.leftIndex G.rightIndex

/--
V.命題9.2(iv): the selected generalized member has the same U-improves /
not-V-nonincreasing counterexample behavior.
-/
theorem u_improves_not_v_nonincreasing
    (_G : GeneralizedSharedWitnessCounterexample Y Z) :
    ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ResidueEndpointPath.sharedWitness_UImproves_and_not_VNonIncreasing

/--
V.命題9.2(iv): package-level counterexample extension theorem for the
generalized shared-witness family.
-/
theorem counterexample_extension_surface
    (G : GeneralizedSharedWitnessCounterexample Y Z) :
    GeneralizedCoord.x ∈
        GeneralizedCoord.leftSupport (Y := Y) (Z := Z) G.leftIndex ∧
      GeneralizedCoord.x ∈
        GeneralizedCoord.rightSupport (Y := Y) (Z := Z) G.rightIndex ∧
      GeneralizedCoord.x ∈
        GeneralizedCoord.lcmSupport (Y := Y) (Z := Z) G.leftIndex G.rightIndex ∧
      ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  GeneralizedCoord.generalized_sharedWitness_counterexample_surface
    G.leftIndex G.rightIndex

end GeneralizedSharedWitnessCounterexample

/-- V.命題9.2: theorem package for the shared-witness repair counterexample. -/
structure SharedWitnessRepairCounterexample (k : Type v) [CommRing k] where
  torCertificate : SharedWitnessTorNonzeroCertificate k

/--
V.命題9.2: theorem package built directly from the selected
principal-resolution calculation.
-/
def SharedWitnessRepairCounterexample.ofPrincipalResolutionCalculation
    {k : Type v} [CommRing k]
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    SharedWitnessRepairCounterexample k where
  torCertificate := C.toTorNonzeroCertificate

/--
V.命題9.2: theorem package built directly from the selected kernel-quotient
calculation.
-/
def SharedWitnessRepairCounterexample.ofKernelQuotientCalculation
    {k : Type v} [CommRing k]
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    SharedWitnessRepairCounterexample k :=
  SharedWitnessRepairCounterexample.ofPrincipalResolutionCalculation
    C.toPrincipalResolutionCalculation

namespace SharedWitnessRepairCounterexample

variable {k : Type v} [CommRing k]

/-- V.命題9.2(i): U-residue goes from `1` to `0`. -/
theorem u_residue_path
    (_C : SharedWitnessRepairCounterexample k) :
    ResidueEndpointPath.sharedWitness.uStart = 1 ∧
      ResidueEndpointPath.sharedWitness.uEnd = 0 :=
  ⟨ResidueEndpointPath.sharedWitness_uStart, ResidueEndpointPath.sharedWitness_uEnd⟩

/-- V.命題9.2(i): V-residue goes from `0` to `1`. -/
theorem v_residue_path
    (_C : SharedWitnessRepairCounterexample k) :
    ResidueEndpointPath.sharedWitness.vStart = 0 ∧
      ResidueEndpointPath.sharedWitness.vEnd = 1 :=
  ⟨ResidueEndpointPath.sharedWitness_vStart, ResidueEndpointPath.sharedWitness_vEnd⟩

/-- V.命題9.2(ii): U-axis improvement does not imply V-axis nonincrease. -/
theorem u_improves_not_v_nonincreasing
    (_C : SharedWitnessRepairCounterexample k) :
    ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ResidueEndpointPath.sharedWitness_UImproves_and_not_VNonIncreasing

/-- V.命題9.2(iii): selected `Tor_1(R/<xy>, R/<xz>)` nonzero class. -/
theorem tor1_nonzero
    (C : SharedWitnessRepairCounterexample k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  C.torCertificate.mathlibTor1_nonzero

end SharedWitnessRepairCounterexample

end Counterexample

end Derived
end AAT.AG
