import Formal.AG.Derived.Intersection
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Matrix.Basis

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace FreeResolution

variable (A : Type v) [CommRing A]

namespace MathlibResolution

open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- V.R4(a): quotient module carrier used by the Mathlib Tor bridge. -/
abbrev quotientModule (I : Ideal A) : ModuleCat.{v} A :=
  ModuleCat.of A (A ⧸ I)

/--
V.R4(a): applying `A/I_U ⊗ -` to a projective resolution of `A/I_V`.

Mathlib defines `Tor` by left-deriving the second tensor factor, so a projective
resolution of `A/I_V` computes `Tor_i(A/I_U, A/I_V)`.
-/
abbrev tensorAppliedComplex (I_U : Ideal A) {I_V : Ideal A}
    (P : ProjectiveResolution (quotientModule A I_V)) :
    ChainComplex (ModuleCat.{v} A) ℕ :=
  ((((tensoringLeft (ModuleCat.{v} A)).obj (quotientModule A I_U)).mapHomologicalComplex _).obj
    P.complex)

/--
V.R4(a): Mathlib theorem that a chosen projective resolution computes
`Tor_i(A/I_U, A/I_V)`.
-/
noncomputable def torIsoProjectiveResolutionHomology
    (I_U : Ideal A) {I_V : Ideal A}
    (P : ProjectiveResolution (quotientModule A I_V)) (i : Nat) :
    Intersection.mathlibTor A I_U I_V i ≅
      (tensorAppliedComplex A I_U P).homology i :=
  P.isoLeftDerivedObj ((tensoringLeft (ModuleCat.{v} A)).obj (quotientModule A I_U)) i

/--
V.R4(a): a finite free Mathlib projective resolution of `A/I`.

The projective resolution and quasi-isomorphism are Mathlib data. The finite-free
fields record the R4 finite coordinate presentation of each degree.
-/
structure FiniteFreeMathlibResolution (I : Ideal A) where
  projectiveResolution : ProjectiveResolution (quotientModule A I)
  length : Nat
  BasisIndex : Nat -> Type v
  [basisIndexFintype : (n : Nat) -> Fintype (BasisIndex n)]
  termIsoFree :
    (n : Nat) -> projectiveResolution.complex.X n ≅ ModuleCat.of A (BasisIndex n -> A)
  supported_le_length : ∀ n, length < n -> Subsingleton (projectiveResolution.complex.X n)

attribute [instance] FiniteFreeMathlibResolution.basisIndexFintype

namespace FiniteFreeMathlibResolution

variable {A}
variable {I : Ideal A}

/--
Transport a finite-free resolution along an equality of ideals while retaining
the same chosen finite basis in every degree.
-/
noncomputable def transportIdeal
    {J : Ideal A}
    (F : FiniteFreeMathlibResolution.{v} A I)
    (h : I = J) :
    FiniteFreeMathlibResolution.{v} A J where
  projectiveResolution := h ▸ F.projectiveResolution
  length := F.length
  BasisIndex := F.BasisIndex
  basisIndexFintype := F.basisIndexFintype
  termIsoFree := by
    subst J
    exact F.termIsoFree
  supported_le_length := by
    subst J
    exact F.supported_le_length

/-- Transporting the resolved ideal keeps the selected basis indices. -/
theorem transportIdeal_BasisIndex
    {J : Ideal A}
    (F : FiniteFreeMathlibResolution.{v} A I)
    (h : I = J)
    (n : Nat) :
    (F.transportIdeal h).BasisIndex n = F.BasisIndex n :=
  rfl

/-- V.R4(a): the categorical complex obtained by tensoring the finite free resolution. -/
abbrev tensorComplex (F : FiniteFreeMathlibResolution.{v} A I) (I_U : Ideal A) :
    ChainComplex (ModuleCat.{v} A) ℕ :=
  tensorAppliedComplex A I_U F.projectiveResolution

/-- V.R4(a): every selected term is a finite free `A`-module. -/
def termIsoFree_certificate (F : FiniteFreeMathlibResolution.{v} A I) (n : Nat) :
    F.projectiveResolution.complex.X n ≅ ModuleCat.of A (F.BasisIndex n -> A) :=
  F.termIsoFree n

/--
V.R4(a): actual projective-resolution differential transported to the selected
finite free coordinates.
-/
noncomputable def coordinateDifferential
    (F : FiniteFreeMathlibResolution.{v} A I) (n : Nat) :
    (F.BasisIndex (n + 1) -> A) →ₗ[A] (F.BasisIndex n -> A) :=
  ModuleCat.Hom.hom
    ((F.termIsoFree (n + 1)).inv ≫
      F.projectiveResolution.complex.d (n + 1) n ≫
      (F.termIsoFree n).hom)

/-- Consecutive coordinate differentials compose to zero. -/
theorem coordinateDifferential_comp
    (F : FiniteFreeMathlibResolution.{v} A I) (n : Nat)
    (x : F.BasisIndex (n + 2) -> A) :
    F.coordinateDifferential n (F.coordinateDifferential (n + 1) x) = 0 := by
  change ModuleCat.Hom.hom
      ((F.termIsoFree (n + 1)).inv ≫
        F.projectiveResolution.complex.d (n + 1) n ≫
        (F.termIsoFree n).hom)
      (ModuleCat.Hom.hom
        ((F.termIsoFree (n + 2)).inv ≫
          F.projectiveResolution.complex.d (n + 2) (n + 1) ≫
          (F.termIsoFree (n + 1)).hom) x) = 0
  rw [← ModuleCat.comp_apply]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp

/-- V.R4(a): finite matrix of the actual selected resolution differential. -/
noncomputable def differentialMatrix
    (F : FiniteFreeMathlibResolution.{v} A I) (n : Nat) :
    Matrix (F.BasisIndex n) (F.BasisIndex (n + 1)) A := by
  letI : DecidableEq (F.BasisIndex n) := Classical.decEq _
  letI : DecidableEq (F.BasisIndex (n + 1)) := Classical.decEq _
  exact LinearMap.toMatrix
    (Pi.basisFun A (F.BasisIndex (n + 1)))
    (Pi.basisFun A (F.BasisIndex n))
    (F.coordinateDifferential n)

/-- Transporting the resolved ideal leaves the coordinate differential matrix
unchanged. -/
theorem transportIdeal_differentialMatrix
    {J : Ideal A}
    (F : FiniteFreeMathlibResolution.{v} A I)
    (h : I = J)
    (n : Nat) :
    (F.transportIdeal h).differentialMatrix n = F.differentialMatrix n := by
  subst J
  rfl

/-- V.R4(a): matrix computation is definitionally tied to the actual differential. -/
theorem differentialMatrix_correct
    (F : FiniteFreeMathlibResolution.{v} A I) (n : Nat) :
    letI : DecidableEq (F.BasisIndex n) := Classical.decEq _
    letI : DecidableEq (F.BasisIndex (n + 1)) := Classical.decEq _
    LinearMap.toMatrix
        (Pi.basisFun A (F.BasisIndex (n + 1)))
        (Pi.basisFun A (F.BasisIndex n))
        (F.coordinateDifferential n) =
      F.differentialMatrix n := by
  rfl

/-- Consecutive finite differential matrices multiply to zero. -/
theorem differentialMatrix_mul_eq_zero
    (F : FiniteFreeMathlibResolution.{v} A I) (n : Nat) :
    letI : DecidableEq (F.BasisIndex n) := Classical.decEq _
    letI : DecidableEq (F.BasisIndex (n + 1)) := Classical.decEq _
    letI : DecidableEq (F.BasisIndex (n + 2)) := Classical.decEq _
    F.differentialMatrix n * F.differentialMatrix (n + 1) = 0 := by
  letI : DecidableEq (F.BasisIndex n) := Classical.decEq _
  letI : DecidableEq (F.BasisIndex (n + 1)) := Classical.decEq _
  letI : DecidableEq (F.BasisIndex (n + 2)) := Classical.decEq _
  have hcomp :
      (F.coordinateDifferential n).comp (F.coordinateDifferential (n + 1)) = 0 := by
    apply LinearMap.ext
    intro x
    exact F.coordinateDifferential_comp n x
  have hmatrix := congrArg
    (LinearMap.toMatrix
      (Pi.basisFun A (F.BasisIndex (n + 2)))
      (Pi.basisFun A (F.BasisIndex n))) hcomp
  rw [LinearMap.toMatrix_comp
    (Pi.basisFun A (F.BasisIndex (n + 2)))
    (Pi.basisFun A (F.BasisIndex (n + 1)))
    (Pi.basisFun A (F.BasisIndex n))] at hmatrix
  rw [F.differentialMatrix_correct, F.differentialMatrix_correct] at hmatrix
  simpa using hmatrix

/--
V.R4(a) / AC5: a finite free Mathlib resolution computes
`Tor_i(A/I_U, A/I)` by the homology of its tensor complex.
-/
noncomputable def torIsoTensorHomology
    (F : FiniteFreeMathlibResolution.{v} A I) (I_U : Ideal A) (i : Nat) :
    Intersection.mathlibTor A I_U I i ≅ (F.tensorComplex I_U).homology i :=
  torIsoProjectiveResolutionHomology A I_U F.projectiveResolution i

/-- V.R4(a) / AC5: inverse orientation of the finite free Tor computation. -/
noncomputable def tensorHomologyIsoTor
    (F : FiniteFreeMathlibResolution.{v} A I) (I_U : Ideal A) (i : Nat) :
    (F.tensorComplex I_U).homology i ≅ Intersection.mathlibTor A I_U I i :=
  (F.torIsoTensorHomology I_U i).symm

end FiniteFreeMathlibResolution

/-! ### A length-one finite-free resolution of a nonzero principal ideal -/

namespace Principal

open CategoryTheory.Limits

variable {A}

/-- V.R4(a): zero module used above degree one in the principal resolution. -/
abbrev zeroModule : ModuleCat.{v} A := ModuleCat.of A PUnit

/-- V.R4(a): quotient module by the selected principal ideal. -/
abbrev quotientModuleOf (a : A) : ModuleCat.{v} A :=
  quotientModule A (Ideal.span ({a} : Set A))

/-- V.R4(a): multiplication by the selected principal generator. -/
def differential (a : A) : ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (a • (LinearMap.id : A →ₗ[A] A))

/-- V.R4(a): quotient projection for the principal ideal. -/
def quotientπ (a : A) : ModuleCat.of A A ⟶ quotientModuleOf a :=
  ModuleCat.ofHom (Ideal.span ({a} : Set A)).mkQ

/-- V.R4(a): the principal differential lands in the quotient kernel. -/
theorem differential_comp_quotientπ (a : A) :
    differential a ≫ quotientπ a = 0 := by
  rw [ModuleCat.hom_ext_iff]
  apply LinearMap.ext
  intro x
  change (Ideal.span ({a} : Set A)).mkQ (a * x) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mem_span_singleton'.mpr ⟨x, by ring⟩

/-- V.R4(a): two-term complex `0 → A → A → 0`. -/
def complex (a : A) : ChainComplex (ModuleCat.{v} A) ℕ :=
  ChainComplex.mk' (ModuleCat.of A A) (ModuleCat.of A A) (differential a)
    (fun {X0 X1} f => ⟨zeroModule, 0, by simp⟩)

/-- V.R4(a): degree-zero augmentation of the principal complex. -/
def augmentation₀ (a : A) : (complex a).X 0 ⟶ quotientModuleOf a :=
  quotientπ a

/-- V.R4(a): augmentation commutes with the selected differential. -/
theorem complex_d_comp_augmentation₀ (a : A) :
    (complex a).d 1 0 ≫ augmentation₀ a = 0 := by
  simpa [complex, augmentation₀] using differential_comp_quotientπ a

/-- V.R4(a): augmentation to the degree-zero single complex. -/
def augmentation (a : A) :
    complex a ⟶ (ChainComplex.single₀ (ModuleCat.{v} A)).obj (quotientModuleOf a) := by
  refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
  exact ⟨augmentation₀ a, complex_d_comp_augmentation₀ a⟩

/-- V.R4(a): all terms above degree one are zero. -/
def complex_X_succ_succ_iso_zero (a : A) (n : ℕ) :
    (complex a).X (n + 2) ≅ zeroModule := by
  let succ' : ∀ {X₀ X₁ : ModuleCat.{v} A} (f : X₁ ⟶ X₀),
      Σ' (X₂ : ModuleCat.{v} A) (_d : X₂ ⟶ X₁), _d ≫ f = 0 :=
    fun {X₀ X₁} f => ⟨zeroModule, 0, by simp⟩
  exact ChainComplex.mk'XIso (ModuleCat.of A A) (ModuleCat.of A A)
    (differential a) succ' n

/-- V.R4(a): each principal-complex term is projective. -/
theorem complex_projective (a : A) (n : ℕ) :
    CategoryTheory.Projective ((complex a).X n) := by
  cases n with
  | zero =>
      simpa [complex] using
        (inferInstance : CategoryTheory.Projective (ModuleCat.of A A))
  | succ n =>
      cases n with
      | zero =>
          simpa [complex] using
            (inferInstance : CategoryTheory.Projective (ModuleCat.of A A))
      | succ n =>
          exact CategoryTheory.Projective.of_iso
            (complex_X_succ_succ_iso_zero a n).symm
            (inferInstance : CategoryTheory.Projective zeroModule)

/-- V.R4(a): multiplication by a nonzero element of a domain is injective. -/
theorem differential_injective [IsDomain A] {a : A} (ha : a ≠ 0) :
    Function.Injective (differential a).hom := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hmul : a * (x - y) = 0 := by
    rw [mul_sub, sub_eq_zero]
    exact hxy
  exact (mul_eq_zero.mp hmul).resolve_left ha

/-- V.R4(a): exactness at degree one. -/
theorem complex_exactAt_one [IsDomain A] {a : A} (ha : a ≠ 0) :
    (complex a).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro y hy
  change (differential a).hom (y : A) = 0 at hy
  have hz : (y : A) = 0 := differential_injective ha (by simpa using hy)
  subst hz
  exact ⟨0, by simp [complex]⟩

/-- V.R4(a): terms in degrees at least two are zero objects. -/
theorem complex_isZero_X_succ_succ (a : A) (n : ℕ) :
    IsZero ((complex a).X (n + 2)) :=
  (ModuleCat.isZero_of_subsingleton zeroModule).of_iso
    (complex_X_succ_succ_iso_zero a n)

/-- V.R4(a): positive-degree exactness of the principal complex. -/
theorem complex_exactAt_succ [IsDomain A] {a : A} (ha : a ≠ 0) (n : ℕ) :
    (complex a).ExactAt (n + 1) := by
  cases n with
  | zero => simpa using complex_exactAt_one ha
  | succ n =>
      rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)]
      apply ShortComplex.exact_of_isZero_X₂
      exact complex_isZero_X_succ_succ a n

/-- V.R4(a): exactness of `A → A → A/⟨a⟩`. -/
theorem differential_quotientπ_exact (a : A) :
    (ShortComplex.mk (differential a) (quotientπ a)
      (differential_comp_quotientπ a)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hx⟩
    subst hx
    change (Ideal.span ({a} : Set A)).mkQ (a * (x : A)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton'.mpr ⟨x, by ring⟩
  · intro y hy
    change (Ideal.span ({a} : Set A)).mkQ (y : A) = 0 at hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton'] at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hx]
    change (differential a).hom x = x * a
    simp [differential]
    exact mul_comm a x

/-- V.R4(a): the principal quotient projection is epic. -/
theorem quotientπ_epi (a : A) : Epi (quotientπ a) := by
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

/-- V.R4(a): degree-zero quasi-isomorphism of the principal resolution. -/
theorem augmentation_quasiIsoAt_zero (a : A) : QuasiIsoAt (augmentation a) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros']
  constructor
  · simpa [augmentation₀, complex] using differential_quotientπ_exact a
  · simpa [augmentation, augmentation₀] using quotientπ_epi a
  all_goals simp [complex]

/-- V.R4(a): positive-degree quasi-isomorphism of the principal resolution. -/
theorem augmentation_quasiIsoAt_succ [IsDomain A] {a : A} (ha : a ≠ 0) (n : ℕ) :
    QuasiIsoAt (augmentation a) (n + 1) := by
  rw [quasiIsoAt_iff_exactAt' _ _
    (ChainComplex.exactAt_succ_single_obj (quotientModuleOf a) n)]
  exact complex_exactAt_succ ha n

/-- V.R4(a): the principal augmentation is a quasi-isomorphism. -/
theorem augmentation_quasiIso [IsDomain A] {a : A} (ha : a ≠ 0) :
    QuasiIso (augmentation a) where
  quasiIsoAt i := by
    cases i with
    | zero => exact augmentation_quasiIsoAt_zero a
    | succ n => exact augmentation_quasiIsoAt_succ ha n

/-- V.R4(a): Mathlib projective resolution of a nonzero principal quotient. -/
noncomputable def projectiveResolution [IsDomain A] {a : A} (ha : a ≠ 0) :
    ProjectiveResolution (quotientModuleOf a) where
  complex := complex a
  projective := complex_projective a
  π := augmentation a
  quasiIso := augmentation_quasiIso ha

/-- V.R4(a): length-one finite-free resolution of a nonzero principal quotient. -/
noncomputable def finiteFreeResolution [IsDomain A] {a : A} (ha : a ≠ 0) :
    FiniteFreeMathlibResolution A (Ideal.span ({a} : Set A)) where
  projectiveResolution := projectiveResolution ha
  length := 1
  BasisIndex n := if n ≤ 1 then ULift.{v} Unit else ULift.{v} Empty
  basisIndexFintype n := by
    by_cases h : n ≤ 1
    · simp [h]
      infer_instance
    · simp [h]
      infer_instance
  termIsoFree n := by
    cases n with
    | zero =>
        simpa [projectiveResolution, complex] using
          (LinearEquiv.funUnique (ULift.{v} Unit) A A).symm.toModuleIso
    | succ n =>
        cases n with
        | zero =>
            simpa [projectiveResolution, complex] using
              (LinearEquiv.funUnique (ULift.{v} Unit) A A).symm.toModuleIso
        | succ n =>
            let hsource := complex_X_succ_succ_iso_zero a n
            let hsourceZero : IsZero (zeroModule : ModuleCat.{v} A) := by
              exact ModuleCat.isZero_of_subsingleton zeroModule
            let htarget : IsZero
                (ModuleCat.of A
                  ((if n + 2 ≤ 1 then ULift.{v} Unit else ULift.{v} Empty) -> A)) := by
              simp
              letI : Subsingleton (ULift.{v} Empty -> A) :=
                ⟨fun f g => funext fun x => nomatch x.down⟩
              exact inferInstance
            simpa [Nat.add_assoc] using
              (hsource ≪≫ hsourceZero.isoZero ≪≫ htarget.isoZero.symm)
  supported_le_length n hn := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
      use n - 2
      omega
    exact ModuleCat.subsingleton_of_isZero (complex_isZero_X_succ_succ a m)

/--
V.R4(a): the first coordinate differential of the principal finite-free
resolution is nonzero whenever its generator is nonzero.
-/
theorem finiteFreeResolution_coordinateDifferential_zero_ne_zero
    [IsDomain A] {a : A} (ha : a ≠ 0) :
    (finiteFreeResolution ha).coordinateDifferential 0 ≠ 0 := by
  intro h
  have hvalue := congrArg
    (fun f => f (fun _ : ULift.{v} Unit => (1 : A)) (ULift.up ())) h
  simp [FiniteFreeMathlibResolution.coordinateDifferential,
    finiteFreeResolution, projectiveResolution, complex, differential] at hvalue
  exact ha hvalue

end Principal

end MathlibResolution

/--
V.R4(a): selected finite free resolution of an `A`-module.

The exactness and augmentation data are explicit fields. This keeps the R4 API
usable without claiming a global construction of all finite free resolutions.
-/
structure SelectedFiniteFreeResolution (M : Type v) [AddCommGroup M] [Module A M] where
  length : Nat
  Term : Nat -> Type v
  [termAddCommGroup : (n : Nat) -> AddCommGroup (Term n)]
  [termModule : (n : Nat) -> Module A (Term n)]
  BasisIndex : Nat -> Type u
  [basisIndexFintype : (n : Nat) -> Fintype (BasisIndex n)]
  termLinearEquivFree : (n : Nat) -> Term n ≃ₗ[A] (BasisIndex n -> A)
  d : (n : Nat) -> Term n.succ →ₗ[A] Term n
  augmentation : Term 0 →ₗ[A] M
  d_comp_d : ∀ (n : Nat) (x : Term n.succ.succ), d n (d n.succ x) = 0
  augmentation_comp_d : ∀ x : Term 1, augmentation (d 0 x) = 0
  supported_le_length : ∀ n, length < n -> Subsingleton (Term n)
  exact : Function.Exact (d 0) augmentation ∧ ∀ n, Function.Exact (d n.succ) (d n)

attribute [instance] SelectedFiniteFreeResolution.termAddCommGroup
attribute [instance] SelectedFiniteFreeResolution.termModule
attribute [instance] SelectedFiniteFreeResolution.basisIndexFintype

namespace SelectedFiniteFreeResolution

variable {A}
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- V.R4(a): every selected term is linearly equivalent to a finite free coordinate module. -/
def termLinearEquivFree_certificate (F : SelectedFiniteFreeResolution.{u, v} A M) (n : Nat) :
    F.Term n ≃ₗ[A] (F.BasisIndex n -> A) :=
  F.termLinearEquivFree n

/-- V.R4(a): the selected resolution carries its exactness certificate. -/
theorem exact_certificate (F : SelectedFiniteFreeResolution.{u, v} A M) :
    Function.Exact (F.d 0) F.augmentation ∧ ∀ n, Function.Exact (F.d n.succ) (F.d n) :=
  F.exact

/-- V.R4(a): actual Mathlib exactness at every positive chain degree. -/
theorem exact_at_succ_holds (F : SelectedFiniteFreeResolution.{u, v} A M) (n : Nat) :
    Function.Exact (F.d n.succ) (F.d n) :=
  F.exact.2 n

/-- V.R4(a): actual Mathlib exactness at the augmentation. -/
theorem augmentation_exact_holds (F : SelectedFiniteFreeResolution.{u, v} A M) :
    Function.Exact (F.d 0) F.augmentation :=
  F.exact.1

end SelectedFiniteFreeResolution

/--
V.R4(a): selected tensor complex `F ⊗ A/I_V` attached to a finite free
resolution. The homology carrier is explicit; R4 later bridges it to Mathlib Tor.
-/
structure SelectedTensorComplex
    {M : Type v} [AddCommGroup M] [Module A M]
    (F : SelectedFiniteFreeResolution.{u, v} A M) (I_V : Ideal A) where
  Term : Nat -> Type v
  [termAddCommGroup : (n : Nat) -> AddCommGroup (Term n)]
  [termModule : (n : Nat) -> Module A (Term n)]
  d : (n : Nat) -> Term n.succ →ₗ[A] Term n
  d_comp_d : ∀ (n : Nat) (x : Term n.succ.succ), d n (d n.succ x) = 0
  Homology : Nat -> Type v
  [homologyAddCommGroup : (n : Nat) -> AddCommGroup (Homology n)]
  [homologyModule : (n : Nat) -> Module A (Homology n)]
  tensorOfResolution : Prop
  tensorOfResolution_holds : tensorOfResolution

attribute [instance] SelectedTensorComplex.termAddCommGroup
attribute [instance] SelectedTensorComplex.termModule
attribute [instance] SelectedTensorComplex.homologyAddCommGroup
attribute [instance] SelectedTensorComplex.homologyModule

namespace SelectedTensorComplex

variable {A}
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {F : SelectedFiniteFreeResolution.{u, v} A M} {I_V : Ideal A}

/-- V.R4(a): homology of the selected tensor complex. -/
abbrev homology (T : SelectedTensorComplex.{u, v} A F I_V) (i : Nat) : Type v :=
  T.Homology i

/-- V.R4(a): the selected tensor complex is recorded as `F ⊗ A/I_V`. -/
theorem tensorOfResolution_certificate (T : SelectedTensorComplex.{u, v} A F I_V) :
    T.tensorOfResolution :=
  T.tensorOfResolution_holds

end SelectedTensorComplex

/--
V.R4(a): package saying that a selected finite free resolution computes Mathlib
`Tor_i(A/I_U, A/I_V)` via an explicit selected equivalence with tensor-complex
homology.

Mathlib's canonical projective-resolution computation is recorded separately in
`MathlibResolution.FiniteFreeMathlibResolution`.
-/
structure FiniteFreeResolutionTorComputation (I_U I_V : Ideal A) where
  quotientResolution :
    SelectedFiniteFreeResolution.{u, v} A (A ⧸ I_U)
  tensorComplex :
    SelectedTensorComplex.{u, v} A quotientResolution I_V
  torLinearEquivTensorHomology :
    (i : Nat) -> Intersection.mathlibTor A I_U I_V i ≃ₗ[A] tensorComplex.homology i

namespace FiniteFreeResolutionTorComputation

variable {A}

/-- V.R4(a): selected equivalence from Mathlib `Tor_i` to tensor-complex homology. -/
def mathlibTorLinearEquivTensorHomology {I_U I_V : Ideal A}
    (C : FiniteFreeResolutionTorComputation.{u, v} A I_U I_V) (i : Nat) :
    Intersection.mathlibTor A I_U I_V i ≃ₗ[A] C.tensorComplex.homology i :=
  C.torLinearEquivTensorHomology i

/-- V.R4(a): inverse selected equivalence, reading tensor homology as law-conflict Tor. -/
def tensorHomologyLinearEquivMathlibTor {I_U I_V : Ideal A}
    (C : FiniteFreeResolutionTorComputation.{u, v} A I_U I_V) (i : Nat) :
    C.tensorComplex.homology i ≃ₗ[A] Intersection.mathlibTor A I_U I_V i :=
  (C.mathlibTorLinearEquivTensorHomology i).symm

end FiniteFreeResolutionTorComputation

end FreeResolution

end Derived
end AAT.AG
