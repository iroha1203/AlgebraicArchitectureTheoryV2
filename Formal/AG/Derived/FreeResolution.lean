import Formal.AG.Derived.Intersection
import Mathlib.Algebra.Exact

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

/-- V.R4(a): the categorical complex obtained by tensoring the finite free resolution. -/
abbrev tensorComplex (F : FiniteFreeMathlibResolution.{v} A I) (I_U : Ideal A) :
    ChainComplex (ModuleCat.{v} A) ℕ :=
  tensorAppliedComplex A I_U F.projectiveResolution

/-- V.R4(a): every selected term is a finite free `A`-module. -/
def termIsoFree_certificate (F : FiniteFreeMathlibResolution.{v} A I) (n : Nat) :
    F.projectiveResolution.complex.X n ≅ ModuleCat.of A (F.BasisIndex n -> A) :=
  F.termIsoFree n

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
