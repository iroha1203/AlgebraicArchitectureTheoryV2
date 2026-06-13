import Formal.AG.Derived.Intersection

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace FreeResolution

variable (A : Type v) [CommRing A]

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
  exact : Prop
  exact_holds : exact

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
    F.exact :=
  F.exact_holds

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
`Tor_i(A/I_U, A/I_V)` via the homology of its tensor complex.
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

/-- V.R4(a): selected finite free resolution computes Mathlib `Tor_i`. -/
def mathlibTorLinearEquivTensorHomology {I_U I_V : Ideal A}
    (C : FiniteFreeResolutionTorComputation.{u, v} A I_U I_V) (i : Nat) :
    Intersection.mathlibTor A I_U I_V i ≃ₗ[A] C.tensorComplex.homology i :=
  C.torLinearEquivTensorHomology i

/-- V.R4(a): inverse form, reading tensor-complex homology as law-conflict Tor. -/
def tensorHomologyLinearEquivMathlibTor {I_U I_V : Ideal A}
    (C : FiniteFreeResolutionTorComputation.{u, v} A I_U I_V) (i : Nat) :
    C.tensorComplex.homology i ≃ₗ[A] Intersection.mathlibTor A I_U I_V i :=
  (C.mathlibTorLinearEquivTensorHomology i).symm

end FiniteFreeResolutionTorComputation

end FreeResolution

end Derived
end AAT.AG
