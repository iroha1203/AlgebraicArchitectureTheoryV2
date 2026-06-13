import Formal.AG.Cohomology.FiniteExamples

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

/--
IV.R11 / 定義13.1: finite Čech chain complex selected for period pairing.

The boundary map is supplied together with `boundary ∘ boundary = 0`.  This is
the chain-side companion to the selected cover-relative Čech cochain complex;
it does not construct singular chains or a general homology theory.
-/
structure FiniteCechChainComplex where
  Chain : Nat -> Type u
  chainAddCommGroup : ∀ n : Nat, AddCommGroup (Chain n)
  boundary : ∀ n : Nat, Chain (n + 1) →+ Chain n
  boundary_comp :
    ∀ (n : Nat) (γ : Chain (n + 2)), boundary n (boundary (n + 1) γ) = 0

attribute [instance] FiniteCechChainComplex.chainAddCommGroup

namespace FiniteCechChainComplex

/-- IV.R11 / 定義13.1: readable notation for the selected boundary. -/
def boundaryOp (C : FiniteCechChainComplex.{u}) (n : Nat) : C.Chain (n + 1) →+ C.Chain n :=
  C.boundary n

/-- IV.R11 / 定義13.1: the selected boundary squares to zero. -/
theorem boundary_comp_zero (C : FiniteCechChainComplex.{u})
    (n : Nat) (γ : C.Chain (n + 2)) :
    C.boundaryOp n (C.boundaryOp (n + 1) γ) = 0 :=
  C.boundary_comp n γ

end FiniteCechChainComplex

/--
IV.R11 / 定義13.1: cochain-chain pairing for a selected Čech model.

The pairing target `Period` is explicit.  In finite models this may be a field,
a coefficient group, or a selected accounting group.
-/
structure CechCochainChainPairing {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) (C : FiniteCechChainComplex.{u}) where
  Period : Type u
  periodAddCommGroup : AddCommGroup Period
  pairing : ∀ n : Nat, K.Cn n -> C.Chain n -> Period

attribute [instance] CechCochainChainPairing.periodAddCommGroup

namespace CechCochainChainPairing

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {C : FiniteCechChainComplex.{u}}

/-- IV.R11 / 定義13.1: notation for `<omega, gamma>`. -/
def pair (P : CechCochainChainPairing K C)
    (n : Nat) (ω : K.Cn n) (γ : C.Chain n) : P.Period :=
  P.pairing n ω γ

end CechCochainChainPairing

/--
IV.R11 / 定理13.2 hypothesis: Stokes compatibility for the selected pairing.

The condition says that the selected Čech differential and selected chain
boundary are adjoint under the pairing.
-/
structure StokesCompatiblePairing {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {K : CoverRelativeCechComplex 𝒰 Ob} {C : FiniteCechChainComplex.{u}}
    (P : CechCochainChainPairing K C) where
  stokes :
    ∀ (n : Nat) (ω : K.Cn n) (γ : C.Chain (n + 1)),
      P.pair (n + 1) (K.d n ω) γ =
        P.pair n ω (C.boundaryOp n γ)

namespace StokesCompatiblePairing

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {C : FiniteCechChainComplex.{u}}
variable {P : CechCochainChainPairing K C}

/-- IV.定理13.2: finite Čech Stokes formula. -/
theorem cechStokes (H : StokesCompatiblePairing P)
    (n : Nat) (ω : K.Cn n) (γ : C.Chain (n + 1)) :
    P.pair (n + 1) (K.d n ω) γ =
      P.pair n ω (C.boundaryOp n γ) :=
  H.stokes n ω γ

end StokesCompatiblePairing

/--
IV.R11 / 定理13.2 connecting-boundary representative data.

When the selected connecting cochain `delta(b)` is represented by a coboundary
compatible with `b`, this package records the exact pairing identity needed for
the period formula.  It is assumption-explicit and does not assert that every
connecting homomorphism is constructed this way.
-/
structure ConnectingBoundaryRepresentative {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {K : CoverRelativeCechComplex 𝒰 Ob} {C : FiniteCechChainComplex.{u}}
    (P : CechCochainChainPairing K C) where
  BoundarySection : Type u
  boundarySectionAddCommGroup : AddCommGroup BoundarySection
  boundaryPairing : BoundarySection -> C.Chain 0 -> P.Period
  deltaRepresentative : BoundarySection -> K.Cn 1
  boundaryPairing_compatible :
    ∀ (b : BoundarySection) (γ : C.Chain 1),
      P.pair 1 (deltaRepresentative b) γ =
        boundaryPairing b (C.boundaryOp 0 γ)

attribute [instance] ConnectingBoundaryRepresentative.boundarySectionAddCommGroup

namespace ConnectingBoundaryRepresentative

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {C : FiniteCechChainComplex.{u}}
variable {P : CechCochainChainPairing K C}

/-- IV.定理13.2: connecting representative period formula. -/
theorem connectingStokes
    (R : ConnectingBoundaryRepresentative P)
    (b : R.BoundarySection) (γ : C.Chain 1) :
    P.pair 1 (R.deltaRepresentative b) γ =
      R.boundaryPairing b (C.boundaryOp 0 γ) :=
  R.boundaryPairing_compatible b γ

end ConnectingBoundaryRepresentative

/--
IV.定義13.4: extension holonomy accounting convention.

This is a bookkeeping convention whose defining property is additivity of
`kappa_U`.  It is not a corollary of Theorem 13.2 by itself: a model must select
the accounting carrier, the extension event type, and the additive `kappa_U`
map separately.
-/
structure ExtensionHolonomyAccounting where
  ExtensionEvent : Type u
  Accounting : Type u
  eventAddCommGroup : AddCommGroup ExtensionEvent
  accountingAddCommGroup : AddCommGroup Accounting
  kappa_U : ExtensionEvent →+ Accounting

attribute [instance] ExtensionHolonomyAccounting.eventAddCommGroup
attribute [instance] ExtensionHolonomyAccounting.accountingAddCommGroup

namespace ExtensionHolonomyAccounting

/-- IV.定義13.4: additivity is the defining property of `kappa_U`. -/
theorem kappa_U_additive (A : ExtensionHolonomyAccounting.{u})
    (x y : A.ExtensionEvent) :
    A.kappa_U (x + y) = A.kappa_U x + A.kappa_U y :=
  map_add A.kappa_U x y

/-- IV.定義13.4: zero accounting follows from the selected additive map. -/
theorem kappa_U_zero (A : ExtensionHolonomyAccounting.{u}) :
    A.kappa_U 0 = 0 :=
  map_zero A.kappa_U

end ExtensionHolonomyAccounting

end Cohomology
end AAT.AG
