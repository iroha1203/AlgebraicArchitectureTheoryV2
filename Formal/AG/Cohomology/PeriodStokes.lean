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

/-! ### Concrete finite basis calculation for theorem 13.2 -/

namespace IntervalBasisStokes

/--
IV-7 / 定理13.2: the two vertices of the selected one-simplex basis model.
-/
inductive Vertex where
  | left
  | right
deriving DecidableEq, Fintype

/--
IV-7 / 定理13.2: the single oriented edge of the selected one-simplex basis
model.
-/
inductive Edge where
  | interval
deriving DecidableEq, Fintype

/-- IV-7 / 定理13.2: concrete cochain groups in degrees 0 and 1. -/
abbrev Cochain : Nat -> Type
  | 0 => Vertex -> Int
  | 1 => Edge -> Int
  | _ + 2 => Int

/-- IV-7 / 定理13.2: concrete chain groups in degrees 0 and 1. -/
abbrev Chain : Nat -> Type
  | 0 => Vertex -> Int
  | 1 => Edge -> Int
  | _ + 2 => Int

/--
IV-7 / 定理13.2: concrete degree-zero Čech coboundary on the one-simplex.

It sends a vertex cochain `ω` to `ω(right) - ω(left)` on the oriented edge.
-/
def d0 : Cochain 0 →+ Cochain 1 where
  toFun ω
    | Edge.interval => ω Vertex.right - ω Vertex.left
  map_zero' := by
    funext e
    cases e
    simp
  map_add' := by
    intro ω η
    funext e
    cases e
    simp [Pi.add_apply]
    abel

/--
IV-7 / 定理13.2: concrete boundary on the oriented one-simplex.

The selected orientation is `left -> right`, so `∂ interval = right - left`.
-/
def boundary0 : Chain 1 →+ Chain 0 where
  toFun γ
    | Vertex.left => -γ Edge.interval
    | Vertex.right => γ Edge.interval
  map_zero' := by
    funext v
    cases v <;> simp
  map_add' := by
    intro γ δ
    funext v
    cases v <;> simp [Pi.add_apply]
    abel

/-- IV-7 / 定理13.2: dot-product pairing in degree 0. -/
def pair0 (ω : Cochain 0) (γ : Chain 0) : Int :=
  ω Vertex.left * γ Vertex.left + ω Vertex.right * γ Vertex.right

/-- IV-7 / 定理13.2: dot-product pairing in degree 1. -/
def pair1 (ω : Cochain 1) (γ : Chain 1) : Int :=
  ω Edge.interval * γ Edge.interval

/--
IV-7 / 定理13.2: basis calculation for finite Čech Stokes on the selected
one-simplex.

No `StokesCompatiblePairing` field is consumed here: both sides reduce to the
same signed basis sum.
-/
theorem finiteIntervalStokes_basis
    (ω : Cochain 0) (γ : Chain 1) :
    pair1 (d0 ω) γ = pair0 ω (boundary0 γ) := by
  simp [pair0, pair1, d0, boundary0]
  ring

/--
IV-7 / 定理13.2: connecting-boundary formula for the same concrete basis
model, read with `delta = d0`.
-/
theorem finiteIntervalConnectingStokes_basis
    (b : Cochain 0) (γ : Chain 1) :
    pair1 (d0 b) γ = pair0 b (boundary0 γ) :=
  finiteIntervalStokes_basis b γ

end IntervalBasisStokes

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
