import Formal.AG.Derived.Counterexample
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace AAT.AG
namespace Derived

universe u v w

namespace Transfer

/-- V.定義10.1: selected transferred obstruction residue for a repair direction. -/
structure TransferredObstruction where
  Direction : Type u
  TransferResidue : Type v
  direction : Direction
  residue : TransferResidue
  nontrivial : TransferResidue -> Prop

namespace TransferredObstruction

/-- V.定義10.1: the selected transferred residue is nontrivial. -/
def HasNontrivialResidue (T : TransferredObstruction.{u, v}) : Prop :=
  T.nontrivial T.residue

end TransferredObstruction

/--
V.定義10.4: selected repair direction, conflict class, support localization, and
transfer pairing.

The field `supportLocalizedOrJustified` records the boundary that a direction
must be support-localized for the chosen conflict class, or otherwise justified
by the selected coefficient regime. A bare `LawConflict_1 != 0` is not enough to
construct this data.
-/
structure TransferPairingData (A : Type v) [CommRing A]
    {I_U I_V : Ideal A}
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  Direction : Type u
  TransferResidue : Type w
  selectedDirection : Direction
  selectedConflictClass : P.LawConflict 1
  conflictSupport : Type u
  supportLocalized : Direction -> P.LawConflict 1 -> Prop
  pairingJustified : Direction -> P.LawConflict 1 -> Prop
  supportLocalizedOrJustified :
    supportLocalized selectedDirection selectedConflictClass ∨
      pairingJustified selectedDirection selectedConflictClass
  zeroResidue : TransferResidue
  nontrivialResidue : TransferResidue -> Prop
  pairing : Direction -> P.LawConflict 1 -> TransferResidue

namespace TransferPairingData

variable {A : Type v} [CommRing A]
variable {I_U I_V : Ideal A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/-- V.定義10.4: transfer residue of the selected direction. -/
def transferResidue (D : TransferPairingData.{u, v, w} A P) : D.TransferResidue :=
  D.pairing D.selectedDirection D.selectedConflictClass

/-- V.定義10.4: selected direction has a nontrivial transferred residue. -/
def HasNontrivialTransferredResidue
    (D : TransferPairingData.{u, v, w} A P) : Prop :=
  D.nontrivialResidue D.transferResidue

/-- V.定義10.4: the selected direction satisfies the support/pairing boundary. -/
theorem supportLocalized_or_pairingJustified
    (D : TransferPairingData.{u, v, w} A P) :
    D.supportLocalized D.selectedDirection D.selectedConflictClass ∨
      D.pairingJustified D.selectedDirection D.selectedConflictClass :=
  D.supportLocalizedOrJustified

end TransferPairingData

/-- V.定理10.5: hypotheses for pairing-based transfer. -/
structure PairingBasedTransferPackage (A : Type v) [CommRing A]
    {I_U I_V : Ideal A}
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  data : TransferPairingData.{u, v, w} A P
  nontrivial_pairing : data.nontrivialResidue data.transferResidue

namespace PairingBasedTransferPackage

variable {A : Type v} [CommRing A]
variable {I_U I_V : Ideal A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/--
V.定理10.5: nontrivial selected pairing implies a nontrivial transferred
obstruction residue for the selected repair direction.
-/
theorem pairingBasedTransfer
    (B : PairingBasedTransferPackage.{u, v, w} A P) :
    B.data.HasNontrivialTransferredResidue :=
  B.nontrivial_pairing

/--
V.定理10.5 boundary: the transfer theorem carries the support-localized or
pairing-justified hypothesis explicitly; ambient `LawConflict_1 != 0` alone is
not a constructor for arbitrary repair directions.
-/
theorem records_supportLocalized_or_pairingJustified
    (B : PairingBasedTransferPackage.{u, v, w} A P) :
    B.data.supportLocalized B.data.selectedDirection B.data.selectedConflictClass ∨
      B.data.pairingJustified B.data.selectedDirection B.data.selectedConflictClass :=
  B.data.supportLocalized_or_pairingJustified

/-- V.定理10.5: package form of the transferred obstruction residue. -/
def transferredObstruction
    (B : PairingBasedTransferPackage.{u, v, w} A P) :
    TransferredObstruction.{u, w} where
  Direction := B.data.Direction
  TransferResidue := B.data.TransferResidue
  direction := B.data.selectedDirection
  residue := B.data.transferResidue
  nontrivial := B.data.nontrivialResidue

/-- V.定理10.5: the transferred obstruction package is nontrivial. -/
theorem transferredObstruction_nontrivial
    (B : PairingBasedTransferPackage.{u, v, w} A P) :
    B.transferredObstruction.HasNontrivialResidue :=
  B.pairingBasedTransfer

end PairingBasedTransferPackage

/-- V.定理10.6: a subspace is proper when it is not the whole space. -/
def ProperSubspace (k : Type v) [Field k]
    (V : Type u) [AddCommGroup V] [Module k V]
    (S : Submodule k V) : Prop :=
  S ≠ ⊤

/--
V.定理10.6: finite-dimensional selected direction space and the linear map
`tau_kappa(v) = <v, kappa>`.

The bilinear pairing itself is represented after fixing `kappa`, so the theorem
only needs the induced linear map `tauKappa`.
-/
structure GenericTransferPackage (k : Type v) [Field k] where
  Direction : Type u
  [directionAddCommGroup : AddCommGroup Direction]
  [directionModule : Module k Direction]
  [directionFiniteDimensional : FiniteDimensional k Direction]
  TransferResidue : Type w
  [residueAddCommGroup : AddCommGroup TransferResidue]
  [residueModule : Module k TransferResidue]
  tauKappa : Direction →ₗ[k] TransferResidue
  tauKappa_ne_zero : tauKappa ≠ 0

attribute [instance] GenericTransferPackage.directionAddCommGroup
attribute [instance] GenericTransferPackage.directionModule
attribute [instance] GenericTransferPackage.directionFiniteDimensional
attribute [instance] GenericTransferPackage.residueAddCommGroup
attribute [instance] GenericTransferPackage.residueModule

namespace GenericTransferPackage

variable {k : Type v} [Field k]

/-- V.定理10.6: transfer-zero directions are the kernel of `tau_kappa`. -/
def transferZeroDirections (G : GenericTransferPackage.{u, v, w} k) :
    Submodule k G.Direction :=
  LinearMap.ker G.tauKappa

/-- V.定理10.6: the selected map `tau_kappa` is nonzero. -/
theorem tauKappa_nonzero (G : GenericTransferPackage.{u, v, w} k) :
    G.tauKappa ≠ 0 :=
  G.tauKappa_ne_zero

/-- V.定理10.6: nonzero `tau_kappa` makes its kernel a proper subspace. -/
theorem transferZeroDirections_proper
    (G : GenericTransferPackage.{u, v, w} k) :
    ProperSubspace k G.Direction G.transferZeroDirections := by
  intro htop
  apply G.tauKappa_ne_zero
  ext v
  have hv : v ∈ G.transferZeroDirections := by
    rw [htop]
    simp
  exact LinearMap.mem_ker.mp hv

/-- V.定理10.6: directions outside the kernel have nonzero transferred residue. -/
theorem nonzeroTransferredResidue_of_not_mem_kernel
    (G : GenericTransferPackage.{u, v, w} k) {v : G.Direction}
    (hv : v ∉ G.transferZeroDirections) :
    G.tauKappa v ≠ 0 := by
  intro hzero
  exact hv (LinearMap.mem_ker.mpr hzero)

/--
V.定理10.6: transfer-zero directions are contained in the proper subspace
`ker(tau_kappa)`.
-/
theorem transferZeroDirections_contained_in_proper_subspace
    (G : GenericTransferPackage.{u, v, w} k) :
    (∀ v : G.Direction, G.tauKappa v = 0 -> v ∈ G.transferZeroDirections) ∧
      ProperSubspace k G.Direction G.transferZeroDirections :=
  ⟨fun _ h => LinearMap.mem_ker.mpr h, G.transferZeroDirections_proper⟩

end GenericTransferPackage

end Transfer

end Derived
end AAT.AG
