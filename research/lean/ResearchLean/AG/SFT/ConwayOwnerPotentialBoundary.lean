import ResearchLean.AG.SFT.ConwayOwnerChoiceBoundary

/-!
Cycle 7 evidence for `G-sft-conway-01`.

Cycle 6 made the selected boundary evaluation depend on degree-zero owner-choice
data, but its existence-level absorption was still exactly single-owner support.
This file adds a genuinely additive local owner-potential boundary over
`ConwayZ2`.

The important result is deliberately negative: the canonical mismatched fork is
absorbed by a local owner-potential boundary even though the support/global
receivers still detect the Conway mismatch.  Thus an unconstrained additive
owner-potential boundary is too weak by itself; later cycles must add global or
common-refinement constraints rather than treat local additive exactness as the
Conway obstruction.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Local additive owner-potential boundary -/

/-- A selected additive degree-zero owner potential. -/
structure OwnerPotential (atlas : TwoCoverAtlas) where
  value : atlas.OwnerIdx -> ConwayZ2

/--
The local additive boundary of an owner potential on a support fork: the
difference between the right and left owner potentials.
-/
def SupportForkOwnerPotentialBoundary {atlas : TwoCoverAtlas}
    (potential : OwnerPotential atlas)
    (fork : SupportForkOneCochain atlas) : ConwayZ2 :=
  potential.value fork.right.owner - potential.value fork.left.owner

/-- The selected defect is absorbed by some local owner-potential boundary. -/
def SupportForkDefectVanishesModuloOwnerPotentialBoundary
    {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  exists potential : OwnerPotential atlas,
    SupportForkOwnerPotentialBoundary potential fork = SupportForkDefect fork

/-- Endpoint potential difference is exactly the selected absorption condition. -/
theorem ownerPotentialBoundary_absorbs_of_endpointDifference
    {atlas : TwoCoverAtlas}
    (potential : OwnerPotential atlas)
    (fork : SupportForkOneCochain atlas)
    (hboundary :
      potential.value fork.right.owner - potential.value fork.left.owner =
        SupportForkDefect fork) :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary fork :=
  ⟨potential, hboundary⟩

/-! ## Canonical mismatched fork -/

/-- A local owner potential separating the two selected owners in the mismatched fork. -/
def mismatchedOwnerPotential : OwnerPotential mismatchedAtlas where
  value
    | Owner.apiOwner => 0
    | Owner.dbOwner => 1
    | Owner.productOwner => 0

/-- The local owner potential absorbs the canonical mismatched support-fork defect. -/
theorem mismatchedOwnerPotential_boundary_eq_defect :
    SupportForkOwnerPotentialBoundary
      mismatchedOwnerPotential
      mismatchedSupportFork =
        SupportForkDefect mismatchedSupportFork := by
  change (1 : ConwayZ2) - 0 = 1
  simp

/-- The canonical mismatched fork vanishes modulo local owner-potential boundaries. -/
theorem mismatchedSupportFork_ownerPotentialBoundaryVanishes :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork :=
  ownerPotentialBoundary_absorbs_of_endpointDifference
    mismatchedOwnerPotential
    mismatchedSupportFork
    mismatchedOwnerPotential_boundary_eq_defect

/--
Local additive owner-potential exactness is too weak: it absorbs the canonical
mismatched fork even though the owner-choice/support boundary receiver still
detects the mismatch.
-/
theorem localOwnerPotential_absorbs_but_ownerChoiceReceiver_detects :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork /\
      Not
        (SupportForkDefectVanishesModuloOwnerChoiceBoundary
          mismatchedSupportFork) :=
  ⟨mismatchedSupportFork_ownerPotentialBoundaryVanishes,
    mismatchedSupportFork_notOwnerChoiceBoundaryVanishes⟩

/--
Local additive owner-potential exactness is also weaker than the global
zero-cochain boundary condition.
-/
theorem localOwnerPotential_absorbs_but_globalBoundary_detects :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork /\
      Not
        (SupportForkDefectVanishesModuloGlobalBoundary
          mismatchedSupportFork) :=
  ⟨mismatchedSupportFork_ownerPotentialBoundaryVanishes,
    mismatchedSupportFork_notGlobalBoundaryVanishes⟩

/--
The selected Cycle 7 package: a nontrivial local additive owner-potential
boundary can absorb the canonical mismatched defect, so local additive exactness
must be constrained by support/global compatibility before it can serve as a
Conway obstruction receiver.
-/
theorem selectedOwnerPotentialBoundaryPackage :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork /\
      Not
        (SupportForkDefectVanishesModuloOwnerChoiceBoundary
          mismatchedSupportFork) /\
      Not
        (SupportForkDefectVanishesModuloGlobalBoundary
          mismatchedSupportFork) /\
      OwnerChoiceBoundaryReceiver mismatchedAtlas /\
      GlobalBoundaryReceiver mismatchedAtlas := by
  exact
    ⟨mismatchedSupportFork_ownerPotentialBoundaryVanishes,
      mismatchedSupportFork_notOwnerChoiceBoundaryVanishes,
      mismatchedSupportFork_notGlobalBoundaryVanishes,
      mismatchedAtlas_ownerChoiceBoundaryReceiver,
      mismatchedAtlas_globalBoundaryReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
