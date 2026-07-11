import ResearchLean.AG.SFT.ConwayGlobalCommonRefinementComparison

/-!
Cycle 11 evidence for `G-sft-conway-01`.

Cycle 7 showed that unconstrained local owner-potential absorption is too weak.
Cycle 10 compared global zero-cochains with common-refinement provenance.  This
file records their finite separation: the canonical mismatched fork is absorbed
by a local owner-potential boundary but is still detected by the combined
global/common-refinement receiver.

This is a negative comparison theorem.  It does not introduce a new receiver;
it fixes the exact point where local additive exactness fails to imply global
compatibility plus common-refinement provenance.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Local absorption versus global/common-refinement compatibility -/

/--
Local owner-potential absorption does not imply combined
global/common-refinement vanishing: the canonical mismatched fork is the finite
counterexample.
-/
theorem localOwnerPotential_absorbs_but_globalCommonRefinement_detects :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork /\
      Not
        (SupportForkDefectVanishesModuloGlobalCommonRefinement
          mismatchedSupportFork) :=
  ⟨mismatchedSupportFork_ownerPotentialBoundaryVanishes,
    mismatchedSupportFork_notGlobalCommonRefinementVanishes⟩

/--
The same finite fork separates local owner-potential absorption from
common-refinement constrained owner-potential vanishing.
-/
theorem localOwnerPotential_absorbs_but_commonRefinementOwnerPotential_detects :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork /\
      Not
        (SupportForkDefectVanishesModuloCommonRefinementOwnerPotential
          mismatchedSupportFork) :=
  ⟨mismatchedSupportFork_ownerPotentialBoundaryVanishes,
    mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes⟩

/--
The mismatch is detected by both the support-constrained and global/common
refinement receivers even though local owner-potential absorption succeeds.
-/
theorem mismatchedLocalPotential_separatedBySupportAndGlobalCommonReceivers :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork /\
      SupportConstrainedOwnerPotentialReceiver mismatchedAtlas /\
      CommonRefinementOwnerPotentialReceiver mismatchedAtlas /\
      GlobalCommonRefinementReceiver mismatchedAtlas :=
  ⟨mismatchedSupportFork_ownerPotentialBoundaryVanishes,
    mismatchedAtlas_supportConstrainedOwnerPotentialReceiver,
    mismatchedAtlas_commonRefinementOwnerPotentialReceiver,
    mismatchedAtlas_globalCommonRefinementReceiver⟩

/--
Compatibility collapses the separation: the compatible finite atlas has no
combined global/common-refinement receiver and no common-refinement
owner-potential receiver.
-/
theorem compatibleAtlas_noLocalGlobalCommonSeparationReceivers :
    Not (GlobalCommonRefinementReceiver compatibleAtlas) /\
      Not (CommonRefinementOwnerPotentialReceiver compatibleAtlas) /\
      Not (SupportConstrainedOwnerPotentialReceiver compatibleAtlas) :=
  ⟨compatibleAtlas_zeroGlobalCommonRefinementReceiver,
    compatibleAtlas_zeroCommonRefinementOwnerPotentialReceiver,
    compatibleAtlas_zeroSupportConstrainedOwnerPotentialReceiver⟩

/--
The selected Cycle 11 package: local additive owner-potential exactness can
absorb the canonical finite mismatch, while the support/common/global
refinement constraints still detect it.
-/
theorem selectedLocalVsGlobalCommonRefinementPackage :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary
      mismatchedSupportFork /\
      Not
        (SupportForkDefectVanishesModuloGlobalCommonRefinement
          mismatchedSupportFork) /\
      Not
        (SupportForkDefectVanishesModuloCommonRefinementOwnerPotential
          mismatchedSupportFork) /\
      GlobalCommonRefinementReceiver mismatchedAtlas /\
      CommonRefinementOwnerPotentialReceiver mismatchedAtlas /\
      Not (GlobalCommonRefinementReceiver compatibleAtlas) := by
  exact
    ⟨mismatchedSupportFork_ownerPotentialBoundaryVanishes,
      mismatchedSupportFork_notGlobalCommonRefinementVanishes,
      mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes,
      mismatchedAtlas_globalCommonRefinementReceiver,
      mismatchedAtlas_commonRefinementOwnerPotentialReceiver,
      compatibleAtlas_zeroGlobalCommonRefinementReceiver⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
