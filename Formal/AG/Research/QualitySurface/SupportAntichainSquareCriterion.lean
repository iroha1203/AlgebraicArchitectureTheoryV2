import Formal.AG.Research.QualitySurface.FiniteSquareCriterion
import Formal.AG.Research.QualitySurface.ProfileCurvature

/-!
Cycle 15 evidence for `G-aat-quality-surface-01`.

This file instantiates the generic finite-square criterion with the
support-antichain / repair-hitting data from the finite profile-curvature
witness. The result is relative to the selected finite square and selected
protected invariant; it does not assert global flatness or complete repair
semantics.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SupportAntichainSquareCriterion

/-! ## Profile-curvature square as a generic finite square -/

abbrev SupportRepairEndpoint :=
  ProfileCurvature.CertificateAt ProfileCurvature.SquareProfile.upperRight

/-- Cycle-3 profile-curvature square as a generic finite square. -/
def profileCurvatureSquare :
    FiniteSquareCriterion.FiniteSquare ProfileCurvature.SquareProfile ProfileCurvature.CertificateAt where
  lowerLeft := ProfileCurvature.SquareProfile.lowerLeft
  lowerRight := ProfileCurvature.SquareProfile.lowerRight
  upperLeft := ProfileCurvature.SquareProfile.upperLeft
  upperRight := ProfileCurvature.SquareProfile.upperRight
  seed := ProfileCurvature.seedAt
  lawBottom := ⟨ProfileCurvature.transportLawBottom.map⟩
  coverRight := ⟨ProfileCurvature.transportCoverRight.map⟩
  coverLeft := ⟨ProfileCurvature.transportCoverLeft.map⟩
  lawTop := ⟨ProfileCurvature.transportLawTop.map⟩

/-- The named endpoint pair of the profile-curvature square. -/
def profileCurvatureEndpointPair :
    FiniteSquareCriterion.EndpointPair SupportRepairEndpoint where
  lawFirst := ProfileCurvature.lawThenCover ProfileCurvature.seedAt
  coverFirst := ProfileCurvature.coverThenLaw ProfileCurvature.seedAt

/-- Generic finite-square endpoints agree with the named profile-curvature paths. -/
theorem profileCurvature_endpointPairOfSquare :
    (FiniteSquareCriterion.endpointPairOfSquare profileCurvatureSquare).lawFirst =
        profileCurvatureEndpointPair.lawFirst ∧
      (FiniteSquareCriterion.endpointPairOfSquare profileCurvatureSquare).coverFirst =
        profileCurvatureEndpointPair.coverFirst :=
  ⟨rfl, rfl⟩

/-! ## Support-antichain / repair-hitting reading -/

/-- Visible reading: scalar projection and verdict only. -/
def SameScalarVerdictSurface
    (left right : SupportRepairEndpoint) : Prop :=
  ProfileCurvature.scalarReading left.val = ProfileCurvature.scalarReading right.val ∧
    ProfileCurvature.verdict left.val = ProfileCurvature.verdict right.val

/-- Same selected support-family antichain. -/
def SameSupportFamilyInvariant
    (left right : SupportRepairEndpoint) : Prop :=
  ProfileCurvature.supportFamily left.val = ProfileCurvature.supportFamily right.val

/-- Same repair hitting requirement. -/
def SameRepairHittingInvariant
    (left right : SupportRepairEndpoint) : Prop :=
  ProfileCurvature.repairHittingNumber left.val = ProfileCurvature.repairHittingNumber right.val

/-- Protected invariant: support family and repair hitting requirement together. -/
def SameSupportRepairInvariant
    (left right : SupportRepairEndpoint) : Prop :=
  SameSupportFamilyInvariant left right ∧
    SameRepairHittingInvariant left right

/-- Square reading that hides support antichain and repair hitting data. -/
def supportRepairSquareReading :
    FiniteSquareCriterion.SquareReading SupportRepairEndpoint where
  VisibleEquivalent := SameScalarVerdictSurface
  SameProtectedInvariant := SameSupportRepairInvariant

/-- The two endpoints agree on the visible scalar/verdict surface. -/
theorem profileCurvature_supportRepair_visibleFlat :
    FiniteSquareCriterion.VisibleFlat
      supportRepairSquareReading profileCurvatureEndpointPair :=
  ⟨ProfileCurvature.same_scalarReading_after_paths,
    ProfileCurvature.same_verdict_after_paths⟩

/-- The law-first endpoint has a nonempty support-family antichain. -/
theorem lawFirst_supportFamily_nonempty_antichain :
    ProfileCurvature.SupportFamilyNonempty
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.lawFirst.val) ∧
      ProfileCurvature.SupportFamilyAntichain
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.lawFirst.val) :=
  ⟨ProfileCurvature.lawThenCover_supportFamily_nonempty,
    ProfileCurvature.lawThenCover_supportFamily_antichain⟩

/-- The cover-first endpoint has a nonempty support-family antichain. -/
theorem coverFirst_supportFamily_nonempty_antichain :
    ProfileCurvature.SupportFamilyNonempty
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.coverFirst.val) ∧
      ProfileCurvature.SupportFamilyAntichain
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.coverFirst.val) :=
  ⟨ProfileCurvature.coverThenLaw_supportFamily_nonempty,
    ProfileCurvature.coverThenLaw_supportFamily_antichain⟩

/-- The two endpoints differ in selected support family. -/
theorem profileCurvature_supportFamily_discrepancy :
    ¬ SameSupportFamilyInvariant
      profileCurvatureEndpointPair.lawFirst
      profileCurvatureEndpointPair.coverFirst :=
  ProfileCurvature.supportFamily_path_ne

/-- The two endpoints differ in repair hitting requirement. -/
theorem profileCurvature_repairHitting_discrepancy :
    ¬ SameRepairHittingInvariant
      profileCurvatureEndpointPair.lawFirst
      profileCurvatureEndpointPair.coverFirst :=
  ProfileCurvature.repairHittingNumber_path_ne

/-- The two endpoints differ in the combined support/repair invariant. -/
theorem profileCurvature_supportRepair_discrepancy :
    ¬ FiniteSquareCriterion.ProtectedInvariantFlat
      supportRepairSquareReading profileCurvatureEndpointPair := by
  intro hsame
  exact profileCurvature_supportFamily_discrepancy hsame.1

/--
Cycle-3 support antichain / repair-hitting witness instantiates the generic
finite-square reading-curvature criterion.
-/
theorem profileCurvature_instantiates_supportAntichainCriterion :
    FiniteSquareCriterion.ReadingCurved
      supportRepairSquareReading profileCurvatureEndpointPair :=
  FiniteSquareCriterion.finiteSquare_curvature_of_visible_agreement_protected_discrepancy
    supportRepairSquareReading profileCurvatureEndpointPair
    profileCurvature_supportRepair_visibleFlat
    profileCurvature_supportRepair_discrepancy

/-- The scalar/verdict visible reading is not faithful to support/repair data. -/
theorem profileCurvature_no_visibleFaithfulness_for_supportRepair :
    ¬ FiniteSquareCriterion.VisibleFaithfulToProtected supportRepairSquareReading :=
  FiniteSquareCriterion.finiteSquare_not_faithful_of_curvature
    supportRepairSquareReading profileCurvatureEndpointPair
    profileCurvature_instantiates_supportAntichainCriterion

/--
The support/repair reading-curvature instance is compatible with the original
cycle-3 `CurvatureCell` predicate.
-/
theorem profileCurvature_readingCurved_implies_curvatureCell
    (hcurved :
      FiniteSquareCriterion.ReadingCurved
        supportRepairSquareReading profileCurvatureEndpointPair) :
    ProfileCurvature.CurvatureCell ProfileCurvature.seedAt := by
  intro hregular
  have hprotected :
      SameSupportRepairInvariant
        profileCurvatureEndpointPair.lawFirst
        profileCurvatureEndpointPair.coverFirst := by
    exact ⟨hregular.2.2.1, hregular.2.2.2⟩
  exact hcurved.2 hprotected

/--
Cycle-15 theorem package: the profile-curvature square is visibly flat for
scalar/verdict, while its support-family antichain and repair hitting
requirement form a protected finite-square curvature instance.
-/
theorem same_scalar_verdict_but_supportAntichainSquare_curved :
    FiniteSquareCriterion.VisibleFlat
        supportRepairSquareReading profileCurvatureEndpointPair ∧
      ProfileCurvature.SupportFamilyNonempty
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.lawFirst.val) ∧
      ProfileCurvature.SupportFamilyAntichain
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.lawFirst.val) ∧
      ProfileCurvature.SupportFamilyNonempty
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.coverFirst.val) ∧
      ProfileCurvature.SupportFamilyAntichain
        (ProfileCurvature.supportFamily profileCurvatureEndpointPair.coverFirst.val) ∧
      ¬ SameSupportFamilyInvariant
        profileCurvatureEndpointPair.lawFirst
        profileCurvatureEndpointPair.coverFirst ∧
      ¬ SameRepairHittingInvariant
        profileCurvatureEndpointPair.lawFirst
        profileCurvatureEndpointPair.coverFirst ∧
      FiniteSquareCriterion.ReadingCurved
        supportRepairSquareReading profileCurvatureEndpointPair ∧
      ProfileCurvature.CurvatureCell ProfileCurvature.seedAt ∧
      ¬ FiniteSquareCriterion.VisibleFaithfulToProtected supportRepairSquareReading := by
  exact ⟨profileCurvature_supportRepair_visibleFlat,
    lawFirst_supportFamily_nonempty_antichain.1,
    lawFirst_supportFamily_nonempty_antichain.2,
    coverFirst_supportFamily_nonempty_antichain.1,
    coverFirst_supportFamily_nonempty_antichain.2,
    profileCurvature_supportFamily_discrepancy,
    profileCurvature_repairHitting_discrepancy,
    profileCurvature_instantiates_supportAntichainCriterion,
    profileCurvature_readingCurved_implies_curvatureCell
      profileCurvature_instantiates_supportAntichainCriterion,
    profileCurvature_no_visibleFaithfulness_for_supportRepair⟩

end SupportAntichainSquareCriterion
end QualitySurface
end Formal.AG.Research
