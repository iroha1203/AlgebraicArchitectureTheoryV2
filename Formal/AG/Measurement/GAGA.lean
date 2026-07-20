import Formal.AG.Cohomology.PeriodStokes
import Formal.AG.Measurement.Packet

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R10 / AC23-AC24 AAT-GAGA finite measurement comparison.

The certified comparison is indexed by one selected finite site, cover,
coefficient, measurement, and common ambient.  Its conclusions are the actual
Hodge, Stokes, finite-nerve, and Tor statements carried by theorem packages.
Candidate-dependent interfaces remain separate data.
-/

/-- VIII.Theorem 12.3: common finite data shared by every certified comparison. -/
structure AATGAGACommonFiniteData (M : MeasurementProfile.{u, v}) where
  /-- The site selected for this comparison. -/
  selectedSite : M.SiteObj
  /-- The finite cover selected for this comparison. -/
  selectedCover : M.Cover
  /-- The coefficient object selected for this comparison. -/
  selectedCoefficient : M.Coeff
  /-- The measurement-domain element selected for this comparison. -/
  selectedMeasurement : M.Domain
  /-- Evidence that the selected measurement belongs to the measured profile. -/
  measuredSelection : M.Measured_M selectedMeasurement
  /-- The common ambient whose two law ideals are read by the Tor package. -/
  commonAmbient : CommonAmbientPair M

/-- VIII.Theorem 12.3: selected finite Hodge package over the common finite data. -/
structure SelectedFiniteHodgeTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  cellularModel : CellularMeasurementModel M
  laplacianReading : SheafLaplacianReading cellularModel
  hodgeData : FiniteHodgeDecompositionData laplacianReading
  hodgePackage : FiniteHodgeDecomposition hodgeData

namespace SelectedFiniteHodgeTheoremPackage

/-- VIII.Theorem 12.3: expose the carried finite Hodge decomposition theorem. -/
theorem decomposition_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (P : SelectedFiniteHodgeTheoremPackage C) :
    P.hodgeData.finiteHodgeDecomposition :=
  P.hodgePackage.decomposition_holds

/-- VIII.Theorem 12.3: expose the carried harmonic-cohomology theorem. -/
theorem harmonic_cohomology_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (P : SelectedFiniteHodgeTheoremPackage C) :
    P.hodgeData.harmonicKernelIdentifiesCohomology :=
  P.hodgePackage.harmonic_cohomology_holds

end SelectedFiniteHodgeTheoremPackage

/-- VIII.Theorem 12.3: selected Period/Stokes package over the common finite data. -/
structure SelectedPeriodStokesTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  extensionAccounting : Cohomology.ExtensionHolonomyAccounting.{v}

namespace SelectedPeriodStokesTheoremPackage

/-- VIII.Theorem 12.3: expose the additive extension-accounting theorem. -/
theorem period_stokes_accounting_additive {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (P : SelectedPeriodStokesTheoremPackage C)
    (x y : P.extensionAccounting.ExtensionEvent) :
    P.extensionAccounting.kappa_U (x + y) =
      P.extensionAccounting.kappa_U x + P.extensionAccounting.kappa_U y :=
  P.extensionAccounting.kappa_U_additive x y

end SelectedPeriodStokesTheoremPackage

/-- VIII.Theorem 12.3: selected topological-capacity package over the common data. -/
structure SelectedTopologicalDebtTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  nerve : Cohomology.CoverNerve.{v}
  nerveComplex : Cohomology.FiniteNerveCochainComplex nerve

namespace SelectedTopologicalDebtTheoremPackage

/-- VIII.Theorem 12.3: expose the finite-nerve capacity theorem. -/
theorem topological_debt_capacity_from_complex {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (P : SelectedTopologicalDebtTheoremPackage C) :
    Module.finrank P.nerveComplex.k P.nerveComplex.C1 <=
      Module.finrank P.nerveComplex.k P.nerveComplex.H1 +
        Module.finrank P.nerveComplex.k P.nerveComplex.C0 +
          Module.finrank P.nerveComplex.k P.nerveComplex.C2 :=
  P.nerveComplex.topologicalDebtCapacity_fromComplex

end SelectedTopologicalDebtTheoremPackage

/-- VIII.Theorem 12.3: selected LawConflict/Tor package over the common data. -/
structure SelectedDerivedConflictTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- The coefficient ring used by the selected Tor computation. -/
  R : Type v
  [commRingR : CommRing R]
  /-- The left ideal read from the common ambient. -/
  leftIdeal : Ideal R
  /-- The right ideal read from the common ambient. -/
  rightIdeal : Ideal R
  /-- Interpretation of common-ambient law ideals in the selected ring. -/
  readLawIdeal : C.commonAmbient.LawIdeal → Ideal R
  leftIdeal_eq : readLawIdeal C.commonAmbient.leftLawIdeal = leftIdeal
  rightIdeal_eq : readLawIdeal C.commonAmbient.rightLawIdeal = rightIdeal
  /-- The selected bridge from LawConflict to mathlib Tor. -/
  torBridge : Derived.Intersection.SelectedTorBridge.{v} R leftIdeal rightIdeal
  /-- The homological degree used by the comparison. -/
  degree : Nat

attribute [instance] SelectedDerivedConflictTheoremPackage.commRingR

namespace SelectedDerivedConflictTheoremPackage

/-- VIII.Theorem 12.3: selected LawConflict object. -/
abbrev lawConflict {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (P : SelectedDerivedConflictTheoremPackage C) : Type v :=
  P.torBridge.LawConflict P.degree

/-- VIII.Theorem 12.3: expose the actual LawConflict/Mathlib Tor equivalence. -/
def lawConflictLinearEquivMathlibTor {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (P : SelectedDerivedConflictTheoremPackage C) :
    P.lawConflict ≃ₗ[P.R]
      Derived.Intersection.mathlibTor P.R P.leftIdeal P.rightIdeal P.degree :=
  P.torBridge.lawConflictLinearEquivMathlibTor P.degree

/-- VIII.Theorem 12.3: the selected LawConflict has an actual Tor reading. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (P : SelectedDerivedConflictTheoremPackage C) :
    Nonempty
      (P.lawConflict ≃ₗ[P.R]
        Derived.Intersection.mathlibTor P.R P.leftIdeal P.rightIdeal P.degree) :=
  ⟨P.lawConflictLinearEquivMathlibTor⟩

end SelectedDerivedConflictTheoremPackage

/-- VIII.Theorem 12.3: theorem packages indexed by one common finite datum. -/
structure AATGAGACertifiedFields {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  finiteHodgeTheoremPackage : SelectedFiniteHodgeTheoremPackage C
  periodStokesTheoremPackage : SelectedPeriodStokesTheoremPackage C
  topologicalDebtTheoremPackage : SelectedTopologicalDebtTheoremPackage C
  derivedConflictTheoremPackage : SelectedDerivedConflictTheoremPackage C

/--
VIII.Theorem 12.3: the certified finite comparison statement.

Every conjunct is the statement of an actual theorem package.  There is no
caller-selected `Prop` or GAGA-local certificate in this definition.
-/
def aatGAGACertifiedComparisonStatement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M}
    (F : AATGAGACertifiedFields C) : Prop :=
  F.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology ∧
    F.finiteHodgeTheoremPackage.hodgeData.finiteHodgeDecomposition ∧
      (∀ (ω : Cohomology.IntervalBasisStokes.Cochain 0)
          (γ : Cohomology.IntervalBasisStokes.Chain 1),
        Cohomology.IntervalBasisStokes.pair1
            (Cohomology.IntervalBasisStokes.d0 ω) γ =
          Cohomology.IntervalBasisStokes.pair0 ω
            (Cohomology.IntervalBasisStokes.boundary0 γ)) ∧
        (∀ x y : F.periodStokesTheoremPackage.extensionAccounting.ExtensionEvent,
          F.periodStokesTheoremPackage.extensionAccounting.kappa_U (x + y) =
            F.periodStokesTheoremPackage.extensionAccounting.kappa_U x +
              F.periodStokesTheoremPackage.extensionAccounting.kappa_U y) ∧
          (Module.finrank F.topologicalDebtTheoremPackage.nerveComplex.k
                F.topologicalDebtTheoremPackage.nerveComplex.C1 <=
            Module.finrank F.topologicalDebtTheoremPackage.nerveComplex.k
                F.topologicalDebtTheoremPackage.nerveComplex.H1 +
              Module.finrank F.topologicalDebtTheoremPackage.nerveComplex.k
                F.topologicalDebtTheoremPackage.nerveComplex.C0 +
                Module.finrank F.topologicalDebtTheoremPackage.nerveComplex.k
                  F.topologicalDebtTheoremPackage.nerveComplex.C2) ∧
            Nonempty
              (F.derivedConflictTheoremPackage.lawConflict ≃ₗ[
                  F.derivedConflictTheoremPackage.R]
                Derived.Intersection.mathlibTor
                  F.derivedConflictTheoremPackage.R
                  F.derivedConflictTheoremPackage.leftIdeal
                  F.derivedConflictTheoremPackage.rightIdeal
                  F.derivedConflictTheoremPackage.degree)

/-- VIII.Theorem 12.3: derive every certified comparison conjunct. -/
theorem aatGAGACertifiedComparisonStatement_holds
    {M : MeasurementProfile.{u, v}} {C : AATGAGACommonFiniteData M}
    (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F := by
  refine ⟨F.finiteHodgeTheoremPackage.harmonic_cohomology_holds,
    F.finiteHodgeTheoremPackage.decomposition_holds, ?_, ?_,
    F.topologicalDebtTheoremPackage.topological_debt_capacity_from_complex,
    F.derivedConflictTheoremPackage.lawConflictTorReading_holds⟩
  · exact Cohomology.IntervalBasisStokes.finiteIntervalStokes_basis
  · exact fun x y =>
      F.periodStokesTheoremPackage.period_stokes_accounting_additive x y

namespace AATGAGACertifiedFields

/-- VIII.Theorem 12.3: expose Hodge/cohomology comparison. -/
theorem hodge_comparison_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    F.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology :=
  F.finiteHodgeTheoremPackage.harmonic_cohomology_holds

/-- VIII.Theorem 12.3: expose harmonic decomposition. -/
theorem harmonic_decomposition_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    F.finiteHodgeTheoremPackage.hodgeData.finiteHodgeDecomposition :=
  F.finiteHodgeTheoremPackage.decomposition_holds

/-- VIII.Theorem 12.3: expose the whole derived certified statement. -/
theorem certified_comparison_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F :=
  aatGAGACertifiedComparisonStatement_holds F

end AATGAGACertifiedFields

/-- VIII.Theorem 12.3: candidate-dependent comparison interfaces. -/
structure AATGAGACandidateInterfaces (M : MeasurementProfile.{u, v}) where
  MonotoneWitnessStabilityInterface : Type v
  FiniteCechStabilityInterface : Type v
  FlatBaseChangeInterface : Type v
  SpectralHotspotInterface : Type v
  TransferLowerBoundInterface : Type v
  monotoneWitnessStability : Option MonotoneWitnessStabilityInterface
  finiteCechStability : Option FiniteCechStabilityInterface
  flatBaseChange : Option FlatBaseChangeInterface
  spectralHotspot : Option SpectralHotspotInterface
  transferLowerBound : Option TransferLowerBoundInterface

/-- VIII.Principle 12.4: non-conclusions for the finite GAGA comparison. -/
structure AATGAGABoundary (M : MeasurementProfile.{u, v}) where
  noExternalDataSourceFidelity : Prop
  noExternalDataSourceFidelity_cert : noExternalDataSourceFidelity
  noExternalProcedureCorrectness : Prop
  noExternalProcedureCorrectness_cert : noExternalProcedureCorrectness
  noArbitraryLawUniverseComparison : Prop
  noArbitraryLawUniverseComparison_cert : noArbitraryLawUniverseComparison
  candidateDependentFieldsNotCertified : Prop
  candidateDependentFieldsNotCertified_cert : candidateDependentFieldsNotCertified

namespace AATGAGABoundary

/-- VIII.Principle 12.4: expose the external-fidelity non-conclusion. -/
theorem noExternalDataSourceFidelity_holds {M : MeasurementProfile.{u, v}}
    (B : AATGAGABoundary M) : B.noExternalDataSourceFidelity :=
  B.noExternalDataSourceFidelity_cert

/-- VIII.Principle 12.4: candidate-dependent fields remain non-conclusions. -/
theorem candidateDependentFieldsNotCertified_holds
    {M : MeasurementProfile.{u, v}} (B : AATGAGABoundary M) :
    B.candidateDependentFieldsNotCertified :=
  B.candidateDependentFieldsNotCertified_cert

end AATGAGABoundary

/-- VIII.Theorem 12.3: data for one common finite AAT-GAGA comparison. -/
structure AATGAGAComparisonData (M : MeasurementProfile.{u, v}) where
  measurementPacketData : MeasurementPacketData M
  /-- Common finite data indexing every certified theorem package. -/
  commonData : AATGAGACommonFiniteData M
  certifiedFields : AATGAGACertifiedFields commonData
  candidateInterfaces : AATGAGACandidateInterfaces M
  boundary : AATGAGABoundary M

/-- VIII.Theorem 12.3: selected finite-profile comparison statement. -/
def aatGAGAComparisonStatement {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGACertifiedComparisonStatement D.certifiedFields

/-- VIII.Theorem 12.3: derive the comparison statement from theorem packages. -/
theorem aatGAGAComparisonStatement_holds {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : aatGAGAComparisonStatement D :=
  aatGAGACertifiedComparisonStatement_holds D.certifiedFields

/-- VIII.Theorem 12.3: finite comparison packet derived from common data. -/
structure AATGAGAComparisonPacket (M : MeasurementProfile.{u, v}) where
  /-- The exact comparison data certified by this packet. -/
  toAATGAGAComparisonData : AATGAGAComparisonData M
  certifiedComparison : aatGAGAComparisonStatement toAATGAGAComparisonData

namespace AATGAGAComparisonPacket

/-- VIII.Theorem 12.3: expose the derived finite-profile comparison. -/
theorem finiteProfileComparison_holds {M : MeasurementProfile.{u, v}}
    (P : AATGAGAComparisonPacket M) :
    aatGAGAComparisonStatement P.toAATGAGAComparisonData :=
  P.certifiedComparison

end AATGAGAComparisonPacket

/-- VIII.Theorem 12.3: construct a packet from common finite data. -/
def aatGAGAComparisonPacketOfData {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : AATGAGAComparisonPacket M where
  toAATGAGAComparisonData := D
  certifiedComparison := aatGAGAComparisonStatement_holds D

/-- VIII.Theorem 12.3: finite measurement comparison theorem package. -/
structure AATGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) where
  packet : AATGAGAComparisonPacket M
  packet_extends_data : packet.toAATGAGAComparisonData = D
  hodge_comparison_holds :
    D.certifiedFields.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology
  harmonic_decomposition_holds :
    D.certifiedFields.finiteHodgeTheoremPackage.hodgeData.finiteHodgeDecomposition
  period_stokes_holds :
    ∀ (ω : Cohomology.IntervalBasisStokes.Cochain 0)
        (γ : Cohomology.IntervalBasisStokes.Chain 1),
      Cohomology.IntervalBasisStokes.pair1
          (Cohomology.IntervalBasisStokes.d0 ω) γ =
        Cohomology.IntervalBasisStokes.pair0 ω
          (Cohomology.IntervalBasisStokes.boundary0 γ)
  period_accounting_additive_holds :
    ∀ x y : D.certifiedFields.periodStokesTheoremPackage.extensionAccounting.ExtensionEvent,
      D.certifiedFields.periodStokesTheoremPackage.extensionAccounting.kappa_U (x + y) =
        D.certifiedFields.periodStokesTheoremPackage.extensionAccounting.kappa_U x +
          D.certifiedFields.periodStokesTheoremPackage.extensionAccounting.kappa_U y
  topological_capacity_holds :
    Module.finrank D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.k
          D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.C1 <=
      Module.finrank D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.k
          D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.H1 +
        Module.finrank D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.k
          D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.C0 +
          Module.finrank D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.k
            D.certifiedFields.topologicalDebtTheoremPackage.nerveComplex.C2
  derived_conflict_tor_holds :
    Nonempty
      (D.certifiedFields.derivedConflictTheoremPackage.lawConflict ≃ₗ[
          D.certifiedFields.derivedConflictTheoremPackage.R]
        Derived.Intersection.mathlibTor
          D.certifiedFields.derivedConflictTheoremPackage.R
          D.certifiedFields.derivedConflictTheoremPackage.leftIdeal
          D.certifiedFields.derivedConflictTheoremPackage.rightIdeal
          D.certifiedFields.derivedConflictTheoremPackage.degree)
  certified_statement_holds : aatGAGAComparisonStatement D

namespace AATGAGAFiniteMeasurementComparison

/-- VIII.Theorem 12.3: expose the complete certified statement. -/
theorem certified_statement_holds_of_package
    {M : MeasurementProfile.{u, v}} {D : AATGAGAComparisonData M}
    (T : AATGAGAFiniteMeasurementComparison D) :
    aatGAGAComparisonStatement D :=
  T.certified_statement_holds

end AATGAGAFiniteMeasurementComparison

/-- VIII.Theorem 12.3: construct the finite AAT-GAGA comparison package. -/
def aatGAGAFiniteMeasurementComparisonPackage
    {M : MeasurementProfile.{u, v}} (D : AATGAGAComparisonData M) :
    AATGAGAFiniteMeasurementComparison D where
  packet := aatGAGAComparisonPacketOfData D
  packet_extends_data := rfl
  hodge_comparison_holds :=
    D.certifiedFields.finiteHodgeTheoremPackage.harmonic_cohomology_holds
  harmonic_decomposition_holds :=
    D.certifiedFields.finiteHodgeTheoremPackage.decomposition_holds
  period_stokes_holds := fun ω γ =>
    Cohomology.IntervalBasisStokes.finiteIntervalStokes_basis ω γ
  period_accounting_additive_holds := fun x y =>
    D.certifiedFields.periodStokesTheoremPackage.period_stokes_accounting_additive x y
  topological_capacity_holds :=
    D.certifiedFields.topologicalDebtTheoremPackage.topological_debt_capacity_from_complex
  derived_conflict_tor_holds :=
    D.certifiedFields.derivedConflictTheoremPackage.lawConflictTorReading_holds
  certified_statement_holds := aatGAGAComparisonStatement_holds D

/-- VIII.Theorem 12.3: the derived finite AAT-GAGA comparison exists. -/
theorem aatGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) :
    Nonempty (AATGAGAFiniteMeasurementComparison D) :=
  ⟨aatGAGAFiniteMeasurementComparisonPackage D⟩

end Measurement
end AAT.AG
