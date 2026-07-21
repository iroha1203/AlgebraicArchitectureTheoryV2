import Formal.AG.Cohomology.PeriodStokes
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Measurement.Packet

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII theorem 12.3: finite AAT-GAGA comparison.

The certified comparison is derived from one selected finite datum.  Its
components are inputs for existing Hodge, finite-cover, derived-intersection,
and Hilbert-series theorems; no comparison conclusion is a caller-supplied
certificate.
-/

/-- VIII.Theorem 12.3: finite data shared by every certified comparison. -/
structure AATGAGACommonFiniteData (M : MeasurementProfile.{u, v}) where
  /-- The finite site object selected for the comparison. -/
  selectedSite : M.SiteObj
  /-- The finite cover element selected for the comparison. -/
  selectedCover : M.Cover
  /-- The coefficient object selected for the comparison. -/
  selectedCoefficient : M.Coeff
  /-- The measured domain element selected for the comparison. -/
  selectedMeasurement : M.Domain
  /-- Evidence that the selected measurement is measured by the profile. -/
  measuredSelection : M.Measured_M selectedMeasurement
  /-- The Hodge model is selected by the same site, cover, coefficient, and measurement. -/
  hodgeCellularModelAt :
    (site : M.SiteObj) → (cover : M.Cover) → (coefficient : M.Coeff) →
      (measurement : M.Domain) → CellularMeasurementModel M
  /-- The common law ambient is selected by the same finite data. -/
  commonAmbientAt :
    (site : M.SiteObj) → (cover : M.Cover) → (coefficient : M.Coeff) →
      (measurement : M.Domain) → CommonAmbientPair M

namespace AATGAGACommonFiniteData

/-- The cellular model determined by the selected finite datum. -/
def selectedCellularModel {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) : CellularMeasurementModel M :=
  C.hodgeCellularModelAt C.selectedSite C.selectedCover C.selectedCoefficient
    C.selectedMeasurement

/-- The common ambient determined by the selected finite datum. -/
def commonAmbient {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) : CommonAmbientPair M :=
  C.commonAmbientAt C.selectedSite C.selectedCover C.selectedCoefficient
    C.selectedMeasurement

end AATGAGACommonFiniteData

/-- VIII.Theorem 12.3: input for the real finite Hodge derivation. -/
structure SelectedFiniteHodgeTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- The Laplacian reading on the cellular model selected by `C`. -/
  laplacianReading : SheafLaplacianReading C.selectedCellularModel
  /-- Normed additive structure on the preceding selected cochain space. -/
  [previousNormed : NormedAddCommGroup
    (C.selectedCellularModel.Cochain laplacianReading.previousDegree)]
  /-- Real inner-product structure on the preceding selected cochain space. -/
  [previousInner : InnerProductSpace ℝ
    (C.selectedCellularModel.Cochain laplacianReading.previousDegree)]
  /-- Finite-dimensionality of the preceding selected cochain space. -/
  [previousFinite : FiniteDimensional ℝ
    (C.selectedCellularModel.Cochain laplacianReading.previousDegree)]
  /-- Normed additive structure on the selected cochain space. -/
  [selectedNormed : NormedAddCommGroup
    (C.selectedCellularModel.Cochain laplacianReading.degree)]
  /-- Real inner-product structure on the selected cochain space. -/
  [selectedInner : InnerProductSpace ℝ
    (C.selectedCellularModel.Cochain laplacianReading.degree)]
  /-- Finite-dimensionality of the selected cochain space. -/
  [selectedFinite : FiniteDimensional ℝ
    (C.selectedCellularModel.Cochain laplacianReading.degree)]
  /-- Normed additive structure on the succeeding selected cochain space. -/
  [nextNormed : NormedAddCommGroup
    (C.selectedCellularModel.Cochain laplacianReading.nextDegree)]
  /-- Real inner-product structure on the succeeding selected cochain space. -/
  [nextInner : InnerProductSpace ℝ
    (C.selectedCellularModel.Cochain laplacianReading.nextDegree)]
  /-- Finite-dimensionality of the succeeding selected cochain space. -/
  [nextFinite : FiniteDimensional ℝ
    (C.selectedCellularModel.Cochain laplacianReading.nextDegree)]
  /-- The actual real finite complex used to derive the Hodge package. -/
  realFiniteComplex : RealFiniteInnerProductComplex
    (C.selectedCellularModel.Cochain laplacianReading.previousDegree)
    (C.selectedCellularModel.Cochain laplacianReading.degree)
    (C.selectedCellularModel.Cochain laplacianReading.nextDegree)
  /-- The comparison from the selected cellular reading to the real complex. -/
  cellularComparison : RealFiniteInnerProductComplex.CellularRealFiniteComplexComparison laplacianReading
    realFiniteComplex

attribute [instance] SelectedFiniteHodgeTheoremPackage.previousNormed
attribute [instance] SelectedFiniteHodgeTheoremPackage.previousInner
attribute [instance] SelectedFiniteHodgeTheoremPackage.previousFinite
attribute [instance] SelectedFiniteHodgeTheoremPackage.selectedNormed
attribute [instance] SelectedFiniteHodgeTheoremPackage.selectedInner
attribute [instance] SelectedFiniteHodgeTheoremPackage.selectedFinite
attribute [instance] SelectedFiniteHodgeTheoremPackage.nextNormed
attribute [instance] SelectedFiniteHodgeTheoremPackage.nextInner
attribute [instance] SelectedFiniteHodgeTheoremPackage.nextFinite

namespace SelectedFiniteHodgeTheoremPackage

/-- The Hodge data derived from the selected real finite complex. -/
noncomputable def hodgeData {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    FiniteHodgeDecompositionData P.laplacianReading :=
  RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionData
    P.laplacianReading P.realFiniteComplex P.cellularComparison

/-- VIII.Theorem 8.5 package derived from the selected real finite complex. -/
theorem hodgePackage {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    FiniteHodgeDecomposition P.hodgeData :=
  RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionPackage
    P.laplacianReading P.realFiniteComplex P.cellularComparison

/-- VIII.Theorem 12.3: the selected Hodge decomposition is theorem-derived. -/
theorem decomposition_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    P.hodgeData.finiteHodgeDecomposition :=
  P.hodgePackage.decomposition_holds

/-- VIII.Theorem 12.3: the selected harmonic/cohomology comparison is theorem-derived. -/
theorem harmonic_cohomology_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    P.hodgeData.harmonicKernelIdentifiesCohomology :=
  P.hodgePackage.harmonic_cohomology_holds

end SelectedFiniteHodgeTheoremPackage

/-- VIII.Theorem 12.3: selected two-cover input for the finite Period/Stokes formula. -/
structure SelectedPeriodStokesTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- The left site object in the selected two-cover reading. -/
  leftSite : M.SiteObj
  /-- The right site object in the selected two-cover reading. -/
  rightSite : M.SiteObj
  /-- Identification of the selected site object with the right site object. -/
  selectedSite_eq_right : C.selectedSite = rightSite
  /-- The left cover element in the selected two-cover reading. -/
  leftCover : M.Cover
  /-- The right cover element in the selected two-cover reading. -/
  rightCover : M.Cover
  /-- Identification of the selected cover element with the right cover element. -/
  selectedCover_eq_right : C.selectedCover = rightCover
  /-- The two selected cover elements are distinct. -/
  leftCover_ne_right : leftCover ≠ rightCover

/-- VIII.Theorem 12.3: selected finite-nerve input attached to site and cover data. -/
structure SelectedTopologicalDebtTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- The finite cover nerve used by the selected capacity calculation. -/
  nerve : Cohomology.CoverNerve.{v}
  /-- Realization of each nerve chart in the selected finite site. -/
  chartToSite : nerve.Chart → M.SiteObj
  /-- Realization of each nerve edge in the selected finite cover. -/
  edgeToCover : nerve.EdgeComponent → M.Cover
  /-- A nerve chart whose realization is the selected site object. -/
  selectedSiteVisible : ∃ chart, chartToSite chart = C.selectedSite
  /-- A nerve edge whose realization is the selected cover element. -/
  selectedCoverVisible : ∃ edge, edgeToCover edge = C.selectedCover
  /-- The finite cochain complex used for the capacity calculation. -/
  nerveComplex : Cohomology.FiniteNerveCochainComplex nerve
  /-- Identification of the complex coefficient field with the selected coefficient. -/
  coefficient_eq : nerveComplex.k = M.Coeff

namespace SelectedTopologicalDebtTheoremPackage

/-- VIII.Theorem 12.3: finite-nerve capacity is derived from the selected complex. -/
theorem topological_debt_capacity_from_complex {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedTopologicalDebtTheoremPackage C) :
    Module.finrank P.nerveComplex.k P.nerveComplex.C1 <=
      Module.finrank P.nerveComplex.k P.nerveComplex.H1 +
        Module.finrank P.nerveComplex.k P.nerveComplex.C0 +
          Module.finrank P.nerveComplex.k P.nerveComplex.C2 :=
  P.nerveComplex.topologicalDebtCapacity_fromComplex

end SelectedTopologicalDebtTheoremPackage

/-- VIII.Theorem 12.3: common-ambient reading of the selected monomial conflict. -/
structure SelectedDerivedConflictTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- Reading of common-ambient law ideals as shared-witness monomial ideals. -/
  readLawIdeal : C.commonAmbient.LawIdeal →
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
  /-- The left common-ambient law ideal reads as the `idealU` monomial ideal. -/
  leftIdeal_eq : readLawIdeal C.commonAmbient.leftLawIdeal =
    Derived.Counterexample.SharedWitnessCoord.idealU ℝ
  /-- The right common-ambient law ideal reads as the `idealV` monomial ideal. -/
  rightIdeal_eq : readLawIdeal C.commonAmbient.rightLawIdeal =
    Derived.Counterexample.SharedWitnessCoord.idealV ℝ

namespace SelectedDerivedConflictTheoremPackage

/-- The left monomial ideal read from the common ambient. -/
def leftIdeal {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ) :=
  P.readLawIdeal C.commonAmbient.leftLawIdeal

/-- The right monomial ideal read from the common ambient. -/
def rightIdeal {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ) :=
  P.readLawIdeal C.commonAmbient.rightLawIdeal

/-- The degree-one LawConflict object computed by the canonical Tor bridge. -/
abbrev lawConflict {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
    P.leftIdeal P.rightIdeal).LawConflict 1

/-- VIII.Theorem 12.3: canonical degree-one LawConflict/Mathlib Tor equivalence. -/
noncomputable def lawConflictLinearEquivMathlibTor {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ]
      Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
        P.leftIdeal P.rightIdeal 1 :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
    P.leftIdeal P.rightIdeal).lawConflictLinearEquivMathlibTor 1

/-- VIII.Theorem 12.3: the selected LawConflict has the canonical Tor reading. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Nonempty
      (P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ]
        Derived.Intersection.mathlibTor
          (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
          P.leftIdeal P.rightIdeal 1) :=
  ⟨P.lawConflictLinearEquivMathlibTor⟩

/-- VIII.Theorem 12.3: monomial Hilbert-series accounting for the selected conflict. -/
def hilbertSeriesAccountingStatement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) : Prop :=
  P.leftIdeal = Derived.Counterexample.SharedWitnessCoord.idealU ℝ ∧
    P.rightIdeal = Derived.Counterexample.SharedWitnessCoord.idealV ℝ ∧
      FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries *
          FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries =
        FiniteModel.DerivedPart5.sharedWitnessAmbientHilbertSeries *
          FiniteModel.DerivedPart5.sharedWitnessConflictAlternatingSeries

/-- VIII.Theorem 12.3: derive the selected monomial Hilbert-series accounting. -/
theorem hilbertSeriesAccounting_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.hilbertSeriesAccountingStatement :=
  ⟨P.leftIdeal_eq, P.rightIdeal_eq,
    FiniteModel.DerivedPart5.sharedWitnessG5_denominatorClearedIdentity⟩

/-- The selected degree-one conflict has positive degree-three Hilbert mass. -/
theorem torOneDegreeThreeMass :
    FiniteModel.DerivedPart5.sharedWitnessTorOneCoeff 3 = 1 :=
  FiniteModel.DerivedPart5.sharedWitnessTorOneCoeff_three

end SelectedDerivedConflictTheoremPackage

/-- VIII.Theorem 12.3: theorem inputs over one common selected finite datum. -/
structure AATGAGACertifiedFields {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- Input from which the selected finite Hodge assertions are derived. -/
  hodgeInput : SelectedFiniteHodgeTheoremPackage C
  /-- Input from which the selected finite Period/Stokes formula is derived. -/
  periodStokesInput : SelectedPeriodStokesTheoremPackage C
  /-- Input from which the selected finite-nerve capacity is derived. -/
  topologicalInput : SelectedTopologicalDebtTheoremPackage C
  /-- Input from which the selected LawConflict/Tor and Hilbert readings are derived. -/
  derivedConflictInput : SelectedDerivedConflictTheoremPackage C

namespace SelectedPeriodStokesTheoremPackage

/-- The selected degree-zero differential on the two-cover. -/
def d0 {M : MeasurementProfile.{u, v}} {C : AATGAGACommonFiniteData M}
    (P : SelectedPeriodStokesTheoremPackage C) (omega : M.Cover → ℝ) : ℝ :=
  omega P.rightCover - omega P.leftCover

/-- The selected degree-zero chain on the two-cover. -/
noncomputable def chain0 {M : MeasurementProfile.{u, v}} {C : AATGAGACommonFiniteData M}
    (P : SelectedPeriodStokesTheoremPackage C) (gamma : ℝ) : M.Cover → ℝ := by
  classical
  exact fun cover => if cover = P.leftCover then -gamma
    else if cover = P.rightCover then gamma else 0

/-- The selected degree-zero pairing. -/
def pair0 {M : MeasurementProfile.{u, v}} {C : AATGAGACommonFiniteData M}
    (P : SelectedPeriodStokesTheoremPackage C)
    (omega chain : M.Cover → ℝ) : ℝ :=
  omega P.leftCover * chain P.leftCover + omega P.rightCover * chain P.rightCover

/-- The selected degree-one pairing. -/
def pair1 {M : MeasurementProfile.{u, v}} {C : AATGAGACommonFiniteData M}
    (_P : SelectedPeriodStokesTheoremPackage C) (omega gamma : ℝ) : ℝ :=
  omega * gamma

/-- VIII.Theorem 12.3: real finite Period/Stokes formula on the selected two-cover. -/
theorem period_stokes_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    ∀ (omega : M.Cover → ℝ) (gamma : ℝ),
      P.pair1 (P.d0 omega) gamma = P.pair0 omega (P.chain0 gamma) := by
  intro omega gamma
  have right_ne_left : P.rightCover ≠ P.leftCover := Ne.symm P.leftCover_ne_right
  simp [pair1, d0, pair0, chain0, right_ne_left]
  ring

end SelectedPeriodStokesTheoremPackage

/-- VIII.Principle 12.4: candidate-dependent comparison interfaces remain separate data. -/
structure AATGAGACandidateInterfaces (M : MeasurementProfile.{u, v}) where
  /-- Carrier for a monotone witness-stability candidate interface. -/
  MonotoneWitnessStabilityInterface : Type v
  /-- Carrier for a finite Čech-stability candidate interface. -/
  FiniteCechStabilityInterface : Type v
  /-- Carrier for a flat-base-change candidate interface. -/
  FlatBaseChangeInterface : Type v
  /-- Carrier for a spectral-hotspot candidate interface. -/
  SpectralHotspotInterface : Type v
  /-- Carrier for a transfer lower-bound candidate interface. -/
  TransferLowerBoundInterface : Type v
  /-- Optional monotone witness-stability candidate input. -/
  monotoneWitnessStability : Option MonotoneWitnessStabilityInterface
  /-- Optional finite Čech-stability candidate input. -/
  finiteCechStability : Option FiniteCechStabilityInterface
  /-- Optional flat-base-change candidate input. -/
  flatBaseChange : Option FlatBaseChangeInterface
  /-- Optional spectral-hotspot candidate input. -/
  spectralHotspot : Option SpectralHotspotInterface
  /-- Optional transfer lower-bound candidate input. -/
  transferLowerBound : Option TransferLowerBoundInterface

/-- VIII.Principle 12.4: non-conclusion data for the finite GAGA comparison. -/
structure AATGAGANonConclusionData (M : MeasurementProfile.{u, v}) where
  /-- Statement that external data-source fidelity is not certified here. -/
  noExternalDataSourceFidelity : Prop
  /-- Evidence for the external data-source fidelity non-conclusion. -/
  noExternalDataSourceFidelity_cert : noExternalDataSourceFidelity
  /-- Statement that external procedure correctness is not certified here. -/
  noExternalProcedureCorrectness : Prop
  /-- Evidence for the external procedure correctness non-conclusion. -/
  noExternalProcedureCorrectness_cert : noExternalProcedureCorrectness
  /-- Statement that arbitrary law-universe comparison is not certified here. -/
  noArbitraryLawUniverseComparison : Prop
  /-- Evidence for the arbitrary law-universe non-conclusion. -/
  noArbitraryLawUniverseComparison_cert : noArbitraryLawUniverseComparison
  /-- Statement that candidate-dependent fields are not certified here. -/
  candidateDependentFieldsNotCertified : Prop
  /-- Evidence for the candidate-dependent non-conclusion. -/
  candidateDependentFieldsNotCertified_cert : candidateDependentFieldsNotCertified

/-- VIII.Theorem 12.3: data for one common finite AAT-GAGA comparison. -/
structure AATGAGAComparisonData (M : MeasurementProfile.{u, v}) where
  /-- The bounded measurement packet that supplies the selected profile data. -/
  measurementPacketData : MeasurementPacketData M
  /-- The selected finite datum shared by all theorem inputs. -/
  commonData : AATGAGACommonFiniteData M
  /-- The theorem inputs from which every certified conjunct is derived. -/
  certifiedFields : AATGAGACertifiedFields commonData
  /-- Candidate-dependent inputs retained separately from certified results. -/
  candidateInterfaces : AATGAGACandidateInterfaces M
  /-- Explicit non-conclusion data retained separately from certified results. -/
  nonConclusionData : AATGAGANonConclusionData M

/-- VIII.Theorem 12.3: conclusions certified from the selected finite theorem inputs. -/
def aatGAGACertifiedComparisonStatement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) : Prop :=
  F.hodgeInput.hodgeData.harmonicKernelIdentifiesCohomology ∧
    F.hodgeInput.hodgeData.finiteHodgeDecomposition ∧
      (∀ (omega : M.Cover → ℝ) (gamma : ℝ),
        F.periodStokesInput.pair1 (F.periodStokesInput.d0 omega) gamma =
          F.periodStokesInput.pair0 omega (F.periodStokesInput.chain0 gamma)) ∧
        (Module.finrank F.topologicalInput.nerveComplex.k F.topologicalInput.nerveComplex.C1 <=
          Module.finrank F.topologicalInput.nerveComplex.k F.topologicalInput.nerveComplex.H1 +
            Module.finrank F.topologicalInput.nerveComplex.k F.topologicalInput.nerveComplex.C0 +
              Module.finrank F.topologicalInput.nerveComplex.k F.topologicalInput.nerveComplex.C2) ∧
          Nonempty
            (F.derivedConflictInput.lawConflict ≃ₗ[
                Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ]
              Derived.Intersection.mathlibTor
                (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
                F.derivedConflictInput.leftIdeal F.derivedConflictInput.rightIdeal 1) ∧
            F.derivedConflictInput.hilbertSeriesAccountingStatement

/-- VIII.Theorem 12.3: derive every certified comparison conjunct. -/
theorem aatGAGACertifiedComparisonStatement_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F :=
  ⟨F.hodgeInput.harmonic_cohomology_holds,
    F.hodgeInput.decomposition_holds,
    F.periodStokesInput.period_stokes_holds,
    F.topologicalInput.topological_debt_capacity_from_complex,
    F.derivedConflictInput.lawConflictTorReading_holds,
    F.derivedConflictInput.hilbertSeriesAccounting_holds⟩

/-- VIII.Theorem 12.3: selected finite-profile comparison statement. -/
def aatGAGAComparisonStatement {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGACertifiedComparisonStatement D.certifiedFields

/-- VIII.Theorem 12.3: derive the comparison statement from common finite data. -/
theorem aatGAGAComparisonStatement_holds {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : aatGAGAComparisonStatement D :=
  aatGAGACertifiedComparisonStatement_holds D.certifiedFields

/-- VIII.Theorem 12.3 acceptance: no certificate bundle is accepted. -/
abbrev AATGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGAComparisonStatement D

/-- VIII.Theorem 12.3: the certified finite comparison is derived from its inputs. -/
theorem aatGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : AATGAGAFiniteMeasurementComparison D :=
  aatGAGAComparisonStatement_holds D

end Measurement
end AAT.AG
