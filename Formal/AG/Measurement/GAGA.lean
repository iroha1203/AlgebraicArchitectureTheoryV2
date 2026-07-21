import Formal.AG.Cohomology.PeriodStokes
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Measurement.Packet

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII theorem 12.3: finite AAT-GAGA comparison.

Every certified reading is tied to one finite profile by direct realization
maps.  Hodge, Period/Stokes, finite-nerve capacity, and derived conflict use
the selected data themselves; no conclusion is stored as a certificate field.
-/

namespace GAGAIntervalNerve

/-- The selected two-chart cover nerve used by the finite comparison. -/
def nerve : Cohomology.CoverNerve where
  Chart := Cohomology.RealIntervalBasisStokes.Vertex
  EdgeComponent := Cohomology.RealIntervalBasisStokes.Edge
  FaceComponent := Empty
  edgeLeft
    | .interval => .left
  edgeRight
    | .interval => .right
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun f => Empty.elim f
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := Empty.elim

/-- The incidence cochain complex of the selected two-chart cover nerve. -/
noncomputable def complex : Cohomology.FiniteNerveCochainComplex nerve where
  k := ℝ
  C0 := Cohomology.RealIntervalBasisStokes.Cochain 0
  C1 := Cohomology.RealIntervalBasisStokes.Cochain 1
  C2 := Cohomology.RealIntervalBasisStokes.Cochain 2
  add_C0 := inferInstance
  add_C1 := inferInstance
  add_C2 := inferInstance
  module_C0 := inferInstance
  module_C1 := inferInstance
  module_C2 := inferInstance
  finiteDimensional_C0 := inferInstance
  finiteDimensional_C1 := inferInstance
  finiteDimensional_C2 := inferInstance
  d0 := Cohomology.RealIntervalBasisStokes.d0
  d1 := 0
  d1_comp_d0 := by
    intro c
    rfl

/-- Capacity follows from the actual incidence complex of the selected nerve. -/
theorem topologicalDebtCapacity :
    Module.finrank complex.k complex.C1 <=
      Module.finrank complex.k complex.H1 + Module.finrank complex.k complex.C0 +
        Module.finrank complex.k complex.C2 :=
  complex.topologicalDebtCapacity_fromComplex

end GAGAIntervalNerve

/-- VIII.Theorem 12.3: finite data shared by every certified comparison. -/
structure AATGAGACommonFiniteData (M : MeasurementProfile.{u, v}) where
  /-- The site object selected for the comparison. -/
  selectedSite : M.SiteObj
  /-- The cover element selected for the comparison. -/
  selectedCover : M.Cover
  /-- The measurement-domain element selected for the comparison. -/
  selectedMeasurement : M.Domain
  /-- Evidence that the selected measurement belongs to the measured profile. -/
  measuredSelection : M.Measured_M selectedMeasurement
  /-- Additive coefficient structure of the selected finite measurement regime. -/
  [coefficientAddCommGroup : AddCommGroup M.Coeff]
  /-- The finite coefficient object is compared explicitly with real coefficients. -/
  coefficientToReal : M.Coeff ≃+ ℝ
  /-- The selected finite cellular cochain model. -/
  cellularModel : CellularMeasurementModel M
  /-- Realization of each cellular site carrier as a profile site object. -/
  cellToSite : cellularModel.Cell → M.SiteObj
  /-- The cellular carrier marking the selected site object. -/
  selectedCell : cellularModel.Cell
  /-- The selected cellular carrier realizes the selected profile site object. -/
  selectedCell_eq : cellToSite selectedCell = selectedSite
  /-- The common ambient used for the selected law-ideal reading. -/
  commonAmbient : CommonAmbientPair M
  /-- The left ambient domain is the selected measurement domain element. -/
  ambientLeftDomain_eq : commonAmbient.leftDomain = selectedMeasurement
  /-- The right ambient domain is the selected measurement domain element. -/
  ambientRightDomain_eq : commonAmbient.rightDomain = selectedMeasurement
  /-- The selected coefficient object. -/
  selectedCoefficient : M.Coeff
  /-- Reading of profile coefficients in the common ambient. -/
  coefficientToAmbient : M.Coeff → commonAmbient.CoefficientObject
  /-- The selected profile coefficient is the left ambient coefficient. -/
  selectedCoefficient_left_eq :
    coefficientToAmbient selectedCoefficient = commonAmbient.leftCoefficient
  /-- The selected profile coefficient is the right ambient coefficient. -/
  selectedCoefficient_right_eq :
    coefficientToAmbient selectedCoefficient = commonAmbient.rightCoefficient

namespace AATGAGACommonFiniteData

attribute [instance] coefficientAddCommGroup

/-- Coherence facts tying every selected finite datum to its realized reading. -/
def coherent {M : MeasurementProfile.{u, v}} (C : AATGAGACommonFiniteData M) : Prop :=
  M.InScope C.selectedMeasurement ∧
    Function.Injective C.coefficientToReal ∧
      C.cellToSite C.selectedCell = C.selectedSite ∧
        C.commonAmbient.leftDomain = C.selectedMeasurement ∧
          C.commonAmbient.rightDomain = C.selectedMeasurement ∧
            C.coefficientToAmbient C.selectedCoefficient = C.commonAmbient.leftCoefficient ∧
              C.coefficientToAmbient C.selectedCoefficient = C.commonAmbient.rightCoefficient

/-- The selected finite data satisfy their direct realization equalities. -/
theorem coherent_holds {M : MeasurementProfile.{u, v}} (C : AATGAGACommonFiniteData M) :
    C.coherent :=
  ⟨C.measuredSelection.inScope, C.coefficientToReal.injective, C.selectedCell_eq,
    C.ambientLeftDomain_eq, C.ambientRightDomain_eq,
    C.selectedCoefficient_left_eq, C.selectedCoefficient_right_eq⟩

end AATGAGACommonFiniteData

/-- VIII.Theorem 12.3: input for the real finite Hodge derivation. -/
structure SelectedFiniteHodgeTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- The Laplacian reading on the directly selected cellular model. -/
  laplacianReading : SheafLaplacianReading C.cellularModel
  /-- Normed additive structure on the preceding selected cochain space. -/
  [previousNormed : NormedAddCommGroup
    (C.cellularModel.Cochain laplacianReading.previousDegree)]
  /-- Real inner-product structure on the preceding selected cochain space. -/
  [previousInner : InnerProductSpace ℝ
    (C.cellularModel.Cochain laplacianReading.previousDegree)]
  /-- Finite-dimensionality of the preceding selected cochain space. -/
  [previousFinite : FiniteDimensional ℝ
    (C.cellularModel.Cochain laplacianReading.previousDegree)]
  /-- Normed additive structure on the selected cochain space. -/
  [selectedNormed : NormedAddCommGroup
    (C.cellularModel.Cochain laplacianReading.degree)]
  /-- Real inner-product structure on the selected cochain space. -/
  [selectedInner : InnerProductSpace ℝ
    (C.cellularModel.Cochain laplacianReading.degree)]
  /-- Finite-dimensionality of the selected cochain space. -/
  [selectedFinite : FiniteDimensional ℝ
    (C.cellularModel.Cochain laplacianReading.degree)]
  /-- Normed additive structure on the succeeding selected cochain space. -/
  [nextNormed : NormedAddCommGroup
    (C.cellularModel.Cochain laplacianReading.nextDegree)]
  /-- Real inner-product structure on the succeeding selected cochain space. -/
  [nextInner : InnerProductSpace ℝ
    (C.cellularModel.Cochain laplacianReading.nextDegree)]
  /-- Finite-dimensionality of the succeeding selected cochain space. -/
  [nextFinite : FiniteDimensional ℝ
    (C.cellularModel.Cochain laplacianReading.nextDegree)]
  /-- The real finite complex from which Hodge data are derived. -/
  realFiniteComplex : RealFiniteInnerProductComplex
    (C.cellularModel.Cochain laplacianReading.previousDegree)
    (C.cellularModel.Cochain laplacianReading.degree)
    (C.cellularModel.Cochain laplacianReading.nextDegree)
  /-- Comparison of the selected cellular operators with the real complex. -/
  cellularComparison : RealFiniteInnerProductComplex.CellularRealFiniteComplexComparison
    laplacianReading realFiniteComplex

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

/-- Hodge data derived from the selected real finite complex. -/
noncomputable def hodgeData {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    FiniteHodgeDecompositionData P.laplacianReading :=
  RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionData
    P.laplacianReading P.realFiniteComplex P.cellularComparison

/-- The finite Hodge package derived from the selected complex. -/
theorem hodgePackage {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    FiniteHodgeDecomposition P.hodgeData :=
  RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionPackage
    P.laplacianReading P.realFiniteComplex P.cellularComparison

/-- The selected finite Hodge decomposition is theorem-derived. -/
theorem decomposition_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    P.hodgeData.finiteHodgeDecomposition :=
  P.hodgePackage.decomposition_holds

/-- The selected harmonic/cohomology comparison is theorem-derived. -/
theorem harmonic_cohomology_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedFiniteHodgeTheoremPackage C) :
    P.hodgeData.harmonicKernelIdentifiesCohomology :=
  P.hodgePackage.harmonic_cohomology_holds

end SelectedFiniteHodgeTheoremPackage

/-- VIII.Theorem 12.3: realization of the selected two-chart Period/Stokes model. -/
structure SelectedPeriodStokesTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- Realization of each interval chart as a cell of the selected Hodge model. -/
  cellRealization :
    Cohomology.RealIntervalBasisStokes.Vertex → C.cellularModel.Cell
  /-- Realization of the two real interval charts in the selected profile site. -/
  siteRealization : Cohomology.RealIntervalBasisStokes.Vertex → M.SiteObj
  /-- The Period/Stokes chart realization agrees with the Hodge-cell realization. -/
  siteRealization_eq_cellToSite :
    ∀ vertex, siteRealization vertex = C.cellToSite (cellRealization vertex)
  /-- Realization of the oriented interval overlap in the selected profile cover. -/
  coverRealization : Cohomology.RealIntervalBasisStokes.Edge → M.Cover
  /-- The right interval chart realizes the selected site object. -/
  rightChart_eq_selectedSite :
    siteRealization .right = C.selectedSite
  /-- The interval overlap realizes the selected cover element. -/
  intervalEdge_eq_selectedCover :
    coverRealization .interval = C.selectedCover
  /-- The two selected interval charts remain distinct after realization. -/
  siteRealization_injective : Function.Injective siteRealization

namespace SelectedPeriodStokesTheoremPackage

/-- The selected finite Period/Stokes formula, anchored to the profile site and cover. -/
def statement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) : Prop :=
  (∀ vertex,
      P.siteRealization vertex = C.cellToSite (P.cellRealization vertex)) ∧
    P.siteRealization .right = C.selectedSite ∧
      P.coverRealization .interval = C.selectedCover ∧
        P.siteRealization_injective ∧
          ∀ (ω : Cohomology.RealIntervalBasisStokes.Cochain 0)
            (γ : Cohomology.RealIntervalBasisStokes.Chain 1),
            Cohomology.RealIntervalBasisStokes.pair1
                (Cohomology.RealIntervalBasisStokes.d0 ω) γ =
              Cohomology.RealIntervalBasisStokes.pair0 ω
                (Cohomology.RealIntervalBasisStokes.chain0 γ)

/-- Derive the selected Period/Stokes formula from the real finite basis theorem. -/
theorem statement_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    P.statement :=
  ⟨P.siteRealization_eq_cellToSite, P.rightChart_eq_selectedSite,
    P.intervalEdge_eq_selectedCover,
    P.siteRealization_injective,
    Cohomology.RealIntervalBasisStokes.finiteIntervalStokes_basis⟩

/-- The selected nerve capacity is computed from the same chart and overlap realization. -/
def topologicalCapacityStatement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) : Prop :=
  (∀ vertex,
      P.siteRealization vertex = C.cellToSite (P.cellRealization vertex)) ∧
    P.siteRealization .right = C.selectedSite ∧
      P.coverRealization .interval = C.selectedCover ∧
        P.siteRealization_injective ∧
          Module.finrank GAGAIntervalNerve.complex.k GAGAIntervalNerve.complex.C1 <=
            Module.finrank GAGAIntervalNerve.complex.k GAGAIntervalNerve.complex.H1 +
              Module.finrank GAGAIntervalNerve.complex.k GAGAIntervalNerve.complex.C0 +
                Module.finrank GAGAIntervalNerve.complex.k GAGAIntervalNerve.complex.C2

/-- Derive selected nerve capacity from its actual incidence cochain complex. -/
theorem topologicalCapacityStatement_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    P.topologicalCapacityStatement :=
  ⟨P.siteRealization_eq_cellToSite, P.rightChart_eq_selectedSite,
    P.intervalEdge_eq_selectedCover,
    P.siteRealization_injective,
    GAGAIntervalNerve.topologicalDebtCapacity⟩

end SelectedPeriodStokesTheoremPackage

/-- VIII.Theorem 12.3: common-ambient reading of the selected monomial conflict. -/
structure SelectedDerivedConflictTheoremPackage {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- Reading of common-ambient law ideals as shared-witness monomial ideals. -/
  readLawIdeal : C.commonAmbient.LawIdeal →
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
  /-- The left common-ambient law ideal reads as `idealU`. -/
  leftIdeal_eq : readLawIdeal C.commonAmbient.leftLawIdeal =
    Derived.Counterexample.SharedWitnessCoord.idealU ℝ
  /-- The right common-ambient law ideal reads as `idealV`. -/
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

/-- The canonical degree-one LawConflict/Mathlib Tor equivalence. -/
noncomputable def lawConflictLinearEquivMathlibTor {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ]
      Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
        P.leftIdeal P.rightIdeal 1 :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
    P.leftIdeal P.rightIdeal).lawConflictLinearEquivMathlibTor 1

/-- The selected LawConflict has the canonical Tor reading. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Nonempty
      (P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ]
        Derived.Intersection.mathlibTor
          (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
          P.leftIdeal P.rightIdeal 1) :=
  ⟨P.lawConflictLinearEquivMathlibTor⟩

/-- Monomial Hilbert-series accounting for the selected conflict. -/
def hilbertSeriesAccountingStatement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) : Prop :=
  P.leftIdeal = Derived.Counterexample.SharedWitnessCoord.idealU ℝ ∧
    P.rightIdeal = Derived.Counterexample.SharedWitnessCoord.idealV ℝ ∧
      FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries *
          FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries =
        FiniteModel.DerivedPart5.sharedWitnessAmbientHilbertSeries *
          FiniteModel.DerivedPart5.sharedWitnessConflictAlternatingSeries

/-- Derive selected monomial Hilbert-series accounting. -/
theorem hilbertSeriesAccounting_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.hilbertSeriesAccountingStatement :=
  ⟨P.leftIdeal_eq, P.rightIdeal_eq,
    FiniteModel.DerivedPart5.sharedWitnessG5_denominatorClearedIdentity⟩

end SelectedDerivedConflictTheoremPackage

/-- VIII.Theorem 12.3: theorem inputs over one common selected finite datum. -/
structure AATGAGACertifiedFields {M : MeasurementProfile.{u, v}}
    (C : AATGAGACommonFiniteData M) where
  /-- Input from which the selected finite Hodge assertions are derived. -/
  hodgeInput : SelectedFiniteHodgeTheoremPackage C
  /-- Input from which Period/Stokes and nerve capacity are derived. -/
  periodStokesInput : SelectedPeriodStokesTheoremPackage C
  /-- Input from which LawConflict/Tor and Hilbert readings are derived. -/
  derivedConflictInput : SelectedDerivedConflictTheoremPackage C

/-- VIII.Principle 12.4: candidate interfaces remain separate from certified results. -/
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

/-- VIII.Principle 12.4: non-conclusion data retained outside the theorem statement. -/
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

/-- VIII.Theorem 12.3: data that enter the certified finite comparison. -/
structure AATGAGAComparisonData (M : MeasurementProfile.{u, v}) where
  /-- The selected finite datum shared by all theorem inputs. -/
  commonData : AATGAGACommonFiniteData M
  /-- The theorem inputs from which every certified conjunct is derived. -/
  certifiedFields : AATGAGACertifiedFields commonData

/-- VIII.Theorem 12.3: certified comparison statement. -/
def aatGAGACertifiedComparisonStatement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) : Prop :=
  C.coherent ∧
    F.hodgeInput.hodgeData.harmonicKernelIdentifiesCohomology ∧
      F.hodgeInput.hodgeData.finiteHodgeDecomposition ∧
        F.periodStokesInput.statement ∧
          F.periodStokesInput.topologicalCapacityStatement ∧
            Nonempty
              (F.derivedConflictInput.lawConflict ≃ₗ[
                  Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ]
                Derived.Intersection.mathlibTor
                  (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)
                  F.derivedConflictInput.leftIdeal F.derivedConflictInput.rightIdeal 1) ∧
              F.derivedConflictInput.hilbertSeriesAccountingStatement

/-- Derive every certified comparison conjunct from the selected finite data. -/
theorem aatGAGACertifiedComparisonStatement_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F :=
  ⟨C.coherent_holds, F.hodgeInput.harmonic_cohomology_holds,
    F.hodgeInput.decomposition_holds, F.periodStokesInput.statement_holds,
    F.periodStokesInput.topologicalCapacityStatement_holds,
    F.derivedConflictInput.lawConflictTorReading_holds,
    F.derivedConflictInput.hilbertSeriesAccounting_holds⟩

/-- VIII.Theorem 12.3: selected finite-profile comparison statement. -/
def aatGAGAComparisonStatement {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGACertifiedComparisonStatement D.certifiedFields

/-- Derive the comparison statement from common finite data. -/
theorem aatGAGAComparisonStatement_holds {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : aatGAGAComparisonStatement D :=
  aatGAGACertifiedComparisonStatement_holds D.certifiedFields

/-- VIII.Theorem 12.3 acceptance statement. -/
abbrev AATGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGAComparisonStatement D

/-- The certified finite comparison is derived from its selected inputs. -/
theorem aatGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : AATGAGAFiniteMeasurementComparison D :=
  aatGAGAComparisonStatement_holds D

end Measurement
end AAT.AG
