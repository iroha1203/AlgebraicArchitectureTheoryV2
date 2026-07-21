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
    C.coherent := by
  letI : AddCommGroup M.Coeff := C.coefficientAddCommGroup
  exact ⟨C.measuredSelection.inScope, C.coefficientToReal.injective, C.selectedCell_eq,
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
  /-- The cellular degree carrying the selected Čech zero-cochains. -/
  periodZeroDegree : C.cellularModel.Degree
  /-- The cellular degree carrying the selected Čech one-cochains. -/
  periodOneDegree : C.cellularModel.Degree
  /-- The cellular degree carrying the selected Čech two-cochains. -/
  periodTwoDegree : C.cellularModel.Degree
  /-- Additive structure on selected cellular zero-cochains. -/
  [periodZeroAddCommGroup : AddCommGroup (C.cellularModel.Cochain periodZeroDegree)]
  /-- Additive structure on selected cellular one-cochains. -/
  [periodOneAddCommGroup : AddCommGroup (C.cellularModel.Cochain periodOneDegree)]
  /-- Additive structure on selected cellular two-cochains. -/
  [periodTwoAddCommGroup : AddCommGroup (C.cellularModel.Cochain periodTwoDegree)]
  /-- Real linear structure on selected cellular zero-cochains. -/
  [periodZeroModule : Module ℝ (C.cellularModel.Cochain periodZeroDegree)]
  /-- Real linear structure on selected cellular one-cochains. -/
  [periodOneModule : Module ℝ (C.cellularModel.Cochain periodOneDegree)]
  /-- Real linear structure on selected cellular two-cochains. -/
  [periodTwoModule : Module ℝ (C.cellularModel.Cochain periodTwoDegree)]
  /-- Finite-dimensionality of selected cellular zero-cochains. -/
  [periodZeroFinite : FiniteDimensional ℝ (C.cellularModel.Cochain periodZeroDegree)]
  /-- Finite-dimensionality of selected cellular one-cochains. -/
  [periodOneFinite : FiniteDimensional ℝ (C.cellularModel.Cochain periodOneDegree)]
  /-- Finite-dimensionality of selected cellular two-cochains. -/
  [periodTwoFinite : FiniteDimensional ℝ (C.cellularModel.Cochain periodTwoDegree)]
  /-- The selected cellular differential from Čech degree zero to degree one. -/
  periodDifferential : C.cellularModel.Differential periodZeroDegree periodOneDegree
  /-- The selected cellular differential from Čech degree one to degree two. -/
  nerveDifferential : C.cellularModel.Differential periodOneDegree periodTwoDegree
  /-- The real-linear selected cellular Čech coboundary. -/
  periodCoboundary :
    C.cellularModel.Cochain periodZeroDegree →ₗ[ℝ]
      C.cellularModel.Cochain periodOneDegree
  /-- The real-linear selected cellular Čech degree-one coboundary. -/
  nerveCoboundary :
    C.cellularModel.Cochain periodOneDegree →ₗ[ℝ]
      C.cellularModel.Cochain periodTwoDegree
  /-- The selected Čech coboundary is the cellular differential. -/
  periodCoboundary_eq_cellular : ∀ ω,
    periodCoboundary ω =
      C.cellularModel.d periodZeroDegree periodOneDegree periodDifferential ω
  /-- The selected degree-one coboundary is the cellular differential. -/
  nerveCoboundary_eq_cellular : ∀ η,
    nerveCoboundary η =
      C.cellularModel.d periodOneDegree periodTwoDegree nerveDifferential η
  /-- The selected cellular Čech differentials compose to zero. -/
  nerveCoboundary_comp_periodCoboundary : ∀ ω,
    nerveCoboundary (periodCoboundary ω) = 0
  /-- Comparison from selected cellular zero-cochains to the real interval model. -/
  zeroCochainToInterval :
    C.cellularModel.Cochain periodZeroDegree ≃ₗ[ℝ]
      Cohomology.RealIntervalBasisStokes.Cochain 0
  /-- Comparison from selected cellular one-cochains to the real interval model. -/
  oneCochainToInterval :
    C.cellularModel.Cochain periodOneDegree ≃ₗ[ℝ]
      Cohomology.RealIntervalBasisStokes.Cochain 1
  /-- Comparison from selected cellular two-cochains to selected nerve faces. -/
  twoCochainToSelectedFaces :
    C.cellularModel.Cochain periodTwoDegree ≃ₗ[ℝ]
      (Empty → ℝ)
  /-- Comparison from selected cellular zero-chains to the real interval model. -/
  zeroChainToInterval :
    C.cellularModel.Cochain periodZeroDegree ≃ₗ[ℝ]
      Cohomology.RealIntervalBasisStokes.Chain 0
  /-- Comparison from selected cellular one-chains to the real interval model. -/
  oneChainToInterval :
    C.cellularModel.Cochain periodOneDegree ≃ₗ[ℝ]
      Cohomology.RealIntervalBasisStokes.Chain 1
  /-- The cellular selected coboundary transports to the interval coboundary. -/
  periodCoboundary_to_interval : ∀ ω,
    oneCochainToInterval (periodCoboundary ω) =
      Cohomology.RealIntervalBasisStokes.d0 (zeroCochainToInterval ω)
  /-- The selected degree-one cellular coboundary has no selected face component. -/
  nerveCoboundary_to_selectedFaces : ∀ η,
    twoCochainToSelectedFaces (nerveCoboundary η) = 0

attribute [local instance] SelectedPeriodStokesTheoremPackage.periodZeroAddCommGroup
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodOneAddCommGroup
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodTwoAddCommGroup
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodZeroModule
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodOneModule
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodTwoModule
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodZeroFinite
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodOneFinite
attribute [local instance] SelectedPeriodStokesTheoremPackage.periodTwoFinite

namespace SelectedPeriodStokesTheoremPackage

/-- The selected two-chart nerve with its cellular and profile realization. -/
def selectedNerve {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    Cohomology.CoverNerve where
  Chart := Cohomology.RealIntervalBasisStokes.Vertex
  EdgeComponent := Cohomology.RealIntervalBasisStokes.Edge
  FaceComponent := Empty
  edgeLeft
    | Cohomology.IntervalBasisStokes.Edge.interval =>
        Cohomology.IntervalBasisStokes.Vertex.left
  edgeRight
    | Cohomology.IntervalBasisStokes.Edge.interval =>
        Cohomology.IntervalBasisStokes.Vertex.right
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun edge =>
    P.coverRealization edge = C.selectedCover ∧
      C.cellToSite (P.cellRealization Cohomology.IntervalBasisStokes.Vertex.left) =
        P.siteRealization Cohomology.IntervalBasisStokes.Vertex.left ∧
        C.cellToSite (P.cellRealization Cohomology.IntervalBasisStokes.Vertex.right) =
          P.siteRealization Cohomology.IntervalBasisStokes.Vertex.right
  faceTripleOverlapComponent := fun face => Empty.elim face
  edgeOverlapComponent_holds := by
    intro edge
    cases edge
    exact ⟨P.intervalEdge_eq_selectedCover,
      (P.siteRealization_eq_cellToSite Cohomology.IntervalBasisStokes.Vertex.left).symm,
      (P.siteRealization_eq_cellToSite Cohomology.IntervalBasisStokes.Vertex.right).symm⟩
  faceTripleOverlapComponent_holds := fun face => Empty.elim face

/--
The selected nerve complex is the selected cellular Cech complex itself, with
coordinates on the realized charts, overlap component, and selected faces.
-/
noncomputable def selectedNerveComplex {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    Cohomology.FiniteNerveCochainComplex P.selectedNerve where
    k := ℝ
    C0 := C.cellularModel.Cochain P.periodZeroDegree
    C1 := C.cellularModel.Cochain P.periodOneDegree
    C2 := C.cellularModel.Cochain P.periodTwoDegree
    add_C0 := P.periodZeroAddCommGroup
    add_C1 := P.periodOneAddCommGroup
    add_C2 := P.periodTwoAddCommGroup
    module_C0 := P.periodZeroModule
    module_C1 := P.periodOneModule
    module_C2 := P.periodTwoModule
    finiteDimensional_C0 := P.periodZeroFinite
    finiteDimensional_C1 := P.periodOneFinite
    finiteDimensional_C2 := P.periodTwoFinite
    d0 := P.periodCoboundary
    d1 := P.nerveCoboundary
    d1_comp_d0 := P.nerveCoboundary_comp_periodCoboundary
    zeroCochainCoordinates := P.zeroCochainToInterval
    oneCochainCoordinates := P.oneCochainToInterval
    twoCochainCoordinates := P.twoCochainToSelectedFaces
    d0_eq_edgeIncidence := by
      intro cochain edge
      cases edge
      change P.oneCochainToInterval (P.periodCoboundary cochain) .interval =
        P.zeroCochainToInterval cochain .right -
          P.zeroCochainToInterval cochain .left
      simpa [Cohomology.RealIntervalBasisStokes.d0] using
        congrFun (P.periodCoboundary_to_interval cochain) .interval
    d1_eq_faceIncidence := by
      intro _ face
      exact Empty.elim face

/-- The selected nerve's degree-zero map is the transported cellular differential. -/
theorem selectedNerveComplex_d0_matches_cellular {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    ∀ ω, P.selectedNerveComplex.d0 ω =
      C.cellularModel.d P.periodZeroDegree P.periodOneDegree P.periodDifferential ω := by
  intro ω
  exact P.periodCoboundary_eq_cellular ω

/-- The selected nerve's degree-one map is the transported cellular differential. -/
theorem selectedNerveComplex_d1_matches_cellular {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    ∀ η, P.selectedNerveComplex.d1 η =
      C.cellularModel.d P.periodOneDegree P.periodTwoDegree P.nerveDifferential η := by
  intro η
  exact P.nerveCoboundary_eq_cellular η

/-- The selected cellular zero-chain pairing, transported from the interval basis. -/
def cellularPair0 {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C)
    (ω γ : C.cellularModel.Cochain P.periodZeroDegree) : ℝ :=
  Cohomology.RealIntervalBasisStokes.pair0 (P.zeroCochainToInterval ω)
    (P.zeroChainToInterval γ)

/-- The selected cellular one-chain pairing, transported from the interval basis. -/
def cellularPair1 {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C)
    (ω γ : C.cellularModel.Cochain P.periodOneDegree) : ℝ :=
  Cohomology.RealIntervalBasisStokes.pair1 (P.oneCochainToInterval ω)
    (P.oneChainToInterval γ)

/-- The selected cellular chain map, transported from the interval chain map. -/
def cellularBoundary {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C)
    (γ : C.cellularModel.Cochain P.periodOneDegree) :
    C.cellularModel.Cochain P.periodZeroDegree :=
  P.zeroChainToInterval.symm
    (Cohomology.RealIntervalBasisStokes.chain0 (P.oneChainToInterval γ))

/-- The selected finite Period/Stokes formula on cellular cochains and chains. -/
def statement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) : Prop :=
  (∀ vertex,
      P.siteRealization vertex = C.cellToSite (P.cellRealization vertex)) ∧
    P.siteRealization .right = C.selectedSite ∧
      P.coverRealization .interval = C.selectedCover ∧
        Function.Injective P.siteRealization ∧
          ∀ (ω : C.cellularModel.Cochain P.periodZeroDegree)
            (γ : C.cellularModel.Cochain P.periodOneDegree),
            P.cellularPair1
                (C.cellularModel.d P.periodZeroDegree P.periodOneDegree
                  P.periodDifferential ω) γ =
              P.cellularPair0 ω (P.cellularBoundary γ)

/-- Derive the selected Period/Stokes formula from the real finite basis theorem. -/
theorem statement_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    P.statement := by
  refine ⟨P.siteRealization_eq_cellToSite, P.rightChart_eq_selectedSite,
    P.intervalEdge_eq_selectedCover, P.siteRealization_injective, ?_⟩
  intro ω γ
  rw [← P.periodCoboundary_eq_cellular]
  unfold cellularPair1 cellularPair0 cellularBoundary
  rw [P.periodCoboundary_to_interval, P.zeroChainToInterval.apply_symm_apply]
  exact Cohomology.RealIntervalBasisStokes.finiteIntervalStokes_basis _ _

/-- The selected nerve capacity is computed from the same chart and overlap realization. -/
def topologicalCapacityStatement {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) : Prop :=
  (∀ vertex,
      P.siteRealization vertex = C.cellToSite (P.cellRealization vertex)) ∧
    P.siteRealization .right = C.selectedSite ∧
        P.coverRealization .interval = C.selectedCover ∧
        Function.Injective P.siteRealization ∧
          (∀ ω, P.periodCoboundary ω =
            C.cellularModel.d P.periodZeroDegree P.periodOneDegree
              P.periodDifferential ω) ∧
            (∀ η, P.nerveCoboundary η =
              C.cellularModel.d P.periodOneDegree P.periodTwoDegree
                P.nerveDifferential η) ∧
              (∀ ω, P.selectedNerveComplex.d0 ω =
                C.cellularModel.d P.periodZeroDegree P.periodOneDegree
                  P.periodDifferential ω) ∧
                (∀ η, P.selectedNerveComplex.d1 η =
                  C.cellularModel.d P.periodOneDegree P.periodTwoDegree
                    P.nerveDifferential η) ∧
                  (∀ ω edge,
                    P.oneCochainToInterval (P.selectedNerveComplex.d0 ω) edge =
                      P.zeroCochainToInterval ω (P.selectedNerve.edgeRight edge) -
                        P.zeroCochainToInterval ω (P.selectedNerve.edgeLeft edge)) ∧
                    (∀ η face,
                      P.twoCochainToSelectedFaces (P.selectedNerveComplex.d1 η) face =
                        P.oneCochainToInterval η (P.selectedNerve.faceEdge0 face) -
                          P.oneCochainToInterval η (P.selectedNerve.faceEdge1 face) +
                            P.oneCochainToInterval η (P.selectedNerve.faceEdge2 face)) ∧
                      Module.finrank P.selectedNerveComplex.k P.selectedNerveComplex.C1 <=
                        Module.finrank P.selectedNerveComplex.k P.selectedNerveComplex.H1 +
                          Module.finrank P.selectedNerveComplex.k P.selectedNerveComplex.C0 +
                            Module.finrank P.selectedNerveComplex.k P.selectedNerveComplex.C2

/-- Derive selected nerve capacity from its actual incidence cochain complex. -/
theorem topologicalCapacityStatement_holds {M : MeasurementProfile.{u, v}}
    {C : AATGAGACommonFiniteData M} (P : SelectedPeriodStokesTheoremPackage C) :
    P.topologicalCapacityStatement := by
  refine ⟨P.siteRealization_eq_cellToSite, P.rightChart_eq_selectedSite,
    P.intervalEdge_eq_selectedCover, P.siteRealization_injective, P.periodCoboundary_eq_cellular,
    P.nerveCoboundary_eq_cellular, P.selectedNerveComplex_d0_matches_cellular,
    P.selectedNerveComplex_d1_matches_cellular,
    P.selectedNerveComplex.d0_eq_edgeIncidence,
    P.selectedNerveComplex.d1_eq_faceIncidence, ?_⟩
  exact P.selectedNerveComplex.topologicalDebtCapacity_fromComplex

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
