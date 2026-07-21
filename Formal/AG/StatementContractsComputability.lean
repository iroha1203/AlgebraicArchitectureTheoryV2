import Formal.AG.Measurement.Computability
import Formal.AG.Measurement.Examples

noncomputable section

namespace AAT.AG

universe u v

/-!
Fixed statement contracts for Part VIII, theorem 4.2.

The generic contract accepts the generated finite regime plus selected
square-free and finite-resolution data.  The selected coefficient branch,
Čech reduction, and verdicts are conclusions of
`Measurement.finiteAATComputability`.
-/

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R) :
    Nonempty (Measurement.FiniteAATComputability R D) :=
  Measurement.finiteAATComputability R D

/-!
The examples below lock the constructor surfaces used by the fixed theorem.
They intentionally spell out primitive inputs and central output types so a
new premise, removed output, or conclusion moved into an input structure makes
this file fail to elaborate.
-/

example {M : Measurement.MeasurementProfile.{u, v}}
    (geometry : Measurement.FiniteMeasurementGeometry M)
    (coeffDecidableEq : DecidableEq M.Coeff)
    (effCoeff : Measurement.EffCoeff M geometry)
    (witnessFintype : Fintype M.WitnessVariables)
    (witnessDecidableEq : DecidableEq M.WitnessVariables) :
    Measurement.FiniteMeasurementRegime M where
  geometry := geometry
  coeffDecidableEq := coeffDecidableEq
  effCoeff := effCoeff
  witnessFintype := witnessFintype
  witnessDecidableEq := witnessDecidableEq

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    (profileInterface : M.EffCoeff)
    (selectedDegree : Nat)
    (domainClass : M.Domain -> G.CechHn selectedDegree)
    (cechProcedure : Measurement.CechComputationProcedure M G)
    (verdictProcedure :
      Measurement.VerdictProcedure M G selectedDegree domainClass cechProcedure) :
    Measurement.EffCoeff M G where
  profileInterface := profileInterface
  selectedDegree := selectedDegree
  domainClass := domainClass
  cechProcedure := cechProcedure
  verdictProcedure := verdictProcedure

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    {selectedDegree : Nat}
    {domainClass : M.Domain -> G.CechHn selectedDegree}
    {cechProcedure : Measurement.CechComputationProcedure M G}
    (availability : M.Domain -> Measurement.VerdictAvailability)
    (measuredZero : ∀ alpha, availability alpha = .measured ->
      cechProcedure.zeroDecision selectedDegree (domainClass alpha) = true ->
      M.InScope alpha ∧ M.Zero alpha)
    (measuredNonzero : ∀ alpha, availability alpha = .measured ->
      cechProcedure.zeroDecision selectedDegree (domainClass alpha) = false ->
      M.InScope alpha ∧ M.NonZero alpha)
    (unmeasured : ∀ alpha, availability alpha = .unmeasured -> M.OutOfScope alpha)
    (unknown : ∀ alpha, availability alpha = .unknown ->
      M.InScope alpha ∧ M.Undecided alpha)
    (notComputed : ∀ alpha, availability alpha = .notComputed ->
      M.NotRunOrUnavailable alpha)
    (method : ∀ alpha, M.SelectedMethod alpha)
    (certificate : ∀ alpha, M.CertRef alpha) :
    Measurement.VerdictProcedure M G selectedDegree domainClass cechProcedure where
  availability := availability
  measured_zero_sound := measuredZero
  measured_nonzero_sound := measuredNonzero
  unmeasured_sound := unmeasured
  unknown_sound := unknown
  notComputed_sound := notComputed
  method := method
  certificate := certificate

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (leftSquareFree rightSquareFree : Measurement.FiniteSquareFreeComputationData R)
    (selectedLeft :
      { support : Finset M.WitnessVariables //
        support ∈ leftSquareFree.forbiddenSupports })
    (selectedRight :
      { support : Finset M.WitnessVariables //
        support ∈ rightSquareFree.forbiddenSupports })
    (rightResolution :
      letI := R.geometry.coeffCommRing
      Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution
        (MvPolynomial M.WitnessVariables M.Coeff)
        (rightSquareFree.obstructionIdeal M.Coeff))
    (torDegree : Nat)
    (selectedConflictClass :
      letI := R.witnessDecidableEq
      letI := R.geometry.coeffCommRing
      (Derived.Intersection.canonicalSelectedTorBridge
        (MvPolynomial M.WitnessVariables M.Coeff)
        (leftSquareFree.obstructionIdeal M.Coeff)
        (rightSquareFree.obstructionIdeal M.Coeff)).LawConflict torDegree) :
    Measurement.FiniteAATComputationData M R where
  leftSquareFree := leftSquareFree
  rightSquareFree := rightSquareFree
  selectedLeftConflictGenerator := selectedLeft
  selectedRightConflictGenerator := selectedRight
  rightResolution := rightResolution
  torDegree := torDegree
  selectedConflictClass := selectedConflictClass

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    (cochainFintype : ∀ n, Fintype (G.CechCochain n))
    (cochainDecidableEq : ∀ n, DecidableEq (G.CechCochain n))
    (cocycleFintype : ∀ n, Fintype (G.CechCocycle n))
    (cohomologyDecidableEq : ∀ n, DecidableEq (G.CechHn n)) :
    Measurement.FiniteCarrierCechPresentation M G where
  cochainFintype := cochainFintype
  cochainDecidableEq := cochainDecidableEq
  cocycleFintype := cocycleFintype
  cohomologyDecidableEq := cohomologyDecidableEq

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    (kernel : ∀ n, G.CechCochain n -> Bool)
    (kernelCorrect : ∀ n c, kernel n c = true ↔ G.differentialHom n c = 0)
    (image : ∀ n, G.CechCochain (n + 1) -> Bool)
    (imageCorrect : ∀ n c, image n c = true ↔
      ∃ b : G.CechCochain n, G.differentialHom n b = c)
    (quotientRepresentative : ∀ n, G.CechHn n -> G.CechCocycle n)
    (quotientRepresentativeCorrect : ∀ n h,
      G.classOfCocycle n (quotientRepresentative n h) = h)
    (zeroDecision : ∀ n, G.CechHn n -> Bool)
    (zeroDecisionCorrect : ∀ n h,
      zeroDecision n h = true ↔ h = G.zeroClass n) :
    Measurement.EffectiveFinitelyPresentedCechProcedure M G where
  kernel := kernel
  kernel_correct := kernelCorrect
  image := image
  image_correct := imageCorrect
  quotientRepresentative := quotientRepresentative
  quotientRepresentative_correct := quotientRepresentativeCorrect
  zeroDecision := zeroDecision
  zeroDecision_correct := zeroDecisionCorrect

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    [Field M.Coeff]
    (CochainSpace : Nat -> Type u)
    (CochainIndex : Nat -> Type u)
    (cochainIndexFintype : ∀ n, Fintype (CochainIndex n))
    (cochainIndexDecidableEq : ∀ n, DecidableEq (CochainIndex n))
    (cochainAddCommGroup : ∀ n, AddCommGroup (CochainSpace n))
    (cochainModule : ∀ n, Module M.Coeff (CochainSpace n))
    (cochainBasis : ∀ n,
      letI := cochainAddCommGroup n
      letI := cochainModule n
      Module.Basis (CochainIndex n) M.Coeff (CochainSpace n))
    (cochainEquivCanonical : ∀ n,
      CochainSpace n ≃+
        Site.FinitePosetCechCochain G.coefficientRegime n)
    (cochainEquivCanonicalSmul :
      ∀ (n : Nat) (r : M.Coeff) (c : CochainSpace n),
        letI := G.coeffCommRing
        letI := G.cochainAddCommGroup n
        letI := G.cochainModule n
        cochainEquivCanonical n (r • c) = r • cochainEquivCanonical n c)
    (differentialLinear : ∀ n,
      letI := cochainAddCommGroup n
      letI := cochainAddCommGroup (n + 1)
      letI := cochainModule n
      letI := cochainModule (n + 1)
      CochainSpace n →ₗ[M.Coeff] CochainSpace (n + 1))
    (differentialEqCanonical : ∀ n c,
      cochainEquivCanonical (n + 1) (differentialLinear n c) =
        G.cechComplex.differential n (cochainEquivCanonical n c))
    (differentialComp : ∀ n c,
      differentialLinear (n + 1) (differentialLinear n c) = 0)
    (differentialMatrix : ∀ n,
      Matrix (CochainIndex (n + 1)) (CochainIndex n) M.Coeff)
    (differentialMatrixCorrect : ∀ n,
      LinearMap.toMatrix (cochainBasis n) (cochainBasis (n + 1))
        (differentialLinear n) = differentialMatrix n) :
    Measurement.FiniteDimensionalCechModel M G where
  CochainSpace := CochainSpace
  CochainIndex := CochainIndex
  cochainIndexFintype := cochainIndexFintype
  cochainIndexDecidableEq := cochainIndexDecidableEq
  cochainAddCommGroup := cochainAddCommGroup
  cochainModule := cochainModule
  cochainBasis := cochainBasis
  cochainEquivCanonical := cochainEquivCanonical
  cochainEquivCanonical_smul := cochainEquivCanonicalSmul
  differentialLinear := differentialLinear
  differential_eq_canonical := differentialEqCanonical
  differential_comp := differentialComp
  differentialMatrix := differentialMatrix
  differentialMatrix_correct := differentialMatrixCorrect

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    (coeffField : Field M.Coeff)
    (coeffDecidableEq : DecidableEq M.Coeff)
    (model : @Measurement.FiniteDimensionalCechModel M G coeffField) :
    Measurement.FiniteDimensionalCechProcedure M G where
  coeffField := coeffField
  coeffDecidableEq := coeffDecidableEq
  model := model

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    (P : Measurement.FiniteDimensionalCechProcedure M G) :
    Measurement.CechComputationProcedure M G :=
  .finiteDimensional P

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    (P : Measurement.FiniteDimensionalCechProcedure M G)
    (n : Nat) (h : G.CechHn n) :
    P.zeroDecision n h = true ↔ h = G.zeroClass n :=
  P.zeroDecision_correct n h

example {M : Measurement.MeasurementProfile.{u, v}}
    {G : Measurement.FiniteMeasurementGeometry M}
    (P : Measurement.EffectiveFinitelyPresentedCechProcedure M G) :
    Measurement.CechComputationProcedure M G :=
  .effectiveFinitelyPresented P

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    Measurement.FiniteAATComputability R D where
  siteObjFintype := C.siteObjFintype
  coverFintype := C.coverFintype
  cochainModule := C.cochainModule
  coefficientComputation := C.coefficientComputation
  verdict := C.verdict
  verdictData := C.verdictData
  verdict_eq := C.verdict_eq
  leftGenerators := C.leftGenerators
  leftGenerator_mem := C.leftGenerator_mem
  leftIdeal_eq_span_generators := C.leftIdeal_eq_span_generators
  leftIdealMembership := C.leftIdealMembership
  leftIdealMembership_correct := C.leftIdealMembership_correct
  rightGenerators := C.rightGenerators
  rightGenerator_mem := C.rightGenerator_mem
  rightIdeal_eq_span_generators := C.rightIdeal_eq_span_generators
  rightIdealMembership := C.rightIdealMembership
  rightIdealMembership_correct := C.rightIdealMembership_correct
  leftMinimalForbiddenSupports := C.leftMinimalForbiddenSupports
  rightMinimalForbiddenSupports := C.rightMinimalForbiddenSupports
  leftStanleyReisner := C.leftStanleyReisner
  rightStanleyReisner := C.rightStanleyReisner
  torComparison := C.torComparison
  torResolutionLength := C.torResolutionLength
  torBasisIndex := C.torBasisIndex
  torBasisIndexFintype := C.torBasisIndexFintype
  torTermIsoFree := C.torTermIsoFree
  torSupported_le_length := C.torSupported_le_length
  torDifferentialMatrix := C.torDifferentialMatrix
  torDifferentialMatrix_correct := C.torDifferentialMatrix_correct
  torTensorComplex := C.torTensorComplex
  torTensorComplex_eq := C.torTensorComplex_eq
  selectedConflictClass := C.selectedConflictClass
  selectedTorClass := C.selectedTorClass
  selectedTensorHomologyClass := C.selectedTensorHomologyClass
  conflictSupport := C.conflictSupport
  conflictSupport_eq_union := C.conflictSupport_eq_union

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    letI := R.geometry.coeffCommRing
    ∀ n,
      Matrix (D.rightResolution.BasisIndex n)
        (D.rightResolution.BasisIndex (n + 1))
        (MvPolynomial M.WitnessVariables M.Coeff) :=
  C.torDifferentialMatrix

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    letI := R.witnessDecidableEq
    C.conflictSupport =
      D.selectedLeftConflictGenerator.1 ∪ D.selectedRightConflictGenerator.1 :=
  C.conflictSupport_eq_union

example :
    Nonempty
      (Measurement.FiniteAATComputability
        Measurement.computabilityFiniteMeasurementRegime
        Measurement.finiteComputabilityExampleData) :=
  Measurement.finiteComputabilityExample_verified

example :
    Measurement.finiteComputabilityExamplePackage.coefficientComputation.route =
      Measurement.CoefficientComputationRoute.effectiveFinitelyPresented :=
  Measurement.finiteComputabilityExample_effectiveRouteSelected

example :
    (Measurement.CechComputationProcedure.finiteDimensional
      Measurement.finiteDimensionalRationalCechProcedure).route =
        Measurement.CoefficientComputationRoute.finiteDimensionalLinearAlgebra :=
  Measurement.finiteDimensionalRationalRoute_fires

example :
    Measurement.finiteDimensionalRationalComputabilityPackage.coefficientComputation.route =
      Measurement.CoefficientComputationRoute.finiteDimensionalLinearAlgebra :=
  Measurement.finiteDimensionalRationalFullRoute_fires

example : Infinite Measurement.finiteDimensionalRationalProfile.Coeff :=
  Measurement.finiteDimensionalRationalCoeff_infinite

example (n : Nat) :
    letI : Field Measurement.finiteDimensionalRationalProfile.Coeff :=
      Measurement.finiteDimensionalRationalCoeffField
    Module.Finite Measurement.finiteDimensionalRationalProfile.Coeff
      (Measurement.finiteDimensionalRationalCechModel.Cohomology n) :=
  Measurement.finiteDimensionalRationalCohomology_moduleFinite n

example (n : Nat) :
    letI : Field Measurement.finiteDimensionalRationalProfile.Coeff :=
      Measurement.finiteDimensionalRationalCoeffField
    Nonempty
      (Measurement.finiteDimensionalRationalCechModel.Cohomology n ≃
        Measurement.finiteDimensionalRationalGeometry.CechHn n) :=
  ⟨Measurement.finiteDimensionalRationalCohomologyEquivCanonical n⟩

example :
    Measurement.finiteComputabilityZeroCochain ≠
      Measurement.finiteComputabilityOneCochain :=
  Measurement.finiteComputabilityCochain_nondegenerate

example :
    ∀ n (h : Measurement.computabilityFiniteMeasurementRegime.geometry.CechHn n),
      Measurement.computabilityFiniteMeasurementRegime.geometry.classOfCocycle n
        (Measurement.finiteComputabilityEffectiveCechProcedure.quotientRepresentative
          n h) = h :=
  Measurement.finiteComputabilityExample_effectiveProcedureRoute.2.2

example :
    Measurement.finiteComputabilityExampleData.conflictSupport =
      Measurement.forbiddenSupportPQFinset ∪
        Measurement.forbiddenSupportQRFinset :=
  Measurement.finiteComputabilityExample_combinatoricsRoute

example :
    Measurement.NontrivialTorFixture.principalFiniteFreeResolutionV2.length = 1 :=
  Measurement.NontrivialTorFixture.nontrivialFiniteChainTorRoute_fires.1

example :
    (Measurement.NontrivialTorFixture.principalFiniteFreeResolutionV2
      |>.coordinateDifferential 0) ≠ 0 :=
  Measurement.NontrivialTorFixture.nontrivialFiniteChainTorRoute_fires.2.1

end AAT.AG
