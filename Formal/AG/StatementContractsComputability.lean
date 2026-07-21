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
    Nonempty (Measurement.FiniteAATComputability.{u, v} R D) :=
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
    (obstructionSquareFree : Measurement.FiniteSquareFreeComputationData R)
    (leftSquareFree rightSquareFree : Measurement.FiniteSquareFreeComputationData R)
    (profileRealization :
      Measurement.FiniteAATProfileRealization M R obstructionSquareFree
        leftSquareFree rightSquareFree)
    (leftIdeal :
      letI := R.geometry.coeffCommRing
      Ideal (MvPolynomial M.WitnessVariables M.Coeff))
    (leftIdealEq :
      letI := R.geometry.coeffCommRing
      leftIdeal = leftSquareFree.obstructionIdeal M.Coeff)
    (rightIdeal :
      letI := R.geometry.coeffCommRing
      Ideal (MvPolynomial M.WitnessVariables M.Coeff))
    (rightIdealEq :
      letI := R.geometry.coeffCommRing
      rightIdeal = rightSquareFree.obstructionIdeal M.Coeff)
    (rightResolution :
      letI := R.geometry.coeffCommRing
      Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution
        (MvPolynomial M.WitnessVariables M.Coeff)
        rightIdeal)
    (tensorMatrixAlgorithm :
      letI := R.geometry.coeffCommRing
      Measurement.FiniteTensorMatrixAlgorithm.{max u v, max u v}
        (MvPolynomial M.WitnessVariables M.Coeff)
        leftIdeal
        rightIdeal
        rightResolution)
    (torDegree : Nat)
    (selectedCoordinateCycle :
      letI := R.geometry.coeffCommRing
      Measurement.FiniteTensorMatrixAlgorithm.Cycle.{max u v, max u v}
        tensorMatrixAlgorithm torDegree) :
    Measurement.FiniteAATComputationData M R where
  obstructionSquareFree := obstructionSquareFree
  leftSquareFree := leftSquareFree
  rightSquareFree := rightSquareFree
  profileRealization := profileRealization
  leftIdeal := leftIdeal
  leftIdeal_eq_squareFree := leftIdealEq
  rightIdeal := rightIdeal
  rightIdeal_eq_squareFree := rightIdealEq
  rightResolution := rightResolution
  tensorMatrixAlgorithm := tensorMatrixAlgorithm
  torDegree := torDegree
  selectedCoordinateCycle := selectedCoordinateCycle

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
    (linearSystemSolver :
      letI : Field M.Coeff := coeffField
      Measurement.FiniteLinearSystemSolver.{u, v} M.Coeff)
    (cosetNormalizer :
      letI : Field M.Coeff := coeffField
      Measurement.FiniteLinearCosetNormalizer.{u, v} M.Coeff)
    (model : @Measurement.FiniteDimensionalCechModel M G coeffField) :
    Measurement.FiniteDimensionalCechProcedure M G where
  coeffField := coeffField
  coeffDecidableEq := coeffDecidableEq
  linearSystemSolver := linearSystemSolver
  cosetNormalizer := cosetNormalizer
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

/-! Independent normal-form statement locks. -/

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteSquareFreeComputationData R)
    (k : Type v) [CommRing k]
    (f : MvPolynomial M.WitnessVariables k)
    {exponent : M.WitnessVariables →₀ ℕ}
    (hexponent : exponent ∈ (D.normalForm k f).support) :
    ∀ support ∈ D.forbiddenSupports,
      ¬ Measurement.FiniteSquareFreeComputationData.supportExponent support ≤
        exponent :=
  D.normalForm_reduced k f hexponent

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteSquareFreeComputationData R)
    (k : Type v) [CommRing k]
    (f : MvPolynomial M.WitnessVariables k) :
    D.discardedPart k f ∈ D.obstructionIdeal k :=
  D.discardedPart_mem_obstructionIdeal k f

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteSquareFreeComputationData R)
    (k : Type v) [CommRing k]
    {f g : MvPolynomial M.WitnessVariables k}
    (hsub : f - g ∈ D.obstructionIdeal k) :
    D.normalForm k f = D.normalForm k g :=
  D.normalForm_eq_of_sub_mem k hsub

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteSquareFreeComputationData R)
    (k : Type v) [CommRing k]
    (q : MvPolynomial M.WitnessVariables k ⧸ D.obstructionIdeal k) :
    Ideal.Quotient.mk (D.obstructionIdeal k) (D.quotientNormalForm k q) = q :=
  D.quotientNormalForm_correct k q

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteSquareFreeComputationData R)
    (k : Type v) [CommRing k]
    (q : MvPolynomial M.WitnessVariables k ⧸ D.obstructionIdeal k) :
    ∀ exponent ∈ (D.quotientNormalForm k q).support,
      ∀ support ∈ D.forbiddenSupports,
        ¬ Measurement.FiniteSquareFreeComputationData.supportExponent support ≤
          exponent :=
  D.quotientNormalForm_reduced k q

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteSquareFreeComputationData R)
    (k : Type v) [CommRing k]
    (q : MvPolynomial M.WitnessVariables k ⧸ D.obstructionIdeal k)
    (f : MvPolynomial M.WitnessVariables k)
    (hclass : Ideal.Quotient.mk (D.obstructionIdeal k) f = q)
    (hreduced : ∀ exponent ∈ f.support,
      ∀ support ∈ D.forbiddenSupports,
        ¬ Measurement.FiniteSquareFreeComputationData.supportExponent support ≤
          exponent) :
    D.quotientNormalForm k q = f :=
  D.quotientNormalForm_unique k q f hclass hreduced

/-! Independent generic support-relation statement locks. -/

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteAATComputationData M R)
    (cycle : D.tensorMatrixAlgorithm.Cycle D.torDegree)
    (hzero : D.coordinateHomologyClassOf cycle = 0) :
    D.classSupportOf cycle = ∅ :=
  D.classSupportOf_eq_empty_of_class_eq_zero cycle hzero

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteAATComputationData M R)
    (cycle : D.tensorMatrixAlgorithm.Cycle D.torDegree)
    (hnonzero : D.coordinateHomologyClassOf cycle ≠ 0) :
    D.classSupportOf cycle = D.cycleSupportOf cycle :=
  D.classSupportOf_eq_cycleSupportOf_of_class_ne_zero cycle hnonzero

example {M : Measurement.MeasurementProfile.{u, v}}
    {R : Measurement.FiniteMeasurementRegime M}
    (D : Measurement.FiniteAATComputationData M R)
    {support : Finset M.WitnessVariables}
    (h : D.ComputedConflictSupport 0 support) : support = ∅ :=
  D.computedConflictSupport_zero h

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
    (n : Nat) (j : D.rightResolution.BasisIndex (n + 1))
    (e : M.WitnessVariables) :
    letI := R.witnessDecidableEq
    letI := R.geometry.coeffCommRing
    e ∈ D.resolutionBasisSupport (n + 1) j ↔
      ∃ i : D.rightResolution.BasisIndex n,
        D.rightResolution.differentialMatrix n i j ≠ 0 ∧
          (e ∈ Measurement.FiniteAATComputationData.polynomialVariableSupport
              M.WitnessVariables M.Coeff
              (D.rightResolution.differentialMatrix n i j) ∨
            e ∈ D.resolutionBasisSupport n i) :=
  D.mem_resolutionBasisSupport_succ_iff n j e

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    letI := R.witnessDecidableEq
    C.conflictSupport = D.selectedClassSupport :=
  C.conflictSupport_eq_selectedClassSupport

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    letI := R.witnessDecidableEq
    letI := R.geometry.coeffCommRing
    C.selectedCoordinateHomologyClass = 0 -> C.conflictSupport = ∅ :=
  C.conflictSupport_eq_empty_of_selectedCoordinateHomologyClass_eq_zero

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    letI := R.witnessDecidableEq
    letI := R.geometry.coeffCommRing
    C.selectedConflictClass = 0 -> C.conflictSupport = ∅ :=
  C.conflictSupport_eq_empty_of_selectedConflictClass_eq_zero

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    letI := R.geometry.coeffCommRing
    ∀ n (x : D.tensorMatrixAlgorithm.Cycle n),
      C.torCoordinateClassZeroDecision n x = true ↔
        D.tensorMatrixAlgorithm.classOfCycle n x = 0 := by
  intro n x
  exact C.torCoordinateClassZeroDecision_correct n x

example :
    Nonempty
      (Measurement.FiniteAATComputability.{0, 0}
        Measurement.computabilityFiniteMeasurementRegime
        Measurement.finiteComputabilityExampleData) :=
  Measurement.finiteComputabilityExample_verified

example :
    Measurement.finiteComputabilityExamplePackage.coefficientComputation.route =
      Measurement.CoefficientComputationRoute.effectiveFinitelyPresented :=
  Measurement.finiteComputabilityExample_effectiveRouteSelected

example :
    (Measurement.CechComputationProcedure.finiteDimensional
      Measurement.finiteDimensionalMatrixCechProcedure).route =
        Measurement.CoefficientComputationRoute.finiteDimensionalLinearAlgebra :=
  Measurement.finiteDimensionalMatrixRoute_fires

example :
    Measurement.finiteDimensionalMatrixComputabilityPackage.coefficientComputation.route =
      Measurement.CoefficientComputationRoute.finiteDimensionalLinearAlgebra :=
  Measurement.finiteDimensionalMatrixFullRoute_fires

example : Finite Measurement.finiteDimensionalMatrixProfile.Coeff :=
  Measurement.finiteDimensionalMatrixCoeff_finite

example (n : Nat) :
    letI : Field Measurement.finiteDimensionalMatrixProfile.Coeff :=
      Measurement.finiteDimensionalMatrixCoeffField
    Module.Finite Measurement.finiteDimensionalMatrixProfile.Coeff
      (Measurement.finiteDimensionalMatrixCechModel.Cohomology n) :=
  Measurement.finiteDimensionalMatrixCohomology_moduleFinite n

example (n : Nat) :
    letI : Field Measurement.finiteDimensionalMatrixProfile.Coeff :=
      Measurement.finiteDimensionalMatrixCoeffField
    Nonempty
      (Measurement.finiteDimensionalMatrixCechModel.Cohomology n ≃
        Measurement.finiteDimensionalMatrixGeometry.CechHn n) :=
  ⟨Measurement.finiteDimensionalMatrixCohomologyEquivCanonical n⟩

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
    Measurement.finiteComputabilityExamplePackage.conflictSupport =
      Measurement.forbiddenSupportPFinset :=
  Measurement.finiteComputabilityExample_combinatoricsRoute

example :
    Measurement.finiteDimensionalMatrixComputabilityPackage.selectedCoordinateCycle ≠ 0 ∧
      Measurement.finiteDimensionalMatrixComputabilityPackage.selectedCoordinateHomologyClass ≠ 0 ∧
      Measurement.finiteDimensionalMatrixComputabilityPackage.selectedTensorHomologyClass ≠ 0 ∧
      Measurement.finiteDimensionalMatrixComputabilityPackage.selectedTorClass ≠ 0 ∧
      Measurement.finiteDimensionalMatrixComputabilityPackage.selectedConflictClass ≠ 0 :=
  Measurement.finiteDimensionalMatrixFullRoute_nonzero

example :
    Measurement.finiteComputabilityExamplePackage.selectedCoordinateCycle ≠ 0 ∧
      Measurement.finiteComputabilityExamplePackage.selectedCoordinateHomologyClass ≠ 0 ∧
      Measurement.finiteComputabilityExamplePackage.selectedTensorHomologyClass ≠ 0 ∧
      Measurement.finiteComputabilityExamplePackage.selectedTorClass ≠ 0 ∧
      Measurement.finiteComputabilityExamplePackage.selectedConflictClass ≠ 0 :=
  Measurement.finiteComputabilityExampleFullRoute_nonzero

/-! The six nondegenerate fixture locks required by the final review. -/

example :
    (1 + MvPolynomial.X Measurement.SquareFreeSupportVertex.p :
        MvPolynomial Measurement.SquareFreeSupportVertex (ZMod 2)) ≠ 1 ∧
      Measurement.tinyLeftSquareFreeData.normalForm (ZMod 2)
          (1 + MvPolynomial.X Measurement.SquareFreeSupportVertex.p) =
        Measurement.tinyLeftSquareFreeData.normalForm (ZMod 2) 1 :=
  Measurement.tinyLeftSquareFree_normalForm_identifies_distinct_lifts

example :
    Measurement.finiteDimensionalNonzeroH1Class ≠
        Measurement.finiteDimensionalNonzeroH1Geometry.zeroClass 1 ∧
      Measurement.finiteDimensionalNonzeroH1Geometry.classOfCocycle 1
          (Measurement.finiteDimensionalNonzeroH1ComputationProcedure
            |>.quotientRepresentative 1
              Measurement.finiteDimensionalNonzeroH1Class) =
        Measurement.finiteDimensionalNonzeroH1Class :=
  Measurement.finiteDimensionalNonzeroH1Representative

example (n : Nat)
    (h : Measurement.computabilityFiniteMeasurementRegime.geometry.CechHn n) :
    Measurement.computabilityFiniteMeasurementRegime.geometry.classOfCocycle n
        (Measurement.finiteComputabilityExamplePackage.cocycleRepresentative n h) = h :=
  Measurement.finiteComputabilityExample_genericRepresentative_correct n h

example :
    (Measurement.FiniteObstructionIdealHandle.selected ≠ .alternate) ∧
      (Measurement.FiniteLawHandle.left ≠ .right) := by
  decide

example :
    Measurement.finiteComputabilityExampleData.selectedConflictClass ≠ 0 ∧
      Measurement.LawConflictMeasurement.selectedClassSupportReading
        Measurement.finiteComputabilityConflictPackage.lawConflictMeasurement :=
  Measurement.finiteComputabilityConflictPackage_nonzero_and_supportReading

example :
    Measurement.finiteComputabilityExampleData.leftIdeal ≠ ⊤ ∧
      Measurement.finiteComputabilityExampleData.rightIdeal ≠ ⊤ ∧
      Measurement.finiteComputabilityExampleData.torDegree = 1 ∧
      Measurement.finiteComputabilityExampleData.selectedConflictClass ≠ 0 ∧
      Measurement.LawConflictMeasurement.selectedClassSupportReading
        Measurement.finiteComputabilityConflictPackage.lawConflictMeasurement :=
  Measurement.finiteComputabilityConflictPackage_proper_degree_one_nonzero_and_supportReading

example {support : Finset Measurement.SquareFreeSupportVertex}
    (h : Measurement.LawConflictMeasurement.conflictSupport
      Measurement.finiteComputabilityConflictPackage.lawConflictMeasurement
        Measurement.finiteComputabilityMeasuredZeroConflict support) :
    support = ∅ :=
  Measurement.finiteComputabilityConflictPackage_zero_support h

example :
    Measurement.NontrivialTorFixture.principalFiniteFreeResolutionV2.length = 1 :=
  Measurement.NontrivialTorFixture.nontrivialFiniteChainTorRoute_fires.1

example :
    (Measurement.NontrivialTorFixture.principalFiniteFreeResolutionV2
      |>.coordinateDifferential 0) ≠ 0 :=
  Measurement.NontrivialTorFixture.nontrivialFiniteChainTorRoute_fires.2.1

example :
    Matrix.mulVec
      (Measurement.NontrivialTorFixture.principalTensorDifferentialMatrixV2 0)
      Measurement.NontrivialTorFixture.yCoordinateCycleV2 = 0 :=
  Measurement.NontrivialTorFixture.yCoordinateCycleV2_is_cycle

example :
    ¬ ∃ b :
        Measurement.NontrivialTorFixture.principalFiniteFreeResolutionV2.BasisIndex 2 →
          Derived.Counterexample.SharedWitnessCoord.R2 ⧸
            Derived.Counterexample.SharedWitnessCoord.idealU (ZMod 2),
      Matrix.mulVec
          (Measurement.NontrivialTorFixture.principalTensorDifferentialMatrixV2 1) b =
        Measurement.NontrivialTorFixture.yCoordinateCycleV2 :=
  Measurement.NontrivialTorFixture.yCoordinateCycleV2_not_boundary

end AAT.AG
