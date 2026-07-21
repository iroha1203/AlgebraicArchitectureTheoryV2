import Formal.AG.Measurement.Computability
import Formal.AG.Measurement.Examples

noncomputable section

namespace AAT.AG

universe u v

namespace Measurement

/--
Independent fixed output contract for Part VIII theorem 4.2.  This type does
not mention `FiniteAATComputability`; premise additions, output removal, or
moving an output into a production input therefore break the conversion gate
below instead of changing this statement by definitional equality.
-/
structure FiniteAATFixedOutputContract {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M)
    (D : FiniteAATComputationData M R) : Type (max (u + 1) (v + 1)) where
  /-- Actual finite profile site-object carrier. -/
  siteObjFintype : Fintype M.SiteObj
  /-- Actual finite profile cover carrier. -/
  coverFintype : Fintype M.Cover
  /-- Every generated Čech cochain degree is a coefficient module. -/
  cochainModule :
    ∀ n,
      letI := R.geometry.coeffCommRing
      letI := R.geometry.cochainAddCommGroup n
      Module M.Coeff (R.geometry.CechCochain n)
  /-- Selected finite-dimensional or effective finitely-presented Čech reduction. -/
  coefficientComputation : CechComputationProcedure M R.geometry
  /-- Canonical cocycle representative exposed uniformly by the selected Čech
  computation route. -/
  cocycleRepresentative :
    ∀ n, R.geometry.CechHn n -> R.geometry.CechCocycle n
  /-- Every exposed cocycle represents exactly its requested canonical class. -/
  cocycleRepresentative_correct :
    ∀ n h,
      R.geometry.classOfCocycle n (cocycleRepresentative n h) = h
  /-- Certified five-state verdict computed from actual Čech classes. -/
  verdict : ∀ alpha : M.Domain, MeasurementVerdict M alpha
  /-- Procedure result together with the selected method/certificate channels. -/
  verdictData : ∀ alpha : M.Domain, VerdictData M alpha
  /-- The exposed verdict is exactly the verdict produced by `verdictData`. -/
  verdict_eq : ∀ alpha, verdict alpha = (verdictData alpha).verdict
  /-- The profile-selected obstruction object is the actual coefficient
  sheaf used by the canonical Čech computation. -/
  profileObstructionObject_realizes :
    D.profileRealization.realizeObstructionObject
        D.profileRealization.selectedObstructionObject =
      R.geometry.obstructionSheaf
  /-- The profile-selected obstruction-ideal handle realizes the generated
  square-free obstruction ideal used by this computation. -/
  profileObstructionIdeal_realizes :
    letI := R.geometry.coeffCommRing
    D.profileRealization.realizeObstructionIdeal
        D.profileRealization.selectedObstructionIdeal =
      D.obstructionIdeal
  /-- The profile-selected left-law handle realizes the concrete left ideal
  used in the tensor computation. -/
  profileLeftLaw_realizes :
    letI := R.geometry.coeffCommRing
    D.profileRealization.realizeLawIdeal
        D.profileRealization.selectedLeftLaw = D.leftIdeal
  /-- The profile-selected right-law handle realizes the concrete ideal
  resolved by the selected finite-free resolution. -/
  profileRightLaw_realizes :
    letI := R.geometry.coeffCommRing
    D.profileRealization.realizeLawIdeal
        D.profileRealization.selectedRightLaw = D.rightIdeal
  /-- Finite monomial presentation of the selected obstruction ideal. -/
  obstructionGenerators :
    letI := R.geometry.coeffCommRing
    Finset (MvPolynomial M.WitnessVariables M.Coeff)
  /-- Every obstruction generator belongs to the selected obstruction ideal. -/
  obstructionGenerator_mem :
    letI := R.geometry.coeffCommRing
    ∀ {f}, f ∈ obstructionGenerators -> f ∈ D.obstructionIdeal
  /-- The finite obstruction generator list presents the selected ideal. -/
  obstructionIdeal_eq_span_generators :
    letI := R.geometry.coeffCommRing
    D.obstructionIdeal = Ideal.span (obstructionGenerators : Set _)
  /-- Obstruction ideal-membership decision derived from the finite monomial
  family. -/
  obstructionIdealMembership :
    letI := R.geometry.coeffCommRing
    MvPolynomial M.WitnessVariables M.Coeff -> Bool
  /-- Obstruction ideal-membership is decided correctly for every polynomial. -/
  obstructionIdealMembership_correct :
    letI := R.geometry.coeffCommRing
    ∀ f, obstructionIdealMembership f = true ↔ f ∈ D.obstructionIdeal
  /-- Computed inclusion-minimal obstruction supports. -/
  obstructionMinimalForbiddenSupports : Finset (Finset M.WitnessVariables)
  /-- The exposed obstruction list is the actual finite minimal-support
  computation. -/
  obstructionMinimalForbiddenSupports_eq :
    obstructionMinimalForbiddenSupports =
      D.obstructionSquareFree.minimalForbiddenSupports
  /-- Exact membership characterization for minimal obstruction supports. -/
  obstructionMinimalForbiddenSupports_spec :
    ∀ support, support ∈ obstructionMinimalForbiddenSupports ↔
      support ∈ D.obstructionSquareFree.forbiddenSupports ∧
        ∀ candidate ∈ D.obstructionSquareFree.forbiddenSupports,
          candidate ⊆ support -> support ⊆ candidate
  /-- The profile-selected obstruction ideal equals the Stanley--Reisner
  ideal generated by the same finite family. -/
  obstructionStanleyReisner :
    letI := R.geometry.coeffCommRing
    D.obstructionIdeal =
      D.obstructionSquareFree.stanleyReisnerIdeal M.Coeff
  /-- Finite left monomial presentation. -/
  leftGenerators :
    letI := R.geometry.coeffCommRing
    Finset (MvPolynomial M.WitnessVariables M.Coeff)
  /-- Every left generator belongs to the generated left ideal. -/
  leftGenerator_mem :
    letI := R.geometry.coeffCommRing
    ∀ {f}, f ∈ leftGenerators -> f ∈ D.leftIdeal
  /-- The finite left generator list presents the selected left ideal. -/
  leftIdeal_eq_span_generators :
    letI := R.geometry.coeffCommRing
    D.leftIdeal = Ideal.span (leftGenerators : Set _)
  /-- Left ideal-membership decision derived from the finite monomial family. -/
  leftIdealMembership :
    letI := R.geometry.coeffCommRing
    MvPolynomial M.WitnessVariables M.Coeff -> Bool
  /-- Left ideal-membership procedure is correct for every polynomial. -/
  leftIdealMembership_correct :
    letI := R.geometry.coeffCommRing
    ∀ f, leftIdealMembership f = true ↔ f ∈ D.leftIdeal
  /-- Finite right monomial presentation. -/
  rightGenerators :
    letI := R.geometry.coeffCommRing
    Finset (MvPolynomial M.WitnessVariables M.Coeff)
  /-- Every right generator belongs to the generated right ideal. -/
  rightGenerator_mem :
    letI := R.geometry.coeffCommRing
    ∀ {f}, f ∈ rightGenerators -> f ∈ D.rightIdeal
  /-- The finite right generator list presents the selected right ideal. -/
  rightIdeal_eq_span_generators :
    letI := R.geometry.coeffCommRing
    D.rightIdeal = Ideal.span (rightGenerators : Set _)
  /-- Right ideal-membership decision derived from the finite monomial family. -/
  rightIdealMembership :
    letI := R.geometry.coeffCommRing
    MvPolynomial M.WitnessVariables M.Coeff -> Bool
  /-- Right ideal-membership procedure is correct for every polynomial. -/
  rightIdealMembership_correct :
    letI := R.geometry.coeffCommRing
    ∀ f, rightIdealMembership f = true ↔ f ∈ D.rightIdeal
  /-- Computed left minimal forbidden supports. -/
  leftMinimalForbiddenSupports : Finset (Finset M.WitnessVariables)
  /-- Computed right minimal forbidden supports. -/
  rightMinimalForbiddenSupports : Finset (Finset M.WitnessVariables)
  /-- The exposed left list is the actual finite minimal-support computation. -/
  leftMinimalForbiddenSupports_eq :
    leftMinimalForbiddenSupports =
      D.leftSquareFree.minimalForbiddenSupports
  /-- The exposed right list is the actual finite minimal-support computation. -/
  rightMinimalForbiddenSupports_eq :
    rightMinimalForbiddenSupports =
      D.rightSquareFree.minimalForbiddenSupports
  /-- Exact membership characterization for the left minimal supports. -/
  leftMinimalForbiddenSupports_spec :
    ∀ support, support ∈ leftMinimalForbiddenSupports ↔
      support ∈ D.leftSquareFree.forbiddenSupports ∧
        ∀ candidate ∈ D.leftSquareFree.forbiddenSupports,
          candidate ⊆ support -> support ⊆ candidate
  /-- Exact membership characterization for the right minimal supports. -/
  rightMinimalForbiddenSupports_spec :
    ∀ support, support ∈ rightMinimalForbiddenSupports ↔
      support ∈ D.rightSquareFree.forbiddenSupports ∧
        ∀ candidate ∈ D.rightSquareFree.forbiddenSupports,
          candidate ⊆ support -> support ⊆ candidate
  /-- Generated left obstruction ideal equals its Stanley--Reisner ideal. -/
  leftStanleyReisner :
    letI := R.geometry.coeffCommRing
    D.leftIdeal = D.leftSquareFree.stanleyReisnerIdeal M.Coeff
  /-- Generated right obstruction ideal equals its Stanley--Reisner ideal. -/
  rightStanleyReisner :
    letI := R.geometry.coeffCommRing
    D.rightIdeal = D.rightSquareFree.stanleyReisnerIdeal M.Coeff
  /-- Selected finite-free resolution computes the Mathlib Tor object. -/
  torComparison :
    letI := R.geometry.coeffCommRing
    Derived.Intersection.mathlibTor
        (MvPolynomial M.WitnessVariables M.Coeff)
        D.leftIdeal D.rightIdeal D.torDegree ≅
      (D.rightResolution.tensorComplex D.leftIdeal).homology D.torDegree
  /-- Finite length of the selected resolution. -/
  torResolutionLength : Nat
  /-- Finite basis indices of every selected resolution term. -/
  torBasisIndex : Nat -> Type (max u v)
  /-- Each selected basis-index carrier is finite. -/
  torBasisIndexFintype : ∀ n, Fintype (torBasisIndex n)
  /-- Coordinate realization of every selected resolution term. -/
  torTermIsoFree :
    letI := R.geometry.coeffCommRing
    ∀ n,
      D.rightResolution.projectiveResolution.complex.X n ≅
        ModuleCat.of (MvPolynomial M.WitnessVariables M.Coeff)
          (torBasisIndex n -> MvPolynomial M.WitnessVariables M.Coeff)
  /-- Terms above the selected finite length vanish extensionally. -/
  torSupported_le_length :
    ∀ n, torResolutionLength < n ->
      Subsingleton (D.rightResolution.projectiveResolution.complex.X n)
  /-- Finite coordinate matrix of every selected resolution differential. -/
  torDifferentialMatrix :
    letI := R.geometry.coeffCommRing
    ∀ n,
      Matrix (D.rightResolution.BasisIndex n)
        (D.rightResolution.BasisIndex (n + 1))
        (MvPolynomial M.WitnessVariables M.Coeff)
  /-- The matrices are obtained from the actual selected resolution. -/
  torDifferentialMatrix_correct :
    letI := R.geometry.coeffCommRing
    ∀ n,
      letI : DecidableEq (D.rightResolution.BasisIndex n) := Classical.decEq _
      letI : DecidableEq (D.rightResolution.BasisIndex (n + 1)) := Classical.decEq _
      LinearMap.toMatrix
          (Pi.basisFun (MvPolynomial M.WitnessVariables M.Coeff)
            (D.rightResolution.BasisIndex (n + 1)))
          (Pi.basisFun (MvPolynomial M.WitnessVariables M.Coeff)
            (D.rightResolution.BasisIndex n))
          (D.resolutionCoordinateDifferential n) =
        torDifferentialMatrix n
  /-- Differential matrices after coefficient reduction modulo the left ideal. -/
  torTensorDifferentialMatrix :
    letI := R.geometry.coeffCommRing
    ∀ n,
      Matrix (D.rightResolution.BasisIndex n)
        (D.rightResolution.BasisIndex (n + 1))
        (MvPolynomial M.WitnessVariables M.Coeff ⧸ D.leftIdeal)
  /-- Tensor matrices are coefficientwise images of the actual resolution matrices. -/
  torTensorDifferentialMatrix_eq_map :
    letI := R.geometry.coeffCommRing
    ∀ n, torTensorDifferentialMatrix n =
      (D.resolutionDifferentialMatrix n).map (Ideal.Quotient.mk D.leftIdeal)
  /-- Kernel decision on every reduced tensor differential matrix. -/
  torTensorKernelDecision :
    letI := R.geometry.coeffCommRing
    ∀ n, D.tensorMatrixAlgorithm.CoordinateTerm (n + 1) -> Bool
  /-- Kernel procedure correctness for the actual reduced matrix. -/
  torTensorKernelDecision_correct :
    letI := R.geometry.coeffCommRing
    ∀ n x, torTensorKernelDecision n x = true ↔
      D.tensorMatrixAlgorithm.differential n x = 0
  /-- Image decision on every reduced tensor differential matrix. -/
  torTensorImageDecision :
    letI := R.geometry.coeffCommRing
    ∀ n, D.tensorMatrixAlgorithm.CoordinateTerm n -> Bool
  /-- Image procedure correctness for the actual reduced matrix. -/
  torTensorImageDecision_correct :
    letI := R.geometry.coeffCommRing
    ∀ n x, torTensorImageDecision n x = true ↔
      ∃ b : D.tensorMatrixAlgorithm.CoordinateTerm (n + 1),
        D.tensorMatrixAlgorithm.differential n b = x
  /-- Vanishing decision for every represented coordinate homology class. -/
  torCoordinateClassZeroDecision :
    letI := R.geometry.coeffCommRing
    ∀ n, D.tensorMatrixAlgorithm.Cycle n -> Bool
  /-- Quotient-class vanishing is exactly the incoming-image matrix decision. -/
  torCoordinateClassZeroDecision_correct :
    letI := R.geometry.coeffCommRing
    ∀ n x, torCoordinateClassZeroDecision n x = true ↔
      D.tensorMatrixAlgorithm.classOfCycle n x = 0
  /-- Actual finite-resolution tensor chain complex. -/
  torTensorComplex :
    letI := R.geometry.coeffCommRing
    ChainComplex
      (ModuleCat.{max u v} (MvPolynomial M.WitnessVariables M.Coeff)) ℕ
  /-- The exposed chain complex is the selected resolution after tensoring. -/
  torTensorComplex_eq :
    letI := R.geometry.coeffCommRing
    torTensorComplex = D.rightResolution.tensorComplex D.leftIdeal
  /-- Reduced finite-matrix chain complex. -/
  torCoordinateComplex :
    letI := R.geometry.coeffCommRing
    ChainComplex
      (ModuleCat.{max u v} (MvPolynomial M.WitnessVariables M.Coeff)) ℕ
  /-- The exposed coordinate complex is generated by the reduced matrices. -/
  torCoordinateComplex_eq :
    letI := R.geometry.coeffCommRing
    torCoordinateComplex = D.tensorMatrixAlgorithm.coordinateComplex
  /-- Chain-level comparison constructed from the selected finite bases. -/
  torTensorCoordinateComplexIso :
    letI := R.geometry.coeffCommRing
    torTensorComplex ≅ torCoordinateComplex
  /-- Actual selected law-conflict class. -/
  selectedConflictClass :
    letI := R.geometry.coeffCommRing
    (Derived.Intersection.canonicalSelectedTorBridge
      (MvPolynomial M.WitnessVariables M.Coeff)
      D.leftIdeal D.rightIdeal).LawConflict D.torDegree
  /-- Selected conflict class after transport to Mathlib Tor. -/
  selectedTorClass :
    letI := R.geometry.coeffCommRing
    Derived.Intersection.mathlibTor
      (MvPolynomial M.WitnessVariables M.Coeff)
      D.leftIdeal D.rightIdeal D.torDegree
  /-- Selected conflict class after finite-resolution chain transport. -/
  selectedTensorHomologyClass :
    letI := R.geometry.coeffCommRing
    (D.rightResolution.tensorComplex D.leftIdeal).homology D.torDegree
  /-- Selected cycle before homology quotienting. -/
  selectedCoordinateCycle :
    letI := R.geometry.coeffCommRing
    D.tensorMatrixAlgorithm.Cycle D.torDegree
  /-- The exposed cycle is the selected input to the finite chain computation. -/
  selectedCoordinateCycle_eq :
    letI := R.geometry.coeffCommRing
    selectedCoordinateCycle = D.selectedCoordinateCycle
  /-- Selected coordinate homology class. -/
  selectedCoordinateHomologyClass :
    letI := R.geometry.coeffCommRing
    D.tensorMatrixAlgorithm.Homology D.torDegree
  /-- The coordinate class is the quotient class of the selected cycle. -/
  selectedCoordinateHomologyClass_eq :
    letI := R.geometry.coeffCommRing
    selectedCoordinateHomologyClass =
      D.tensorMatrixAlgorithm.classOfCycle D.torDegree selectedCoordinateCycle
  /-- Tensor homology is obtained through the constructed chain comparison. -/
  selectedTensorHomologyClass_eq :
    letI := R.geometry.coeffCommRing
    selectedTensorHomologyClass =
      (D.tensorMatrixAlgorithm.coordinateHomologyIsoTensor D.torDegree).hom
        selectedCoordinateHomologyClass
  /-- Mathlib Tor is obtained by the selected resolution comparison. -/
  selectedTorClass_eq :
    letI := R.geometry.coeffCommRing
    selectedTorClass =
      (D.rightResolution.torIsoTensorHomology D.leftIdeal D.torDegree).inv
        selectedTensorHomologyClass
  /-- The law-conflict class is the canonical Tor transport. -/
  selectedConflictClass_eq :
    letI := R.geometry.coeffCommRing
    selectedConflictClass =
      ((Derived.Intersection.canonicalSelectedTorBridge
        (MvPolynomial M.WitnessVariables M.Coeff)
        D.leftIdeal D.rightIdeal).lawConflictLinearEquivMathlibTor
          D.torDegree).symm selectedTorClass
  /-- Finite support computed for the selected homology class. -/
  conflictSupport : Finset M.WitnessVariables
  /-- The exposed support is the support constructed for the same selected
  homology class. -/
  conflictSupport_eq_selectedClassSupport :
    letI := R.witnessDecidableEq
    conflictSupport = D.selectedClassSupport
  /-- A zero selected coordinate homology class cannot carry nonempty support. -/
  conflictSupport_eq_empty_of_selectedCoordinateHomologyClass_eq_zero :
    letI := R.witnessDecidableEq
    letI := R.geometry.coeffCommRing
    selectedCoordinateHomologyClass = 0 -> conflictSupport = ∅
  /-- A zero selected final LawConflict class cannot carry nonempty support. -/
  conflictSupport_eq_empty_of_selectedConflictClass_eq_zero :
    letI := R.witnessDecidableEq
    letI := R.geometry.coeffCommRing
    selectedConflictClass = 0 -> conflictSupport = ∅
  /-- For a nonzero selected class, support is computed from its selected
  reduced cycle representative and the actual resolution matrices. -/
  conflictSupport_eq_selectedCycleSupport_of_selectedCoordinateHomologyClass_ne_zero :
    letI := R.witnessDecidableEq
    letI := R.geometry.coeffCommRing
    selectedCoordinateHomologyClass ≠ 0 ->
      conflictSupport = D.selectedCycleSupport

/-- Independent fixed output contract for the final relation-valued
`LawConflictMeasurement` connection. -/
structure FiniteAATFixedConflictOutputContract
    {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M)
    (D : FiniteAATComputationData M R)
    (C : FiniteAATConflictRealization D) :
    Type (max (u + 1) (v + 1)) where
  /-- Complete finite Čech, square-free, Tor, and support output contract. -/
  computation : FiniteAATFixedOutputContract R D
  /-- Relation-valued measurement on the selected common ambient. -/
  lawConflictMeasurement :
    LawConflictMeasurement.{u, v, max u v} C.commonAmbient
  lawConflictMeasurement_eq_computed :
    lawConflictMeasurement = C.lawConflictMeasurement
  selectedClassSupportReading :
    lawConflictMeasurement.selectedClassSupportReading
  computedConflictSupport_selected :
    letI := R.geometry.coeffCommRing
    D.ComputedConflictSupport D.selectedConflictClass D.selectedClassSupport
  computedConflictSupport_congr :
    letI := R.geometry.coeffCommRing
    ∀ {conflictClass conflictClass' : D.ActualConflictClass}
      {support support' : Finset M.WitnessVariables},
      conflictClass = conflictClass' -> support = support' ->
        (D.ComputedConflictSupport conflictClass support ↔
          D.ComputedConflictSupport conflictClass' support')
  computedConflictSupport_zero :
    letI := R.geometry.coeffCommRing
    ∀ {support : Finset M.WitnessVariables},
      D.ComputedConflictSupport 0 support -> support = ∅
  supportRelation_zero :
    letI := R.geometry.coeffCommRing
    ∀ {support : C.commonAmbient.SupportCarrier},
      C.supportRelation (0 : D.ActualConflictClass) support ->
        support = C.supportEquiv ∅

end Measurement


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

/-- Convert the production package into the independent fixed output contract. -/
def finiteAATFixedOutputContractOf
    {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATComputability R D) :
    Measurement.FiniteAATFixedOutputContract R D where
  siteObjFintype := C.siteObjFintype
  coverFintype := C.coverFintype
  cochainModule := C.cochainModule
  coefficientComputation := C.coefficientComputation
  cocycleRepresentative := C.cocycleRepresentative
  cocycleRepresentative_correct := C.cocycleRepresentative_correct
  verdict := C.verdict
  verdictData := C.verdictData
  verdict_eq := C.verdict_eq
  profileObstructionObject_realizes := C.profileObstructionObject_realizes
  profileObstructionIdeal_realizes := C.profileObstructionIdeal_realizes
  profileLeftLaw_realizes := C.profileLeftLaw_realizes
  profileRightLaw_realizes := C.profileRightLaw_realizes
  obstructionGenerators := C.obstructionGenerators
  obstructionGenerator_mem := C.obstructionGenerator_mem
  obstructionIdeal_eq_span_generators :=
    C.obstructionIdeal_eq_span_generators
  obstructionIdealMembership := C.obstructionIdealMembership
  obstructionIdealMembership_correct := C.obstructionIdealMembership_correct
  obstructionMinimalForbiddenSupports :=
    C.obstructionMinimalForbiddenSupports
  obstructionMinimalForbiddenSupports_eq :=
    C.obstructionMinimalForbiddenSupports_eq
  obstructionMinimalForbiddenSupports_spec :=
    C.obstructionMinimalForbiddenSupports_spec
  obstructionStanleyReisner := C.obstructionStanleyReisner
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
  leftMinimalForbiddenSupports_eq := C.leftMinimalForbiddenSupports_eq
  rightMinimalForbiddenSupports_eq := C.rightMinimalForbiddenSupports_eq
  leftMinimalForbiddenSupports_spec := C.leftMinimalForbiddenSupports_spec
  rightMinimalForbiddenSupports_spec := C.rightMinimalForbiddenSupports_spec
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
  torTensorDifferentialMatrix := C.torTensorDifferentialMatrix
  torTensorDifferentialMatrix_eq_map := C.torTensorDifferentialMatrix_eq_map
  torTensorKernelDecision := C.torTensorKernelDecision
  torTensorKernelDecision_correct := C.torTensorKernelDecision_correct
  torTensorImageDecision := C.torTensorImageDecision
  torTensorImageDecision_correct := C.torTensorImageDecision_correct
  torCoordinateClassZeroDecision := C.torCoordinateClassZeroDecision
  torCoordinateClassZeroDecision_correct :=
    C.torCoordinateClassZeroDecision_correct
  torTensorComplex := C.torTensorComplex
  torTensorComplex_eq := C.torTensorComplex_eq
  torCoordinateComplex := C.torCoordinateComplex
  torCoordinateComplex_eq := C.torCoordinateComplex_eq
  torTensorCoordinateComplexIso := C.torTensorCoordinateComplexIso
  selectedConflictClass := C.selectedConflictClass
  selectedTorClass := C.selectedTorClass
  selectedTensorHomologyClass := C.selectedTensorHomologyClass
  selectedCoordinateCycle := C.selectedCoordinateCycle
  selectedCoordinateCycle_eq := C.selectedCoordinateCycle_eq
  selectedCoordinateHomologyClass := C.selectedCoordinateHomologyClass
  selectedCoordinateHomologyClass_eq := C.selectedCoordinateHomologyClass_eq
  selectedTensorHomologyClass_eq := C.selectedTensorHomologyClass_eq
  selectedTorClass_eq := C.selectedTorClass_eq
  selectedConflictClass_eq := C.selectedConflictClass_eq
  conflictSupport := C.conflictSupport
  conflictSupport_eq_selectedClassSupport :=
    C.conflictSupport_eq_selectedClassSupport
  conflictSupport_eq_empty_of_selectedCoordinateHomologyClass_eq_zero :=
    C.conflictSupport_eq_empty_of_selectedCoordinateHomologyClass_eq_zero
  conflictSupport_eq_empty_of_selectedConflictClass_eq_zero :=
    C.conflictSupport_eq_empty_of_selectedConflictClass_eq_zero
  conflictSupport_eq_selectedCycleSupport_of_selectedCoordinateHomologyClass_ne_zero :=
    C.conflictSupport_eq_selectedCycleSupport_of_selectedCoordinateHomologyClass_ne_zero

/-- The production theorem fills the independent fixed output contract. -/
example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R) :
    Nonempty (Measurement.FiniteAATFixedOutputContract R D) :=
  ⟨finiteAATFixedOutputContractOf R D
    (Measurement.finiteAATComputabilityPackage R D)⟩

/-- Convert the final production package into the independent conflict contract. -/
def finiteAATFixedConflictOutputContractOf
    {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATConflictRealization D)
    (P : Measurement.FiniteAATConflictComputability R D C) :
    Measurement.FiniteAATFixedConflictOutputContract R D C where
  computation := finiteAATFixedOutputContractOf R D P.computation
  lawConflictMeasurement := P.lawConflictMeasurement
  lawConflictMeasurement_eq_computed := P.lawConflictMeasurement_eq_computed
  selectedClassSupportReading := P.selectedClassSupportReading
  computedConflictSupport_selected := D.computedConflictSupport_selected
  computedConflictSupport_congr := by
    intro conflictClass conflictClass' support support' hclass hsupport
    exact D.computedConflictSupport_congr hclass hsupport
  computedConflictSupport_zero := by
    intro support hsupport
    exact D.computedConflictSupport_zero hsupport
  supportRelation_zero := by
    intro support hsupport
    exact C.supportRelation_zero hsupport

/-- The final production theorem fills the independent conflict contract. -/
example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R)
    (C : Measurement.FiniteAATConflictRealization D) :
    Nonempty (Measurement.FiniteAATFixedConflictOutputContract R D C) :=
  ⟨finiteAATFixedConflictOutputContractOf R D C
    (Measurement.finiteAATConflictComputabilityPackage R D C)⟩

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
