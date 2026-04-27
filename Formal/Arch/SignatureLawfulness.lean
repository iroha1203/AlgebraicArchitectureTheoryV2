import Formal.Arch.DependencyObstruction

namespace Formal.Arch

universe u v w

namespace ArchitectureSignature

/-- Boundary or abstraction policy violation on one dependency pair. -/
def PolicyViolation {C : Type u} (G : ArchGraph C)
    (allowed : C -> C -> Prop) (pair : C × C) : Prop :=
  G.edge pair.1 pair.2 ∧ ¬ allowed pair.1 pair.2

instance instDecidablePredPolicyViolation {C : Type u} (G : ArchGraph C)
    (allowed : C -> C -> Prop)
    [DecidableRel G.edge] [DecidableRel allowed] :
    DecidablePred (PolicyViolation G allowed) := by
  intro pair
  unfold PolicyViolation
  infer_instance

/-- A dependency graph respects a local edge policy. -/
def PolicySound {C : Type u} (G : ArchGraph C)
    (allowed : C -> C -> Prop) : Prop :=
  ∀ {c d : C}, G.edge c d -> allowed c d

/-- The five concrete required-law witnesses represented by Signature v1 axes. -/
inductive ArchitectureRequiredLawWitness where
  | hasCycle
  | projectionSoundness
  | lsp
  | boundaryPolicy
  | abstractionPolicy
  deriving DecidableEq, Repr

/-- The measured universe for the current required Signature law family. -/
def architectureRequiredLawWitnesses : List ArchitectureRequiredLawWitness :=
  [ .hasCycle
  , .projectionSoundness
  , .lsp
  , .boundaryPolicy
  , .abstractionPolicy
  ]

/-- The concrete architecture data used by the Signature-integrated law bridge. -/
structure ArchitectureLawModel (C : Type u) (A : Type v) (Obs : Type w) where
  G : ArchGraph C
  π : InterfaceProjection C A
  GA : AbstractGraph A
  O : Observation C Obs
  U : ComponentUniverse G
  boundaryAllowed : C -> C -> Prop
  abstractionAllowed : C -> C -> Prop
  lspPairClosed :
    ∀ {x y : C}, π.expose x = π.expose y -> x ∈ U.components ∧ y ∈ U.components

namespace ArchitectureLawModel

variable {C : Type u} {A : Type v} {Obs : Type w}

/-- The Signature v1 value whose selected required law axes are populated. -/
def signatureOf (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    ArchitectureSignatureV1 :=
  v1OfFiniteWithRequiredLawAxes X.G X.π X.GA X.O X.U.components
    X.boundaryAllowed X.abstractionAllowed

end ArchitectureLawModel

/--
Concrete obstruction predicate for the Signature-integrated required law
family.
-/
def ArchitectureRequiredLawBad {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    ArchitectureRequiredLawWitness -> Prop
  | .hasCycle => HasClosedWalk X.G
  | .projectionSoundness =>
      ∃ edge : C × C, ProjectionObstruction X.G X.π X.GA edge
  | .lsp =>
      ∃ pair : C × C, LSPObstruction X.π X.O pair
  | .boundaryPolicy =>
      ∃ pair : C × C, PolicyViolation X.G X.boundaryAllowed pair
  | .abstractionPolicy =>
      ∃ pair : C × C, PolicyViolation X.G X.abstractionAllowed pair

/-- Architecture lawfulness represented by the selected required Signature axes. -/
def ArchitectureLawful {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) : Prop :=
  WalkAcyclic X.G ∧
  ProjectionSound X.G X.π X.GA ∧
  LSPCompatible X.π X.O ∧
  PolicySound X.G X.boundaryAllowed ∧
  PolicySound X.G X.abstractionAllowed

/-- Required Signature v1 axes must be present and exactly zero. -/
def RequiredSignatureAxesAvailableAndZero (sig : ArchitectureSignatureV1) : Prop :=
  ∀ axis, IsSelectedRequiredLawAxis axis ->
    ArchitectureSignatureV1.axisAvailableAndZero sig axis

/-- The witness subfamily represented by each Signature v1 axis. -/
def architectureWitnessForAxis :
    ArchitectureSignatureV1Axis -> ArchitectureRequiredLawWitness -> Prop
  | .hasCycle, .hasCycle => True
  | .projectionSoundnessViolation, .projectionSoundness => True
  | .lspViolationCount, .lsp => True
  | .boundaryViolationCount, .boundaryPolicy => True
  | .abstractionViolationCount, .abstractionPolicy => True
  | _, _ => False

theorem mem_architectureRequiredLawWitnesses
    (witness : ArchitectureRequiredLawWitness) :
    witness ∈ architectureRequiredLawWitnesses := by
  cases witness <;> simp [architectureRequiredLawWitnesses]

private theorem architectureLawful_iff_no_measured_bad
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    ArchitectureLawful X ↔
      ∀ w, w ∈ architectureRequiredLawWitnesses ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hLawful witness _hMeasured
    rcases hLawful with ⟨hAcyclic, hProjection, hLSP, hBoundary,
      hAbstraction⟩
    cases witness
    · exact fun hClosed => hAcyclic hClosed
    · rintro ⟨edge, hBad⟩
      exact (projectionSound_iff_noProjectionObstruction.mp hProjection) edge hBad
    · rintro ⟨pair, hBad⟩
      exact (lspCompatible_iff_noLSPObstruction.mp hLSP) pair hBad
    · rintro ⟨pair, hBad⟩
      exact hBad.2 (hBoundary hBad.1)
    · rintro ⟨pair, hBad⟩
      exact hBad.2 (hAbstraction hBad.1)
  · intro hNoBad
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hClosed
      exact hNoBad .hasCycle
        (mem_architectureRequiredLawWitnesses .hasCycle) hClosed
    · exact projectionSound_iff_noProjectionObstruction.mpr (by
        intro edge hBad
        exact hNoBad .projectionSoundness
          (mem_architectureRequiredLawWitnesses .projectionSoundness)
          ⟨edge, hBad⟩)
    · exact lspCompatible_iff_noLSPObstruction.mpr (by
        intro pair hBad
        exact hNoBad .lsp (mem_architectureRequiredLawWitnesses .lsp)
          ⟨pair, hBad⟩)
    · intro c d hEdge
      by_contra hNotAllowed
      exact hNoBad .boundaryPolicy
        (mem_architectureRequiredLawWitnesses .boundaryPolicy)
        ⟨(c, d), hEdge, hNotAllowed⟩
    · intro c d hEdge
      by_contra hNotAllowed
      exact hNoBad .abstractionPolicy
        (mem_architectureRequiredLawWitnesses .abstractionPolicy)
        ⟨(c, d), hEdge, hNotAllowed⟩

theorem architectureLawFamily_completeWitnessCoverage :
    CompleteWitnessCoverage
      ({ Witness := ArchitectureRequiredLawWitness
         Axis := ArchitectureSignatureV1Axis
         measured := architectureRequiredLawWitnesses
         required := fun _ => True
         bad := fun X => ArchitectureRequiredLawBad X
         lawful := fun X => ArchitectureLawful X
         lawful_iff_no_measured_bad := by
          intro X
          exact architectureLawful_iff_no_measured_bad X
         requiredAxis := IsSelectedRequiredLawAxis } :
        LawFamily (ArchitectureLawModel C A Obs)) := by
  intro witness
  constructor
  · intro _hMeasured
    trivial
  · intro _hRequired
    exact mem_architectureRequiredLawWitnesses witness

/-- Concrete law family used by the Signature-integrated zero-curvature bridge. -/
def architectureLawFamily (C : Type u) (A : Type v) (Obs : Type w) :
    LawFamily (ArchitectureLawModel C A Obs) where
  Witness := ArchitectureRequiredLawWitness
  Axis := ArchitectureSignatureV1Axis
  measured := architectureRequiredLawWitnesses
  required := fun _ => True
  bad := fun X => ArchitectureRequiredLawBad X
  lawful := fun X => ArchitectureLawful X
  lawful_iff_no_measured_bad := by
    intro X
    exact architectureLawful_iff_no_measured_bad X
  requiredAxis := IsSelectedRequiredLawAxis

theorem architectureLawFamily_completeCoverage :
    CompleteWitnessCoverage (architectureLawFamily C A Obs) := by
  exact architectureLawFamily_completeWitnessCoverage

theorem architecture_axisCoversOnlyRequired :
    AxisCoversOnlyRequired (architectureLawFamily C A Obs)
      architectureWitnessForAxis := by
  intro axis _hRequiredAxis witness _hWitness
  trivial

theorem architecture_requiredWitnessCoveredByAxis :
    RequiredWitnessCoveredByAxis (architectureLawFamily C A Obs)
      architectureWitnessForAxis := by
  intro witness _hRequired
  cases witness
  · exact ⟨.hasCycle, by
      show .hasCycle ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.projectionSoundnessViolation, by
      show .projectionSoundnessViolation ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.lspViolationCount, by
      show .lspViolationCount ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.boundaryViolationCount, by
      show .boundaryViolationCount ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.abstractionViolationCount, by
      show .abstractionViolationCount ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩

private theorem availableAndZero_hasCycle_iff_no_closed_walk
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .hasCycle ↔ ¬ HasClosedWalk X.G := by
  constructor
  · intro hAvailable hClosed
    have hCycle :
        hasCycleBool X.G X.U.components = true :=
      (hasCycleBool_correct_under_finite_universe X.U).mpr hClosed
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf at hAvailable
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      v1CoreOfFinite, v0OfFinite, boolRisk, hCycle, AvailableAndZero] at hAvailable
  · intro hNoClosed
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf
    have hNoCycle : hasCycleBool X.G X.U.components = false := by
      cases h : hasCycleBool X.G X.U.components
      · rfl
      · exact False.elim (hNoClosed
          ((hasCycleBool_correct_under_finite_universe X.U).mp h))
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      v1CoreOfFinite, v0OfFinite, boolRisk, hNoCycle, AvailableAndZero]

private theorem availableAndZero_projection_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .projectionSoundnessViolation ↔
        ¬ ∃ edge : C × C, ProjectionObstruction X.G X.π X.GA edge := by
  constructor
  · intro hAvailable hExists
    have hZero :
        projectionSoundnessViolation X.G X.π X.GA X.U.components = 0 := by
      unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf at hAvailable
      simpa [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
        AvailableAndZero] using hAvailable
    have hSound : ProjectionSound X.G X.π X.GA :=
      projectionSound_of_projectionSoundnessViolation_eq_zero
        X.U.edgeClosed hZero
    rcases hExists with ⟨edge, hBad⟩
    exact (projectionSound_iff_noProjectionObstruction.mp hSound) edge hBad
  · intro hNoExists
    have hSound : ProjectionSound X.G X.π X.GA :=
      projectionSound_iff_noProjectionObstruction.mpr (by
        intro edge hBad
        exact hNoExists ⟨edge, hBad⟩)
    have hZero :
        projectionSoundnessViolation X.G X.π X.GA X.U.components = 0 :=
      projectionSoundnessViolation_eq_zero_of_projectionSound
        X.U.components hSound
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      AvailableAndZero, hZero]

private theorem availableAndZero_lsp_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .lspViolationCount ↔
        ¬ ∃ pair : C × C, LSPObstruction X.π X.O pair := by
  constructor
  · intro hAvailable hExists
    have hZero : lspViolationCount X.π X.O X.U.components = 0 := by
      unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf at hAvailable
      simpa [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
        AvailableAndZero] using hAvailable
    have hLSP : LSPCompatible X.π X.O :=
      lspCompatible_of_lspViolationCount_eq_zero X.lspPairClosed hZero
    rcases hExists with ⟨pair, hBad⟩
    exact (lspCompatible_iff_noLSPObstruction.mp hLSP) pair hBad
  · intro hNoExists
    have hLSP : LSPCompatible X.π X.O :=
      lspCompatible_iff_noLSPObstruction.mpr (by
        intro pair hBad
        exact hNoExists ⟨pair, hBad⟩)
    have hZero : lspViolationCount X.π X.O X.U.components = 0 :=
      lspViolationCount_eq_zero_of_lspCompatible X.U.components hLSP
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      AvailableAndZero, hZero]

private theorem policyViolationCount_eq_zero_iff_no_obstruction
    {C : Type u} {G : ArchGraph C} [DecidableRel G.edge]
    (U : ComponentUniverse G) (allowed : C -> C -> Prop)
    [DecidableRel allowed] :
    countWhere (componentPairs U.components) (fun pair =>
      decide (G.edge pair.1 pair.2) && ! decide (allowed pair.1 pair.2)) = 0 ↔
        ¬ ∃ pair : C × C, PolicyViolation G allowed pair := by
  constructor
  · intro hZero hExists
    rcases hExists with ⟨pair, hBad⟩
    have hPairMem : pair ∈ componentPairs U.components := by
      exact mem_componentPairs_iff.mpr (U.edgeClosed hBad.1)
    have hViolationMem :
        pair ∈ (componentPairs U.components).filter (fun pair =>
          decide (G.edge pair.1 pair.2) && ! decide (allowed pair.1 pair.2)) := by
      simp [hPairMem, hBad.1, hBad.2]
    have hPositive :
        0 <
          countWhere (componentPairs U.components) (fun pair =>
            decide (G.edge pair.1 pair.2) &&
              ! decide (allowed pair.1 pair.2)) := by
      unfold countWhere
      exact List.length_pos_of_mem hViolationMem
    exact (Nat.ne_of_gt hPositive) hZero
  · intro hNoExists
    have hNoBad :
        ∀ pair, pair ∈ componentPairs U.components ->
          ¬ PolicyViolation G allowed pair := by
      intro pair _hMem hBad
      exact hNoExists ⟨pair, hBad⟩
    have hZero :
        violationCount (PolicyViolation G allowed)
          (componentPairs U.components) = 0 :=
      (violationCount_eq_zero_iff_forall_not_bad).mpr hNoBad
    simpa [violationCount, violatingWitnesses, countWhere, PolicyViolation]
      using hZero

private theorem availableAndZero_boundary_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .boundaryViolationCount ↔
        ¬ ∃ pair : C × C, PolicyViolation X.G X.boundaryAllowed pair := by
  simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
    v1CoreOfFinite, v0OfFinite, boundaryViolationCountOfFinite,
    AxisAvailableAndZero, ArchitectureLawModel.signatureOf, AvailableAndZero,
    policyViolationCount_eq_zero_iff_no_obstruction X.U X.boundaryAllowed]

private theorem availableAndZero_abstraction_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .abstractionViolationCount ↔
        ¬ ∃ pair : C × C, PolicyViolation X.G X.abstractionAllowed pair := by
  simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
    v1CoreOfFinite, v0OfFinite, abstractionViolationCountOfFinite,
    AxisAvailableAndZero, ArchitectureLawModel.signatureOf, AvailableAndZero,
    policyViolationCount_eq_zero_iff_no_obstruction X.U X.abstractionAllowed]

private theorem no_hasCycle_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    ¬ HasClosedWalk X.G ↔
      ∀ w, architectureWitnessForAxis .hasCycle w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoClosed w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    exact hNoClosed
  · intro hNoBad hClosed
    exact hNoBad .hasCycle trivial hClosed

private theorem no_projection_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ edge : C × C, ProjectionObstruction X.G X.π X.GA edge) ↔
      ∀ w, architectureWitnessForAxis .projectionSoundnessViolation w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .projectionSoundness trivial hExists

private theorem no_lsp_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ pair : C × C, LSPObstruction X.π X.O pair) ↔
      ∀ w, architectureWitnessForAxis .lspViolationCount w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .lsp trivial hExists

private theorem no_boundary_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ pair : C × C, PolicyViolation X.G X.boundaryAllowed pair) ↔
      ∀ w, architectureWitnessForAxis .boundaryViolationCount w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .boundaryPolicy trivial hExists

private theorem no_abstraction_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ pair : C × C, PolicyViolation X.G X.abstractionAllowed pair) ↔
      ∀ w, architectureWitnessForAxis .abstractionViolationCount w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .abstractionPolicy trivial hExists

theorem architecture_requiredAxisFamilyExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    RequiredAxisFamilyExact X (architectureLawFamily C A Obs)
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      architectureWitnessForAxis := by
  intro axis hRequiredAxis
  change IsSelectedRequiredLawAxis axis at hRequiredAxis
  unfold IsSelectedRequiredLawAxis at hRequiredAxis
  rw [mem_selectedRequiredLawAxes_iff] at hRequiredAxis
  rcases hRequiredAxis with hAxis | hAxis | hAxis | hAxis | hAxis
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_hasCycle_iff_no_closed_walk X)
      (no_hasCycle_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_projection_iff_no_obstruction X)
      (no_projection_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_lsp_iff_no_obstruction X)
      (no_lsp_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_boundary_iff_no_obstruction X)
      (no_boundary_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_abstraction_iff_no_obstruction X)
      (no_abstraction_axis_witness_iff X)

theorem architecture_requiredAxisExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    RequiredAxisExact X (architectureLawFamily C A Obs)
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X)) := by
  exact requiredAxisExact_of_axisExactFamily
    (architecture_requiredAxisFamilyExact X)
    architecture_axisCoversOnlyRequired
    architecture_requiredWitnessCoveredByAxis

/--
Final Signature-integrated zero-curvature theorem for the selected required
Signature v1 axes.
-/
theorem architectureLawful_iff_requiredSignatureAxesAvailableAndZero
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    ArchitectureLawful X ↔
      RequiredSignatureAxesAvailableAndZero (ArchitectureLawModel.signatureOf X) := by
  exact lawful_iff_requiredAxesAvailableAndZero_of_completeCoverage_and_requiredAxisExact
    (architectureLawFamily_completeCoverage (C := C) (A := A) (Obs := Obs))
    (architecture_requiredAxisExact X)

end ArchitectureSignature

end Formal.Arch
