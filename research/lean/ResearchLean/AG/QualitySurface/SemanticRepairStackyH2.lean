import ResearchLean.AG.QualitySurface.SemanticRepairNonabelianTorsor

/-!
Cycle 7 evidence for `G-aat-quality-surface-04`.

This file raises the higher / stacky part of the finite obstruction tower from
Bool-level tokens to a finite stacky `H2` repair-descent envelope.  The envelope
records a finite selected 2-cocycle and a boundary map.  Effective stacky
repair descent remains an independent predicate, and the passage from a
trivialization to an effective repair witness is a visible discharge theorem.

The result is target support only.  It does not assert unrestricted `H2`,
arbitrary higher stacks, runtime repair synthesis, ArchMap correctness, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairStackyH2

open SemanticRepairObstructionTower
open SemanticRepairSheafH1
open SemanticRepairNonabelianTriple
open SemanticRepairNonabelianTorsor

universe u v w x y z r

/-! ## Finite stacky `H2` repair descent envelope -/

/--
A finite/small stacky repair `H2` envelope.

The structure records finite 2-coherence data and repair witnesses.  It does
not store higher coherence vanishing, stack effectiveness, global repair
coherence, or tower vanishing.
-/
structure FiniteStackyRepairH2Envelope
    (Coherence : Type z)
    (Repair : Type r) where
  coherenceOrder : List Coherence
  repairOrder : List Repair
  neutral2 : Coherence
  compose2 : Coherence -> Coherence -> Coherence
  selected2Cocycle : Coherence
  selected2_cocycle :
    compose2 selected2Cocycle neutral2 = selected2Cocycle
  boundary2 : Repair -> Coherence
  effectiveRepair : Repair -> Prop

/-- Finite stacky 2-cocycles. -/
def StackyCechZ2
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    (cochain : Coherence) : Prop :=
  stack.compose2 cochain stack.neutral2 = cochain

/-- Finite stacky 2-boundaries. -/
def StackyCechB2
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    (cochain : Coherence) : Prop :=
  exists repair, stack.boundary2 repair = cochain

/-- The selected stacky `H2` obstruction vanishes. -/
def StackyRepairH2Zero
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) : Prop :=
  StackyCechZ2 stack stack.selected2Cocycle /\
    StackyCechB2 stack stack.selected2Cocycle

/-- The selected stacky `H2` obstruction is nonzero. -/
def StackyRepairH2Nonzero
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) : Prop :=
  StackyCechZ2 stack stack.selected2Cocycle /\
    Not (StackyCechB2 stack stack.selected2Cocycle)

/-- The selected stacky 2-cocycle is trivialized. -/
def StackyRepairTrivial
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) : Prop :=
  StackyCechB2 stack stack.selected2Cocycle

/--
Effective stacky repair descent.

This is an independent predicate with a concrete repair witness.  It is not a
field of `FiniteStackyRepairH2Envelope`.
-/
def EffectiveStackyRepairDescent
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) : Prop :=
  exists repair,
    stack.effectiveRepair repair /\
      stack.boundary2 repair = stack.selected2Cocycle

/--
Visible discharge from a stacky trivialization to an effective repair witness.
It is not stored in the stacky envelope.
-/
structure StackyRepairDescentDischarge
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) where
  effective_of_trivialization :
    forall repair,
      stack.boundary2 repair = stack.selected2Cocycle ->
        stack.effectiveRepair repair

/-- The selected stacky 2-cochain is a 2-cocycle. -/
theorem stackyRepairH2_wellDefined
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) :
    StackyCechZ2 stack stack.selected2Cocycle := by
  exact stack.selected2_cocycle

/-- Zero stacky `H2` is the selected stacky trivialization predicate. -/
theorem stackyH2Zero_iff_stackyRepairTrivial
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) :
    StackyRepairH2Zero stack <-> StackyRepairTrivial stack := by
  constructor
  · intro hzero
    exact hzero.2
  · intro htrivial
    exact ⟨stack.selected2_cocycle, htrivial⟩

/-- Stacky trivialization is equivalent to effective stacky repair descent under explicit discharge. -/
theorem stackyRepairTrivial_iff_effectiveStackyRepairDescent
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    (stackDischarge : StackyRepairDescentDischarge stack) :
    StackyRepairTrivial stack <->
      EffectiveStackyRepairDescent stack := by
  constructor
  · intro htrivial
    rcases htrivial with ⟨repair, hboundary⟩
    exact
      ⟨repair,
        stackDischarge.effective_of_trivialization repair hboundary,
        hboundary⟩
  · intro heffective
    rcases heffective with ⟨repair, _heffective, hboundary⟩
    exact ⟨repair, hboundary⟩

/-- Effective stacky repair descent is equivalent to zero stacky `H2`. -/
theorem effectiveStackyRepairDescent_iff_stackyH2Zero
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    (stackDischarge : StackyRepairDescentDischarge stack) :
    EffectiveStackyRepairDescent stack <->
      StackyRepairH2Zero stack := by
  constructor
  · intro heffective
    exact
      (stackyH2Zero_iff_stackyRepairTrivial stack).2
        ((stackyRepairTrivial_iff_effectiveStackyRepairDescent
          stack stackDischarge).2 heffective)
  · intro hzero
    exact
      (stackyRepairTrivial_iff_effectiveStackyRepairDescent
        stack stackDischarge).1
        ((stackyH2Zero_iff_stackyRepairTrivial stack).1 hzero)

/-- A nonzero stacky `H2` obstruction rules out effective stacky repair descent. -/
theorem nonzero_stackyH2_no_effectiveDescent
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) :
    StackyRepairH2Nonzero stack ->
      Not (EffectiveStackyRepairDescent stack) := by
  intro hnonzero heffective
  rcases heffective with ⟨repair, _heffective, hboundary⟩
  exact hnonzero.2 ⟨repair, hboundary⟩

/-! ## Comparison with the finite obstruction tower -/

/-- Explicit bridge from finite stacky `H2` descent to the old higher/stack tokens. -/
structure StackyH2TowerComparison
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) where
  tower_higher_zero_of_h2Zero :
    StackyRepairH2Zero stack ->
      HigherCoherenceVanishes (toFiniteTower E)
  h2Zero_of_tower_higher_zero :
    HigherCoherenceVanishes (toFiniteTower E) ->
      StackyRepairH2Zero stack
  tower_stack_zero_of_effective :
    EffectiveStackyRepairDescent stack ->
      StackEffectivelyVanishes (toFiniteTower E)
  effective_of_tower_stack_zero :
    StackEffectivelyVanishes (toFiniteTower E) ->
      EffectiveStackyRepairDescent stack

/-- Higher tower token is equivalent to zero stacky `H2` through the explicit bridge. -/
theorem towerHigherToken_iff_stackyH2Zero
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    {Coherence : Type z}
    {Repair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence Repair}
    (comparison : StackyH2TowerComparison E stack) :
    HigherCoherenceVanishes (toFiniteTower E) <->
      StackyRepairH2Zero stack := by
  constructor
  · intro hhigher
    exact comparison.h2Zero_of_tower_higher_zero hhigher
  · intro hzero
    exact comparison.tower_higher_zero_of_h2Zero hzero

/-- Stack tower token is equivalent to effective stacky repair descent through the bridge. -/
theorem towerStackToken_iff_effectiveStackyRepairDescent
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    {Coherence : Type z}
    {Repair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence Repair}
    (comparison : StackyH2TowerComparison E stack) :
    StackEffectivelyVanishes (toFiniteTower E) <->
      EffectiveStackyRepairDescent stack := by
  constructor
  · intro hstack
    exact comparison.effective_of_tower_stack_zero hstack
  · intro heffective
    exact comparison.tower_stack_zero_of_effective heffective

/--
Nonzero stacky `H2` obstruction rules out global coherence through explicit
tower comparison and sheaf `H1` discharge.
-/
theorem no_globalRepairCoherent_of_nonzero_stackyH2
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    (comparison : StackyH2TowerComparison E stack) :
    StackyRepairH2Nonzero stack ->
      Not (GlobalSemanticRepairCoherent (toFiniteTower E)) := by
  intro hnonzero hglobal
  have hhigher :
      HigherCoherenceVanishes (toFiniteTower E) :=
    (globalRepairCoherent_forces_obstructionTowerVanishes
      (toFiniteTower E)
      (layeredAdequacy_of_sheafH1Discharge discharge)
      hglobal).2.2.1
  exact hnonzero.2 (comparison.h2Zero_of_tower_higher_zero hhigher).2

/--
First-layer sheaf `H1`, nonabelian descent, and effective stacky descent
together discharge global semantic repair coherence.
-/
theorem globalRepairCoherent_of_sheafH1_nonabelian_and_stackyDescent
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorComparison : NonabelianTorsorTowerComparison E torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackComparison : StackyH2TowerComparison E stack)
    (hzero : SemanticRepairH1Zero E)
    (hnonabelian : EffectiveNonabelianRepairDescent torsor)
    (hstacky : EffectiveStackyRepairDescent stack) :
    GlobalSemanticRepairCoherent (toFiniteTower E) := by
  have hh2 : StackyRepairH2Zero stack :=
    by
      rcases hstacky with ⟨repair, _heffective, hboundary⟩
      exact ⟨stack.selected2_cocycle, ⟨repair, hboundary⟩⟩
  exact
    globalRepairCoherent_of_sheafH1_zero_and_effectiveNonabelianDescent
      E discharge torsor torsorComparison hzero hnonabelian
      (stackComparison.tower_higher_zero_of_h2Zero hh2)
      (stackComparison.tower_stack_zero_of_effective hstacky)

/-! ## Legacy triple-overlap shadow and selected witness -/

/-- Visible shadow from the old triple-overlap witness to stacky `H2`. -/
structure TripleOverlapStackyH2Shadow
    {Choice : Type z}
    (layer : FiniteRepairChoiceTransitionLayer Choice)
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) where
  triple_defect_forces_h2_nonzero :
    TripleOverlapDefect layer ->
      StackyRepairH2Nonzero stack
  h2_zero_forces_triple_coherent :
    StackyRepairH2Zero stack ->
      TripleOverlapCoherent layer

/-- A pointed torsor whose nonabelian descent is effective. -/
def selectedTrivialPointedRepairTorsor :
    FinitePointedRepairTorsor RepairChoiceToken Unit where
  choiceOrder :=
    [RepairChoiceToken.neutral,
      RepairChoiceToken.left,
      RepairChoiceToken.right,
      RepairChoiceToken.leftRight,
      RepairChoiceToken.rightLeft]
  repairOrder := [()]
  neutral := RepairChoiceToken.neutral
  compose := repairChoiceCompose
  inverse := fun _ => RepairChoiceToken.neutral
  selectedTransition := RepairChoiceToken.neutral
  selected_cocycle := rfl
  gauge := fun _ => RepairChoiceToken.neutral
  effectiveRepair := fun _ => True

/-- The selected trivial pointed torsor has effective nonabelian descent. -/
theorem selectedTrivialPointedRepairTorsor_effectiveDescent :
    EffectiveNonabelianRepairDescent selectedTrivialPointedRepairTorsor := by
  exact ⟨(), trivial, rfl⟩

/-- A finite stacky repair envelope with a nonzero selected 2-obstruction. -/
def selectedStackyRepairH2Envelope :
    FiniteStackyRepairH2Envelope RepairChoiceToken Unit where
  coherenceOrder :=
    [RepairChoiceToken.neutral,
      RepairChoiceToken.left,
      RepairChoiceToken.right,
      RepairChoiceToken.leftRight,
      RepairChoiceToken.rightLeft]
  repairOrder := [()]
  neutral2 := RepairChoiceToken.neutral
  compose2 := repairChoiceCompose
  selected2Cocycle := RepairChoiceToken.left
  selected2_cocycle := rfl
  boundary2 := fun _ => RepairChoiceToken.neutral
  effectiveRepair := fun _ => True

/-- The selected stacky envelope has nonzero stacky `H2`. -/
theorem selectedStackyRepairH2Envelope_h2Nonzero :
    StackyRepairH2Nonzero selectedStackyRepairH2Envelope := by
  refine ⟨rfl, ?_⟩
  intro hboundary
  rcases hboundary with ⟨repair, hboundary⟩
  change RepairChoiceToken.neutral = RepairChoiceToken.left at hboundary
  cases hboundary

/-- The selected stacky envelope has no effective stacky descent. -/
theorem selectedStackyRepairH2Envelope_no_effectiveDescent :
    Not (EffectiveStackyRepairDescent selectedStackyRepairH2Envelope) := by
  exact
    nonzero_stackyH2_no_effectiveDescent
      selectedStackyRepairH2Envelope
      selectedStackyRepairH2Envelope_h2Nonzero

/-- The old selected triple-overlap witness shadows the selected stacky `H2` obstruction. -/
def selectedTripleOverlapStackyH2Shadow :
    TripleOverlapStackyH2Shadow
      selectedTransitionLayer selectedStackyRepairH2Envelope where
  triple_defect_forces_h2_nonzero := by
    intro hdefect
    exact selectedStackyRepairH2Envelope_h2Nonzero
  h2_zero_forces_triple_coherent := by
    intro hzero
    exact False.elim
      (selectedStackyRepairH2Envelope_h2Nonzero.2 hzero.2)

/-- The selected triple-overlap defect maps to nonzero stacky `H2`. -/
theorem selectedTripleOverlapDefect_forces_stackyH2Nonzero :
    StackyRepairH2Nonzero selectedStackyRepairH2Envelope := by
  exact
    selectedTripleOverlapStackyH2Shadow.triple_defect_forces_h2_nonzero
      selectedTransitionLayer_tripleOverlapDefect

/--
Sheaf `H1` zero and effective nonabelian descent are not enough for stacky
repair descent.
-/
theorem sheafH1Zero_nonabelianDescent_not_enough_for_stackyDescent :
    SemanticRepairH1Zero selectedTorsorSheafEnvelope /\
      EffectiveNonabelianRepairDescent selectedTrivialPointedRepairTorsor /\
      StackyRepairH2Nonzero selectedStackyRepairH2Envelope /\
      Not (EffectiveStackyRepairDescent selectedStackyRepairH2Envelope) := by
  exact
    ⟨selectedTorsorSheafEnvelope_h1Zero,
      selectedTrivialPointedRepairTorsor_effectiveDescent,
      selectedStackyRepairH2Envelope_h2Nonzero,
      selectedStackyRepairH2Envelope_no_effectiveDescent⟩

/-- Cycle 7 finite stacky `H2` repair descent theorem package. -/
theorem finiteStackyH2RepairDescentEnvelope_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorComparison : NonabelianTorsorTowerComparison E torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackDischarge : StackyRepairDescentDischarge stack)
    (stackComparison : StackyH2TowerComparison E stack) :
    StackyCechZ2 stack stack.selected2Cocycle /\
      (StackyRepairH2Zero stack <-> StackyRepairTrivial stack) /\
      (StackyRepairTrivial stack <->
        EffectiveStackyRepairDescent stack) /\
      (EffectiveStackyRepairDescent stack <->
        StackyRepairH2Zero stack) /\
      (StackyRepairH2Nonzero stack ->
        Not (EffectiveStackyRepairDescent stack)) /\
      (HigherCoherenceVanishes (toFiniteTower E) <->
        StackyRepairH2Zero stack) /\
      (StackEffectivelyVanishes (toFiniteTower E) <->
        EffectiveStackyRepairDescent stack) /\
      (StackyRepairH2Nonzero stack ->
        Not (GlobalSemanticRepairCoherent (toFiniteTower E))) /\
      (SemanticRepairH1Zero E ->
        EffectiveNonabelianRepairDescent torsor ->
          EffectiveStackyRepairDescent stack ->
            GlobalSemanticRepairCoherent (toFiniteTower E)) := by
  exact
    ⟨stackyRepairH2_wellDefined stack,
      stackyH2Zero_iff_stackyRepairTrivial stack,
      stackyRepairTrivial_iff_effectiveStackyRepairDescent
        stack stackDischarge,
      effectiveStackyRepairDescent_iff_stackyH2Zero stack stackDischarge,
      nonzero_stackyH2_no_effectiveDescent stack,
      towerHigherToken_iff_stackyH2Zero stackComparison,
      towerStackToken_iff_effectiveStackyRepairDescent stackComparison,
      no_globalRepairCoherent_of_nonzero_stackyH2 E discharge stack
        stackComparison,
      globalRepairCoherent_of_sheafH1_nonabelian_and_stackyDescent
        E discharge torsor torsorComparison stack stackComparison⟩

end SemanticRepairStackyH2
end QualitySurface
end ResearchLean.AG
