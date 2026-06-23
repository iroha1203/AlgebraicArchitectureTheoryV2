import Formal.AG.Research.QualitySurface.SemanticRepairSheafH1
import Formal.AG.Research.QualitySurface.SemanticRepairNonabelianTriple

/-!
Cycle 6 evidence for `G-aat-quality-surface-04`.

This file replaces the Bool-level nonabelian torsor token, inside the
finite/small target boundary, by a pointed repair-choice torsor envelope.  The
new surface separates nonabelian cocycles, boundaries, torsor triviality, and
effective nonabelian repair descent.  Effective descent is a predicate with a
repair witness, not a field of the torsor structure, and the equivalence with
torsor triviality is proved as a theorem.

The result is target support only.  It does not assert unrestricted
nonabelian cohomology, arbitrary Grothendieck-site torsors, runtime repair
synthesis, ArchMap correctness, higher-stack effectiveness, or whole-codebase
quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairNonabelianTorsor

open SemanticRepairObstructionTower
open SemanticRepairSheafH1
open SemanticRepairNonabelianTriple

universe u v w x y z r

/-! ## Finite pointed nonabelian repair torsors -/

/--
A finite/small pointed repair-choice torsor.

The structure records the finite repair-choice vocabulary, a selected
transition, and a way for an effective repair witness to gauge that transition.
It does not store torsor triviality, effective descent, global repair
coherence, tower vanishing, or stack effectiveness.
-/
structure FinitePointedRepairTorsor
    (Choice : Type z)
    (Repair : Type r) where
  choiceOrder : List Choice
  repairOrder : List Repair
  neutral : Choice
  compose : Choice -> Choice -> Choice
  inverse : Choice -> Choice
  selectedTransition : Choice
  selected_cocycle : compose selectedTransition neutral = selectedTransition
  gauge : Repair -> Choice
  effectiveRepair : Repair -> Prop

/-- Nonabelian Cech-style 1-cocycles in the finite pointed torsor. -/
def NonabelianCechZ1
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    (choice : Choice) : Prop :=
  torsor.compose choice torsor.neutral = choice

/-- Nonabelian Cech-style 1-boundaries in the finite pointed torsor. -/
def NonabelianCechB1
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    (choice : Choice) : Prop :=
  exists repair, torsor.gauge repair = choice

/-- The selected nonabelian repair `H1` class is zero. -/
def NonabelianRepairH1Zero
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) : Prop :=
  NonabelianCechZ1 torsor torsor.selectedTransition /\
    NonabelianCechB1 torsor torsor.selectedTransition

/-- The selected nonabelian repair `H1` class is nonzero. -/
def NonabelianRepairH1Nonzero
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) : Prop :=
  NonabelianCechZ1 torsor torsor.selectedTransition /\
    Not (NonabelianCechB1 torsor torsor.selectedTransition)

/-- The pointed torsor is trivial at the selected transition. -/
def PointedTorsorTrivial
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) : Prop :=
  NonabelianCechB1 torsor torsor.selectedTransition

/--
Effective nonabelian repair descent.

This is an independent predicate with a concrete repair witness.  It is not a
field of `FinitePointedRepairTorsor`.
-/
def EffectiveNonabelianRepairDescent
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) : Prop :=
  exists repair,
    torsor.effectiveRepair repair /\
      torsor.gauge repair = torsor.selectedTransition

/--
Visible discharge from a pointed torsor trivialization to an effective repair
witness.  It is not a field of `FinitePointedRepairTorsor`.
-/
structure NonabelianRepairTorsorDescentDischarge
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) where
  effective_of_trivialization :
    forall repair,
      torsor.gauge repair = torsor.selectedTransition ->
        torsor.effectiveRepair repair

/-- The selected nonabelian transition is a cocycle. -/
theorem nonabelianRepairTorsor_wellDefined
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) :
    NonabelianCechZ1 torsor torsor.selectedTransition := by
  exact torsor.selected_cocycle

/-- Zero nonabelian `H1` class is pointed torsor triviality. -/
theorem nonabelianH1Zero_iff_pointedTorsorTrivial
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) :
    NonabelianRepairH1Zero torsor <-> PointedTorsorTrivial torsor := by
  constructor
  · intro hzero
    exact hzero.2
  · intro htrivial
    exact ⟨torsor.selected_cocycle, htrivial⟩

/-- Pointed torsor triviality is equivalent to effective nonabelian repair descent. -/
theorem pointedTorsorTrivial_iff_effectiveNonabelianRepairDescent
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    (torsorDischarge : NonabelianRepairTorsorDescentDischarge torsor) :
    PointedTorsorTrivial torsor <->
      EffectiveNonabelianRepairDescent torsor := by
  constructor
  · intro htrivial
    rcases htrivial with ⟨repair, hgauge⟩
    exact
      ⟨repair,
        torsorDischarge.effective_of_trivialization repair hgauge,
        hgauge⟩
  · intro heffective
    rcases heffective with ⟨repair, _heffective, hgauge⟩
    exact ⟨repair, hgauge⟩

/-- Effective nonabelian repair descent is equivalent to zero nonabelian `H1`. -/
theorem effectiveNonabelianRepairDescent_iff_nonabelianH1Zero
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    (torsorDischarge : NonabelianRepairTorsorDescentDischarge torsor) :
    EffectiveNonabelianRepairDescent torsor <->
      NonabelianRepairH1Zero torsor := by
  constructor
  · intro heffective
    exact
      (nonabelianH1Zero_iff_pointedTorsorTrivial torsor).2
        ((pointedTorsorTrivial_iff_effectiveNonabelianRepairDescent
          torsor torsorDischarge).2 heffective)
  · intro hzero
    exact
      (pointedTorsorTrivial_iff_effectiveNonabelianRepairDescent
        torsor torsorDischarge).1
        ((nonabelianH1Zero_iff_pointedTorsorTrivial torsor).1 hzero)

/-- A nonzero nonabelian `H1` class rules out effective nonabelian repair descent. -/
theorem nonzero_nonabelianH1_no_effectiveDescent
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) :
    NonabelianRepairH1Nonzero torsor ->
      Not (EffectiveNonabelianRepairDescent torsor) := by
  intro hnonzero heffective
  rcases heffective with ⟨repair, _heffective, hgauge⟩
  exact hnonzero.2 ⟨repair, hgauge⟩

/-! ## Comparison with the finite obstruction tower -/

/--
Explicit comparison between a pointed torsor envelope and the old finite tower
token.  This is a visible bridge, not a field of the torsor itself.
-/
structure NonabelianTorsorTowerComparison
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) where
  tower_torsor_zero_of_trivial :
    PointedTorsorTrivial torsor ->
      NonabelianTorsorTrivial (toFiniteTower E)
  trivial_of_tower_torsor_zero :
    NonabelianTorsorTrivial (toFiniteTower E) ->
      PointedTorsorTrivial torsor

/-- The old tower token is exactly the pointed torsor triviality through the explicit bridge. -/
theorem towerNonabelianToken_iff_pointedTorsorTrivial
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    {Choice : Type z}
    {Repair : Type r}
    {torsor : FinitePointedRepairTorsor Choice Repair}
    (comparison : NonabelianTorsorTowerComparison E torsor) :
    NonabelianTorsorTrivial (toFiniteTower E) <->
      PointedTorsorTrivial torsor := by
  constructor
  · intro htower
    exact comparison.trivial_of_tower_torsor_zero htower
  · intro htrivial
    exact comparison.tower_torsor_zero_of_trivial htrivial

/--
Nonzero pointed torsor obstruction rules out global coherence through the
explicit tower comparison and the sheaf `H1` discharge.
-/
theorem no_globalRepairCoherent_of_nonzero_nonabelianH1
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    (comparison : NonabelianTorsorTowerComparison E torsor) :
    NonabelianRepairH1Nonzero torsor ->
      Not (GlobalSemanticRepairCoherent (toFiniteTower E)) := by
  intro hnonzero hglobal
  have htower :
      NonabelianTorsorTrivial (toFiniteTower E) :=
    (globalRepairCoherent_forces_obstructionTowerVanishes
      (toFiniteTower E)
      (layeredAdequacy_of_sheafH1Discharge discharge)
      hglobal).2.1
  exact hnonzero.2 (comparison.trivial_of_tower_torsor_zero htower)

/--
Zero sheaf `H1` plus effective nonabelian repair descent discharges the
nonabelian layer of global semantic repair coherence.
-/
theorem globalRepairCoherent_of_sheafH1_zero_and_effectiveNonabelianDescent
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    (comparison : NonabelianTorsorTowerComparison E torsor)
    (hzero : SemanticRepairH1Zero E)
    (heffective : EffectiveNonabelianRepairDescent torsor)
    (hhigher : HigherCoherenceVanishes (toFiniteTower E))
    (hstack : StackEffectivelyVanishes (toFiniteTower E)) :
    GlobalSemanticRepairCoherent (toFiniteTower E) := by
  have htrivial : PointedTorsorTrivial torsor :=
    by
      rcases heffective with ⟨repair, _heffective, hgauge⟩
      exact ⟨repair, hgauge⟩
  exact
    globalRepairCoherent_of_sheafH1_zero E discharge hzero
      (comparison.tower_torsor_zero_of_trivial htrivial)
      hhigher hstack

/-! ## Legacy finite transition shadow -/

/--
A visible shadow from the old selected transition layer to the pointed torsor
surface.  It records only comparison theorems.
-/
structure TransitionTorsorShadow
    {Choice : Type z}
    (layer : FiniteRepairChoiceTransitionLayer Choice)
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) where
  noncommuting_forces_nonzero :
    SelectedPairNoncommuting layer ->
      NonabelianRepairH1Nonzero torsor
  trivial_forces_pair_commutes :
    PointedTorsorTrivial torsor ->
      SelectedPairCommutes layer

/-! ## Selected finite witness -/

/-- A finite sheaf `H1` envelope whose first layer vanishes. -/
def selectedTorsorSheafSite :
    SemanticRepairSite PUnit where
  Chart := Unit
  chartOrder := [()]
  sourceTraceToken := fun _ => false

/-- The selected sheaf coefficient has every finite 1-cochain as a boundary. -/
def selectedTorsorSheafCoefficient :
    SemanticResidualCoefficientSheaf selectedTorsorSheafSite where
  C0 := Bool
  C1 := Bool
  C2 := Unit
  c0Order := [false, true]
  c1Order := [false, true]
  zero1 := false
  zero2 := ()
  delta0 := fun primitive => primitive
  delta1 := fun _ => ()
  zero1_cocycle := rfl
  delta1_delta0_zero := by
    intro primitive
    rfl
  residual := true
  residual_cocycle := rfl

/-- Selected first-layer sheaf envelope used to separate abelian and nonabelian descent. -/
def selectedTorsorSheafEnvelope :
    SemanticRepairSheafH1Envelope PUnit where
  site := selectedTorsorSheafSite
  coefficient := selectedTorsorSheafCoefficient
  primitiveSemanticallyClosed := fun _ => True
  torsorObstruction := true
  higherObstruction := false
  stackObstruction := false
  finiteShadow := fun _ => false
  finiteShadow_boundary_zero := by
    intro primitive
    rfl
  cohomologous := fun _ _ => True
  cohomologous_refl := by
    intro cochain
    trivial
  cohomologous_symm := by
    intro left right h
    trivial
  cohomologous_trans := by
    intro left middle right hleft hright
    trivial
  boundary_cohomologous_zero := by
    intro primitive
    trivial
  exact_boundary_of_cohomologous_zero := by
    intro cochain hcocycle hzero
    exact ⟨cochain, rfl⟩

/-- The selected sheaf envelope has zero first-layer sheaf `H1`. -/
theorem selectedTorsorSheafEnvelope_h1Zero :
    SemanticRepairH1Zero selectedTorsorSheafEnvelope := by
  exact ⟨rfl, trivial⟩

/-- A selected pointed torsor with a nontrivial repair-choice twist. -/
def selectedPointedRepairTorsor :
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
  selectedTransition := RepairChoiceToken.left
  selected_cocycle := rfl
  gauge := fun _ => RepairChoiceToken.neutral
  effectiveRepair := fun _ => True

/-- The selected pointed torsor has a nonzero nonabelian `H1` class. -/
theorem selectedPointedRepairTorsor_nonabelianH1Nonzero :
    NonabelianRepairH1Nonzero selectedPointedRepairTorsor := by
  refine ⟨rfl, ?_⟩
  intro hboundary
  rcases hboundary with ⟨repair, hgauge⟩
  change RepairChoiceToken.neutral = RepairChoiceToken.left at hgauge
  cases hgauge

/-- The selected pointed torsor has no effective nonabelian repair descent. -/
theorem selectedPointedRepairTorsor_no_effectiveDescent :
    Not (EffectiveNonabelianRepairDescent selectedPointedRepairTorsor) := by
  exact
    nonzero_nonabelianH1_no_effectiveDescent
      selectedPointedRepairTorsor
      selectedPointedRepairTorsor_nonabelianH1Nonzero

/-- The old selected transition witness shadows the selected pointed torsor. -/
def selectedTransitionTorsorShadow :
    TransitionTorsorShadow
      selectedTransitionLayer selectedPointedRepairTorsor where
  noncommuting_forces_nonzero := by
    intro hnoncommuting
    exact selectedPointedRepairTorsor_nonabelianH1Nonzero
  trivial_forces_pair_commutes := by
    intro htrivial
    exact False.elim
      (selectedPointedRepairTorsor_nonabelianH1Nonzero.2 htrivial)

/-- The selected old noncommuting transition witness maps to nonzero pointed torsor `H1`. -/
theorem selectedTransitionLayer_noncommuting_forces_torsorNonzero :
    NonabelianRepairH1Nonzero selectedPointedRepairTorsor := by
  exact
    selectedTransitionTorsorShadow.noncommuting_forces_nonzero
      selectedTransitionLayer_pairNoncommuting

/--
First-layer sheaf `H1` zero is not enough for effective nonabelian descent.

This is the finite/small anti-weakening witness for Cycle 6.
-/
theorem sheafH1Zero_not_enough_for_effectiveNonabelianDescent :
    SemanticRepairH1Zero selectedTorsorSheafEnvelope /\
      NonabelianRepairH1Nonzero selectedPointedRepairTorsor /\
      Not (EffectiveNonabelianRepairDescent selectedPointedRepairTorsor) := by
  exact
    ⟨selectedTorsorSheafEnvelope_h1Zero,
      selectedPointedRepairTorsor_nonabelianH1Nonzero,
      selectedPointedRepairTorsor_no_effectiveDescent⟩

/-- Cycle 6 pointed nonabelian repair torsor descent theorem package. -/
theorem finitePointedNonabelianRepairTorsorDescentEnvelope_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    (torsorDischarge : NonabelianRepairTorsorDescentDischarge torsor)
    (comparison : NonabelianTorsorTowerComparison E torsor) :
    NonabelianCechZ1 torsor torsor.selectedTransition /\
      (NonabelianRepairH1Zero torsor <->
        PointedTorsorTrivial torsor) /\
      (PointedTorsorTrivial torsor <->
        EffectiveNonabelianRepairDescent torsor) /\
      (EffectiveNonabelianRepairDescent torsor <->
        NonabelianRepairH1Zero torsor) /\
      (NonabelianRepairH1Nonzero torsor ->
        Not (EffectiveNonabelianRepairDescent torsor)) /\
      (NonabelianRepairH1Nonzero torsor ->
        Not (GlobalSemanticRepairCoherent (toFiniteTower E))) /\
      (SemanticRepairH1Zero E ->
        EffectiveNonabelianRepairDescent torsor ->
          HigherCoherenceVanishes (toFiniteTower E) ->
            StackEffectivelyVanishes (toFiniteTower E) ->
              GlobalSemanticRepairCoherent (toFiniteTower E)) := by
  exact
    ⟨nonabelianRepairTorsor_wellDefined torsor,
      nonabelianH1Zero_iff_pointedTorsorTrivial torsor,
      pointedTorsorTrivial_iff_effectiveNonabelianRepairDescent
        torsor torsorDischarge,
      effectiveNonabelianRepairDescent_iff_nonabelianH1Zero
        torsor torsorDischarge,
      nonzero_nonabelianH1_no_effectiveDescent torsor,
      no_globalRepairCoherent_of_nonzero_nonabelianH1
        E discharge torsor comparison,
      globalRepairCoherent_of_sheafH1_zero_and_effectiveNonabelianDescent
        E discharge torsor comparison⟩

end SemanticRepairNonabelianTorsor
end QualitySurface
end Formal.AG.Research
