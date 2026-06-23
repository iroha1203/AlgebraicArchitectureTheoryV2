import Formal.AG.Research.QualitySurface.SemanticRepairTowerFunctoriality

/-!
Cycle 4 evidence for `G-aat-quality-surface-04`.

The previous cycles built a finite obstruction tower, discharged its visible
adequacy premise, and added finite tower functoriality.  This file adds a
finite nonabelian / higher transition witness layer.  It separates the first
Cech-style `H1` boundary from nonabelian repair-choice and triple-overlap
coherence defects: the selected witness has first-layer `H1` vanishing, but a
noncommuting repair-choice pair and a triple-overlap defect obstruct the later
tower layers.

The result remains finite and target-support only.  It does not construct a
full nonabelian cohomology theory, an arbitrary higher stack, runtime repair
synthesis, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairNonabelianTriple

open SemanticRepairObstructionTower
open SemanticRepairAdequacyDischarge

universe u v w x y z

/-! ## Finite repair-choice transition layer -/

/-- A small symbolic finite repair-choice vocabulary with noncommuting composites. -/
inductive RepairChoiceToken where
  | neutral
  | left
  | right
  | leftRight
  | rightLeft

/-- A deliberately finite noncommuting composition table for repair choices. -/
def repairChoiceCompose :
    RepairChoiceToken -> RepairChoiceToken -> RepairChoiceToken
  | RepairChoiceToken.neutral, choice => choice
  | RepairChoiceToken.left, RepairChoiceToken.neutral => RepairChoiceToken.left
  | RepairChoiceToken.left, RepairChoiceToken.left => RepairChoiceToken.neutral
  | RepairChoiceToken.left, RepairChoiceToken.right =>
      RepairChoiceToken.leftRight
  | RepairChoiceToken.left, RepairChoiceToken.leftRight =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.left, RepairChoiceToken.rightLeft =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.right, RepairChoiceToken.neutral =>
      RepairChoiceToken.right
  | RepairChoiceToken.right, RepairChoiceToken.left =>
      RepairChoiceToken.rightLeft
  | RepairChoiceToken.right, RepairChoiceToken.right =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.right, RepairChoiceToken.leftRight =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.right, RepairChoiceToken.rightLeft =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.leftRight, RepairChoiceToken.neutral =>
      RepairChoiceToken.leftRight
  | RepairChoiceToken.leftRight, RepairChoiceToken.left =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.leftRight, RepairChoiceToken.right =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.leftRight, RepairChoiceToken.leftRight =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.leftRight, RepairChoiceToken.rightLeft =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.rightLeft, RepairChoiceToken.neutral =>
      RepairChoiceToken.rightLeft
  | RepairChoiceToken.rightLeft, RepairChoiceToken.left =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.rightLeft, RepairChoiceToken.right =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.rightLeft, RepairChoiceToken.leftRight =>
      RepairChoiceToken.neutral
  | RepairChoiceToken.rightLeft, RepairChoiceToken.rightLeft =>
      RepairChoiceToken.neutral

/--
A finite transition layer on a triple overlap.

The fields are local transition tokens and a composition law.  They do not
store tower vanishing, global coherence, or stack effectiveness.
-/
structure FiniteRepairChoiceTransitionLayer (Choice : Type z) where
  compose : Choice -> Choice -> Choice
  g01 : Choice
  g12 : Choice
  g02 : Choice

/-- The selected pair of repair-choice transitions commutes. -/
def SelectedPairCommutes
    {Choice : Type z}
    (layer : FiniteRepairChoiceTransitionLayer Choice) : Prop :=
  layer.compose layer.g01 layer.g12 =
    layer.compose layer.g12 layer.g01

/-- The selected triple-overlap transition is coherent. -/
def TripleOverlapCoherent
    {Choice : Type z}
    (layer : FiniteRepairChoiceTransitionLayer Choice) : Prop :=
  layer.compose layer.g01 layer.g12 = layer.g02

/-- The selected pair has a nonabelian commutator defect. -/
def SelectedPairNoncommuting
    {Choice : Type z}
    (layer : FiniteRepairChoiceTransitionLayer Choice) : Prop :=
  Not (SelectedPairCommutes layer)

/-- The selected triple-overlap has a higher coherence defect. -/
def TripleOverlapDefect
    {Choice : Type z}
    (layer : FiniteRepairChoiceTransitionLayer Choice) : Prop :=
  Not (TripleOverlapCoherent layer)

/--
Soundness bridge from finite tower tokens to the explicit transition layer.

This is intentionally one-way: if the finite tower token vanishes, the
corresponding transition law is coherent.  The bridge does not contain tower
vanishing, global coherence, or the target equivalence.
-/
structure TransitionLayerSoundness
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    {Choice : Type z}
    (layer : FiniteRepairChoiceTransitionLayer Choice) where
  torsor_trivial_sound :
    NonabelianTorsorTrivial T -> SelectedPairCommutes layer
  higher_vanishes_sound :
    HigherCoherenceVanishes T -> TripleOverlapCoherent layer

/-! ## Defect obstruction theorems -/

/-- A noncommuting selected pair obstructs nonabelian torsor triviality. -/
theorem noncommuting_obstructs_nonabelianTorsorTrivial
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {Choice : Type z}
    {layer : FiniteRepairChoiceTransitionLayer Choice}
    (sound : TransitionLayerSoundness T layer) :
    SelectedPairNoncommuting layer ->
      Not (NonabelianTorsorTrivial T) := by
  intro hnoncommuting htorsor
  exact hnoncommuting (sound.torsor_trivial_sound htorsor)

/-- A triple-overlap defect obstructs higher coherence vanishing. -/
theorem tripleOverlapDefect_obstructs_higherCoherenceVanishes
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {Choice : Type z}
    {layer : FiniteRepairChoiceTransitionLayer Choice}
    (sound : TransitionLayerSoundness T layer) :
    TripleOverlapDefect layer ->
      Not (HigherCoherenceVanishes T) := by
  intro hdefect hhigher
  exact hdefect (sound.higher_vanishes_sound hhigher)

/-- Any noncommuting selected pair obstructs full finite tower vanishing. -/
theorem noncommuting_obstructs_obstructionTowerVanishes
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {Choice : Type z}
    {layer : FiniteRepairChoiceTransitionLayer Choice}
    (sound : TransitionLayerSoundness T layer) :
    SelectedPairNoncommuting layer ->
      Not (ObstructionTowerVanishes T) := by
  intro hnoncommuting hvanishes
  exact
    noncommuting_obstructs_nonabelianTorsorTrivial sound
      hnoncommuting hvanishes.2.1

/-- Any triple-overlap defect obstructs full finite tower vanishing. -/
theorem tripleOverlapDefect_obstructs_obstructionTowerVanishes
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {Choice : Type z}
    {layer : FiniteRepairChoiceTransitionLayer Choice}
    (sound : TransitionLayerSoundness T layer) :
    TripleOverlapDefect layer ->
      Not (ObstructionTowerVanishes T) := by
  intro hdefect hvanishes
  exact
    tripleOverlapDefect_obstructs_higherCoherenceVanishes sound
      hdefect hvanishes.2.2.1

/--
A noncommuting repair-choice defect rules out global coherence under the
existing finite adequacy bridge.
-/
theorem noncommuting_obstructs_globalRepairCoherent
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {Choice : Type z}
    {layer : FiniteRepairChoiceTransitionLayer Choice}
    (adequacy : LayeredRepairAdequacy T)
    (sound : TransitionLayerSoundness T layer) :
    SelectedPairNoncommuting layer ->
      Not (GlobalSemanticRepairCoherent T) := by
  intro hnoncommuting hglobal
  exact
    noncommuting_obstructs_obstructionTowerVanishes sound hnoncommuting
      (globalRepairCoherent_forces_obstructionTowerVanishes
        T adequacy hglobal)

/--
A triple-overlap defect rules out global coherence under the existing finite
adequacy bridge.
-/
theorem tripleOverlapDefect_obstructs_globalRepairCoherent
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {Choice : Type z}
    {layer : FiniteRepairChoiceTransitionLayer Choice}
    (adequacy : LayeredRepairAdequacy T)
    (sound : TransitionLayerSoundness T layer) :
    TripleOverlapDefect layer ->
      Not (GlobalSemanticRepairCoherent T) := by
  intro hdefect hglobal
  exact
    tripleOverlapDefect_obstructs_obstructionTowerVanishes sound hdefect
      (globalRepairCoherent_forces_obstructionTowerVanishes
        T adequacy hglobal)

/-! ## Selected finite witness -/

/-- The selected finite nonabelian / triple-overlap transition layer. -/
def selectedTransitionLayer :
    FiniteRepairChoiceTransitionLayer RepairChoiceToken where
  compose := repairChoiceCompose
  g01 := RepairChoiceToken.left
  g12 := RepairChoiceToken.right
  g02 := RepairChoiceToken.rightLeft

/-- The selected repair-choice pair is noncommuting. -/
theorem selectedTransitionLayer_pairNoncommuting :
    SelectedPairNoncommuting selectedTransitionLayer := by
  intro hcommutes
  change RepairChoiceToken.leftRight = RepairChoiceToken.rightLeft at hcommutes
  cases hcommutes

/-- The selected triple overlap has a higher coherence defect. -/
theorem selectedTransitionLayer_tripleOverlapDefect :
    TripleOverlapDefect selectedTransitionLayer := by
  intro hcoherent
  change RepairChoiceToken.leftRight = RepairChoiceToken.rightLeft at hcoherent
  cases hcoherent

/--
A finite tower where first-layer `H1` vanishes but nonabelian and higher
transition tokens do not.
-/
def selectedTransitionDefectTower :
    FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} PUnit where
  Chart := Unit
  chartOrder := [()]
  C0 := Unit
  C1 := Bool
  C2 := Unit
  c0Order := [()]
  c1Order := [false, true]
  c2Zero := ()
  delta0 := fun _ => true
  delta1 := fun _ => ()
  delta1_delta0_zero := by
    intro primitive
    rfl
  residual := true
  residual_cocycle := rfl
  primitiveSemanticallyClosed := fun _ => True
  torsorObstruction := true
  higherObstruction := true
  stackObstruction := false
  finiteShadow := fun _ => false
  finiteShadow_boundary_zero := by
    intro primitive
    rfl
  sourceTraceToken := fun _ => false

/-- The selected tower has first-layer `H1` vanishing. -/
theorem selectedTransitionDefectTower_h1Vanishes :
    H1Vanishes selectedTransitionDefectTower := by
  exact ⟨(), rfl⟩

/-- The selected tower does not have nonabelian torsor triviality. -/
theorem selectedTransitionDefectTower_not_nonabelianTorsorTrivial :
    Not (NonabelianTorsorTrivial selectedTransitionDefectTower) := by
  intro htorsor
  cases htorsor

/-- The selected tower does not have higher coherence vanishing. -/
theorem selectedTransitionDefectTower_not_higherCoherenceVanishes :
    Not (HigherCoherenceVanishes selectedTransitionDefectTower) := by
  intro hhigher
  cases hhigher

/-- The selected tower's adequacy bridge remains explicit and conditional. -/
def selectedTransitionDefectTower_adequacy :
    LayeredRepairAdequacy selectedTransitionDefectTower where
  semanticFaithful_of_boundary := by
    intro primitive _hboundary
    trivial
  torsorEffective_of_trivial := by
    intro h
    exact h
  torsorTrivial_of_effective := by
    intro h
    exact h
  higherEffective_of_vanishes := by
    intro h
    exact h
  higherVanishes_of_effective := by
    intro h
    exact h
  stackEffective_of_vanishes := by
    intro h
    exact h
  stackVanishes_of_effective := by
    intro h
    exact h

/-- The selected transition layer is soundly read by the selected tower tokens. -/
def selectedTransitionLayer_soundness :
    TransitionLayerSoundness
      selectedTransitionDefectTower selectedTransitionLayer where
  torsor_trivial_sound := by
    intro htorsor
    exact False.elim
      (selectedTransitionDefectTower_not_nonabelianTorsorTrivial htorsor)
  higher_vanishes_sound := by
    intro hhigher
    exact False.elim
      (selectedTransitionDefectTower_not_higherCoherenceVanishes hhigher)

/-- The selected transition defects obstruct full tower vanishing. -/
theorem selectedTransitionDefectTower_not_obstructionTowerVanishes :
    Not (ObstructionTowerVanishes selectedTransitionDefectTower) := by
  exact
    tripleOverlapDefect_obstructs_obstructionTowerVanishes
      selectedTransitionLayer_soundness
      selectedTransitionLayer_tripleOverlapDefect

/-- The selected transition defects obstruct global semantic repair coherence. -/
theorem selectedTransitionDefectTower_not_globalCoherent :
    Not (GlobalSemanticRepairCoherent selectedTransitionDefectTower) := by
  exact
    tripleOverlapDefect_obstructs_globalRepairCoherent
      selectedTransitionDefectTower_adequacy
      selectedTransitionLayer_soundness
      selectedTransitionLayer_tripleOverlapDefect

/--
First-layer `H1` vanishing alone is not enough for full tower descent when
nonabelian / higher transition defects remain.
-/
theorem h1Vanishes_not_enough_for_globalCoherent_due_transitionDefect :
    exists T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} PUnit,
      exists layer : FiniteRepairChoiceTransitionLayer RepairChoiceToken,
        H1Vanishes T /\
          TransitionLayerSoundness T layer /\
          SelectedPairNoncommuting layer /\
          TripleOverlapDefect layer /\
          Not (ObstructionTowerVanishes T) /\
          Not (GlobalSemanticRepairCoherent T) := by
  exact
    ⟨selectedTransitionDefectTower,
      selectedTransitionLayer,
      selectedTransitionDefectTower_h1Vanishes,
      selectedTransitionLayer_soundness,
      selectedTransitionLayer_pairNoncommuting,
      selectedTransitionLayer_tripleOverlapDefect,
      selectedTransitionDefectTower_not_obstructionTowerVanishes,
      selectedTransitionDefectTower_not_globalCoherent⟩

/-- Cycle 4 finite nonabelian / higher transition witness package. -/
theorem finiteNonabelianTripleOverlap_package :
    SelectedPairNoncommuting selectedTransitionLayer /\
      TripleOverlapDefect selectedTransitionLayer /\
      H1Vanishes selectedTransitionDefectTower /\
      Not (NonabelianTorsorTrivial selectedTransitionDefectTower) /\
      Not (HigherCoherenceVanishes selectedTransitionDefectTower) /\
      Not (ObstructionTowerVanishes selectedTransitionDefectTower) /\
      Not (GlobalSemanticRepairCoherent selectedTransitionDefectTower) /\
      (exists T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} PUnit,
        exists layer : FiniteRepairChoiceTransitionLayer RepairChoiceToken,
          H1Vanishes T /\
            TransitionLayerSoundness T layer /\
            SelectedPairNoncommuting layer /\
            TripleOverlapDefect layer /\
            Not (ObstructionTowerVanishes T) /\
            Not (GlobalSemanticRepairCoherent T)) := by
  exact
    ⟨selectedTransitionLayer_pairNoncommuting,
      selectedTransitionLayer_tripleOverlapDefect,
      selectedTransitionDefectTower_h1Vanishes,
      selectedTransitionDefectTower_not_nonabelianTorsorTrivial,
      selectedTransitionDefectTower_not_higherCoherenceVanishes,
      selectedTransitionDefectTower_not_obstructionTowerVanishes,
      selectedTransitionDefectTower_not_globalCoherent,
      h1Vanishes_not_enough_for_globalCoherent_due_transitionDefect⟩

end SemanticRepairNonabelianTriple
end QualitySurface
end Formal.AG.Research
