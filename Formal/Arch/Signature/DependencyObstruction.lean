import Formal.Arch.Core.Matrix

namespace Formal.Arch

universe u

/--
A dependency obstruction witness is a nonempty closed walk.

This packages `HasClosedWalk` as a first-class witness type so dependency
cycles can use the generic obstruction-count kernel without forcing them into
an equality-diagram shape.
-/
structure ClosedWalkWitness {C : Type u} (G : ArchGraph C) where
  vertex : C
  walk : Walk G vertex vertex
  nonempty : 0 < walk.length

/-- A closed-walk witness is itself the forbidden obstruction. -/
def ClosedWalkBad {C : Type u} {G : ArchGraph C}
    (_w : ClosedWalkWitness G) : Prop :=
  True

instance instDecidablePredClosedWalkBad {C : Type u} {G : ArchGraph C} :
    DecidablePred (@ClosedWalkBad C G) := by
  intro _w
  exact isTrue trivial

/-- Measured closed-walk obstruction witnesses. -/
def closedWalkViolatingWitnesses {C : Type u} {G : ArchGraph C}
    (witnesses : List (ClosedWalkWitness G)) :
    List (ClosedWalkWitness G) :=
  violatingWitnesses ClosedWalkBad witnesses

/-- Count measured closed-walk obstruction witnesses. -/
def closedWalkViolationCount {C : Type u} {G : ArchGraph C}
    (witnesses : List (ClosedWalkWitness G)) : Nat :=
  violationCount ClosedWalkBad witnesses

/--
Membership in measured closed-walk violations is exactly membership in the
measured witness universe.
-/
theorem mem_closedWalkViolatingWitnesses_iff {C : Type u} {G : ArchGraph C}
    {witnesses : List (ClosedWalkWitness G)} {w : ClosedWalkWitness G} :
    w ∈ closedWalkViolatingWitnesses witnesses ↔ w ∈ witnesses := by
  simp [closedWalkViolatingWitnesses, ClosedWalkBad,
    mem_violatingWitnesses_iff]

/-- Zero measured closed-walk violations means the measured witness list is empty. -/
theorem closedWalkViolationCount_eq_zero_iff_forall_not_bad {C : Type u}
    {G : ArchGraph C} {witnesses : List (ClosedWalkWitness G)} :
    closedWalkViolationCount witnesses = 0 ↔
      ∀ w, w ∈ witnesses -> ¬ ClosedWalkBad w := by
  exact violationCount_eq_zero_iff_forall_not_bad

/-- A closed-walk witness exposes the existing `HasClosedWalk` predicate. -/
theorem hasClosedWalk_of_closedWalkWitness {C : Type u} {G : ArchGraph C}
    (w : ClosedWalkWitness G) : HasClosedWalk G :=
  ⟨w.vertex, w.walk, w.nonempty⟩

/-- Existing `HasClosedWalk` evidence can be packaged as an obstruction witness. -/
theorem exists_closedWalkWitness_of_hasClosedWalk {C : Type u} {G : ArchGraph C}
    (h : HasClosedWalk G) : ∃ w : ClosedWalkWitness G, ClosedWalkBad w := by
  rcases h with ⟨c, walk, hNonempty⟩
  exact ⟨⟨c, walk, hNonempty⟩, trivial⟩

/-- Closed-walk witnesses are exactly the existing `HasClosedWalk` predicate. -/
theorem hasClosedWalk_iff_exists_closedWalkWitness {C : Type u}
    {G : ArchGraph C} :
    HasClosedWalk G ↔ ∃ w : ClosedWalkWitness G, ClosedWalkBad w := by
  constructor
  · exact exists_closedWalkWitness_of_hasClosedWalk
  · rintro ⟨w, _⟩
    exact hasClosedWalk_of_closedWalkWitness w

/--
Walk acyclicity is exact absence of closed-walk obstruction witnesses.
-/
theorem walkAcyclic_iff_no_closedWalkObstruction {C : Type u}
    {G : ArchGraph C} :
    WalkAcyclic G ↔ ∀ w : ClosedWalkWitness G, ¬ ClosedWalkBad w := by
  constructor
  · intro hWalkAcyclic w _hBad
    exact hWalkAcyclic (hasClosedWalk_of_closedWalkWitness w)
  · intro hNoWitness hClosed
    rcases exists_closedWalkWitness_of_hasClosedWalk hClosed with ⟨w, hBad⟩
    exact hNoWitness w hBad

/--
Graph acyclicity is exact absence of closed-walk obstruction witnesses.
-/
theorem acyclic_iff_no_closedWalkObstruction {C : Type u} {G : ArchGraph C} :
    Acyclic G ↔ ∀ w : ClosedWalkWitness G, ¬ ClosedWalkBad w := by
  exact Iff.trans acyclic_iff_walkAcyclic walkAcyclic_iff_no_closedWalkObstruction

/--
On a finite component universe, adjacency nilpotence is exact absence of
closed-walk obstruction witnesses.
-/
theorem adjacencyNilpotent_iff_no_closedWalkObstruction {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    AdjacencyNilpotent U ↔ ∀ w : ClosedWalkWitness G, ¬ ClosedWalkBad w := by
  exact Iff.trans (adjacencyNilpotent_iff_walkAcyclic U)
    walkAcyclic_iff_no_closedWalkObstruction

/--
Adjacency nilpotence rules out closed-walk obstruction witnesses.
-/
theorem no_closedWalkObstruction_of_adjacencyNilpotent {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    {U : ComponentUniverse G} (hNil : AdjacencyNilpotent U) :
    ∀ w : ClosedWalkWitness G, ¬ ClosedWalkBad w :=
  (adjacencyNilpotent_iff_no_closedWalkObstruction U).mp hNil

/--
Absence of closed-walk obstruction witnesses gives adjacency nilpotence on a
finite component universe.
-/
theorem adjacencyNilpotent_of_no_closedWalkObstruction {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G)
    (hNoWitness : ∀ w : ClosedWalkWitness G, ¬ ClosedWalkBad w) :
    AdjacencyNilpotent U :=
  (adjacencyNilpotent_iff_no_closedWalkObstruction U).mpr hNoWitness

end Formal.Arch
