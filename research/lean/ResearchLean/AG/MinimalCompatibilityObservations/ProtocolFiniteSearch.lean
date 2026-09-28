import ResearchLean.AG.MinimalCompatibilityObservations.FiniteAmbientTable
import ResearchLean.AG.MinimalCompatibilityObservations.GreedySelection
import ResearchLean.AG.MinimalCompatibilityObservations.FiniteMinimum
import Formal.Util.AssertStandardAxioms

/-!
# G-128: finite observation searches on primitive protocols

The surrounding changes and E1 membership test are generated from the
original protocol data and supplied execution tables.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction

universe u v w

variable {Q : FixedFDirectedMultigraph.{u, v}}
variable (P : FiniteProtocolInput.{u, v, w} Q)
variable [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
  [∀ v : Q.Vertex, DecidableEq (P.data.Fiber v)]
variable (visible : ExplicitEnumeration P.H)
  (vertices : ExplicitEnumeration Q.Vertex)
  (edges : ExplicitEnumeration Q.Edge)
  (fibers : ∀ v, ExplicitEnumeration (P.data.Fiber v))

/-- Select a least full observation set using the original ambient changes
and E1 predicate. -/
def protocolFullMinimum : Option (Finset (ProtocolFullPoints P.data)) := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact minimumObservation (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolFullPoints P.data vertices edges fibers)

/-- A returned full-point set is sufficient and no larger than any other
sufficient finite set for this original protocol action. -/
theorem protocolFullMinimum_some
    (B : Finset (ProtocolFullPoints P.data))
    (h : protocolFullMinimum P visible vertices edges fibers = some B) :
    letI := ambientFullAction P.data P.H
    Sufficient (compatibleChange P.data P.H) B ∧
      ∀ C : Finset (ProtocolFullPoints P.data),
        Sufficient (compatibleChange P.data P.H) C → B.card ≤ C.card := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact minimumObservation_some (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolFullPoints P.data vertices edges fibers) B
    (by simpa only [protocolFullMinimum] using h)

/-- Run the finite greedy cover search on all full protocol points. -/
def protocolFullGreedy : Finset (ProtocolFullPoints P.data) ⊕
    ambientChange P.data P.H := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact greedyObservationSet (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolFullPoints P.data vertices edges fibers)

/-- The actual greedy output is sufficient, or carries an original ambient
change that no full observation can distinguish from identity for E1. -/
theorem protocolFullGreedy_correct :
    letI := ambientFullAction P.data P.H
    match protocolFullGreedy P visible vertices edges fibers with
    | Sum.inl B => Sufficient (compatibleChange P.data P.H) B
    | Sum.inr k => k ∉ compatibleChange P.data P.H ∧
        ∀ x : ProtocolFullPoints P.data, k • x = x := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  have h := greedyObservationSet_correct
    (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolFullPoints P.data vertices edges fibers)
  unfold protocolFullGreedy
  cases hg : greedyObservationSet (compatibleChange P.data P.H)
      (FiniteProtocolInput.ambientTable P visible vertices fibers)
      (allProtocolFullPoints P.data vertices edges fibers) with
  | inl B => simpa [hg] using h
  | inr k =>
      have hk : k ∉ compatibleChange P.data P.H ∧
          (∀ x : ProtocolFullPoints P.data, k • x = x) ∧
          minObservations (X := ProtocolFullPoints P.data)
            (compatibleChange P.data P.H) = ⊤ ∧
          optimalQueries (X := ProtocolFullPoints P.data)
            (compatibleChange P.data P.H) = ⊤ := by
        simpa [hg] using h
      exact ⟨hk.1, hk.2.1⟩

/-- Search the original ambient group for a compatible extension of a
full-point observation table. -/
def protocolFullCompatibleExtension
    (B : Finset (ProtocolFullPoints P.data))
    (t : {x : ProtocolFullPoints P.data // x ∈ B} →
      ProtocolFullPoints P.data) : Option (ambientChange P.data P.H) := by
  letI : DecidableEq (ProtocolFullPoints P.data) := inferInstance
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact findCompatibleExtension (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

/-- A successful compatible search returns the original ambient change with
the specified observation table and E1 membership. -/
theorem protocolFullCompatibleExtension_some
    (B : Finset (ProtocolFullPoints P.data))
    (t : {x : ProtocolFullPoints P.data // x ∈ B} →
      ProtocolFullPoints P.data)
    (a : ambientChange P.data P.H)
    (h : protocolFullCompatibleExtension P visible vertices edges fibers B t =
      some a) :
    letI := ambientFullAction P.data P.H
    observe B a = t ∧ a ∈ compatibleChange P.data P.H := by
  letI : DecidableEq (ProtocolFullPoints P.data) := inferInstance
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact findCompatibleExtension_some (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t a
    (by simpa only [protocolFullCompatibleExtension] using h)

/-- Search for any original ambient change realizing the full-point table. -/
def protocolFullExtension
    (B : Finset (ProtocolFullPoints P.data))
    (t : {x : ProtocolFullPoints P.data // x ∈ B} →
      ProtocolFullPoints P.data) : Option (ambientChange P.data P.H) := by
  letI : DecidableEq (ProtocolFullPoints P.data) := inferInstance
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact findExtension
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

/-- Select a least state-only observation set from the same ambient table. -/
def protocolStateMinimum : Option (Finset (ProtocolStates P.data)) := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact minimumObservation (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolStates P.data vertices fibers)

/-- Run the finite greedy cover search on states alone. -/
def protocolStateGreedy : Finset (ProtocolStates P.data) ⊕
    ambientChange P.data P.H := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact greedyObservationSet (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolStates P.data vertices fibers)

/-- A successful compatible search returns fiber maps satisfying E1 and
the specified table under the original full action. -/
theorem protocolFullCompatibleExtension_readback
    (B : Finset (ProtocolFullPoints P.data))
    (t : {x : ProtocolFullPoints P.data // x ∈ B} →
      ProtocolFullPoints P.data)
    (a : ambientChange P.data P.H)
    (h : protocolFullCompatibleExtension P visible vertices edges fibers B t =
      some a) :
    letI := ambientFullAction P.data P.H
    ∃ φ : ∀ v, P.data.Fiber v ≃ P.data.Fiber (a.1.1.1.vertex v),
      a = fiberPairToAmbient P.data P.H ⟨a.1.1, φ⟩ ∧
      (∀ (e : Q.Edge) (x : P.data.Fiber (Q.source e)),
        φ (Q.target e) (P.data.edgeEquiv e x) =
          P.data.renamedEdgeEquiv a.1.1.1 e (φ (Q.source e) x)) ∧
      observe B a = t := by
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  obtain ⟨ht, ha⟩ := protocolFullCompatibleExtension_some
    P visible vertices edges fibers B t a h
  let p := ambientEquivFiberPair P.data P.H a
  have hp : fiberPairToAmbient P.data P.H p = a :=
    (ambientEquivFiberPair P.data P.H).left_inv a
  have he1 := (fiberPair_compatible_iff P.data P.H p).1 (by
    rw [hp]
    exact ha)
  exact ⟨p.2, hp.symm, he1, ht⟩

/-- Compatible extension fails iff no E1 ambient change realizes the table. -/
theorem protocolFullCompatibleExtension_none_iff
    (B : Finset (ProtocolFullPoints P.data))
    (t : {x : ProtocolFullPoints P.data // x ∈ B} →
      ProtocolFullPoints P.data) :
    letI := ambientFullAction P.data P.H
    protocolFullCompatibleExtension P visible vertices edges fibers B t = none ↔
      ¬ ∃ a : ambientChange P.data P.H,
        a ∈ compatibleChange P.data P.H ∧ observe B a = t := by
  letI : DecidableEq (ProtocolFullPoints P.data) := inferInstance
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact findCompatibleExtension_none_iff (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

/-- Unconstrained extension succeeds with the original observation table. -/
theorem protocolFullExtension_some
    (B : Finset (ProtocolFullPoints P.data))
    (t : {x : ProtocolFullPoints P.data // x ∈ B} →
      ProtocolFullPoints P.data)
    (a : ambientChange P.data P.H)
    (h : protocolFullExtension P visible vertices fibers B t = some a) :
    letI := ambientFullAction P.data P.H
    observe B a = t := by
  letI : DecidableEq (ProtocolFullPoints P.data) := inferInstance
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact findExtension_some
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t a h

/-- Unconstrained extension fails iff the table has no ambient realization. -/
theorem protocolFullExtension_none_iff
    (B : Finset (ProtocolFullPoints P.data))
    (t : {x : ProtocolFullPoints P.data // x ∈ B} →
      ProtocolFullPoints P.data) :
    letI := ambientFullAction P.data P.H
    protocolFullExtension P visible vertices fibers B t = none ↔
      ¬ ∃ a : ambientChange P.data P.H, observe B a = t := by
  letI : DecidableEq (ProtocolFullPoints P.data) := inferInstance
  letI : MulAction (ambientChange P.data P.H) (ProtocolFullPoints P.data) :=
    ambientFullAction P.data P.H
  exact findExtension_none_iff
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

/-- The state-only minimum search returns an actual least sufficient set. -/
theorem protocolStateMinimum_some
    (B : Finset (ProtocolStates P.data))
    (h : protocolStateMinimum P visible vertices edges fibers = some B) :
    letI := ambientStateAction P.data P.H
    Sufficient (compatibleChange P.data P.H) B ∧
      ∀ C : Finset (ProtocolStates P.data),
        Sufficient (compatibleChange P.data P.H) C → B.card ≤ C.card := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact minimumObservation_some (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolStates P.data vertices fibers) B
    (by simpa only [protocolStateMinimum] using h)

/-- State-only greedy either gives a sufficient set or an incompatible
ambient change fixing every state. -/
theorem protocolStateGreedy_correct :
    letI := ambientStateAction P.data P.H
    match protocolStateGreedy P visible vertices edges fibers with
    | Sum.inl B => Sufficient (compatibleChange P.data P.H) B
    | Sum.inr k => k ∉ compatibleChange P.data P.H ∧
        ∀ x : ProtocolStates P.data,
          (ambientStateAction P.data P.H).smul k x = x := by
  letI : DecidableEq (ambientChange P.data P.H) :=
    ambientDecidableEq P.data P.H vertices edges fibers
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  have h := greedyObservationSet_correct
    (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers)
    (allProtocolStates P.data vertices fibers)
  unfold protocolStateGreedy
  cases hg : greedyObservationSet (compatibleChange P.data P.H)
      (FiniteProtocolInput.ambientTable P visible vertices fibers)
      (allProtocolStates P.data vertices fibers) with
  | inl B => simpa [hg] using h
  | inr k =>
      have hk : k ∉ compatibleChange P.data P.H ∧
          (∀ x : ProtocolStates P.data,
            (ambientStateAction P.data P.H).smul k x = x) ∧
          minObservations (X := ProtocolStates P.data)
            (compatibleChange P.data P.H) = ⊤ ∧
          optimalQueries (X := ProtocolStates P.data)
            (compatibleChange P.data P.H) = ⊤ := by
        simpa [hg] using h
      exact ⟨hk.1, hk.2.1⟩

/-- Search for an E1-compatible extension of a state-only observation table. -/
def protocolStateCompatibleExtension
    (B : Finset (ProtocolStates P.data))
    (t : {x : ProtocolStates P.data // x ∈ B} → ProtocolStates P.data) :
    Option (ambientChange P.data P.H) := by
  letI : DecidableEq (ProtocolStates P.data) := inferInstance
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact findCompatibleExtension (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

/-- A successful state-table search returns the original E1 change and
the specified observations. -/
theorem protocolStateCompatibleExtension_some
    (B : Finset (ProtocolStates P.data))
    (t : {x : ProtocolStates P.data // x ∈ B} → ProtocolStates P.data)
    (a : ambientChange P.data P.H)
    (h : protocolStateCompatibleExtension P visible vertices edges fibers B t =
      some a) :
    letI := ambientStateAction P.data P.H
    observe B a = t ∧ a ∈ compatibleChange P.data P.H := by
  letI : DecidableEq (ProtocolStates P.data) := inferInstance
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact findCompatibleExtension_some (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t a h

/-- State-table search failure excludes every E1-compatible extension. -/
theorem protocolStateCompatibleExtension_none_iff
    (B : Finset (ProtocolStates P.data))
    (t : {x : ProtocolStates P.data // x ∈ B} → ProtocolStates P.data) :
    letI := ambientStateAction P.data P.H
    protocolStateCompatibleExtension P visible vertices edges fibers B t = none ↔
      ¬ ∃ a : ambientChange P.data P.H,
        a ∈ compatibleChange P.data P.H ∧ observe B a = t := by
  letI : DecidableEq (ProtocolStates P.data) := inferInstance
  letI : DecidablePred (· ∈ compatibleChange P.data P.H) :=
    compatibleDecidablePred P.data P.H vertices edges fibers
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact findCompatibleExtension_none_iff (compatibleChange P.data P.H)
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

/-- Search for any original ambient extension of a state-only table. -/
def protocolStateExtension
    (B : Finset (ProtocolStates P.data))
    (t : {x : ProtocolStates P.data // x ∈ B} → ProtocolStates P.data) :
    Option (ambientChange P.data P.H) := by
  letI : DecidableEq (ProtocolStates P.data) := inferInstance
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact findExtension
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

omit [DecidableEq Q.Edge] in
/-- A returned ambient change realizes the original state table. -/
theorem protocolStateExtension_some
    (B : Finset (ProtocolStates P.data))
    (t : {x : ProtocolStates P.data // x ∈ B} → ProtocolStates P.data)
    (a : ambientChange P.data P.H)
    (h : protocolStateExtension P visible vertices fibers B t = some a) :
    letI := ambientStateAction P.data P.H
    observe B a = t := by
  letI : DecidableEq (ProtocolStates P.data) := inferInstance
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact findExtension_some
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t a h

omit [DecidableEq Q.Edge] in
/-- Failure excludes every original ambient realization of the state table. -/
theorem protocolStateExtension_none_iff
    (B : Finset (ProtocolStates P.data))
    (t : {x : ProtocolStates P.data // x ∈ B} → ProtocolStates P.data) :
    letI := ambientStateAction P.data P.H
    protocolStateExtension P visible vertices fibers B t = none ↔
      ¬ ∃ a : ambientChange P.data P.H, observe B a = t := by
  letI : DecidableEq (ProtocolStates P.data) := inferInstance
  letI : MulAction (ambientChange P.data P.H) (ProtocolStates P.data) :=
    ambientStateAction P.data P.H
  exact findExtension_none_iff
    (FiniteProtocolInput.ambientTable P visible vertices fibers) B t

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
