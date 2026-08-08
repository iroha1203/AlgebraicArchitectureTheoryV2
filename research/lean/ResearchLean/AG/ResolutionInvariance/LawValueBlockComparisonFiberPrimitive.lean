import Mathlib.LinearAlgebra.Dual.Lemmas
import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonFiberPeriods
import Formal.Util.AssertStandardAxioms

/-!
# Local primitives on exact law-value coordinate fibers

This module turns the Cycle 17 period-vanishing result into an actual local
degree-zero primitive.  The generic theorem treats finite directed multigraphs
with loops and parallel edges.  It masks edges outside a selected subgraph,
identifies the annihilator of the masked incidence kernel with the range of the
flipped incidence pairing, and obtains a vertex potential without choosing or
storing paths, a spanning tree, or a basis.

The specialization uses C3 through the actual exact-block cocycle period
theorem.  Its primitive is an existential theorem output and is not added to a
condition, morphism, or certificate field.  This module does not yet assemble
the chart-fiber primitives, descend the residual cochain, or prove H1
surjectivity.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open BigOperators CanonicalResolution TwoPhase

universe u

variable {Source : Type u}

namespace FiniteDirectedMultigraph

/-- On a finite directed multigraph, a rational edge value that annihilates
every supported circulation is the coboundary of a vertex potential on every
supported edge.  Loops and parallel edges are retained as distinct edges. -/
theorem exists_potential_on_of_annihilates_supported_cycles
    {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex]
    (edgeLeft edgeRight : Edge → Vertex)
    (supported : Edge → Prop)
    (value : Edge → ℚ)
    (hperiod : ∀ chain : Edge → ℚ,
      (∀ edge, ¬ supported edge → chain edge = 0) →
      (∀ vertex,
        (∑ edge, if edgeRight edge = vertex then chain edge else 0) =
          ∑ edge, if edgeLeft edge = vertex then chain edge else 0) →
      ∑ edge, chain edge * value edge = 0) :
    ∃ potential : Vertex → ℚ,
      ∀ edge, supported edge →
        potential (edgeRight edge) - potential (edgeLeft edge) = value edge := by
  classical
  let incidence : (Edge → ℚ) →ₗ[ℚ] (Vertex → ℚ) →ₗ[ℚ] ℚ := by
    apply LinearMap.mk₂ ℚ fun chain potential =>
      ∑ edge,
        if supported edge then
          chain edge *
            (potential (edgeRight edge) - potential (edgeLeft edge))
        else 0
    · intro x y potential
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hedge : supported edge <;> simp [hedge, add_mul]
    · intro scalar chain potential
      change
        (∑ edge,
          if supported edge then
            (scalar * chain edge) *
              (potential (edgeRight edge) - potential (edgeLeft edge))
          else 0) =
        scalar * ∑ edge,
          if supported edge then
            chain edge *
              (potential (edgeRight edge) - potential (edgeLeft edge))
          else 0
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hedge : supported edge <;> simp [hedge, mul_assoc]
    · intro chain p q
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hedge : supported edge
      · simp only [hedge, ↓reduceIte, Pi.add_apply]
        ring
      · simp [hedge]
    · intro scalar chain potential
      change
        (∑ edge,
          if supported edge then
            chain edge *
              (scalar * potential (edgeRight edge) -
                scalar * potential (edgeLeft edge))
          else 0) =
        scalar * ∑ edge,
          if supported edge then
            chain edge *
              (potential (edgeRight edge) - potential (edgeLeft edge))
          else 0
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hedge : supported edge
      · simp only [hedge, ↓reduceIte]
        ring
      · simp [hedge]
  let pairing : (Edge → ℚ) →ₗ[ℚ] ℚ := {
    toFun chain :=
      ∑ edge, if supported edge then chain edge * value edge else 0
    map_add' x y := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hedge : supported edge <;> simp [hedge, add_mul]
    map_smul' scalar chain := by
      change
        (∑ edge,
          if supported edge then
            (scalar * chain edge) * value edge
          else 0) =
        scalar * ∑ edge,
          if supported edge then chain edge * value edge else 0
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hedge : supported edge <;> simp [hedge, mul_assoc]
  }
  have hpairing : pairing ∈ (LinearMap.ker incidence).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro chain hchain
    have hincidenceZero : incidence chain = 0 :=
      LinearMap.mem_ker.mp hchain
    have hconservation : ∀ vertex,
        (∑ edge,
            if edgeRight edge = vertex then
              (if supported edge then chain edge else 0)
            else 0) =
          ∑ edge,
            if edgeLeft edge = vertex then
              (if supported edge then chain edge else 0)
            else 0 := by
      intro vertex
      have hvalue :=
        LinearMap.congr_fun hincidenceZero (Pi.single vertex (1 : ℚ))
      change
        (∑ edge,
          if supported edge then
            chain edge *
              ((Pi.single vertex (1 : ℚ) : Vertex → ℚ) (edgeRight edge) -
                (Pi.single vertex (1 : ℚ) : Vertex → ℚ) (edgeLeft edge))
          else 0) = 0 at hvalue
      have hrewrite :
          (∑ edge,
            if supported edge then
              chain edge *
                ((Pi.single vertex (1 : ℚ) : Vertex → ℚ) (edgeRight edge) -
                  (Pi.single vertex (1 : ℚ) : Vertex → ℚ) (edgeLeft edge))
            else 0) =
          (∑ edge,
              if edgeRight edge = vertex then
                (if supported edge then chain edge else 0)
              else 0) -
            ∑ edge,
              if edgeLeft edge = vertex then
                (if supported edge then chain edge else 0)
              else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro edge _
        by_cases hedge : supported edge
        · by_cases hright : edgeRight edge = vertex <;>
            by_cases hleft : edgeLeft edge = vertex <;>
              simp [hedge, hright, hleft, Pi.single_apply]
        · simp [hedge]
      rw [hrewrite] at hvalue
      exact sub_eq_zero.mp hvalue
    have hzero := hperiod (fun edge => if supported edge then chain edge else 0)
      (by intro edge hedge; simp [hedge]) hconservation
    change (∑ edge, if supported edge then chain edge * value edge else 0) = 0
    simpa using hzero
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hpairing
  obtain ⟨potential, hpotential⟩ := hpairing
  refine ⟨potential, ?_⟩
  intro edge hedge
  have hvalue :=
    LinearMap.congr_fun hpotential (Pi.single edge (1 : ℚ))
  change
    (∑ other,
      if supported other then
        (Pi.single edge (1 : ℚ) : Edge → ℚ) other *
          (potential (edgeRight other) - potential (edgeLeft other))
      else 0) =
    ∑ other,
      if supported other then
        (Pi.single edge (1 : ℚ) : Edge → ℚ) other * value other
      else 0 at hvalue
  have hleftSum :
      (∑ other,
        if supported other then
          (Pi.single edge (1 : ℚ) : Edge → ℚ) other *
            (potential (edgeRight other) - potential (edgeLeft other))
        else 0) =
      potential (edgeRight edge) - potential (edgeLeft edge) := by
    rw [Finset.sum_eq_single edge]
    · simp [hedge]
    · intro other _ hne
      simp [hne]
    · simp
  have hrightSum :
      (∑ other,
        if supported other then
          (Pi.single edge (1 : ℚ) : Edge → ℚ) other * value other
        else 0) = value edge := by
    rw [Finset.sum_eq_single edge]
    · simp [hedge]
    · intro other _ hne
      simp [hne]
    · simp
  rw [hleftSum, hrightSum] at hvalue
  exact hvalue

end FiniteDirectedMultigraph

/-- Module-local exact-block chart finiteness, derived from the canonical
coordinate subnerve instance fixed in Cycle 14. -/
noncomputable local instance exactBlockChartFintypeForPrimitive [Fintype Source]
    {q : Reading Source}
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    Fintype (D.ChartBlockCoordinate laws hadequate label) := by
  change Fintype (D.lawValueCoordinateSubnerve laws hadequate label).Chart
  infer_instance

/-- Module-local exact-block edge finiteness, derived from the canonical
coordinate subnerve instance fixed in Cycle 14. -/
noncomputable local instance exactBlockEdgeFintypeForPrimitive [Fintype Source]
    {q : Reading Source}
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    Fintype (D.EdgeBlockCoordinate laws hadequate label) := by
  change Fintype
    (D.lawValueCoordinateSubnerve laws hadequate label).EdgeComponent
  infer_instance

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-- C3 and the actual block cocycle equation produce a degree-zero primitive
on every exact coordinate fiber.  The primitive is existential and is asserted
only on endpoint-defined fiber edges. -/
theorem lawValueBlockCycle_exists_coordinateFiberPrimitive [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC3 : M.ConditionC3At laws hcoarse hfine label)
    (cycle :
      LinearMap.ker (fine.lawValueBlockComplex laws hfine label).d1)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label) :
    ∃ primitive : fine.ChartBlockCoordinate laws hfine label → ℚ,
      ∀ fineEdge,
        M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge →
          fine.lawValueBlockD0 laws hfine label primitive fineEdge =
            cycle.1 fineEdge := by
  classical
  obtain ⟨primitive, hprimitive⟩ :=
    FiniteDirectedMultigraph.exists_potential_on_of_annihilates_supported_cycles
      (fine.edgeLeftBlockCoordinate laws hfine label)
      (fine.edgeRightBlockCoordinate laws hfine label)
      (M.CoordinateFiberEdge laws hcoarse hfine label coarseChart)
      cycle.1 (by
        intro chain hsupport hconservation
        apply M.lawValueBlockCycle_annihilates_coordinateFiberCycle laws
          hcoarse hfine label hC3 cycle coarseChart chain
        refine ⟨hsupport, ?_⟩
        intro fineChart _hchart
        simpa [coordinateFiberIncoming, coordinateFiberOutgoing] using
          hconservation fineChart)
  refine ⟨primitive, ?_⟩
  intro fineEdge hedge
  exact hprimitive fineEdge hedge

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
