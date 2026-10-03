import ResearchLean.AG.RelativeRepairComposition.W3GaugeLabels

/-!
# W3's original full gauge action and loop transformation

The formulas below are evaluations of actual affine conjugation on the
original e,f and their full translation coordinates, for every permission.
-/
namespace AAT.AG.RelativeRepairComposition.W3GaugeAction
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3GaugeLabels

/-- Actual conjugation changes the whole original e correction by b_t-b_s. -/
theorem gauge_first (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : GlobalLabels sheared S) (R : RealRepairs sheared S) :
    (parameters (NativeAffine.gauge geometry (reference sheared) (reference sheared)
      comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S) b R)).1 =
      (parameters R).1 + b.1 vertexT - b.1 vertexS := by
  change (NativeAffine.gauge geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S) b R).operation
      (name edgeE).2.2 0 = _
  rw [NativeAffine.gauge_value]
  change b.1 vertexT + R.operation (name edgeE).2.2 (-b.1 vertexS + 0) = _
  rw [add_zero]
  rw [actual_operation_apply]
  change b.1 vertexT + (-b.1 vertexS + (parameters R).1) = _
  abel_nf

/-- Actual conjugation changes the whole original f correction by b_s-T b_t. -/
theorem gauge_second (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : GlobalLabels sheared S) (R : RealRepairs sheared S) :
    (parameters (NativeAffine.gauge geometry (reference sheared) (reference sheared)
      comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S) b R)).2 =
      (parameters R).2 + b.1 vertexS - linearAction sheared (b.1 vertexT) := by
  change (NativeAffine.gauge geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S) b R).operation
      (name edgeF).2.2 0 = _
  rw [NativeAffine.gauge_value]
  change b.1 vertexS + R.operation (name edgeF).2.2 (-b.1 vertexT + 0) = _
  rw [add_zero]
  rw [actual_operation_apply]
  change b.1 vertexS + (linearAction sheared (-b.1 vertexT) + (parameters R).2) = _
  rw [map_neg]
  abel_nf

/-- The same original loop changes by the entire vector (I-T)b_s. -/
theorem gauge_loop (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : GlobalLabels sheared S) (R : RealRepairs sheared S) :
    let R' := NativeAffine.gauge geometry (reference sheared) (reference sheared)
      comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S) b R
    loopValue sheared (parameters R').1 (parameters R').2 =
      loopValue sheared (parameters R).1 (parameters R).2 +
        (b.1 vertexS - linearAction sheared (b.1 vertexS)) := by
  dsimp only
  unfold loopValue
  rw [gauge_first, gauge_second, map_sub, map_add]
  abel_nf

/-- Full original labels can send e to zero while retaining the entire original loop value. -/
theorem unrestricted_normal_parameters (sheared : Bool) (R : RealRepairs sheared candidates) :
    parameters (NativeAffine.gauge geometry (reference sheared) (reference sheared)
      comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges candidates)
      (unrestrictedLabel sheared 0 (-(parameters R).1)) R) =
        (0, loopValue sheared (parameters R).1 (parameters R).2) := by
  apply Prod.ext
  · rw [gauge_first, unrestricted_source, unrestricted_target]
    simp
  · rw [gauge_second, unrestricted_source, unrestricted_target, map_neg]
    unfold loopValue
    abel_nf

end AAT.AG.RelativeRepairComposition.W3GaugeAction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3GaugeAction
