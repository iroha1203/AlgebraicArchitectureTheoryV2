import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditions
import ResearchLean.AG.UniformInvariance.ASubnerveReduction
import Formal.Util.AssertStandardAxioms

/-!
# Condition C on every target subnerve

This module begins claim (iii) of
`G-107-aat-uniform-invariance-characterization` by fixing the geometric
predicate whose locus the Atlas theorem will place inside the uniform locus.
The whole-nerve clauses C0, C5, and C6 are reused unchanged.  Clauses C1--C4
are read instead on every nonempty coarse target subset `A` and on its
canonical fine preimage under `comparisonFactor`.

## Implementation notes

The subset clauses use only K1 supports, chart/edge/face incidence, and the
canonical partial maps already constructed for actual A-subnerves.  They do
not mention a law family, adequacy, a cochain complex, cohomology, rank,
defect, uniformity, or a checker result.  Paths, lifts, and rational filling
chains occur only under propositions; no certificate is added to the input
geometry or to a finite presentation.

The predicate is deliberately fixed before its executable presentation-level
checker and before the bridge back to the law-indexed G-104 `ConditionC`.
Those later theorems must therefore decide and transport this independently
specified geometry rather than define a convenient surrogate for it.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution BigOperators

universe u

variable {Source : Type u}

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-! ## Canonical maps on one A-subnerve -/

/-- The canonical chart map from the fine preimage-A-subnerve to the coarse
A-subnerve. -/
def aSubnerveChartMap
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (chart : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    coarse.ChartInTargetSubset A :=
  M.targetSubsetChartMap A
    (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
    (fun _ htarget => htarget) chart

/-- The canonical partial edge map from the fine preimage-A-subnerve to the
coarse A-subnerve. -/
def aSubnerveEdgeMapOption
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (edge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    Option (coarse.EdgeInTargetSubset A) :=
  M.targetSubsetEdgeMapOption A
    (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
    (fun _ htarget => htarget) edge

/-- The canonical partial face map from the fine preimage-A-subnerve to the
coarse A-subnerve. -/
def aSubnerveFaceMapOption
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (face : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    Option (coarse.FaceInTargetSubset A) :=
  M.targetSubsetFaceMapOption A
    (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
    (fun _ htarget => htarget) face

/-! ## A-subnerve fiber incidence -/

/-- A fine A-subnerve edge lies in the endpoint-defined fiber of one coarse
A-subnerve chart when both endpoint images are that chart.  Its partial edge
image is deliberately not part of this predicate. -/
def TargetSubsetFiberEdge
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) : Prop :=
  M.aSubnerveChartMap A
      (fine.targetSubsetEdgeLeft
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) fineEdge) =
      coarseChart ∧
    M.aSubnerveChartMap A
      (fine.targetSubsetEdgeRight
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) fineEdge) =
      coarseChart

/-- Undirected adjacency inside one endpoint-defined A-subnerve chart fiber. -/
def TargetSubsetFiberAdjacent
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (left right : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) : Prop :=
  ∃ fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A),
    M.TargetSubsetFiberEdge A coarseChart fineEdge ∧
      ((fine.targetSubsetEdgeLeft
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            fineEdge = left ∧
          fine.targetSubsetEdgeRight
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            fineEdge = right) ∨
        (fine.targetSubsetEdgeLeft
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            fineEdge = right ∧
          fine.targetSubsetEdgeRight
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            fineEdge = left))

/-! ## Rational local cycles and boundaries -/

/-- Incoming coefficient sum of a finite A-subnerve edge chain at one chart. -/
def targetSubsetFiberIncoming {q : Reading Source}
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (chain : D.EdgeInTargetSubset A → ℚ)
    (chart : D.ChartInTargetSubset A) : ℚ := by
  classical
  exact ∑ edge,
    if D.targetSubsetEdgeRight A edge = chart then chain edge else 0

/-- Outgoing coefficient sum of a finite A-subnerve edge chain at one chart. -/
def targetSubsetFiberOutgoing {q : Reading Source}
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (chain : D.EdgeInTargetSubset A → ℚ)
    (chart : D.ChartInTargetSubset A) : ℚ := by
  classical
  exact ∑ edge,
    if D.targetSubsetEdgeLeft A edge = chart then chain edge else 0

/-- A rational one-cycle supported on the endpoint-defined graph over one
coarse A-subnerve chart. -/
def TargetSubsetFiberCycle
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (chain : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) → ℚ) : Prop :=
  (∀ fineEdge,
      ¬ M.TargetSubsetFiberEdge A coarseChart fineEdge →
        chain fineEdge = 0) ∧
    ∀ fineChart : fine.ChartInTargetSubset
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A),
      M.aSubnerveChartMap A fineChart = coarseChart →
        targetSubsetFiberIncoming fine
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            chain fineChart =
          targetSubsetFiberOutgoing fine
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            chain fineChart

/-- A fine A-subnerve face is internal to one chart fiber when each of its
three boundary edges has both endpoints in that fiber. -/
def TargetSubsetInternalFace
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) : Prop :=
  M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge0
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) fineFace) ∧
    M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge1
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) fineFace) ∧
    M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge2
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) fineFace)

/-- The oriented edge boundary of a finite rational A-subnerve face chain. -/
def targetSubsetFaceBoundary {q : Reading Source}
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (faces : D.FaceInTargetSubset A → ℚ)
    (edge : D.EdgeInTargetSubset A) : ℚ := by
  classical
  exact
    (∑ face,
      if D.targetSubsetFaceEdge0 A face = edge then faces face else 0) -
    (∑ face,
      if D.targetSubsetFaceEdge1 A face = edge then faces face else 0) +
    ∑ face,
      if D.targetSubsetFaceEdge2 A face = edge then faces face else 0

/-! ## The four subset-relative clauses -/

/-- C1 on one actual A-subnerve: every coarse chart fiber is nonempty and
connected by the full endpoint-defined fine fiber graph. -/
def ConditionC1AtTargetSubset
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target) : Prop :=
  ∀ coarseChart : coarse.ChartInTargetSubset A,
    (∃ fineChart : fine.ChartInTargetSubset
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A),
      M.aSubnerveChartMap A fineChart = coarseChart) ∧
    ∀ left right : fine.ChartInTargetSubset
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A),
      M.aSubnerveChartMap A left = coarseChart →
      M.aSubnerveChartMap A right = coarseChart →
      Relation.ReflTransGen
        (M.TargetSubsetFiberAdjacent A coarseChart) left right

/-- C2 on one actual A-subnerve: every coarse edge has an exact fine lift
under the canonical partial subset map. -/
def ConditionC2AtTargetSubset
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target) : Prop :=
  ∀ coarseEdge : coarse.EdgeInTargetSubset A,
    ∃ fineEdge : fine.EdgeInTargetSubset
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A),
      M.aSubnerveEdgeMapOption A fineEdge = some coarseEdge

/-- C3 on one actual A-subnerve: every rational cycle in an endpoint-defined
chart fiber is a rational combination of boundaries of internal faces. -/
def ConditionC3AtTargetSubset
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target) : Prop :=
  ∀ coarseChart : coarse.ChartInTargetSubset A,
    ∀ chain : fine.EdgeInTargetSubset
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) → ℚ,
      M.TargetSubsetFiberCycle A coarseChart chain →
        ∃ faces : fine.FaceInTargetSubset
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) → ℚ,
          (∀ fineFace,
            ¬ M.TargetSubsetInternalFace A coarseChart fineFace →
              faces fineFace = 0) ∧
          ∀ fineEdge,
            chain fineEdge =
              targetSubsetFaceBoundary fine
                (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
                faces fineEdge

/-- C4 on one actual A-subnerve: every coarse face has an exact fine lift
under the canonical partial subset map. -/
def ConditionC4AtTargetSubset
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target) : Prop :=
  ∀ coarseFace : coarse.FaceInTargetSubset A,
    ∃ fineFace : fine.FaceInTargetSubset
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A),
      M.aSubnerveFaceMapOption A fineFace = some coarseFace

/-! ## The all-subset Atlas hypothesis -/

/-- The geometric Atlas hypothesis: whole-nerve C0/C5/C6 together with
C1--C4 on every nonempty actual A-subnerve and canonical fine preimage.

This transparent proposition contains no law family, H¹ statement, rank,
defect, uniformity conclusion, or executable result bit. -/
def ConditionCAllA
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) : Prop :=
  M.ConditionC0 ∧
    (∀ A : Set coarseReading.Target, A.Nonempty →
      M.ConditionC1AtTargetSubset A ∧
      M.ConditionC2AtTargetSubset A ∧
      M.ConditionC3AtTargetSubset A ∧
      M.ConditionC4AtTargetSubset A) ∧
    M.ConditionC5 ∧
    M.ConditionC6

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
