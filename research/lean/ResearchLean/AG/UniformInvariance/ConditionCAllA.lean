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

/-- Normalize an incoming A-subnerve coefficient sum to its defining finite
edge sum. -/
@[simp] theorem targetSubsetFiberIncoming_apply {q : Reading Source}
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (chain : D.EdgeInTargetSubset A → ℚ)
    (chart : D.ChartInTargetSubset A) :
    targetSubsetFiberIncoming D A chain chart =
      (by
        classical
        exact ∑ edge,
          if D.targetSubsetEdgeRight A edge = chart then chain edge else 0) := by
  classical
  rfl

/-- Outgoing coefficient sum of a finite A-subnerve edge chain at one chart. -/
def targetSubsetFiberOutgoing {q : Reading Source}
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (chain : D.EdgeInTargetSubset A → ℚ)
    (chart : D.ChartInTargetSubset A) : ℚ := by
  classical
  exact ∑ edge,
    if D.targetSubsetEdgeLeft A edge = chart then chain edge else 0

/-- Normalize an outgoing A-subnerve coefficient sum to its defining finite
edge sum. -/
@[simp] theorem targetSubsetFiberOutgoing_apply {q : Reading Source}
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (chain : D.EdgeInTargetSubset A → ℚ)
    (chart : D.ChartInTargetSubset A) :
    targetSubsetFiberOutgoing D A chain chart =
      (by
        classical
        exact ∑ edge,
          if D.targetSubsetEdgeLeft A edge = chart then chain edge else 0) := by
  classical
  rfl

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

/-- Normalize an oriented A-subnerve face boundary to its three defining
finite face sums. -/
@[simp] theorem targetSubsetFaceBoundary_apply {q : Reading Source}
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (faces : D.FaceInTargetSubset A → ℚ)
    (edge : D.EdgeInTargetSubset A) :
    targetSubsetFaceBoundary D A faces edge =
      (by
        classical
        exact
          (∑ face,
            if D.targetSubsetFaceEdge0 A face = edge then faces face else 0) -
          (∑ face,
            if D.targetSubsetFaceEdge1 A face = edge then faces face else 0) +
          ∑ face,
            if D.targetSubsetFaceEdge2 A face = edge then faces face else 0) := by
  classical
  rfl

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

/-! ## Public no-unfold API -/

/-- Normalization rule exposing the underlying chart of the canonical
A-subnerve chart map. -/
@[simp]
theorem aSubnerveChartMap_coe
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (chart : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    (M.aSubnerveChartMap A chart).1 = M.chartMap chart.1 :=
  rfl

/-- Equality under the A-subnerve chart map is characterized by equality of
the underlying whole-nerve chart images. -/
theorem aSubnerveChartMap_eq_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineChart : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseChart : coarse.ChartInTargetSubset A) :
    M.aSubnerveChartMap A fineChart = coarseChart ↔
      M.chartMap fineChart.1 = coarseChart.1 := by
  constructor
  · intro hmap
    exact congrArg Subtype.val hmap
  · intro hmap
    exact Subtype.ext hmap

/-- Normalization rule characterizing a missing A-subnerve edge image by the
underlying whole-nerve partial edge map. -/
@[simp]
theorem aSubnerveEdgeMapOption_eq_none_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (edge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    M.aSubnerveEdgeMapOption A edge = none ↔ M.edgeMap edge.1 = none := by
  unfold aSubnerveEdgeMapOption targetSubsetEdgeMapOption
  split <;> simp_all

/-- A concrete A-subnerve edge image is characterized by the corresponding
whole-nerve edge image. -/
theorem aSubnerveEdgeMapOption_eq_some_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseEdge : coarse.EdgeInTargetSubset A) :
    M.aSubnerveEdgeMapOption A fineEdge = some coarseEdge ↔
      M.edgeMap fineEdge.1 = some coarseEdge.1 := by
  unfold aSubnerveEdgeMapOption targetSubsetEdgeMapOption
  split
  · simp_all
  · rename_i mappedEdge hmap
    constructor
    · intro hsubset
      have heq : mappedEdge = coarseEdge.1 :=
        congrArg Subtype.val (Option.some.inj hsubset)
      simpa [heq] using hmap
    · intro hwhole
      have heq : mappedEdge = coarseEdge.1 :=
        Option.some.inj (hmap.symm.trans hwhole)
      subst mappedEdge
      congr 1

/-- Normalization rule characterizing a missing A-subnerve face image by the
underlying whole-nerve partial face map. -/
@[simp]
theorem aSubnerveFaceMapOption_eq_none_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (face : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    M.aSubnerveFaceMapOption A face = none ↔ M.faceMap face.1 = none := by
  unfold aSubnerveFaceMapOption targetSubsetFaceMapOption
  split <;> simp_all

/-- A concrete A-subnerve face image is characterized by the corresponding
whole-nerve face image. -/
theorem aSubnerveFaceMapOption_eq_some_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseFace : coarse.FaceInTargetSubset A) :
    M.aSubnerveFaceMapOption A fineFace = some coarseFace ↔
      M.faceMap fineFace.1 = some coarseFace.1 := by
  unfold aSubnerveFaceMapOption targetSubsetFaceMapOption
  split
  · simp_all
  · rename_i mappedFace hmap
    constructor
    · intro hsubset
      have heq : mappedFace = coarseFace.1 :=
        congrArg Subtype.val (Option.some.inj hsubset)
      simpa [heq] using hmap
    · intro hwhole
      have heq : mappedFace = coarseFace.1 :=
        Option.some.inj (hmap.symm.trans hwhole)
      subst mappedFace
      congr 1

/-- A mapped A-subnerve edge carries its left endpoint to the left endpoint
of the displayed coarse edge. -/
theorem aSubnerveChartMap_edgeLeft_of_edgeMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseEdge : coarse.EdgeInTargetSubset A)
    (hmap : M.aSubnerveEdgeMapOption A fineEdge = some coarseEdge) :
    M.aSubnerveChartMap A
        (fine.targetSubsetEdgeLeft
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineEdge) =
      coarse.targetSubsetEdgeLeft A coarseEdge := by
  have hwhole : M.edgeMap fineEdge.1 = some coarseEdge.1 :=
    (M.aSubnerveEdgeMapOption_eq_some_iff A fineEdge coarseEdge).1 hmap
  apply Subtype.ext
  exact M.edge_some_left fineEdge.1 coarseEdge.1 hwhole

/-- A mapped A-subnerve edge carries its right endpoint to the right endpoint
of the displayed coarse edge. -/
theorem aSubnerveChartMap_edgeRight_of_edgeMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseEdge : coarse.EdgeInTargetSubset A)
    (hmap : M.aSubnerveEdgeMapOption A fineEdge = some coarseEdge) :
    M.aSubnerveChartMap A
        (fine.targetSubsetEdgeRight
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineEdge) =
      coarse.targetSubsetEdgeRight A coarseEdge := by
  have hwhole : M.edgeMap fineEdge.1 = some coarseEdge.1 :=
    (M.aSubnerveEdgeMapOption_eq_some_iff A fineEdge coarseEdge).1 hmap
  apply Subtype.ext
  exact M.edge_some_right fineEdge.1 coarseEdge.1 hwhole

/-- A degenerate A-subnerve edge has equal chart images at its two endpoints. -/
theorem aSubnerveChartMap_edgeLeft_eq_right_of_edgeMapOption_eq_none
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (hmap : M.aSubnerveEdgeMapOption A fineEdge = none) :
    M.aSubnerveChartMap A
        (fine.targetSubsetEdgeLeft
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineEdge) =
      M.aSubnerveChartMap A
        (fine.targetSubsetEdgeRight
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineEdge) := by
  have hwhole : M.edgeMap fineEdge.1 = none :=
    (M.aSubnerveEdgeMapOption_eq_none_iff A fineEdge).1 hmap
  apply Subtype.ext
  exact M.edge_none_fiber fineEdge.1 hwhole

/-- A mapped A-subnerve face maps boundary edge zero to boundary edge zero. -/
theorem aSubnerveEdgeMapOption_faceEdge0_of_faceMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseFace : coarse.FaceInTargetSubset A)
    (hmap : M.aSubnerveFaceMapOption A fineFace = some coarseFace) :
    M.aSubnerveEdgeMapOption A
        (fine.targetSubsetFaceEdge0
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineFace) =
      some (coarse.targetSubsetFaceEdge0 A coarseFace) := by
  apply (M.aSubnerveEdgeMapOption_eq_some_iff A _ _).2
  exact M.face_some_edge0 fineFace.1 coarseFace.1
    ((M.aSubnerveFaceMapOption_eq_some_iff A fineFace coarseFace).1 hmap)

/-- A mapped A-subnerve face maps boundary edge one to boundary edge one. -/
theorem aSubnerveEdgeMapOption_faceEdge1_of_faceMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseFace : coarse.FaceInTargetSubset A)
    (hmap : M.aSubnerveFaceMapOption A fineFace = some coarseFace) :
    M.aSubnerveEdgeMapOption A
        (fine.targetSubsetFaceEdge1
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineFace) =
      some (coarse.targetSubsetFaceEdge1 A coarseFace) := by
  apply (M.aSubnerveEdgeMapOption_eq_some_iff A _ _).2
  exact M.face_some_edge1 fineFace.1 coarseFace.1
    ((M.aSubnerveFaceMapOption_eq_some_iff A fineFace coarseFace).1 hmap)

/-- A mapped A-subnerve face maps boundary edge two to boundary edge two. -/
theorem aSubnerveEdgeMapOption_faceEdge2_of_faceMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (coarseFace : coarse.FaceInTargetSubset A)
    (hmap : M.aSubnerveFaceMapOption A fineFace = some coarseFace) :
    M.aSubnerveEdgeMapOption A
        (fine.targetSubsetFaceEdge2
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineFace) =
      some (coarse.targetSubsetFaceEdge2 A coarseFace) := by
  apply (M.aSubnerveEdgeMapOption_eq_some_iff A _ _).2
  exact M.face_some_edge2 fineFace.1 coarseFace.1
    ((M.aSubnerveFaceMapOption_eq_some_iff A fineFace coarseFace).1 hmap)

/-- Endpoint characterization of the A-subnerve fiber-edge predicate. -/
theorem targetSubsetFiberEdge_iff_endpoint_cells
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    M.TargetSubsetFiberEdge A coarseChart fineEdge ↔
      M.chartMap (fine.nerve.edgeLeft fineEdge.1) = coarseChart.1 ∧
      M.chartMap (fine.nerve.edgeRight fineEdge.1) = coarseChart.1 := by
  unfold TargetSubsetFiberEdge
  rw [M.aSubnerveChartMap_eq_iff, M.aSubnerveChartMap_eq_iff]
  rfl

/-- A fiber edge supplies undirected adjacency between its two endpoints. -/
theorem targetSubsetFiberAdjacent_of_edge
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (hfiber : M.TargetSubsetFiberEdge A coarseChart fineEdge) :
    M.TargetSubsetFiberAdjacent A coarseChart
        (fine.targetSubsetEdgeLeft
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineEdge)
        (fine.targetSubsetEdgeRight
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
          fineEdge) := by
  exact ⟨fineEdge, hfiber, Or.inl ⟨rfl, rfl⟩⟩

/-- Characterize A-subnerve fiber adjacency by a fiber edge and its two
possible endpoint orientations. -/
theorem targetSubsetFiberAdjacent_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (left right : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :
    M.TargetSubsetFiberAdjacent A coarseChart left right ↔
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
                fineEdge = left)) :=
  Iff.rfl

/-- A-subnerve fiber adjacency is symmetric. -/
theorem TargetSubsetFiberAdjacent.symm
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    {coarseChart : coarse.ChartInTargetSubset A}
    {left right : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)}
    (hadjacent : M.TargetSubsetFiberAdjacent A coarseChart left right) :
    M.TargetSubsetFiberAdjacent A coarseChart right left := by
  obtain ⟨fineEdge, hfiber, hendpoints⟩ := hadjacent
  exact ⟨fineEdge, hfiber, hendpoints.elim Or.inr Or.inl⟩

/-- Constructor for a rational cycle on an endpoint-defined A-subnerve fiber. -/
theorem targetSubsetFiberCycle_mk
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (chain : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) → ℚ)
    (hsupport : ∀ fineEdge,
      ¬ M.TargetSubsetFiberEdge A coarseChart fineEdge → chain fineEdge = 0)
    (hconservation : ∀ fineChart,
      M.aSubnerveChartMap A fineChart = coarseChart →
        targetSubsetFiberIncoming fine
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            chain fineChart =
          targetSubsetFiberOutgoing fine
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
            chain fineChart) :
    M.TargetSubsetFiberCycle A coarseChart chain :=
  ⟨hsupport, hconservation⟩

/-- A fiber cycle vanishes away from its endpoint-defined fiber graph. -/
theorem TargetSubsetFiberCycle.support
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    {coarseChart : coarse.ChartInTargetSubset A}
    {chain : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) → ℚ}
    (hcycle : M.TargetSubsetFiberCycle A coarseChart chain)
    (fineEdge)
    (houtside : ¬ M.TargetSubsetFiberEdge A coarseChart fineEdge) :
    chain fineEdge = 0 :=
  hcycle.1 fineEdge houtside

/-- A fiber cycle satisfies flow conservation at every chart of its fiber. -/
theorem TargetSubsetFiberCycle.conservation
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    {coarseChart : coarse.ChartInTargetSubset A}
    {chain : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A) → ℚ}
    (hcycle : M.TargetSubsetFiberCycle A coarseChart chain)
    (fineChart)
    (hmap : M.aSubnerveChartMap A fineChart = coarseChart) :
    targetSubsetFiberIncoming fine
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
        chain fineChart =
      targetSubsetFiberOutgoing fine
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
        chain fineChart :=
  hcycle.2 fineChart hmap

/-- Constructor for an internal A-subnerve face from its three fiber edges. -/
theorem targetSubsetInternalFace_mk
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (coarseChart : coarse.ChartInTargetSubset A)
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A))
    (hedge0 : M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge0 _ fineFace))
    (hedge1 : M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge1 _ fineFace))
    (hedge2 : M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge2 _ fineFace)) :
    M.TargetSubsetInternalFace A coarseChart fineFace :=
  ⟨hedge0, hedge1, hedge2⟩

/-- Boundary edge zero of an internal face lies in the same chart fiber. -/
theorem TargetSubsetInternalFace.edge0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    {coarseChart : coarse.ChartInTargetSubset A}
    {fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)}
    (hface : M.TargetSubsetInternalFace A coarseChart fineFace) :
    M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge0 _ fineFace) :=
  hface.1

/-- Boundary edge one of an internal face lies in the same chart fiber. -/
theorem TargetSubsetInternalFace.edge1
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    {coarseChart : coarse.ChartInTargetSubset A}
    {fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)}
    (hface : M.TargetSubsetInternalFace A coarseChart fineFace) :
    M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge1 _ fineFace) :=
  hface.2.1

/-- Boundary edge two of an internal face lies in the same chart fiber. -/
theorem TargetSubsetInternalFace.edge2
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    {coarseChart : coarse.ChartInTargetSubset A}
    {fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)}
    (hface : M.TargetSubsetInternalFace A coarseChart fineFace) :
    M.TargetSubsetFiberEdge A coarseChart
      (fine.targetSubsetFaceEdge2 _ fineFace) :=
  hface.2.2

/-- Constructor for C1 on one actual A-subnerve. -/
theorem conditionC1AtTargetSubset_intro
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (hfiber : ∀ coarseChart,
      (∃ fineChart, M.aSubnerveChartMap A fineChart = coarseChart) ∧
      ∀ left right,
        M.aSubnerveChartMap A left = coarseChart →
        M.aSubnerveChartMap A right = coarseChart →
        Relation.ReflTransGen
          (M.TargetSubsetFiberAdjacent A coarseChart) left right) :
    M.ConditionC1AtTargetSubset A :=
  hfiber

/-- C1 supplies a fine chart over every coarse A-subnerve chart. -/
theorem ConditionC1AtTargetSubset.fiber_nonempty
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    (hC1 : M.ConditionC1AtTargetSubset A)
    (coarseChart) :
    ∃ fineChart, M.aSubnerveChartMap A fineChart = coarseChart :=
  (hC1 coarseChart).1

/-- C1 connects any two fine charts over the same coarse A-subnerve chart. -/
theorem ConditionC1AtTargetSubset.connected
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    (hC1 : M.ConditionC1AtTargetSubset A)
    (coarseChart) (left right)
    (hleft : M.aSubnerveChartMap A left = coarseChart)
    (hright : M.aSubnerveChartMap A right = coarseChart) :
    Relation.ReflTransGen
      (M.TargetSubsetFiberAdjacent A coarseChart) left right :=
  (hC1 coarseChart).2 left right hleft hright

/-- Constructor for C2 on one actual A-subnerve. -/
theorem conditionC2AtTargetSubset_intro
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (hlift : ∀ coarseEdge, ∃ fineEdge,
      M.aSubnerveEdgeMapOption A fineEdge = some coarseEdge) :
    M.ConditionC2AtTargetSubset A :=
  hlift

/-- C2 supplies an exact fine lift of a displayed coarse A-subnerve edge. -/
theorem ConditionC2AtTargetSubset.lift
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    (hC2 : M.ConditionC2AtTargetSubset A)
    (coarseEdge) :
    ∃ fineEdge, M.aSubnerveEdgeMapOption A fineEdge = some coarseEdge :=
  hC2 coarseEdge

/-- Constructor for C3 on one actual A-subnerve. -/
theorem conditionC3AtTargetSubset_intro
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (hfill : ∀ coarseChart chain,
      M.TargetSubsetFiberCycle A coarseChart chain →
        ∃ faces,
          (∀ fineFace,
            ¬ M.TargetSubsetInternalFace A coarseChart fineFace →
              faces fineFace = 0) ∧
          ∀ fineEdge,
            chain fineEdge = targetSubsetFaceBoundary fine _ faces fineEdge) :
    M.ConditionC3AtTargetSubset A :=
  hfill

/-- C3 fills a displayed rational fiber cycle by internal fine faces. -/
theorem ConditionC3AtTargetSubset.fill
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    (hC3 : M.ConditionC3AtTargetSubset A)
    (coarseChart) (chain)
    (hcycle : M.TargetSubsetFiberCycle A coarseChart chain) :
    ∃ faces,
      (∀ fineFace,
        ¬ M.TargetSubsetInternalFace A coarseChart fineFace →
          faces fineFace = 0) ∧
      ∀ fineEdge,
        chain fineEdge = targetSubsetFaceBoundary fine _ faces fineEdge :=
  hC3 coarseChart chain hcycle

/-- Constructor for C4 on one actual A-subnerve. -/
theorem conditionC4AtTargetSubset_intro
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target)
    (hlift : ∀ coarseFace, ∃ fineFace,
      M.aSubnerveFaceMapOption A fineFace = some coarseFace) :
    M.ConditionC4AtTargetSubset A :=
  hlift

/-- C4 supplies an exact fine lift of a displayed coarse A-subnerve face. -/
theorem ConditionC4AtTargetSubset.lift
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {A : Set coarseReading.Target}
    (hC4 : M.ConditionC4AtTargetSubset A)
    (coarseFace) :
    ∃ fineFace, M.aSubnerveFaceMapOption A fineFace = some coarseFace :=
  hC4 coarseFace

/-- Constructor for the all-subset Atlas hypothesis. -/
theorem conditionCAllA_intro
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (h0 : M.ConditionC0)
    (hA : ∀ A : Set coarseReading.Target, A.Nonempty →
      M.ConditionC1AtTargetSubset A ∧
      M.ConditionC2AtTargetSubset A ∧
      M.ConditionC3AtTargetSubset A ∧
      M.ConditionC4AtTargetSubset A)
    (h5 : M.ConditionC5)
    (h6 : M.ConditionC6) :
    M.ConditionCAllA :=
  ⟨h0, hA, h5, h6⟩

/-- Projection of whole-nerve C0 from the all-subset Atlas hypothesis. -/
theorem ConditionCAllA.conditionC0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA) : M.ConditionC0 :=
  hC.1

/-- Projection of the four subset clauses at a nonempty target subset. -/
theorem ConditionCAllA.subsetClauses
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA)
    (A : Set coarseReading.Target) (hA : A.Nonempty) :
    M.ConditionC1AtTargetSubset A ∧
      M.ConditionC2AtTargetSubset A ∧
      M.ConditionC3AtTargetSubset A ∧
      M.ConditionC4AtTargetSubset A :=
  hC.2.1 A hA

/-- Projection of subset-relative C1 at a nonempty target subset. -/
theorem ConditionCAllA.conditionC1At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA)
    (A : Set coarseReading.Target) (hA : A.Nonempty) :
    M.ConditionC1AtTargetSubset A :=
  (ConditionCAllA.subsetClauses M hC A hA).1

/-- Projection of subset-relative C2 at a nonempty target subset. -/
theorem ConditionCAllA.conditionC2At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA)
    (A : Set coarseReading.Target) (hA : A.Nonempty) :
    M.ConditionC2AtTargetSubset A :=
  (ConditionCAllA.subsetClauses M hC A hA).2.1

/-- Projection of subset-relative C3 at a nonempty target subset. -/
theorem ConditionCAllA.conditionC3At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA)
    (A : Set coarseReading.Target) (hA : A.Nonempty) :
    M.ConditionC3AtTargetSubset A :=
  (ConditionCAllA.subsetClauses M hC A hA).2.2.1

/-- Projection of subset-relative C4 at a nonempty target subset. -/
theorem ConditionCAllA.conditionC4At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA)
    (A : Set coarseReading.Target) (hA : A.Nonempty) :
    M.ConditionC4AtTargetSubset A :=
  (ConditionCAllA.subsetClauses M hC A hA).2.2.2

/-- Projection of whole-nerve C5 from the all-subset Atlas hypothesis. -/
theorem ConditionCAllA.conditionC5
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA) : M.ConditionC5 :=
  hC.2.2.1

/-- Projection of whole-nerve C6 from the all-subset Atlas hypothesis. -/
theorem ConditionCAllA.conditionC6
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hC : M.ConditionCAllA) : M.ConditionC6 :=
  hC.2.2.2

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
