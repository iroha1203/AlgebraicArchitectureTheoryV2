import ResearchLean.AG.ResolutionInvariance.LawValueCoordinateSubnerve
import Formal.Util.AssertStandardAxioms

/-!
# Incidence and support conditions for resolution invariance

This module fixes conditions C0--C6 from `G-104-aat-resolution-invariance`.
C0, C5, and C6 are conditions on the whole supported nerves.  C1--C4 are
quantified over every canonical law-value coordinate subnerve from Cycle 14.

C3 is stated only with local finite rational chains.  A fiber edge is any fine
block edge whose two endpoint coordinates map to the chosen coarse block
chart; it need not be declared degenerate.  No global complex, cohomology
group, comparison-map exactness, or isomorphism occurs in the condition
package.
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

/-! ## Whole-nerve conditions -/

/-- C0: each coarse chart support is exactly the union of the canonical images
of fine chart supports in its chart fiber. -/
def ConditionC0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) : Prop :=
  ∀ coarseChart coarseTarget,
    coarseTarget ∈ coarse.chartSupport coarseChart ↔
      ∃ fineChart fineTarget,
        M.chartMap fineChart = coarseChart ∧
        fineTarget ∈ fine.chartSupport fineChart ∧
        comparisonFactor coarseReading fineReading hcoarser fineTarget =
          coarseTarget

/-- C5: every whole-nerve coarse edge has at most one declared fine edge lift. -/
def ConditionC5
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) : Prop :=
  ∀ coarseEdge fineLeft fineRight,
    M.edgeMap fineLeft = some coarseEdge →
    M.edgeMap fineRight = some coarseEdge →
    fineLeft = fineRight

/-- C6: every fine edge mapped to a coarse self-loop is itself a self-loop.
This condition is independent of C5 and quantifies over every mapped edge. -/
def ConditionC6
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) : Prop :=
  ∀ fineEdge coarseEdge,
    M.edgeMap fineEdge = some coarseEdge →
    coarse.nerve.edgeLeft coarseEdge = coarse.nerve.edgeRight coarseEdge →
    fine.nerve.edgeLeft fineEdge = fine.nerve.edgeRight fineEdge

/-! ## Coordinate-relative fiber incidence -/

/-- A fine block edge lies in the fiber of one coarse block chart when both
endpoint coordinates map to that chart.  The edge map is deliberately absent. -/
def CoordinateFiberEdge
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (fineEdge : fine.EdgeBlockCoordinate laws hfine label) : Prop :=
  M.chartBlockCoordinateMap laws hcoarse hfine label
      (fine.edgeLeftBlockCoordinate laws hfine label fineEdge) = coarseChart ∧
    M.chartBlockCoordinateMap laws hcoarse hfine label
      (fine.edgeRightBlockCoordinate laws hfine label fineEdge) = coarseChart

/-- Characterize a block fiber edge by the images of its two endpoint
coordinates.  This is the public elimination rule for `CoordinateFiberEdge`. -/
theorem coordinateFiberEdge_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (fineEdge : fine.EdgeBlockCoordinate laws hfine label) :
    M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge ↔
      M.chartBlockCoordinateMap laws hcoarse hfine label
          (fine.edgeLeftBlockCoordinate laws hfine label fineEdge) =
        coarseChart ∧
      M.chartBlockCoordinateMap laws hcoarse hfine label
          (fine.edgeRightBlockCoordinate laws hfine label fineEdge) =
        coarseChart :=
  Iff.rfl

/-- Undirected adjacency inside one exact coordinate fiber. -/
def CoordinateFiberAdjacent
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (left right : fine.ChartBlockCoordinate laws hfine label) : Prop :=
  ∃ fineEdge : fine.EdgeBlockCoordinate laws hfine label,
    M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge ∧
      ((fine.edgeLeftBlockCoordinate laws hfine label fineEdge = left ∧
          fine.edgeRightBlockCoordinate laws hfine label fineEdge = right) ∨
        (fine.edgeLeftBlockCoordinate laws hfine label fineEdge = right ∧
          fine.edgeRightBlockCoordinate laws hfine label fineEdge = left))

/-- Characterize block-fiber adjacency by a fiber edge and either orientation
of its endpoints.  This is the public elimination rule for adjacency. -/
theorem coordinateFiberAdjacent_iff
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (left right : fine.ChartBlockCoordinate laws hfine label) :
    M.CoordinateFiberAdjacent laws hcoarse hfine label coarseChart left right ↔
      ∃ fineEdge : fine.EdgeBlockCoordinate laws hfine label,
        M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge ∧
          ((fine.edgeLeftBlockCoordinate laws hfine label fineEdge = left ∧
              fine.edgeRightBlockCoordinate laws hfine label fineEdge = right) ∨
            (fine.edgeLeftBlockCoordinate laws hfine label fineEdge = right ∧
              fine.edgeRightBlockCoordinate laws hfine label fineEdge = left)) :=
  Iff.rfl

/-- Block-fiber adjacency is symmetric. -/
theorem CoordinateFiberAdjacent.symm
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    {coarseChart : coarse.ChartBlockCoordinate laws hcoarse label}
    {left right : fine.ChartBlockCoordinate laws hfine label}
    (hadjacent : M.CoordinateFiberAdjacent laws hcoarse hfine label
      coarseChart left right) :
    M.CoordinateFiberAdjacent laws hcoarse hfine label
      coarseChart right left := by
  obtain ⟨fineEdge, hfiber, hendpoints⟩ := hadjacent
  exact ⟨fineEdge, hfiber, hendpoints.elim Or.inr Or.inl⟩

/-- C1 on one coordinate subnerve: every coarse block-chart fiber is nonempty
and connected by the full endpoint-defined fiber graph. -/
def ConditionC1At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) : Prop :=
  ∀ coarseChart : coarse.ChartBlockCoordinate laws hcoarse label,
    (∃ fineChart : fine.ChartBlockCoordinate laws hfine label,
      M.chartBlockCoordinateMap laws hcoarse hfine label fineChart =
        coarseChart) ∧
    ∀ left right : fine.ChartBlockCoordinate laws hfine label,
      M.chartBlockCoordinateMap laws hcoarse hfine label left = coarseChart →
      M.chartBlockCoordinateMap laws hcoarse hfine label right = coarseChart →
      Relation.ReflTransGen
        (M.CoordinateFiberAdjacent laws hcoarse hfine label coarseChart)
        left right

/-- C1 quantified over every source-generated coordinate label. -/
def ConditionC1
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) : Prop :=
  ∀ label : LawValueLabel laws, M.ConditionC1At laws hcoarse hfine label

/-- C2 on one coordinate subnerve: every coarse block edge has an exact
same-label fine lift under the canonical partial block map. -/
def ConditionC2At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) : Prop :=
  ∀ coarseEdge : coarse.EdgeBlockCoordinate laws hcoarse label,
    ∃ fineEdge : fine.EdgeBlockCoordinate laws hfine label,
      M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge =
        some coarseEdge

/-- C2 quantified over every source-generated coordinate label. -/
def ConditionC2
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) : Prop :=
  ∀ label : LawValueLabel laws, M.ConditionC2At laws hcoarse hfine label

/-! ## The local rational condition C3 -/

/-- Incoming coefficient sum of a finite block-edge chain at one fine block
chart. -/
def coordinateFiberIncoming [Fintype Source]
    (laws : FiniteLawFamily Source)
    {q : Reading Source} (hadequate : laws.Adequate q)
    (D : TargetSupportedNerve q) (label : LawValueLabel laws)
    (chain : D.EdgeBlockCoordinate laws hadequate label → ℚ)
    (chart : D.ChartBlockCoordinate laws hadequate label) : ℚ := by
  classical
  exact ∑ edge,
    if D.edgeRightBlockCoordinate laws hadequate label edge = chart then
      chain edge
    else 0

/-- Normalize an incoming block-fiber coefficient sum to its defining finite
edge sum. -/
@[simp] theorem coordinateFiberIncoming_apply [Fintype Source]
    (laws : FiniteLawFamily Source)
    {q : Reading Source} (hadequate : laws.Adequate q)
    (D : TargetSupportedNerve q) (label : LawValueLabel laws)
    (chain : D.EdgeBlockCoordinate laws hadequate label → ℚ)
    (chart : D.ChartBlockCoordinate laws hadequate label) :
    coordinateFiberIncoming laws hadequate D label chain chart =
      (by
        classical
        exact ∑ edge,
          if D.edgeRightBlockCoordinate laws hadequate label edge = chart then
            chain edge
          else 0) := by
  classical
  rfl

/-- Outgoing coefficient sum of a finite block-edge chain at one fine block
chart. -/
def coordinateFiberOutgoing [Fintype Source]
    (laws : FiniteLawFamily Source)
    {q : Reading Source} (hadequate : laws.Adequate q)
    (D : TargetSupportedNerve q) (label : LawValueLabel laws)
    (chain : D.EdgeBlockCoordinate laws hadequate label → ℚ)
    (chart : D.ChartBlockCoordinate laws hadequate label) : ℚ := by
  classical
  exact ∑ edge,
    if D.edgeLeftBlockCoordinate laws hadequate label edge = chart then
      chain edge
    else 0

/-- Normalize an outgoing block-fiber coefficient sum to its defining finite
edge sum. -/
@[simp] theorem coordinateFiberOutgoing_apply [Fintype Source]
    (laws : FiniteLawFamily Source)
    {q : Reading Source} (hadequate : laws.Adequate q)
    (D : TargetSupportedNerve q) (label : LawValueLabel laws)
    (chain : D.EdgeBlockCoordinate laws hadequate label → ℚ)
    (chart : D.ChartBlockCoordinate laws hadequate label) :
    coordinateFiberOutgoing laws hadequate D label chain chart =
      (by
        classical
        exact ∑ edge,
          if D.edgeLeftBlockCoordinate laws hadequate label edge = chart then
            chain edge
          else 0) := by
  classical
  rfl

/-- A rational one-cycle supported on the endpoint-defined graph over one
coarse block chart. -/
def CoordinateFiberCycle [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (chain : fine.EdgeBlockCoordinate laws hfine label → ℚ) : Prop :=
  (∀ fineEdge,
      ¬ M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge →
        chain fineEdge = 0) ∧
    ∀ fineChart : fine.ChartBlockCoordinate laws hfine label,
      M.chartBlockCoordinateMap laws hcoarse hfine label fineChart =
          coarseChart →
        coordinateFiberIncoming laws hfine fine label chain fineChart =
          coordinateFiberOutgoing laws hfine fine label chain fineChart

/-- Constructor for a rational cycle on one endpoint-defined block fiber. -/
theorem coordinateFiberCycle_mk [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (chain : fine.EdgeBlockCoordinate laws hfine label → ℚ)
    (hsupport : ∀ fineEdge,
      ¬ M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge →
        chain fineEdge = 0)
    (hconservation : ∀ fineChart,
      M.chartBlockCoordinateMap laws hcoarse hfine label fineChart =
          coarseChart →
        coordinateFiberIncoming laws hfine fine label chain fineChart =
          coordinateFiberOutgoing laws hfine fine label chain fineChart) :
    M.CoordinateFiberCycle laws hcoarse hfine label coarseChart chain :=
  ⟨hsupport, hconservation⟩

/-- A block-fiber cycle vanishes away from its endpoint-defined fiber graph. -/
theorem CoordinateFiberCycle.support [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    {coarseChart : coarse.ChartBlockCoordinate laws hcoarse label}
    {chain : fine.EdgeBlockCoordinate laws hfine label → ℚ}
    (hcycle : M.CoordinateFiberCycle laws hcoarse hfine label coarseChart chain)
    (fineEdge)
    (houtside :
      ¬ M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge) :
    chain fineEdge = 0 :=
  hcycle.1 fineEdge houtside

/-- A block-fiber cycle satisfies flow conservation at every chart of its
fiber. -/
theorem CoordinateFiberCycle.conservation [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    {coarseChart : coarse.ChartBlockCoordinate laws hcoarse label}
    {chain : fine.EdgeBlockCoordinate laws hfine label → ℚ}
    (hcycle : M.CoordinateFiberCycle laws hcoarse hfine label coarseChart chain)
    (fineChart)
    (hmap : M.chartBlockCoordinateMap laws hcoarse hfine label fineChart =
      coarseChart) :
    coordinateFiberIncoming laws hfine fine label chain fineChart =
      coordinateFiberOutgoing laws hfine fine label chain fineChart :=
  hcycle.2 fineChart hmap

/-- A fine block face is internal to one coordinate fiber when each of its
three block edges has both endpoints in that fiber. -/
def CoordinateInternalFace
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (fineFace : fine.FaceBlockCoordinate laws hfine label) : Prop :=
  M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge0BlockCoordinate laws hfine label fineFace) ∧
    M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge1BlockCoordinate laws hfine label fineFace) ∧
    M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge2BlockCoordinate laws hfine label fineFace)

/-- Constructor for an internal block face from its three fiber edges. -/
theorem coordinateInternalFace_mk
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (fineFace : fine.FaceBlockCoordinate laws hfine label)
    (hedge0 : M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge0BlockCoordinate laws hfine label fineFace))
    (hedge1 : M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge1BlockCoordinate laws hfine label fineFace))
    (hedge2 : M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge2BlockCoordinate laws hfine label fineFace)) :
    M.CoordinateInternalFace laws hcoarse hfine label coarseChart fineFace :=
  ⟨hedge0, hedge1, hedge2⟩

/-- Boundary edge zero of an internal block face lies in the same fiber. -/
theorem CoordinateInternalFace.edge0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    {coarseChart : coarse.ChartBlockCoordinate laws hcoarse label}
    {fineFace : fine.FaceBlockCoordinate laws hfine label}
    (hface : M.CoordinateInternalFace laws hcoarse hfine label
      coarseChart fineFace) :
    M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge0BlockCoordinate laws hfine label fineFace) :=
  hface.1

/-- Boundary edge one of an internal block face lies in the same fiber. -/
theorem CoordinateInternalFace.edge1
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    {coarseChart : coarse.ChartBlockCoordinate laws hcoarse label}
    {fineFace : fine.FaceBlockCoordinate laws hfine label}
    (hface : M.CoordinateInternalFace laws hcoarse hfine label
      coarseChart fineFace) :
    M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge1BlockCoordinate laws hfine label fineFace) :=
  hface.2.1

/-- Boundary edge two of an internal block face lies in the same fiber. -/
theorem CoordinateInternalFace.edge2
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    {coarseChart : coarse.ChartBlockCoordinate laws hcoarse label}
    {fineFace : fine.FaceBlockCoordinate laws hfine label}
    (hface : M.CoordinateInternalFace laws hcoarse hfine label
      coarseChart fineFace) :
    M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
      (fine.faceEdge2BlockCoordinate laws hfine label fineFace) :=
  hface.2.2

/-- The oriented block-edge boundary of a finite rational block-face chain. -/
def coordinateFaceBoundary [Fintype Source]
    (laws : FiniteLawFamily Source)
    {q : Reading Source} (hadequate : laws.Adequate q)
    (D : TargetSupportedNerve q) (label : LawValueLabel laws)
    (faces : D.FaceBlockCoordinate laws hadequate label → ℚ)
    (edge : D.EdgeBlockCoordinate laws hadequate label) : ℚ := by
  classical
  exact
    (∑ face,
      if D.faceEdge0BlockCoordinate laws hadequate label face = edge then
        faces face
      else 0) -
    (∑ face,
      if D.faceEdge1BlockCoordinate laws hadequate label face = edge then
        faces face
      else 0) +
    ∑ face,
      if D.faceEdge2BlockCoordinate laws hadequate label face = edge then
        faces face
      else 0

/-- Normalize an oriented block-face boundary to its three defining finite
face sums. -/
@[simp] theorem coordinateFaceBoundary_apply [Fintype Source]
    (laws : FiniteLawFamily Source)
    {q : Reading Source} (hadequate : laws.Adequate q)
    (D : TargetSupportedNerve q) (label : LawValueLabel laws)
    (faces : D.FaceBlockCoordinate laws hadequate label → ℚ)
    (edge : D.EdgeBlockCoordinate laws hadequate label) :
    coordinateFaceBoundary laws hadequate D label faces edge =
      (by
        classical
        exact
          (∑ face,
            if D.faceEdge0BlockCoordinate laws hadequate label face = edge then
              faces face
            else 0) -
          (∑ face,
            if D.faceEdge1BlockCoordinate laws hadequate label face = edge then
              faces face
            else 0) +
          ∑ face,
            if D.faceEdge2BlockCoordinate laws hadequate label face = edge then
              faces face
            else 0) := by
  classical
  rfl

/-- C3 on one coordinate subnerve: every local rational fiber cycle is a
rational linear combination of boundaries of internal block faces. -/
def ConditionC3At [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) : Prop :=
  ∀ coarseChart : coarse.ChartBlockCoordinate laws hcoarse label,
    ∀ chain : fine.EdgeBlockCoordinate laws hfine label → ℚ,
      M.CoordinateFiberCycle laws hcoarse hfine label coarseChart chain →
        ∃ faces : fine.FaceBlockCoordinate laws hfine label → ℚ,
          (∀ fineFace,
            ¬ M.CoordinateInternalFace laws hcoarse hfine label coarseChart
                fineFace →
              faces fineFace = 0) ∧
          ∀ fineEdge,
            chain fineEdge =
              coordinateFaceBoundary laws hfine fine label faces fineEdge

/-- C3 quantified over every source-generated coordinate label. -/
def ConditionC3 [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) : Prop :=
  ∀ label : LawValueLabel laws, M.ConditionC3At laws hcoarse hfine label

/-! ## Coordinate-relative face lifting -/

/-- C4 on one coordinate subnerve: every coarse block face has an exact
same-label fine lift under the canonical partial block map. -/
def ConditionC4At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) : Prop :=
  ∀ coarseFace : coarse.FaceBlockCoordinate laws hcoarse label,
    ∃ fineFace : fine.FaceBlockCoordinate laws hfine label,
      M.faceBlockCoordinateMapOption laws hcoarse hfine label fineFace =
        some coarseFace

/-- C4 quantified over every source-generated coordinate label. -/
def ConditionC4
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) : Prop :=
  ∀ label : LawValueLabel laws, M.ConditionC4At laws hcoarse hfine label

/-! ## The complete fixed condition package -/

/-- The fixed C0--C6 hypothesis package.  Every field is a proposition; no
lift, path, filling chain, inverse, or cohomology certificate is stored as data. -/
structure ConditionC [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) : Prop where
  c0 : M.ConditionC0
  c1 : M.ConditionC1 laws hcoarse hfine
  c2 : M.ConditionC2 laws hcoarse hfine
  c3 : M.ConditionC3 laws hcoarse hfine
  c4 : M.ConditionC4 laws hcoarse hfine
  c5 : M.ConditionC5
  c6 : M.ConditionC6

/-! ## Whole-to-block bridges for C5 and C6 -/

/-- An exact block-edge image exposes the corresponding whole-nerve edge
image; no separate coordinate-map certificate is needed. -/
theorem edgeMap_eq_some_of_edgeBlockCoordinateMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (fineEdge : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.EdgeBlockCoordinate laws hcoarse label)
    (hmap : M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge =
      some coarseEdge) :
    M.edgeMap fineEdge.1.cell = some coarseEdge.1.cell := by
  unfold edgeBlockCoordinateMapOption at hmap
  split at hmap
  · contradiction
  · rename_i mappedEdge hwhole
    have hcoordinate := Option.some.inj hmap
    have hcell := congrArg
      (fun coordinate : coarse.EdgeBlockCoordinate laws hcoarse label =>
        coordinate.1.cell)
      hcoordinate
    change mappedEdge = coarseEdge.1.cell at hcell
    simpa [hcell] using hwhole

/-- Whole-nerve C5 restricts to uniqueness of an exact same-label block-edge
lift in every coordinate subnerve. -/
theorem conditionC5_block_unique
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC5 : M.ConditionC5)
    (label : LawValueLabel laws)
    (coarseEdge : coarse.EdgeBlockCoordinate laws hcoarse label)
    (fineLeft fineRight : fine.EdgeBlockCoordinate laws hfine label)
    (hleft : M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineLeft =
      some coarseEdge)
    (hright : M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineRight =
      some coarseEdge) :
    fineLeft = fineRight := by
  apply fine.lawValueCoordinateSubnerveEdgeCell_injective laws hfine label
  exact hC5 coarseEdge.1.cell fineLeft.1.cell fineRight.1.cell
    (M.edgeMap_eq_some_of_edgeBlockCoordinateMapOption_eq_some laws hcoarse
      hfine label fineLeft coarseEdge hleft)
    (M.edgeMap_eq_some_of_edgeBlockCoordinateMapOption_eq_some laws hcoarse
      hfine label fineRight coarseEdge hright)

/-- Whole-nerve C6 reflects a coarse block self-loop to a fine block
self-loop, independently of edge-lift uniqueness. -/
theorem conditionC6_block_endpoint_reflection
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC6 : M.ConditionC6)
    (label : LawValueLabel laws)
    (fineEdge : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.EdgeBlockCoordinate laws hcoarse label)
    (hmap : M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge =
      some coarseEdge)
    (hloop :
      coarse.edgeLeftBlockCoordinate laws hcoarse label coarseEdge =
        coarse.edgeRightBlockCoordinate laws hcoarse label coarseEdge) :
    fine.edgeLeftBlockCoordinate laws hfine label fineEdge =
      fine.edgeRightBlockCoordinate laws hfine label fineEdge := by
  apply fine.lawValueCoordinateSubnerveChartCell_injective laws hfine label
  have hcoarseLoop := congrArg
    (fun coordinate : coarse.ChartBlockCoordinate laws hcoarse label =>
      coordinate.1.cell)
    hloop
  change
    coarse.nerve.edgeLeft coarseEdge.1.cell =
      coarse.nerve.edgeRight coarseEdge.1.cell at hcoarseLoop
  exact hC6 fineEdge.1.cell coarseEdge.1.cell
    (M.edgeMap_eq_some_of_edgeBlockCoordinateMapOption_eq_some laws hcoarse
      hfine label fineEdge coarseEdge hmap)
    hcoarseLoop

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
