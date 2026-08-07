import ResearchLean.AG.ResolutionInvariance.ComparisonData
import ResearchLean.AG.TwoPhase.CoefficientComplex
import Formal.Util.AssertStandardAxioms

/-!
# Law-generated coefficient complexes for resolution invariance

This module implements the K0/K1 coefficient-generation obligation of
`G-104-aat-resolution-invariance`.  The input geometry declares only finite
nerve cells, nonempty chart supports in one adequate reading target, and the
endpoint coherence of every face boundary.  Edge and face supports are then
derived by intersection (K1).  In each degree, coordinates are exactly the
distinct `(law, value)` pairs attained by the canonical law descent on the
derived cell support (K0).

The two differentials are generated from the same-label incidence formulas.
The proof that `d1 (d0 c) = 0` uses the three face-endpoint equalities; it is
not supplied as a certificate or an input field.  The resulting object is the
reviewed `ThreeCochainComplex ℚ` used by G-102.

## Implementation notes

Coordinates are represented by their cell, law, value, and a proof that the
value occurs on the derived support.  Occurrence points are witnesses only and
are not part of coordinate equality, so repeated target occurrences cannot
duplicate a coefficient coordinate.  This is preferable to indexing by
supported target points, which would reintroduce the multiplicity rejected by
the fixed K0 contract.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

universe u

variable {Source : Type u}

/-! ## K1 input geometry and derived supports -/

/--
A finite nerve supported on one reading target, with only chart supports
declared.  The three endpoint equalities say that every face boundary is an
oriented triangle; they are the input geometry used to derive `d1 d0 = 0`.
-/
structure TargetSupportedNerve (q : Reading Source) where
  nerve : CoverNerve
  [chartFintype : Fintype nerve.Chart]
  [edgeFintype : Fintype nerve.EdgeComponent]
  [faceFintype : Fintype nerve.FaceComponent]
  chartSupport : nerve.Chart → Set q.Target
  chartSupport_nonempty : ∀ chart, (chartSupport chart).Nonempty
  faceEdge0_left : ∀ face,
    nerve.edgeLeft (nerve.faceEdge0 face) =
      nerve.edgeLeft (nerve.faceEdge1 face)
  faceEdge0_right : ∀ face,
    nerve.edgeRight (nerve.faceEdge0 face) =
      nerve.edgeLeft (nerve.faceEdge2 face)
  faceEdge1_right : ∀ face,
    nerve.edgeRight (nerve.faceEdge1 face) =
      nerve.edgeRight (nerve.faceEdge2 face)

namespace TargetSupportedNerve

attribute [instance] chartFintype edgeFintype faceFintype

/-- K1 edge support, derived as the intersection of the endpoint chart supports. -/
def edgeSupport (D : TargetSupportedNerve q) (edge : D.nerve.EdgeComponent) :
    Set q.Target :=
  D.chartSupport (D.nerve.edgeLeft edge) ∩
    D.chartSupport (D.nerve.edgeRight edge)

/-- Membership in a K1 edge support is membership at both endpoint charts. -/
@[simp]
theorem mem_edgeSupport_iff (D : TargetSupportedNerve q)
    (edge : D.nerve.EdgeComponent) (target : q.Target) :
    target ∈ D.edgeSupport edge ↔
      target ∈ D.chartSupport (D.nerve.edgeLeft edge) ∧
        target ∈ D.chartSupport (D.nerve.edgeRight edge) :=
  Iff.rfl

/-- K1 face support, derived as the intersection of its three edge supports. -/
def faceSupport (D : TargetSupportedNerve q) (face : D.nerve.FaceComponent) :
    Set q.Target :=
  D.edgeSupport (D.nerve.faceEdge0 face) ∩
    (D.edgeSupport (D.nerve.faceEdge1 face) ∩
      D.edgeSupport (D.nerve.faceEdge2 face))

/-- Membership in a K1 face support is membership on all three boundary edges. -/
@[simp]
theorem mem_faceSupport_iff (D : TargetSupportedNerve q)
    (face : D.nerve.FaceComponent) (target : q.Target) :
    target ∈ D.faceSupport face ↔
      target ∈ D.edgeSupport (D.nerve.faceEdge0 face) ∧
        target ∈ D.edgeSupport (D.nerve.faceEdge1 face) ∧
          target ∈ D.edgeSupport (D.nerve.faceEdge2 face) := by
  simp [faceSupport]

end TargetSupportedNerve

/-! ## K0 coordinates -/

/--
One law-generated coordinate on one cell.  The occurrence witness proves that
the value is in the image of the canonical law descent on that cell support;
the witness itself is proof data and therefore cannot create duplicates.
-/
structure CellCoordinate (laws : FiniteLawFamily Source) (q : Reading Source)
    (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) where
  cell : Cell
  law : laws.Law
  value : laws.Value law
  generated : ∃ target, target ∈ support cell ∧
    lawDescend laws q hadequate law target = value

namespace CellCoordinate

/-- Two generated coordinates are equal when their cell, law, and value agree. -/
@[ext]
theorem ext (laws : FiniteLawFamily Source) (q : Reading Source)
    (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target)
    {left right : CellCoordinate laws q hadequate Cell support}
    (hcell : left.cell = right.cell)
    (hlaw : left.law = right.law)
    (hvalue : HEq left.value right.value) : left = right := by
  cases left with
  | mk leftCell leftLaw leftValue leftGenerated =>
      cases right with
      | mk rightCell rightLaw rightValue rightGenerated =>
          cases hcell
          cases hlaw
          cases hvalue
          rfl

/-- A supported target point generates its unique cell-law-value coordinate. -/
def ofSupportedTarget (laws : FiniteLawFamily Source) (q : Reading Source)
    (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (cell : Cell) (law : laws.Law)
    (target : q.Target) (htarget : target ∈ support cell) :
    CellCoordinate laws q hadequate Cell support :=
  ⟨cell, law, lawDescend laws q hadequate law target,
    ⟨target, htarget, rfl⟩⟩

/-- The generated coordinate records the cell used to construct it. -/
@[simp]
theorem ofSupportedTarget_cell (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (cell : Cell) (law : laws.Law)
    (target : q.Target) (htarget : target ∈ support cell) :
    (ofSupportedTarget laws q hadequate Cell support cell law target htarget).cell =
      cell :=
  rfl

/-- The generated coordinate records the law used to construct it. -/
@[simp]
theorem ofSupportedTarget_law (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (cell : Cell) (law : laws.Law)
    (target : q.Target) (htarget : target ∈ support cell) :
    (ofSupportedTarget laws q hadequate Cell support cell law target htarget).law =
      law :=
  rfl

/--
Two occurrences of the same descended law value generate the same coordinate;
target-point multiplicity is not part of the K0 index.
-/
theorem ofSupportedTarget_eq_of_value_eq (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (cell : Cell) (law : laws.Law)
    (leftTarget rightTarget : q.Target)
    (hleft : leftTarget ∈ support cell)
    (hright : rightTarget ∈ support cell)
    (hvalue : lawDescend laws q hadequate law leftTarget =
      lawDescend laws q hadequate law rightTarget) :
    ofSupportedTarget laws q hadequate Cell support cell law leftTarget hleft =
      ofSupportedTarget laws q hadequate Cell support cell law rightTarget hright := by
  apply CellCoordinate.ext
  · rfl
  · rfl
  · exact heq_of_eq hvalue

/--
Law-generated cell coordinates are finite when the source, law family, and
cell set are finite.  Surjectivity removes occurrence multiplicity: every
coordinate is reached from a supported target point, but equal law values have
only one codomain coordinate.
-/
noncomputable instance instFintype (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q)
    (Cell : Type u) [Fintype Source] [Fintype Cell]
    (support : Cell → Set q.Target) :
    Fintype (CellCoordinate laws q hadequate Cell support) := by
  classical
  letI : Fintype q.Target := Fintype.ofSurjective q.read q.surjective
  let Domain :=
    Σ cell : Cell, Σ law : laws.Law, {target : q.Target // target ∈ support cell}
  let toCoordinate : Domain → CellCoordinate laws q hadequate Cell support :=
    fun input =>
      ofSupportedTarget laws q hadequate Cell support input.1 input.2.1
        input.2.2.1 input.2.2.2
  exact Fintype.ofSurjective toCoordinate (by
    intro coordinate
    obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
    refine ⟨⟨coordinate.cell, coordinate.law, ⟨target, htarget⟩⟩, ?_⟩
    dsimp [toCoordinate]
    apply CellCoordinate.ext
    · rfl
    · rfl
    · exact heq_of_eq hvalue)

end CellCoordinate

namespace TargetSupportedNerve

/-- Degree-zero coordinates generated on chart supports. -/
abbrev ChartCoordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q) :=
  CellCoordinate laws q hadequate D.nerve.Chart D.chartSupport

/-- Degree-one coordinates generated on K1 edge supports. -/
abbrev EdgeCoordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q) :=
  CellCoordinate laws q hadequate D.nerve.EdgeComponent D.edgeSupport

/-- Degree-two coordinates generated on K1 face supports. -/
abbrev FaceCoordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q) :=
  CellCoordinate laws q hadequate D.nerve.FaceComponent D.faceSupport

/-- Every chart-law pair has at least one generated coordinate. -/
theorem chartCoordinate_exists (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (chart : D.nerve.Chart) (law : laws.Law) :
    ∃ coordinate : D.ChartCoordinate laws hadequate,
      coordinate.cell = chart ∧ coordinate.law = law := by
  obtain ⟨target, htarget⟩ := D.chartSupport_nonempty chart
  exact ⟨CellCoordinate.ofSupportedTarget laws q hadequate D.nerve.Chart
      D.chartSupport chart law target htarget, rfl, rfl⟩

/-- The same law-value coordinate at the left endpoint of a generated edge coordinate. -/
def edgeLeftCoordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.EdgeCoordinate laws hadequate) :
    D.ChartCoordinate laws hadequate := by
  refine ⟨D.nerve.edgeLeft coordinate.cell, coordinate.law,
    coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  exact ⟨target, (D.mem_edgeSupport_iff coordinate.cell target).1 htarget |>.1,
    hvalue⟩

/-- The left endpoint coordinate lies over the left endpoint chart. -/
@[simp]
theorem edgeLeftCoordinate_cell (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.EdgeCoordinate laws hadequate) :
    (D.edgeLeftCoordinate laws hadequate coordinate).cell =
      D.nerve.edgeLeft coordinate.cell :=
  rfl

/-- The same law-value coordinate at the right endpoint of a generated edge coordinate. -/
def edgeRightCoordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.EdgeCoordinate laws hadequate) :
    D.ChartCoordinate laws hadequate := by
  refine ⟨D.nerve.edgeRight coordinate.cell, coordinate.law,
    coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  exact ⟨target, (D.mem_edgeSupport_iff coordinate.cell target).1 htarget |>.2,
    hvalue⟩

/-- The right endpoint coordinate lies over the right endpoint chart. -/
@[simp]
theorem edgeRightCoordinate_cell (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.EdgeCoordinate laws hadequate) :
    (D.edgeRightCoordinate laws hadequate coordinate).cell =
      D.nerve.edgeRight coordinate.cell :=
  rfl

/-- The same law-value coordinate on boundary edge zero of a generated face coordinate. -/
def faceEdge0Coordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    D.EdgeCoordinate laws hadequate := by
  refine ⟨D.nerve.faceEdge0 coordinate.cell, coordinate.law,
    coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  exact ⟨target, (D.mem_faceSupport_iff coordinate.cell target).1 htarget |>.1,
    hvalue⟩

/-- Boundary-coordinate zero lies over boundary edge zero. -/
@[simp]
theorem faceEdge0Coordinate_cell (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    (D.faceEdge0Coordinate laws hadequate coordinate).cell =
      D.nerve.faceEdge0 coordinate.cell :=
  rfl

/-- The same law-value coordinate on boundary edge one of a generated face coordinate. -/
def faceEdge1Coordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    D.EdgeCoordinate laws hadequate := by
  refine ⟨D.nerve.faceEdge1 coordinate.cell, coordinate.law,
    coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  exact ⟨target,
    (D.mem_faceSupport_iff coordinate.cell target).1 htarget |>.2.1,
    hvalue⟩

/-- Boundary-coordinate one lies over boundary edge one. -/
@[simp]
theorem faceEdge1Coordinate_cell (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    (D.faceEdge1Coordinate laws hadequate coordinate).cell =
      D.nerve.faceEdge1 coordinate.cell :=
  rfl

/-- The same law-value coordinate on boundary edge two of a generated face coordinate. -/
def faceEdge2Coordinate (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    D.EdgeCoordinate laws hadequate := by
  refine ⟨D.nerve.faceEdge2 coordinate.cell, coordinate.law,
    coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  exact ⟨target,
    (D.mem_faceSupport_iff coordinate.cell target).1 htarget |>.2.2,
    hvalue⟩

/-- Boundary-coordinate two lies over boundary edge two. -/
@[simp]
theorem faceEdge2Coordinate_cell (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    (D.faceEdge2Coordinate laws hadequate coordinate).cell =
      D.nerve.faceEdge2 coordinate.cell :=
  rfl

/-! ## Generated differentials -/

/-- K0 degree-zero differential, generated by the right-minus-left incidence formula. -/
def lawGeneratedD0 (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q) :
    (D.ChartCoordinate laws hadequate → ℚ) →ₗ[ℚ]
      (D.EdgeCoordinate laws hadequate → ℚ) where
  toFun cochain coordinate :=
    cochain (D.edgeRightCoordinate laws hadequate coordinate) -
      cochain (D.edgeLeftCoordinate laws hadequate coordinate)
  map_add' left right := by
    ext coordinate
    simp
    ring
  map_smul' scalar cochain := by
    ext coordinate
    simp
    ring

/-- Evaluation formula for the generated degree-zero differential. -/
@[simp]
theorem lawGeneratedD0_apply (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (cochain : D.ChartCoordinate laws hadequate → ℚ)
    (coordinate : D.EdgeCoordinate laws hadequate) :
    D.lawGeneratedD0 laws hadequate cochain coordinate =
      cochain (D.edgeRightCoordinate laws hadequate coordinate) -
        cochain (D.edgeLeftCoordinate laws hadequate coordinate) :=
  rfl

/-- K0 degree-one differential, generated by the alternating face-boundary formula. -/
def lawGeneratedD1 (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q) :
    (D.EdgeCoordinate laws hadequate → ℚ) →ₗ[ℚ]
      (D.FaceCoordinate laws hadequate → ℚ) where
  toFun cochain coordinate :=
    cochain (D.faceEdge0Coordinate laws hadequate coordinate) -
      cochain (D.faceEdge1Coordinate laws hadequate coordinate) +
        cochain (D.faceEdge2Coordinate laws hadequate coordinate)
  map_add' left right := by
    ext coordinate
    simp
    ring
  map_smul' scalar cochain := by
    ext coordinate
    simp
    ring

/-- Evaluation formula for the generated degree-one differential. -/
@[simp]
theorem lawGeneratedD1_apply (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (cochain : D.EdgeCoordinate laws hadequate → ℚ)
    (coordinate : D.FaceCoordinate laws hadequate) :
    D.lawGeneratedD1 laws hadequate cochain coordinate =
      cochain (D.faceEdge0Coordinate laws hadequate coordinate) -
        cochain (D.faceEdge1Coordinate laws hadequate coordinate) +
          cochain (D.faceEdge2Coordinate laws hadequate coordinate) :=
  rfl

private theorem left_faceEdge0_eq_left_faceEdge1
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    D.edgeLeftCoordinate laws hadequate
        (D.faceEdge0Coordinate laws hadequate coordinate) =
      D.edgeLeftCoordinate laws hadequate
        (D.faceEdge1Coordinate laws hadequate coordinate) := by
  cases coordinate with
  | mk face law value generated =>
      dsimp [edgeLeftCoordinate, faceEdge0Coordinate, faceEdge1Coordinate]
      apply CellCoordinate.ext
      · exact D.faceEdge0_left face
      · rfl
      · rfl

private theorem right_faceEdge0_eq_left_faceEdge2
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    D.edgeRightCoordinate laws hadequate
        (D.faceEdge0Coordinate laws hadequate coordinate) =
      D.edgeLeftCoordinate laws hadequate
        (D.faceEdge2Coordinate laws hadequate coordinate) := by
  cases coordinate with
  | mk face law value generated =>
      dsimp [edgeRightCoordinate, edgeLeftCoordinate, faceEdge0Coordinate,
        faceEdge2Coordinate]
      apply CellCoordinate.ext
      · exact D.faceEdge0_right face
      · rfl
      · rfl

private theorem right_faceEdge1_eq_right_faceEdge2
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (coordinate : D.FaceCoordinate laws hadequate) :
    D.edgeRightCoordinate laws hadequate
        (D.faceEdge1Coordinate laws hadequate coordinate) =
      D.edgeRightCoordinate laws hadequate
        (D.faceEdge2Coordinate laws hadequate coordinate) := by
  cases coordinate with
  | mk face law value generated =>
      dsimp [edgeRightCoordinate, faceEdge1Coordinate, faceEdge2Coordinate]
      apply CellCoordinate.ext
      · exact D.faceEdge1_right face
      · rfl
      · rfl

/-- The K0/K1 incidence formulas compose to zero by face endpoint coherence. -/
theorem lawGenerated_d1_comp_d0 (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (cochain : D.ChartCoordinate laws hadequate → ℚ) :
    D.lawGeneratedD1 laws hadequate
        (D.lawGeneratedD0 laws hadequate cochain) = 0 := by
  funext coordinate
  change
    (cochain (D.edgeRightCoordinate laws hadequate
        (D.faceEdge0Coordinate laws hadequate coordinate)) -
      cochain (D.edgeLeftCoordinate laws hadequate
        (D.faceEdge0Coordinate laws hadequate coordinate))) -
    (cochain (D.edgeRightCoordinate laws hadequate
        (D.faceEdge1Coordinate laws hadequate coordinate)) -
      cochain (D.edgeLeftCoordinate laws hadequate
        (D.faceEdge1Coordinate laws hadequate coordinate))) +
    (cochain (D.edgeRightCoordinate laws hadequate
        (D.faceEdge2Coordinate laws hadequate coordinate)) -
      cochain (D.edgeLeftCoordinate laws hadequate
        (D.faceEdge2Coordinate laws hadequate coordinate))) = 0
  rw [D.left_faceEdge0_eq_left_faceEdge1 laws hadequate coordinate,
    D.right_faceEdge0_eq_left_faceEdge2 laws hadequate coordinate,
    D.right_faceEdge1_eq_right_faceEdge2 laws hadequate coordinate]
  ring

/--
The finite `ℚ`-cochain complex generated canonically from the adequate law
family, chart supports, K1 intersections, and the K0 same-label formulas.
-/
def lawGeneratedComplex [Fintype Source] (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q) :
    ThreeCochainComplex ℚ where
  C0 := D.ChartCoordinate laws hadequate → ℚ
  C1 := D.EdgeCoordinate laws hadequate → ℚ
  C2 := D.FaceCoordinate laws hadequate → ℚ
  d0 := D.lawGeneratedD0 laws hadequate
  d1 := D.lawGeneratedD1 laws hadequate
  d1_comp_d0 := D.lawGenerated_d1_comp_d0 laws hadequate

/-- The complex degree-zero differential is the generated K0 incidence map. -/
@[simp]
theorem lawGeneratedComplex_d0 [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    (D.lawGeneratedComplex laws hadequate).d0 =
      D.lawGeneratedD0 laws hadequate :=
  rfl

/-- The complex degree-one differential is the generated K0 incidence map. -/
@[simp]
theorem lawGeneratedComplex_d1 [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    (D.lawGeneratedComplex laws hadequate).d1 =
      D.lawGeneratedD1 laws hadequate :=
  rfl

end TargetSupportedNerve

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
