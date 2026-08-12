import ResearchLean.AG.UniformInvariance.DefectSemantics
import Formal.Util.AssertStandardAxioms

/-!
# Finite comparison presentations

This module begins claim (ii) of
`G-107-aat-uniform-invariance-characterization` by fixing the executable raw
input whose later matrix checker will read.  A presentation contains finite,
decidable reading targets and nerve cells, incidence and partial comparison
tables, and chart supports as `Finset`s.  It generates the actual G-104
`TargetSupportedNerveMorphism`; it does not store an already assembled semantic
geometry.

## Implementation notes

The canonical comparison factor is defined upstream with `Classical.choose`,
so it is unsuitable as the computational factor of a presentation.  Here a
finite list search selects a fine-reading representative and applies the raw
coarse reading.  The coarse-kernel hypothesis proves independence of the
representative, commutation, and equality with the upstream canonical factor.
The same equality is then used when constructing semantic support
compatibility.

The source, coarse-target, and six nerve-cell enumerations are explicit because
`Finset.toList` has no compiler code in the current Lean runtime; deriving a
list from `Fintype.elems` would make the representative search and the later
all-subset and finite-reduction observers non-executable.  These lists carry
only coverage of already supplied finite types; they do not carry a reduction
state, terminal, condition bit, or observation.  Search itself uses the
standard `List.find?` operation.  Source-enumeration order, duplicates, and the
fallback do not affect the semantics, as certified by the canonical-factor
equality theorem below.  Duplicate entries only repeat finite generation;
coverage is the material property used by completeness theorems.

We reject an arbitrary factor field, a canonical-factor equality field, and an
opaque completed-geometry field: each would disconnect the future checker from
the semantics it is meant to decide.  Overlap-component predicates of the
generated nerves are `True`; the presentation cell types already enumerate the
selected components, while all incidence data used by the coefficient complex
remain the raw tables below.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology

universe u

/-! ## Executable finite search -/

/-- Return the first list entry satisfying a Boolean predicate, or a supplied
fallback when no entry satisfies it. -/
def firstMatchingOr {α : Type u} (fallback : α) (predicate : α → Bool) :
    List α → α :=
  fun entries => (entries.find? predicate).getD fallback

/-- A finite search returns a satisfying entry whenever the searched list
contains one. -/
theorem firstMatchingOr_satisfies {α : Type u} (fallback : α)
    (predicate : α → Bool) (entries : List α)
    (hexists : ∃ entry ∈ entries, predicate entry = true) :
    predicate (firstMatchingOr fallback predicate entries) = true := by
  cases hfound : entries.find? predicate with
  | none =>
      obtain ⟨entry, hentry, hsatisfies⟩ := hexists
      exact ((List.find?_eq_none.mp hfound entry hentry) hsatisfies).elim
  | some entry =>
      simpa [firstMatchingOr, hfound] using List.find?_some hfound

/-! ## Raw finite comparison data -/

/-- A finite, executable presentation of the comparison geometry used by
G-107.  Its proof fields express only finite-list coverage, reading
surjectivity, incidence, hereditary degeneracy, support nonemptiness, and
source-level support compatibility; no reduction terminal, cohomology,
uniformity, condition, or observation result is stored. -/
structure FiniteComparisonPresentation where
  Source : Type u
  sourceFintype : Fintype Source := by infer_instance
  sourceDecidableEq : DecidableEq Source := by infer_instance
  sourceDefault : Source
  sourceEntries : List Source
  source_mem_sourceEntries : ∀ source, source ∈ sourceEntries
  CoarseTarget : Type u
  coarseTargetFintype : Fintype CoarseTarget := by infer_instance
  coarseTargetDecidableEq : DecidableEq CoarseTarget := by infer_instance
  coarseTargetEntries : List CoarseTarget
  coarseTarget_mem_coarseTargetEntries :
    ∀ target, target ∈ coarseTargetEntries
  FineTarget : Type u
  fineTargetFintype : Fintype FineTarget := by infer_instance
  fineTargetDecidableEq : DecidableEq FineTarget := by infer_instance
  coarseRead : Source → CoarseTarget
  fineRead : Source → FineTarget
  coarseRead_surjective : Function.Surjective coarseRead
  fineRead_surjective : Function.Surjective fineRead
  rawCoarserThan : ∀ ⦃left right : Source⦄,
    fineRead left = fineRead right → coarseRead left = coarseRead right
  CoarseChart : Type u
  coarseChartFintype : Fintype CoarseChart := by infer_instance
  coarseChartDecidableEq : DecidableEq CoarseChart := by infer_instance
  coarseChartEntries : List CoarseChart
  coarseChart_mem_coarseChartEntries : ∀ chart, chart ∈ coarseChartEntries
  CoarseEdge : Type u
  coarseEdgeFintype : Fintype CoarseEdge := by infer_instance
  coarseEdgeDecidableEq : DecidableEq CoarseEdge := by infer_instance
  coarseEdgeEntries : List CoarseEdge
  coarseEdge_mem_coarseEdgeEntries : ∀ edge, edge ∈ coarseEdgeEntries
  CoarseFace : Type u
  coarseFaceFintype : Fintype CoarseFace := by infer_instance
  coarseFaceDecidableEq : DecidableEq CoarseFace := by infer_instance
  coarseFaceEntries : List CoarseFace
  coarseFace_mem_coarseFaceEntries : ∀ face, face ∈ coarseFaceEntries
  coarseEdgeLeft : CoarseEdge → CoarseChart
  coarseEdgeRight : CoarseEdge → CoarseChart
  coarseFaceEdge0 : CoarseFace → CoarseEdge
  coarseFaceEdge1 : CoarseFace → CoarseEdge
  coarseFaceEdge2 : CoarseFace → CoarseEdge
  coarseFaceEdge0_left : ∀ face,
    coarseEdgeLeft (coarseFaceEdge0 face) =
      coarseEdgeLeft (coarseFaceEdge1 face)
  coarseFaceEdge0_right : ∀ face,
    coarseEdgeRight (coarseFaceEdge0 face) =
      coarseEdgeLeft (coarseFaceEdge2 face)
  coarseFaceEdge1_right : ∀ face,
    coarseEdgeRight (coarseFaceEdge1 face) =
      coarseEdgeRight (coarseFaceEdge2 face)
  coarseChartSupport : CoarseChart → Finset CoarseTarget
  coarseChartSupport_nonempty : ∀ chart,
    (coarseChartSupport chart).Nonempty
  FineChart : Type u
  fineChartFintype : Fintype FineChart := by infer_instance
  fineChartDecidableEq : DecidableEq FineChart := by infer_instance
  fineChartEntries : List FineChart
  fineChart_mem_fineChartEntries : ∀ chart, chart ∈ fineChartEntries
  FineEdge : Type u
  fineEdgeFintype : Fintype FineEdge := by infer_instance
  fineEdgeDecidableEq : DecidableEq FineEdge := by infer_instance
  fineEdgeEntries : List FineEdge
  fineEdge_mem_fineEdgeEntries : ∀ edge, edge ∈ fineEdgeEntries
  FineFace : Type u
  fineFaceFintype : Fintype FineFace := by infer_instance
  fineFaceDecidableEq : DecidableEq FineFace := by infer_instance
  fineFaceEntries : List FineFace
  fineFace_mem_fineFaceEntries : ∀ face, face ∈ fineFaceEntries
  fineEdgeLeft : FineEdge → FineChart
  fineEdgeRight : FineEdge → FineChart
  fineFaceEdge0 : FineFace → FineEdge
  fineFaceEdge1 : FineFace → FineEdge
  fineFaceEdge2 : FineFace → FineEdge
  fineFaceEdge0_left : ∀ face,
    fineEdgeLeft (fineFaceEdge0 face) =
      fineEdgeLeft (fineFaceEdge1 face)
  fineFaceEdge0_right : ∀ face,
    fineEdgeRight (fineFaceEdge0 face) =
      fineEdgeLeft (fineFaceEdge2 face)
  fineFaceEdge1_right : ∀ face,
    fineEdgeRight (fineFaceEdge1 face) =
      fineEdgeRight (fineFaceEdge2 face)
  fineChartSupport : FineChart → Finset FineTarget
  fineChartSupport_nonempty : ∀ chart,
    (fineChartSupport chart).Nonempty
  chartMap : FineChart → CoarseChart
  edgeMap : FineEdge → Option CoarseEdge
  faceMap : FineFace → Option CoarseFace
  edge_some_left : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fineEdgeLeft fineEdge) = coarseEdgeLeft coarseEdge
  edge_some_right : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fineEdgeRight fineEdge) = coarseEdgeRight coarseEdge
  edge_none_fiber : ∀ fineEdge,
    edgeMap fineEdge = none →
      chartMap (fineEdgeLeft fineEdge) = chartMap (fineEdgeRight fineEdge)
  face_some_edge0 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fineFaceEdge0 fineFace) = some (coarseFaceEdge0 coarseFace)
  face_some_edge1 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fineFaceEdge1 fineFace) = some (coarseFaceEdge1 coarseFace)
  face_some_edge2 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fineFaceEdge2 fineFace) = some (coarseFaceEdge2 coarseFace)
  face_none_edge0 : ∀ fineFace,
    faceMap fineFace = none → edgeMap (fineFaceEdge0 fineFace) = none
  face_none_edge1 : ∀ fineFace,
    faceMap fineFace = none → edgeMap (fineFaceEdge1 fineFace) = none
  face_none_edge2 : ∀ fineFace,
    faceMap fineFace = none → edgeMap (fineFaceEdge2 fineFace) = none
  chartSupport_compatible_source : ∀ fineChart source,
    fineRead source ∈ fineChartSupport fineChart →
      coarseRead source ∈ coarseChartSupport (chartMap fineChart)

namespace FiniteComparisonPresentation

attribute [instance] sourceFintype sourceDecidableEq
attribute [instance] coarseTargetFintype coarseTargetDecidableEq
attribute [instance] fineTargetFintype fineTargetDecidableEq
attribute [instance] coarseChartFintype coarseChartDecidableEq
attribute [instance] coarseEdgeFintype coarseEdgeDecidableEq
attribute [instance] coarseFaceFintype coarseFaceDecidableEq
attribute [instance] fineChartFintype fineChartDecidableEq
attribute [instance] fineEdgeFintype fineEdgeDecidableEq
attribute [instance] fineFaceFintype fineFaceDecidableEq

/-- The coarse semantic reading generated from the raw finite reading table. -/
def coarseReading (P : FiniteComparisonPresentation) : Reading P.Source where
  Target := P.CoarseTarget
  read := P.coarseRead
  surjective := P.coarseRead_surjective

/-- The fine semantic reading generated from the raw finite reading table. -/
def fineReading (P : FiniteComparisonPresentation) : Reading P.Source where
  Target := P.FineTarget
  read := P.fineRead
  surjective := P.fineRead_surjective

/-- The semantic coarse-reading relation generated from the raw kernel
inclusion proof. -/
theorem coarserThan (P : FiniteComparisonPresentation) :
    P.coarseReading.CoarserThan P.fineReading := by
  intro left right hequal
  exact P.rawCoarserThan hequal

/-! ## Executable factor and canonical comparison -/

/-- Select a fine-reading representative by executable search through the
finite source enumeration. -/
def computedRepresentative (P : FiniteComparisonPresentation)
    (target : P.FineTarget) : P.Source :=
  firstMatchingOr P.sourceDefault
    (fun source => decide (P.fineRead source = target))
    P.sourceEntries

/-- The searched representative reads to the requested fine target. -/
theorem fineRead_computedRepresentative (P : FiniteComparisonPresentation)
    (target : P.FineTarget) :
    P.fineRead (P.computedRepresentative target) = target := by
  apply of_decide_eq_true
  unfold computedRepresentative
  obtain ⟨source, hsource⟩ := P.fineRead_surjective target
  exact firstMatchingOr_satisfies P.sourceDefault
    (fun entry => decide (P.fineRead entry = target)) P.sourceEntries
    ⟨source, P.source_mem_sourceEntries source, by simp [hsource]⟩

/-- The executable factor applies the raw coarse reading to an enumerated
representative of the fine target. -/
def computedFactor (P : FiniteComparisonPresentation) :
    P.FineTarget → P.CoarseTarget :=
  fun target => P.coarseRead (P.computedRepresentative target)

/-- The executable factor commutes with both raw reading tables. -/
theorem computedFactor_commutes (P : FiniteComparisonPresentation)
    (source : P.Source) :
    P.computedFactor (P.fineRead source) = P.coarseRead source := by
  exact P.rawCoarserThan
    (P.fineRead_computedRepresentative (P.fineRead source))

/-- The executable factor generated from the finite tables equals the
upstream canonical comparison factor. -/
theorem computedFactor_eq_comparisonFactor
    (P : FiniteComparisonPresentation) :
    P.computedFactor =
      comparisonFactor P.coarseReading P.fineReading P.coarserThan :=
  comparisonFactor_unique P.coarseReading P.fineReading P.coarserThan
    P.computedFactor P.computedFactor_commutes

/-! ## Generated supported nerves -/

/-- The coarse selected nerve generated from raw incidence and finite support
tables. -/
def coarseSupportedNerve (P : FiniteComparisonPresentation) :
    TargetSupportedNerve P.coarseReading where
  nerve := {
    Chart := P.CoarseChart
    EdgeComponent := P.CoarseEdge
    FaceComponent := P.CoarseFace
    edgeLeft := P.coarseEdgeLeft
    edgeRight := P.coarseEdgeRight
    faceEdge0 := P.coarseFaceEdge0
    faceEdge1 := P.coarseFaceEdge1
    faceEdge2 := P.coarseFaceEdge2
    edgeOverlapComponent := fun _ => True
    faceTripleOverlapComponent := fun _ => True
    edgeOverlapComponent_holds := fun _ => True.intro
    faceTripleOverlapComponent_holds := fun _ => True.intro
  }
  chartSupport := fun chart => (P.coarseChartSupport chart : Set P.CoarseTarget)
  chartSupport_nonempty := fun chart => by
    simpa using P.coarseChartSupport_nonempty chart
  faceEdge0_left := P.coarseFaceEdge0_left
  faceEdge0_right := P.coarseFaceEdge0_right
  faceEdge1_right := P.coarseFaceEdge1_right

/-- The fine selected nerve generated from raw incidence and finite support
tables. -/
def fineSupportedNerve (P : FiniteComparisonPresentation) :
    TargetSupportedNerve P.fineReading where
  nerve := {
    Chart := P.FineChart
    EdgeComponent := P.FineEdge
    FaceComponent := P.FineFace
    edgeLeft := P.fineEdgeLeft
    edgeRight := P.fineEdgeRight
    faceEdge0 := P.fineFaceEdge0
    faceEdge1 := P.fineFaceEdge1
    faceEdge2 := P.fineFaceEdge2
    edgeOverlapComponent := fun _ => True
    faceTripleOverlapComponent := fun _ => True
    edgeOverlapComponent_holds := fun _ => True.intro
    faceTripleOverlapComponent_holds := fun _ => True.intro
  }
  chartSupport := fun chart => (P.fineChartSupport chart : Set P.FineTarget)
  chartSupport_nonempty := fun chart => by
    simpa using P.fineChartSupport_nonempty chart
  faceEdge0_left := P.fineFaceEdge0_left
  faceEdge0_right := P.fineFaceEdge0_right
  faceEdge1_right := P.fineFaceEdge1_right

/-! ## Generated actual comparison geometry -/

/-- The actual G-104 comparison morphism generated from all raw presentation
tables.  Its support proof uses the computed/canonical factor equality. -/
def toGeometry (P : FiniteComparisonPresentation) :
    TargetSupportedNerveMorphism
      P.coarseReading P.fineReading P.coarserThan
      P.coarseSupportedNerve P.fineSupportedNerve where
  chartMap := P.chartMap
  edgeMap := P.edgeMap
  faceMap := P.faceMap
  edge_some_left := P.edge_some_left
  edge_some_right := P.edge_some_right
  edge_none_fiber := P.edge_none_fiber
  face_some_edge0 := P.face_some_edge0
  face_some_edge1 := P.face_some_edge1
  face_some_edge2 := P.face_some_edge2
  face_none_edge0 := P.face_none_edge0
  face_none_edge1 := P.face_none_edge1
  face_none_edge2 := P.face_none_edge2
  chartSupport_compatible := by
    intro fineChart fineTarget htarget
    rw [← congrFun P.computedFactor_eq_comparisonFactor fineTarget]
    exact P.chartSupport_compatible_source fineChart
      (P.computedRepresentative fineTarget) (by
        simpa only [P.fineRead_computedRepresentative fineTarget] using htarget)

/-! ## Raw/semantic correspondence API -/

/-- Semantic coarse reading agrees pointwise with the raw coarse table. -/
@[simp]
theorem coarseReading_read (P : FiniteComparisonPresentation)
    (source : P.Source) : P.coarseReading.read source = P.coarseRead source :=
  rfl

/-- Semantic fine reading agrees pointwise with the raw fine table. -/
@[simp]
theorem fineReading_read (P : FiniteComparisonPresentation)
    (source : P.Source) : P.fineReading.read source = P.fineRead source :=
  rfl

/-- Coarse semantic chart support is exactly raw `Finset` membership. -/
@[simp]
theorem mem_coarseSupportedNerve_chartSupport
    (P : FiniteComparisonPresentation) (chart : P.CoarseChart)
    (target : P.CoarseTarget) :
    target ∈ P.coarseSupportedNerve.chartSupport chart ↔
      target ∈ P.coarseChartSupport chart :=
  Iff.rfl

/-- Fine semantic chart support is exactly raw `Finset` membership. -/
@[simp]
theorem mem_fineSupportedNerve_chartSupport
    (P : FiniteComparisonPresentation) (chart : P.FineChart)
    (target : P.FineTarget) :
    target ∈ P.fineSupportedNerve.chartSupport chart ↔
      target ∈ P.fineChartSupport chart :=
  Iff.rfl

/-- The generated semantic chart map is the raw chart table. -/
@[simp]
theorem toGeometry_chartMap (P : FiniteComparisonPresentation)
    (chart : P.FineChart) : P.toGeometry.chartMap chart = P.chartMap chart :=
  rfl

/-- The generated semantic edge map is the raw partial edge table. -/
@[simp]
theorem toGeometry_edgeMap (P : FiniteComparisonPresentation)
    (edge : P.FineEdge) : P.toGeometry.edgeMap edge = P.edgeMap edge :=
  rfl

/-- The generated semantic face map is the raw partial face table. -/
@[simp]
theorem toGeometry_faceMap (P : FiniteComparisonPresentation)
    (face : P.FineFace) : P.toGeometry.faceMap face = P.faceMap face :=
  rfl

/-- The coarse semantic left endpoint is the raw incidence table. -/
@[simp]
theorem coarseSupportedNerve_edgeLeft (P : FiniteComparisonPresentation)
    (edge : P.CoarseEdge) :
    P.coarseSupportedNerve.nerve.edgeLeft edge = P.coarseEdgeLeft edge :=
  rfl

/-- The coarse semantic right endpoint is the raw incidence table. -/
@[simp]
theorem coarseSupportedNerve_edgeRight (P : FiniteComparisonPresentation)
    (edge : P.CoarseEdge) :
    P.coarseSupportedNerve.nerve.edgeRight edge = P.coarseEdgeRight edge :=
  rfl

/-- The coarse semantic first face edge is the raw incidence table. -/
@[simp]
theorem coarseSupportedNerve_faceEdge0 (P : FiniteComparisonPresentation)
    (face : P.CoarseFace) :
    P.coarseSupportedNerve.nerve.faceEdge0 face = P.coarseFaceEdge0 face :=
  rfl

/-- The coarse semantic second face edge is the raw incidence table. -/
@[simp]
theorem coarseSupportedNerve_faceEdge1 (P : FiniteComparisonPresentation)
    (face : P.CoarseFace) :
    P.coarseSupportedNerve.nerve.faceEdge1 face = P.coarseFaceEdge1 face :=
  rfl

/-- The coarse semantic third face edge is the raw incidence table. -/
@[simp]
theorem coarseSupportedNerve_faceEdge2 (P : FiniteComparisonPresentation)
    (face : P.CoarseFace) :
    P.coarseSupportedNerve.nerve.faceEdge2 face = P.coarseFaceEdge2 face :=
  rfl

/-- The fine semantic left endpoint is the raw incidence table. -/
@[simp]
theorem fineSupportedNerve_edgeLeft (P : FiniteComparisonPresentation)
    (edge : P.FineEdge) :
    P.fineSupportedNerve.nerve.edgeLeft edge = P.fineEdgeLeft edge :=
  rfl

/-- The fine semantic right endpoint is the raw incidence table. -/
@[simp]
theorem fineSupportedNerve_edgeRight (P : FiniteComparisonPresentation)
    (edge : P.FineEdge) :
    P.fineSupportedNerve.nerve.edgeRight edge = P.fineEdgeRight edge :=
  rfl

/-- The fine semantic first face edge is the raw incidence table. -/
@[simp]
theorem fineSupportedNerve_faceEdge0 (P : FiniteComparisonPresentation)
    (face : P.FineFace) :
    P.fineSupportedNerve.nerve.faceEdge0 face = P.fineFaceEdge0 face :=
  rfl

/-- The fine semantic second face edge is the raw incidence table. -/
@[simp]
theorem fineSupportedNerve_faceEdge1 (P : FiniteComparisonPresentation)
    (face : P.FineFace) :
    P.fineSupportedNerve.nerve.faceEdge1 face = P.fineFaceEdge1 face :=
  rfl

/-- The fine semantic third face edge is the raw incidence table. -/
@[simp]
theorem fineSupportedNerve_faceEdge2 (P : FiniteComparisonPresentation)
    (face : P.FineFace) :
    P.fineSupportedNerve.nerve.faceEdge2 face = P.fineFaceEdge2 face :=
  rfl

end FiniteComparisonPresentation

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
