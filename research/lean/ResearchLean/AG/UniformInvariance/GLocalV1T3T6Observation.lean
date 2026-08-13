import ResearchLean.AG.UniformInvariance.GLocalV1T3T6Witnesses
import ResearchLean.AG.UniformInvariance.GLocalV1Observation

/-!
# Registered T3/T6 `G_local-v1` observation equality

This module discharges fixed GOAL claim (v)(a).  It evaluates every structural
coordinate of the permanent observation kernel for the independently
registered ternary-cycle T3 and T6 presentations, proves both evaluations
equal one closed presentation-independent normal form, and concludes
`obsG T3 = obsG T6`.

The proof uses only the registered raw incidence/support/map tables, the full
generated relabel orbit, Cycle 24's six packet-empty theorems, and permanent
definition-owner evaluation APIs.  The common normal form is constructed from
literal observation constructors and complete occurrence lists; it is not a
presentation field, theorem premise, checker result, uniformity label, or
external certificate.

## Implementation notes

Each of the six nonempty target scopes is normalized in two layers: first a
retained cell's label and neighbor histogram are proved from the registered raw
tables, then the permanent histogram quotient clips only repeated occurrences.
This mirrors the radius-one observation contract while avoiding enumeration of
the exponentially large state space.  Direct reduction of the entire `obsG`
term was rejected because it obscures which raw component is used and is not a
practical kernel computation for T6.  Supplying the common value as a theorem
premise or presentation field was also rejected as answer encoding; instead it
is a closed literal value reached independently from both presentations.  The
final orbit minimum uses an owner theorem saying every generated candidate is
that value, so the structured comparator itself is never opened downstream.
-/

namespace AAT.AG.ResolutionInvariance
namespace GLocalV1T3T6Witnesses

open FiniteComparisonPresentation

/-- Closed flag row shared by the hand normal forms for one side and cell type.

Position: fixture-local constructor for fixed GOAL claim (v)(a).  Its entries
encode only the reducer flags proved from the registered raw self-loop and
FaceTwin tables below; no observation value or semantic label is an input. -/
def handFlags (side : GLocalV1Side) (cellType : GLocalV1CellType) :
    GLocalV1Flags :=
  match cellType with
  | .vertex => ⟨true, false, decide (side = .fine), false, false, false⟩
  | .edge => ⟨true, decide (side = .coarse), false, false, true, false⟩
  | _ => ⟨false, false, false, false, false, false⟩

/-- Assemble one closed cell-label normal form from its literal structural
coordinates.

Position: fixture-local constructor for claim (v)(a).  Support and factor-image
codes are explicit raw-table normal forms, not supplied results of `obsG`. -/
def handLabel (side : GLocalV1Side) (cellType : GLocalV1CellType)
    (support piImage : List Nat) : GLocalV1CellLabel :=
  ⟨side, cellType, .mapped, support, piImage, handFlags side cellType⟩

/-- Assemble one closed radius-one neighbor descriptor from a proved label,
signed incidence list, and complete outward-stub occurrences.

Position: fixture-local constructor for claim (v)(a); histogram clipping is
performed by the permanent kernel and no expected descriptor is assumed. -/
def handDescriptor (label : GLocalV1CellLabel)
    (relations : List GLocalV1Relation)
    (stubs : List GLocalV1OutwardStub) : GLocalV1NeighborDescriptor :=
  ⟨label, relations.mergeSort gLocalV1OrdLE, gLocalV1Histogram stubs⟩

/-- Assemble one closed rooted-ball normal form from a root label and complete
neighbor-descriptor occurrences.

Position: fixture-local constructor for claim (v)(a).  The permanent histogram
kernel performs the only normalization; neither presentation is referenced. -/
def handBall (root : GLocalV1CellLabel)
    (neighbors : List GLocalV1NeighborDescriptor) : GLocalV1RootedBall :=
  ⟨root, gLocalV1Histogram neighbors⟩

/-- The anchor-chart ball used as a closed normal form in the registered
T3/T6 evaluations.

Position: fixture-local constructor for fixed GOAL claim (v)(a). Raw
premise/provenance: it is built only from literal chart-at and endpoint-slot
incidence occurrences, with no observation or semantic label as input. -/
def handAnchorChartBall (side : GLocalV1Side) (support piImage : List Nat) :
    GLocalV1RootedBall :=
  let chart := handLabel side .chart support piImage
  let vertex := handLabel side .vertex support piImage
  handBall chart [handDescriptor vertex [.chartAt]
    [⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩]]

/-- The anchor-vertex ball used as a closed normal form in the registered
T3/T6 evaluations.

Position: fixture-local constructor for claim (v)(a). Raw
premise/provenance: its chart and self-loop edge descriptors are the complete
registered anchor incidence occurrences, not a precomputed observation. -/
def handAnchorVertexBall (side : GLocalV1Side) (support piImage : List Nat) :
    GLocalV1RootedBall :=
  let chart := handLabel side .chart support piImage
  let vertex := handLabel side .vertex support piImage
  let edge := handLabel side .edge support piImage
  handBall vertex [handDescriptor chart [.chartAt] [],
    handDescriptor edge [.endpoint0, .endpoint1] []]

/-- The anchor-edge ball used as a closed normal form in the registered
T3/T6 evaluations.

Position: fixture-local constructor for claim (v)(a). Raw
premise/provenance: its doubled endpoint relation and chart outward stub come
directly from the registered anchor self-loop. -/
def handAnchorEdgeBall (side : GLocalV1Side) (support piImage : List Nat) :
    GLocalV1RootedBall :=
  let vertex := handLabel side .vertex support piImage
  let edge := handLabel side .edge support piImage
  handBall edge [handDescriptor vertex [.endpoint0, .endpoint1]
    [⟨.chart, .chartAt⟩]]

/-- The neutral-chart ball with multiplicities already clipped at two.

Position: fixture-local normal-form constructor for claim (v)(a). Raw
premise/provenance: its two saturated endpoint-slot occurrences are justified
below from the literal threefold and sixfold neutral incidence tables. -/
def handNeutralChartBall (side : GLocalV1Side) (support piImage : List Nat) :
    GLocalV1RootedBall :=
  let chart := handLabel side .chart support piImage
  let vertex := handLabel side .vertex support piImage
  handBall chart [handDescriptor vertex [.chartAt]
    [⟨.edge, .slot0⟩, ⟨.edge, .slot0⟩,
     ⟨.edge, .slot1⟩, ⟨.edge, .slot1⟩]]

/-- The neutral-vertex ball with repeated incident edges clipped at two.

Position: fixture-local normal-form constructor for claim (v)(a). Raw
premise/provenance: the descriptor contains the registered chart relation and
the clip-two image of all repeated neutral-edge incidences. -/
def handNeutralVertexBall (side : GLocalV1Side) (support piImage : List Nat) :
    GLocalV1RootedBall :=
  let chart := handLabel side .chart support piImage
  let vertex := handLabel side .vertex support piImage
  let edge := handLabel side .edge support piImage
  let vertexToEdge := handDescriptor edge [.endpoint0, .endpoint1]
    [⟨.face, .slot0⟩, ⟨.face, .slot1⟩, ⟨.face, .slot2⟩]
  handBall vertex [handDescriptor chart [.chartAt] [],
    vertexToEdge, vertexToEdge]

/-- The neutral-edge ball with all radius-two multiplicities clipped at two.

Position: fixture-local normal-form constructor for claim (v)(a). Raw
premise/provenance: its vertex and three boundary-face descriptors enumerate
the registered radius-two incidences before the permanent histogram kernel
identifies multiplicities above two. -/
def handNeutralEdgeBall (side : GLocalV1Side) (support piImage : List Nat) :
    GLocalV1RootedBall :=
  let vertex := handLabel side .vertex support piImage
  let edge := handLabel side .edge support piImage
  let face := handLabel side .face support piImage
  handBall edge [
    handDescriptor vertex [.endpoint0, .endpoint1]
      [⟨.chart, .chartAt⟩,
       ⟨.edge, .slot0⟩, ⟨.edge, .slot0⟩,
       ⟨.edge, .slot1⟩, ⟨.edge, .slot1⟩],
    handDescriptor face [.boundary0Pos]
      [⟨.edge, .slot1⟩, ⟨.edge, .slot2⟩],
    handDescriptor face [.boundary1Neg]
      [⟨.edge, .slot0⟩, ⟨.edge, .slot2⟩],
    handDescriptor face [.boundary2Pos]
      [⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩]]

/-- The neutral-face ball with all repeated boundary occurrences clipped.

Position: fixture-local normal-form constructor for claim (v)(a). Raw
premise/provenance: its three signed boundary descriptors are assembled from
the registered face table and complete endpoint/adjacent-face stubs. -/
def handNeutralFaceBall (side : GLocalV1Side) (support piImage : List Nat) :
    GLocalV1RootedBall :=
  let edge := handLabel side .edge support piImage
  let face := handLabel side .face support piImage
  handBall face [
    handDescriptor edge [.boundary0Pos]
      [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
       ⟨.face, .slot1⟩, ⟨.face, .slot2⟩],
    handDescriptor edge [.boundary1Neg]
      [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
       ⟨.face, .slot0⟩, ⟨.face, .slot2⟩],
    handDescriptor edge [.boundary2Pos]
      [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
       ⟨.face, .slot0⟩, ⟨.face, .slot1⟩]]

/-- Ordered chart/vertex prefix of the anchor component in the closed
occurrence normal form.

Position: fixture-local list constructor for claim (v)(a), generated from the
named hand balls and carrying no computed histogram as a premise. -/
def orderedAnchorChartVertex (side : GLocalV1Side)
    (support piImage : List Nat) : List GLocalV1RootedBall :=
  [handAnchorChartBall side support piImage,
   handAnchorVertexBall side support piImage]

/-- Ordered anchor-edge block in the closed occurrence normal form.

Position: fixture-local list constructor for claim (v)(a), retaining the raw
single anchor-edge multiplicity before histogram clipping. -/
def orderedAnchorEdge (side : GLocalV1Side)
    (support piImage : List Nat) : List GLocalV1RootedBall :=
  [handAnchorEdgeBall side support piImage]

/-- Ordered chart/vertex prefix of a neutral component.

Position: fixture-local list constructor for claim (v)(a), built only from
the two named neutral rooted balls. -/
def orderedNeutralChartVertex (side : GLocalV1Side)
    (support piImage : List Nat) : List GLocalV1RootedBall :=
  [handNeutralChartBall side support piImage,
   handNeutralVertexBall side support piImage]

/-- Repeat the neutral-edge ball with the literal registered multiplicity.

Position: raw occurrence-list constructor for claim (v)(a).  The count is
later specialized independently to T3 and T6 before clip-two saturation. -/
def orderedNeutralEdges (side : GLocalV1Side)
    (support piImage : List Nat) (count : Nat) : List GLocalV1RootedBall :=
  List.replicate count (handNeutralEdgeBall side support piImage)

/-- Repeat the neutral-face ball with the literal registered multiplicity.

Position: raw occurrence-list constructor for claim (v)(a).  It records the
complete T3/T6 face occurrences rather than an already clipped result. -/
def orderedNeutralFaces (side : GLocalV1Side)
    (support piImage : List Nat) (count : Nat) : List GLocalV1RootedBall :=
  List.replicate count (handNeutralFaceBall side support piImage)

/-- Complete target-zero rooted-ball occurrence normal form parameterized by
the registered neutral multiplicity.

Position: closed structural list for claim (v)(a), assembled independently of
`obsG`, checker values, and the T3/T6 semantic labels. -/
def rawA0Occurrences (count : Nat) : List GLocalV1RootedBall :=
  orderedAnchorChartVertex .coarse [0] [0] ++
  orderedNeutralChartVertex .coarse [0] [0] ++
  orderedAnchorEdge .coarse [0] [0] ++
  orderedNeutralEdges .coarse [0] [0] count ++
  orderedNeutralFaces .coarse [0] [0] count ++
  orderedAnchorChartVertex .fine [0, 1] [0] ++
  orderedAnchorEdge .fine [0, 1] [0]

/-- Complete target-one rooted-ball occurrence normal form parameterized by
the registered neutral multiplicity.

Position: closed structural list for claim (v)(a); every entry comes from the
neutral raw incidence/support pattern and no observation result is supplied. -/
def rawA1Occurrences (count : Nat) : List GLocalV1RootedBall :=
  orderedNeutralChartVertex .coarse [1] [1] ++
  orderedNeutralEdges .coarse [1] [1] count ++
  orderedNeutralFaces .coarse [1] [1] count ++
  orderedNeutralChartVertex .fine [2] [1] ++
  orderedNeutralEdges .fine [2] [1] count ++
  orderedNeutralFaces .fine [2] [1] count

/-- Complete full-target rooted-ball occurrence normal form parameterized by
the registered neutral multiplicity.

Position: closed structural list for claim (v)(a), combining the anchor and
neutral raw components before permanent histogram clipping. -/
def rawFullOccurrences (count : Nat) : List GLocalV1RootedBall :=
  orderedAnchorChartVertex .coarse [0] [0] ++
  orderedNeutralChartVertex .coarse [0, 1] [0, 1] ++
  orderedAnchorEdge .coarse [0] [0] ++
  orderedNeutralEdges .coarse [0, 1] [0, 1] count ++
  orderedNeutralFaces .coarse [0, 1] [0, 1] count ++
  orderedAnchorChartVertex .fine [0, 1] [0] ++
  orderedNeutralChartVertex .fine [2] [1] ++
  orderedAnchorEdge .fine [0, 1] [0] ++
  orderedNeutralEdges .fine [2] [1] count ++
  orderedNeutralFaces .fine [2] [1] count

/-- Closed target-zero histogram normal form chosen from the complete T3
occurrence list.

Position: presentation-independent normal form for claim (v)(a).  The later
T6 equality is proved by clip-two saturation rather than assumed here. -/
def commonA0Balls : GLocalV1Histogram GLocalV1RootedBall :=
  gLocalV1Histogram (rawA0Occurrences 3)

/-- Closed target-one histogram normal form chosen from the complete T3
occurrence list.

Position: presentation-independent normal form for claim (v)(a), with no
dependency on a presentation field, checker bit, or semantic label. -/
def commonA1Balls : GLocalV1Histogram GLocalV1RootedBall :=
  gLocalV1Histogram (rawA1Occurrences 3)

/-- Closed full-target histogram normal form chosen from the complete T3
occurrence list.

Position: presentation-independent normal form for claim (v)(a); T3 and T6
are evaluated to it independently below. -/
def commonFullBalls : GLocalV1Histogram GLocalV1RootedBall :=
  gLocalV1Histogram (rawFullOccurrences 3)

/-! ## Multiplicity-saturated occurrence normal forms -/

/-- Saturate one repeated rooted-ball block inside a common prefix and suffix.

Position: fixture-local list reassociation helper for fixed GOAL claim
(v)(a).  It delegates every semantic step to the definition-owner lawful-order
histogram API and carries no expected observation or label. -/
theorem rootedBallHistogram_saturateBlock (extra : Nat)
    (pre post : List GLocalV1RootedBall) (payload : GLocalV1RootedBall) :
    gLocalV1Histogram
        ((pre ++ List.replicate (extra + 2) payload) ++ post) =
      gLocalV1Histogram ((pre ++ [payload, payload]) ++ post) := by
  simpa only [List.append_assoc] using
    gLocalV1RootedBallHistogram_append_replicate_add_two_eq_two
      pre post payload extra

/-- Every target-zero neutral multiplicity at least two has the common clipped
rooted-ball histogram.

Position: fixture-local multiplicity normalization for fixed GOAL claim
(v)(a).  It uses only the complete literal occurrence list and the owner
clip-two saturation theorem; no observation result is supplied. -/
theorem rawA0OccurrencesHistogram_add_two_eq_two (extra : Nat) :
    gLocalV1Histogram (rawA0Occurrences (extra + 2)) =
      gLocalV1Histogram (rawA0Occurrences 2) := by
  unfold rawA0Occurrences orderedAnchorChartVertex
    orderedNeutralChartVertex orderedAnchorEdge orderedNeutralEdges
    orderedNeutralFaces
  let preEdge := [handAnchorChartBall .coarse [0] [0],
    handAnchorVertexBall .coarse [0] [0],
    handNeutralChartBall .coarse [0] [0],
    handNeutralVertexBall .coarse [0] [0],
    handAnchorEdgeBall .coarse [0] [0]]
  let edge := handNeutralEdgeBall .coarse [0] [0]
  let face := handNeutralFaceBall .coarse [0] [0]
  let post := [handAnchorChartBall .fine [0, 1] [0],
    handAnchorVertexBall .fine [0, 1] [0],
    handAnchorEdgeBall .fine [0, 1] [0]]
  calc
    _ = gLocalV1Histogram
        ((preEdge ++ [edge, edge]) ++
          (List.replicate (extra + 2) face ++ post)) := by
      simpa only [preEdge, edge, face, post, List.append_assoc] using
        rootedBallHistogram_saturateBlock extra preEdge
          (List.replicate (extra + 2) face ++ post) edge
    _ = gLocalV1Histogram
        (((preEdge ++ [edge, edge]) ++ [face, face]) ++ post) := by
      simpa only [List.append_assoc] using
        rootedBallHistogram_saturateBlock extra
          (preEdge ++ [edge, edge]) post face
    _ = _ := by rfl

/-- Every target-one neutral multiplicity at least two has the common clipped
rooted-ball histogram.

Position: fixture-local multiplicity normalization for fixed GOAL claim
(v)(a).  It uses only the complete literal occurrence list and the owner
clip-two saturation theorem; no observation result is supplied. -/
theorem rawA1OccurrencesHistogram_add_two_eq_two (extra : Nat) :
    gLocalV1Histogram (rawA1Occurrences (extra + 2)) =
      gLocalV1Histogram (rawA1Occurrences 2) := by
  unfold rawA1Occurrences orderedNeutralChartVertex orderedNeutralEdges
    orderedNeutralFaces
  let pre := [handNeutralChartBall .coarse [1] [1],
    handNeutralVertexBall .coarse [1] [1]]
  let ce := handNeutralEdgeBall .coarse [1] [1]
  let cf := handNeutralFaceBall .coarse [1] [1]
  let middle := [handNeutralChartBall .fine [2] [1],
    handNeutralVertexBall .fine [2] [1]]
  let fe := handNeutralEdgeBall .fine [2] [1]
  let ff := handNeutralFaceBall .fine [2] [1]
  calc
    _ = gLocalV1Histogram
        ((pre ++ [ce, ce]) ++
          (List.replicate (extra + 2) cf ++ middle ++
            List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff)) := by
      simpa only [pre, ce, cf, middle, fe, ff, List.append_assoc] using
        rootedBallHistogram_saturateBlock extra pre
          (List.replicate (extra + 2) cf ++ middle ++
            List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff) ce
    _ = gLocalV1Histogram
        (((pre ++ [ce, ce]) ++ [cf, cf]) ++
          (middle ++ List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff)) := by
      simpa only [List.append_assoc] using
        rootedBallHistogram_saturateBlock extra (pre ++ [ce, ce])
          (middle ++ List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff) cf
    _ = gLocalV1Histogram
        ((((pre ++ [ce, ce]) ++ [cf, cf]) ++ middle ++ [fe, fe]) ++
          List.replicate (extra + 2) ff) := by
      simpa only [List.append_assoc] using
        rootedBallHistogram_saturateBlock extra
          ((pre ++ [ce, ce]) ++ [cf, cf] ++ middle)
          (List.replicate (extra + 2) ff) fe
    _ = gLocalV1Histogram
        (((((pre ++ [ce, ce]) ++ [cf, cf]) ++ middle ++ [fe, fe]) ++
          [ff, ff]) ++ []) := by
      simpa only [List.append_assoc, List.append_nil] using
        rootedBallHistogram_saturateBlock extra
          (((pre ++ [ce, ce]) ++ [cf, cf]) ++ middle ++ [fe, fe]) [] ff
    _ = _ := by rfl

/-- Every full-scope neutral multiplicity at least two has the common clipped
rooted-ball histogram.

Position: fixture-local multiplicity normalization for fixed GOAL claim
(v)(a).  It uses only the complete literal occurrence list and the owner
clip-two saturation theorem; no observation result is supplied. -/
theorem rawFullOccurrencesHistogram_add_two_eq_two (extra : Nat) :
    gLocalV1Histogram (rawFullOccurrences (extra + 2)) =
      gLocalV1Histogram (rawFullOccurrences 2) := by
  unfold rawFullOccurrences orderedAnchorChartVertex
    orderedNeutralChartVertex orderedAnchorEdge orderedNeutralEdges
    orderedNeutralFaces
  let pre := [handAnchorChartBall .coarse [0] [0],
    handAnchorVertexBall .coarse [0] [0],
    handNeutralChartBall .coarse [0, 1] [0, 1],
    handNeutralVertexBall .coarse [0, 1] [0, 1],
    handAnchorEdgeBall .coarse [0] [0]]
  let ce := handNeutralEdgeBall .coarse [0, 1] [0, 1]
  let cf := handNeutralFaceBall .coarse [0, 1] [0, 1]
  let middle := [handAnchorChartBall .fine [0, 1] [0],
    handAnchorVertexBall .fine [0, 1] [0],
    handNeutralChartBall .fine [2] [1],
    handNeutralVertexBall .fine [2] [1],
    handAnchorEdgeBall .fine [0, 1] [0]]
  let fe := handNeutralEdgeBall .fine [2] [1]
  let ff := handNeutralFaceBall .fine [2] [1]
  calc
    _ = gLocalV1Histogram
        ((pre ++ [ce, ce]) ++
          (List.replicate (extra + 2) cf ++ middle ++
            List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff)) := by
      simpa only [pre, ce, cf, middle, fe, ff, List.append_assoc] using
        rootedBallHistogram_saturateBlock extra pre
          (List.replicate (extra + 2) cf ++ middle ++
            List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff) ce
    _ = gLocalV1Histogram
        (((pre ++ [ce, ce]) ++ [cf, cf]) ++
          (middle ++ List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff)) := by
      simpa only [List.append_assoc] using
        rootedBallHistogram_saturateBlock extra (pre ++ [ce, ce])
          (middle ++ List.replicate (extra + 2) fe ++
            List.replicate (extra + 2) ff) cf
    _ = gLocalV1Histogram
        ((((pre ++ [ce, ce]) ++ [cf, cf]) ++ middle ++ [fe, fe]) ++
          List.replicate (extra + 2) ff) := by
      simpa only [List.append_assoc] using
        rootedBallHistogram_saturateBlock extra
          ((pre ++ [ce, ce]) ++ [cf, cf] ++ middle)
          (List.replicate (extra + 2) ff) fe
    _ = gLocalV1Histogram
        (((((pre ++ [ce, ce]) ++ [cf, cf]) ++ middle ++ [fe, fe]) ++
          [ff, ff]) ++ []) := by
      simpa only [List.append_assoc, List.append_nil] using
        rootedBallHistogram_saturateBlock extra
          (((pre ++ [ce, ce]) ++ [cf, cf]) ++ middle ++ [fe, fe]) [] ff
    _ = _ := by rfl

/-- Three copies are the chosen closed target-zero histogram normal form.

Position: fixture-local definitional normalization for fixed GOAL claim
(v)(a); it introduces no observation premise. -/
theorem rawA0Histogram_three_eq_common :
    gLocalV1Histogram (rawA0Occurrences 3) = commonA0Balls := by
  rfl

/-- Three copies are the chosen closed target-one histogram normal form.

Position: fixture-local definitional normalization for fixed GOAL claim
(v)(a); it introduces no observation premise. -/
theorem rawA1Histogram_three_eq_common :
    gLocalV1Histogram (rawA1Occurrences 3) = commonA1Balls := by
  rfl

/-- Three copies are the chosen closed full-scope histogram normal form.

Position: fixture-local definitional normalization for fixed GOAL claim
(v)(a); it introduces no observation premise. -/
theorem rawFullHistogram_three_eq_common :
    gLocalV1Histogram (rawFullOccurrences 3) = commonFullBalls := by
  rfl

/-- Six and three copies of each target-zero neutral role have the same
clipped histogram.

Position: fixture-local finite multiplicity normalization for fixed GOAL
claim (v)(a).  It uses only the complete raw occurrence lists. -/
theorem rawA0Histogram_six_eq_common :
    gLocalV1Histogram (rawA0Occurrences 6) = commonA0Balls := by
  exact (rawA0OccurrencesHistogram_add_two_eq_two 4).trans
    (rawA0OccurrencesHistogram_add_two_eq_two 1).symm

/-- Six and three copies of each target-one neutral role have the same
clipped histogram.

Position: fixture-local finite multiplicity normalization for fixed GOAL
claim (v)(a).  It uses only the complete raw occurrence lists. -/
theorem rawA1Histogram_six_eq_common :
    gLocalV1Histogram (rawA1Occurrences 6) = commonA1Balls := by
  exact (rawA1OccurrencesHistogram_add_two_eq_two 4).trans
    (rawA1OccurrencesHistogram_add_two_eq_two 1).symm

/-- Six and three copies of each full-scope neutral role have the same
clipped histogram.

Position: fixture-local finite multiplicity normalization for fixed GOAL
claim (v)(a).  It uses only the complete raw occurrence lists. -/
theorem rawFullHistogram_six_eq_common :
    gLocalV1Histogram (rawFullOccurrences 6) = commonFullBalls := by
  exact (rawFullOccurrencesHistogram_add_two_eq_two 4).trans
    (rawFullOccurrencesHistogram_add_two_eq_two 1).symm


section IdentitySplitGeneric

variable {neutralEdgeCount faceCount : Nat}
variable (faceEdge0 faceEdge1 faceEdge2 :
  Fin faceCount → Fin (neutralEdgeCount + 1))
variable (hfaceEdge0 : ∀ face, faceEdge0 face ≠ 0)
variable (hfaceEdge1 : ∀ face, faceEdge1 face ≠ 0)
variable (hfaceEdge2 : ∀ face, faceEdge2 face ≠ 0)

local notation "P" => identitySplitPresentation neutralEdgeCount faceCount
  faceEdge0 faceEdge1 faceEdge2 hfaceEdge0 hfaceEdge1 hfaceEdge2

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
def c25IdentitySplitSwapRelabel : (P).GLocalV1TargetRelabel :=
  ⟨[0, 1], [1, 0, 2]⟩

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
@[simp] theorem c25IdentitySplitCoarseTargetEntriesDedup :
    (P).coarseTargetEntriesDedup = List.finRange 2 := by
  rfl

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
@[simp] theorem c25IdentitySplitFineTargetEntries :
    (P).fineTargetEntries = List.finRange 3 := by
  rfl

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
@[simp] theorem c25IdentitySplitCoarseTargetCode (target : Fin 2) :
    (P).coarseTargetCode target = target.val := by
  fin_cases target <;> rfl

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
@[simp] theorem c25IdentitySplitFineTargetCode (target : Fin 3) :
    (P).fineTargetCode target = target.val := by
  fin_cases target <;> rfl

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
@[simp] theorem c25IdentitySplitComputedFactor (target : Fin 3) :
    (P).computedFactor target = coarseRead target := by
  fin_cases target <;> rfl

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
theorem c25IdentitySplitTargetRelabelValid_iff
    (relabel : (P).GLocalV1TargetRelabel) :
    (P).gLocalV1TargetRelabelValid relabel = true ↔
      relabel = (P).gLocalV1IdentityRelabel ∨
      relabel = c25IdentitySplitSwapRelabel faceEdge0 faceEdge1 faceEdge2
        hfaceEdge0 hfaceEdge1 hfaceEdge2 := by
  rcases relabel with ⟨coarse, fine⟩
  constructor
  · intro hvalid
    have hcoarse :=
      (P).gLocalV1TargetRelabelValid_coarse_perm
        ⟨coarse, fine⟩ hvalid
    have hfine :=
      (P).gLocalV1TargetRelabelValid_fine_perm
        ⟨coarse, fine⟩ hvalid
    rw [c25IdentitySplitCoarseTargetEntriesDedup] at hcoarse
    rw [c25IdentitySplitFineTargetEntries] at hfine
    change coarse.Perm [0, 1] at hcoarse
    change fine.Perm [0, 1, 2] at hfine
    have hcoarseMem : coarse ∈ [0, 1].permutations :=
      List.mem_permutations.mpr hcoarse
    have hfineMem : fine ∈ [0, 1, 2].permutations :=
      List.mem_permutations.mpr hfine
    simp [List.permutations, List.permutationsAux_cons,
      List.permutationsAux_nil, List.permutationsAux2_snd_cons,
      List.permutationsAux2_snd_nil] at hcoarseMem hfineMem
    rcases hcoarseMem with rfl | rfl <;>
      rcases hfineMem with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      try { exact Or.inl rfl }
      try { exact Or.inr rfl }
    all_goals
      exfalso
      have hcomm := (P).gLocalV1TargetRelabelValid_commutes _ hvalid
      have h0 := hcomm (0 : Fin 3)
      have h1 := hcomm (1 : Fin 3)
      have h2 := hcomm (2 : Fin 3)
      simp [c25IdentitySplitComputedFactor,
        c25IdentitySplitCoarseTargetCode,
        c25IdentitySplitFineTargetCode,
        c25IdentitySplitFineTargetEntries,
        gLocalV1CoarseRelabelCode_mk,
        gLocalV1FineRelabelTarget_mk, coarseRead,
        List.finRange] at h0 h1 h2
  · intro h
    rcases h with hidentity | hswap
    · rw [hidentity]
      exact (P).gLocalV1IdentityRelabel_valid
    · rw [hswap]
      apply (P).gLocalV1TargetRelabelValid_of
      · rw [c25IdentitySplitCoarseTargetEntriesDedup]
        change [0, 1].Perm [0, 1]
        decide
      · rw [c25IdentitySplitFineTargetEntries]
        change [1, 0, 2].Perm [0, 1, 2]
        decide
      · intro target _htarget
        fin_cases target <;>
          simp [c25IdentitySplitSwapRelabel,
            c25IdentitySplitComputedFactor,
            c25IdentitySplitCoarseTargetCode,
            c25IdentitySplitFineTargetCode,
            c25IdentitySplitFineTargetEntries, coarseRead, List.finRange]

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
theorem c25IdentitySplitMemTargetRelabels_iff
    (relabel : (P).GLocalV1TargetRelabel) :
    relabel ∈ (P).gLocalV1TargetRelabels ↔
      relabel = (P).gLocalV1IdentityRelabel ∨
      relabel = c25IdentitySplitSwapRelabel faceEdge0 faceEdge1 faceEdge2
        hfaceEdge0 hfaceEdge1 hfaceEdge2 := by
  rw [(P).mem_gLocalV1TargetRelabels_iff_valid]
  exact c25IdentitySplitTargetRelabelValid_iff faceEdge0 faceEdge1 faceEdge2
    hfaceEdge0 hfaceEdge1 hfaceEdge2 relabel

end IdentitySplitGeneric

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
def c25T3SwapRelabel : t3Presentation.GLocalV1TargetRelabel :=
  ⟨[0, 1], [1, 0, 2]⟩

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
theorem c25T3MemTargetRelabels_iff
    (relabel : t3Presentation.GLocalV1TargetRelabel) :
    relabel ∈ t3Presentation.gLocalV1TargetRelabels ↔
      relabel = t3Presentation.gLocalV1IdentityRelabel ∨
      relabel = c25T3SwapRelabel := by
  simpa [t3Presentation, c25T3SwapRelabel,
    c25IdentitySplitSwapRelabel] using
      (c25IdentitySplitMemTargetRelabels_iff
        t3FaceEdge0 t3FaceEdge1 t3FaceEdge2
        (by intro face; fin_cases face <;> decide)
        (by intro face; fin_cases face <;> decide)
        (by intro face; fin_cases face <;> decide) relabel)

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
def c25T6SwapRelabel : t6Presentation.GLocalV1TargetRelabel :=
  ⟨[0, 1], [1, 0, 2]⟩

/-- Raw identity-split relabel normalization for fixed GOAL claim (v)(a).

Position: fixture-family finite-table API; every premise comes from complete
target enumerations, permutation tables, and factor commutation, with no
supplied observation value, semantic label, or minimum certificate. -/
theorem c25T6MemTargetRelabels_iff
    (relabel : t6Presentation.GLocalV1TargetRelabel) :
    relabel ∈ t6Presentation.gLocalV1TargetRelabels ↔
      relabel = t6Presentation.gLocalV1IdentityRelabel ∨
      relabel = c25T6SwapRelabel := by
  simpa [t6Presentation, c25T6SwapRelabel,
    c25IdentitySplitSwapRelabel] using
      (c25IdentitySplitMemTargetRelabels_iff
        t6FaceEdge0 t6FaceEdge1 t6FaceEdge2
        (by intro face; fin_cases face <;> decide)
        (by intro face; fin_cases face <;> decide)
        (by intro face; fin_cases face <;> decide) relabel)

/-! ## Closed common observation and finite condition coordinates -/

/-- The whole-scope row in the closed T3/T6 structural normal form.

Position: closed normal-form component for fixed GOAL claim (v)(a).  Its
dependency cone contains only literal condition coordinates, the empty packet
list, and the complete rooted-ball histogram; it does not inspect either
presentation, `obsG`, a checker result, or a semantic label. -/
def commonWholeRecord : GLocalV1ScopeRecord GLocalV1WholeConditions :=
  ⟨⟨false, true, true⟩, [], commonFullBalls⟩

/-- The target-zero row in the closed T3/T6 structural normal form.

Position: closed normal-form component for fixed GOAL claim (v)(a), generated
only from literal condition coordinates, an empty packet list, and the
complete target-zero occurrence histogram. -/
def commonA0Record : GLocalV1ScopeRecord GLocalV1AConditions :=
  ⟨⟨false, false, true, false⟩, [], commonA0Balls⟩

/-- The target-one row in the closed T3/T6 structural normal form.

Position: closed normal-form component for fixed GOAL claim (v)(a), generated
only from literal condition coordinates, an empty packet list, and the
complete target-one occurrence histogram. -/
def commonA1Record : GLocalV1ScopeRecord GLocalV1AConditions :=
  ⟨⟨true, true, true, true⟩, [], commonA1Balls⟩

/-- The full-target row in the closed T3/T6 structural normal form.

Position: closed normal-form component for fixed GOAL claim (v)(a), generated
only from literal condition coordinates, an empty packet list, and the
complete full-scope occurrence histogram. -/
def commonFullRecord : GLocalV1ScopeRecord GLocalV1AConditions :=
  ⟨⟨true, true, true, true⟩, [], commonFullBalls⟩

/-- The presentation-independent closed observation normal form reached by T3
and T6.

Position: closed right-hand side for fixed GOAL claim (v)(a).  Its transitive
dependency cone contains only permanent observation constructors, literal
condition coordinates, empty packet lists, and complete raw rooted-ball
occurrence lists.  It contains no presentation identity, `obsG`, checker bit,
uniformity result, or semantic label. -/
def commonObservation : GLocalV1ObsValue :=
  ⟨⟨false, false, false, true, false, true, true⟩,
    commonWholeRecord,
    gLocalV1Histogram [commonA0Record, commonA1Record, commonFullRecord]⟩

/-- T3's executable full-target scope is the registered two-element full set.

Position: scope normal form for fixed GOAL claim (v)(a), derived from the
complete target enumeration and not from an observation or label. -/
theorem t3FullTargetSubset :
    t3Presentation.gLocalV1FullTargetSubset = targetFull := by
  rw [t3Presentation.gLocalV1FullTargetSubset_eq_univ]
  ext target
  fin_cases target <;> simp [targetFull]

/-- T6's executable full-target scope is the registered two-element full set.

Position: scope normal form for fixed GOAL claim (v)(a), derived from the
complete target enumeration and not from an observation or label. -/
theorem t6FullTargetSubset :
    t6Presentation.gLocalV1FullTargetSubset = targetFull := by
  rw [t6Presentation.gLocalV1FullTargetSubset_eq_univ]
  ext target
  fin_cases target <;> simp [targetFull]

/-- T3 enumerates exactly the three nonempty target scopes in executable order.

Position: finite scope normal form for fixed GOAL claim (v)(a).  It evaluates
the permanent exhaustive subset generator on the complete raw target list and
supplies no subset certificate, observation, or label. -/
theorem t3NonemptyTargetSubsets :
    t3Presentation.gLocalV1NonemptyTargetSubsets =
      [targetZero, targetOne, targetFull] := by
  rw [t3Presentation.gLocalV1NonemptyTargetSubsets_apply]
  simp [targetZero, targetOne, targetFull, t3Presentation,
    identitySplitPresentation]
  decide +kernel

/-- T6 enumerates exactly the three nonempty target scopes in executable order.

Position: finite scope normal form for fixed GOAL claim (v)(a).  It evaluates
the permanent exhaustive subset generator on the complete raw target list and
supplies no subset certificate, observation, or label. -/
theorem t6NonemptyTargetSubsets :
    t6Presentation.gLocalV1NonemptyTargetSubsets =
      [targetZero, targetOne, targetFull] := by
  rw [t6Presentation.gLocalV1NonemptyTargetSubsets_apply]
  simp [targetZero, targetOne, targetFull, t6Presentation,
    identitySplitPresentation]
  decide +kernel

/-- T3's packet-free whole-scope C0/C5/C6 coordinate normal form.

Position: independent T3 evaluation for fixed GOAL claim (v)(a).  The terminal
state is derived from raw packet emptiness and the tuple is kernel-computed
from the raw presentation; it is not a premise. -/
theorem t3WholeConditions :
    t3Presentation.gLocalV1WholeConditions targetFull =
      ⟨false, true, true⟩ := by
  rw [t3Presentation.gLocalV1WholeConditions_eq_initial_of_initial_packet_empty
    targetFull t3_targetFull_initial_packet_empty]
  decide +kernel

/-- T6's packet-free whole-scope C0/C5/C6 coordinate normal form.

Position: independent T6 evaluation for fixed GOAL claim (v)(a).  The terminal
state is derived from raw packet emptiness and the tuple is kernel-computed
from the raw presentation; it is not a premise. -/
theorem t6WholeConditions :
    t6Presentation.gLocalV1WholeConditions targetFull =
      ⟨false, true, true⟩ := by
  rw [t6Presentation.gLocalV1WholeConditions_eq_initial_of_initial_packet_empty
    targetFull t6_targetFull_initial_packet_empty]
  decide +kernel

/-- T3's packet-free target-zero C1--C4 coordinate normal form.

Position: independent T3 finite evaluation for fixed GOAL claim (v)(a), from
raw retained cells after the packet-empty fast path and with no expected vector
or semantic label as a premise. -/
theorem t3A0Conditions :
    t3Presentation.gLocalV1AConditions targetZero =
      ⟨false, false, true, false⟩ := by
  rw [t3Presentation.gLocalV1AConditions_eq_initial_of_initial_packet_empty
    targetZero t3_targetZero_initial_packet_empty]
  decide +kernel

/-- T3's packet-free target-one C1--C4 coordinate normal form.

Position: independent T3 finite evaluation for fixed GOAL claim (v)(a), from
raw retained cells after the packet-empty fast path and with no expected vector
or semantic label as a premise. -/
theorem t3A1Conditions :
    t3Presentation.gLocalV1AConditions targetOne =
      ⟨true, true, true, true⟩ := by
  rw [t3Presentation.gLocalV1AConditions_eq_initial_of_initial_packet_empty
    targetOne t3_targetOne_initial_packet_empty]
  decide +kernel

/-- T3's packet-free full-target C1--C4 coordinate normal form.

Position: independent T3 finite evaluation for fixed GOAL claim (v)(a), from
raw retained cells after the packet-empty fast path and with no expected vector
or semantic label as a premise. -/
theorem t3FullConditions :
    t3Presentation.gLocalV1AConditions targetFull =
      ⟨true, true, true, true⟩ := by
  rw [t3Presentation.gLocalV1AConditions_eq_initial_of_initial_packet_empty
    targetFull t3_targetFull_initial_packet_empty]
  decide +kernel

/-- T6's packet-free target-zero C1--C4 coordinate normal form.

Position: independent T6 finite evaluation for fixed GOAL claim (v)(a), from
raw retained cells after the packet-empty fast path and with no expected vector
or semantic label as a premise. -/
theorem t6A0Conditions :
    t6Presentation.gLocalV1AConditions targetZero =
      ⟨false, false, true, false⟩ := by
  rw [t6Presentation.gLocalV1AConditions_eq_initial_of_initial_packet_empty
    targetZero t6_targetZero_initial_packet_empty]
  decide +kernel

/-- T6's packet-free target-one C1--C4 coordinate normal form.

Position: independent T6 finite evaluation for fixed GOAL claim (v)(a), from
raw retained cells after the packet-empty fast path and with no expected vector
or semantic label as a premise. -/
theorem t6A1Conditions :
    t6Presentation.gLocalV1AConditions targetOne =
      ⟨true, true, true, true⟩ := by
  rw [t6Presentation.gLocalV1AConditions_eq_initial_of_initial_packet_empty
    targetOne t6_targetOne_initial_packet_empty]
  decide +kernel

/-- T6's packet-free full-target C1--C4 coordinate normal form.

Position: independent T6 finite evaluation for fixed GOAL claim (v)(a), from
raw retained cells after the packet-empty fast path and with no expected vector
or semantic label as a premise. -/
theorem t6FullConditions :
    t6Presentation.gLocalV1AConditions targetFull =
      ⟨true, true, true, true⟩ := by
  rw [t6Presentation.gLocalV1AConditions_eq_initial_of_initial_packet_empty
    targetFull t6_targetFull_initial_packet_empty]
  decide +kernel

/-- T3's aggregate seven-coordinate condition normal form.

Position: independent T3 coordinate assembly for fixed GOAL claim (v)(a),
using the owner equation plus all three computed subset rows and the computed
whole row; no aggregate vector is supplied as a premise. -/
theorem t3ConditionVector :
    t3Presentation.gLocalV1ConditionVector =
      ⟨false, false, false, true, false, true, true⟩ := by
  rw [t3Presentation.gLocalV1ConditionVector_apply,
    t3FullTargetSubset, t3NonemptyTargetSubsets, t3WholeConditions]
  simp [t3A0Conditions, t3A1Conditions, t3FullConditions]

/-- T6's aggregate seven-coordinate condition normal form.

Position: independent T6 coordinate assembly for fixed GOAL claim (v)(a),
using the owner equation plus all three computed subset rows and the computed
whole row; no aggregate vector is supplied as a premise. -/
theorem t6ConditionVector :
    t6Presentation.gLocalV1ConditionVector =
      ⟨false, false, false, true, false, true, true⟩ := by
  rw [t6Presentation.gLocalV1ConditionVector_apply,
    t6FullTargetSubset, t6NonemptyTargetSubsets, t6WholeConditions]
  simp [t6A0Conditions, t6A1Conditions, t6FullConditions]

/-- T3's all-path packet-kind union is empty at target zero.

Position: all-path component of fixed GOAL claim (v)(a), derived from raw
initial packet emptiness rather than a selected trace or supplied packet list. -/
theorem t3A0PacketKindUnion :
    t3Presentation.gLocalV1PacketKindUnion targetZero = [] :=
  t3Presentation.gLocalV1PacketKindUnion_eq_nil_of_initial_packet_empty
    targetZero t3_targetZero_initial_packet_empty

/-- T3's all-path packet-kind union is empty at target one.

Position: all-path component of fixed GOAL claim (v)(a), derived from raw
initial packet emptiness rather than a selected trace or supplied packet list. -/
theorem t3A1PacketKindUnion :
    t3Presentation.gLocalV1PacketKindUnion targetOne = [] :=
  t3Presentation.gLocalV1PacketKindUnion_eq_nil_of_initial_packet_empty
    targetOne t3_targetOne_initial_packet_empty

/-- T3's all-path packet-kind union is empty at the full target.

Position: all-path component of fixed GOAL claim (v)(a), derived from raw
initial packet emptiness rather than a selected trace or supplied packet list. -/
theorem t3FullPacketKindUnion :
    t3Presentation.gLocalV1PacketKindUnion targetFull = [] :=
  t3Presentation.gLocalV1PacketKindUnion_eq_nil_of_initial_packet_empty
    targetFull t3_targetFull_initial_packet_empty

/-- T6's all-path packet-kind union is empty at target zero.

Position: all-path component of fixed GOAL claim (v)(a), derived from raw
initial packet emptiness rather than a selected trace or supplied packet list. -/
theorem t6A0PacketKindUnion :
    t6Presentation.gLocalV1PacketKindUnion targetZero = [] :=
  t6Presentation.gLocalV1PacketKindUnion_eq_nil_of_initial_packet_empty
    targetZero t6_targetZero_initial_packet_empty

/-- T6's all-path packet-kind union is empty at target one.

Position: all-path component of fixed GOAL claim (v)(a), derived from raw
initial packet emptiness rather than a selected trace or supplied packet list. -/
theorem t6A1PacketKindUnion :
    t6Presentation.gLocalV1PacketKindUnion targetOne = [] :=
  t6Presentation.gLocalV1PacketKindUnion_eq_nil_of_initial_packet_empty
    targetOne t6_targetOne_initial_packet_empty

/-- T6's all-path packet-kind union is empty at the full target.

Position: all-path component of fixed GOAL claim (v)(a), derived from raw
initial packet emptiness rather than a selected trace or supplied packet list. -/
theorem t6FullPacketKindUnion :
    t6Presentation.gLocalV1PacketKindUnion targetFull = [] :=
  t6Presentation.gLocalV1PacketKindUnion_eq_nil_of_initial_packet_empty
    targetFull t6_targetFull_initial_packet_empty

/-- Embed a raw T3 fine target in the registered presentation type.

Position: fixture-local target alias for claim (v)(a); it carries only the
literal `Fin 3` target index and no relabel or observation result. -/
def t3FineTarget (target : Fin 3) : t3Presentation.FineTarget := by
  change Fin 3
  exact target

/-- Embed a raw T6 fine target in the registered presentation type.

Position: fixture-local target alias for claim (v)(a); it carries only the
literal `Fin 3` target index and no relabel or observation result. -/
def t6FineTarget (target : Fin 3) : t6Presentation.FineTarget := by
  change Fin 3
  exact target

/-! ## Relabel invariance of the complete cell-label data -/

/-- T3's canonical fine-target code is the literal registered target index.

Position: fixture-local code normalization for fixed GOAL claim (v)(a),
derived from the complete source-generated target enumeration alone. -/
theorem t3FineTargetCode (target : t3Presentation.FineTarget) :
    t3Presentation.fineTargetCode target = target.val := by
  rw [t3Presentation.fineTargetCode_apply]
  change ((List.finRange 3).map id).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- T3's canonical coarse-target code is its literal registered index.

Position: fixture-local code normalization for claim (v)(a), using only the
complete coarse-target enumeration. -/
theorem t3CoarseTargetCode (target : t3Presentation.CoarseTarget) :
    t3Presentation.coarseTargetCode target = target.val := by
  rw [t3Presentation.coarseTargetCode_apply]
  change (List.finRange 2).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- The identity relabel preserves every T3 fine-target code.

Position: finite relabel normalization for claim (v)(a), derived from the
owner identity equation and `t3FineTargetCode`. -/
theorem t3FineIdentityCode :
    t3Presentation.gLocalV1FineRelabelCode
        t3Presentation.gLocalV1IdentityRelabel = fun target => target.val := by
  funext target
  rw [t3Presentation.gLocalV1FineRelabelCode_identity]
  exact t3FineTargetCode target

/-- The nonidentity T3 relabel swaps codes zero and one and fixes code two.

Position: finite relabel normalization for claim (v)(a), evaluated from the
generated swap table rather than a supplied relabel certificate. -/
theorem t3FineSwapCode :
    t3Presentation.gLocalV1FineRelabelCode c25T3SwapRelabel =
      fun target => if target.val = 0 then 1 else if target.val = 1 then 0 else 2 := by
  funext target
  change Fin 3 at target
  fin_cases target <;>
    simp [c25T3SwapRelabel, t3Presentation.gLocalV1FineRelabelCode_mk,
      t3FineTargetCode]

/-- The T3 swap and identity relabels have the same coarse code table.

Position: factor-side relabel normalization for claim (v)(a); it uses the
literal coarse table and carries no observation coordinate. -/
theorem t3CoarseSwapCode :
    t3Presentation.gLocalV1CoarseRelabelCode c25T3SwapRelabel =
      t3Presentation.gLocalV1CoarseRelabelCode
        t3Presentation.gLocalV1IdentityRelabel := by
  funext target
  rw [t3Presentation.gLocalV1CoarseRelabelCode_identity]
  change Fin 2 at target
  fin_cases target <;>
    simp [c25T3SwapRelabel, t3Presentation.gLocalV1CoarseRelabelCode_mk,
      t3CoarseTargetCode]

/-- Every scoped T3 fine-chart support contains target zero exactly when it
contains target one.

Position: raw-support symmetry premise for the swap invariance part of claim
(v)(a), delegated to the registered fixture owner theorem. -/
theorem t3FineChartSupportSymmetric
    (A : Finset t3Presentation.CoarseTarget)
    (chart : t3Presentation.FineChart) :
    t3FineTarget 0 ∈ t3Presentation.gLocalV1FineChartSupport A chart ↔
      t3FineTarget 1 ∈ t3Presentation.gLocalV1FineChartSupport A chart :=
  t3_fineChartSupport_zero_iff_one A chart

/-- Every scoped T3 fine-edge support is invariant under exchanging targets
zero and one.

Position: raw edge-support consequence for claim (v)(a), obtained from the
owner support-intersection equation and chart symmetry only. -/
theorem t3FineEdgeSupportSymmetric
    (A : Finset t3Presentation.CoarseTarget)
    (edge : t3Presentation.FineEdge) :
    t3FineTarget 0 ∈ t3Presentation.gLocalV1FineEdgeSupport A edge ↔
      t3FineTarget 1 ∈ t3Presentation.gLocalV1FineEdgeSupport A edge := by
  rw [t3Presentation.gLocalV1FineEdgeSupport_apply]
  simp only [Finset.mem_inter]
  rw [t3FineChartSupportSymmetric, t3FineChartSupportSymmetric]

/-- Every scoped T3 fine-face support is invariant under exchanging targets
zero and one.

Position: raw face-support consequence for claim (v)(a), obtained from the
owner three-edge intersection equation and edge symmetry only. -/
theorem t3FineFaceSupportSymmetric
    (A : Finset t3Presentation.CoarseTarget)
    (face : t3Presentation.FineFace) :
    t3FineTarget 0 ∈ t3Presentation.gLocalV1FineFaceSupport A face ↔
      t3FineTarget 1 ∈ t3Presentation.gLocalV1FineFaceSupport A face := by
  rw [t3Presentation.gLocalV1FineFaceSupport_apply]
  simp only [Finset.mem_inter]
  rw [t3FineEdgeSupportSymmetric, t3FineEdgeSupportSymmetric,
    t3FineEdgeSupportSymmetric]

/-- A T3 fine support symmetric in targets zero and one has the same code
image under the swap and identity relabels.

Position: finite-set transport lemma for claim (v)(a); the sole material
premise is the stated raw support symmetry, not an expected label. -/
theorem t3FineCodeImageEq (support : Finset t3Presentation.FineTarget)
    (hsym : t3FineTarget 0 ∈ support ↔ t3FineTarget 1 ∈ support) :
    support.image (t3Presentation.gLocalV1FineRelabelCode c25T3SwapRelabel) =
      support.image (t3Presentation.gLocalV1FineRelabelCode
        t3Presentation.gLocalV1IdentityRelabel) := by
  rw [t3FineSwapCode, t3FineIdentityCode]
  ext code
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨target, htarget, rfl⟩
    change Fin 3 at target
    fin_cases target
    · exact ⟨t3FineTarget 1, hsym.mp htarget, by simp [t3FineTarget]⟩
    · exact ⟨t3FineTarget 0, hsym.mpr htarget, by simp [t3FineTarget]⟩
    · exact ⟨t3FineTarget 2, htarget, by simp [t3FineTarget]⟩
  · rintro ⟨target, htarget, rfl⟩
    change Fin 3 at target
    fin_cases target
    · exact ⟨t3FineTarget 1, hsym.mp htarget, by simp [t3FineTarget]⟩
    · exact ⟨t3FineTarget 0, hsym.mpr htarget, by simp [t3FineTarget]⟩
    · exact ⟨t3FineTarget 2, htarget, by simp [t3FineTarget]⟩

/-- Every T3 cell has the same support-code component under swap and identity.

Position: cell-label component theorem for claim (v)(a).  It case-splits only
the raw cell constructor and invokes definition-owner equations plus support
symmetry; no rooted-ball or observation result is supplied. -/
theorem t3CellSupportCodesSwapEq
    (A : Finset t3Presentation.CoarseTarget)
    (state : t3Presentation.GLocalV1V5State A)
    (cell : t3Presentation.GLocalV1Cell A state) :
    t3Presentation.gLocalV1CellSupportCodes A state c25T3SwapRelabel cell =
      t3Presentation.gLocalV1CellSupportCodes A state
        t3Presentation.gLocalV1IdentityRelabel cell := by
  cases cell <;> rename_i value
  all_goals rw [t3Presentation.gLocalV1CellSupportCodes_apply,
    t3Presentation.gLocalV1CellSupportCodes_apply]
  all_goals simp only
  all_goals try rw [t3CoarseSwapCode]
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t3FineCodeImageEq _ (t3FineChartSupportSymmetric A value))
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t3FineCodeImageEq _ (t3FineChartSupportSymmetric A value))
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t3FineCodeImageEq _ (t3FineEdgeSupportSymmetric A value))
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t3FineCodeImageEq _ (t3FineFaceSupportSymmetric A value))

/-- Every T3 cell has the same factor-image-code component under swap and
identity.

Position: cell-label component theorem for claim (v)(a), using only the
proved equality of the coarse relabel code tables. -/
theorem t3CellPiImageCodesSwapEq
    (A : Finset t3Presentation.CoarseTarget)
    (state : t3Presentation.GLocalV1V5State A)
    (cell : t3Presentation.GLocalV1Cell A state) :
    t3Presentation.gLocalV1CellPiImageCodes A state c25T3SwapRelabel cell =
      t3Presentation.gLocalV1CellPiImageCodes A state
        t3Presentation.gLocalV1IdentityRelabel cell := by
  cases cell <;> rename_i value <;>
    rw [t3Presentation.gLocalV1CellPiImageCodes_apply,
      t3Presentation.gLocalV1CellPiImageCodes_apply, t3CoarseSwapCode]

/-- Every T3 cell label is invariant under the only nonidentity valid relabel.

Position: pointwise relabel-invariance theorem for claim (v)(a), assembled
from independently proved support-code and factor-image-code equalities. -/
theorem t3CellLabelSwapEq (A : Finset t3Presentation.CoarseTarget)
    (state : t3Presentation.GLocalV1V5State A)
    (cell : t3Presentation.GLocalV1Cell A state) :
    t3Presentation.gLocalV1CellLabel A state c25T3SwapRelabel cell =
      t3Presentation.gLocalV1CellLabel A state
        t3Presentation.gLocalV1IdentityRelabel cell := by
  rw [t3Presentation.gLocalV1CellLabel_apply,
    t3Presentation.gLocalV1CellLabel_apply,
    t3CellSupportCodesSwapEq, t3CellPiImageCodesSwapEq]

/-- The complete T3 initial rooted-ball histogram is invariant under the fine
target swap for every target scope.

Position: orbit-invariance theorem for claim (v)(a), lifted by the owner
congruence API from pointwise equality of all generated retained-cell labels. -/
theorem t3InitialBallHistogramSwapEq
    (A : Finset t3Presentation.CoarseTarget) :
    t3Presentation.gLocalV1InitialBallHistogram A c25T3SwapRelabel =
      t3Presentation.gLocalV1InitialBallHistogram A
        t3Presentation.gLocalV1IdentityRelabel := by
  apply t3Presentation.gLocalV1InitialBallHistogram_eq_of_cellLabel_eq
  intro cell _
  exact t3CellLabelSwapEq A _ cell

/-- T6's canonical fine-target code is the literal registered target index.

Position: fixture-local code normalization for fixed GOAL claim (v)(a),
derived from the complete source-generated target enumeration alone. -/
theorem t6FineTargetCode (target : t6Presentation.FineTarget) :
    t6Presentation.fineTargetCode target = target.val := by
  rw [t6Presentation.fineTargetCode_apply]
  change ((List.finRange 3).map id).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- T6's canonical coarse-target code is its literal registered index.

Position: fixture-local code normalization for claim (v)(a), using only the
complete coarse-target enumeration. -/
theorem t6CoarseTargetCode (target : t6Presentation.CoarseTarget) :
    t6Presentation.coarseTargetCode target = target.val := by
  rw [t6Presentation.coarseTargetCode_apply]
  change (List.finRange 2).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- The identity relabel preserves every T6 fine-target code.

Position: finite relabel normalization for claim (v)(a), derived from the
owner identity equation and `t6FineTargetCode`. -/
theorem t6FineIdentityCode :
    t6Presentation.gLocalV1FineRelabelCode
        t6Presentation.gLocalV1IdentityRelabel = fun target => target.val := by
  funext target
  rw [t6Presentation.gLocalV1FineRelabelCode_identity]
  exact t6FineTargetCode target

/-- The nonidentity T6 relabel swaps codes zero and one and fixes code two.

Position: finite relabel normalization for claim (v)(a), evaluated from the
generated swap table rather than a supplied relabel certificate. -/
theorem t6FineSwapCode :
    t6Presentation.gLocalV1FineRelabelCode c25T6SwapRelabel =
      fun target => if target.val = 0 then 1 else if target.val = 1 then 0 else 2 := by
  funext target
  change Fin 3 at target
  fin_cases target <;>
    simp [c25T6SwapRelabel, t6Presentation.gLocalV1FineRelabelCode_mk,
      t6FineTargetCode]

/-- The T6 swap and identity relabels have the same coarse code table.

Position: factor-side relabel normalization for claim (v)(a); it uses the
literal coarse table and carries no observation coordinate. -/
theorem t6CoarseSwapCode :
    t6Presentation.gLocalV1CoarseRelabelCode c25T6SwapRelabel =
      t6Presentation.gLocalV1CoarseRelabelCode
        t6Presentation.gLocalV1IdentityRelabel := by
  funext target
  rw [t6Presentation.gLocalV1CoarseRelabelCode_identity]
  change Fin 2 at target
  fin_cases target <;>
    simp [c25T6SwapRelabel, t6Presentation.gLocalV1CoarseRelabelCode_mk,
      t6CoarseTargetCode]

/-- Every scoped T6 fine-chart support contains target zero exactly when it
contains target one.

Position: raw-support symmetry premise for the swap invariance part of claim
(v)(a), delegated to the registered fixture owner theorem. -/
theorem t6FineChartSupportSymmetric
    (A : Finset t6Presentation.CoarseTarget)
    (chart : t6Presentation.FineChart) :
    t6FineTarget 0 ∈ t6Presentation.gLocalV1FineChartSupport A chart ↔
      t6FineTarget 1 ∈ t6Presentation.gLocalV1FineChartSupport A chart :=
  t6_fineChartSupport_zero_iff_one A chart

/-- Every scoped T6 fine-edge support is invariant under exchanging targets
zero and one.

Position: raw edge-support consequence for claim (v)(a), obtained from the
owner support-intersection equation and chart symmetry only. -/
theorem t6FineEdgeSupportSymmetric
    (A : Finset t6Presentation.CoarseTarget)
    (edge : t6Presentation.FineEdge) :
    t6FineTarget 0 ∈ t6Presentation.gLocalV1FineEdgeSupport A edge ↔
      t6FineTarget 1 ∈ t6Presentation.gLocalV1FineEdgeSupport A edge := by
  rw [t6Presentation.gLocalV1FineEdgeSupport_apply]
  simp only [Finset.mem_inter]
  rw [t6FineChartSupportSymmetric, t6FineChartSupportSymmetric]

/-- Every scoped T6 fine-face support is invariant under exchanging targets
zero and one.

Position: raw face-support consequence for claim (v)(a), obtained from the
owner three-edge intersection equation and edge symmetry only. -/
theorem t6FineFaceSupportSymmetric
    (A : Finset t6Presentation.CoarseTarget)
    (face : t6Presentation.FineFace) :
    t6FineTarget 0 ∈ t6Presentation.gLocalV1FineFaceSupport A face ↔
      t6FineTarget 1 ∈ t6Presentation.gLocalV1FineFaceSupport A face := by
  rw [t6Presentation.gLocalV1FineFaceSupport_apply]
  simp only [Finset.mem_inter]
  rw [t6FineEdgeSupportSymmetric, t6FineEdgeSupportSymmetric,
    t6FineEdgeSupportSymmetric]

/-- A T6 fine support symmetric in targets zero and one has the same code
image under the swap and identity relabels.

Position: finite-set transport lemma for claim (v)(a); the sole material
premise is the stated raw support symmetry, not an expected label. -/
theorem t6FineCodeImageEq (support : Finset t6Presentation.FineTarget)
    (hsym : t6FineTarget 0 ∈ support ↔ t6FineTarget 1 ∈ support) :
    support.image (t6Presentation.gLocalV1FineRelabelCode c25T6SwapRelabel) =
      support.image (t6Presentation.gLocalV1FineRelabelCode
        t6Presentation.gLocalV1IdentityRelabel) := by
  rw [t6FineSwapCode, t6FineIdentityCode]
  ext code
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨target, htarget, rfl⟩
    change Fin 3 at target
    fin_cases target
    · exact ⟨t6FineTarget 1, hsym.mp htarget, by simp [t6FineTarget]⟩
    · exact ⟨t6FineTarget 0, hsym.mpr htarget, by simp [t6FineTarget]⟩
    · exact ⟨t6FineTarget 2, htarget, by simp [t6FineTarget]⟩
  · rintro ⟨target, htarget, rfl⟩
    change Fin 3 at target
    fin_cases target
    · exact ⟨t6FineTarget 1, hsym.mp htarget, by simp [t6FineTarget]⟩
    · exact ⟨t6FineTarget 0, hsym.mpr htarget, by simp [t6FineTarget]⟩
    · exact ⟨t6FineTarget 2, htarget, by simp [t6FineTarget]⟩

/-- Every T6 cell has the same support-code component under swap and identity.

Position: cell-label component theorem for claim (v)(a).  It case-splits only
the raw cell constructor and invokes definition-owner equations plus support
symmetry; no rooted-ball or observation result is supplied. -/
theorem t6CellSupportCodesSwapEq
    (A : Finset t6Presentation.CoarseTarget)
    (state : t6Presentation.GLocalV1V5State A)
    (cell : t6Presentation.GLocalV1Cell A state) :
    t6Presentation.gLocalV1CellSupportCodes A state c25T6SwapRelabel cell =
      t6Presentation.gLocalV1CellSupportCodes A state
        t6Presentation.gLocalV1IdentityRelabel cell := by
  cases cell <;> rename_i value
  all_goals rw [t6Presentation.gLocalV1CellSupportCodes_apply,
    t6Presentation.gLocalV1CellSupportCodes_apply]
  all_goals simp only
  all_goals try rw [t6CoarseSwapCode]
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t6FineCodeImageEq _ (t6FineChartSupportSymmetric A value))
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t6FineCodeImageEq _ (t6FineChartSupportSymmetric A value))
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t6FineCodeImageEq _ (t6FineEdgeSupportSymmetric A value))
  · exact congrArg (fun values : Finset Nat => values.sort (· ≤ ·))
      (t6FineCodeImageEq _ (t6FineFaceSupportSymmetric A value))

/-- Every T6 cell has the same factor-image-code component under swap and
identity.

Position: cell-label component theorem for claim (v)(a), using only the
proved equality of the coarse relabel code tables. -/
theorem t6CellPiImageCodesSwapEq
    (A : Finset t6Presentation.CoarseTarget)
    (state : t6Presentation.GLocalV1V5State A)
    (cell : t6Presentation.GLocalV1Cell A state) :
    t6Presentation.gLocalV1CellPiImageCodes A state c25T6SwapRelabel cell =
      t6Presentation.gLocalV1CellPiImageCodes A state
        t6Presentation.gLocalV1IdentityRelabel cell := by
  cases cell <;> rename_i value <;>
    rw [t6Presentation.gLocalV1CellPiImageCodes_apply,
      t6Presentation.gLocalV1CellPiImageCodes_apply, t6CoarseSwapCode]

/-- Every T6 cell label is invariant under the only nonidentity valid relabel.

Position: pointwise relabel-invariance theorem for claim (v)(a), assembled
from independently proved support-code and factor-image-code equalities. -/
theorem t6CellLabelSwapEq (A : Finset t6Presentation.CoarseTarget)
    (state : t6Presentation.GLocalV1V5State A)
    (cell : t6Presentation.GLocalV1Cell A state) :
    t6Presentation.gLocalV1CellLabel A state c25T6SwapRelabel cell =
      t6Presentation.gLocalV1CellLabel A state
        t6Presentation.gLocalV1IdentityRelabel cell := by
  rw [t6Presentation.gLocalV1CellLabel_apply,
    t6Presentation.gLocalV1CellLabel_apply,
    t6CellSupportCodesSwapEq, t6CellPiImageCodesSwapEq]

/-- The complete T6 initial rooted-ball histogram is invariant under the fine
target swap for every target scope.

Position: orbit-invariance theorem for claim (v)(a), lifted by the owner
congruence API from pointwise equality of all generated retained-cell labels. -/
theorem t6InitialBallHistogramSwapEq
    (A : Finset t6Presentation.CoarseTarget) :
    t6Presentation.gLocalV1InitialBallHistogram A c25T6SwapRelabel =
      t6Presentation.gLocalV1InitialBallHistogram A
        t6Presentation.gLocalV1IdentityRelabel := by
  apply t6Presentation.gLocalV1InitialBallHistogram_eq_of_cellLabel_eq
  intro cell _
  exact t6CellLabelSwapEq A _ cell

/-- Embed a raw `Fin 2` chart index in T6's coarse chart type.

Position: fixture-local raw-index bridge; its provenance is the registered T6
chart enumeration and it supplies no observation result or certificate. -/
private def t6C25CoarseChart (chart : Fin 2) :
    t6Presentation.CoarseChart := chart

/-- Embed a raw `Fin 7` edge index in T6's coarse edge type.

Position: fixture-local raw-index bridge; its provenance is the registered T6
edge enumeration and it supplies no observation result or certificate. -/
private def t6C25CoarseEdge (edge : Fin 7) :
    t6Presentation.CoarseEdge := edge

/-- Embed a raw `Fin 6` face index in T6's coarse face type.

Position: fixture-local raw-index bridge; its provenance is the registered T6
face enumeration and it supplies no observation result or certificate. -/
private def t6C25CoarseFace (face : Fin 6) :
    t6Presentation.CoarseFace := face

/-- Embed a raw `Fin 2` chart index in T6's fine chart type.

Position: fixture-local raw-index bridge; its provenance is the registered T6
fine chart enumeration and it supplies no observation result or certificate. -/
private def t6C25FineChart (chart : Fin 2) :
    t6Presentation.FineChart := chart

/-- Embed a raw `Fin 7` edge index in T6's fine edge type.

Position: fixture-local raw-index bridge; its provenance is the registered T6
fine edge enumeration and it supplies no observation result or certificate. -/
private def t6C25FineEdge (edge : Fin 7) :
    t6Presentation.FineEdge := edge

/-- Embed a raw `Fin 6` face index in T6's fine face type.

Position: fixture-local raw-index bridge; its provenance is the registered T6
fine face enumeration and it supplies no observation result or certificate. -/
private def t6C25FineFace (face : Fin 6) :
    t6Presentation.FineFace := face

/-- Embed a raw `Fin 3` target index in T6's fine target type.

Position: fixture-local raw-index bridge; its provenance is the registered T6
fine target enumeration and it supplies no observation result or certificate. -/
private def t6C25FineTarget (target : Fin 3) :
    t6Presentation.FineTarget := target

/-- Evaluate the identity code of every registered T6 coarse target.

Position: fixture-local raw-enumeration theorem; its premise is only the target
index and its provenance is `coarseTargetEntries`, not an observation value. -/
@[simp] theorem t6C25CoarseTargetCode
    (target : t6Presentation.CoarseTarget) :
    t6Presentation.coarseTargetCode target = target.val := by
  change (List.finRange 2).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- Evaluate the identity code of every registered T6 fine target.

Position: fixture-local raw-enumeration theorem; its premise is only the target
index and its provenance is `fineTargetEntries`, not an observation value. -/
@[simp] theorem t6C25FineTargetCode
    (target : t6Presentation.FineTarget) :
    t6Presentation.fineTargetCode target = target.val := by
  change ((List.finRange 3).map id).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- Compute the fine targets lying over T6 target zero.

Position: fixture-local scope theorem; its raw provenance is the registered
reading and computed-factor API, with no supplied scope or observation row. -/
theorem t6C25FineScopeA0 :
    t6Presentation.gLocalV1FineScopeTargets targetZero =
      {t6C25FineTarget 0, t6C25FineTarget 1} := by
  rw [t6Presentation.gLocalV1FineScopeTargets_apply]
  ext target
  fin_cases target <;>
    simp +decide

/-- Compute the fine targets lying over T6 target one.

Position: fixture-local scope theorem; its raw provenance is the registered
reading and computed-factor API, with no supplied scope or observation row. -/
theorem t6C25FineScopeA1 :
    t6Presentation.gLocalV1FineScopeTargets targetOne =
      {t6C25FineTarget 2} := by
  rw [t6Presentation.gLocalV1FineScopeTargets_apply]
  ext target
  fin_cases target <;>
    simp +decide

/-- Compute the fine targets lying over the full T6 target set.

Position: fixture-local scope theorem; its raw provenance is the registered
reading and computed-factor API, with no supplied scope or observation row. -/
theorem t6C25FineScopeFull :
    t6Presentation.gLocalV1FineScopeTargets targetFull = Finset.univ := by
  rw [t6Presentation.gLocalV1FineScopeTargets_apply]
  ext target
  fin_cases target <;>
    simp +decide

/-- Normalize T6's fine identity-relabel code function pointwise.

Position: fixture-local relabel theorem; its raw premise is the identity
relabel and target enumeration, and it carries no computed observation. -/
theorem t6C25FineIdentityCodeFun :
    t6Presentation.gLocalV1FineRelabelCode
        t6Presentation.gLocalV1IdentityRelabel =
      fun target => target.val := by
  funext target
  rw [t6Presentation.gLocalV1FineRelabelCode_identity]
  exact t6C25FineTargetCode target

/-- Normalize T6's coarse identity-relabel code function pointwise.

Position: fixture-local relabel theorem; its raw premise is the identity
relabel and target enumeration, and it carries no computed observation. -/
theorem t6C25CoarseIdentityCodeFun :
    t6Presentation.gLocalV1CoarseRelabelCode
        t6Presentation.gLocalV1IdentityRelabel =
      fun target => target.val := by
  funext target
  rw [t6Presentation.gLocalV1CoarseRelabelCode_identity]
  exact t6C25CoarseTargetCode target

/-- Sort the closed natural-number support pair used by the T6 fixture.

Position: presentation-independent finite-list normalization; its raw premise
is the literal finset `{0, 1}` and it contains no observation datum. -/
theorem t6C25Sort01Nat :
    ({0, 1} : Finset Nat).sort (· ≤ ·) = [0, 1] := by
  rw [Finset.sort_insert (r := (· ≤ ·)) (by simp) (by simp)]
  simp

/-- Compute the complete retained T6 cell list at target zero.

Position: fixture-local owner-boundary theorem; its raw provenance is the
registered T6 tables and initial-state cell-list equation, not a supplied list. -/
theorem t6C25CellListA0 :
    t6Presentation.gLocalV1CellList targetZero
      (t6Presentation.gLocalV1InitialState targetZero) =
    [.coarseChart (t6C25CoarseChart 0),
     .coarseVertex (t6C25CoarseChart 0),
     .coarseChart (t6C25CoarseChart 1),
     .coarseVertex (t6C25CoarseChart 1),
     .coarseEdge (t6C25CoarseEdge 0),
     .coarseEdge (t6C25CoarseEdge 1),
     .coarseEdge (t6C25CoarseEdge 2),
     .coarseEdge (t6C25CoarseEdge 3),
     .coarseEdge (t6C25CoarseEdge 4),
     .coarseEdge (t6C25CoarseEdge 5),
     .coarseEdge (t6C25CoarseEdge 6),
     .coarseFace (t6C25CoarseFace 0),
     .coarseFace (t6C25CoarseFace 1),
     .coarseFace (t6C25CoarseFace 2),
     .coarseFace (t6C25CoarseFace 3),
     .coarseFace (t6C25CoarseFace 4),
     .coarseFace (t6C25CoarseFace 5),
     .fineChart (t6C25FineChart 0),
     .fineVertex (t6C25FineChart 0),
     .fineEdge (t6C25FineEdge 0)] := by
  rw [t6Presentation.gLocalV1CellList_apply]
  decide +kernel

/-- Compute the complete retained T6 cell list at target one.

Position: fixture-local owner-boundary theorem; its raw provenance is the
registered T6 tables and initial-state cell-list equation, not a supplied list. -/
theorem t6C25CellListA1 :
    t6Presentation.gLocalV1CellList targetOne
      (t6Presentation.gLocalV1InitialState targetOne) =
    [.coarseChart (t6C25CoarseChart 1),
     .coarseVertex (t6C25CoarseChart 1),
     .coarseEdge (t6C25CoarseEdge 1),
     .coarseEdge (t6C25CoarseEdge 2),
     .coarseEdge (t6C25CoarseEdge 3),
     .coarseEdge (t6C25CoarseEdge 4),
     .coarseEdge (t6C25CoarseEdge 5),
     .coarseEdge (t6C25CoarseEdge 6),
     .coarseFace (t6C25CoarseFace 0),
     .coarseFace (t6C25CoarseFace 1),
     .coarseFace (t6C25CoarseFace 2),
     .coarseFace (t6C25CoarseFace 3),
     .coarseFace (t6C25CoarseFace 4),
     .coarseFace (t6C25CoarseFace 5),
     .fineChart (t6C25FineChart 1),
     .fineVertex (t6C25FineChart 1),
     .fineEdge (t6C25FineEdge 1),
     .fineEdge (t6C25FineEdge 2),
     .fineEdge (t6C25FineEdge 3),
     .fineEdge (t6C25FineEdge 4),
     .fineEdge (t6C25FineEdge 5),
     .fineEdge (t6C25FineEdge 6),
     .fineFace (t6C25FineFace 0),
     .fineFace (t6C25FineFace 1),
     .fineFace (t6C25FineFace 2),
     .fineFace (t6C25FineFace 3),
     .fineFace (t6C25FineFace 4),
     .fineFace (t6C25FineFace 5)] := by
  rw [t6Presentation.gLocalV1CellList_apply]
  decide +kernel

/-- Compute the complete retained T6 cell list at full target scope.

Position: fixture-local owner-boundary theorem; its raw provenance is the
registered T6 tables and initial-state cell-list equation, not a supplied list. -/
theorem t6C25CellListFull :
    t6Presentation.gLocalV1CellList targetFull
      (t6Presentation.gLocalV1InitialState targetFull) =
    [.coarseChart (t6C25CoarseChart 0),
     .coarseVertex (t6C25CoarseChart 0),
     .coarseChart (t6C25CoarseChart 1),
     .coarseVertex (t6C25CoarseChart 1),
     .coarseEdge (t6C25CoarseEdge 0),
     .coarseEdge (t6C25CoarseEdge 1),
     .coarseEdge (t6C25CoarseEdge 2),
     .coarseEdge (t6C25CoarseEdge 3),
     .coarseEdge (t6C25CoarseEdge 4),
     .coarseEdge (t6C25CoarseEdge 5),
     .coarseEdge (t6C25CoarseEdge 6),
     .coarseFace (t6C25CoarseFace 0),
     .coarseFace (t6C25CoarseFace 1),
     .coarseFace (t6C25CoarseFace 2),
     .coarseFace (t6C25CoarseFace 3),
     .coarseFace (t6C25CoarseFace 4),
     .coarseFace (t6C25CoarseFace 5),
     .fineChart (t6C25FineChart 0),
     .fineVertex (t6C25FineChart 0),
     .fineChart (t6C25FineChart 1),
     .fineVertex (t6C25FineChart 1),
     .fineEdge (t6C25FineEdge 0),
     .fineEdge (t6C25FineEdge 1),
     .fineEdge (t6C25FineEdge 2),
     .fineEdge (t6C25FineEdge 3),
     .fineEdge (t6C25FineEdge 4),
     .fineEdge (t6C25FineEdge 5),
     .fineEdge (t6C25FineEdge 6),
     .fineFace (t6C25FineFace 0),
     .fineFace (t6C25FineFace 1),
     .fineFace (t6C25FineFace 2),
     .fineFace (t6C25FineFace 3),
     .fineFace (t6C25FineFace 4),
     .fineFace (t6C25FineFace 5)] := by
  rw [t6Presentation.gLocalV1CellList_apply]
  decide +kernel

/-- Every registered T6 coarse edge is a self-loop.

Position: fixture-local incidence theorem; its raw provenance is the registered
endpoint table and it supplies no criticality, flag, or observation result. -/
theorem t6C25CoarseSelfLoop
    (edge : t6Presentation.CoarseEdge) :
    t6Presentation.coarseEdgeLeft edge =
      t6Presentation.coarseEdgeRight edge := by
  fin_cases edge <;>
    simp [t6Presentation, identitySplitPresentation, edgeChart]

/-- Every registered T6 fine edge is a self-loop.

Position: fixture-local incidence theorem; its raw provenance is the registered
endpoint table and it supplies no criticality, flag, or observation result. -/
theorem t6C25FineSelfLoop
    (edge : t6Presentation.FineEdge) :
    t6Presentation.fineEdgeLeft edge =
      t6Presentation.fineEdgeRight edge := by
  fin_cases edge <;>
    simp [t6Presentation, identitySplitPresentation, edgeChart]

/-- Compute the T6 fine-to-coarse map on every registered edge index.

Position: fixture-local map theorem; its raw provenance is the registered
partial edge map and it supplies no map-status label or observation result. -/
theorem t6C25EdgeMap (edge : Fin 7) :
    t6Presentation.edgeMap (t6C25FineEdge edge) =
      some (t6C25CoarseEdge edge) := by
  fin_cases edge <;>
    simp [t6Presentation, identitySplitPresentation,
      t6C25FineEdge, t6C25CoarseEdge]

/-- T6's fine FaceTwin key is injective at every coarse target scope.

Position: fixture-local raw-face theorem; its provenance is the registered
face-edge table, with no supplied twin flag, face class, or observation. -/
theorem t6C25FineFaceKeyInjective (A : Finset (Fin 2)) :
    Function.Injective (t6Presentation.gLocalV1FineFaceKey A) := by
  intro left right hequal
  have hedge : t6Presentation.fineFaceEdge0 left =
      t6Presentation.fineFaceEdge0 right :=
    congrArg GLocalV1FineFaceTwinKey.edge0 hequal
  fin_cases left <;> fin_cases right <;>
    simp [t6Presentation, identitySplitPresentation, t6FaceEdge0] at hedge ⊢

/-- Normalize the flag row of any retained T6 coarse edge.

Position: fixture-local flag theorem; its raw premises are edge retention and
the self-loop table, discharged through owner critical/guard/bridge APIs. -/
theorem t6C25CoarseEdgeFlags
    {A : Finset t6Presentation.CoarseTarget}
    (edge : t6Presentation.CoarseEdge)
    (hmem : edge ∈ (t6Presentation.gLocalV1InitialState A).coarseEdges) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.coarseEdge edge) =
      handFlags .coarse .edge := by
  have hcritical :=
    t6Presentation.mem_gLocalV1CoarseCriticalEdges_of_mem_of_selfLoop
      A _ edge hmem (t6C25CoarseSelfLoop edge)
  have hguard :=
    t6Presentation.mem_gLocalV1GuardedCoarseEdges_of_mem_critical
      A _ edge hcritical
  have hnbridge :=
    t6Presentation.not_mem_gLocalV1CoarseBridges_of_selfLoop
      A (t6Presentation.gLocalV1InitialState A) edge
      (t6C25CoarseSelfLoop edge)
  rw [t6Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical, hguard, hnbridge,
    t6C25CoarseSelfLoop]

/-- Normalize the flag row of any retained T6 fine edge.

Position: fixture-local flag theorem; its raw premises are edge retention and
the self-loop table, discharged through owner critical/bridge APIs. -/
theorem t6C25FineEdgeFlags
    {A : Finset t6Presentation.CoarseTarget}
    (edge : t6Presentation.FineEdge)
    (hmem : edge ∈ (t6Presentation.gLocalV1InitialState A).fineEdges) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.fineEdge edge) =
      handFlags .fine .edge := by
  have hcritical :=
    t6Presentation.mem_gLocalV1FineCriticalEdges_of_mem_of_selfLoop
      A _ edge hmem (t6C25FineSelfLoop edge)
  have hnbridge :=
    t6Presentation.not_mem_gLocalV1FineBridges_of_selfLoop
      A (t6Presentation.gLocalV1InitialState A) edge
      (t6C25FineSelfLoop edge)
  rw [t6Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical, hnbridge, t6C25FineSelfLoop]

/-- Normalize the flag row of a retained T6 coarse-edge endpoint vertex.

Position: fixture-local flag theorem; its raw premises are edge retention and
endpoint incidence, discharged through the owner critical-vertex API. -/
theorem t6C25CoarseVertexFlags
    {A : Finset t6Presentation.CoarseTarget}
    (chart : t6Presentation.CoarseChart)
    (edge : t6Presentation.CoarseEdge)
    (hmem : edge ∈ (t6Presentation.gLocalV1InitialState A).coarseEdges)
    (hendpoint : chart = t6Presentation.coarseEdgeLeft edge ∨
      chart = t6Presentation.coarseEdgeRight edge) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.coarseVertex chart) =
      handFlags .coarse .vertex := by
  have hcriticalEdge :=
    t6Presentation.mem_gLocalV1CoarseCriticalEdges_of_mem_of_selfLoop
      A _ edge hmem (t6C25CoarseSelfLoop edge)
  have hcritical :=
    t6Presentation.mem_gLocalV1CoarseCriticalVertices_of_criticalEdge_endpoint
      A _ edge chart hcriticalEdge hendpoint
  rw [t6Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical]

/-- Normalize the flag row of a mapped retained T6 fine-edge endpoint vertex.

Position: fixture-local flag theorem; its raw premises are fine/coarse edge
retention, the edge map, and endpoint incidence, not a supplied flag row. -/
theorem t6C25FineVertexFlags
    {A : Finset t6Presentation.CoarseTarget}
    (chart : t6Presentation.FineChart) (edge : Fin 7)
    (hfine : t6C25FineEdge edge ∈
      (t6Presentation.gLocalV1InitialState A).fineEdges)
    (hcoarse : t6C25CoarseEdge edge ∈
      (t6Presentation.gLocalV1InitialState A).coarseEdges)
    (hendpoint : chart =
        t6Presentation.fineEdgeLeft (t6C25FineEdge edge) ∨
      chart = t6Presentation.fineEdgeRight (t6C25FineEdge edge)) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.fineVertex chart) =
      handFlags .fine .vertex := by
  have hfineCritical :=
    t6Presentation.mem_gLocalV1FineCriticalEdges_of_mem_of_selfLoop
      A _ _ hfine (t6C25FineSelfLoop _)
  have hcritical :=
    t6Presentation.mem_gLocalV1FineCriticalVertices_of_criticalEdge_endpoint
      A _ _ chart hfineCritical hendpoint
  have hcoarseCritical :=
    t6Presentation.mem_gLocalV1CoarseCriticalEdges_of_mem_of_selfLoop
      A _ _ hcoarse (t6C25CoarseSelfLoop _)
  have hactive :=
    t6Presentation.mem_gLocalV1ActiveFineVertices_of_mapped_criticalEdge_endpoint
      A _ (t6C25FineEdge edge) (t6C25CoarseEdge edge) chart
      hfine hcoarseCritical (t6C25EdgeMap edge) hendpoint
  rw [t6Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical, hactive]

/-- Normalize the flag row of every T6 coarse face.

Position: fixture-local flag theorem; its raw provenance is coarse FaceTwin-key
injectivity and the owner twin-flag equation, not an expected observation. -/
theorem t6C25CoarseFaceFlags
    {A : Finset t6Presentation.CoarseTarget}
    (face : t6Presentation.CoarseFace) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.coarseFace face) =
      handFlags .coarse .face := by
  have htwin :=
    t6Presentation.gLocalV1CoarseFaceTwinFlag_eq_false_of_key_injective
      A face (t6_faceKey_injective A)
  rw [t6Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, htwin]

/-- Normalize the flag row of every T6 fine face.

Position: fixture-local flag theorem; its raw provenance is fine FaceTwin-key
injectivity and the owner twin-flag equation, not an expected observation. -/
theorem t6C25FineFaceFlags
    {A : Finset t6Presentation.CoarseTarget}
    (face : t6Presentation.FineFace) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.fineFace face) =
      handFlags .fine .face := by
  have htwin :=
    t6Presentation.gLocalV1FineFaceTwinFlag_eq_false_of_key_injective
      A face (t6C25FineFaceKeyInjective A)
  rw [t6Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, htwin]

/-- Normalize the structurally empty flag row of every T6 coarse chart.

Position: fixture-local flag theorem; its raw provenance is the cell-flags
owner equation and the chart constructor, with no supplied flag certificate. -/
theorem t6C25CoarseChartFlags
    {A : Finset t6Presentation.CoarseTarget}
    (chart : t6Presentation.CoarseChart) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.coarseChart chart) =
      handFlags .coarse .chart := by
  rw [t6Presentation.gLocalV1CellFlags_apply]
  rfl

/-- Normalize the structurally empty flag row of every T6 fine chart.

Position: fixture-local flag theorem; its raw provenance is the cell-flags
owner equation and the chart constructor, with no supplied flag certificate. -/
theorem t6C25FineChartFlags
    {A : Finset t6Presentation.CoarseTarget}
    (chart : t6Presentation.FineChart) :
    t6Presentation.gLocalV1CellFlags A
        (t6Presentation.gLocalV1InitialState A) (.fineChart chart) =
      handFlags .fine .chart := by
  rw [t6Presentation.gLocalV1CellFlags_apply]
  rfl

/-- Closed per-cell rooted-ball normal form for T6 target zero.

Position: fixture-local normal-form constructor; its raw provenance is the
registered anchor/neutral roles and literal support codes, not an `obsG` field. -/
private def t6C25ExpectedA0Ball :
    t6Presentation.GLocalV1Cell targetZero
      (t6Presentation.gLocalV1InitialState targetZero) → GLocalV1RootedBall
  | .coarseChart chart => if chart = t6C25CoarseChart 0 then
      handAnchorChartBall .coarse [0] [0]
    else handNeutralChartBall .coarse [0] [0]
  | .coarseVertex chart => if chart = t6C25CoarseChart 0 then
      handAnchorVertexBall .coarse [0] [0]
    else handNeutralVertexBall .coarse [0] [0]
  | .coarseEdge edge => if edge = t6C25CoarseEdge 0 then
      handAnchorEdgeBall .coarse [0] [0]
    else handNeutralEdgeBall .coarse [0] [0]
  | .coarseFace _ => handNeutralFaceBall .coarse [0] [0]
  | .fineChart _ => handAnchorChartBall .fine [0, 1] [0]
  | .fineVertex _ => handAnchorVertexBall .fine [0, 1] [0]
  | .fineEdge _ => handAnchorEdgeBall .fine [0, 1] [0]
  | .fineFace _ => handNeutralFaceBall .fine [] []

set_option maxHeartbeats 20000000 in
/-- Evaluate the root label of every retained T6 target-zero cell.

Position: fixture-local member-aware theorem; its raw premises are the complete
cell list, support/map tables, and owner flag APIs, not a supplied label. -/
theorem t6C25A0RootLabel
    (root : t6Presentation.GLocalV1Cell targetZero
      (t6Presentation.gLocalV1InitialState targetZero))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetZero
      (t6Presentation.gLocalV1InitialState targetZero)) :
    t6Presentation.gLocalV1CellLabel targetZero
        (t6Presentation.gLocalV1InitialState targetZero)
        t6Presentation.gLocalV1IdentityRelabel root =
      (t6C25ExpectedA0Ball root).rootLabel := by
  rw [t6C25CellListA0] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq,
    t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
    t6C25FineChart, t6C25FineEdge,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t6Presentation.gLocalV1CellLabel_apply,
      t6Presentation.gLocalV1CellSide_apply,
      t6Presentation.gLocalV1CellType_apply,
      t6Presentation.gLocalV1CellSupportCodes_apply,
      t6Presentation.gLocalV1CellPiImageCodes_apply,
      t6Presentation.gLocalV1CellMapStatus_apply]
  all_goals try rw [t6C25CoarseChartFlags]
  all_goals try rw [t6C25FineChartFlags]
  all_goals try rw [t6C25CoarseVertexFlags _ (t6C25CoarseEdge 0)
    (by decide +kernel) (by left; rfl)]
  all_goals try rw [t6C25CoarseVertexFlags _ (t6C25CoarseEdge 1)
    (by decide +kernel) (by
      left
      simp [t6Presentation, identitySplitPresentation, edgeChart,
        t6C25CoarseEdge])]
  all_goals try rw [t6C25FineVertexFlags _ 0
    (by decide +kernel) (by decide +kernel) (by left; rfl)]
  all_goals try rw [t6C25CoarseEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t6C25FineEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t6C25CoarseFaceFlags]
  all_goals
    simp only [t6Presentation.gLocalV1CoarseChartSupport_apply,
      t6Presentation.gLocalV1FineChartSupport_apply,
      t6Presentation.gLocalV1CoarseEdgeSupport_apply,
      t6Presentation.gLocalV1FineEdgeSupport_apply,
      t6Presentation.gLocalV1CoarseFaceSupport_apply]
  all_goals try rw [t6C25FineScopeA0]
  all_goals try rw [t6C25CoarseIdentityCodeFun]
  all_goals try rw [t6C25FineIdentityCodeFun]
  all_goals try simp only [t6_computedFactor_apply]
  all_goals
    simp +decide (config := { maxSteps := 5000000 })
      [t6C25ExpectedA0Ball, handAnchorChartBall,
        handNeutralChartBall, handAnchorVertexBall,
        handNeutralVertexBall, handAnchorEdgeBall,
        handNeutralEdgeBall, handNeutralFaceBall,
        handBall, handLabel, t6Presentation, identitySplitPresentation,
        targetZero, coarseRead, coarseChartSupport, fineChartSupport,
        edgeChart, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2,
        t6C25CoarseChart, t6C25CoarseEdge,
        t6C25FineTarget, t6C25Sort01Nat]

/-- Clip six alternating neutral edge-stub pairs to two copies per slot.

Position: presentation-independent histogram theorem; its raw premise is the
literal stub occurrence list and its provenance is permutation plus clip-two. -/
theorem t6C25NeutralStubHistogramSixEqTwo :
    gLocalV1Histogram
        ([⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram
        ([⟨.edge, .slot0⟩, ⟨.edge, .slot0⟩,
          ⟨.edge, .slot1⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) := by
  let zero : GLocalV1OutwardStub := ⟨.edge, .slot0⟩
  let one : GLocalV1OutwardStub := ⟨.edge, .slot1⟩
  calc
    _ = gLocalV1Histogram
        ([zero, zero, zero, zero, zero, zero,
          one, one, one, one, one, one]) :=
      gLocalV1Histogram_eq_of_perm (by decide +kernel)
    _ = gLocalV1Histogram
        ([zero, zero, one, one, one, one, one, one]) := by
      simpa [List.replicate_succ] using
        (gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
          ([] : List GLocalV1OutwardStub)
          [one, one, one, one, one, one] zero 4)
    _ = gLocalV1Histogram [zero, zero, one, one] := by
      simpa [List.replicate_succ] using
        (gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
          [zero, zero] ([] : List GLocalV1OutwardStub) one 4)
    _ = _ := rfl

/-- Clip a neutral edge's vertex-neighbor stubs while retaining its chart stub.

Position: presentation-independent histogram theorem; its raw premise is the
literal stub occurrence list and its provenance is permutation plus clip-two. -/
theorem t6C25NeutralEdgeVertexStubHistogram :
    gLocalV1Histogram
        ([⟨.chart, .chartAt⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram
        ([⟨.chart, .chartAt⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot0⟩,
          ⟨.edge, .slot1⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) := by
  let chart : GLocalV1OutwardStub := ⟨.chart, .chartAt⟩
  let zero : GLocalV1OutwardStub := ⟨.edge, .slot0⟩
  let one : GLocalV1OutwardStub := ⟨.edge, .slot1⟩
  calc
    _ = gLocalV1Histogram
        ([chart, zero, zero, zero, zero, zero,
          one, one, one, one, one]) :=
      gLocalV1Histogram_eq_of_perm (by decide +kernel)
    _ = gLocalV1Histogram
        ([chart, zero, zero, one, one, one, one, one]) := by
      simpa [List.replicate_succ] using
        (gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
          [chart] [one, one, one, one, one] zero 3)
    _ = gLocalV1Histogram [chart, zero, zero, one, one] := by
      simpa [List.replicate_succ] using
        (gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
          [chart, zero, zero] ([] : List GLocalV1OutwardStub) one 3)
    _ = _ := rfl

/-- Normalize the `0,2,1` face-stub permutation.

Position: presentation-independent histogram theorem; its sole raw premise is
the literal three-stub permutation and it supplies no histogram certificate. -/
theorem t6C25FaceStubHistogram021 :
    gLocalV1Histogram
        ([⟨.face, .slot0⟩, ⟨.face, .slot2⟩, ⟨.face, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.face, .slot0⟩, ⟨.face, .slot1⟩,
        ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize the `1,0,2` face-stub permutation.

Position: presentation-independent histogram theorem; its sole raw premise is
the literal three-stub permutation and it supplies no histogram certificate. -/
theorem t6C25FaceStubHistogram102 :
    gLocalV1Histogram
        ([⟨.face, .slot1⟩, ⟨.face, .slot0⟩, ⟨.face, .slot2⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.face, .slot0⟩, ⟨.face, .slot1⟩,
        ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize the `2,1,0` face-stub permutation.

Position: presentation-independent histogram theorem; its sole raw premise is
the literal three-stub permutation and it supplies no histogram certificate. -/
theorem t6C25FaceStubHistogram210 :
    gLocalV1Histogram
        ([⟨.face, .slot2⟩, ⟨.face, .slot1⟩, ⟨.face, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.face, .slot0⟩, ⟨.face, .slot1⟩,
        ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize the `2,0` edge-stub permutation.

Position: presentation-independent histogram theorem; its sole raw premise is
the literal two-stub permutation and it supplies no histogram certificate. -/
theorem t6C25EdgeStubHistogram20 :
    gLocalV1Histogram
        ([⟨.edge, .slot2⟩, ⟨.edge, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.edge, .slot0⟩, ⟨.edge, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize the `2,1` edge-stub permutation.

Position: presentation-independent histogram theorem; its sole raw premise is
the literal two-stub permutation and it supplies no histogram certificate. -/
theorem t6C25EdgeStubHistogram21 :
    gLocalV1Histogram
        ([⟨.edge, .slot2⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.edge, .slot1⟩, ⟨.edge, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize the `1,0` edge-stub permutation.

Position: presentation-independent histogram theorem; its sole raw premise is
the literal two-stub permutation and it supplies no histogram certificate. -/
theorem t6C25EdgeStubHistogram10 :
    gLocalV1Histogram
        ([⟨.edge, .slot1⟩, ⟨.edge, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize a `2,1` face suffix behind the fixed vertex-stub prefix.

Position: presentation-independent histogram theorem; its raw premise is the
literal prefixed stub permutation and it carries no observation result. -/
theorem t6C25FacePrefixStubHistogram21 :
    gLocalV1Histogram
        ([⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
          ⟨.face, .slot2⟩, ⟨.face, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
        ⟨.face, .slot1⟩, ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize a `2,0` face suffix behind the fixed vertex-stub prefix.

Position: presentation-independent histogram theorem; its raw premise is the
literal prefixed stub permutation and it carries no observation result. -/
theorem t6C25FacePrefixStubHistogram20 :
    gLocalV1Histogram
        ([⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
          ⟨.face, .slot2⟩, ⟨.face, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
        ⟨.face, .slot0⟩, ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Normalize a `1,0` face suffix behind the fixed vertex-stub prefix.

Position: presentation-independent histogram theorem; its raw premise is the
literal prefixed stub permutation and it carries no observation result. -/
theorem t6C25FacePrefixStubHistogram10 :
    gLocalV1Histogram
        ([⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
          ⟨.face, .slot1⟩, ⟨.face, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
        ⟨.face, .slot0⟩, ⟨.face, .slot1⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- Move the last two entries of a generic three-element list into order.

Position: presentation-independent raw-list lemma; its only premise is three
payloads and it contains no T6 or observation data. -/
theorem t6C25Perm3_021 {alpha : Type}
    (a b c : alpha) : [a, c, b].Perm [a, b, c] :=
  (List.Perm.swap b c []).cons a

/-- Swap the first two entries of a generic three-element list.

Position: presentation-independent raw-list lemma; its only premise is three
payloads and it contains no T6 or observation data. -/
theorem t6C25Perm3_102 {alpha : Type}
    (a b c : alpha) : [b, a, c].Perm [a, b, c] :=
  List.Perm.swap a b [c]

/-- Rotate a generic `1,2,0` three-element list into order.

Position: presentation-independent raw-list lemma; its only premise is three
payloads and it contains no T6 or observation data. -/
theorem t6C25Perm3_120 {alpha : Type}
    (a b c : alpha) : [b, c, a].Perm [a, b, c] :=
  ((List.Perm.swap a c []).cons b).trans (List.Perm.swap a b [c])

/-- Rotate a generic `2,0,1` three-element list into order.

Position: presentation-independent raw-list lemma; its only premise is three
payloads and it contains no T6 or observation data. -/
theorem t6C25Perm3_201 {alpha : Type}
    (a b c : alpha) : [c, a, b].Perm [a, b, c] :=
  (List.Perm.swap a c [b]).trans ((List.Perm.swap b c []).cons a)

/-- Reverse a generic three-element list by an explicit permutation proof.

Position: presentation-independent raw-list lemma; its only premise is three
payloads and it contains no T6 or observation data. -/
theorem t6C25Perm3_210 {alpha : Type}
    (a b c : alpha) : [c, b, a].Perm [a, b, c] := by
  exact (List.Perm.swap b c [a]).trans
    (((List.Perm.swap a c []).cons b).trans (List.Perm.swap a b [c]))

set_option maxHeartbeats 20000000 in
/-- Evaluate the neighbor-descriptor histogram of every retained A0 cell.

Position: fixture-local member-aware theorem; its raw premises are the complete
cell list and incidence tables, normalized through owner histogram APIs. -/
theorem t6C25A0NeighborHistogram
    (root : t6Presentation.GLocalV1Cell targetZero
      (t6Presentation.gLocalV1InitialState targetZero))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetZero
      (t6Presentation.gLocalV1InitialState targetZero)) :
    gLocalV1Histogram
        (t6Presentation.gLocalV1NeighborDescriptors targetZero
          (t6Presentation.gLocalV1InitialState targetZero)
          t6Presentation.gLocalV1IdentityRelabel root) =
      (t6C25ExpectedA0Ball root).neighborDescriptors := by
  rw [t6C25CellListA0] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq,
    t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
    t6C25FineChart, t6C25FineEdge,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t6Presentation.gLocalV1NeighborDescriptors_eq_of_cellList_eq
      _ _ _ _ _ t6C25CellListA0]
    simp +decide [t6Presentation.gLocalV1IncidenceRelations_apply,
      t6C25A0RootLabel, t6C25ExpectedA0Ball,
      handAnchorChartBall, handAnchorVertexBall, handAnchorEdgeBall,
      handNeutralChartBall, handNeutralVertexBall, handNeutralEdgeBall,
      handNeutralFaceBall, handBall, handDescriptor]
  all_goals
    repeat' rw [t6Presentation.gLocalV1OutwardStubHistogram_eq_of_cellList_eq
      _ _ _ _ _ t6C25CellListA0]
    simp only [t6Presentation.gLocalV1IncidenceRelations_apply,
      t6Presentation.gLocalV1CellType_apply,
      gLocalV1RelationStubSlot_apply]
    simp +decide [t6Presentation, identitySplitPresentation,
      edgeChart, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2,
      t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
      t6C25FineChart, t6C25FineEdge]
  all_goals
    try simp only [t6C25NeutralStubHistogramSixEqTwo,
      t6C25NeutralEdgeVertexStubHistogram,
      t6C25FaceStubHistogram021, t6C25FaceStubHistogram102,
      t6C25FaceStubHistogram210,
      t6C25EdgeStubHistogram20, t6C25EdgeStubHistogram21,
      t6C25EdgeStubHistogram10,
      t6C25FacePrefixStubHistogram21,
      t6C25FacePrefixStubHistogram20,
      t6C25FacePrefixStubHistogram10]
  all_goals
    first
    | exact gLocalV1Histogram_cons_six_eq_cons_two _ _
    | rfl
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_021 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_102 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_120 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_201 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_210 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_021 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_102 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_120 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_201 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_210 _ _ _).cons _)

/-- Assemble the rooted-ball normal form of every retained T6 A0 cell.

Position: fixture-local composition theorem; its raw provenance is the
independently proved root label and neighbor histogram, not a supplied ball. -/
theorem t6C25A0RootedBall
    (root : t6Presentation.GLocalV1Cell targetZero
      (t6Presentation.gLocalV1InitialState targetZero))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetZero
      (t6Presentation.gLocalV1InitialState targetZero)) :
    t6Presentation.gLocalV1RootedBall targetZero
        (t6Presentation.gLocalV1InitialState targetZero)
        t6Presentation.gLocalV1IdentityRelabel root =
      t6C25ExpectedA0Ball root := by
  rw [t6Presentation.gLocalV1RootedBall_apply]
  congr 1
  · exact t6C25A0RootLabel root hroot
  · exact t6C25A0NeighborHistogram root hroot

set_option maxHeartbeats 20000000 in
/-- T6 target-zero identity-relabel rooted-ball occurrences, derived from the
registered raw cell list with clipping performed separately at every
histogram layer.

Position: primary fixture-local A0 occurrence theorem; its raw premises are the
registered cell/support/incidence/map tables and it assumes no observation. -/
theorem t6A0RootedBallOccurrences :
    (t6Presentation.gLocalV1CellList targetZero
      (t6Presentation.gLocalV1InitialState targetZero)).map (fun root =>
        t6Presentation.gLocalV1RootedBall targetZero
          (t6Presentation.gLocalV1InitialState targetZero)
          t6Presentation.gLocalV1IdentityRelabel root) =
      rawA0Occurrences 6 := by
  calc
    _ = (t6Presentation.gLocalV1CellList targetZero
          (t6Presentation.gLocalV1InitialState targetZero)).map
          t6C25ExpectedA0Ball := by
      apply List.map_congr_left
      intro root hroot
      exact t6C25A0RootedBall root hroot
    _ = rawA0Occurrences 6 := by
      rw [t6C25CellListA0]
      simp +decide [t6C25ExpectedA0Ball, rawA0Occurrences,
        orderedAnchorChartVertex, orderedAnchorEdge,
        orderedNeutralChartVertex, orderedNeutralEdges,
        orderedNeutralFaces, List.replicate_succ,
        t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
        t6C25FineChart, t6C25FineEdge]
      repeat' apply And.intro
      all_goals intro himpossible
      all_goals have hval := congrArg Fin.val himpossible
      all_goals norm_num at hval

/-- Closed per-cell rooted-ball normal form for T6 target one.

Position: fixture-local normal-form constructor; its raw provenance is the
registered neutral roles and literal support codes, not an `obsG` field. -/
private def t6C25ExpectedA1Ball :
    t6Presentation.GLocalV1Cell targetOne
      (t6Presentation.gLocalV1InitialState targetOne) → GLocalV1RootedBall
  | .coarseChart _ => handNeutralChartBall .coarse [1] [1]
  | .coarseVertex _ => handNeutralVertexBall .coarse [1] [1]
  | .coarseEdge _ => handNeutralEdgeBall .coarse [1] [1]
  | .coarseFace _ => handNeutralFaceBall .coarse [1] [1]
  | .fineChart _ => handNeutralChartBall .fine [2] [1]
  | .fineVertex _ => handNeutralVertexBall .fine [2] [1]
  | .fineEdge _ => handNeutralEdgeBall .fine [2] [1]
  | .fineFace _ => handNeutralFaceBall .fine [2] [1]

set_option maxHeartbeats 20000000 in
/-- Evaluate the root label of every retained T6 target-one cell.

Position: fixture-local member-aware theorem; its raw premises are the complete
cell list, support/map tables, and owner flag APIs, not a supplied label. -/
theorem t6C25A1RootLabel
    (root : t6Presentation.GLocalV1Cell targetOne
      (t6Presentation.gLocalV1InitialState targetOne))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetOne
      (t6Presentation.gLocalV1InitialState targetOne)) :
    t6Presentation.gLocalV1CellLabel targetOne
        (t6Presentation.gLocalV1InitialState targetOne)
        t6Presentation.gLocalV1IdentityRelabel root =
      (t6C25ExpectedA1Ball root).rootLabel := by
  rw [t6C25CellListA1] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
    t6C25FineChart, t6C25FineEdge, t6C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t6Presentation.gLocalV1CellLabel_apply,
      t6Presentation.gLocalV1CellSide_apply,
      t6Presentation.gLocalV1CellType_apply,
      t6Presentation.gLocalV1CellSupportCodes_apply,
      t6Presentation.gLocalV1CellPiImageCodes_apply,
      t6Presentation.gLocalV1CellMapStatus_apply]
  all_goals try rw [t6C25CoarseChartFlags]
  all_goals try rw [t6C25FineChartFlags]
  all_goals try rw [t6C25CoarseVertexFlags _ (t6C25CoarseEdge 1)
    (by decide +kernel) (by
      left
      simp [t6Presentation, identitySplitPresentation, edgeChart,
        t6C25CoarseEdge])]
  all_goals try rw [t6C25FineVertexFlags _ 1
    (by decide +kernel) (by decide +kernel) (by
      left
      simp [t6Presentation, identitySplitPresentation, edgeChart,
        t6C25FineEdge])]
  all_goals try rw [t6C25CoarseEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t6C25FineEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t6C25CoarseFaceFlags]
  all_goals try rw [t6C25FineFaceFlags]
  all_goals
    simp only [t6Presentation.gLocalV1CoarseChartSupport_apply,
      t6Presentation.gLocalV1FineChartSupport_apply,
      t6Presentation.gLocalV1CoarseEdgeSupport_apply,
      t6Presentation.gLocalV1FineEdgeSupport_apply,
      t6Presentation.gLocalV1CoarseFaceSupport_apply,
      t6Presentation.gLocalV1FineFaceSupport_apply]
  all_goals try rw [t6C25FineScopeA1]
  all_goals try rw [t6C25CoarseIdentityCodeFun]
  all_goals try rw [t6C25FineIdentityCodeFun]
  all_goals try simp only [t6_computedFactor_apply]
  all_goals
    simp +decide (config := { maxSteps := 5000000 })
      [t6C25ExpectedA1Ball, handNeutralChartBall,
        handNeutralVertexBall, handNeutralEdgeBall,
        handNeutralFaceBall, handBall, handLabel,
        t6Presentation, identitySplitPresentation,
        targetOne, coarseRead, coarseChartSupport, fineChartSupport,
        edgeChart, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2,
        t6C25FineTarget]

set_option maxHeartbeats 20000000 in
/-- Evaluate the neighbor-descriptor histogram of every retained A1 cell.

Position: fixture-local member-aware theorem; its raw premises are the complete
cell list and incidence tables, normalized through owner histogram APIs. -/
theorem t6C25A1NeighborHistogram
    (root : t6Presentation.GLocalV1Cell targetOne
      (t6Presentation.gLocalV1InitialState targetOne))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetOne
      (t6Presentation.gLocalV1InitialState targetOne)) :
    gLocalV1Histogram
        (t6Presentation.gLocalV1NeighborDescriptors targetOne
          (t6Presentation.gLocalV1InitialState targetOne)
          t6Presentation.gLocalV1IdentityRelabel root) =
      (t6C25ExpectedA1Ball root).neighborDescriptors := by
  rw [t6C25CellListA1] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
    t6C25FineChart, t6C25FineEdge, t6C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t6Presentation.gLocalV1NeighborDescriptors_eq_of_cellList_eq
      _ _ _ _ _ t6C25CellListA1]
    simp +decide [t6Presentation.gLocalV1IncidenceRelations_apply,
      t6C25A1RootLabel, t6C25ExpectedA1Ball,
      handNeutralChartBall, handNeutralVertexBall, handNeutralEdgeBall,
      handNeutralFaceBall, handBall, handDescriptor]
  all_goals
    repeat' rw [t6Presentation.gLocalV1OutwardStubHistogram_eq_of_cellList_eq
      _ _ _ _ _ t6C25CellListA1]
    simp only [t6Presentation.gLocalV1IncidenceRelations_apply,
      t6Presentation.gLocalV1CellType_apply,
      gLocalV1RelationStubSlot_apply]
    simp +decide [t6Presentation, identitySplitPresentation,
      edgeChart, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2,
      t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
      t6C25FineChart, t6C25FineEdge, t6C25FineFace]
  all_goals
    try simp only [t6C25NeutralStubHistogramSixEqTwo,
      t6C25NeutralEdgeVertexStubHistogram,
      t6C25FaceStubHistogram021, t6C25FaceStubHistogram102,
      t6C25FaceStubHistogram210,
      t6C25EdgeStubHistogram20, t6C25EdgeStubHistogram21,
      t6C25EdgeStubHistogram10,
      t6C25FacePrefixStubHistogram21,
      t6C25FacePrefixStubHistogram20,
      t6C25FacePrefixStubHistogram10]
  all_goals
    first
    | exact gLocalV1Histogram_cons_six_eq_cons_two _ _
    | rfl
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_021 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_102 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_120 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_201 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_210 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_021 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_102 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_120 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_201 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_210 _ _ _).cons _)

/-- Assemble the rooted-ball normal form of every retained T6 A1 cell.

Position: fixture-local composition theorem; its raw provenance is the
independently proved root label and neighbor histogram, not a supplied ball. -/
theorem t6C25A1RootedBall
    (root : t6Presentation.GLocalV1Cell targetOne
      (t6Presentation.gLocalV1InitialState targetOne))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetOne
      (t6Presentation.gLocalV1InitialState targetOne)) :
    t6Presentation.gLocalV1RootedBall targetOne
        (t6Presentation.gLocalV1InitialState targetOne)
        t6Presentation.gLocalV1IdentityRelabel root =
      t6C25ExpectedA1Ball root := by
  rw [t6Presentation.gLocalV1RootedBall_apply]
  congr 1
  · exact t6C25A1RootLabel root hroot
  · exact t6C25A1NeighborHistogram root hroot

set_option maxHeartbeats 20000000 in
/-- T6 target-one identity-relabel rooted-ball occurrences, derived from the
registered raw cell list with clipping performed separately at every
histogram layer.

Position: primary fixture-local A1 occurrence theorem; its raw premises are the
registered cell/support/incidence/map tables and it assumes no observation. -/
theorem t6A1RootedBallOccurrences :
    (t6Presentation.gLocalV1CellList targetOne
      (t6Presentation.gLocalV1InitialState targetOne)).map (fun root =>
        t6Presentation.gLocalV1RootedBall targetOne
          (t6Presentation.gLocalV1InitialState targetOne)
          t6Presentation.gLocalV1IdentityRelabel root) =
      rawA1Occurrences 6 := by
  calc
    _ = (t6Presentation.gLocalV1CellList targetOne
          (t6Presentation.gLocalV1InitialState targetOne)).map
          t6C25ExpectedA1Ball := by
      apply List.map_congr_left
      intro root hroot
      exact t6C25A1RootedBall root hroot
    _ = rawA1Occurrences 6 := by
      rw [t6C25CellListA1]
      simp [t6C25ExpectedA1Ball, rawA1Occurrences,
        orderedNeutralChartVertex, orderedNeutralEdges,
        orderedNeutralFaces, List.replicate_succ]

/-- Closed per-cell rooted-ball normal form for T6 full target scope.

Position: fixture-local normal-form constructor; its raw provenance is the
registered anchor/neutral roles and literal support codes, not an `obsG` field. -/
private def t6C25ExpectedFullBall :
    t6Presentation.GLocalV1Cell targetFull
      (t6Presentation.gLocalV1InitialState targetFull) → GLocalV1RootedBall
  | .coarseChart chart => if chart = t6C25CoarseChart 0 then
      handAnchorChartBall .coarse [0] [0]
    else handNeutralChartBall .coarse [0, 1] [0, 1]
  | .coarseVertex chart => if chart = t6C25CoarseChart 0 then
      handAnchorVertexBall .coarse [0] [0]
    else handNeutralVertexBall .coarse [0, 1] [0, 1]
  | .coarseEdge edge => if edge = t6C25CoarseEdge 0 then
      handAnchorEdgeBall .coarse [0] [0]
    else handNeutralEdgeBall .coarse [0, 1] [0, 1]
  | .coarseFace _ => handNeutralFaceBall .coarse [0, 1] [0, 1]
  | .fineChart chart => if chart = t6C25FineChart 0 then
      handAnchorChartBall .fine [0, 1] [0]
    else handNeutralChartBall .fine [2] [1]
  | .fineVertex chart => if chart = t6C25FineChart 0 then
      handAnchorVertexBall .fine [0, 1] [0]
    else handNeutralVertexBall .fine [2] [1]
  | .fineEdge edge => if edge = t6C25FineEdge 0 then
      handAnchorEdgeBall .fine [0, 1] [0]
    else handNeutralEdgeBall .fine [2] [1]
  | .fineFace _ => handNeutralFaceBall .fine [2] [1]

set_option maxHeartbeats 20000000 in
/-- Evaluate the root label of every retained T6 full-scope cell.

Position: fixture-local member-aware theorem; its raw premises are the complete
cell list, support/map tables, and owner flag APIs, not a supplied label. -/
theorem t6C25FullRootLabel
    (root : t6Presentation.GLocalV1Cell targetFull
      (t6Presentation.gLocalV1InitialState targetFull))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetFull
      (t6Presentation.gLocalV1InitialState targetFull)) :
    t6Presentation.gLocalV1CellLabel targetFull
        (t6Presentation.gLocalV1InitialState targetFull)
        t6Presentation.gLocalV1IdentityRelabel root =
      (t6C25ExpectedFullBall root).rootLabel := by
  rw [t6C25CellListFull] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
    t6C25FineChart, t6C25FineEdge, t6C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t6Presentation.gLocalV1CellLabel_apply,
      t6Presentation.gLocalV1CellSide_apply,
      t6Presentation.gLocalV1CellType_apply,
      t6Presentation.gLocalV1CellSupportCodes_apply,
      t6Presentation.gLocalV1CellPiImageCodes_apply,
      t6Presentation.gLocalV1CellMapStatus_apply]
  all_goals try rw [t6C25CoarseChartFlags]
  all_goals try rw [t6C25FineChartFlags]
  all_goals try rw [t6C25CoarseVertexFlags _ (t6C25CoarseEdge 0)
    (by decide +kernel) (by left; rfl)]
  all_goals try rw [t6C25CoarseVertexFlags _ (t6C25CoarseEdge 1)
    (by decide +kernel) (by
      left
      simp [t6Presentation, identitySplitPresentation, edgeChart,
        t6C25CoarseEdge])]
  all_goals try rw [t6C25FineVertexFlags _ 0
    (by decide +kernel) (by decide +kernel) (by left; rfl)]
  all_goals try rw [t6C25FineVertexFlags _ 1
    (by decide +kernel) (by decide +kernel) (by
      left
      simp [t6Presentation, identitySplitPresentation, edgeChart,
        t6C25FineEdge])]
  all_goals try rw [t6C25CoarseEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t6C25FineEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t6C25CoarseFaceFlags]
  all_goals try rw [t6C25FineFaceFlags]
  all_goals
    simp only [t6Presentation.gLocalV1CoarseChartSupport_apply,
      t6Presentation.gLocalV1FineChartSupport_apply,
      t6Presentation.gLocalV1CoarseEdgeSupport_apply,
      t6Presentation.gLocalV1FineEdgeSupport_apply,
      t6Presentation.gLocalV1CoarseFaceSupport_apply,
      t6Presentation.gLocalV1FineFaceSupport_apply]
  all_goals try rw [t6C25FineScopeFull]
  all_goals try rw [t6C25CoarseIdentityCodeFun]
  all_goals try rw [t6C25FineIdentityCodeFun]
  all_goals try simp only [t6_computedFactor_apply]
  all_goals
    simp +decide (config := { maxSteps := 5000000 })
      [t6C25ExpectedFullBall,
        handAnchorChartBall, handAnchorVertexBall, handAnchorEdgeBall,
        handNeutralChartBall, handNeutralVertexBall,
        handNeutralEdgeBall, handNeutralFaceBall,
        handBall, handLabel,
        t6Presentation, identitySplitPresentation,
        targetFull, coarseRead, coarseChartSupport, fineChartSupport,
        edgeChart, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2,
        t6C25CoarseChart, t6C25CoarseEdge,
        t6C25FineChart, t6C25FineEdge, t6C25Sort01Nat]

set_option maxHeartbeats 20000000 in
/-- Evaluate the neighbor-descriptor histogram of every retained full cell.

Position: fixture-local member-aware theorem; its raw premises are the complete
cell list and incidence tables, normalized through owner histogram APIs. -/
theorem t6C25FullNeighborHistogram
    (root : t6Presentation.GLocalV1Cell targetFull
      (t6Presentation.gLocalV1InitialState targetFull))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetFull
      (t6Presentation.gLocalV1InitialState targetFull)) :
    gLocalV1Histogram
        (t6Presentation.gLocalV1NeighborDescriptors targetFull
          (t6Presentation.gLocalV1InitialState targetFull)
          t6Presentation.gLocalV1IdentityRelabel root) =
      (t6C25ExpectedFullBall root).neighborDescriptors := by
  rw [t6C25CellListFull] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
    t6C25FineChart, t6C25FineEdge, t6C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t6Presentation.gLocalV1NeighborDescriptors_eq_of_cellList_eq
      _ _ _ _ _ t6C25CellListFull]
    simp +decide [t6Presentation.gLocalV1IncidenceRelations_apply,
      t6C25FullRootLabel, t6C25ExpectedFullBall,
      handAnchorChartBall, handAnchorVertexBall, handAnchorEdgeBall,
      handNeutralChartBall, handNeutralVertexBall, handNeutralEdgeBall,
      handNeutralFaceBall, handBall, handDescriptor]
  all_goals
    repeat' rw [t6Presentation.gLocalV1OutwardStubHistogram_eq_of_cellList_eq
      _ _ _ _ _ t6C25CellListFull]
    simp only [t6Presentation.gLocalV1IncidenceRelations_apply,
      t6Presentation.gLocalV1CellType_apply,
      gLocalV1RelationStubSlot_apply]
    simp +decide [t6Presentation, identitySplitPresentation,
      edgeChart, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2,
      t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
      t6C25FineChart, t6C25FineEdge, t6C25FineFace]
  all_goals
    try simp only [t6C25NeutralStubHistogramSixEqTwo,
      t6C25NeutralEdgeVertexStubHistogram,
      t6C25FaceStubHistogram021, t6C25FaceStubHistogram102,
      t6C25FaceStubHistogram210,
      t6C25EdgeStubHistogram20, t6C25EdgeStubHistogram21,
      t6C25EdgeStubHistogram10,
      t6C25FacePrefixStubHistogram21,
      t6C25FacePrefixStubHistogram20,
      t6C25FacePrefixStubHistogram10]
  all_goals
    first
    | exact gLocalV1Histogram_cons_six_eq_cons_two _ _
    | rfl
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_021 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_102 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_120 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_201 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t6C25Perm3_210 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_021 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_102 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_120 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_201 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t6C25Perm3_210 _ _ _).cons _)

/-- Assemble the rooted-ball normal form of every retained T6 full-scope cell.

Position: fixture-local composition theorem; its raw provenance is the
independently proved root label and neighbor histogram, not a supplied ball. -/
theorem t6C25FullRootedBall
    (root : t6Presentation.GLocalV1Cell targetFull
      (t6Presentation.gLocalV1InitialState targetFull))
    (hroot : root ∈ t6Presentation.gLocalV1CellList targetFull
      (t6Presentation.gLocalV1InitialState targetFull)) :
    t6Presentation.gLocalV1RootedBall targetFull
        (t6Presentation.gLocalV1InitialState targetFull)
        t6Presentation.gLocalV1IdentityRelabel root =
      t6C25ExpectedFullBall root := by
  rw [t6Presentation.gLocalV1RootedBall_apply]
  congr 1
  · exact t6C25FullRootLabel root hroot
  · exact t6C25FullNeighborHistogram root hroot

set_option maxHeartbeats 20000000 in
/-- T6 full-scope identity-relabel rooted-ball occurrences, derived from the
registered raw cell list with clipping performed separately at every
histogram layer.

Position: primary fixture-local full occurrence theorem; its raw premises are
the registered cell/support/incidence/map tables and it assumes no observation. -/
theorem t6FullRootedBallOccurrences :
    (t6Presentation.gLocalV1CellList targetFull
      (t6Presentation.gLocalV1InitialState targetFull)).map (fun root =>
        t6Presentation.gLocalV1RootedBall targetFull
          (t6Presentation.gLocalV1InitialState targetFull)
          t6Presentation.gLocalV1IdentityRelabel root) =
      rawFullOccurrences 6 := by
  calc
    _ = (t6Presentation.gLocalV1CellList targetFull
          (t6Presentation.gLocalV1InitialState targetFull)).map
          t6C25ExpectedFullBall := by
      apply List.map_congr_left
      intro root hroot
      exact t6C25FullRootedBall root hroot
    _ = rawFullOccurrences 6 := by
      rw [t6C25CellListFull]
      simp [t6C25ExpectedFullBall, rawFullOccurrences,
        orderedAnchorChartVertex, orderedAnchorEdge,
        orderedNeutralChartVertex, orderedNeutralEdges,
        orderedNeutralFaces, List.replicate_succ,
        t6C25CoarseChart, t6C25CoarseEdge, t6C25CoarseFace,
        t6C25FineChart, t6C25FineEdge, t6C25FineFace]
      repeat' apply And.intro
      all_goals intro himpossible
      all_goals have hval := congrArg Fin.val himpossible
      all_goals norm_num at hval

/-- t3C25CoarseChart is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it is a typed alias used to state raw finite T3 cells without changing their data; Raw premise/provenance: it only preserves the registered finite carrier type used by the raw T3 fixture.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25CoarseChart (chart : Fin 2) :
    t3Presentation.CoarseChart := chart

/-- t3C25CoarseEdge is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it is a typed alias used to state raw finite T3 cells without changing their data; Raw premise/provenance: it only preserves the registered finite carrier type used by the raw T3 fixture.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25CoarseEdge (edge : Fin 4) :
    t3Presentation.CoarseEdge := edge

/-- t3C25CoarseFace is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it is a typed alias used to state raw finite T3 cells without changing their data; Raw premise/provenance: it only preserves the registered finite carrier type used by the raw T3 fixture.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25CoarseFace (face : Fin 3) :
    t3Presentation.CoarseFace := face

/-- t3C25FineChart is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it is a typed alias used to state raw finite T3 cells without changing their data; Raw premise/provenance: it only preserves the registered finite carrier type used by the raw T3 fixture.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25FineChart (chart : Fin 2) :
    t3Presentation.FineChart := chart

/-- t3C25FineEdge is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it is a typed alias used to state raw finite T3 cells without changing their data; Raw premise/provenance: it only preserves the registered finite carrier type used by the raw T3 fixture.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25FineEdge (edge : Fin 4) :
    t3Presentation.FineEdge := edge

/-- t3C25FineFace is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it is a typed alias used to state raw finite T3 cells without changing their data; Raw premise/provenance: it only preserves the registered finite carrier type used by the raw T3 fixture.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25FineFace (face : Fin 3) :
    t3Presentation.FineFace := face

/-- t3C25FineTarget is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it is a typed alias used to state raw finite T3 cells without changing their data; Raw premise/provenance: it only preserves the registered finite carrier type used by the raw T3 fixture.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25FineTarget (target : Fin 3) :
    t3Presentation.FineTarget := target

/-- t3C25CoarseTargetCode is a fixture-local theorem for the registered T3 observation calculation.

Position: it normalizes finite target codes used in T3 cell labels; Raw premise/provenance: it follows from the registered target enumeration and identity relabel owner equations.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
@[simp] theorem t3C25CoarseTargetCode
    (target : t3Presentation.CoarseTarget) :
    t3Presentation.coarseTargetCode target = target.val := by
  change (List.finRange 2).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- t3C25FineTargetCode is a fixture-local theorem for the registered T3 observation calculation.

Position: it normalizes finite target codes used in T3 cell labels; Raw premise/provenance: it follows from the registered target enumeration and identity relabel owner equations.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
@[simp] theorem t3C25FineTargetCode
    (target : t3Presentation.FineTarget) :
    t3Presentation.fineTargetCode target = target.val := by
  change ((List.finRange 3).map id).dedup.idxOf target = target.val
  fin_cases target <;> decide

/-- t3C25FineScopeFull is a fixture-local theorem for the registered T3 observation calculation.

Position: it fixes the full-scope fine-target scope used by the T3 normal form; Raw premise/provenance: it follows from the registered computed-factor table through gLocalV1FineScopeTargets_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineScopeFull :
    t3Presentation.gLocalV1FineScopeTargets targetFull = Finset.univ := by
  rw [t3Presentation.gLocalV1FineScopeTargets_apply]
  ext target
  fin_cases target <;>
    simp +decide

/-- t3C25FineIdentityCodeFun is a fixture-local theorem for the registered T3 observation calculation.

Position: it normalizes finite target codes used in T3 cell labels; Raw premise/provenance: it follows from the registered target enumeration and identity relabel owner equations.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineIdentityCodeFun :
    t3Presentation.gLocalV1FineRelabelCode
        t3Presentation.gLocalV1IdentityRelabel =
      fun target => target.val := by
  funext target
  rw [t3Presentation.gLocalV1FineRelabelCode_identity]
  exact t3C25FineTargetCode target

/-- t3C25CoarseIdentityCodeFun is a fixture-local theorem for the registered T3 observation calculation.

Position: it normalizes finite target codes used in T3 cell labels; Raw premise/provenance: it follows from the registered target enumeration and identity relabel owner equations.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CoarseIdentityCodeFun :
    t3Presentation.gLocalV1CoarseRelabelCode
        t3Presentation.gLocalV1IdentityRelabel =
      fun target => target.val := by
  funext target
  rw [t3Presentation.gLocalV1CoarseRelabelCode_identity]
  exact t3C25CoarseTargetCode target

/-- t3C25Sort01Nat is a fixture-local theorem for the registered T3 observation calculation.

Position: it normalizes finite target codes used in T3 cell labels; Raw premise/provenance: it follows from the registered target enumeration and identity relabel owner equations.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25Sort01Nat :
    ({0, 1} : Finset Nat).sort (· ≤ ·) = [0, 1] := by
  rw [Finset.sort_insert (r := (· ≤ ·)) (by simp) (by simp)]
  simp

/-- t3C25NeutralStubHistogramThreeEqTwo is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25NeutralStubHistogramThreeEqTwo :
    gLocalV1Histogram
        ([⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram
        ([⟨.edge, .slot0⟩, ⟨.edge, .slot0⟩,
          ⟨.edge, .slot1⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) := by
  let zero : GLocalV1OutwardStub := ⟨.edge, .slot0⟩
  let one : GLocalV1OutwardStub := ⟨.edge, .slot1⟩
  calc
    _ = gLocalV1Histogram [zero, zero, zero, one, one, one] :=
      gLocalV1Histogram_eq_of_perm (by decide +kernel)
    _ = gLocalV1Histogram [zero, zero, one, one, one] := by
      simpa [List.replicate_succ] using
        (gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
          ([] : List GLocalV1OutwardStub) [one, one, one] zero 1)
    _ = gLocalV1Histogram [zero, zero, one, one] := by
      simpa [List.replicate_succ] using
        (gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
          [zero, zero] ([] : List GLocalV1OutwardStub) one 1)

/-- t3C25NeutralEdgeVertexStubHistogram is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25NeutralEdgeVertexStubHistogram :
    gLocalV1Histogram
        ([⟨.chart, .chartAt⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram
        ([⟨.chart, .chartAt⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot0⟩,
          ⟨.edge, .slot1⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)
/-- t3C25CellListFull is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the exact retained-cell enumeration for the full-scope T3 proof; Raw premise/provenance: it evaluates the registered initial state through gLocalV1CellList_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CellListFull :
    t3Presentation.gLocalV1CellList targetFull
      (t3Presentation.gLocalV1InitialState targetFull) =
    [.coarseChart (t3C25CoarseChart 0),
     .coarseVertex (t3C25CoarseChart 0),
     .coarseChart (t3C25CoarseChart 1),
     .coarseVertex (t3C25CoarseChart 1),
     .coarseEdge (t3C25CoarseEdge 0),
     .coarseEdge (t3C25CoarseEdge 1),
     .coarseEdge (t3C25CoarseEdge 2),
     .coarseEdge (t3C25CoarseEdge 3),
     .coarseFace (t3C25CoarseFace 0),
     .coarseFace (t3C25CoarseFace 1),
     .coarseFace (t3C25CoarseFace 2),
     .fineChart (t3C25FineChart 0),
     .fineVertex (t3C25FineChart 0),
     .fineChart (t3C25FineChart 1),
     .fineVertex (t3C25FineChart 1),
     .fineEdge (t3C25FineEdge 0),
     .fineEdge (t3C25FineEdge 1),
     .fineEdge (t3C25FineEdge 2),
     .fineEdge (t3C25FineEdge 3),
     .fineFace (t3C25FineFace 0),
     .fineFace (t3C25FineFace 1),
     .fineFace (t3C25FineFace 2)] := by
  rw [t3Presentation.gLocalV1CellList_apply]
  decide +kernel

/-- t3C25CoarseSelfLoop is a fixture-local theorem for the registered T3 observation calculation.

Position: it supplies the self-loop premise to definition-owner critical and bridge APIs; Raw premise/provenance: it is computed from the registered raw edge endpoint table.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CoarseSelfLoop
    (edge : t3Presentation.CoarseEdge) :
    t3Presentation.coarseEdgeLeft edge =
      t3Presentation.coarseEdgeRight edge := by
  fin_cases edge <;>
    simp [t3Presentation, identitySplitPresentation, edgeChart]

/-- t3C25FineSelfLoop is a fixture-local theorem for the registered T3 observation calculation.

Position: it supplies the self-loop premise to definition-owner critical and bridge APIs; Raw premise/provenance: it is computed from the registered raw edge endpoint table.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineSelfLoop
    (edge : t3Presentation.FineEdge) :
    t3Presentation.fineEdgeLeft edge =
      t3Presentation.fineEdgeRight edge := by
  fin_cases edge <;>
    simp [t3Presentation, identitySplitPresentation, edgeChart]

/-- t3C25EdgeMap is a fixture-local theorem for the registered T3 observation calculation.

Position: it supplies mapped-edge provenance for the active-fine-vertex owner API; Raw premise/provenance: it is computed from the registered raw fine-to-coarse edge map.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25EdgeMap (edge : Fin 4) :
    t3Presentation.edgeMap (t3C25FineEdge edge) =
      some (t3C25CoarseEdge edge) := by
  fin_cases edge <;>
    simp [t3Presentation, identitySplitPresentation,
      t3C25FineEdge, t3C25CoarseEdge]

/-- t3C25FineFaceKeyInjective is a fixture-local theorem for the registered T3 observation calculation.

Position: it supplies the injectivity premise to the FaceTwin owner theorem; Raw premise/provenance: it follows from the registered raw fine face edge-zero table.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineFaceKeyInjective (A : Finset (Fin 2)) :
    Function.Injective (t3Presentation.gLocalV1FineFaceKey A) := by
  intro left right hequal
  have hedge : t3Presentation.fineFaceEdge0 left =
      t3Presentation.fineFaceEdge0 right :=
    congrArg GLocalV1FineFaceTwinKey.edge0 hequal
  fin_cases left <;> fin_cases right <;>
    simp [t3Presentation, identitySplitPresentation, t3FaceEdge0] at hedge ⊢

/-- t3C25CoarseEdgeFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CoarseEdgeFlags
    {A : Finset t3Presentation.CoarseTarget}
    (edge : t3Presentation.CoarseEdge)
    (hmem : edge ∈ (t3Presentation.gLocalV1InitialState A).coarseEdges) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.coarseEdge edge) =
      handFlags .coarse .edge := by
  have hcritical :=
    t3Presentation.mem_gLocalV1CoarseCriticalEdges_of_mem_of_selfLoop
      A _ edge hmem (t3C25CoarseSelfLoop edge)
  have hguard :=
    t3Presentation.mem_gLocalV1GuardedCoarseEdges_of_mem_critical
      A _ edge hcritical
  have hnbridge :=
    t3Presentation.not_mem_gLocalV1CoarseBridges_of_selfLoop
      A (t3Presentation.gLocalV1InitialState A) edge
      (t3C25CoarseSelfLoop edge)
  rw [t3Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical, hguard, hnbridge,
    t3C25CoarseSelfLoop]

/-- t3C25FineEdgeFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineEdgeFlags
    {A : Finset t3Presentation.CoarseTarget}
    (edge : t3Presentation.FineEdge)
    (hmem : edge ∈ (t3Presentation.gLocalV1InitialState A).fineEdges) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.fineEdge edge) =
      handFlags .fine .edge := by
  have hcritical :=
    t3Presentation.mem_gLocalV1FineCriticalEdges_of_mem_of_selfLoop
      A _ edge hmem (t3C25FineSelfLoop edge)
  have hnbridge :=
    t3Presentation.not_mem_gLocalV1FineBridges_of_selfLoop
      A (t3Presentation.gLocalV1InitialState A) edge
      (t3C25FineSelfLoop edge)
  rw [t3Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical, hnbridge, t3C25FineSelfLoop]

/-- t3C25CoarseVertexFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CoarseVertexFlags
    {A : Finset t3Presentation.CoarseTarget}
    (chart : t3Presentation.CoarseChart)
    (edge : t3Presentation.CoarseEdge)
    (hmem : edge ∈ (t3Presentation.gLocalV1InitialState A).coarseEdges)
    (hendpoint : chart = t3Presentation.coarseEdgeLeft edge ∨
      chart = t3Presentation.coarseEdgeRight edge) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.coarseVertex chart) =
      handFlags .coarse .vertex := by
  have hcriticalEdge :=
    t3Presentation.mem_gLocalV1CoarseCriticalEdges_of_mem_of_selfLoop
      A _ edge hmem (t3C25CoarseSelfLoop edge)
  have hcritical :=
    t3Presentation.mem_gLocalV1CoarseCriticalVertices_of_criticalEdge_endpoint
      A _ edge chart hcriticalEdge hendpoint
  rw [t3Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical]

/-- t3C25FineVertexFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineVertexFlags
    {A : Finset t3Presentation.CoarseTarget}
    (chart : t3Presentation.FineChart) (edge : Fin 4)
    (hfine : t3C25FineEdge edge ∈
      (t3Presentation.gLocalV1InitialState A).fineEdges)
    (hcoarse : t3C25CoarseEdge edge ∈
      (t3Presentation.gLocalV1InitialState A).coarseEdges)
    (hendpoint : chart =
        t3Presentation.fineEdgeLeft (t3C25FineEdge edge) ∨
      chart = t3Presentation.fineEdgeRight (t3C25FineEdge edge)) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.fineVertex chart) =
      handFlags .fine .vertex := by
  have hfineCritical :=
    t3Presentation.mem_gLocalV1FineCriticalEdges_of_mem_of_selfLoop
      A _ _ hfine (t3C25FineSelfLoop _)
  have hcritical :=
    t3Presentation.mem_gLocalV1FineCriticalVertices_of_criticalEdge_endpoint
      A _ _ chart hfineCritical hendpoint
  have hcoarseCritical :=
    t3Presentation.mem_gLocalV1CoarseCriticalEdges_of_mem_of_selfLoop
      A _ _ hcoarse (t3C25CoarseSelfLoop _)
  have hactive :=
    t3Presentation.mem_gLocalV1ActiveFineVertices_of_mapped_criticalEdge_endpoint
      A _ (t3C25FineEdge edge) (t3C25CoarseEdge edge) chart
      hfine hcoarseCritical (t3C25EdgeMap edge) hendpoint
  rw [t3Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, hcritical, hactive]

/-- t3C25CoarseFaceFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CoarseFaceFlags
    {A : Finset t3Presentation.CoarseTarget}
    (face : t3Presentation.CoarseFace) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.coarseFace face) =
      handFlags .coarse .face := by
  have htwin :=
    t3Presentation.gLocalV1CoarseFaceTwinFlag_eq_false_of_key_injective
      A face (t3_faceKey_injective A)
  rw [t3Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, htwin]

/-- t3C25FineFaceFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineFaceFlags
    {A : Finset t3Presentation.CoarseTarget}
    (face : t3Presentation.FineFace) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.fineFace face) =
      handFlags .fine .face := by
  have htwin :=
    t3Presentation.gLocalV1FineFaceTwinFlag_eq_false_of_key_injective
      A face (t3C25FineFaceKeyInjective A)
  rw [t3Presentation.gLocalV1CellFlags_apply]
  simp [handFlags, htwin]

/-- t3C25CoarseChartFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CoarseChartFlags
    {A : Finset t3Presentation.CoarseTarget}
    (chart : t3Presentation.CoarseChart) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.coarseChart chart) =
      handFlags .coarse .chart := by
  rw [t3Presentation.gLocalV1CellFlags_apply]
  rfl

/-- t3C25FineChartFlags is a fixture-local theorem for the registered T3 observation calculation.

Position: it derives the fixture-local role flags without unfolding the generic flag definition; Raw premise/provenance: it combines raw retained membership, endpoints, self-loops, edge maps, and face keys through definition-owner flag theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineChartFlags
    {A : Finset t3Presentation.CoarseTarget}
    (chart : t3Presentation.FineChart) :
    t3Presentation.gLocalV1CellFlags A
        (t3Presentation.gLocalV1InitialState A) (.fineChart chart) =
      handFlags .fine .chart := by
  rw [t3Presentation.gLocalV1CellFlags_apply]
  rfl

/-- t3C25FaceStubHistogram021 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FaceStubHistogram021 :
    gLocalV1Histogram
        ([⟨.face, .slot0⟩, ⟨.face, .slot2⟩, ⟨.face, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.face, .slot0⟩, ⟨.face, .slot1⟩,
        ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25FaceStubHistogram102 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FaceStubHistogram102 :
    gLocalV1Histogram
        ([⟨.face, .slot1⟩, ⟨.face, .slot0⟩, ⟨.face, .slot2⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.face, .slot0⟩, ⟨.face, .slot1⟩,
        ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25FaceStubHistogram210 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FaceStubHistogram210 :
    gLocalV1Histogram
        ([⟨.face, .slot2⟩, ⟨.face, .slot1⟩, ⟨.face, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.face, .slot0⟩, ⟨.face, .slot1⟩,
        ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25EdgeStubHistogram20 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25EdgeStubHistogram20 :
    gLocalV1Histogram
        ([⟨.edge, .slot2⟩, ⟨.edge, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.edge, .slot0⟩, ⟨.edge, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25EdgeStubHistogram21 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25EdgeStubHistogram21 :
    gLocalV1Histogram
        ([⟨.edge, .slot2⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.edge, .slot1⟩, ⟨.edge, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25EdgeStubHistogram10 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25EdgeStubHistogram10 :
    gLocalV1Histogram
        ([⟨.edge, .slot1⟩, ⟨.edge, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25FacePrefixStubHistogram21 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FacePrefixStubHistogram21 :
    gLocalV1Histogram
        ([⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
          ⟨.face, .slot2⟩, ⟨.face, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
        ⟨.face, .slot1⟩, ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25FacePrefixStubHistogram20 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FacePrefixStubHistogram20 :
    gLocalV1Histogram
        ([⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
          ⟨.face, .slot2⟩, ⟨.face, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
        ⟨.face, .slot0⟩, ⟨.face, .slot2⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25FacePrefixStubHistogram10 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FacePrefixStubHistogram10 :
    gLocalV1Histogram
        ([⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
          ⟨.face, .slot1⟩, ⟨.face, .slot0⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram [⟨.vertex, .slot0⟩, ⟨.vertex, .slot1⟩,
        ⟨.face, .slot0⟩, ⟨.face, .slot1⟩] :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

/-- t3C25Perm3_021 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25Perm3_021 {alpha : Type}
    (a b c : alpha) : [a, c, b].Perm [a, b, c] :=
  (List.Perm.swap b c []).cons a

/-- t3C25Perm3_102 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25Perm3_102 {alpha : Type}
    (a b c : alpha) : [b, a, c].Perm [a, b, c] :=
  List.Perm.swap a b [c]

/-- t3C25Perm3_120 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25Perm3_120 {alpha : Type}
    (a b c : alpha) : [b, c, a].Perm [a, b, c] :=
  ((List.Perm.swap a c []).cons b).trans (List.Perm.swap a b [c])

/-- t3C25Perm3_201 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25Perm3_201 {alpha : Type}
    (a b c : alpha) : [c, a, b].Perm [a, b, c] :=
  (List.Perm.swap a c [b]).trans ((List.Perm.swap b c []).cons a)

/-- t3C25Perm3_210 is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25Perm3_210 {alpha : Type}
    (a b c : alpha) : [c, b, a].Perm [a, b, c] := by
  exact (List.Perm.swap b c [a]).trans
    (((List.Perm.swap a c []).cons b).trans (List.Perm.swap a b [c]))

/-- t3C25ExpectedFullBall is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it names the closed full-scope role-indexed ball normal form used as a theorem conclusion; Raw premise/provenance: it is assembled only from the existing handAnchor or handNeutral rooted-ball constructors.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25ExpectedFullBall :
    t3Presentation.GLocalV1Cell targetFull
      (t3Presentation.gLocalV1InitialState targetFull) → GLocalV1RootedBall
  | .coarseChart chart => if chart = t3C25CoarseChart 0 then
      handAnchorChartBall .coarse [0] [0]
    else handNeutralChartBall .coarse [0, 1] [0, 1]
  | .coarseVertex chart => if chart = t3C25CoarseChart 0 then
      handAnchorVertexBall .coarse [0] [0]
    else handNeutralVertexBall .coarse [0, 1] [0, 1]
  | .coarseEdge edge => if edge = t3C25CoarseEdge 0 then
      handAnchorEdgeBall .coarse [0] [0]
    else handNeutralEdgeBall .coarse [0, 1] [0, 1]
  | .coarseFace _ => handNeutralFaceBall .coarse [0, 1] [0, 1]
  | .fineChart chart => if chart = t3C25FineChart 0 then
      handAnchorChartBall .fine [0, 1] [0]
    else handNeutralChartBall .fine [2] [1]
  | .fineVertex chart => if chart = t3C25FineChart 0 then
      handAnchorVertexBall .fine [0, 1] [0]
    else handNeutralVertexBall .fine [2] [1]
  | .fineEdge edge => if edge = t3C25FineEdge 0 then
      handAnchorEdgeBall .fine [0, 1] [0]
    else handNeutralEdgeBall .fine [2] [1]
  | .fineFace _ => handNeutralFaceBall .fine [2] [1]

set_option maxHeartbeats 20000000 in
/-- t3C25FullCellLabelOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the member-aware root-label projection of the full-scope normal form; Raw premise/provenance: it evaluates retained raw cells through CellLabel_apply and component owner equations, using the exact cell-list membership premise.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FullCellLabelOfMem
    (root : t3Presentation.GLocalV1Cell targetFull
      (t3Presentation.gLocalV1InitialState targetFull))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetFull
      (t3Presentation.gLocalV1InitialState targetFull)) :
    t3Presentation.gLocalV1CellLabel targetFull
        (t3Presentation.gLocalV1InitialState targetFull)
        t3Presentation.gLocalV1IdentityRelabel root =
      (t3C25ExpectedFullBall root).rootLabel := by
  rw [t3C25CellListFull] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
    t3C25FineChart, t3C25FineEdge, t3C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t3Presentation.gLocalV1CellLabel_apply,
      t3Presentation.gLocalV1CellSide_apply,
      t3Presentation.gLocalV1CellType_apply,
      t3Presentation.gLocalV1CellSupportCodes_apply,
      t3Presentation.gLocalV1CellPiImageCodes_apply,
      t3Presentation.gLocalV1CellMapStatus_apply]
  all_goals try rw [t3C25CoarseChartFlags]
  all_goals try rw [t3C25FineChartFlags]
  all_goals try rw [t3C25CoarseVertexFlags _ (t3C25CoarseEdge 0)
    (by decide +kernel) (by left; rfl)]
  all_goals try rw [t3C25CoarseVertexFlags _ (t3C25CoarseEdge 1)
    (by decide +kernel) (by
      left
      simp [t3Presentation, identitySplitPresentation, edgeChart,
        t3C25CoarseEdge])]
  all_goals try rw [t3C25FineVertexFlags _ 0
    (by decide +kernel) (by decide +kernel) (by left; rfl)]
  all_goals try rw [t3C25FineVertexFlags _ 1
    (by decide +kernel) (by decide +kernel) (by
      left
      simp [t3Presentation, identitySplitPresentation, edgeChart,
        t3C25FineEdge])]
  all_goals try rw [t3C25CoarseEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t3C25FineEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t3C25CoarseFaceFlags]
  all_goals try rw [t3C25FineFaceFlags]
  all_goals
    simp only [t3Presentation.gLocalV1CoarseChartSupport_apply,
      t3Presentation.gLocalV1FineChartSupport_apply,
      t3Presentation.gLocalV1CoarseEdgeSupport_apply,
      t3Presentation.gLocalV1FineEdgeSupport_apply,
      t3Presentation.gLocalV1CoarseFaceSupport_apply,
      t3Presentation.gLocalV1FineFaceSupport_apply]
  all_goals try rw [t3C25FineScopeFull]
  all_goals try rw [t3C25CoarseIdentityCodeFun]
  all_goals try rw [t3C25FineIdentityCodeFun]
  all_goals try simp only [t3_computedFactor_apply]
  all_goals
    simp +decide (config := { maxSteps := 5000000 })
      [t3C25ExpectedFullBall,
        handAnchorChartBall, handAnchorVertexBall, handAnchorEdgeBall,
        handNeutralChartBall, handNeutralVertexBall,
        handNeutralEdgeBall, handNeutralFaceBall,
        handBall, handLabel,
        t3Presentation, identitySplitPresentation,
        targetFull, coarseRead, coarseChartSupport, fineChartSupport,
        edgeChart, t3FaceEdge0, t3FaceEdge1, t3FaceEdge2,
        t3C25CoarseChart, t3C25CoarseEdge,
        t3C25FineChart, t3C25FineEdge, t3C25Sort01Nat]

set_option maxHeartbeats 20000000 in
/-- t3C25FullNeighborHistogramOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FullNeighborHistogramOfMem
    (root : t3Presentation.GLocalV1Cell targetFull
      (t3Presentation.gLocalV1InitialState targetFull))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetFull
      (t3Presentation.gLocalV1InitialState targetFull)) :
    gLocalV1Histogram
        (t3Presentation.gLocalV1NeighborDescriptors targetFull
          (t3Presentation.gLocalV1InitialState targetFull)
          t3Presentation.gLocalV1IdentityRelabel root) =
      (t3C25ExpectedFullBall root).neighborDescriptors := by
  rw [t3C25CellListFull] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
    t3C25FineChart, t3C25FineEdge, t3C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals
    rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [t3Presentation.gLocalV1NeighborDescriptors_eq_of_cellList_eq
      _ _ _ _ _ t3C25CellListFull]
    simp +decide [t3Presentation.gLocalV1IncidenceRelations_apply,
      t3C25FullCellLabelOfMem, t3C25ExpectedFullBall,
      handAnchorChartBall, handAnchorVertexBall, handAnchorEdgeBall,
      handNeutralChartBall, handNeutralVertexBall, handNeutralEdgeBall,
      handNeutralFaceBall, handBall, handDescriptor]
  all_goals
    repeat' rw [t3Presentation.gLocalV1OutwardStubHistogram_eq_of_cellList_eq
      _ _ _ _ _ t3C25CellListFull]
    simp only [t3Presentation.gLocalV1IncidenceRelations_apply,
      t3Presentation.gLocalV1CellType_apply,
      gLocalV1RelationStubSlot_apply]
    simp +decide [t3Presentation, identitySplitPresentation,
      edgeChart, t3FaceEdge0, t3FaceEdge1, t3FaceEdge2,
      t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
      t3C25FineChart, t3C25FineEdge, t3C25FineFace]
  all_goals
    try simp only [t3C25NeutralStubHistogramThreeEqTwo,
      t3C25NeutralEdgeVertexStubHistogram,
      t3C25FaceStubHistogram021, t3C25FaceStubHistogram102,
      t3C25FaceStubHistogram210,
      t3C25EdgeStubHistogram20, t3C25EdgeStubHistogram21,
      t3C25EdgeStubHistogram10,
      t3C25FacePrefixStubHistogram21,
      t3C25FacePrefixStubHistogram20,
      t3C25FacePrefixStubHistogram10]
  all_goals
    first
    | exact gLocalV1Histogram_cons_three_eq_cons_two _ _
    | rfl
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_021 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_102 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_120 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_201 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_210 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_021 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_102 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_120 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_201 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_210 _ _ _).cons _)

/-- t3C25FullRootedBallOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the unified retained-root normal-form theorem for the full-scope scope; Raw premise/provenance: it composes the preceding label and neighbor results through gLocalV1RootedBall_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FullRootedBallOfMem
    (root : t3Presentation.GLocalV1Cell targetFull
      (t3Presentation.gLocalV1InitialState targetFull))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetFull
      (t3Presentation.gLocalV1InitialState targetFull)) :
    t3Presentation.gLocalV1RootedBall targetFull
        (t3Presentation.gLocalV1InitialState targetFull)
        t3Presentation.gLocalV1IdentityRelabel root =
      t3C25ExpectedFullBall root := by
  rw [t3Presentation.gLocalV1RootedBall_apply]
  congr 1
  · exact t3C25FullCellLabelOfMem root hroot
  · exact t3C25FullNeighborHistogramOfMem root hroot

set_option maxHeartbeats 20000000 in
/-- t3FullRootedBallOccurrences is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the public full-scope occurrence endpoint consumed by the T3 observation tail, with clip-two deferred to the outer histogram; Raw premise/provenance: it maps the unified member-aware theorem over the exact owner-evaluated cell list.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3FullRootedBallOccurrences :
    (t3Presentation.gLocalV1CellList targetFull
      (t3Presentation.gLocalV1InitialState targetFull)).map (fun root =>
        t3Presentation.gLocalV1RootedBall targetFull
          (t3Presentation.gLocalV1InitialState targetFull)
          t3Presentation.gLocalV1IdentityRelabel root) =
      rawFullOccurrences 3 := by
  calc
    _ = (t3Presentation.gLocalV1CellList targetFull
          (t3Presentation.gLocalV1InitialState targetFull)).map
          t3C25ExpectedFullBall := by
      apply List.map_congr_left
      intro root hroot
      exact t3C25FullRootedBallOfMem root hroot
    _ = rawFullOccurrences 3 := by
      rw [t3C25CellListFull]
      simp [t3C25ExpectedFullBall, rawFullOccurrences,
        orderedAnchorChartVertex, orderedAnchorEdge,
        orderedNeutralChartVertex, orderedNeutralEdges,
        orderedNeutralFaces, List.replicate_succ,
        t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
        t3C25FineChart, t3C25FineEdge, t3C25FineFace]
      repeat' apply And.intro
      all_goals intro himpossible
      all_goals have hval := congrArg Fin.val himpossible
      all_goals norm_num at hval

/-- t3C25FineScopeA1 is a fixture-local theorem for the registered T3 observation calculation.

Position: it fixes the target-one fine-target scope used by the T3 normal form; Raw premise/provenance: it follows from the registered computed-factor table through gLocalV1FineScopeTargets_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineScopeA1 :
    t3Presentation.gLocalV1FineScopeTargets targetOne =
      {t3C25FineTarget 2} := by
  rw [t3Presentation.gLocalV1FineScopeTargets_apply]
  ext target
  fin_cases target <;>
    simp +decide

/-- t3C25CellListA1 is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the exact retained-cell enumeration for the target-one T3 proof; Raw premise/provenance: it evaluates the registered initial state through gLocalV1CellList_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CellListA1 :
    t3Presentation.gLocalV1CellList targetOne
      (t3Presentation.gLocalV1InitialState targetOne) =
    [.coarseChart (t3C25CoarseChart 1),
     .coarseVertex (t3C25CoarseChart 1),
     .coarseEdge (t3C25CoarseEdge 1),
     .coarseEdge (t3C25CoarseEdge 2),
     .coarseEdge (t3C25CoarseEdge 3),
     .coarseFace (t3C25CoarseFace 0),
     .coarseFace (t3C25CoarseFace 1),
     .coarseFace (t3C25CoarseFace 2),
     .fineChart (t3C25FineChart 1),
     .fineVertex (t3C25FineChart 1),
     .fineEdge (t3C25FineEdge 1),
     .fineEdge (t3C25FineEdge 2),
     .fineEdge (t3C25FineEdge 3),
     .fineFace (t3C25FineFace 0),
     .fineFace (t3C25FineFace 1),
     .fineFace (t3C25FineFace 2)] := by
  rw [t3Presentation.gLocalV1CellList_apply]
  decide +kernel

/-- t3C25ExpectedA1Ball is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it names the closed target-one role-indexed ball normal form used as a theorem conclusion; Raw premise/provenance: it is assembled only from the existing handAnchor or handNeutral rooted-ball constructors.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25ExpectedA1Ball :
    t3Presentation.GLocalV1Cell targetOne
      (t3Presentation.gLocalV1InitialState targetOne) → GLocalV1RootedBall
  | .coarseChart _ => handNeutralChartBall .coarse [1] [1]
  | .coarseVertex _ => handNeutralVertexBall .coarse [1] [1]
  | .coarseEdge _ => handNeutralEdgeBall .coarse [1] [1]
  | .coarseFace _ => handNeutralFaceBall .coarse [1] [1]
  | .fineChart _ => handNeutralChartBall .fine [2] [1]
  | .fineVertex _ => handNeutralVertexBall .fine [2] [1]
  | .fineEdge _ => handNeutralEdgeBall .fine [2] [1]
  | .fineFace _ => handNeutralFaceBall .fine [2] [1]

set_option maxHeartbeats 20000000 in
/-- t3C25A1CellLabelOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the member-aware root-label projection of the target-one normal form; Raw premise/provenance: it evaluates retained raw cells through CellLabel_apply and component owner equations, using the exact cell-list membership premise.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25A1CellLabelOfMem
    (root : t3Presentation.GLocalV1Cell targetOne
      (t3Presentation.gLocalV1InitialState targetOne))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetOne
      (t3Presentation.gLocalV1InitialState targetOne)) :
    t3Presentation.gLocalV1CellLabel targetOne
        (t3Presentation.gLocalV1InitialState targetOne)
        t3Presentation.gLocalV1IdentityRelabel root =
      (t3C25ExpectedA1Ball root).rootLabel := by
  rw [t3C25CellListA1] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
    t3C25FineChart, t3C25FineEdge, t3C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals rcases hroot with rfl | rfl | rfl
  all_goals
    rw [t3Presentation.gLocalV1CellLabel_apply,
      t3Presentation.gLocalV1CellSide_apply,
      t3Presentation.gLocalV1CellType_apply,
      t3Presentation.gLocalV1CellSupportCodes_apply,
      t3Presentation.gLocalV1CellPiImageCodes_apply,
      t3Presentation.gLocalV1CellMapStatus_apply]
  all_goals try rw [t3C25CoarseChartFlags]
  all_goals try rw [t3C25FineChartFlags]
  all_goals try rw [t3C25CoarseVertexFlags _ (t3C25CoarseEdge 1)
    (by decide +kernel) (by
      left
      simp [t3Presentation, identitySplitPresentation, edgeChart,
        t3C25CoarseEdge])]
  all_goals try rw [t3C25FineVertexFlags _ 1
    (by decide +kernel) (by decide +kernel) (by
      left
      simp [t3Presentation, identitySplitPresentation, edgeChart,
        t3C25FineEdge])]
  all_goals try rw [t3C25CoarseEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t3C25FineEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t3C25CoarseFaceFlags]
  all_goals try rw [t3C25FineFaceFlags]
  all_goals
    simp only [t3Presentation.gLocalV1CoarseChartSupport_apply,
      t3Presentation.gLocalV1FineChartSupport_apply,
      t3Presentation.gLocalV1CoarseEdgeSupport_apply,
      t3Presentation.gLocalV1FineEdgeSupport_apply,
      t3Presentation.gLocalV1CoarseFaceSupport_apply,
      t3Presentation.gLocalV1FineFaceSupport_apply]
  all_goals try rw [t3C25FineScopeA1]
  all_goals try rw [t3C25CoarseIdentityCodeFun]
  all_goals try rw [t3C25FineIdentityCodeFun]
  all_goals try simp only [t3_computedFactor_apply]
  all_goals
    simp +decide (config := { maxSteps := 5000000 })
      [t3C25ExpectedA1Ball, handNeutralChartBall,
        handNeutralVertexBall, handNeutralEdgeBall,
        handNeutralFaceBall, handBall, handLabel,
        t3Presentation, identitySplitPresentation,
        targetOne, coarseRead, coarseChartSupport, fineChartSupport,
        edgeChart, t3FaceEdge0, t3FaceEdge1, t3FaceEdge2,
        t3C25FineTarget]

set_option maxHeartbeats 20000000 in
/-- t3C25A1NeighborHistogramOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25A1NeighborHistogramOfMem
    (root : t3Presentation.GLocalV1Cell targetOne
      (t3Presentation.gLocalV1InitialState targetOne))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetOne
      (t3Presentation.gLocalV1InitialState targetOne)) :
    gLocalV1Histogram
        (t3Presentation.gLocalV1NeighborDescriptors targetOne
          (t3Presentation.gLocalV1InitialState targetOne)
          t3Presentation.gLocalV1IdentityRelabel root) =
      (t3C25ExpectedA1Ball root).neighborDescriptors := by
  rw [t3C25CellListA1] at hroot
  rcases root with chart | chart | edge | face | chart | chart | edge | face
  all_goals simp +decide only [List.mem_cons,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq, GLocalV1Cell.fineFace.injEq,
    t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
    t3C25FineChart, t3C25FineEdge, t3C25FineFace,
    reduceCtorEq] at hroot
  all_goals simp_all only [List.not_mem_nil, or_false, false_or]
  all_goals rcases hroot with rfl | rfl | rfl
  all_goals
    rw [t3Presentation.gLocalV1NeighborDescriptors_eq_of_cellList_eq
      _ _ _ _ _ t3C25CellListA1]
    simp +decide [t3Presentation.gLocalV1IncidenceRelations_apply,
      t3C25A1CellLabelOfMem, t3C25ExpectedA1Ball,
      handNeutralChartBall, handNeutralVertexBall, handNeutralEdgeBall,
      handNeutralFaceBall, handBall, handDescriptor]
  all_goals
    repeat' rw [t3Presentation.gLocalV1OutwardStubHistogram_eq_of_cellList_eq
      _ _ _ _ _ t3C25CellListA1]
    simp only [t3Presentation.gLocalV1IncidenceRelations_apply,
      t3Presentation.gLocalV1CellType_apply,
      gLocalV1RelationStubSlot_apply]
    simp +decide [t3Presentation, identitySplitPresentation,
      edgeChart, t3FaceEdge0, t3FaceEdge1, t3FaceEdge2,
      t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
      t3C25FineChart, t3C25FineEdge, t3C25FineFace]
  all_goals
    try simp only [t3C25NeutralStubHistogramThreeEqTwo,
      t3C25NeutralEdgeVertexStubHistogram,
      t3C25FaceStubHistogram021, t3C25FaceStubHistogram102,
      t3C25FaceStubHistogram210,
      t3C25EdgeStubHistogram20, t3C25EdgeStubHistogram21,
      t3C25EdgeStubHistogram10,
      t3C25FacePrefixStubHistogram21,
      t3C25FacePrefixStubHistogram20,
      t3C25FacePrefixStubHistogram10]
  all_goals
    first
    | exact gLocalV1Histogram_cons_three_eq_cons_two _ _
    | rfl
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_021 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_102 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_120 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_201 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_210 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_021 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_102 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_120 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_201 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_210 _ _ _).cons _)

/-- t3C25A1RootedBallOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the unified retained-root normal-form theorem for the target-one scope; Raw premise/provenance: it composes the preceding label and neighbor results through gLocalV1RootedBall_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25A1RootedBallOfMem
    (root : t3Presentation.GLocalV1Cell targetOne
      (t3Presentation.gLocalV1InitialState targetOne))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetOne
      (t3Presentation.gLocalV1InitialState targetOne)) :
    t3Presentation.gLocalV1RootedBall targetOne
        (t3Presentation.gLocalV1InitialState targetOne)
        t3Presentation.gLocalV1IdentityRelabel root =
      t3C25ExpectedA1Ball root := by
  rw [t3Presentation.gLocalV1RootedBall_apply]
  congr 1
  · exact t3C25A1CellLabelOfMem root hroot
  · exact t3C25A1NeighborHistogramOfMem root hroot

set_option maxHeartbeats 20000000 in
/-- t3A1RootedBallOccurrences is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the public target-one occurrence endpoint consumed by the T3 observation tail, with clip-two deferred to the outer histogram; Raw premise/provenance: it maps the unified member-aware theorem over the exact owner-evaluated cell list.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3A1RootedBallOccurrences :
    (t3Presentation.gLocalV1CellList targetOne
      (t3Presentation.gLocalV1InitialState targetOne)).map (fun root =>
        t3Presentation.gLocalV1RootedBall targetOne
          (t3Presentation.gLocalV1InitialState targetOne)
          t3Presentation.gLocalV1IdentityRelabel root) =
      rawA1Occurrences 3 := by
  calc
    _ = (t3Presentation.gLocalV1CellList targetOne
          (t3Presentation.gLocalV1InitialState targetOne)).map
          t3C25ExpectedA1Ball := by
      apply List.map_congr_left
      intro root hroot
      exact t3C25A1RootedBallOfMem root hroot
    _ = rawA1Occurrences 3 := by
      rw [t3C25CellListA1]
      simp [t3C25ExpectedA1Ball, rawA1Occurrences,
        orderedNeutralChartVertex, orderedNeutralEdges,
        orderedNeutralFaces, List.replicate_succ]

/-- t3C25FineScopeA0 is a fixture-local theorem for the registered T3 observation calculation.

Position: it fixes the target-zero fine-target scope used by the T3 normal form; Raw premise/provenance: it follows from the registered computed-factor table through gLocalV1FineScopeTargets_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25FineScopeA0 :
    t3Presentation.gLocalV1FineScopeTargets targetZero =
      {t3C25FineTarget 0, t3C25FineTarget 1} := by
  rw [t3Presentation.gLocalV1FineScopeTargets_apply]
  ext target
  fin_cases target <;>
    simp +decide

/-- t3C25CellListA0 is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the exact retained-cell enumeration for the target-zero T3 proof; Raw premise/provenance: it evaluates the registered initial state through gLocalV1CellList_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25CellListA0 :
    t3Presentation.gLocalV1CellList targetZero
      (t3Presentation.gLocalV1InitialState targetZero) =
    [.coarseChart (t3C25CoarseChart 0),
     .coarseVertex (t3C25CoarseChart 0),
     .coarseChart (t3C25CoarseChart 1),
     .coarseVertex (t3C25CoarseChart 1),
     .coarseEdge (t3C25CoarseEdge 0),
     .coarseEdge (t3C25CoarseEdge 1),
     .coarseEdge (t3C25CoarseEdge 2),
     .coarseEdge (t3C25CoarseEdge 3),
     .coarseFace (t3C25CoarseFace 0),
     .coarseFace (t3C25CoarseFace 1),
     .coarseFace (t3C25CoarseFace 2),
     .fineChart (t3C25FineChart 0),
     .fineVertex (t3C25FineChart 0),
     .fineEdge (t3C25FineEdge 0)] := by
  rw [t3Presentation.gLocalV1CellList_apply]
  decide +kernel

/-- t3C25ExpectedA0Ball is a fixture-local typed normal-form definition for the registered T3 observation calculation.

Position: it names the closed target-zero role-indexed ball normal form used as a theorem conclusion; Raw premise/provenance: it is assembled only from the existing handAnchor or handNeutral rooted-ball constructors.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
private def t3C25ExpectedA0Ball :
    t3Presentation.GLocalV1Cell targetZero
      (t3Presentation.gLocalV1InitialState targetZero) → GLocalV1RootedBall
  | .coarseChart chart => if chart = t3C25CoarseChart 0 then
      handAnchorChartBall .coarse [0] [0]
    else handNeutralChartBall .coarse [0] [0]
  | .coarseVertex chart => if chart = t3C25CoarseChart 0 then
      handAnchorVertexBall .coarse [0] [0]
    else handNeutralVertexBall .coarse [0] [0]
  | .coarseEdge edge => if edge = t3C25CoarseEdge 0 then
      handAnchorEdgeBall .coarse [0] [0]
    else handNeutralEdgeBall .coarse [0] [0]
  | .coarseFace _ => handNeutralFaceBall .coarse [0] [0]
  | .fineChart _ => handAnchorChartBall .fine [0, 1] [0]
  | .fineVertex _ => handAnchorVertexBall .fine [0, 1] [0]
  | .fineEdge _ => handAnchorEdgeBall .fine [0, 1] [0]
  | .fineFace _ => handNeutralFaceBall .fine [] []

set_option maxHeartbeats 20000000 in
/-- t3C25A0CellLabelOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the member-aware root-label projection of the target-zero normal form; Raw premise/provenance: it evaluates retained raw cells through CellLabel_apply and component owner equations, using the exact cell-list membership premise.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25A0CellLabelOfMem
    (root : t3Presentation.GLocalV1Cell targetZero
      (t3Presentation.gLocalV1InitialState targetZero))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetZero
      (t3Presentation.gLocalV1InitialState targetZero)) :
    t3Presentation.gLocalV1CellLabel targetZero
        (t3Presentation.gLocalV1InitialState targetZero)
        t3Presentation.gLocalV1IdentityRelabel root =
      (t3C25ExpectedA0Ball root).rootLabel := by
  rw [t3C25CellListA0] at hroot
  cases root <;> rename_i index <;> fin_cases index
  all_goals simp_all only [List.mem_cons, List.not_mem_nil, or_false, false_or,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq,
    t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
    t3C25FineChart, t3C25FineEdge, reduceCtorEq]
  all_goals
    rw [t3Presentation.gLocalV1CellLabel_apply,
      t3Presentation.gLocalV1CellSide_apply,
      t3Presentation.gLocalV1CellType_apply,
      t3Presentation.gLocalV1CellSupportCodes_apply,
      t3Presentation.gLocalV1CellPiImageCodes_apply,
      t3Presentation.gLocalV1CellMapStatus_apply]
  all_goals try rw [t3C25CoarseChartFlags]
  all_goals try rw [t3C25FineChartFlags]
  all_goals try rw [t3C25CoarseVertexFlags _ (t3C25CoarseEdge 0)
    (by decide +kernel) (by left; rfl)]
  all_goals try rw [t3C25CoarseVertexFlags _ (t3C25CoarseEdge 1)
    (by decide +kernel) (by
      left
      simp [t3Presentation, identitySplitPresentation, edgeChart,
        t3C25CoarseEdge])]
  all_goals try rw [t3C25FineVertexFlags _ 0
    (by decide +kernel) (by decide +kernel) (by left; rfl)]
  all_goals try rw [t3C25CoarseEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t3C25FineEdgeFlags _ (by decide +kernel)]
  all_goals try rw [t3C25CoarseFaceFlags]
  all_goals
    simp only [t3Presentation.gLocalV1CoarseChartSupport_apply,
      t3Presentation.gLocalV1FineChartSupport_apply,
      t3Presentation.gLocalV1CoarseEdgeSupport_apply,
      t3Presentation.gLocalV1FineEdgeSupport_apply,
      t3Presentation.gLocalV1CoarseFaceSupport_apply]
  all_goals try rw [t3C25FineScopeA0]
  all_goals try rw [t3C25CoarseIdentityCodeFun]
  all_goals try rw [t3C25FineIdentityCodeFun]
  all_goals try simp only [t3_computedFactor_apply]
  all_goals
    simp +decide (config := { maxSteps := 5000000 })
      [t3C25ExpectedA0Ball, handAnchorChartBall,
        handNeutralChartBall, handAnchorVertexBall,
        handNeutralVertexBall, handAnchorEdgeBall,
        handNeutralEdgeBall, handNeutralFaceBall,
        handBall, handLabel, t3Presentation, identitySplitPresentation,
        targetZero, coarseRead, coarseChartSupport, fineChartSupport,
        edgeChart, t3FaceEdge0, t3FaceEdge1, t3FaceEdge2,
        t3C25CoarseChart, t3C25CoarseEdge,
        t3C25FineTarget, t3C25Sort01Nat]

/-- t3C25A0NeutralEdgeVertexStubHistogram is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25A0NeutralEdgeVertexStubHistogram :
    gLocalV1Histogram
        ([⟨.chart, .chartAt⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) =
      gLocalV1Histogram
        ([⟨.chart, .chartAt⟩,
          ⟨.edge, .slot0⟩, ⟨.edge, .slot0⟩,
          ⟨.edge, .slot1⟩, ⟨.edge, .slot1⟩] :
          List GLocalV1OutwardStub) :=
  gLocalV1Histogram_eq_of_perm (by decide +kernel)

set_option maxHeartbeats 20000000 in
/-- t3C25A0NeighborHistogramOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it preserves histogram clipping while normalizing a raw finite stub or descriptor order; Raw premise/provenance: it uses literal T3 incidence orders plus generic histogram permutation or clip-two saturation theorems.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25A0NeighborHistogramOfMem
    (root : t3Presentation.GLocalV1Cell targetZero
      (t3Presentation.gLocalV1InitialState targetZero))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetZero
      (t3Presentation.gLocalV1InitialState targetZero)) :
    gLocalV1Histogram
        (t3Presentation.gLocalV1NeighborDescriptors targetZero
          (t3Presentation.gLocalV1InitialState targetZero)
          t3Presentation.gLocalV1IdentityRelabel root) =
      (t3C25ExpectedA0Ball root).neighborDescriptors := by
  rw [t3C25CellListA0] at hroot
  cases root <;> rename_i index <;> fin_cases index
  all_goals simp_all only [List.mem_cons, List.not_mem_nil, or_false, false_or,
    GLocalV1Cell.coarseChart.injEq, GLocalV1Cell.coarseVertex.injEq,
    GLocalV1Cell.coarseEdge.injEq, GLocalV1Cell.coarseFace.injEq,
    GLocalV1Cell.fineChart.injEq, GLocalV1Cell.fineVertex.injEq,
    GLocalV1Cell.fineEdge.injEq,
    t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
    t3C25FineChart, t3C25FineEdge, reduceCtorEq]
  all_goals
    rw [t3Presentation.gLocalV1NeighborDescriptors_eq_of_cellList_eq
      _ _ _ _ _ t3C25CellListA0]
    simp +decide [t3Presentation.gLocalV1IncidenceRelations_apply,
      t3C25A0CellLabelOfMem, t3C25ExpectedA0Ball,
      handAnchorChartBall, handAnchorVertexBall, handAnchorEdgeBall,
      handNeutralChartBall, handNeutralVertexBall, handNeutralEdgeBall,
      handNeutralFaceBall, handBall, handDescriptor]
  all_goals
    repeat' rw [t3Presentation.gLocalV1OutwardStubHistogram_eq_of_cellList_eq
      _ _ _ _ _ t3C25CellListA0]
    simp only [t3Presentation.gLocalV1IncidenceRelations_apply,
      t3Presentation.gLocalV1CellType_apply,
      gLocalV1RelationStubSlot_apply]
    simp +decide [t3Presentation, identitySplitPresentation,
      edgeChart, t3FaceEdge0, t3FaceEdge1, t3FaceEdge2,
      t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
      t3C25FineChart, t3C25FineEdge]
  all_goals
    try simp only [t3C25NeutralStubHistogramThreeEqTwo,
      t3C25A0NeutralEdgeVertexStubHistogram,
      t3C25FaceStubHistogram021, t3C25FaceStubHistogram102,
      t3C25FaceStubHistogram210,
      t3C25EdgeStubHistogram20, t3C25EdgeStubHistogram21,
      t3C25EdgeStubHistogram10,
      t3C25FacePrefixStubHistogram21,
      t3C25FacePrefixStubHistogram20,
      t3C25FacePrefixStubHistogram10]
  all_goals
    first
    | exact gLocalV1Histogram_cons_three_eq_cons_two _ _
    | rfl
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_021 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_102 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_120 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_201 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm (t3C25Perm3_210 _ _ _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_021 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_102 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_120 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_201 _ _ _).cons _)
    | exact gLocalV1Histogram_eq_of_perm ((t3C25Perm3_210 _ _ _).cons _)

/-- t3C25A0RootedBallOfMem is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the unified retained-root normal-form theorem for the target-zero scope; Raw premise/provenance: it composes the preceding label and neighbor results through gLocalV1RootedBall_apply.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3C25A0RootedBallOfMem
    (root : t3Presentation.GLocalV1Cell targetZero
      (t3Presentation.gLocalV1InitialState targetZero))
    (hroot : root ∈ t3Presentation.gLocalV1CellList targetZero
      (t3Presentation.gLocalV1InitialState targetZero)) :
    t3Presentation.gLocalV1RootedBall targetZero
        (t3Presentation.gLocalV1InitialState targetZero)
        t3Presentation.gLocalV1IdentityRelabel root =
      t3C25ExpectedA0Ball root := by
  rw [t3Presentation.gLocalV1RootedBall_apply]
  congr 1
  · exact t3C25A0CellLabelOfMem root hroot
  · exact t3C25A0NeighborHistogramOfMem root hroot

set_option maxHeartbeats 20000000 in
/-- t3A0RootedBallOccurrences is a fixture-local theorem for the registered T3 observation calculation.

Position: it is the public target-zero occurrence endpoint consumed by the T3 observation tail, with clip-two deferred to the outer histogram; Raw premise/provenance: it maps the unified member-aware theorem over the exact owner-evaluated cell list.
No observation value, checker result, uniformity label, or external certificate is supplied. -/
theorem t3A0RootedBallOccurrences :
    (t3Presentation.gLocalV1CellList targetZero
      (t3Presentation.gLocalV1InitialState targetZero)).map (fun root =>
        t3Presentation.gLocalV1RootedBall targetZero
          (t3Presentation.gLocalV1InitialState targetZero)
          t3Presentation.gLocalV1IdentityRelabel root) =
      rawA0Occurrences 3 := by
  calc
    _ = (t3Presentation.gLocalV1CellList targetZero
          (t3Presentation.gLocalV1InitialState targetZero)).map
          t3C25ExpectedA0Ball := by
      apply List.map_congr_left
      intro root hroot
      exact t3C25A0RootedBallOfMem root hroot
    _ = rawA0Occurrences 3 := by
      rw [t3C25CellListA0]
      simp +decide [t3C25ExpectedA0Ball, rawA0Occurrences,
        orderedAnchorChartVertex, orderedAnchorEdge,
        orderedNeutralChartVertex, orderedNeutralEdges,
        orderedNeutralFaces, List.replicate_succ,
        t3C25CoarseChart, t3C25CoarseEdge, t3C25CoarseFace,
        t3C25FineChart, t3C25FineEdge]
      repeat' apply And.intro
      all_goals intro himpossible
      all_goals have hval := congrArg Fin.val himpossible
      all_goals norm_num at hval


/-- T3's target-zero initial rooted-ball histogram is the closed common row.

Position: identity-orbit evaluation for fixed GOAL claim (v)(a). Raw
premise/provenance: the complete retained-cell occurrence theorem and the
permanent histogram normalizer; no expected observation is assumed. -/
theorem c25T3A0InitialBallHistogramIdentity :
    t3Presentation.gLocalV1InitialBallHistogram targetZero
        t3Presentation.gLocalV1IdentityRelabel = commonA0Balls := by
  calc
    _ = gLocalV1Histogram (rawA0Occurrences 3) :=
      t3Presentation.gLocalV1InitialBallHistogram_eq_of_occurrences_eq
        targetZero t3Presentation.gLocalV1IdentityRelabel
          (rawA0Occurrences 3) t3A0RootedBallOccurrences
    _ = commonA0Balls := rawA0Histogram_three_eq_common

/-- T3's target-one initial rooted-ball histogram is the closed common row.

Position: identity-orbit evaluation for claim (v)(a). Raw premise/provenance:
the complete target-one retained-cell occurrence theorem only. -/
theorem c25T3A1InitialBallHistogramIdentity :
    t3Presentation.gLocalV1InitialBallHistogram targetOne
        t3Presentation.gLocalV1IdentityRelabel = commonA1Balls := by
  calc
    _ = gLocalV1Histogram (rawA1Occurrences 3) :=
      t3Presentation.gLocalV1InitialBallHistogram_eq_of_occurrences_eq
        targetOne t3Presentation.gLocalV1IdentityRelabel
          (rawA1Occurrences 3) t3A1RootedBallOccurrences
    _ = commonA1Balls := rawA1Histogram_three_eq_common

/-- T3's full-scope initial rooted-ball histogram is the closed common row.

Position: identity-orbit evaluation for claim (v)(a). Raw premise/provenance:
the complete full-scope retained-cell occurrence theorem only. -/
theorem c25T3FullInitialBallHistogramIdentity :
    t3Presentation.gLocalV1InitialBallHistogram targetFull
        t3Presentation.gLocalV1IdentityRelabel = commonFullBalls := by
  calc
    _ = gLocalV1Histogram (rawFullOccurrences 3) :=
      t3Presentation.gLocalV1InitialBallHistogram_eq_of_occurrences_eq
        targetFull t3Presentation.gLocalV1IdentityRelabel
          (rawFullOccurrences 3) t3FullRootedBallOccurrences
    _ = commonFullBalls := rawFullHistogram_three_eq_common

/-- T6's target-zero initial rooted-ball histogram is the closed common row.

Position: independent identity-orbit evaluation for claim (v)(a). Raw
premise/provenance: the complete T6 occurrence theorem and clip-two
saturation from six repetitions to the common T3 normal form. -/
theorem c25T6A0InitialBallHistogramIdentity :
    t6Presentation.gLocalV1InitialBallHistogram targetZero
        t6Presentation.gLocalV1IdentityRelabel = commonA0Balls := by
  calc
    _ = gLocalV1Histogram (rawA0Occurrences 6) :=
      t6Presentation.gLocalV1InitialBallHistogram_eq_of_occurrences_eq
        targetZero t6Presentation.gLocalV1IdentityRelabel
          (rawA0Occurrences 6) t6A0RootedBallOccurrences
    _ = commonA0Balls := rawA0Histogram_six_eq_common

/-- T6's target-one initial rooted-ball histogram is the closed common row.

Position: independent identity-orbit evaluation for claim (v)(a). Raw
premise/provenance: the complete T6 occurrence theorem and clip-two
saturation of its literal sixfold neutral multiplicity. -/
theorem c25T6A1InitialBallHistogramIdentity :
    t6Presentation.gLocalV1InitialBallHistogram targetOne
        t6Presentation.gLocalV1IdentityRelabel = commonA1Balls := by
  calc
    _ = gLocalV1Histogram (rawA1Occurrences 6) :=
      t6Presentation.gLocalV1InitialBallHistogram_eq_of_occurrences_eq
        targetOne t6Presentation.gLocalV1IdentityRelabel
          (rawA1Occurrences 6) t6A1RootedBallOccurrences
    _ = commonA1Balls := rawA1Histogram_six_eq_common

/-- T6's full-scope initial rooted-ball histogram is the closed common row.

Position: independent identity-orbit evaluation for claim (v)(a). Raw
premise/provenance: the complete full T6 occurrence theorem and permanent
clip-two saturation. -/
theorem c25T6FullInitialBallHistogramIdentity :
    t6Presentation.gLocalV1InitialBallHistogram targetFull
        t6Presentation.gLocalV1IdentityRelabel = commonFullBalls := by
  calc
    _ = gLocalV1Histogram (rawFullOccurrences 6) :=
      t6Presentation.gLocalV1InitialBallHistogram_eq_of_occurrences_eq
        targetFull t6Presentation.gLocalV1IdentityRelabel
          (rawFullOccurrences 6) t6FullRootedBallOccurrences
    _ = commonFullBalls := rawFullHistogram_six_eq_common

/-- T3's terminal rooted-ball histogram at target zero is the common row.

Position: packet-free terminal evaluation for claim (v)(a). Raw
premise/provenance: Cycle 24's directly proved initial packet emptiness and
the independent identity histogram calculation. -/
theorem c25T3A0TerminalBallHistogramIdentity :
    t3Presentation.gLocalV1TerminalBallHistogram targetZero
        t3Presentation.gLocalV1IdentityRelabel = commonA0Balls := by
  rw [t3Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
    targetZero _ t3_targetZero_initial_packet_empty]
  exact c25T3A0InitialBallHistogramIdentity

/-- T3's terminal rooted-ball histogram at target one is the common row.

Position: packet-free terminal evaluation for claim (v)(a), using only raw
initial packet emptiness and the identity histogram calculation. -/
theorem c25T3A1TerminalBallHistogramIdentity :
    t3Presentation.gLocalV1TerminalBallHistogram targetOne
        t3Presentation.gLocalV1IdentityRelabel = commonA1Balls := by
  rw [t3Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
    targetOne _ t3_targetOne_initial_packet_empty]
  exact c25T3A1InitialBallHistogramIdentity

/-- T3's full terminal rooted-ball histogram is the common row.

Position: packet-free terminal evaluation for claim (v)(a), using only raw
initial packet emptiness and the full identity histogram calculation. -/
theorem c25T3FullTerminalBallHistogramIdentity :
    t3Presentation.gLocalV1TerminalBallHistogram targetFull
        t3Presentation.gLocalV1IdentityRelabel = commonFullBalls := by
  rw [t3Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
    targetFull _ t3_targetFull_initial_packet_empty]
  exact c25T3FullInitialBallHistogramIdentity

/-- T6's terminal rooted-ball histogram at target zero is the common row.

Position: packet-free terminal evaluation for claim (v)(a), using the raw T6
packet-emptiness fact and the independently saturated identity histogram. -/
theorem c25T6A0TerminalBallHistogramIdentity :
    t6Presentation.gLocalV1TerminalBallHistogram targetZero
        t6Presentation.gLocalV1IdentityRelabel = commonA0Balls := by
  rw [t6Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
    targetZero _ t6_targetZero_initial_packet_empty]
  exact c25T6A0InitialBallHistogramIdentity

/-- T6's terminal rooted-ball histogram at target one is the common row.

Position: packet-free terminal evaluation for claim (v)(a), using the raw T6
packet-emptiness fact and the independently saturated identity histogram. -/
theorem c25T6A1TerminalBallHistogramIdentity :
    t6Presentation.gLocalV1TerminalBallHistogram targetOne
        t6Presentation.gLocalV1IdentityRelabel = commonA1Balls := by
  rw [t6Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
    targetOne _ t6_targetOne_initial_packet_empty]
  exact c25T6A1InitialBallHistogramIdentity

/-- T6's full terminal rooted-ball histogram is the common row.

Position: packet-free terminal evaluation for claim (v)(a), using the raw T6
packet-emptiness fact and the independently saturated full histogram. -/
theorem c25T6FullTerminalBallHistogramIdentity :
    t6Presentation.gLocalV1TerminalBallHistogram targetFull
        t6Presentation.gLocalV1IdentityRelabel = commonFullBalls := by
  rw [t6Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
    targetFull _ t6_targetFull_initial_packet_empty]
  exact c25T6FullInitialBallHistogramIdentity

/-- T3's terminal histogram under the fine swap is the common row at every
specified target-zero scope.

Position: generated-orbit evaluation for claim (v)(a). Raw
premise/provenance: the pointwise cell-label swap theorem, raw packet
emptiness, and the independent identity calculation. -/
theorem c25T3A0TerminalBallHistogramSwap :
    t3Presentation.gLocalV1TerminalBallHistogram targetZero c25T3SwapRelabel =
      commonA0Balls := by
  rw [t3Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
      targetZero _ t3_targetZero_initial_packet_empty,
    t3InitialBallHistogramSwapEq]
  exact c25T3A0InitialBallHistogramIdentity

/-- T3's target-one terminal histogram under the fine swap is the common row.

Position: generated-orbit evaluation for claim (v)(a), with only raw
packet-emptiness and proved label invariance as premises. -/
theorem c25T3A1TerminalBallHistogramSwap :
    t3Presentation.gLocalV1TerminalBallHistogram targetOne c25T3SwapRelabel =
      commonA1Balls := by
  rw [t3Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
      targetOne _ t3_targetOne_initial_packet_empty,
    t3InitialBallHistogramSwapEq]
  exact c25T3A1InitialBallHistogramIdentity

/-- T3's full terminal histogram under the fine swap is the common row.

Position: generated-orbit evaluation for claim (v)(a), with only raw
packet-emptiness and proved label invariance as premises. -/
theorem c25T3FullTerminalBallHistogramSwap :
    t3Presentation.gLocalV1TerminalBallHistogram targetFull c25T3SwapRelabel =
      commonFullBalls := by
  rw [t3Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
      targetFull _ t3_targetFull_initial_packet_empty,
    t3InitialBallHistogramSwapEq]
  exact c25T3FullInitialBallHistogramIdentity

/-- T6's target-zero terminal histogram under the fine swap is the common row.

Position: generated-orbit evaluation for claim (v)(a), with raw T6
packet-emptiness and proved label invariance as the only material inputs. -/
theorem c25T6A0TerminalBallHistogramSwap :
    t6Presentation.gLocalV1TerminalBallHistogram targetZero c25T6SwapRelabel =
      commonA0Balls := by
  rw [t6Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
      targetZero _ t6_targetZero_initial_packet_empty,
    t6InitialBallHistogramSwapEq]
  exact c25T6A0InitialBallHistogramIdentity

/-- T6's target-one terminal histogram under the fine swap is the common row.

Position: generated-orbit evaluation for claim (v)(a), with raw T6
packet-emptiness and proved label invariance as the only material inputs. -/
theorem c25T6A1TerminalBallHistogramSwap :
    t6Presentation.gLocalV1TerminalBallHistogram targetOne c25T6SwapRelabel =
      commonA1Balls := by
  rw [t6Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
      targetOne _ t6_targetOne_initial_packet_empty,
    t6InitialBallHistogramSwapEq]
  exact c25T6A1InitialBallHistogramIdentity

/-- T6's full terminal histogram under the fine swap is the common row.

Position: generated-orbit evaluation for claim (v)(a), with raw T6
packet-emptiness and proved label invariance as the only material inputs. -/
theorem c25T6FullTerminalBallHistogramSwap :
    t6Presentation.gLocalV1TerminalBallHistogram targetFull c25T6SwapRelabel =
      commonFullBalls := by
  rw [t6Presentation.gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
      targetFull _ t6_targetFull_initial_packet_empty,
    t6InitialBallHistogramSwapEq]
  exact c25T6FullInitialBallHistogramIdentity

/-- T3's identity-relabel candidate is the closed common observation.

Position: independent T3 candidate evaluation for claim (v)(a). Raw
premise/provenance: all condition rows, packet-union rows, and identity
terminal histograms are separately proved before this record assembly. -/
theorem c25T3CandidateIdentity :
    t3Presentation.gLocalV1Candidate
      t3Presentation.gLocalV1IdentityRelabel = commonObservation := by
  rw [t3Presentation.gLocalV1Candidate_apply, t3ConditionVector,
    t3Presentation.gLocalV1WholeRecord_apply, t3FullTargetSubset,
    t3WholeConditions, t3FullPacketKindUnion,
    c25T3FullTerminalBallHistogramIdentity, t3NonemptyTargetSubsets]
  simp only [List.map_cons, List.map_nil]
  rw [t3Presentation.gLocalV1ARecord_apply,
    t3Presentation.gLocalV1ARecord_apply,
    t3Presentation.gLocalV1ARecord_apply,
    t3A0Conditions, t3A1Conditions, t3FullConditions,
    t3A0PacketKindUnion, t3A1PacketKindUnion, t3FullPacketKindUnion,
    c25T3A0TerminalBallHistogramIdentity,
    c25T3A1TerminalBallHistogramIdentity,
    c25T3FullTerminalBallHistogramIdentity]
  rfl

/-- T3's swap-relabel candidate is the closed common observation.

Position: independent T3 orbit evaluation for claim (v)(a). Raw
premise/provenance: the same structural rows as the identity proof plus the
independent all-cell label-invariance theorem. -/
theorem c25T3CandidateSwap :
    t3Presentation.gLocalV1Candidate c25T3SwapRelabel = commonObservation := by
  rw [t3Presentation.gLocalV1Candidate_apply, t3ConditionVector,
    t3Presentation.gLocalV1WholeRecord_apply, t3FullTargetSubset,
    t3WholeConditions, t3FullPacketKindUnion,
    c25T3FullTerminalBallHistogramSwap, t3NonemptyTargetSubsets]
  simp only [List.map_cons, List.map_nil]
  rw [t3Presentation.gLocalV1ARecord_apply,
    t3Presentation.gLocalV1ARecord_apply,
    t3Presentation.gLocalV1ARecord_apply,
    t3A0Conditions, t3A1Conditions, t3FullConditions,
    t3A0PacketKindUnion, t3A1PacketKindUnion, t3FullPacketKindUnion,
    c25T3A0TerminalBallHistogramSwap,
    c25T3A1TerminalBallHistogramSwap,
    c25T3FullTerminalBallHistogramSwap]
  rfl

/-- T6's identity-relabel candidate is the closed common observation.

Position: independent T6 candidate evaluation for claim (v)(a). Raw
premise/provenance: all condition, packet, and independently normalized T6
terminal rows are consumed field by field. -/
theorem c25T6CandidateIdentity :
    t6Presentation.gLocalV1Candidate
      t6Presentation.gLocalV1IdentityRelabel = commonObservation := by
  rw [t6Presentation.gLocalV1Candidate_apply, t6ConditionVector,
    t6Presentation.gLocalV1WholeRecord_apply, t6FullTargetSubset,
    t6WholeConditions, t6FullPacketKindUnion,
    c25T6FullTerminalBallHistogramIdentity, t6NonemptyTargetSubsets]
  simp only [List.map_cons, List.map_nil]
  rw [t6Presentation.gLocalV1ARecord_apply,
    t6Presentation.gLocalV1ARecord_apply,
    t6Presentation.gLocalV1ARecord_apply,
    t6A0Conditions, t6A1Conditions, t6FullConditions,
    t6A0PacketKindUnion, t6A1PacketKindUnion, t6FullPacketKindUnion,
    c25T6A0TerminalBallHistogramIdentity,
    c25T6A1TerminalBallHistogramIdentity,
    c25T6FullTerminalBallHistogramIdentity]
  rfl

/-- T6's swap-relabel candidate is the closed common observation.

Position: independent T6 orbit evaluation for claim (v)(a). Raw
premise/provenance: the same T6 structural rows plus the proved all-cell
label-invariance theorem. -/
theorem c25T6CandidateSwap :
    t6Presentation.gLocalV1Candidate c25T6SwapRelabel = commonObservation := by
  rw [t6Presentation.gLocalV1Candidate_apply, t6ConditionVector,
    t6Presentation.gLocalV1WholeRecord_apply, t6FullTargetSubset,
    t6WholeConditions, t6FullPacketKindUnion,
    c25T6FullTerminalBallHistogramSwap, t6NonemptyTargetSubsets]
  simp only [List.map_cons, List.map_nil]
  rw [t6Presentation.gLocalV1ARecord_apply,
    t6Presentation.gLocalV1ARecord_apply,
    t6Presentation.gLocalV1ARecord_apply,
    t6A0Conditions, t6A1Conditions, t6FullConditions,
    t6A0PacketKindUnion, t6A1PacketKindUnion, t6FullPacketKindUnion,
    c25T6A0TerminalBallHistogramSwap,
    c25T6A1TerminalBallHistogramSwap,
    c25T6FullTerminalBallHistogramSwap]
  rfl

/-- The registered T3 presentation evaluates to the closed common structural
observation.

Position: primary T3 evaluation for fixed GOAL claim (v)(a). Raw
premise/provenance: exhaustive generated relabel membership plus the two
independent candidate normal forms; the comparator is never opened. -/
theorem t3_obsG_eq_commonObservation :
    t3Presentation.obsG = commonObservation := by
  apply t3Presentation.obsG_eq_of_forall_mem_targetRelabels_candidate_eq
  intro relabel hmem
  rw [c25T3MemTargetRelabels_iff] at hmem
  rcases hmem with rfl | rfl
  · exact c25T3CandidateIdentity
  · exact c25T3CandidateSwap

/-- The registered T6 presentation evaluates to the same closed structural
observation.

Position: primary independent T6 evaluation for fixed GOAL claim (v)(a). Raw
premise/provenance: exhaustive generated relabel membership plus the two T6
candidate normal forms; the comparator is never opened. -/
theorem t6_obsG_eq_commonObservation :
    t6Presentation.obsG = commonObservation := by
  apply t6Presentation.obsG_eq_of_forall_mem_targetRelabels_candidate_eq
  intro relabel hmem
  rw [c25T6MemTargetRelabels_iff] at hmem
  rcases hmem with rfl | rfl
  · exact c25T6CandidateIdentity
  · exact c25T6CandidateSwap

/-- The registered T3 and T6 inputs have exactly the same permanent
`G_local-v1` observation.

Position: fixed GOAL claim (v)(a). It combines two independently proved full
evaluations; the common normal form contains no presentation identity,
checker result, semantic label, H1 value, or external certificate. -/
theorem t3_obsG_eq_t6_obsG :
    t3Presentation.obsG = t6Presentation.obsG := by
  rw [t3_obsG_eq_commonObservation, t6_obsG_eq_commonObservation]

end GLocalV1T3T6Witnesses
end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.GLocalV1T3T6Witnesses
