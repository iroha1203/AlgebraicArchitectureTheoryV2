import Formal.AG.Cohomology.CoverNerve
import Formal.AG.Site.Descent
import ResearchLean.AG.QualitySurface.SemanticRepairSheafH1

/-!
Cycle 1 evidence for `G-aat-quality-surface-05`.

This file anchors the true-sheaf `H1` target in an explicit finite cover
surface.  The cover records selected charts, pairwise-overlap components, and
triple-overlap components with their boundary edges.  The associated Cech data
then feeds `SemanticRepairSheafH1Envelope` through explicit
`delta1_delta0_eq_zero` and residual-cocycle witnesses.

The cycle intentionally stops before the target theorem: sheaf condition,
semantic faithfulness, exactness, effective descent, `[residual] = 0`, and
global semantic repair coherence are not hidden in the cover.
-/

universe u v w x y z r

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairTrueSheafH1

open SemanticRepairSheafH1
open SemanticRepairObstructionTower
open SemanticRepairGluingComplex
open CategoryTheory
open Opposite

/-! ## Finite cover and triple-overlap surface -/

/--
A finite/small semantic repair cover over a semantic repair site.

The fields are input geometry only: selected cover charts, selected pairwise
overlap components, selected triple-overlap components, and the boundary edges
of each triple overlap.  No global repair certificate, obstruction vanishing,
or effective descent condition is stored here.
-/
structure SemanticRepairCover
    {Atom : Type u}
    (site : SemanticRepairSite.{u, v} Atom) where
  CoverChart : Type w
  chart : CoverChart -> site.Chart
  chartOrder : List CoverChart
  chart_complete : forall chart, chart ∈ chartOrder
  Overlap : CoverChart -> CoverChart -> Type w
  overlapOrder :
    List (Sigma fun pair : CoverChart × CoverChart =>
      Overlap pair.1 pair.2)
  overlap_complete :
    forall left right (overlap : Overlap left right),
      Sigma.mk (left, right) overlap ∈ overlapOrder
  TripleOverlap : CoverChart -> CoverChart -> CoverChart -> Type w
  tripleEdge01 :
    forall {i j k}, TripleOverlap i j k -> Overlap i j
  tripleEdge12 :
    forall {i j k}, TripleOverlap i j k -> Overlap j k
  tripleEdge02 :
    forall {i j k}, TripleOverlap i j k -> Overlap i k
  /-- Selected overlap component for every ordered chart pair. -/
  selectedOverlap : forall left right, Overlap left right
  /-- Selected triple-overlap component for every ordered chart triple. -/
  selectedTriple : forall i j k, TripleOverlap i j k
  selectedOverlap_eq_tripleEdge01 : forall i j k,
    selectedOverlap i j = tripleEdge01 (selectedTriple i j k)
  selectedOverlap_eq_tripleEdge12 : forall i j k,
    selectedOverlap j k = tripleEdge12 (selectedTriple i j k)
  selectedOverlap_eq_tripleEdge02 : forall i j k,
    selectedOverlap i k = tripleEdge02 (selectedTriple i j k)
  tripleOrder :
    List (Sigma fun triple : CoverChart × CoverChart × CoverChart =>
      TripleOverlap triple.1 triple.2.1 triple.2.2)
  triple_complete :
    forall i j k (triple : TripleOverlap i j k),
      Sigma.mk (i, j, k) triple ∈ tripleOrder

/-- Every selected cover chart is listed in the finite cover order. -/
theorem coverChart_mem
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site)
    (chart : cover.CoverChart) :
    chart ∈ cover.chartOrder :=
  cover.chart_complete chart

/-- Every selected pairwise-overlap component is listed in the finite cover. -/
theorem coverOverlap_mem
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site)
    (left right : cover.CoverChart)
    (overlap : cover.Overlap left right) :
    Sigma.mk (left, right) overlap ∈ cover.overlapOrder :=
  cover.overlap_complete left right overlap

/-- Every selected triple-overlap component is listed in the finite cover. -/
theorem coverTriple_mem
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site)
    (i j k : cover.CoverChart)
    (triple : cover.TripleOverlap i j k) :
    Sigma.mk (i, j, k) triple ∈ cover.tripleOrder :=
  cover.triple_complete i j k triple

/--
Read the semantic repair cover as the generic cover-nerve surface.

The generic `CoverNerve` only asks for selected edge and face components; the
repair cover supplies those from pairwise and triple overlaps.
-/
def toCoverNerve
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site) :
    AAT.AG.Cohomology.CoverNerve.{w} where
  Chart := cover.CoverChart
  EdgeComponent :=
    Sigma fun pair : cover.CoverChart × cover.CoverChart =>
      cover.Overlap pair.1 pair.2
  FaceComponent :=
    Sigma fun triple : cover.CoverChart × cover.CoverChart × cover.CoverChart =>
      cover.TripleOverlap triple.1 triple.2.1 triple.2.2
  edgeLeft edge := edge.1.1
  edgeRight edge := edge.1.2
  faceEdge0 face :=
    Sigma.mk (face.1.1, face.1.2.1)
      (cover.tripleEdge01 face.2)
  faceEdge1 face :=
    Sigma.mk (face.1.2.1, face.1.2.2)
      (cover.tripleEdge12 face.2)
  faceEdge2 face :=
    Sigma.mk (face.1.1, face.1.2.2)
      (cover.tripleEdge02 face.2)
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := by
    intro _edge
    trivial
  faceTripleOverlapComponent_holds := by
    intro _face
    trivial

/-- Pairwise overlaps become selected edge components of the cover nerve. -/
theorem coverNerve_edge_selected
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site)
    (edge : (toCoverNerve cover).EdgeComponent) :
    (toCoverNerve cover).edgeOverlapComponent edge :=
  AAT.AG.Cohomology.CoverNerve.edge_component_selected
    (toCoverNerve cover) edge

/-- Triple overlaps become selected face components of the cover nerve. -/
theorem coverNerve_face_selected
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site)
    (face : (toCoverNerve cover).FaceComponent) :
    (toCoverNerve cover).faceTripleOverlapComponent face :=
  AAT.AG.Cohomology.CoverNerve.face_component_selected
    (toCoverNerve cover) face

/-! ## Cover-indexed Cech data feeding the sheaf `H1` envelope -/

/--
Cover-indexed Cech data for the semantic residual coefficient sheaf.

The two compatibility fields are the explicit restriction-functoriality
witnesses needed for the first Cech differential: boundaries are cocycles and
the selected residual is a cocycle.  They do not assert residual vanishing or
global repair coherence.
-/
structure SemanticRepairCoverCechData
    {Atom : Type u}
    (site : SemanticRepairSite.{u, v} Atom)
    (_cover : SemanticRepairCover.{u, v, w} site) where
  C0 : Type z
  C1 : Type x
  C2 : Type y
  c0Order : List C0
  c1Order : List C1
  zero1 : C1
  zero2 : C2
  delta0 : C0 -> C1
  delta1 : C1 -> C2
  residual : C1
  delta1_delta0_eq_zero :
    forall primitive, delta1 (delta0 primitive) = zero2
  residual_cocycle :
    delta1 residual = zero2

/-- Cover-indexed Cech data with an explicit zero-cocycle witness. -/
structure SemanticRepairCoverCechDataWithZero
    {Atom : Type u}
    (site : SemanticRepairSite.{u, v} Atom)
    (cover : SemanticRepairCover.{u, v, w} site) extends
      SemanticRepairCoverCechData.{u, v, w, x, y, z} site cover where
  zero1_cocycle : delta1 zero1 = zero2

/-- Convert cover Cech data with zero into the coefficient sheaf surface. -/
def toCoefficientSheafWithZero
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {cover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverCechDataWithZero.{u, v, w, x, y, z} site cover) :
    SemanticResidualCoefficientSheaf.{u, v, z, x, y} site where
  C0 := data.C0
  C1 := data.C1
  C2 := data.C2
  c0Order := data.c0Order
  c1Order := data.c1Order
  zero1 := data.zero1
  zero2 := data.zero2
  delta0 := data.delta0
  delta1 := data.delta1
  zero1_cocycle := data.zero1_cocycle
  delta1_delta0_zero := data.delta1_delta0_eq_zero
  residual := data.residual
  residual_cocycle := data.residual_cocycle

/-- Cover restriction functoriality gives `delta1 (delta0 primitive) = 0`. -/
theorem cover_delta1_delta0_eq_zero
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {cover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverCechDataWithZero.{u, v, w, x, y, z} site cover)
    (primitive : data.C0) :
    data.delta1 (data.delta0 primitive) = data.zero2 :=
  data.delta1_delta0_eq_zero primitive

/-- The selected residual supplied by the cover data is a Cech 1-cocycle. -/
theorem cover_residual_cocycle_wellDefined
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {cover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverCechDataWithZero.{u, v, w, x, y, z} site cover) :
    data.delta1 data.residual = data.zero2 :=
  data.residual_cocycle

/--
Envelope data whose coefficient sheaf is produced from the explicit cover
Cech data.  The remaining fields are quotient/exactness surface data; they are
kept separate from cover membership so that later audits can distinguish input
geometry from material premises.
-/
structure SemanticRepairCoverH1EnvelopeData
    (Atom : Type u) where
  site : SemanticRepairSite.{u, v} Atom
  cover : SemanticRepairCover.{u, v, w} site
  cech :
    SemanticRepairCoverCechDataWithZero.{u, v, w, x, y, z} site cover
  primitiveSemanticallyClosed : cech.C0 -> Prop
  torsorObstruction : Bool
  higherObstruction : Bool
  stackObstruction : Bool
  finiteShadow : cech.C1 -> Bool
  finiteShadow_boundary_zero :
    forall primitive, finiteShadow (cech.delta0 primitive) = false
  cohomologous : cech.C1 -> cech.C1 -> Prop
  cohomologous_refl : forall cochain, cohomologous cochain cochain
  cohomologous_symm :
    forall {left right}, cohomologous left right -> cohomologous right left
  cohomologous_trans :
    forall {left middle right},
      cohomologous left middle ->
        cohomologous middle right ->
          cohomologous left right
  boundary_cohomologous_zero :
    forall primitive, cohomologous (cech.delta0 primitive) cech.zero1
  exact_boundary_of_cohomologous_zero :
    forall cochain,
      cech.delta1 cochain = cech.zero2 ->
        cohomologous cochain cech.zero1 ->
          exists primitive, cech.delta0 primitive = cochain

/-- Build the existing sheaf `H1` envelope from explicit cover Cech data. -/
def toSheafH1Envelope
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) :
    SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom where
  site := data.site
  coefficient := toCoefficientSheafWithZero data.cech
  primitiveSemanticallyClosed := data.primitiveSemanticallyClosed
  torsorObstruction := data.torsorObstruction
  higherObstruction := data.higherObstruction
  stackObstruction := data.stackObstruction
  finiteShadow := data.finiteShadow
  finiteShadow_boundary_zero := data.finiteShadow_boundary_zero
  cohomologous := data.cohomologous
  cohomologous_refl := data.cohomologous_refl
  cohomologous_symm := data.cohomologous_symm
  cohomologous_trans := data.cohomologous_trans
  boundary_cohomologous_zero := data.boundary_cohomologous_zero
  exact_boundary_of_cohomologous_zero :=
    data.exact_boundary_of_cohomologous_zero

/-- The cover-produced envelope has the explicit finite triple-overlap boundary law. -/
theorem coverEnvelope_delta1_delta0_eq_zero
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (primitive : (toSheafH1Envelope data).coefficient.C0) :
    (toSheafH1Envelope data).coefficient.delta1
        ((toSheafH1Envelope data).coefficient.delta0 primitive) =
      (toSheafH1Envelope data).coefficient.zero2 :=
  data.cech.delta1_delta0_eq_zero primitive

/-- The cover-produced envelope has a well-defined residual 1-cocycle. -/
theorem coverEnvelope_residual_cocycle_wellDefined
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) :
    CechZ1 (toSheafH1Envelope data)
      (toSheafH1Envelope data).coefficient.residual :=
  data.cech.residual_cocycle

/-- Cycle 1 theorem package: finite cover enumeration feeds the sheaf `H1` cocycle surface. -/
theorem semanticRepairCoverH1_cycle1_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) :
    (forall chart : data.cover.CoverChart,
      chart ∈ data.cover.chartOrder) /\
      (forall left right (overlap : data.cover.Overlap left right),
        Sigma.mk (left, right) overlap ∈ data.cover.overlapOrder) /\
      (forall i j k (triple : data.cover.TripleOverlap i j k),
        Sigma.mk (i, j, k) triple ∈ data.cover.tripleOrder) /\
      (forall primitive : (toSheafH1Envelope data).coefficient.C0,
        CechZ1 (toSheafH1Envelope data)
          ((toSheafH1Envelope data).coefficient.delta0 primitive)) /\
      CechZ1 (toSheafH1Envelope data)
        (toSheafH1Envelope data).coefficient.residual := by
  exact
    ⟨data.cover.chart_complete,
      data.cover.overlap_complete,
      data.cover.triple_complete,
      coverEnvelope_delta1_delta0_eq_zero data,
      coverEnvelope_residual_cocycle_wellDefined data⟩

/-! ## Cover-produced semantic faithfulness and exactness discharge -/

/--
Semantic faithfulness certificate for a cover-produced sheaf `H1` envelope.

The certificate only says that boundary primitives are semantically closed.  It
does not store `SemanticRepairH1Zero`, `GlobalSemanticRepairCoherent`, effective
descent, or an obstruction-vanishing premise.
-/
structure SemanticRepairCoverH1ExactnessCertificate
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) where
  semanticFaithful_of_boundary :
    forall primitive,
      data.cech.delta0 primitive = data.cech.residual ->
        data.primitiveSemanticallyClosed primitive

/--
Build the visible sheaf `H1` semantic-faithfulness discharge from a cover
certificate.
-/
def coverEnvelope_sheafH1ExactnessDischarge_of_certificate
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom}
    (certificate : SemanticRepairCoverH1ExactnessCertificate data) :
    SemanticRepairSheafH1ExactnessDischarge (toSheafH1Envelope data) where
  semanticFaithful_of_boundary := by
    intro primitive hboundary
    exact certificate.semanticFaithful_of_boundary primitive hboundary

/--
The cover-produced envelope exposes quotient exactness as zero-class iff
boundary membership.

This theorem uses the explicit `boundary_cohomologous_zero` and
`exact_boundary_of_cohomologous_zero` fields already present in
`SemanticRepairCoverH1EnvelopeData`; it does not assume zero class or global
coherence.
-/
theorem coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (_certificate : SemanticRepairCoverH1ExactnessCertificate data) :
    SemanticRepairH1Zero (toSheafH1Envelope data) <->
      CechB1 (toSheafH1Envelope data)
        (toSheafH1Envelope data).coefficient.residual := by
  exact sheafH1Zero_iff_h1Boundary (toSheafH1Envelope data)

/-- Boundary primitives in the cover-produced envelope are semantically closed. -/
theorem coverEnvelope_semanticFaithful_of_boundary
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom}
    (certificate : SemanticRepairCoverH1ExactnessCertificate data)
    {primitive : (toSheafH1Envelope data).coefficient.C0}
    (hboundary :
      (toSheafH1Envelope data).coefficient.delta0 primitive =
        (toSheafH1Envelope data).coefficient.residual) :
    (toSheafH1Envelope data).primitiveSemanticallyClosed primitive := by
  exact certificate.semanticFaithful_of_boundary primitive hboundary

/--
Cycle 2 theorem package: cover-produced envelopes expose semantic-faithfulness
and quotient-exactness discharge without promoting the target theorem to
completion.
-/
theorem coverEnvelope_exactnessFaithfulness_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (certificate : SemanticRepairCoverH1ExactnessCertificate data) :
    SemanticRepairSheafH1ExactnessDischarge (toSheafH1Envelope data) /\
      (forall primitive : (toSheafH1Envelope data).coefficient.C0,
        (toSheafH1Envelope data).coefficient.delta0 primitive =
          (toSheafH1Envelope data).coefficient.residual ->
            (toSheafH1Envelope data).primitiveSemanticallyClosed primitive) /\
      (SemanticRepairH1Zero (toSheafH1Envelope data) <->
        CechB1 (toSheafH1Envelope data)
          (toSheafH1Envelope data).coefficient.residual) /\
      (SemanticRepairH1Nonzero (toSheafH1Envelope data) ->
        Not (GlobalSemanticRepairCoherent (toFiniteTower (toSheafH1Envelope data)))) :=
  by
    let discharge :=
      coverEnvelope_sheafH1ExactnessDischarge_of_certificate certificate
    exact
      ⟨discharge,
        fun primitive hboundary =>
          coverEnvelope_semanticFaithful_of_boundary certificate hboundary,
        coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate data certificate,
        no_globalRepairCoherent_of_nonzero_sheafH1
          (toSheafH1Envelope data) discharge⟩

/-! ## Zero `H1` effective descent for the cover-produced envelope -/

/--
Explicit effective-descent evidence for the cover-produced first-layer
envelope.

These fields keep the later finite tokens visible.  The certificate does not
store `SemanticRepairH1Zero`, a boundary primitive, or
`GlobalSemanticRepairCoherent`.
-/
structure SemanticRepairCoverH1EffectiveDescentCertificate
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) where
  torsor_trivial :
    NonabelianTorsorTrivial (toFiniteTower (toSheafH1Envelope data))
  higher_vanishes :
    HigherCoherenceVanishes (toFiniteTower (toSheafH1Envelope data))
  stack_effectively_vanishes :
    StackEffectivelyVanishes (toFiniteTower (toSheafH1Envelope data))

/--
Cover-produced `H1` data in the abelian true-sheaf boundary.

Unlike `SemanticRepairCoverH1EnvelopeData`, this input surface has no
later-layer obstruction fields.  The associated envelope sets the nonabelian,
higher, and stacky tokens to `false` by construction, so the effective-descent
certificate below has concrete provenance rather than being hand supplied.
-/
structure SemanticRepairCoverH1AbelianDescentData
    (Atom : Type u) where
  site : SemanticRepairSite.{u, v} Atom
  cover : SemanticRepairCover.{u, v, w} site
  cech :
    SemanticRepairCoverCechDataWithZero.{u, v, w, x, y, z} site cover
  primitiveSemanticallyClosed : cech.C0 -> Prop
  finiteShadow : cech.C1 -> Bool
  finiteShadow_boundary_zero :
    forall primitive, finiteShadow (cech.delta0 primitive) = false
  cohomologous : cech.C1 -> cech.C1 -> Prop
  cohomologous_refl : forall cochain, cohomologous cochain cochain
  cohomologous_symm :
    forall {left right}, cohomologous left right -> cohomologous right left
  cohomologous_trans :
    forall {left middle right},
      cohomologous left middle ->
        cohomologous middle right ->
          cohomologous left right
  boundary_cohomologous_zero :
    forall primitive, cohomologous (cech.delta0 primitive) cech.zero1
  exact_boundary_of_cohomologous_zero :
    forall cochain,
      cech.delta1 cochain = cech.zero2 ->
        cohomologous cochain cech.zero1 ->
          exists primitive, cech.delta0 primitive = cochain

/- Build the ordinary cover envelope with later obstruction tokens fixed to zero. -/
def SemanticRepairCoverH1AbelianDescentData.toEnvelopeData
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom) :
    SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom where
  site := data.site
  cover := data.cover
  cech := data.cech
  primitiveSemanticallyClosed := data.primitiveSemanticallyClosed
  torsorObstruction := false
  higherObstruction := false
  stackObstruction := false
  finiteShadow := data.finiteShadow
  finiteShadow_boundary_zero := data.finiteShadow_boundary_zero
  cohomologous := data.cohomologous
  cohomologous_refl := data.cohomologous_refl
  cohomologous_symm := data.cohomologous_symm
  cohomologous_trans := data.cohomologous_trans
  boundary_cohomologous_zero := data.boundary_cohomologous_zero
  exact_boundary_of_cohomologous_zero :=
    data.exact_boundary_of_cohomologous_zero

/--
Concrete provenance for effective descent in the abelian true-sheaf boundary.

The three later-layer vanishings are definitional consequences of
`SemanticRepairCoverH1AbelianDescentData.toEnvelopeData`; no theorem argument or
certificate field supplies them.
-/
theorem coverEnvelope_effectiveDescentCertificate_of_abelianDescentData
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom) :
    SemanticRepairCoverH1EffectiveDescentCertificate data.toEnvelopeData := by
  exact ⟨rfl, rfl, rfl⟩

/--
Zero cover-produced sheaf `H1` gives global semantic repair coherence under
explicit effective-descent evidence.
-/
theorem coverEnvelope_globalRepairCoherent_of_sheafH1Zero_effectiveDescent
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (descent :
      SemanticRepairCoverH1EffectiveDescentCertificate data) :
    SemanticRepairH1Zero (toSheafH1Envelope data) ->
      GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data)) := by
  intro hzero
  exact
    globalRepairCoherent_of_sheafH1_zero
      (toSheafH1Envelope data)
      (coverEnvelope_sheafH1ExactnessDischarge_of_certificate faithfulness)
      hzero
      descent.torsor_trivial
      descent.higher_vanishes
      descent.stack_effectively_vanishes

/--
Under explicit effective-descent evidence, global coherence is equivalent to
zero cover-produced sheaf `H1`.

The forward direction reads the first layer from an actual global coherent
certificate.  The reverse direction uses only the visible faithfulness and
effective-descent certificates above.
-/
theorem coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_effectiveDescent
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (descent :
      SemanticRepairCoverH1EffectiveDescentCertificate data) :
    GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data)) <->
      SemanticRepairH1Zero (toSheafH1Envelope data) := by
  constructor
  · intro hglobal
    have htower :
        ObstructionTowerVanishes (toFiniteTower (toSheafH1Envelope data)) :=
      globalRepairCoherent_forces_obstructionTowerVanishes
        (toFiniteTower (toSheafH1Envelope data))
        (layeredAdequacy_of_sheafH1Discharge
          (coverEnvelope_sheafH1ExactnessDischarge_of_certificate
            faithfulness))
        hglobal
    exact
      (h1Vanishes_iff_sheafH1Zero_of_exactEnvelope
        (toSheafH1Envelope data)).1 htower.1
  · exact
      coverEnvelope_globalRepairCoherent_of_sheafH1Zero_effectiveDescent
        data faithfulness descent

/--
Cycle 3 theorem package: zero cover-produced sheaf `H1` effective descent, with
later-layer evidence kept explicit.
-/
theorem coverEnvelope_zeroH1EffectiveDescent_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (descent :
      SemanticRepairCoverH1EffectiveDescentCertificate data) :
    (SemanticRepairH1Zero (toSheafH1Envelope data) ->
      GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower (toSheafH1Envelope data)) <->
        SemanticRepairH1Zero (toSheafH1Envelope data)) /\
      NonabelianTorsorTrivial (toFiniteTower (toSheafH1Envelope data)) /\
      HigherCoherenceVanishes (toFiniteTower (toSheafH1Envelope data)) /\
      StackEffectivelyVanishes (toFiniteTower (toSheafH1Envelope data)) := by
  exact
    ⟨coverEnvelope_globalRepairCoherent_of_sheafH1Zero_effectiveDescent
        data faithfulness descent,
      coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_effectiveDescent
        data faithfulness descent,
      descent.torsor_trivial,
      descent.higher_vanishes,
      descent.stack_effectively_vanishes⟩

/--
Zero cover-produced sheaf `H1` gives global semantic repair coherence in the
abelian true-sheaf boundary with effective descent constructed from the input
data.
-/
theorem coverEnvelope_globalRepairCoherent_of_sheafH1Zero_abelianDescent
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom)
    (faithfulness :
      SemanticRepairCoverH1ExactnessCertificate data.toEnvelopeData) :
    SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData) ->
      GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) := by
  exact
    coverEnvelope_globalRepairCoherent_of_sheafH1Zero_effectiveDescent
      data.toEnvelopeData faithfulness
      (coverEnvelope_effectiveDescentCertificate_of_abelianDescentData data)

/--
In the abelian true-sheaf boundary, the main `H1` gluing equivalence no longer
takes an effective-descent certificate argument: the needed later-layer
vanishings are constructed by `toEnvelopeData`.
-/
theorem coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_abelianDescent
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom)
    (faithfulness :
      SemanticRepairCoverH1ExactnessCertificate data.toEnvelopeData) :
    GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) <->
      SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData) :=
  coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_effectiveDescent
    data.toEnvelopeData faithfulness
    (coverEnvelope_effectiveDescentCertificate_of_abelianDescentData data)

/--
Cycle 9 package: effective descent for the abelian true-sheaf `H1` boundary is
constructed from the cover-produced data, not supplied as a separate
certificate.
-/
theorem coverEnvelope_abelianDescent_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom)
    (faithfulness :
      SemanticRepairCoverH1ExactnessCertificate data.toEnvelopeData) :
    (SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData) ->
      GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) <->
        SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData)) /\
      NonabelianTorsorTrivial
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) := by
  exact
    ⟨coverEnvelope_globalRepairCoherent_of_sheafH1Zero_abelianDescent
        data faithfulness,
      coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_abelianDescent
        data faithfulness,
      rfl, rfl, rfl⟩

/--
Cover-produced abelian data with explicit boundary-exactness provenance.

This input surface does not carry the quotient relation or exactness fields
expected by `SemanticRepairSheafH1Envelope`.  Instead, it gives a concrete
boundary primitive for every cocycle and a semantic-closure transport law for
primitives with the same boundary.  The ordinary envelope relation and
exactness fields are generated below.
-/
structure SemanticRepairCoverH1BoundaryExactAbelianData
    (Atom : Type u) where
  site : SemanticRepairSite.{u, v} Atom
  cover : SemanticRepairCover.{u, v, w} site
  cech :
    SemanticRepairCoverCechDataWithZero.{u, v, w, x, y, z} site cover
  primitiveSemanticallyClosed : cech.C0 -> Prop
  finiteShadow : cech.C1 -> Bool
  finiteShadow_boundary_zero :
    forall primitive, finiteShadow (cech.delta0 primitive) = false
  boundaryPrimitive : cech.C1 -> cech.C0
  boundaryPrimitive_spec :
    forall cochain,
      cech.delta1 cochain = cech.zero2 ->
        cech.delta0 (boundaryPrimitive cochain) = cochain
  boundaryPrimitive_semanticallyClosed :
    forall cochain,
      (hcocycle : cech.delta1 cochain = cech.zero2) ->
        primitiveSemanticallyClosed (boundaryPrimitive cochain)
  primitiveSemanticallyClosed_respects_delta0 :
    forall {left right},
      cech.delta0 left = cech.delta0 right ->
        primitiveSemanticallyClosed left ->
          primitiveSemanticallyClosed right

/--
Generate the abelian descent data from explicit boundary-exact cover data.

The cohomology relation is the equality-or-shared-boundary relation.  Its
exactness witnesses are constructed from `boundaryPrimitive`, so quotient-style
`H1` exactness is no longer supplied as an envelope field by the caller.
-/
def SemanticRepairCoverH1BoundaryExactAbelianData.toAbelianDescentData
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom) :
    SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom where
  site := data.site
  cover := data.cover
  cech := data.cech
  primitiveSemanticallyClosed := data.primitiveSemanticallyClosed
  finiteShadow := data.finiteShadow
  finiteShadow_boundary_zero := data.finiteShadow_boundary_zero
  cohomologous := fun left right =>
    left = right \/
      (exists primitive, data.cech.delta0 primitive = left) /\
        (exists primitive, data.cech.delta0 primitive = right)
  cohomologous_refl := by
    intro cochain
    exact Or.inl rfl
  cohomologous_symm := by
    intro left right hsame
    rcases hsame with hEq | hBoundary
    · exact Or.inl hEq.symm
    · exact Or.inr ⟨hBoundary.2, hBoundary.1⟩
  cohomologous_trans := by
    intro left middle right hleftMiddle hmiddleRight
    rcases hleftMiddle with hEqLeft | hBoundaryLeft
    · subst middle
      exact hmiddleRight
    · rcases hmiddleRight with hEqRight | hBoundaryRight
      · subst right
        exact Or.inr hBoundaryLeft
      · exact Or.inr ⟨hBoundaryLeft.1, hBoundaryRight.2⟩
  boundary_cohomologous_zero := by
    intro primitive
    exact
      Or.inr
        ⟨⟨primitive, rfl⟩,
          ⟨data.boundaryPrimitive data.cech.zero1,
            data.boundaryPrimitive_spec
              data.cech.zero1 data.cech.zero1_cocycle⟩⟩
  exact_boundary_of_cohomologous_zero := by
    intro cochain hcocycle _hsameZero
    exact
      ⟨data.boundaryPrimitive cochain,
        data.boundaryPrimitive_spec cochain hcocycle⟩

/--
Semantic faithfulness / exactness certificate generated from boundary-exact
abelian data.

The selected residual boundary primitive is semantically closed by construction,
and semantic closure is transported to any primitive with the same boundary.
-/
theorem coverEnvelope_exactnessCertificate_of_boundaryExactAbelianData
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom) :
    SemanticRepairCoverH1ExactnessCertificate
      data.toAbelianDescentData.toEnvelopeData := by
  constructor
  intro primitive hboundary
  let selected := data.boundaryPrimitive data.cech.residual
  have hselectedBoundary :
      data.cech.delta0 selected = data.cech.residual :=
    data.boundaryPrimitive_spec
      data.cech.residual data.cech.residual_cocycle
  have hselectedClosed :
      data.primitiveSemanticallyClosed selected :=
    data.boundaryPrimitive_semanticallyClosed
      data.cech.residual data.cech.residual_cocycle
  exact
    data.primitiveSemanticallyClosed_respects_delta0
      (by
        calc
          data.cech.delta0 selected = data.cech.residual := hselectedBoundary
          _ = data.cech.delta0 primitive := hboundary.symm)
      hselectedClosed

/--
In boundary-exact abelian data, both effective descent and semantic
faithfulness / quotient exactness are generated from the input surface.
-/
theorem coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_boundaryExactAbelian
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom) :
    GlobalSemanticRepairCoherent
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
      SemanticRepairH1Zero
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) :=
  coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_abelianDescent
    data.toAbelianDescentData
    (coverEnvelope_exactnessCertificate_of_boundaryExactAbelianData data)

/--
Cycle 10 package: boundary-exact abelian data discharges exactness /
faithfulness provenance as well as effective descent, while leaving selected
AAT sheaf-condition discharge separate.
-/
theorem coverEnvelope_boundaryExactAbelian_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom) :
    (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
        SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      SemanticRepairCoverH1ExactnessCertificate
        data.toAbelianDescentData.toEnvelopeData /\
      SemanticRepairCoverH1EffectiveDescentCertificate
        data.toAbelianDescentData.toEnvelopeData /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) := by
  exact
    ⟨coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_boundaryExactAbelian
        data,
      coverEnvelope_exactnessCertificate_of_boundaryExactAbelianData data,
      coverEnvelope_effectiveDescentCertificate_of_abelianDescentData
        data.toAbelianDescentData,
      rfl, rfl, rfl⟩

/--
Abelian cover data whose `H1` class relation is boundary-generated, without a
primitive selector for every cocycle.

The only distinguished primitive is a zero-boundary witness.  The cohomology
relation generated below says that two cochains are either definitionally equal
or are both explicit boundaries.  Thus a cochain cohomologous to zero carries
its own boundary witness through the relation, rather than through a global
`C1 -> C0` exactness selector.
-/
structure SemanticRepairCoverH1BoundaryRelationAbelianData
    (Atom : Type u) where
  site : SemanticRepairSite.{u, v} Atom
  cover : SemanticRepairCover.{u, v, w} site
  cech :
    SemanticRepairCoverCechDataWithZero.{u, v, w, x, y, z} site cover
  primitiveSemanticallyClosed : cech.C0 -> Prop
  finiteShadow : cech.C1 -> Bool
  finiteShadow_boundary_zero :
    forall primitive, finiteShadow (cech.delta0 primitive) = false
  zeroPrimitive : cech.C0
  zeroPrimitive_boundary : cech.delta0 zeroPrimitive = cech.zero1
  residualSupport : cech.C1 -> Prop
  residual_has_support : residualSupport cech.residual
  boundary_residualSupport_semanticallyClosed :
    forall primitive,
      residualSupport (cech.delta0 primitive) ->
        primitiveSemanticallyClosed primitive

/--
Generate abelian descent data from the boundary-generated relation.

Unlike `SemanticRepairCoverH1BoundaryExactAbelianData`, this construction does
not assume a primitive for every cocycle.  The exactness field required by the
ordinary envelope is obtained by unpacking the boundary witness carried by
`cohomologous cochain zero1`.
-/
def SemanticRepairCoverH1BoundaryRelationAbelianData.toAbelianDescentData
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom where
  site := data.site
  cover := data.cover
  cech := data.cech
  primitiveSemanticallyClosed := data.primitiveSemanticallyClosed
  finiteShadow := data.finiteShadow
  finiteShadow_boundary_zero := data.finiteShadow_boundary_zero
  cohomologous := fun left right =>
    left = right \/
      (exists primitive, data.cech.delta0 primitive = left) /\
        (exists primitive, data.cech.delta0 primitive = right)
  cohomologous_refl := by
    intro cochain
    exact Or.inl rfl
  cohomologous_symm := by
    intro left right hsame
    rcases hsame with hEq | hBoundary
    · exact Or.inl hEq.symm
    · exact Or.inr ⟨hBoundary.2, hBoundary.1⟩
  cohomologous_trans := by
    intro left middle right hleftMiddle hmiddleRight
    rcases hleftMiddle with hEqLeft | hBoundaryLeft
    · subst middle
      exact hmiddleRight
    · rcases hmiddleRight with hEqRight | hBoundaryRight
      · subst right
        exact Or.inr hBoundaryLeft
      · exact Or.inr ⟨hBoundaryLeft.1, hBoundaryRight.2⟩
  boundary_cohomologous_zero := by
    intro primitive
    exact
      Or.inr
        ⟨⟨primitive, rfl⟩,
          ⟨data.zeroPrimitive, data.zeroPrimitive_boundary⟩⟩
  exact_boundary_of_cohomologous_zero := by
    intro cochain _hcocycle hsameZero
    rcases hsameZero with hEqZero | hBoundary
    · exact ⟨data.zeroPrimitive, by simpa [hEqZero] using data.zeroPrimitive_boundary⟩
    · exact hBoundary.1

/--
Semantic faithfulness certificate generated from residual support rather than a
universal boundary selector.

The field `residualSupport` records semantic support on cochains.  If a
primitive has boundary equal to the selected residual, residual support
transports to that boundary and yields semantic closure of the primitive.
-/
theorem coverEnvelope_exactnessCertificate_of_boundaryRelationAbelianData
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    SemanticRepairCoverH1ExactnessCertificate
      data.toAbelianDescentData.toEnvelopeData := by
  constructor
  intro primitive hboundary
  apply data.boundary_residualSupport_semanticallyClosed
  exact hboundary.symm ▸ data.residual_has_support

/--
The boundary-generated abelian relation supplies the true-sheaf `H1` gluing
equivalence without using `boundaryPrimitive : C1 -> C0`.
-/
theorem coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_boundaryRelationAbelian
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    GlobalSemanticRepairCoherent
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
      SemanticRepairH1Zero
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) :=
  coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_abelianDescent
    data.toAbelianDescentData
    (coverEnvelope_exactnessCertificate_of_boundaryRelationAbelianData data)

/--
Cycle 12 package: exactness / faithfulness provenance through a
boundary-generated relation and residual semantic support.

This remains a checkpoint because selected AAT sheaf-condition provenance is
handled separately, but it removes the final-review blocker caused by a
primitive selector for every cocycle.
-/
theorem coverEnvelope_boundaryRelationAbelian_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
        SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      SemanticRepairCoverH1ExactnessCertificate
        data.toAbelianDescentData.toEnvelopeData /\
      SemanticRepairCoverH1EffectiveDescentCertificate
        data.toAbelianDescentData.toEnvelopeData /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) := by
  exact
    ⟨coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_boundaryRelationAbelian
        data,
      coverEnvelope_exactnessCertificate_of_boundaryRelationAbelianData data,
      coverEnvelope_effectiveDescentCertificate_of_abelianDescentData
        data.toAbelianDescentData,
      rfl, rfl, rfl⟩

/--
Canonical boundary-generated same-class relation available in the current Cech
surface.

The present `C0/C1/C2` surface has no additive subtraction on cochains, so this
is not a full additive quotient relation.  It is the canonical zero-class
detector generated by `B1`: two cochains are identified when they are equal or
both are explicit boundaries.
-/
def CechH1BoundarySameClass
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (left right : E.coefficient.C1) : Prop :=
  left = right \/ CechB1 E left /\ CechB1 E right

/-- Canonical boundary-generated zero-class predicate for the current Cech surface. -/
def CechH1BoundaryZeroClass
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (cochain : E.coefficient.C1) : Prop :=
  CechZ1 E cochain /\
    CechH1BoundarySameClass E cochain E.coefficient.zero1

/-- Canonical boundary-generated nonzero predicate for the current Cech surface. -/
def CechH1BoundaryNonzeroClass
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (cochain : E.coefficient.C1) : Prop :=
  CechZ1 E cochain /\
    Not (CechH1BoundarySameClass E cochain E.coefficient.zero1)

/--
Cycle 14 relation provenance: the Cycle 12 relation is exactly the canonical
boundary-generated same-class relation for this Cech surface.
-/
theorem coverEnvelope_boundaryRelation_sameClass_iff_boundarySameClass
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom)
    (left right :
      (toSheafH1Envelope
        data.toAbelianDescentData.toEnvelopeData).coefficient.C1) :
    H1SameClass
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        left right <->
      CechH1BoundarySameClass
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        left right := by
  rfl

/--
The Cycle 12 zero `H1` predicate is the canonical boundary-generated zero-class
predicate.
-/
theorem coverEnvelope_boundaryRelation_sheafH1Zero_iff_boundaryZeroClass
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    SemanticRepairH1Zero
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
      CechH1BoundaryZeroClass
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual := by
  constructor
  · intro hzero
    exact
      ⟨hzero.1,
        (coverEnvelope_boundaryRelation_sameClass_iff_boundarySameClass
          data
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.zero1).1
          hzero.2⟩
  · intro hzero
    exact
      ⟨hzero.1,
        (coverEnvelope_boundaryRelation_sameClass_iff_boundarySameClass
          data
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.zero1).2
          hzero.2⟩

/--
The Cycle 12 nonzero `H1` predicate is the canonical boundary-generated nonzero
predicate.
-/
theorem coverEnvelope_boundaryRelation_sheafH1Nonzero_iff_boundaryNonzeroClass
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    SemanticRepairH1Nonzero
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
      CechH1BoundaryNonzeroClass
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual := by
  constructor
  · intro hnonzero
    refine ⟨hnonzero.1, ?_⟩
    intro hboundaryZero
    exact hnonzero.2
      ((coverEnvelope_boundaryRelation_sameClass_iff_boundarySameClass
        data
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.zero1).2
        hboundaryZero)
  · intro hnonzero
    refine ⟨hnonzero.1, ?_⟩
    intro hsame
    exact hnonzero.2
      ((coverEnvelope_boundaryRelation_sameClass_iff_boundarySameClass
        data
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.zero1).1
        hsame)

/--
For the boundary-generated relation, canonical zero class is equivalent to
being a residual cocycle and an explicit `B1` boundary.
-/
theorem coverEnvelope_boundaryRelation_boundaryZeroClass_iff_cocycle_and_boundary
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    CechH1BoundaryZeroClass
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual <->
      CechZ1
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual /\
      CechB1
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual := by
  constructor
  · intro hzero
    refine ⟨hzero.1, ?_⟩
    rcases hzero.2 with hEq | hBoundary
    · exact
        ⟨data.zeroPrimitive,
          by
            simpa [hEq] using data.zeroPrimitive_boundary⟩
    · exact hBoundary.1
  · intro hboundary
    exact
      ⟨hboundary.1,
        Or.inr
          ⟨hboundary.2,
            ⟨data.zeroPrimitive, data.zeroPrimitive_boundary⟩⟩⟩

/--
Cycle 14 package: quotient-relation provenance for the Cycle 12
boundary-generated relation surface.
-/
theorem coverEnvelope_boundaryRelationQuotientProvenance_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    (forall left right :
      (toSheafH1Envelope
        data.toAbelianDescentData.toEnvelopeData).coefficient.C1,
      H1SameClass
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          left right <->
        CechH1BoundarySameClass
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          left right) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
        CechH1BoundaryZeroClass
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual) /\
      (SemanticRepairH1Nonzero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
        CechH1BoundaryNonzeroClass
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual) /\
      (CechH1BoundaryZeroClass
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual <->
        CechZ1
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual /\
        CechB1
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual) := by
  exact
    ⟨coverEnvelope_boundaryRelation_sameClass_iff_boundarySameClass data,
      coverEnvelope_boundaryRelation_sheafH1Zero_iff_boundaryZeroClass data,
      coverEnvelope_boundaryRelation_sheafH1Nonzero_iff_boundaryNonzeroClass data,
      coverEnvelope_boundaryRelation_boundaryZeroClass_iff_cocycle_and_boundary
        data⟩

/-! ## Explicit AAT sheaf-condition discharge surface -/

/--
A selected AAT sheaf-condition witness attached to a cover-produced semantic
repair envelope.

The AAT site and cover are external evidence.  This certificate records only
the cover-wise sheaf condition.  It does not include `SemanticRepairH1Zero`,
boundary membership, global coherence, or the target equivalence.
-/
structure SemanticRepairCoverH1SheafConditionCertificate
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base) where
  sheafConditionFor : AAT.AG.Site.AATSheafConditionFor S F cover
  envelope_residual_cocycle :
    CechZ1 (toSheafH1Envelope data)
      (toSheafH1Envelope data).coefficient.residual
  envelope_boundary_cocycle :
    forall primitive : (toSheafH1Envelope data).coefficient.C0,
      CechZ1 (toSheafH1Envelope data)
        ((toSheafH1Envelope data).coefficient.delta0 primitive)

/-- Extract the selected cover-wise AAT sheaf condition from the certificate. -/
theorem coverEnvelope_sheafConditionFor_of_certificate
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom}
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (certificate :
      SemanticRepairCoverH1SheafConditionCertificate data S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover :=
  certificate.sheafConditionFor

/-- The selected sheaf condition gives AAT descent for the selected cover. -/
theorem coverEnvelope_descent_of_sheafConditionCertificate
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom}
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (certificate :
      SemanticRepairCoverH1SheafConditionCertificate data S F cover) :
    AAT.AG.Site.AATDescent S F cover :=
  AAT.AG.Site.AATSheafConditionFor.descent
    certificate.sheafConditionFor

/--
Cycle 4 theorem package: the cover-produced semantic repair envelope is paired
with an explicit AAT cover-wise sheaf condition and its descent consequence.
-/
theorem coverEnvelope_sheafConditionDischarge_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1SheafConditionCertificate data S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1 (toSheafH1Envelope data)
        (toSheafH1Envelope data).coefficient.residual /\
      (forall primitive : (toSheafH1Envelope data).coefficient.C0,
        CechZ1 (toSheafH1Envelope data)
          ((toSheafH1Envelope data).coefficient.delta0 primitive)) /\
      (forall chart : data.cover.CoverChart,
        chart ∈ data.cover.chartOrder) /\
      (forall left right (overlap : data.cover.Overlap left right),
        Sigma.mk (left, right) overlap ∈ data.cover.overlapOrder) /\
      (forall i j k (triple : data.cover.TripleOverlap i j k),
        Sigma.mk (i, j, k) triple ∈ data.cover.tripleOrder) := by
  exact
    ⟨coverEnvelope_sheafConditionFor_of_certificate certificate,
      coverEnvelope_descent_of_sheafConditionCertificate certificate,
      certificate.envelope_residual_cocycle,
      certificate.envelope_boundary_cocycle,
      data.cover.chart_complete,
      data.cover.overlap_complete,
      data.cover.triple_complete⟩

/--
Global true-sheaf evidence for the selected AAT cover associated with a
boundary-exact abelian semantic repair surface.

The cover-wise sheaf-condition certificate is not caller supplied; it is
generated from the AAT sheaf condition for the ambient presheaf plus membership
of the selected cover in the AAT topology.
-/
structure SemanticRepairCoverH1TrueSheafConditionCertificate
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base) where
  cover_mem : cover ∈ S.topology base
  sheafCondition : AAT.AG.Site.AATSheafCondition S F

/--
Generate the selected cover-wise sheaf-condition certificate from global
true-sheaf evidence and the cover-produced Cech laws.
-/
theorem coverEnvelope_sheafConditionCertificate_of_trueSheafCondition
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom}
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (certificate :
      SemanticRepairCoverH1TrueSheafConditionCertificate data S F cover) :
    SemanticRepairCoverH1SheafConditionCertificate
      data.toAbelianDescentData.toEnvelopeData S F cover where
  sheafConditionFor :=
    AAT.AG.Site.AATSheafCondition.cover
      certificate.sheafCondition cover certificate.cover_mem
  envelope_residual_cocycle :=
    coverEnvelope_residual_cocycle_wellDefined
      data.toAbelianDescentData.toEnvelopeData
  envelope_boundary_cocycle :=
    coverEnvelope_delta1_delta0_eq_zero
      data.toAbelianDescentData.toEnvelopeData

/--
Cycle 11 package: selected cover-wise AAT sheaf-condition evidence is generated
from global true-sheaf evidence, and the generated certificate is used with the
boundary-exact abelian gluing package.
-/
theorem coverEnvelope_trueSheafBoundaryExactAbelian_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1TrueSheafConditionCertificate data S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
          SemanticRepairH1Zero
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      SemanticRepairCoverH1ExactnessCertificate
        data.toAbelianDescentData.toEnvelopeData /\
      SemanticRepairCoverH1EffectiveDescentCertificate
        data.toAbelianDescentData.toEnvelopeData := by
  let selected :=
    coverEnvelope_sheafConditionCertificate_of_trueSheafCondition
      certificate
  let exactness :=
    coverEnvelope_exactnessCertificate_of_boundaryExactAbelianData data
  exact
    ⟨coverEnvelope_sheafConditionFor_of_certificate selected,
      coverEnvelope_descent_of_sheafConditionCertificate selected,
      coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_boundaryExactAbelian
        data,
      exactness,
      coverEnvelope_effectiveDescentCertificate_of_abelianDescentData
        data.toAbelianDescentData⟩

/-! ## G-02 finite comparison surface -/

/--
Compatibility data comparing a cover-produced sheaf `H1` envelope with a G-02
finite semantic repair-gluing complex.

The comparison records only type-level and differential/residual compatibility.
It does not store `SemanticRepairH1Zero`, `ObstructionClassVanishes`, boundary
membership, semantic faithfulness, or global coherence.
-/
structure SemanticRepairG02FiniteComparison
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (K :
      FiniteSemanticRepairGluingComplex.{u, v, w, z, x} Atom) where
  c0Equiv : (toSheafH1Envelope data).coefficient.C0 ≃ K.C0
  c1Equiv : (toSheafH1Envelope data).coefficient.C1 ≃ K.C1
  delta0_compat :
    forall primitive,
      c1Equiv ((toSheafH1Envelope data).coefficient.delta0 primitive) =
        K.delta0 (c0Equiv primitive)
  residual_compat :
    c1Equiv (toSheafH1Envelope data).coefficient.residual = K.residual

/-- A cover-produced boundary maps to a G-02 finite boundary under compatibility. -/
theorem g02Boundary_of_coverBoundary
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom}
    {K :
      FiniteSemanticRepairGluingComplex.{u, v, w, z, x} Atom}
    (comparison : SemanticRepairG02FiniteComparison data K) :
    CechB1 (toSheafH1Envelope data)
        (toSheafH1Envelope data).coefficient.residual ->
      ObstructionClassVanishes K := by
  intro hboundary
  rcases hboundary with ⟨primitive, hprimitive⟩
  refine ⟨comparison.c0Equiv primitive, ?_⟩
  have hmap :
      comparison.c1Equiv
          ((toSheafH1Envelope data).coefficient.delta0 primitive) =
        comparison.c1Equiv
          (toSheafH1Envelope data).coefficient.residual := by
    rw [hprimitive]
  rw [comparison.delta0_compat primitive, comparison.residual_compat] at hmap
  exact hmap

/-- A G-02 finite boundary pulls back to a cover-produced sheaf boundary. -/
theorem coverBoundary_of_g02Boundary
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom}
    {K :
      FiniteSemanticRepairGluingComplex.{u, v, w, z, x} Atom}
    (comparison : SemanticRepairG02FiniteComparison data K) :
    ObstructionClassVanishes K ->
      CechB1 (toSheafH1Envelope data)
        (toSheafH1Envelope data).coefficient.residual := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hprimitive⟩
  refine ⟨comparison.c0Equiv.symm primitive, ?_⟩
  apply comparison.c1Equiv.injective
  rw [comparison.delta0_compat, comparison.residual_compat]
  simpa using hprimitive

/--
G-02 finite obstruction vanishing is the finite selected-cover shadow of the
cover-produced sheaf `H1` zero class.
-/
theorem coverEnvelope_sheafH1Zero_iff_g02ObstructionVanishes
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (K :
      FiniteSemanticRepairGluingComplex.{u, v, w, z, x} Atom)
    (comparison : SemanticRepairG02FiniteComparison data K) :
    SemanticRepairH1Zero (toSheafH1Envelope data) <->
      ObstructionClassVanishes K := by
  constructor
  · intro hzero
    exact
      g02Boundary_of_coverBoundary comparison
        ((coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
          data faithfulness).1 hzero)
  · intro hvanishes
    exact
      (coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
        data faithfulness).2
        (coverBoundary_of_g02Boundary comparison hvanishes)

/-- Cycle 5 theorem package: G-02 finite comparison for the cover-produced sheaf `H1`. -/
theorem coverEnvelope_g02FiniteComparison_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (K :
      FiniteSemanticRepairGluingComplex.{u, v, w, z, x} Atom)
    (comparison : SemanticRepairG02FiniteComparison data K) :
    (SemanticRepairH1Zero (toSheafH1Envelope data) <->
      ObstructionClassVanishes K) /\
      (CechB1 (toSheafH1Envelope data)
          (toSheafH1Envelope data).coefficient.residual ->
        ObstructionClassVanishes K) /\
      (ObstructionClassVanishes K ->
        CechB1 (toSheafH1Envelope data)
          (toSheafH1Envelope data).coefficient.residual) := by
  exact
    ⟨coverEnvelope_sheafH1Zero_iff_g02ObstructionVanishes
        data faithfulness K comparison,
      g02Boundary_of_coverBoundary comparison,
      coverBoundary_of_g02Boundary comparison⟩

/-! ## ArchSig finite shadow surface -/

/--
The cover-produced sheaf `H1` zero class is read as a trivial bounded finite
shadow by the ArchSig-facing finite obstruction tower.
-/
theorem coverEnvelope_archSigFiniteShadow_of_sheafH1Zero
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) :
    SemanticRepairH1Zero (toSheafH1Envelope data) ->
      FiniteShadowTrivial (toFiniteTower (toSheafH1Envelope data)) := by
  exact finiteTower_h1Shadow_of_sheafH1 (toSheafH1Envelope data)

/--
G-02 finite obstruction vanishing is enough for the ArchSig bounded finite
shadow of the cover-produced package to be trivial.
-/
theorem coverEnvelope_archSigFiniteShadow_of_g02ObstructionVanishes
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (K :
      FiniteSemanticRepairGluingComplex.{u, v, w, z, x} Atom)
    (comparison : SemanticRepairG02FiniteComparison data K) :
    ObstructionClassVanishes K ->
      FiniteShadowTrivial (toFiniteTower (toSheafH1Envelope data)) := by
  intro hvanishes
  exact
    coverEnvelope_archSigFiniteShadow_of_sheafH1Zero data
      ((coverEnvelope_sheafH1Zero_iff_g02ObstructionVanishes
        data faithfulness K comparison).2 hvanishes)

/--
Cycle 6 theorem package: the cover-produced true-sheaf `H1` discharge is visible
to the bounded ArchSig finite shadow, both directly and through the G-02 finite
comparison.
-/
theorem coverEnvelope_archSigFiniteShadow_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (K :
      FiniteSemanticRepairGluingComplex.{u, v, w, z, x} Atom)
    (comparison : SemanticRepairG02FiniteComparison data K) :
    (SemanticRepairH1Zero (toSheafH1Envelope data) ->
      FiniteShadowTrivial (toFiniteTower (toSheafH1Envelope data))) /\
      (ObstructionClassVanishes K ->
        FiniteShadowTrivial (toFiniteTower (toSheafH1Envelope data))) := by
  exact
    ⟨coverEnvelope_archSigFiniteShadow_of_sheafH1Zero data,
      coverEnvelope_archSigFiniteShadow_of_g02ObstructionVanishes
        data faithfulness K comparison⟩

/-! ## Cover-refinement naturality surface -/

/--
A selected finite refinement from a fine semantic repair cover to a coarse one.

The refinement records only cover geometry: selected chart, overlap, and
triple-overlap maps.  It does not carry Cech boundary membership, sheaf `H1`
zero, global repair coherence, or effective descent.
-/
structure SemanticRepairCoverRefinement
    {Atom : Type u}
    (coarse fine :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) where
  chartMap : fine.cover.CoverChart -> coarse.cover.CoverChart
  overlapMap :
    forall {left right},
      fine.cover.Overlap left right ->
        coarse.cover.Overlap (chartMap left) (chartMap right)
  tripleMap :
    forall {i j k},
      fine.cover.TripleOverlap i j k ->
        coarse.cover.TripleOverlap (chartMap i) (chartMap j) (chartMap k)

/--
Compatibility data saying that the selected cover refinement pulls the coarse
cover-produced Cech `H1` envelope back to the fine one.

The comparison records only primitive/cochain pullback and `delta0` / residual
compatibility.  It does not store `SemanticRepairH1Zero`,
`GlobalSemanticRepairCoherent`, effective descent, ArchMap correctness, or
target completion.
-/
structure SemanticRepairCoverH1RefinementComparison
    {Atom : Type u}
    (coarse fine :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom) where
  refinement : SemanticRepairCoverRefinement coarse fine
  primitivePullback :
    (toSheafH1Envelope coarse).coefficient.C0 ->
      (toSheafH1Envelope fine).coefficient.C0
  cochainPullback :
    (toSheafH1Envelope coarse).coefficient.C1 ->
      (toSheafH1Envelope fine).coefficient.C1
  delta0_naturality :
    forall primitive,
      cochainPullback
          ((toSheafH1Envelope coarse).coefficient.delta0 primitive) =
        (toSheafH1Envelope fine).coefficient.delta0
          (primitivePullback primitive)
  residual_naturality :
    cochainPullback (toSheafH1Envelope coarse).coefficient.residual =
      (toSheafH1Envelope fine).coefficient.residual

/-- A coarse boundary pulls back to a fine boundary under cover refinement. -/
theorem coverEnvelope_refinement_boundary_pullback
    {Atom : Type u}
    {coarse fine :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom}
    (comparison :
      SemanticRepairCoverH1RefinementComparison coarse fine) :
    CechB1 (toSheafH1Envelope coarse)
        (toSheafH1Envelope coarse).coefficient.residual ->
      CechB1 (toSheafH1Envelope fine)
        (toSheafH1Envelope fine).coefficient.residual := by
  intro hboundary
  rcases hboundary with ⟨primitive, hprimitive⟩
  refine ⟨comparison.primitivePullback primitive, ?_⟩
  calc
    (toSheafH1Envelope fine).coefficient.delta0
        (comparison.primitivePullback primitive) =
        comparison.cochainPullback
          ((toSheafH1Envelope coarse).coefficient.delta0 primitive) := by
      exact (comparison.delta0_naturality primitive).symm
    _ = comparison.cochainPullback
        (toSheafH1Envelope coarse).coefficient.residual := by
      rw [hprimitive]
    _ = (toSheafH1Envelope fine).coefficient.residual := by
      exact comparison.residual_naturality

/--
Cover refinement preserves the cover-produced sheaf `H1` zero class, once the
coarse and fine exactness/faithfulness discharges are explicit.
-/
theorem coverEnvelope_refinement_sheafH1Zero_pullback
    {Atom : Type u}
    (coarse fine :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (coarseExact : SemanticRepairCoverH1ExactnessCertificate coarse)
    (fineExact : SemanticRepairCoverH1ExactnessCertificate fine)
    (comparison :
      SemanticRepairCoverH1RefinementComparison coarse fine) :
    SemanticRepairH1Zero (toSheafH1Envelope coarse) ->
      SemanticRepairH1Zero (toSheafH1Envelope fine) := by
  intro hzero
  exact
    (coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
      fine fineExact).2
      (coverEnvelope_refinement_boundary_pullback comparison
        ((coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
          coarse coarseExact).1 hzero))

/--
Cycle 7 theorem package: selected finite cover refinement is natural for the
cover-produced true-sheaf `H1` zero predicate.
-/
theorem coverEnvelope_refinementNaturality_package
    {Atom : Type u}
    (coarse fine :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    (coarseExact : SemanticRepairCoverH1ExactnessCertificate coarse)
    (fineExact : SemanticRepairCoverH1ExactnessCertificate fine)
    (comparison :
      SemanticRepairCoverH1RefinementComparison coarse fine) :
    (CechB1 (toSheafH1Envelope coarse)
        (toSheafH1Envelope coarse).coefficient.residual ->
      CechB1 (toSheafH1Envelope fine)
        (toSheafH1Envelope fine).coefficient.residual) /\
      (SemanticRepairH1Zero (toSheafH1Envelope coarse) ->
        SemanticRepairH1Zero (toSheafH1Envelope fine)) /\
      (forall chart : fine.cover.CoverChart,
        comparison.refinement.chartMap chart ∈ coarse.cover.chartOrder) /\
      (forall left right (overlap : fine.cover.Overlap left right),
        Sigma.mk
            (comparison.refinement.chartMap left,
              comparison.refinement.chartMap right)
            (comparison.refinement.overlapMap overlap) ∈
          coarse.cover.overlapOrder) /\
      (forall i j k (triple : fine.cover.TripleOverlap i j k),
        Sigma.mk
            (comparison.refinement.chartMap i,
              comparison.refinement.chartMap j,
              comparison.refinement.chartMap k)
            (comparison.refinement.tripleMap triple) ∈
          coarse.cover.tripleOrder) := by
  exact
    ⟨coverEnvelope_refinement_boundary_pullback comparison,
      coverEnvelope_refinement_sheafH1Zero_pullback
        coarse fine coarseExact fineExact comparison,
      fun chart => coarse.cover.chart_complete
        (comparison.refinement.chartMap chart),
      fun left right overlap => coarse.cover.overlap_complete
        (comparison.refinement.chartMap left)
        (comparison.refinement.chartMap right)
        (comparison.refinement.overlapMap overlap),
      fun i j k triple => coarse.cover.triple_complete
        (comparison.refinement.chartMap i)
        (comparison.refinement.chartMap j)
        (comparison.refinement.chartMap k)
        (comparison.refinement.tripleMap triple)⟩

/-! ## Target theorem package -/

/--
The named true-sheaf `H1` semantic repair-gluing equivalence for the
cover-produced envelope.

All material discharges remain explicit: semantic faithfulness / exactness come
from `faithfulness`, the selected AAT sheaf condition comes from
`sheafCondition`, and later effective-descent tokens come from `descent`.
-/
theorem trueSheafH1_semanticRepairGluing_iff
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (_sheafCondition :
      SemanticRepairCoverH1SheafConditionCertificate data S F cover)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (descent :
      SemanticRepairCoverH1EffectiveDescentCertificate data) :
    GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data)) <->
      SemanticRepairH1Zero (toSheafH1Envelope data) :=
  coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_effectiveDescent
    data faithfulness descent

/--
Target theorem package for G-05: the cover-produced residual is a well-defined
1-cocycle, zero sheaf `H1` is equivalent to global semantic repair coherence
under explicit material discharges, nonzero sheaf `H1` rules out global
coherence, and the quotient exactness / effective-descent package is exposed.
-/
theorem trueSheafH1SemanticRepairGluing_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1EnvelopeData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (sheafCondition :
      SemanticRepairCoverH1SheafConditionCertificate data S F cover)
    (faithfulness : SemanticRepairCoverH1ExactnessCertificate data)
    (descent :
      SemanticRepairCoverH1EffectiveDescentCertificate data) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1 (toSheafH1Envelope data)
        (toSheafH1Envelope data).coefficient.residual /\
      (forall primitive : (toSheafH1Envelope data).coefficient.C0,
        CechZ1 (toSheafH1Envelope data)
          ((toSheafH1Envelope data).coefficient.delta0 primitive)) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower (toSheafH1Envelope data)) <->
          SemanticRepairH1Zero (toSheafH1Envelope data)) /\
      (SemanticRepairH1Nonzero (toSheafH1Envelope data) ->
        Not
          (GlobalSemanticRepairCoherent
            (toFiniteTower (toSheafH1Envelope data)))) /\
      (SemanticRepairH1Zero (toSheafH1Envelope data) <->
        CechB1 (toSheafH1Envelope data)
          (toSheafH1Envelope data).coefficient.residual) /\
      (SemanticRepairH1Zero (toSheafH1Envelope data) ->
        GlobalSemanticRepairCoherent
          (toFiniteTower (toSheafH1Envelope data))) := by
  exact
    ⟨coverEnvelope_sheafConditionFor_of_certificate sheafCondition,
      coverEnvelope_descent_of_sheafConditionCertificate sheafCondition,
      sheafCondition.envelope_residual_cocycle,
      sheafCondition.envelope_boundary_cocycle,
      trueSheafH1_semanticRepairGluing_iff
        data sheafCondition faithfulness descent,
      no_globalRepairCoherent_of_nonzero_sheafH1
        (toSheafH1Envelope data)
        (coverEnvelope_sheafH1ExactnessDischarge_of_certificate
          faithfulness),
      coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
        data faithfulness,
      coverEnvelope_globalRepairCoherent_of_sheafH1Zero_effectiveDescent
        data faithfulness descent⟩

/--
Named true-sheaf `H1` semantic repair-gluing equivalence for the abelian
cover-produced boundary.

This strengthens the Cycle 8 surface by removing the hand-supplied `descent`
argument.  Effective descent is generated by
`coverEnvelope_effectiveDescentCertificate_of_abelianDescentData`.
-/
theorem trueSheafH1_semanticRepairGluing_iff_abelianDescent
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom)
    (faithfulness :
      SemanticRepairCoverH1ExactnessCertificate data.toEnvelopeData) :
    GlobalSemanticRepairCoherent
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) <->
      SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData) :=
  coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_abelianDescent
    data faithfulness

/--
Target-adjacent theorem package for the abelian true-sheaf `H1` boundary.

The package still keeps sheaf-condition and faithfulness certificates explicit,
so it is a proof-obligation discharge checkpoint rather than final
`target-theorem-proved`.  Its effective-descent component has concrete
provenance from the abelian cover data.
-/
theorem trueSheafH1SemanticRepairGluing_abelianDescent_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1AbelianDescentData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (sheafCondition :
      SemanticRepairCoverH1SheafConditionCertificate
        data.toEnvelopeData S F cover)
    (faithfulness :
      SemanticRepairCoverH1ExactnessCertificate data.toEnvelopeData) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1 (toSheafH1Envelope data.toEnvelopeData)
        (toSheafH1Envelope data.toEnvelopeData).coefficient.residual /\
      (forall primitive : (toSheafH1Envelope data.toEnvelopeData).coefficient.C0,
        CechZ1 (toSheafH1Envelope data.toEnvelopeData)
          ((toSheafH1Envelope data.toEnvelopeData).coefficient.delta0 primitive)) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) <->
          SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData)) /\
      (SemanticRepairH1Nonzero (toSheafH1Envelope data.toEnvelopeData) ->
        Not
          (GlobalSemanticRepairCoherent
            (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)))) /\
      (SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData) <->
        CechB1 (toSheafH1Envelope data.toEnvelopeData)
          (toSheafH1Envelope data.toEnvelopeData).coefficient.residual) /\
      (SemanticRepairH1Zero (toSheafH1Envelope data.toEnvelopeData) ->
        GlobalSemanticRepairCoherent
          (toFiniteTower (toSheafH1Envelope data.toEnvelopeData))) /\
      NonabelianTorsorTrivial
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower (toSheafH1Envelope data.toEnvelopeData)) := by
  exact
    ⟨coverEnvelope_sheafConditionFor_of_certificate sheafCondition,
      coverEnvelope_descent_of_sheafConditionCertificate sheafCondition,
      sheafCondition.envelope_residual_cocycle,
      sheafCondition.envelope_boundary_cocycle,
      trueSheafH1_semanticRepairGluing_iff_abelianDescent
        data faithfulness,
      no_globalRepairCoherent_of_nonzero_sheafH1
        (toSheafH1Envelope data.toEnvelopeData)
        (coverEnvelope_sheafH1ExactnessDischarge_of_certificate
          faithfulness),
      coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
        data.toEnvelopeData faithfulness,
      coverEnvelope_globalRepairCoherent_of_sheafH1Zero_abelianDescent
        data faithfulness,
      rfl, rfl, rfl⟩

/--
Named true-sheaf `H1` semantic repair-gluing equivalence for boundary-exact
abelian cover data.

This strengthens the abelian descent checkpoint by generating both
effective-descent evidence and semantic faithfulness / quotient exactness from
the boundary-exact input surface.
-/
theorem trueSheafH1_semanticRepairGluing_iff_boundaryExactAbelian
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom) :
    GlobalSemanticRepairCoherent
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
      SemanticRepairH1Zero
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) :=
  coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_boundaryExactAbelian
    data

/--
Target-adjacent theorem package for boundary-exact abelian cover data.

The package still keeps selected AAT sheaf-condition evidence explicit, so it
is a checkpoint rather than final `target-theorem-proved`.
-/
theorem trueSheafH1SemanticRepairGluing_boundaryExactAbelian_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (sheafCondition :
      SemanticRepairCoverH1SheafConditionCertificate
        data.toAbelianDescentData.toEnvelopeData S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual /\
      (forall primitive :
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.C0,
        CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          ((toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.delta0
              primitive)) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
          SemanticRepairH1Zero
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      (SemanticRepairH1Nonzero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        Not
          (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)))) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
        CechB1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData))) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) := by
  let exactness :=
    coverEnvelope_exactnessCertificate_of_boundaryExactAbelianData data
  exact
    ⟨coverEnvelope_sheafConditionFor_of_certificate sheafCondition,
      coverEnvelope_descent_of_sheafConditionCertificate sheafCondition,
      sheafCondition.envelope_residual_cocycle,
      sheafCondition.envelope_boundary_cocycle,
      trueSheafH1_semanticRepairGluing_iff_boundaryExactAbelian data,
      no_globalRepairCoherent_of_nonzero_sheafH1
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (coverEnvelope_sheafH1ExactnessDischarge_of_certificate
          exactness),
      coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
        data.toAbelianDescentData.toEnvelopeData exactness,
      coverEnvelope_globalRepairCoherent_of_sheafH1Zero_abelianDescent
        data.toAbelianDescentData exactness,
      rfl, rfl, rfl⟩

/--
Target-adjacent theorem package for boundary-exact abelian cover data whose
selected cover-wise sheaf condition is generated from global true-sheaf
evidence.

This removes the cover-wise `sheafCondition` argument from the target package.
The remaining AAT material evidence is the ambient true-sheaf certificate plus
membership of the selected cover in the AAT topology.
-/
theorem trueSheafH1SemanticRepairGluing_trueSheafBoundaryExactAbelian_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryExactAbelianData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1TrueSheafConditionCertificate data S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual /\
      (forall primitive :
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.C0,
        CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          ((toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.delta0
              primitive)) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
          SemanticRepairH1Zero
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      (SemanticRepairH1Nonzero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        Not
          (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)))) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
        CechB1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData))) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) := by
  let selected :=
    coverEnvelope_sheafConditionCertificate_of_trueSheafCondition
      certificate
  exact
    trueSheafH1SemanticRepairGluing_boundaryExactAbelian_package
      data selected

/--
Named true-sheaf `H1` semantic repair-gluing equivalence for the
boundary-generated abelian relation surface.

This variant avoids the Cycle 10 `boundaryPrimitive : C1 -> C0` selector.  The
exactness needed for zero-class transport is obtained by unpacking the boundary
witness carried by the cohomology relation itself.
-/
theorem trueSheafH1_semanticRepairGluing_iff_boundaryRelationAbelian
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom) :
    GlobalSemanticRepairCoherent
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
      SemanticRepairH1Zero
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) :=
  coverEnvelope_globalRepairCoherent_iff_sheafH1Zero_boundaryRelationAbelian
    data

/--
Target-adjacent theorem package for boundary-generated abelian cover data.

This remains a checkpoint: it removes the universal boundary selector from the
exactness provenance, but still takes selected cover-wise AAT sheaf-condition
evidence explicitly.
-/
theorem trueSheafH1SemanticRepairGluing_boundaryRelationAbelian_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (sheafCondition :
      SemanticRepairCoverH1SheafConditionCertificate
        data.toAbelianDescentData.toEnvelopeData S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual /\
      (forall primitive :
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.C0,
        CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          ((toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.delta0
              primitive)) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
          SemanticRepairH1Zero
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      (SemanticRepairH1Nonzero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        Not
          (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)))) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
        CechB1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData))) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) := by
  let exactness :=
    coverEnvelope_exactnessCertificate_of_boundaryRelationAbelianData data
  exact
    ⟨coverEnvelope_sheafConditionFor_of_certificate sheafCondition,
      coverEnvelope_descent_of_sheafConditionCertificate sheafCondition,
      sheafCondition.envelope_residual_cocycle,
      sheafCondition.envelope_boundary_cocycle,
      trueSheafH1_semanticRepairGluing_iff_boundaryRelationAbelian data,
      no_globalRepairCoherent_of_nonzero_sheafH1
        (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (coverEnvelope_sheafH1ExactnessDischarge_of_certificate
          exactness),
      coverEnvelope_sheafH1Zero_iff_h1Boundary_of_certificate
        data.toAbelianDescentData.toEnvelopeData exactness,
      coverEnvelope_globalRepairCoherent_of_sheafH1Zero_abelianDescent
        data.toAbelianDescentData exactness,
      rfl, rfl, rfl⟩

/--
Global true-sheaf evidence for the selected AAT cover associated with the
boundary-generated abelian relation surface.

This is the Cycle 13 analogue of
`SemanticRepairCoverH1TrueSheafConditionCertificate`, specialized to the Cycle
12 data.  It stores only global true-sheaf evidence and selected-cover topology
membership, not a cover-wise sheaf-condition certificate or any `H1` /
coherence conclusion.
-/
structure SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base) where
  cover_mem : cover ∈ S.topology base
  sheafCondition : AAT.AG.Site.AATSheafCondition S F

/--
Generate the selected cover-wise sheaf-condition certificate for the Cycle 12
boundary-relation surface.
-/
theorem coverEnvelope_sheafConditionCertificate_of_boundaryRelationTrueSheafCondition
    {Atom : Type u}
    {data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom}
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {F : AAT.AG.Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data S F cover) :
    SemanticRepairCoverH1SheafConditionCertificate
      data.toAbelianDescentData.toEnvelopeData S F cover where
  sheafConditionFor :=
    AAT.AG.Site.AATSheafCondition.cover
      certificate.sheafCondition cover certificate.cover_mem
  envelope_residual_cocycle :=
    coverEnvelope_residual_cocycle_wellDefined
      data.toAbelianDescentData.toEnvelopeData
  envelope_boundary_cocycle :=
    coverEnvelope_delta1_delta0_eq_zero
      data.toAbelianDescentData.toEnvelopeData

/--
Target-adjacent theorem package for the Cycle 12 boundary-generated relation
surface with cover-wise sheaf condition generated from global true-sheaf
evidence.
-/
theorem trueSheafH1SemanticRepairGluing_trueSheafBoundaryRelationAbelian_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.residual /\
      (forall primitive :
        (toSheafH1Envelope
          data.toAbelianDescentData.toEnvelopeData).coefficient.C0,
        CechZ1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          ((toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.delta0
              primitive)) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) <->
          SemanticRepairH1Zero
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      (SemanticRepairH1Nonzero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        Not
          (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)))) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) <->
        CechB1 (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.toAbelianDescentData.toEnvelopeData).coefficient.residual) /\
      (SemanticRepairH1Zero
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData) ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData))) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope data.toAbelianDescentData.toEnvelopeData)) := by
  let selected :=
    coverEnvelope_sheafConditionCertificate_of_boundaryRelationTrueSheafCondition
      certificate
  exact
    trueSheafH1SemanticRepairGluing_boundaryRelationAbelian_package
      data selected

/--
Boundary-relation cover data equipped with additive coefficient laws.

The additive laws are coefficient algebra only.  They do not store a zero
`H1` class, a boundary primitive for the residual, global coherence, exactness,
or effective descent.
-/
structure SemanticRepairCoverH1BoundaryRelationAdditiveData
    (Atom : Type u) where
  boundaryRelation :
    SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} Atom
  [c0AddCommGroup : AddCommGroup boundaryRelation.cech.C0]
  [c1AddCommGroup : AddCommGroup boundaryRelation.cech.C1]
  zero1_eq_zero : boundaryRelation.cech.zero1 = 0
  delta0_zero : boundaryRelation.cech.delta0 0 = 0
  delta0_add :
    forall left right,
      boundaryRelation.cech.delta0 (left + right) =
        boundaryRelation.cech.delta0 left + boundaryRelation.cech.delta0 right
  delta0_neg :
    forall primitive,
      boundaryRelation.cech.delta0 (-primitive) =
        -boundaryRelation.cech.delta0 primitive

/--
Generate the target-strength additive Cech `H1 = Z1 / B1` data from the
boundary-relation cover data and its coefficient algebra.
-/
def SemanticRepairCoverH1BoundaryRelationAdditiveData.toAdditiveCechH1Data
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom) :
    SemanticRepairAdditiveCechH1Data
      (toSheafH1Envelope
        data.boundaryRelation.toAbelianDescentData.toEnvelopeData) where
  c0AddCommGroup := data.c0AddCommGroup
  c1AddCommGroup := data.c1AddCommGroup
  zero1_eq_zero := data.zero1_eq_zero
  delta0_zero := data.delta0_zero
  delta0_add := data.delta0_add
  delta0_neg := data.delta0_neg

/--
Concrete Cycle 17 bridge: in the boundary-relation true-sheaf surface, global
semantic repair coherence is equivalent to vanishing of the selected residual's
additive Cech `H1 = Z1 / B1` class, with exactness and later-layer vanishings
constructed from the cover data.
-/
theorem coverEnvelope_boundaryRelationAdditive_globalRepairCoherent_iff_additiveH1Zero
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom) :
    GlobalSemanticRepairCoherent
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
      SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data := by
  exact
    globalRepairCoherent_iff_additiveH1Zero
      (toSheafH1Envelope
        data.boundaryRelation.toAbelianDescentData.toEnvelopeData)
      data.toAdditiveCechH1Data
      (coverEnvelope_sheafH1ExactnessDischarge_of_certificate
        (coverEnvelope_exactnessCertificate_of_boundaryRelationAbelianData
          data.boundaryRelation))
      rfl rfl rfl

/--
Cycle 17 package: true-sheaf boundary-relation data with additive coefficient
laws supplies the target-strength additive `H1` gluing equivalence without
external later-layer vanishing arguments.
-/
theorem trueSheafH1SemanticRepairGluing_trueSheafBoundaryRelationAdditive_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      CechZ1
        (toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData)
        (toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.residual /\
      (forall primitive :
        (toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.C0,
        CechZ1
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)
          ((toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.delta0
              primitive)) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        CechB1
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.residual) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) := by
  let selected :=
    coverEnvelope_sheafConditionCertificate_of_boundaryRelationTrueSheafCondition
      certificate
  have hbridge :
      GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
        SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data :=
    coverEnvelope_boundaryRelationAdditive_globalRepairCoherent_iff_additiveH1Zero
      data
  exact
    ⟨coverEnvelope_sheafConditionFor_of_certificate selected,
      coverEnvelope_descent_of_sheafConditionCertificate selected,
      selected.envelope_residual_cocycle,
      selected.envelope_boundary_cocycle,
      hbridge,
      hbridge.2,
      hbridge.1,
      semanticRepairAdditiveH1Zero_iff_boundary data.toAdditiveCechH1Data,
      rfl, rfl, rfl⟩

end SemanticRepairTrueSheafH1
end QualitySurface
end ResearchLean.AG
