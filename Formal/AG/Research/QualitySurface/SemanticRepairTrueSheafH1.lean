import Formal.AG.Cohomology.CoverNerve
import Formal.AG.Site.Descent
import Formal.AG.Research.QualitySurface.SemanticRepairSheafH1

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

namespace Formal.AG.Research
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

end SemanticRepairTrueSheafH1
end QualitySurface
end Formal.AG.Research
