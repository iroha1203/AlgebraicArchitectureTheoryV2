import Formal.AG.Cohomology.CoverNerve
import Formal.AG.SemanticRepair.GluingComplex
import Formal.AG.Site.Descent
import Formal.AG.SingularityMonodromyStack.ArchitectureStack

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory

universe u v w x y z r

/-! ## X.§4 finite cover and additive Cech H1 surface -/

/--
X.定義4.1: finite semantic repair cover with selected overlap and
triple-overlap components.

The cover carries only selected local geometry.  It does not store a global
repair, an H1-zero premise, or later-layer vanishing evidence.
-/
structure SemanticRepairCover
    (P : SemanticAtomProjection.{u, v}) where
  baseCover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component
  CoverChart : Type w
  chart : CoverChart -> baseCover.Chart
  chartInjective : Function.Injective chart
  chartFinite : Fintype CoverChart
  Overlap : CoverChart -> CoverChart -> Type w
  overlapFinite : forall left right, Fintype (Overlap left right)
  TripleOverlap : CoverChart -> CoverChart -> CoverChart -> Type w
  tripleFinite : forall i j k, Fintype (TripleOverlap i j k)
  tripleEdge01 : forall {i j k}, TripleOverlap i j k -> Overlap i j
  tripleEdge12 : forall {i j k}, TripleOverlap i j k -> Overlap j k
  tripleEdge02 : forall {i j k}, TripleOverlap i j k -> Overlap i k
  /-- The selected comparison edge for each ordered chart pair. -/
  selectedOverlap : forall left right, Overlap left right
  /-- The selected comparison face for each ordered chart triple. -/
  selectedTriple : forall i j k, TripleOverlap i j k
  selectedOverlap_eq_tripleEdge01 : forall i j k,
    selectedOverlap i j = tripleEdge01 (selectedTriple i j k)
  selectedOverlap_eq_tripleEdge12 : forall i j k,
    selectedOverlap j k = tripleEdge12 (selectedTriple i j k)
  selectedOverlap_eq_tripleEdge02 : forall i j k,
    selectedOverlap i k = tripleEdge02 (selectedTriple i j k)

namespace SemanticRepairCover

attribute [instance] chartFinite overlapFinite tripleFinite

/-- X.定義4.1: read the selected finite repair cover as a generic cover nerve. -/
def toCoverNerve
    {P : SemanticAtomProjection.{u, v}}
    (cover : SemanticRepairCover.{u, v, w, x} P) :
    Cohomology.CoverNerve.{w} where
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
    Sigma.mk (face.1.1, face.1.2.1) (cover.tripleEdge01 face.2)
  faceEdge1 face :=
    Sigma.mk (face.1.2.1, face.1.2.2) (cover.tripleEdge12 face.2)
  faceEdge2 face :=
    Sigma.mk (face.1.1, face.1.2.2) (cover.tripleEdge02 face.2)
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := by
    intro _edge
    trivial
  faceTripleOverlapComponent_holds := by
    intro _face
    trivial

end SemanticRepairCover

/--
X.定義4.2: Cech-style coefficient data over a selected semantic repair cover.

The differentials and cocycle witnesses are supplied data.  This definition
records the bounded finite surface; it does not assert exactness or global
semantic repair coherence.
-/
structure SemanticRepairCoverCechData
    {P : SemanticAtomProjection.{u, v}}
    (_cover : SemanticRepairCover.{u, v, w, x} P) where
  C0 : Type y
  C1 : Type x
  C2 : Type z
  c0Finite : Fintype C0
  c1Finite : Fintype C1
  zero1 : C1
  zero2 : C2
  delta0 : C0 -> C1
  delta1 : C1 -> C2
  residual : C1
  zero1_cocycle : delta1 zero1 = zero2
  delta1_delta0_eq_zero : forall primitive, delta1 (delta0 primitive) = zero2
  residual_cocycle : delta1 residual = zero2

namespace SemanticRepairCoverCechData

attribute [instance] c0Finite c1Finite

end SemanticRepairCoverCechData

/--
Cover-indexed realization of the selected Cech surface.

The realization evaluates degree-zero cochains on charts, degree-one
cochains on selected overlaps, and degree-two cochains on selected triple
overlaps.  Its compatibility fields describe the two differentials
componentwise; it stores neither a vanishing conclusion nor an effective
descent witness.
-/
structure SemanticRepairCoverCechRealization
    {P : SemanticAtomProjection.{u, v}}
    (cover : SemanticRepairCover.{u, v, w, x} P)
    (cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover) where
  /-- Common additive fiber receiving selected Cech components. -/
  Fiber : Type w
  fiberAddCommGroup : AddCommGroup Fiber
  /-- Degree-zero evaluation on one repair-cover chart. -/
  eval0 : cech.C0 -> cover.CoverChart -> Fiber
  /-- Degree-one evaluation on one selected repair-cover overlap. -/
  eval1 : cech.C1 -> forall {left right : cover.CoverChart},
    cover.Overlap left right -> Fiber
  /-- Degree-two evaluation on one selected repair-cover triple face. -/
  eval2 : cech.C2 -> forall {i j k : cover.CoverChart},
    cover.TripleOverlap i j k -> Fiber
  eval_delta0 : forall primitive {left right : cover.CoverChart}
    (overlap : cover.Overlap left right),
    eval1 (cech.delta0 primitive) overlap =
      eval0 primitive right - eval0 primitive left
  eval_delta1 : forall cochain {i j k : cover.CoverChart}
    (triple : cover.TripleOverlap i j k),
    eval2 (cech.delta1 cochain) triple =
      eval1 cochain (cover.tripleEdge01 triple) +
        eval1 cochain (cover.tripleEdge12 triple) -
          eval1 cochain (cover.tripleEdge02 triple)
  eval_zero1 : forall {left right : cover.CoverChart}
    (overlap : cover.Overlap left right),
    eval1 cech.zero1 overlap = 0
  eval_zero2 : forall {i j k : cover.CoverChart}
    (triple : cover.TripleOverlap i j k),
    eval2 cech.zero2 triple = 0

namespace SemanticRepairCoverCechRealization

attribute [instance] fiberAddCommGroup

/-- The residual has the selected cocycle equation on every triple overlap. -/
def ResidualFacewiseCocycle
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (realization : SemanticRepairCoverCechRealization cover cech) : Prop :=
  forall {i j k : cover.CoverChart} (triple : cover.TripleOverlap i j k),
    realization.eval1 cech.residual (cover.tripleEdge01 triple) +
        realization.eval1 cech.residual (cover.tripleEdge12 triple) =
      realization.eval1 cech.residual (cover.tripleEdge02 triple)

/-- The residual cocycle field yields its componentwise triple-overlap form. -/
theorem residualFacewiseCocycle
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (realization : SemanticRepairCoverCechRealization cover cech) :
    realization.ResidualFacewiseCocycle := by
  intro i j k triple
  have hdefect :
      realization.eval1 cech.residual (cover.tripleEdge01 triple) +
          realization.eval1 cech.residual (cover.tripleEdge12 triple) -
            realization.eval1 cech.residual (cover.tripleEdge02 triple) = 0 := by
    calc
      realization.eval1 cech.residual (cover.tripleEdge01 triple) +
          realization.eval1 cech.residual (cover.tripleEdge12 triple) -
            realization.eval1 cech.residual (cover.tripleEdge02 triple) =
          realization.eval2 (cech.delta1 cech.residual) triple := by
            exact (realization.eval_delta1 cech.residual triple).symm
      _ = realization.eval2 cech.zero2 triple := by
            rw [cech.residual_cocycle]
      _ = 0 := realization.eval_zero2 triple
  exact sub_eq_zero.mp hdefect

end SemanticRepairCoverCechRealization

/-- Context cells generated by a selected semantic repair cover. -/
inductive AdditiveRepairCoverContext
    {P : SemanticAtomProjection.{u, v}}
    (cover : SemanticRepairCover.{u, v, w, x} P) : Type w where
  | global
  | chart (value : cover.CoverChart)
  | overlap (value : Sigma fun pair : cover.CoverChart × cover.CoverChart =>
      cover.Overlap pair.1 pair.2)
  | triple (value : Sigma fun indices : cover.CoverChart × cover.CoverChart × cover.CoverChart =>
      cover.TripleOverlap indices.1 indices.2.1 indices.2.2)

namespace AdditiveRepairCoverContext

/-- The charts present in one selected repair-cover cell. -/
def Supports
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    (context : AdditiveRepairCoverContext cover)
    (baseChart : cover.baseCover.Chart) : Prop :=
  match context with
  | .global => True
  | .chart value => baseChart = cover.chart value
  | .overlap value =>
      baseChart = cover.chart value.1.1 ∨ baseChart = cover.chart value.1.2
  | .triple value =>
      baseChart = cover.chart value.1.1 ∨
        baseChart = cover.chart value.1.2.1 ∨
          baseChart = cover.chart value.1.2.2

/--
An actual restriction arrow of the selected repair cover.

Every local cell restricts to the global cell.  Away from the global cell,
the target charts must be represented by the source cell.  In particular,
there is no restriction from the global cell to a proper local cell.
-/
def Restrict
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    (source target : AdditiveRepairCoverContext cover) : Type w :=
  Subtype fun _ : ULift.{w} PUnit =>
    target = .global \/
      (source ≠ .global /\
        forall chart, Supports target chart -> Supports source chart)

end AdditiveRepairCoverContext

/--
Selected complete repair-cover data used by the Part VI descent datum.

The three compatibility equations require the pairwise transitions used by the
descent datum to be the three edges of every selected triple face.  This is
cover geometry only; it carries neither a repair primitive nor a vanishing
claim.
-/
structure SelectedRepairCoverDescentSelection
    {P : SemanticAtomProjection.{u, v}}
    (cover : SemanticRepairCover.{u, v, w, x} P) where
  /-- Selected overlap for each ordered pair of repair-cover charts. -/
  overlap : forall left right : cover.CoverChart, cover.Overlap left right
  /-- Selected triple face for each ordered triple of repair-cover charts. -/
  triple : forall i j k : cover.CoverChart, cover.TripleOverlap i j k
  overlap_eq_tripleEdge01 : forall i j k,
    overlap i j = cover.tripleEdge01 (triple i j k)
  overlap_eq_tripleEdge12 : forall i j k,
    overlap j k = cover.tripleEdge12 (triple i j k)
  overlap_eq_tripleEdge02 : forall i j k,
    overlap i k = cover.tripleEdge02 (triple i j k)

/-- The selected comparison data carried by a finite semantic repair cover. -/
def SemanticRepairCover.toDescentSelection
    {P : SemanticAtomProjection.{u, v}}
    (cover : SemanticRepairCover.{u, v, w, x} P) :
    SelectedRepairCoverDescentSelection cover where
  overlap := cover.selectedOverlap
  triple := cover.selectedTriple
  overlap_eq_tripleEdge01 := cover.selectedOverlap_eq_tripleEdge01
  overlap_eq_tripleEdge12 := cover.selectedOverlap_eq_tripleEdge12
  overlap_eq_tripleEdge02 := cover.selectedOverlap_eq_tripleEdge02

/-- X.定義4.2: Cech-style 1-cocycles on the bounded semantic repair cover. -/
def CechZ1
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    (cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover)
    (cochain : cech.C1) : Prop :=
  cech.delta1 cochain = cech.zero2

/-- X.定義4.2: Cech-style 1-boundaries on the bounded semantic repair cover. -/
def CechB1
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    (cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover)
    (cochain : cech.C1) : Prop :=
  exists primitive, cech.delta0 primitive = cochain

/--
X.定義4.3: additive regime for the bounded Cech H1 surface.

The additive laws are coefficient algebra only.  They do not store a boundary
primitive for the residual, a zero class, global coherence, or later-layer
vanishing evidence.
-/
structure SemanticRepairAdditiveCechH1Data
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    (cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover) where
  [c0AddCommGroup : AddCommGroup cech.C0]
  [c1AddCommGroup : AddCommGroup cech.C1]
  [c2AddCommGroup : AddCommGroup cech.C2]
  zero1_eq_zero : cech.zero1 = 0
  zero2_eq_zero : cech.zero2 = 0
  delta0_zero : cech.delta0 0 = 0
  delta0_add :
    forall left right,
      cech.delta0 (left + right) = cech.delta0 left + cech.delta0 right
  delta0_neg : forall primitive, cech.delta0 (-primitive) = -cech.delta0 primitive
  delta1_add :
    forall left right,
      cech.delta1 (left + right) = cech.delta1 left + cech.delta1 right
  delta1_neg : forall cochain, cech.delta1 (-cochain) = -cech.delta1 cochain

namespace SemanticRepairAdditiveCechH1Data

attribute [instance] c0AddCommGroup c1AddCommGroup c2AddCommGroup

/-- X.定義4.4: additive 1-cocycles used by the quotient `Z1/B1`. -/
def Cocycle
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (_data : SemanticRepairAdditiveCechH1Data cech) : Type x :=
  { cochain : cech.C1 // CechZ1 cech cochain }

/-- X.定義4.4: two cocycles differ by an additive Cech boundary. -/
def Cohomologous
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech)
    (left right : data.Cocycle) : Prop :=
  letI := data.c1AddCommGroup
  exists primitive, left.1 - right.1 = cech.delta0 primitive

/-- X.定義4.4: the additive Cech boundary relation is reflexive. -/
theorem cohomologous_refl
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech)
    (cochain : data.Cocycle) :
    data.Cohomologous cochain cochain := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  refine ⟨0, ?_⟩
  change cochain.1 - cochain.1 = cech.delta0 0
  rw [data.delta0_zero]
  simp

/-- X.定義4.4: the additive Cech boundary relation is symmetric. -/
theorem cohomologous_symm
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech)
    {left right : data.Cocycle} :
    data.Cohomologous left right -> data.Cohomologous right left := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  intro h
  rcases h with ⟨primitive, hprimitive⟩
  refine ⟨-primitive, ?_⟩
  calc
    right.1 - left.1 = -(left.1 - right.1) := by abel
    _ = -(cech.delta0 primitive) := by rw [hprimitive]
    _ = cech.delta0 (-primitive) := by rw [← data.delta0_neg primitive]

/-- X.定義4.4: the additive Cech boundary relation is transitive. -/
theorem cohomologous_trans
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech)
    {left middle right : data.Cocycle} :
    data.Cohomologous left middle ->
      data.Cohomologous middle right ->
        data.Cohomologous left right := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  intro hleft hright
  rcases hleft with ⟨leftPrimitive, hleftPrimitive⟩
  rcases hright with ⟨rightPrimitive, hrightPrimitive⟩
  refine ⟨leftPrimitive + rightPrimitive, ?_⟩
  calc
    left.1 - right.1 =
        (left.1 - middle.1) + (middle.1 - right.1) := by abel
    _ = cech.delta0 leftPrimitive + cech.delta0 rightPrimitive := by
      rw [hleftPrimitive, hrightPrimitive]
    _ = cech.delta0 (leftPrimitive + rightPrimitive) := by
      rw [← data.delta0_add leftPrimitive rightPrimitive]

/-- X.定義4.4: setoid for additive Cech H1. -/
def setoid
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech) :
    Setoid data.Cocycle where
  r := data.Cohomologous
  iseqv := ⟨data.cohomologous_refl, data.cohomologous_symm, data.cohomologous_trans⟩

/-- X.定義4.4: semantic repair additive H1 as `Z1/B1`. -/
def H1
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech) : Type x :=
  Quotient data.setoid

/-- X.定義4.4: the selected residual additive H1 class. -/
def residualClass
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech) :
    data.H1 :=
  Quotient.mk data.setoid ⟨cech.residual, cech.residual_cocycle⟩

/-- X.定義4.4: the zero additive H1 class. -/
def zeroClass
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech) :
    data.H1 :=
  Quotient.mk data.setoid ⟨cech.zero1, cech.zero1_cocycle⟩

/-- X.定義4.4: selected residual class vanishes in additive Cech H1. -/
def H1Zero
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech) : Prop :=
  data.residualClass = data.zeroClass

/--
X.補題4.5 additive core: the selected quotient class is zero exactly when
the selected residual is a bounded Cech boundary.
-/
theorem h1Zero_iff_boundary
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech) :
    data.H1Zero <-> CechB1 cech cech.residual := by
  letI := data.c1AddCommGroup
  constructor
  · intro hzero
    have hrel :
        data.Cohomologous
          ⟨cech.residual, cech.residual_cocycle⟩
          ⟨cech.zero1, cech.zero1_cocycle⟩ :=
      Quotient.exact hzero
    rcases hrel with ⟨primitive, hprimitive⟩
    refine ⟨primitive, ?_⟩
    have hresidual : cech.residual = cech.delta0 primitive := by
      calc
        cech.residual = cech.residual - cech.zero1 := by
          rw [data.zero1_eq_zero, sub_zero]
        _ = cech.delta0 primitive := hprimitive
    exact hresidual.symm
  · intro hboundary
    rcases hboundary with ⟨primitive, hprimitive⟩
    apply Quotient.sound
    refine ⟨primitive, ?_⟩
    calc
      cech.residual - cech.zero1 = cech.residual := by
        rw [data.zero1_eq_zero, sub_zero]
      _ = cech.delta0 primitive := hprimitive.symm

end SemanticRepairAdditiveCechH1Data

/-- X.補題4.5: public quotient-zero reading for semantic repair additive H1. -/
theorem semanticRepairAdditiveH1Zero_iff_boundary
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover}
    (data : SemanticRepairAdditiveCechH1Data cech) :
    data.H1Zero <-> CechB1 cech cech.residual :=
  data.h1Zero_iff_boundary

/--
X.定義4.6: component-coverage and component-faithfulness presentation.

This is retained as a concrete presentation whose support-derived closure is
bridged to `SemanticRepairCoverH1FaithfulnessData` below.
-/
structure SemanticRepairCoverH1BoundaryRelationAbelianData
    (P : SemanticAtomProjection.{u, v}) where
  cover : SemanticRepairCover.{u, v, w, x} P
  cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover
  supportOf : cech.C0 -> P.Support
  component_covered_of_boundary :
    forall primitive,
      cech.delta0 primitive = cech.residual ->
        ResidualComponentCoveredSupport P cover.baseCover (supportOf primitive)
  component_faithful_of_boundary :
    forall primitive,
      cech.delta0 primitive = cech.residual ->
        ResidualComponentFaithfulSupport P cover.baseCover (supportOf primitive)

/--
X.定義4.6: general boundary-relation faithfulness data without a global selector.

`P` is the closure predicate on local primitives and `Q` is the residual-support
predicate on cochains. The data keeps the zero primitive, `Q`-membership of
the selected residual, and the implication from `Q (delta0 primitive)` to
`P primitive` explicit.

## Implementation notes

The component-coverage package above remains a concrete presentation of this
data: it supplies `P` from semantic closure and takes `Q` to be equality with
the selected residual. This keeps the non-additive definition independent from
that particular support reading.
-/
structure SemanticRepairCoverH1FaithfulnessData
    (projection : SemanticAtomProjection.{u, v}) where
  /-- The selected finite semantic repair cover. -/
  cover : SemanticRepairCover.{u, v, w, x} projection
  /-- The Cech cochain data carried by the selected cover. -/
  cech : SemanticRepairCoverCechData.{u, v, w, x, y, z} cover
  /-- The general closure predicate on degree-zero primitives. -/
  P : cech.C0 -> Prop
  /-- The residual-support predicate on degree-one cochains. -/
  Q : cech.C1 -> Prop
  /-- A primitive whose coboundary is the selected zero cochain. -/
  zeroPrimitive : cech.C0
  /-- The supplied primitive maps to the selected zero cochain. -/
  delta0_zeroPrimitive : cech.delta0 zeroPrimitive = cech.zero1
  /-- The selected residual satisfies the residual-support predicate. -/
  residual_in_Q : Q cech.residual
  /-- Residual-support of a primitive coboundary entails its closure predicate. -/
  faithful :
    forall primitive,
      Q (cech.delta0 primitive) -> P primitive

namespace SemanticRepairCoverH1FaithfulnessData

/-- X.定義4.6: global coherence read through the general closure predicate `P`. -/
def GlobalRepairCoherent
    {projection : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1FaithfulnessData.{u, v, w, x, y, z} projection) : Prop :=
  exists primitive,
    data.cech.delta0 primitive = data.cech.residual /\
      data.P primitive

/-- X.定義4.6: the supplied zero primitive is a boundary for the selected zero cochain. -/
theorem zero1_is_boundary
    {projection : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1FaithfulnessData.{u, v, w, x, y, z} projection) :
    CechB1 data.cech data.cech.zero1 :=
  ⟨data.zeroPrimitive, data.delta0_zeroPrimitive⟩

/--
X.定義4.6 / 定理4.8 sufficient direction: a residual boundary is globally
coherent because the faithfulness law is applied to that boundary primitive.
-/
theorem globalRepairCoherent_of_boundary
    {projection : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1FaithfulnessData.{u, v, w, x, y, z} projection) :
    CechB1 data.cech data.cech.residual ->
      data.GlobalRepairCoherent := by
  rintro ⟨primitive, hboundary⟩
  refine ⟨primitive, hboundary, ?_⟩
  apply data.faithful primitive
  rw [hboundary]
  exact data.residual_in_Q

end SemanticRepairCoverH1FaithfulnessData

/--
X.定義4.6 / 定理4.8: general `P`/`Q` faithfulness data together with the
additive Cech H1 laws on the same selected cover.

The additive package supplies the quotient reading of the selected residual;
it does not contain a residual primitive or global coherence witness.
-/
structure SemanticRepairCoverH1AdditiveFaithfulnessData
    (projection : SemanticAtomProjection.{u, v}) where
  /-- The general `P`/`Q` faithfulness presentation. -/
  faithfulness : SemanticRepairCoverH1FaithfulnessData.{u, v, w, x, y, z} projection
  /-- The additive Cech H1 laws for the faithfulness presentation. -/
  additive : SemanticRepairAdditiveCechH1Data faithfulness.cech

namespace SemanticRepairCoverH1AdditiveFaithfulnessData

/-- X.定義4.6: read the general faithfulness presentation. -/
def toFaithfulnessData
    {projection : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1AdditiveFaithfulnessData.{u, v, w, x, y, z} projection) :
    SemanticRepairCoverH1FaithfulnessData.{u, v, w, x, y, z} projection :=
  data.faithfulness

/-- X.定義4.3: read the additive Cech H1 laws. -/
def toAdditiveCechH1Data
    {projection : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1AdditiveFaithfulnessData.{u, v, w, x, y, z} projection) :
    SemanticRepairAdditiveCechH1Data data.faithfulness.cech :=
  data.additive

/--
X.定理4.8 sufficient direction for general `P`/`Q` data: vanishing of the
selected additive H1 class yields global coherence through the faithfulness
law.
-/
theorem globalRepairCoherent_of_additiveH1Zero
    {projection : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1AdditiveFaithfulnessData.{u, v, w, x, y, z} projection) :
    data.toAdditiveCechH1Data.H1Zero ->
      data.toFaithfulnessData.GlobalRepairCoherent := by
  intro hzero
  exact data.toFaithfulnessData.globalRepairCoherent_of_boundary
    (data.toAdditiveCechH1Data.h1Zero_iff_boundary.mp hzero)

end SemanticRepairCoverH1AdditiveFaithfulnessData

namespace SemanticRepairCoverH1BoundaryRelationAbelianData

/-- X.定義4.6: the boundary-relation data as a finite §3 gluing complex. -/
def toFiniteGluingComplex
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} P) :
    FiniteSemanticRepairGluingComplex.{u, v, w, x, y} where
  projection := P
  cover := data.cover.baseCover
  C0 := data.cech.C0
  C1 := data.cech.C1
  primitiveFinite := data.cech.c0Finite
  cochainFinite := data.cech.c1Finite
  supportOf := data.supportOf
  delta0 := data.cech.delta0
  residual := data.cech.residual

/-- X.定義4.6: boundary-relation faithfulness discharges §3 hypotheses. -/
theorem semanticFaithfulnessHypotheses
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} P) :
    SemanticFaithfulnessHypotheses data.toFiniteGluingComplex where
  component_covered_of_boundary primitive hboundary :=
    data.component_covered_of_boundary primitive hboundary
  component_faithful_of_boundary primitive hboundary :=
    data.component_faithful_of_boundary primitive hboundary

/--
X.定義4.6: construct the general `P`/`Q` data from the component presentation.

Here `P` is semantic closure of the assigned support and `Q` is equality with
the selected residual. A zero primitive is supplied separately so this bridge
does not assume additive coefficients.
-/
def toFaithfulnessData
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} P)
    (zeroPrimitive : data.cech.C0)
    (hzeroPrimitive : data.cech.delta0 zeroPrimitive = data.cech.zero1) :
    SemanticRepairCoverH1FaithfulnessData.{u, v, w, x, y, z} P where
  cover := data.cover
  cech := data.cech
  P := fun primitive => PrimitiveSemanticallyClosed data.toFiniteGluingComplex primitive
  Q := fun cochain => cochain = data.cech.residual
  zeroPrimitive := zeroPrimitive
  delta0_zeroPrimitive := hzeroPrimitive
  residual_in_Q := rfl
  faithful primitive hQ :=
    primitive_semanticRepairClosed_of_faithful_delta0
      data.semanticFaithfulnessHypotheses (primitive := primitive) hQ

/--
X.定義4.6: the general `P`-based coherence of the component bridge is exactly
the existing support-based global semantic repair coherence.
-/
theorem toFaithfulnessData_globalRepairCoherent_iff
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} P)
    (zeroPrimitive : data.cech.C0)
    (hzeroPrimitive : data.cech.delta0 zeroPrimitive = data.cech.zero1) :
    (data.toFaithfulnessData zeroPrimitive hzeroPrimitive).GlobalRepairCoherent <->
      GlobalSemanticRepairCoherent data.toFiniteGluingComplex :=
  Iff.rfl

end SemanticRepairCoverH1BoundaryRelationAbelianData

/-- X.定義4.3/4.6: boundary-relation cover data equipped with additive laws. -/
structure SemanticRepairCoverH1BoundaryRelationAdditiveData
    (P : SemanticAtomProjection.{u, v}) where
  boundaryRelation :
    SemanticRepairCoverH1BoundaryRelationAbelianData.{u, v, w, x, y, z} P
  additive :
    SemanticRepairAdditiveCechH1Data boundaryRelation.cech

namespace SemanticRepairCoverH1BoundaryRelationAdditiveData

/-- X.定義4.3: read the additive Cech H1 data from boundary-relation data. -/
def toAdditiveCechH1Data
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    SemanticRepairAdditiveCechH1Data data.boundaryRelation.cech :=
  data.additive

/--
X.定義4.6: additive coefficients construct the zero primitive required by the
general faithfulness data.
-/
def toFaithfulnessData
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    SemanticRepairCoverH1FaithfulnessData.{u, v, w, x, y, z} P := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  exact data.boundaryRelation.toFaithfulnessData 0
    (data.additive.delta0_zero.trans data.additive.zero1_eq_zero.symm)

/--
X.定義4.6: combine the component presentation with additive Cech H1 laws as
a concrete instance of the general `P`/`Q` additive faithfulness data.
-/
def toAdditiveFaithfulnessData
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    SemanticRepairCoverH1AdditiveFaithfulnessData.{u, v, w, x, y, z} P where
  faithfulness := data.toFaithfulnessData
  additive := data.additive

/--
X.定理4.8 component presentation: additive H1 zero yields global semantic
repair coherence through the general `P`/`Q` additive faithfulness data.
-/
theorem globalRepairCoherent_of_additiveH1Zero
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    data.toAdditiveCechH1Data.H1Zero ->
      data.toFaithfulnessData.GlobalRepairCoherent := by
  intro hzero
  exact data.toAdditiveFaithfulnessData.globalRepairCoherent_of_additiveH1Zero hzero

/--
X.定義4.7: true-sheaf condition certificate for the selected cover.

This certificate contains only cover membership and the global sheaf condition.
It does not contain a global semantic repair, an H1-zero proof, or later-layer
vanishing fields.
-/
structure TrueSheafConditionCertificate
    {P : SemanticAtomProjection.{u, v}}
    (_data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    {U : AtomCarrier.{r}}
    {A : ArchitectureObject U}
    (S : Site.AATSite A)
    (F : Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base) where
  cover_mem : cover ∈ S.topology base
  sheafCondition : Site.AATSheafCondition S F

/--
X.定理4.8 conclusion 5, torsor layer: additive primitives whose differential
is the selected residual.
-/
def AdditiveRepairSolution
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Type y :=
  { primitive : data.boundaryRelation.cech.C0 //
    data.boundaryRelation.cech.delta0 primitive =
      data.boundaryRelation.cech.residual }

/-- The additive gauge group is the degree-zero kernel of the selected differential. -/
def additiveRepairGaugeSubgroup
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    letI := data.additive.c0AddCommGroup
    letI := data.additive.c1AddCommGroup
    AddSubgroup data.boundaryRelation.cech.C0 := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  exact
    { carrier := { gauge | data.boundaryRelation.cech.delta0 gauge = 0 }
      zero_mem' := data.additive.delta0_zero
      add_mem' := fun {left} {right} hleft hright => by
        change data.boundaryRelation.cech.delta0 (left + right) = 0
        change data.boundaryRelation.cech.delta0 left = 0 at hleft
        change data.boundaryRelation.cech.delta0 right = 0 at hright
        rw [data.additive.delta0_add, hleft, hright, add_zero]
      neg_mem' := fun {gauge} hgauge => by
        change data.boundaryRelation.cech.delta0 (-gauge) = 0
        change data.boundaryRelation.cech.delta0 gauge = 0 at hgauge
        rw [data.additive.delta0_neg, hgauge, neg_zero] }

/-- The gauge carrier acting on residual-solving primitives. -/
def AdditiveRepairGauge
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Type y := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  exact ↑data.additiveRepairGaugeSubgroup

/-- The degree-zero kernel carries its inherited additive gauge-group structure. -/
instance additiveRepairGaugeAddCommGroup
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    letI := data.additive.c0AddCommGroup
    letI := data.additive.c1AddCommGroup
    AddCommGroup (AdditiveRepairGauge data) := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  exact data.additiveRepairGaugeSubgroup.toAddCommGroup

/-- A translation between two residual-solving primitives. -/
def AdditiveRepairPrimitiveTranslation
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (source target : AdditiveRepairSolution data) : Type y := by
  letI := data.additive.c0AddCommGroup
  exact { translation : data.boundaryRelation.cech.C0 // translation + source.1 = target.1 }

/-- The canonical difference translation between two repair solutions. -/
def additiveRepairPrimitiveTranslation
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (source target : AdditiveRepairSolution data) :
    AdditiveRepairPrimitiveTranslation data source target := by
  letI := data.additive.c0AddCommGroup
  exact ⟨target.1 - source.1, by abel⟩

/-- The canonical solution difference is a gauge element. -/
def additiveRepairGaugeBetween
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (source target : AdditiveRepairSolution data) :
    AdditiveRepairGauge data := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  refine ⟨target.1 - source.1, ?_⟩
  calc
    data.boundaryRelation.cech.delta0 (target.1 - source.1) =
        data.boundaryRelation.cech.delta0 target.1 +
          data.boundaryRelation.cech.delta0 (-source.1) := by
            rw [show target.1 - source.1 = target.1 + -source.1 by abel]
            exact data.additive.delta0_add target.1 (-source.1)
    _ = data.boundaryRelation.cech.delta0 target.1 +
          -data.boundaryRelation.cech.delta0 source.1 := by
            rw [data.additive.delta0_neg]
    _ = data.boundaryRelation.cech.delta0 target.1 -
          data.boundaryRelation.cech.delta0 source.1 :=
      (sub_eq_add_neg _ _).symm
    _ = data.boundaryRelation.cech.residual -
          data.boundaryRelation.cech.residual := by rw [target.2, source.2]
    _ = 0 := sub_self _

/-- The additive gauge action on residual-solving primitives. -/
def additiveRepairGaugeAction
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (gauge : AdditiveRepairGauge data)
    (solution : AdditiveRepairSolution data) :
    AdditiveRepairSolution data := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  exact ⟨gauge.1 + solution.1, by
    calc
      data.boundaryRelation.cech.delta0 (gauge.1 + solution.1) =
          data.boundaryRelation.cech.delta0 gauge.1 +
            data.boundaryRelation.cech.delta0 solution.1 :=
        data.additive.delta0_add gauge.1 solution.1
      _ = 0 + data.boundaryRelation.cech.residual := by rw [gauge.2, solution.2]
      _ = data.boundaryRelation.cech.residual := zero_add _⟩

/-- The additive gauge group acts on the residual-solving primitive carrier. -/
instance additiveRepairGaugeAddAction
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    letI := data.additive.c0AddCommGroup
    letI := data.additive.c1AddCommGroup
    AddAction (AdditiveRepairGauge data) (AdditiveRepairSolution data) := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  exact
    { vadd := data.additiveRepairGaugeAction
      zero_vadd := fun solution => by
        apply Subtype.ext
        change (0 : data.boundaryRelation.cech.C0) + solution.1 = solution.1
        exact zero_add _
      add_vadd := fun left right solution => by
        apply Subtype.ext
        change (left.1 + right.1) + solution.1 = left.1 + (right.1 + solution.1)
        exact add_assoc _ _ _ }

/-- The zero gauge fixes every residual-solving primitive. -/
theorem additiveRepairGaugeAction_zero
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (solution : AdditiveRepairSolution data) :
    data.additiveRepairGaugeAction 0 solution = solution := by
  change (0 : AdditiveRepairGauge data) +ᵥ solution = solution
  exact zero_vadd _ _

/-- Successive gauge translations compose by addition. -/
theorem additiveRepairGaugeAction_add
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (left right : AdditiveRepairGauge data)
    (solution : AdditiveRepairSolution data) :
    data.additiveRepairGaugeAction (left + right) solution =
      data.additiveRepairGaugeAction left (data.additiveRepairGaugeAction right solution) := by
  change (left + right) +ᵥ solution = left +ᵥ (right +ᵥ solution)
  exact add_vadd _ _ _

/-- The gauge difference sends one solution to the other. -/
theorem additiveRepairGaugeBetween_action
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (source target : AdditiveRepairSolution data) :
    data.additiveRepairGaugeAction (data.additiveRepairGaugeBetween source target) source =
      target := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  apply Subtype.ext
  change target.1 - source.1 + source.1 = target.1
  abel

/-- The gauge action is free on the repair-solution carrier. -/
theorem additiveRepairGaugeAction_free
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    {left right : AdditiveRepairGauge data}
    {solution : AdditiveRepairSolution data}
    (haction : data.additiveRepairGaugeAction left solution =
      data.additiveRepairGaugeAction right solution) :
    left = right := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  apply Subtype.ext
  have hvalue := congrArg Subtype.val haction
  change left.1 + solution.1 = right.1 + solution.1 at hvalue
  calc
    left.1 = (left.1 + solution.1) - solution.1 := by abel
    _ = (right.1 + solution.1) - solution.1 := by rw [hvalue]
    _ = right.1 := by abel

/-- The gauge action is simply transitive whenever two repair solutions are given. -/
def AdditiveRepairGaugeActsSimplyTransitively
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  forall source target : AdditiveRepairSolution data,
    ExistsUnique fun gauge : AdditiveRepairGauge data =>
      gauge +ᵥ source = target

/-- The repair-solution carrier has the additive gauge torsor law. -/
theorem additiveRepairGaugeActsSimplyTransitively
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    data.AdditiveRepairGaugeActsSimplyTransitively := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  intro source target
  refine ⟨data.additiveRepairGaugeBetween source target,
    data.additiveRepairGaugeBetween_action source target, ?_⟩
  intro gauge hgauge
  apply data.additiveRepairGaugeAction_free
  calc
    data.additiveRepairGaugeAction gauge source = target := hgauge
    _ = data.additiveRepairGaugeAction
          (data.additiveRepairGaugeBetween source target) source :=
      (data.additiveRepairGaugeBetween_action source target).symm

/-- A selected additive H1-zero proof determines one residual-solving primitive. -/
def additiveRepairSolution_of_h1Zero
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    AdditiveRepairSolution data := by
  let hboundary := data.toAdditiveCechH1Data.h1Zero_iff_boundary.mp hzero
  exact ⟨Classical.choose hboundary, Classical.choose_spec hboundary⟩

/-- Existence of a repair solution is equivalent to the selected H1-zero statement. -/
theorem additiveRepairSolution_nonempty_iff_h1Zero
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Nonempty (AdditiveRepairSolution data) <-> data.toAdditiveCechH1Data.H1Zero := by
  constructor
  · intro hsolution
    rcases hsolution with ⟨solution⟩
    exact data.toAdditiveCechH1Data.h1Zero_iff_boundary.mpr ⟨solution.1, solution.2⟩
  · intro hzero
    exact ⟨data.additiveRepairSolution_of_h1Zero hzero⟩

/--
Part IV torsor layer in the additive specialization: a chosen H1-zero proof
produces a pointed torsor under the explicit gauge group.  This does not claim
triviality for an arbitrary nonadditive torsor.
-/
def NonabelianTorsorTrivial
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  data.toAdditiveCechH1Data.H1Zero ->
    exists origin : AdditiveRepairSolution data,
      forall target : AdditiveRepairSolution data,
        ExistsUnique fun gauge : AdditiveRepairGauge data =>
          data.additiveRepairGaugeAction gauge origin = target

/-- The H1-zero proof supplies the pointed additive torsor. -/
theorem nonabelianTorsorTrivial_of_additiveH1Zero
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    data.NonabelianTorsorTrivial := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  intro hzero
  let origin := data.additiveRepairSolution_of_h1Zero hzero
  refine ⟨origin, ?_⟩
  intro target
  exact data.additiveRepairGaugeActsSimplyTransitively origin target

/-- The selected degree-two coherence defect on one actual triple face. -/
def SelectedHigherCoherenceDefect
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    {i j k : data.boundaryRelation.cover.CoverChart}
    (triple : data.boundaryRelation.cover.TripleOverlap i j k) : realization.Fiber :=
  realization.eval2
    (data.boundaryRelation.cech.delta1 data.boundaryRelation.cech.residual) triple

/-- The selected degree-two coherence defect vanishes on every actual triple face. -/
def SelectedHigherCoherenceTrivialization
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech) : Prop :=
  forall {i j k : data.boundaryRelation.cover.CoverChart}
    (triple : data.boundaryRelation.cover.TripleOverlap i j k),
    data.SelectedHigherCoherenceDefect realization triple = 0

/--
The selected higher-coherence predicate is indexed by a concrete compatible
realization.  It is the facewise transition equation, not a claim that an
arbitrary H2 surface vanishes.
-/
def HigherCoherenceVanishes
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech) :
    Prop :=
  data.SelectedHigherCoherenceTrivialization realization

/-- The aggregate residual cocycle gives a zero witness for every selected C2 defect. -/
theorem selectedHigherCoherenceTrivialization_of_additive
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech) :
    data.SelectedHigherCoherenceTrivialization realization := by
  intro i j k triple
  change realization.eval2
    (data.boundaryRelation.cech.delta1 data.boundaryRelation.cech.residual) triple = 0
  calc
    realization.eval2
        (data.boundaryRelation.cech.delta1 data.boundaryRelation.cech.residual) triple =
        realization.eval2 data.boundaryRelation.cech.zero2 triple := by
          rw [data.boundaryRelation.cech.residual_cocycle]
    _ = 0 := realization.eval_zero2 triple

/-- A zero selected C2 defect gives the facewise transition equation. -/
theorem selectedHigherCoherence_facewise
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (hcoherence : data.SelectedHigherCoherenceTrivialization realization)
    {i j k : data.boundaryRelation.cover.CoverChart}
    (triple : data.boundaryRelation.cover.TripleOverlap i j k) :
    realization.eval1 data.boundaryRelation.cech.residual
        (data.boundaryRelation.cover.tripleEdge01 triple) +
      realization.eval1 data.boundaryRelation.cech.residual
        (data.boundaryRelation.cover.tripleEdge12 triple) =
    realization.eval1 data.boundaryRelation.cech.residual
      (data.boundaryRelation.cover.tripleEdge02 triple) := by
  apply sub_eq_zero.mp
  calc
    realization.eval1 data.boundaryRelation.cech.residual
          (data.boundaryRelation.cover.tripleEdge01 triple) +
        realization.eval1 data.boundaryRelation.cech.residual
          (data.boundaryRelation.cover.tripleEdge12 triple) -
          realization.eval1 data.boundaryRelation.cech.residual
            (data.boundaryRelation.cover.tripleEdge02 triple) =
        data.SelectedHigherCoherenceDefect realization triple := by
          exact (realization.eval_delta1 data.boundaryRelation.cech.residual triple).symm
    _ = 0 := hcoherence triple

/-- The selected compatible realization has the facewise higher coherence. -/
theorem higherCoherenceVanishes_of_additive
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech) :
    data.HigherCoherenceVanishes realization := by
  exact data.selectedHigherCoherenceTrivialization_of_additive realization

/-- The Part VI base generated by the actual repair-cover cells and incidence. -/
def additiveRepairCoverStackBase
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    SingularityMonodromyStack.ArchitectureStackBase.{w} where
  Context := AdditiveRepairCoverContext data.boundaryRelation.cover
  Overlap := fun left right =>
    { edge : (Sigma fun i : data.boundaryRelation.cover.CoverChart =>
        Sigma fun j : data.boundaryRelation.cover.CoverChart =>
          data.boundaryRelation.cover.Overlap i j) //
      left = AdditiveRepairCoverContext.chart edge.1 /\
        right = AdditiveRepairCoverContext.chart edge.2.1 }
  TripleOverlap := fun left middle right =>
    { face : (Sigma fun i : data.boundaryRelation.cover.CoverChart =>
        Sigma fun j : data.boundaryRelation.cover.CoverChart =>
          Sigma fun k : data.boundaryRelation.cover.CoverChart =>
            data.boundaryRelation.cover.TripleOverlap i j k) //
      left = AdditiveRepairCoverContext.chart face.1 /\
        middle = AdditiveRepairCoverContext.chart face.2.1 /\
          right = AdditiveRepairCoverContext.chart face.2.2.1 }
  restrict := AdditiveRepairCoverContext.Restrict
  idRestrict := by
    intro context
    refine ⟨ULift.up PUnit.unit, ?_⟩
    cases context with
    | global => exact Or.inl rfl
    | chart value =>
        refine Or.inr ⟨?_, fun _ h => h⟩
        intro h
        cases h
    | overlap value =>
        refine Or.inr ⟨?_, fun _ h => h⟩
        intro h
        cases h
    | triple value =>
        refine Or.inr ⟨?_, fun _ h => h⟩
        intro h
        cases h
  compRestrict := by
    intro T U V restriction next
    refine ⟨ULift.up PUnit.unit, ?_⟩
    rcases restriction.2 with hglobal | ⟨hsource, hrestriction⟩
    · exact Or.inl hglobal
    · rcases next.2 with hmiddleGlobal | ⟨hnextSource, hnext⟩
      · exact False.elim (hsource hmiddleGlobal)
      · exact Or.inr ⟨hnextSource, fun chart h => hnext chart (hrestriction chart h)⟩
  id_comp := by
    intro _ _ restriction
    apply Subtype.ext
    apply ULift.ext
    exact PUnit.ext _ _
  comp_id := by
    intro _ _ restriction
    apply Subtype.ext
    apply ULift.ext
    exact PUnit.ext _ _
  assoc := by
    intro _ _ _ _ _ _ _
    apply Subtype.ext
    apply ULift.ext
    exact PUnit.ext _ _
  overlapContext := fun overlap =>
    match overlap with
    | ⟨⟨i, j, edge⟩, _⟩ => .overlap ⟨(i, j), edge⟩
  overlap_left := by
    intro left right overlap
    refine ⟨ULift.up PUnit.unit, ?_⟩
    refine Or.inr ⟨?_, ?_⟩
    · intro h
      cases h
    · intro chart hchart
      rcases overlap with ⟨⟨i, j, edge⟩, hleft, hright⟩
      cases hleft
      exact Or.inl hchart
  overlap_right := by
    intro left right overlap
    refine ⟨ULift.up PUnit.unit, ?_⟩
    refine Or.inr ⟨?_, ?_⟩
    · intro h
      cases h
    · intro chart hchart
      rcases overlap with ⟨⟨i, j, edge⟩, hleft, hright⟩
      cases hright
      exact Or.inr hchart
  tripleContext := fun triple =>
    match triple with
    | ⟨⟨i, j, k, face⟩, _⟩ => .triple ⟨(i, j, k), face⟩
  triple_to_leftOverlap := by
    intro left middle right overlap triple
    refine ⟨ULift.up PUnit.unit, ?_⟩
    refine Or.inr ⟨?_, ?_⟩
    · intro h
      cases h
    · intro chart hchart
      rcases overlap with ⟨⟨i, j, edge⟩, hleft, hmiddle⟩
      rcases triple with ⟨⟨a, b, c, face⟩, htripleLeft, htripleMiddle, htripleRight⟩
      have hi : AdditiveRepairCoverContext.chart i = AdditiveRepairCoverContext.chart a :=
        hleft.symm.trans htripleLeft
      have hj : AdditiveRepairCoverContext.chart j = AdditiveRepairCoverContext.chart b :=
        hmiddle.symm.trans htripleMiddle
      injection hi with hi
      injection hj with hj
      subst a
      subst b
      exact Or.elim hchart Or.inl (fun h => Or.inr (Or.inl h))
  triple_to_rightOverlap := by
    intro left middle right overlap triple
    refine ⟨ULift.up PUnit.unit, ?_⟩
    refine Or.inr ⟨?_, ?_⟩
    · intro h
      cases h
    · intro chart hchart
      rcases overlap with ⟨⟨j, k, edge⟩, hmiddle, hright⟩
      rcases triple with ⟨⟨a, b, c, face⟩, htripleLeft, htripleMiddle, htripleRight⟩
      have hj : AdditiveRepairCoverContext.chart j = AdditiveRepairCoverContext.chart b :=
        hmiddle.symm.trans htripleMiddle
      have hk : AdditiveRepairCoverContext.chart k = AdditiveRepairCoverContext.chart c :=
        hright.symm.trans htripleRight
      injection hj with hj
      injection hk with hk
      subst b
      subst c
      exact Or.elim hchart (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  triple_to_outerOverlap := by
    intro left middle right overlap triple
    refine ⟨ULift.up PUnit.unit, ?_⟩
    refine Or.inr ⟨?_, ?_⟩
    · intro h
      cases h
    · intro chart hchart
      rcases overlap with ⟨⟨i, k, edge⟩, hleft, hright⟩
      rcases triple with ⟨⟨a, b, c, face⟩, htripleLeft, htripleMiddle, htripleRight⟩
      have hi : AdditiveRepairCoverContext.chart i = AdditiveRepairCoverContext.chart a :=
        hleft.symm.trans htripleLeft
      have hk : AdditiveRepairCoverContext.chart k = AdditiveRepairCoverContext.chart c :=
        hright.symm.trans htripleRight
      injection hi with hi
      injection hk with hk
      subst a
      subst c
      exact Or.elim hchart Or.inl (fun h => Or.inr (Or.inr h))

/-- A translation in one additive fiber. -/
def AdditiveFiberTranslation
    {F : Type w} [AddCommGroup F] (source target : F) : Type w :=
  { translation : F // translation + source = target }

/-- The canonical fiber translation. -/
def additiveFiberTranslation
    {F : Type w} [AddCommGroup F] (source target : F) :
    AdditiveFiberTranslation source target :=
  ⟨target - source, by abel⟩

/-- A fiber translation between fixed objects is unique. -/
theorem additiveFiberTranslation_unique
    {F : Type w} [AddCommGroup F] {source target : F}
    (first second : AdditiveFiberTranslation source target) : first = second := by
  apply Subtype.ext
  calc
    first.1 = (first.1 + source) - source := by abel
    _ = (second.1 + source) - source := by rw [first.2, second.2]
    _ = second.1 := by abel

/-- The constant additive-fiber groupoid on the repair-cover Part VI base. -/
def additiveRepairCoverTranslationPresheaf
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech) :
    SingularityMonodromyStack.ArchitecturePresheaf
      data.additiveRepairCoverStackBase := by
  letI := realization.fiberAddCommGroup
  exact
    { Obj := fun _ => realization.Fiber
      Iso := fun source target => AdditiveFiberTranslation source target
      id := fun _ => ⟨0, by simp⟩
      inv := fun translation => ⟨-translation.1, by
        calc
          -translation.1 + _ = -translation.1 + (translation.1 + _) := by
            rw [translation.2]
          _ = _ := by abel⟩
      comp := fun {_} {source middle target} first second =>
        ⟨second.1 + first.1, by
          calc
            second.1 + first.1 + source = second.1 + (first.1 + source) := by abel
            _ = second.1 + middle := by rw [first.2]
            _ = target := second.2⟩
      id_comp := fun {_} {_ _} translation => by
        apply Subtype.ext
        simp
      comp_id := fun {_} {_ _} translation => by
        apply Subtype.ext
        simp
      assoc := fun {_} {_ _ _ _} first second third => by
        apply Subtype.ext
        change third.1 + (second.1 + first.1) = (third.1 + second.1) + first.1
        ac_rfl
      inv_comp := fun {_} {_ _} translation => by
        apply Subtype.ext
        simp
      comp_inv := fun {_} {_ _} translation => by
        apply Subtype.ext
        simp
      pullbackObj := fun _ object => object
      pullbackIso := fun {_ _} _ {_ _} translation => translation
      pullback_id := fun {_ _} _ _ => rfl
      pullback_comp := fun {_ _} _ {_ _ _} _ _ => rfl
      pullbackBaseId := fun {_} _ => rfl
      pullbackBaseComp := fun {_ _ _} _ _ _ => rfl
      pullbackIsoBaseId := fun {_} {_ _} _ => HEq.rfl
      pullbackIsoBaseComp := fun {_ _ _} _ _ {_ _} _ => HEq.rfl }

/-- A solution realizes the residual as a local difference on each overlap. -/
theorem residualTransition_eq_localDifference
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (solution : AdditiveRepairSolution data)
    {left right : data.boundaryRelation.cover.CoverChart}
    (overlap : data.boundaryRelation.cover.Overlap left right) :
    realization.eval1 data.boundaryRelation.cech.residual overlap =
      realization.eval0 solution.1 right - realization.eval0 solution.1 left := by
  calc
    realization.eval1 data.boundaryRelation.cech.residual overlap =
        realization.eval1 (data.boundaryRelation.cech.delta0 solution.1) overlap := by
          rw [solution.2]
    _ = realization.eval0 solution.1 right - realization.eval0 solution.1 left :=
      realization.eval_delta0 solution.1 overlap

/-- Local additive-fiber objects selected by one H1-zero repair solution. -/
def selectedRepairLocalObjects
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    SingularityMonodromyStack.LocalArchitectureObjects
      (data.additiveRepairCoverTranslationPresheaf realization) := by
  let solution := data.additiveRepairSolution_of_h1Zero hzero
  exact
    { CoverIndex := data.boundaryRelation.cover.CoverChart
      context := fun chart =>
        AdditiveRepairCoverContext.chart (cover := data.boundaryRelation.cover) chart
      object := fun chart => realization.eval0 solution.1 chart }

/--
The selected repair descent datum uses actual overlaps and triple overlaps.
The selection proves that its pairwise comparisons are the three edges of
each selected triple face.
-/
def selectedRepairDescentDatum
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    SingularityMonodromyStack.ArchitectureDescentDatum
      (data.additiveRepairCoverTranslationPresheaf realization)
      (data.selectedRepairLocalObjects realization hzero) := by
  letI := realization.fiberAddCommGroup
  let solution := data.additiveRepairSolution_of_h1Zero hzero
  let selection := data.boundaryRelation.cover.toDescentSelection
  exact
    { overlap := fun i j => ⟨⟨i, j, selection.overlap i j⟩, rfl, rfl⟩
      overlapIso := fun i j =>
        ⟨realization.eval1 data.boundaryRelation.cech.residual (selection.overlap i j), by
          have htransition :=
            data.residualTransition_eq_localDifference realization solution (selection.overlap i j)
          calc
            realization.eval1 data.boundaryRelation.cech.residual (selection.overlap i j) +
                realization.eval0 solution.1 i =
                (realization.eval0 solution.1 j - realization.eval0 solution.1 i) +
                  realization.eval0 solution.1 i := by rw [htransition]
            _ = realization.eval0 solution.1 j := by abel⟩
      triple := fun i j k => ⟨⟨i, j, k, selection.triple i j k⟩, rfl, rfl, rfl⟩
      tripleCocycle := fun i j k =>
        { left := realization.eval0 solution.1 i
          middle := realization.eval0 solution.1 j
          right := realization.eval0 solution.1 k
          ij := ⟨realization.eval1 data.boundaryRelation.cech.residual
              (selection.overlap i j), by
            have htransition := data.residualTransition_eq_localDifference
              realization solution (selection.overlap i j)
            calc
              realization.eval1 data.boundaryRelation.cech.residual
                  (selection.overlap i j) +
                    realization.eval0 solution.1 i =
                  (realization.eval0 solution.1 j - realization.eval0 solution.1 i) +
                    realization.eval0 solution.1 i := by rw [htransition]
              _ = realization.eval0 solution.1 j := by abel⟩
          jk := ⟨realization.eval1 data.boundaryRelation.cech.residual
              (selection.overlap j k), by
            have htransition := data.residualTransition_eq_localDifference
              realization solution (selection.overlap j k)
            calc
              realization.eval1 data.boundaryRelation.cech.residual
                  (selection.overlap j k) +
                    realization.eval0 solution.1 j =
                  (realization.eval0 solution.1 k - realization.eval0 solution.1 j) +
                    realization.eval0 solution.1 j := by rw [htransition]
              _ = realization.eval0 solution.1 k := by abel⟩
          ik := ⟨realization.eval1 data.boundaryRelation.cech.residual
              (selection.overlap i k), by
            have htransition := data.residualTransition_eq_localDifference
              realization solution (selection.overlap i k)
            calc
              realization.eval1 data.boundaryRelation.cech.residual
                  (selection.overlap i k) +
                    realization.eval0 solution.1 i =
                  (realization.eval0 solution.1 k - realization.eval0 solution.1 i) +
                    realization.eval0 solution.1 i := by rw [htransition]
              _ = realization.eval0 solution.1 k := by abel⟩
          cocycle_eq := by
            apply Subtype.ext
            change realization.eval1 data.boundaryRelation.cech.residual
                (selection.overlap j k) +
                realization.eval1 data.boundaryRelation.cech.residual
                  (selection.overlap i j) =
              realization.eval1 data.boundaryRelation.cech.residual
                (selection.overlap i k)
            rw [selection.overlap_eq_tripleEdge12,
              selection.overlap_eq_tripleEdge01,
              selection.overlap_eq_tripleEdge02]
            rw [add_comm]
            exact data.selectedHigherCoherence_facewise realization
              (data.selectedHigherCoherenceTrivialization_of_additive realization)
              (selection.triple i j k) }
      cocycleCondition := fun overlapIsomorphisms _ =>
        forall i j k,
          (data.additiveRepairCoverTranslationPresheaf realization).comp
              (overlapIsomorphisms i j) (overlapIsomorphisms j k) =
            overlapIsomorphisms i k
      cocycleCondition_holds := by
        intro i j k
        apply Subtype.ext
        change realization.eval1 data.boundaryRelation.cech.residual
            (selection.overlap j k) +
            realization.eval1 data.boundaryRelation.cech.residual
              (selection.overlap i j) =
          realization.eval1 data.boundaryRelation.cech.residual
            (selection.overlap i k)
        rw [selection.overlap_eq_tripleEdge12,
          selection.overlap_eq_tripleEdge01,
          selection.overlap_eq_tripleEdge02, add_comm]
        exact data.selectedHigherCoherence_facewise realization
          (data.selectedHigherCoherenceTrivialization_of_additive realization)
          (selection.triple i j k) }

/--
An H1-zero proof constructs effective descent for the selected repair datum,
not for arbitrary local data on the cover.
-/
def selectedRepairEffectiveDescent_of_h1Zero
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    SingularityMonodromyStack.EffectiveArchitectureDescent
      (data.additiveRepairCoverTranslationPresheaf realization)
      (data.selectedRepairDescentDatum realization hzero) := by
  letI := realization.fiberAddCommGroup
  let solution := data.additiveRepairSolution_of_h1Zero hzero
  refine
    { globalContext := AdditiveRepairCoverContext.global (cover := data.boundaryRelation.cover)
      globalObject := (0 : realization.Fiber)
      restrictToLocal := ?_
      localComparison := ?_
      realizesOverlapData := ?_
      realizesOverlapData_holds := ?_ }
  · intro _
    exact ⟨ULift.up PUnit.unit, Or.inl rfl⟩
  · intro chart
    exact ⟨realization.eval0 solution.1 chart, by
      change realization.eval0 solution.1 chart + 0 = realization.eval0 solution.1 chart
      exact add_zero _⟩
  · intro localComparisons overlapIsomorphisms
    exact forall i j,
      overlapIsomorphisms i j =
        (data.additiveRepairCoverTranslationPresheaf realization).comp
          ((data.additiveRepairCoverTranslationPresheaf realization).inv (localComparisons i))
          (localComparisons j)
  · intro i j
    apply additiveFiberTranslation_unique

/--
The selected stack-facing conclusion is indexed by an actual realization and
an H1-zero proof.  The complete repair-cover selection is part of the cover
geometry, and the conclusion asserts effective descent for its selected datum.
-/
def StackEffectivelyVanishes
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    Prop :=
  Nonempty (SingularityMonodromyStack.EffectiveArchitectureDescent
    (data.additiveRepairCoverTranslationPresheaf realization)
    (data.selectedRepairDescentDatum realization hzero))

/-- The selected effective-descent datum is constructed from the additive H1-zero proof. -/
theorem stackEffectivelyVanishes_of_additive
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    data.StackEffectivelyVanishes realization hzero := by
  exact ⟨data.selectedRepairEffectiveDescent_of_h1Zero realization hzero⟩

/--
An actual cover-indexed realization and an H1-zero proof give both selected
facewise higher coherence and effective descent for the selected repair datum.
-/
theorem selectedHigherCoherenceAndEffectiveDescent_of_additive
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (realization : SemanticRepairCoverCechRealization
      data.boundaryRelation.cover data.boundaryRelation.cech)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    data.HigherCoherenceVanishes realization /\
      data.StackEffectivelyVanishes realization hzero := by
  exact ⟨data.higherCoherenceVanishes_of_additive realization,
    data.stackEffectivelyVanishes_of_additive realization hzero⟩

/-- X.定理4.8: cover membership and a sheaf condition generate the cover sheaf condition. -/
theorem coverSheafConditionFor_of_trueSheafCertificate
    {P : SemanticAtomProjection.{u, v}}
    {data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    {U : AtomCarrier.{r}}
    {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (certificate : TrueSheafConditionCertificate data S F cover) :
    Site.AATSheafConditionFor S F cover :=
  Site.AATSheafCondition.cover
    certificate.sheafCondition cover certificate.cover_mem

/-- X.定理4.8: the cover sheaf condition generates descent for the selected cover. -/
theorem coverDescent_of_trueSheafCertificate
    {P : SemanticAtomProjection.{u, v}}
    {data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    {U : AtomCarrier.{r}}
    {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (certificate : TrueSheafConditionCertificate data S F cover) :
    Site.AATDescent S F cover :=
  (coverSheafConditionFor_of_trueSheafCertificate certificate).descent

/--
X.定理4.8: in the boundary-relation additive surface, global semantic repair
coherence is equivalent to vanishing of the selected additive Cech H1 class.

The reverse implication uses the boundary-relation faithfulness data and the
additive regime.  It is not derived from the cover sheaf condition in
`TrueSheafConditionCertificate`; the sheaf certificate supplies the cover
sheaf/descent conclusions only.
-/
theorem globalRepairCoherent_iff_additiveH1Zero
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    GlobalSemanticRepairCoherent
        data.boundaryRelation.toFiniteGluingComplex <->
      data.toAdditiveCechH1Data.H1Zero := by
  have hfinite :
      GlobalSemanticRepairCoherent
          data.boundaryRelation.toFiniteGluingComplex <->
        ObstructionClassVanishes
          data.boundaryRelation.toFiniteGluingComplex :=
    finiteSemanticRepairGluingDescent_iff
      data.boundaryRelation.toFiniteGluingComplex
      data.boundaryRelation.semanticFaithfulnessHypotheses
  have hquot :
      data.toAdditiveCechH1Data.H1Zero <->
        CechB1 data.boundaryRelation.cech
          data.boundaryRelation.cech.residual :=
    data.toAdditiveCechH1Data.h1Zero_iff_boundary
  constructor
  · intro hglobal
    exact hquot.mpr (hfinite.mp hglobal)
  · intro hzero
    exact data.globalRepairCoherent_of_additiveH1Zero hzero

/-! ## X.命題4.9 finite complex shadow -/

/--
X.命題4.9: comparison data from the additive cover H1 surface to a selected
§3 finite gluing complex.

The comparison records only the primitive/cochain equivalences and their
compatibility with `delta0` and the selected residual.  It does not store H1
zero, obstruction vanishing, or global semantic repair coherence.
-/
structure SemanticRepairAdditiveFiniteComparison
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) where
  c0Equiv : data.boundaryRelation.cech.C0 ≃ K.C0
  c1Equiv : data.boundaryRelation.cech.C1 ≃ K.C1
  delta0_compat :
    forall primitive,
      c1Equiv (data.boundaryRelation.cech.delta0 primitive) =
        K.delta0 (c0Equiv primitive)
  residual_compat :
    c1Equiv data.boundaryRelation.cech.residual = K.residual

/-- X.命題4.9: cover boundary membership maps to the selected finite obstruction boundary. -/
theorem finiteShadow_obstructionVanishes_of_coverBoundary
    {P : SemanticAtomProjection.{u, v}}
    {data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    {K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}}
    (comparison : SemanticRepairAdditiveFiniteComparison data K) :
    CechB1 data.boundaryRelation.cech data.boundaryRelation.cech.residual ->
      ObstructionClassVanishes K := by
  intro hboundary
  rcases hboundary with ⟨primitive, hprimitive⟩
  refine ⟨comparison.c0Equiv primitive, ?_⟩
  calc
    K.delta0 (comparison.c0Equiv primitive) =
        comparison.c1Equiv (data.boundaryRelation.cech.delta0 primitive) := by
      exact (comparison.delta0_compat primitive).symm
    _ = comparison.c1Equiv data.boundaryRelation.cech.residual := by
      rw [hprimitive]
    _ = K.residual := comparison.residual_compat

/-- X.命題4.9: selected finite obstruction vanishing maps back to cover boundary membership. -/
theorem coverBoundary_of_finiteShadow_obstructionVanishes
    {P : SemanticAtomProjection.{u, v}}
    {data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    {K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}}
    (comparison : SemanticRepairAdditiveFiniteComparison data K) :
    ObstructionClassVanishes K ->
      CechB1 data.boundaryRelation.cech data.boundaryRelation.cech.residual := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hprimitive⟩
  refine ⟨comparison.c0Equiv.symm primitive, ?_⟩
  apply comparison.c1Equiv.injective
  rw [comparison.delta0_compat, comparison.residual_compat]
  simpa using hprimitive

/-- X.命題4.9: additive H1 zero is the selected finite complex shadow. -/
theorem additiveH1Zero_iff_finiteShadow_obstructionVanishes
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (comparison : SemanticRepairAdditiveFiniteComparison data K) :
    data.toAdditiveCechH1Data.H1Zero <-> ObstructionClassVanishes K := by
  constructor
  · intro hzero
    exact
      finiteShadow_obstructionVanishes_of_coverBoundary comparison
        ((semanticRepairAdditiveH1Zero_iff_boundary
          data.toAdditiveCechH1Data).1 hzero)
  · intro hvanishes
    exact
      (semanticRepairAdditiveH1Zero_iff_boundary
        data.toAdditiveCechH1Data).2
        (coverBoundary_of_finiteShadow_obstructionVanishes
          comparison hvanishes)

/-- X.命題4.9 package: finite complex shadow for additive semantic repair H1. -/
theorem finiteShadowComparison_package
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (comparison : SemanticRepairAdditiveFiniteComparison data K) :
    (data.toAdditiveCechH1Data.H1Zero <-> ObstructionClassVanishes K) /\
      (CechB1 data.boundaryRelation.cech
          data.boundaryRelation.cech.residual ->
        ObstructionClassVanishes K) /\
      (ObstructionClassVanishes K ->
        CechB1 data.boundaryRelation.cech
          data.boundaryRelation.cech.residual) := by
  exact
    ⟨additiveH1Zero_iff_finiteShadow_obstructionVanishes data K comparison,
      finiteShadow_obstructionVanishes_of_coverBoundary comparison,
      coverBoundary_of_finiteShadow_obstructionVanishes comparison⟩

/-! ## X.命題4.10 refinement pullback -/

/--
X.命題4.10: selected finite refinement from a fine semantic repair cover to a
coarse one.

This is cover geometry only.  It does not carry boundary membership, H1 zero,
global coherence, or any converse-refinement assertion.
-/
structure SemanticRepairCoverRefinement
    {P : SemanticAtomProjection.{u, v}}
    (coarse fine : SemanticRepairCover.{u, v, w, x} P) where
  chartMap : fine.CoverChart -> coarse.CoverChart
  overlapMap :
    forall {left right},
      fine.Overlap left right ->
        coarse.Overlap (chartMap left) (chartMap right)
  tripleMap :
    forall {i j k},
      fine.TripleOverlap i j k ->
        coarse.TripleOverlap (chartMap i) (chartMap j) (chartMap k)

/--
X.命題4.10: Cech-level comparison data for pulling a coarse additive H1
surface back to a fine one.

The comparison records only primitive/cochain pullback and compatibility with
`delta0` and residual.  It does not include a reverse map.
-/
structure SemanticRepairAdditiveRefinementComparison
    {P : SemanticAtomProjection.{u, v}}
    (coarse fine :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) where
  refinement :
    SemanticRepairCoverRefinement coarse.boundaryRelation.cover
      fine.boundaryRelation.cover
  primitivePullback :
    coarse.boundaryRelation.cech.C0 -> fine.boundaryRelation.cech.C0
  cochainPullback :
    coarse.boundaryRelation.cech.C1 -> fine.boundaryRelation.cech.C1
  delta0_naturality :
    forall primitive,
      cochainPullback (coarse.boundaryRelation.cech.delta0 primitive) =
        fine.boundaryRelation.cech.delta0 (primitivePullback primitive)
  residual_naturality :
    cochainPullback coarse.boundaryRelation.cech.residual =
      fine.boundaryRelation.cech.residual

/-- X.命題4.10: a coarse boundary pulls back to a fine boundary. -/
theorem refinement_boundary_pullback
    {P : SemanticAtomProjection.{u, v}}
    {coarse fine :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    (comparison :
      SemanticRepairAdditiveRefinementComparison coarse fine) :
    CechB1 coarse.boundaryRelation.cech
        coarse.boundaryRelation.cech.residual ->
      CechB1 fine.boundaryRelation.cech
        fine.boundaryRelation.cech.residual := by
  intro hboundary
  rcases hboundary with ⟨primitive, hprimitive⟩
  refine ⟨comparison.primitivePullback primitive, ?_⟩
  calc
    fine.boundaryRelation.cech.delta0
        (comparison.primitivePullback primitive) =
        comparison.cochainPullback
          (coarse.boundaryRelation.cech.delta0 primitive) := by
      exact (comparison.delta0_naturality primitive).symm
    _ = comparison.cochainPullback coarse.boundaryRelation.cech.residual := by
      rw [hprimitive]
    _ = fine.boundaryRelation.cech.residual := comparison.residual_naturality

/-- X.命題4.10: additive H1 zero pulls back along the selected cover refinement. -/
theorem refinement_additiveH1Zero_pullback
    {P : SemanticAtomProjection.{u, v}}
    (coarse fine :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (comparison :
      SemanticRepairAdditiveRefinementComparison coarse fine) :
    coarse.toAdditiveCechH1Data.H1Zero ->
      fine.toAdditiveCechH1Data.H1Zero := by
  intro hzero
  exact
    (semanticRepairAdditiveH1Zero_iff_boundary
      fine.toAdditiveCechH1Data).2
      (refinement_boundary_pullback comparison
        ((semanticRepairAdditiveH1Zero_iff_boundary
          coarse.toAdditiveCechH1Data).1 hzero))

/-- X.命題4.10 package: selected refinement preserves boundary and H1-zero forward. -/
theorem refinementPullback_package
    {P : SemanticAtomProjection.{u, v}}
    (coarse fine :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (comparison :
      SemanticRepairAdditiveRefinementComparison coarse fine) :
    (CechB1 coarse.boundaryRelation.cech
        coarse.boundaryRelation.cech.residual ->
      CechB1 fine.boundaryRelation.cech
        fine.boundaryRelation.cech.residual) /\
      (coarse.toAdditiveCechH1Data.H1Zero ->
        fine.toAdditiveCechH1Data.H1Zero) := by
  exact
    ⟨refinement_boundary_pullback comparison,
      refinement_additiveH1Zero_pullback coarse fine comparison⟩

/--
X.定理4.8 [CBI]: true-sheaf H1 semantic repair-gluing, boundary-relation
additive package.

The core conclusion groups are exposed in the statement: cover sheaf/descent,
cocycle well-definedness, global-coherence/additive-H1 equivalence, quotient
boundary reading, and torsor trivialization.  The selected higher-coherence
and effective-descent construction is stated separately with its actual
realization input.
-/
theorem trueSheafH1SemanticRepairGluing_boundaryRelationAdditive_package
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    {U : AtomCarrier.{r}}
    {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {base : S.category}
    {cover : Sieve base}
    (certificate : TrueSheafConditionCertificate data S F cover) :
    Site.AATSheafConditionFor S F cover /\
      Site.AATDescent S F cover /\
      CechZ1 data.boundaryRelation.cech data.boundaryRelation.cech.residual /\
      (forall primitive,
        CechZ1 data.boundaryRelation.cech
          (data.boundaryRelation.cech.delta0 primitive)) /\
      (GlobalSemanticRepairCoherent
            data.boundaryRelation.toFiniteGluingComplex <->
          data.toAdditiveCechH1Data.H1Zero) /\
      (data.toAdditiveCechH1Data.H1Zero <->
        CechB1 data.boundaryRelation.cech
          data.boundaryRelation.cech.residual) /\
      NonabelianTorsorTrivial data := by
  exact
    ⟨coverSheafConditionFor_of_trueSheafCertificate certificate,
      coverDescent_of_trueSheafCertificate certificate,
      data.boundaryRelation.cech.residual_cocycle,
      data.boundaryRelation.cech.delta1_delta0_eq_zero,
      globalRepairCoherent_iff_additiveH1Zero data,
      data.toAdditiveCechH1Data.h1Zero_iff_boundary,
      nonabelianTorsorTrivial_of_additiveH1Zero data⟩

end SemanticRepairCoverH1BoundaryRelationAdditiveData

end SemanticRepair
end AAT.AG
