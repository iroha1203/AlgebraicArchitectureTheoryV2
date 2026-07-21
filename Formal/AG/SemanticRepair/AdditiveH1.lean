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
  chartFinite : Fintype CoverChart
  Overlap : CoverChart -> CoverChart -> Type w
  overlapFinite : forall left right, Fintype (Overlap left right)
  TripleOverlap : CoverChart -> CoverChart -> CoverChart -> Type w
  tripleFinite : forall i j k, Fintype (TripleOverlap i j k)
  tripleEdge01 : forall {i j k}, TripleOverlap i j k -> Overlap i j
  tripleEdge12 : forall {i j k}, TripleOverlap i j k -> Overlap j k
  tripleEdge02 : forall {i j k}, TripleOverlap i j k -> Overlap i k

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
  zero1_eq_zero : cech.zero1 = 0
  delta0_zero : cech.delta0 0 = 0
  delta0_add :
    forall left right,
      cech.delta0 (left + right) = cech.delta0 left + cech.delta0 right
  delta0_neg : forall primitive, cech.delta0 (-primitive) = -cech.delta0 primitive

namespace SemanticRepairAdditiveCechH1Data

attribute [instance] c0AddCommGroup c1AddCommGroup

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
X.定理4.8 conclusion 5, torsor layer: additive primitives whose coboundary is
the selected residual.  This is the actual repair-solution carrier, rather
than the ambient degree-zero cochain carrier.
-/
def AdditiveRepairSolution
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Type y :=
  { primitive : data.boundaryRelation.cech.C0 //
    data.boundaryRelation.cech.delta0 primitive =
      data.boundaryRelation.cech.residual }

/--
X.定理4.8 conclusion 5: a translation between two actual additive repair
solutions.  Its equality is the selected torsor action equation.
-/
def AdditiveRepairPrimitiveTranslation
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    [AddCommGroup data.boundaryRelation.cech.C0]
    (source target : AdditiveRepairSolution data) : Type y :=
  { translation : data.boundaryRelation.cech.C0 // translation + source.1 = target.1 }

/-- X.定理4.8 conclusion 5: the canonical translation between two solutions. -/
def additiveRepairPrimitiveTranslation
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    [AddCommGroup data.boundaryRelation.cech.C0]
    (source target : AdditiveRepairSolution data) :
    AdditiveRepairPrimitiveTranslation data source target :=
  ⟨target.1 - source.1, by abel⟩

/--
X.定理4.8 conclusion 5: a translation between residual-solving primitives has
zero coboundary, so it belongs to the additive stabilizer of the solution
torsor.
-/
theorem additiveRepairPrimitiveTranslation_stabilizes
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    [AddCommGroup data.boundaryRelation.cech.C0]
    [AddCommGroup data.boundaryRelation.cech.C1]
    {source target : AdditiveRepairSolution data}
    (translation : AdditiveRepairPrimitiveTranslation data source target) :
    data.boundaryRelation.cech.delta0 translation.1 = 0 := by
  calc
    data.boundaryRelation.cech.delta0 translation.1 =
        data.boundaryRelation.cech.delta0 translation.1 +
          data.boundaryRelation.cech.delta0 source.1 -
            data.boundaryRelation.cech.delta0 source.1 := by abel
    _ = data.boundaryRelation.cech.delta0 (translation.1 + source.1) -
          data.boundaryRelation.cech.delta0 source.1 := by
      rw [data.additive.delta0_add]
    _ = data.boundaryRelation.cech.residual - data.boundaryRelation.cech.residual := by
      rw [translation.2, source.2, target.2]
    _ = 0 := sub_self _

/-- X.定理4.8 conclusion 5: a translation between fixed solutions is unique. -/
theorem additiveRepairPrimitiveTranslation_unique
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    [AddCommGroup data.boundaryRelation.cech.C0]
    {source target : AdditiveRepairSolution data}
    (first second : AdditiveRepairPrimitiveTranslation data source target) :
    first = second := by
  apply Subtype.ext
  calc
    first.1 = (first.1 + source.1) - source.1 := by abel
    _ = (second.1 + source.1) - source.1 := by rw [first.2, second.2]
    _ = second.1 := by abel

/--
X.定理4.8 conclusion 5: a pointed regular torsor of actual repair solutions.
The origin is constructed from the selected additive `H1` zero statement.
-/
structure AdditiveRepairPrimitiveTorsor
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    [AddCommGroup data.boundaryRelation.cech.C0]
    [AddCommGroup data.boundaryRelation.cech.C1] where
  origin : AdditiveRepairSolution data
  translation : forall source target : AdditiveRepairSolution data,
    AdditiveRepairPrimitiveTranslation data source target
  translation_stabilizes : forall source target,
    data.boundaryRelation.cech.delta0 (translation source target).1 = 0
  translation_unique : forall source target
    (candidate : AdditiveRepairPrimitiveTranslation data source target),
    candidate = translation source target

/-- X.定理4.8 conclusion 5: construct the regular additive repair torsor. -/
def additiveRepairPrimitiveTorsor
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    letI := data.additive.c0AddCommGroup
    letI := data.additive.c1AddCommGroup
    AdditiveRepairPrimitiveTorsor data := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  rcases data.toAdditiveCechH1Data.h1Zero_iff_boundary.mp hzero with ⟨primitive, hprimitive⟩
  exact
    { origin := ⟨primitive, hprimitive⟩
      translation := fun source target => data.additiveRepairPrimitiveTranslation source target
      translation_stabilizes := fun source target =>
        data.additiveRepairPrimitiveTranslation_stabilizes
          (data.additiveRepairPrimitiveTranslation source target)
      translation_unique := fun source target candidate =>
        data.additiveRepairPrimitiveTranslation_unique candidate
    }

/--
X.定理4.8 conclusion 5: vanishing of the selected additive `H1` class
constructs a nonempty regular torsor of actual repair solutions, with the
additive stabilizer made explicit by `delta0 translation = 0`.
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
      forall source target : AdditiveRepairSolution data,
        ExistsUnique fun translation : data.boundaryRelation.cech.C0 =>
          translation + source.1 = target.1 /\
            data.boundaryRelation.cech.delta0 translation = 0

/-- X.定理4.8 conclusion 5: the regular additive repair torsor is constructed. -/
theorem nonabelianTorsorTrivial_of_additive
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    NonabelianTorsorTrivial data := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  intro hzero
  let torsor := data.additiveRepairPrimitiveTorsor hzero
  refine ⟨torsor.origin, ?_⟩
  intro source target
  refine ⟨(torsor.translation source target).1, ?_, ?_⟩
  · exact ⟨(torsor.translation source target).2,
      torsor.translation_stabilizes source target⟩
  · intro translation htranslation
    have candidate : AdditiveRepairPrimitiveTranslation data source target :=
      ⟨translation, htranslation.1⟩
    have hcandidate : candidate = torsor.translation source target :=
      torsor.translation_unique source target candidate
    exact congrArg Subtype.val hcandidate

/--
X.定理4.8 conclusion 5, higher-coherence layer: the selected degree-two
obstruction and its actual zero witness.
-/
structure AdditiveHigherCoherenceWitness
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) where
  higherObstruction : data.boundaryRelation.cech.C2
  higherObstruction_eq_residualDifferential :
    higherObstruction =
      data.boundaryRelation.cech.delta1 data.boundaryRelation.cech.residual
  vanishes : higherObstruction = data.boundaryRelation.cech.zero2

/-- X.定理4.8 conclusion 5: construct the higher-coherence zero witness. -/
def additiveHigherCoherenceWitness
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    AdditiveHigherCoherenceWitness data where
  higherObstruction := data.boundaryRelation.cech.delta1 data.boundaryRelation.cech.residual
  higherObstruction_eq_residualDifferential := rfl
  vanishes := data.boundaryRelation.cech.residual_cocycle

/--
X.定理4.8 conclusion 5: higher coherence is witnessed by the selected
degree-two obstruction and its zero equality.
-/
def HigherCoherenceVanishes
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  data.boundaryRelation.cech.delta1 data.boundaryRelation.cech.residual =
    data.boundaryRelation.cech.zero2

/-- X.定理4.8 conclusion 5: the higher-coherence witness is constructed. -/
theorem higherCoherenceVanishes_of_additive
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    HigherCoherenceVanishes data :=
  data.boundaryRelation.cech.residual_cocycle

/--
X.定理4.8 conclusion 5: the one-context base used for the additive
translation groupoid.
-/
def additiveTranslationStackBase
    {P : SemanticAtomProjection.{u, v}}
    (_data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    SingularityMonodromyStack.ArchitectureStackBase.{y} where
  Context := PUnit
  Overlap := fun _ _ => PUnit
  TripleOverlap := fun _ _ _ => PUnit
  restrict := fun _ _ => PUnit
  idRestrict := fun _ => PUnit.unit
  compRestrict := fun _ _ => PUnit.unit
  id_comp := fun {_ _} _ => Subsingleton.elim _ _
  comp_id := fun {_ _} _ => Subsingleton.elim _ _
  assoc := fun {_ _ _ _} _ _ _ => Subsingleton.elim _ _
  overlapContext := fun {_ _} _ => PUnit.unit
  overlap_left := fun {_ _} _ => PUnit.unit
  overlap_right := fun {_ _} _ => PUnit.unit
  tripleContext := fun {_ _ _} _ => PUnit.unit
  triple_to_leftOverlap := fun {_ _ _} _ _ => PUnit.unit
  triple_to_rightOverlap := fun {_ _ _} _ _ => PUnit.unit
  triple_to_outerOverlap := fun {_ _ _} _ _ => PUnit.unit

/--
X.定理4.8 conclusion 5: the groupoid-valued translation presheaf of actual
additive repair solutions.  Every isomorphism retains its translation equation.
-/
def additiveTranslationPresheaf
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    letI := data.additive.c0AddCommGroup
    SingularityMonodromyStack.ArchitecturePresheaf
      (additiveTranslationStackBase data) := by
  letI := data.additive.c0AddCommGroup
  exact
    { Obj := fun _ => AdditiveRepairSolution data
      Iso := fun source target =>
        AdditiveRepairPrimitiveTranslation data source target
      id := fun primitive => ⟨0, by simp⟩
      inv := fun translation =>
        ⟨-translation.1, by
          calc
            -translation.1 + _ = -translation.1 + (translation.1 + _) := by
              rw [translation.2]
            _ = _ := by abel⟩
      comp := fun {_} {source middle target} first second =>
        ⟨second.1 + first.1, by
          calc
            second.1 + first.1 + source.1 =
                second.1 + (first.1 + source.1) := by abel
            _ = second.1 + middle := by rw [first.2]
            _ = target.1 := second.2⟩
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
      pullbackObj := fun _ primitive => primitive
      pullbackIso := fun {_ _} _ {_ _} translation => translation
      pullback_id := fun {_ _} _ _ => rfl
      pullback_comp := fun {_ _} _ {_ _ _} _ _ => rfl
      pullbackBaseId := fun {_} _ => rfl
      pullbackBaseComp := fun {_ _ _} _ _ _ => rfl
      pullbackIsoBaseId := fun {_} {_ _} _ => HEq.rfl
      pullbackIsoBaseComp := fun {_ _ _} _ _ {_ _} _ => HEq.rfl }

/--
X.定理4.8 conclusion 5: construct effective descent for every selected local
datum in the additive repair-solution translation groupoid.
-/
def additiveTranslationArchitectureStack
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (hzero : data.toAdditiveCechH1Data.H1Zero) :
    letI := data.additive.c0AddCommGroup
    letI := data.additive.c1AddCommGroup
    SingularityMonodromyStack.ArchitectureStack
      (additiveTranslationPresheaf data) := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  let torsor := data.additiveRepairPrimitiveTorsor hzero
  refine { effectiveDescent := ?_ }
  intro localData descentDatum
  exact
    { globalContext := PUnit.unit
      globalObject := torsor.origin
      restrictToLocal := fun _ => PUnit.unit
      localComparison := fun localIndex =>
        torsor.translation torsor.origin (localData.object localIndex)
      realizesOverlapData := fun localComparisons overlapIsomorphisms =>
        forall i j,
          overlapIsomorphisms i j =
            (additiveTranslationPresheaf data).comp
              ((additiveTranslationPresheaf data).inv (localComparisons i))
              (localComparisons j)
      realizesOverlapData_holds := by
        intro i j
        apply additiveRepairPrimitiveTranslation_unique }

/--
X.定理4.8 conclusion 5: each selected additive translation datum has the
explicit effective-descent witness constructed above.
-/
def additiveTranslation_effectiveDescent
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (hzero : data.toAdditiveCechH1Data.H1Zero)
    (localData : SingularityMonodromyStack.LocalArchitectureObjects
      (additiveTranslationPresheaf data))
    (descentDatum : SingularityMonodromyStack.ArchitectureDescentDatum
      (additiveTranslationPresheaf data) localData) :
    letI := data.additive.c0AddCommGroup
    letI := data.additive.c1AddCommGroup
    SingularityMonodromyStack.EffectiveArchitectureDescent
      (additiveTranslationPresheaf data) descentDatum := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  exact data.additiveTranslationArchitectureStack hzero |>.effectiveDescent localData descentDatum

/--
X.定理4.8 conclusion 5: stack effectiveness means that the additive
translation presheaf has effective descent for every selected local datum.
-/
def StackEffectivelyVanishes
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  forall hzero : data.toAdditiveCechH1Data.H1Zero,
    forall (localData : SingularityMonodromyStack.LocalArchitectureObjects
        (additiveTranslationPresheaf data))
      (descentDatum : SingularityMonodromyStack.ArchitectureDescentDatum
        (additiveTranslationPresheaf data) localData),
      Nonempty (SingularityMonodromyStack.EffectiveArchitectureDescent
        (additiveTranslationPresheaf data) descentDatum)

/-- X.定理4.8 conclusion 5: the additive translation stack is constructed. -/
theorem stackEffectivelyVanishes_of_additive
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    StackEffectivelyVanishes data := by
  letI := data.additive.c0AddCommGroup
  letI := data.additive.c1AddCommGroup
  intro hzero localData descentDatum
  exact ⟨data.additiveTranslation_effectiveDescent hzero localData descentDatum⟩

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

The five conclusion groups are exposed in the statement: cover
sheaf/descent, cocycle well-definedness, global-coherence/additive-H1
equivalence, quotient boundary reading, and constructed later-layer vanishing.
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
      NonabelianTorsorTrivial data /\
      HigherCoherenceVanishes data /\
      StackEffectivelyVanishes data := by
  exact
    ⟨coverSheafConditionFor_of_trueSheafCertificate certificate,
      coverDescent_of_trueSheafCertificate certificate,
      data.boundaryRelation.cech.residual_cocycle,
      data.boundaryRelation.cech.delta1_delta0_eq_zero,
      globalRepairCoherent_iff_additiveH1Zero data,
      data.toAdditiveCechH1Data.h1Zero_iff_boundary,
      nonabelianTorsorTrivial_of_additive data,
      higherCoherenceVanishes_of_additive data,
      stackEffectivelyVanishes_of_additive data⟩

end SemanticRepairCoverH1BoundaryRelationAdditiveData

end SemanticRepair
end AAT.AG
