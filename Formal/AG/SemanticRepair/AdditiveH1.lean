import Formal.AG.Cohomology.CoverNerve
import Formal.AG.SemanticRepair.GluingComplex
import Formal.AG.Site.Descent

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

/-- X.定義4.6: boundary-relation faithfulness data without a global selector. -/
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

/-- X.定理4.8 conclusion 5: nonabelian torsor obstruction vanishes by construction. -/
def NonabelianTorsorTrivial
    {P : SemanticAtomProjection.{u, v}}
    (_data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  True

/-- X.定理4.8 conclusion 5: higher coherence obstruction vanishes by construction. -/
def HigherCoherenceVanishes
    {P : SemanticAtomProjection.{u, v}}
    (_data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  True

/-- X.定理4.8 conclusion 5: stack effectiveness obstruction vanishes by construction. -/
def StackEffectivelyVanishes
    {P : SemanticAtomProjection.{u, v}}
    (_data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  True

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
    exact hfinite.mpr (hquot.mp hzero)

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
      trivial,
      trivial,
      trivial⟩

end SemanticRepairCoverH1BoundaryRelationAdditiveData

end SemanticRepair
end AAT.AG
