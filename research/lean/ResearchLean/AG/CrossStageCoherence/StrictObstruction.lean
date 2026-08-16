import ResearchLean.AG.CrossStageCoherence.UpperObstruction

/-!
# The maximal strict inner obstruction

The strict sector contains every total 2-cell whose two path lifts already
agree as core-package morphisms and whose authored comparator projects to the
identity.  Thus it is a maximal subtype fixed by a qualification predicate,
not an authored selection of convenient faces.

Its canonical comparison is generated at the geometry projection and takes
values in `H_G`.  The resulting raw cochain is separately defined from the
total cochain.  A bridge theorem identifies its inclusion with restriction of
the total raw cochain, and a non-definitional theorem identifies strict orbit
vanishing with existence of one global edge coordinate satisfying all strict
path equations.

## Implementation notes

The strict sector is the subtype cut out by the full qualification predicate,
not an authored list of convenient faces.  Raw orbit vanishing and strict
coherentizability are kept separate so their equivalence is established by
the same cancellation and uniqueness mechanism as the total obstruction.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

/-- Full qualification for membership in the strict inner sector. -/
def StrictCellQualified {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U)
    (cell : P.TwoCell) : Prop :=
  (data.lift.pathLift (P.twoLeft cell)).base =
      (data.lift.pathLift (P.twoRight cell)).base ∧
    compositeFiberPushforward
      (data.lift.geometry (P.twoTarget cell)) (data.comparator cell) = 1

/-- Every and only qualified total cell belongs to the strict sector. -/
abbrev StrictTwoCell {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U) :=
  { cell : P.TwoCell // StrictCellQualified data cell }

/-- The finite strict sub-presentation with unchanged vertices and edges. -/
noncomputable def strictTwoPresentation
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    FiniteTransportTwoPresentation.{u} := by
  classical
  exact
    { Vertex := P.Vertex
      vertexFintype := P.vertexFintype
      Edge := P.Edge
      edgeFintype := P.edgeFintype
      TwoCell := StrictTwoCell data
      twoCellFintype := Fintype.ofFinite _
      twoSource cell := P.twoSource cell.1
      twoTarget cell := P.twoTarget cell.1
      twoLeft cell := P.twoLeft cell.1
      twoRight cell := P.twoRight cell.1 }

/-- Inclusion of strict faces into total faces. -/
def strictTwoCellEmbedding {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U) :
    StrictTwoCell data ↪ P.TwoCell :=
  Function.Embedding.subtype _

/-- Strict membership is exactly the fixed qualification predicate. -/
theorem strictTwoCell_mem_iff {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U)
    (cell : P.TwoCell) :
    Nonempty { strict : StrictTwoCell data // strict.1 = cell } ↔
      StrictCellQualified data cell := by
  constructor
  · rintro ⟨strict⟩
    simpa [strict.2] using strict.1.2
  · intro qualified
    exact ⟨⟨⟨cell, qualified⟩, rfl⟩⟩

/-- Convert a kernel element into the authored inner subgroup. -/
noncomputable def innerFiberAutOfPushforwardEqOne
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (automorphism : CompositeFiberAut G)
    (identity : compositeFiberPushforward G automorphism = 1) :
    InnerFiberAut G :=
  ⟨automorphism,
    (compositeFiberPushforward_eq_one_iff automorphism).1 identity⟩

/-- The inclusion recovers the original kernel element. -/
@[simp] theorem innerFiberInclusion_ofPushforwardEqOne
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (automorphism : CompositeFiberAut G)
    (identity : compositeFiberPushforward G automorphism = 1) :
    innerFiberInclusion G
      (innerFiberAutOfPushforwardEqOne automorphism identity) = automorphism :=
  rfl

/-- Strict authored comparator in `H_G`. -/
noncomputable def strictAuthoredComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (cell : StrictTwoCell data) :
    InnerFiberAut (data.lift.geometry (P.twoTarget cell.1)) :=
  innerFiberAutOfPushforwardEqOne (data.comparator cell.1) cell.2.2

/-- A strict edge reselection assigns one `H_G` element to every total edge. -/
abbrev StrictEdgeReselection {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U) :=
  (i j : P.Vertex) → (edge : P.Edge i j) → InnerFiberAut (data.geometry j)

/-- Include a strict edge coordinate into the total `C_G` coordinate. -/
noncomputable def strictToUpperReselection
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : StrictEdgeReselection data) : UpperEdgeReselection data :=
  fun i j edge => innerFiberInclusion (data.geometry j) (reselection i j edge)

/-- A strict edge gauge leaves the full core-package edge lift unchanged. -/
theorem strictReselectedEdgeLift_base
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : StrictEdgeReselection data)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift data (strictToUpperReselection data reselection)
      edge).base = (data.edgeLift edge).base := by
  change (data.edgeLift edge).base.comp
      (reselection i j edge).1.1.hom.base = (data.edgeLift edge).base
  rw [(reselection i j edge).2]
  exact (@Category.comp_id
    (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
    _ _ (data.edgeLift edge).base)

/-- A strict edge gauge leaves every evaluated core-package path unchanged. -/
theorem strictReselectedPathLift_base
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : StrictEdgeReselection data)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift data
      (strictToUpperReselection data reselection) path).base =
      (data.pathLift path).base := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      change (upperReselectedEdgeLift data
          (strictToUpperReselection data reselection) edge).base.comp
          (upperReselectedPathLift data
            (strictToUpperReselection data reselection) tail).base =
        (data.edgeLift edge).base.comp (data.pathLift tail).base
      rw [strictReselectedEdgeLift_base, inductionHypothesis]

/-- Strict parallelism survives every strict edge coordinate. -/
theorem strictReselectedTwoCellBase
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift)
    (cell : StrictTwoCell data) :
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection)
      (P.twoLeft cell.1)).base =
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection)
      (P.twoRight cell.1)).base := by
  rw [strictReselectedPathLift_base, strictReselectedPathLift_base]
  exact cell.2.1

/-- Canonical `H_G` comparison of two geometry-strong lifts with equal core lifts. -/
noncomputable def canonicalInnerFiberComparator
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (left right : GeometryTotalHom G H) (baseEq : left.base = right.base)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right] :
    InnerFiberAut H := by
  have rightBase : right.base =
      left.base ≫ (Iso.refl H.core).hom := by
    simpa using baseEq.symm
  let comparison : H ≅ H :=
    CategoryTheory.Functor.IsStronglyCocartesian.codomainIsoOfBaseIso
      (p := geometryProjection U) (f := left.base) (f' := right.base)
      (g := Iso.refl H.core) rightBase left right
  have homLift : (geometryProjection U).IsHomLift
      (𝟙 H.core) comparison.hom := by
    change (geometryProjection U).IsHomLift (Iso.refl H.core).hom
      (CategoryTheory.Functor.IsStronglyCocartesian.map
        (geometryProjection U) left.base left rightBase right)
    infer_instance
  have coreIdentity : comparison.hom.base = 𝟙 H.core :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift
      (geometryProjection U) _ comparison.hom).symm
  have pointedIdentity : comparison.hom.base.base =
      𝟙 (packagePoint H.core) := by
    exact congrArg PackageTotalHom.base coreIdentity
  exact ⟨⟨comparison, pointedIdentity⟩, coreIdentity⟩

/-- The inner canonical comparator satisfies its geometry path factorization. -/
@[simp] theorem canonicalInnerFiberComparator_fac
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (left right : GeometryTotalHom G H) (baseEq : left.base = right.base)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right] :
    left.comp (CompositeFiberAut.hom
        (innerFiberInclusion H
          (canonicalInnerFiberComparator left right baseEq))) = right := by
  have rightBase : right.base = left.base ≫ (Iso.refl H.core).hom := by
    simpa using baseEq.symm
  unfold canonicalInnerFiberComparator innerFiberInclusion
  dsimp only
  simpa only using CategoryTheory.Functor.IsStronglyCocartesian.fac
    (p := geometryProjection U) (f := left.base) (φ := left)
    (g := (Iso.refl H.core).hom) (f' := right.base)
    (hf' := rightBase) (φ' := right)

/-- Generated strict comparator after one global strict edge coordinate. -/
noncomputable def strictCanonicalTwoCellComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift)
    (cell : StrictTwoCell data) :
    InnerFiberAut (data.lift.geometry (P.twoTarget cell.1)) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoLeft cell.1)).base
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoLeft cell.1)) :=
    (upperReselectLiftData data.lift
      (strictToUpperReselection data.lift reselection)).pathLift_geometryStrong
      (P.twoLeft cell.1)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoRight cell.1)).base
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoRight cell.1)) :=
    (upperReselectLiftData data.lift
      (strictToUpperReselection data.lift reselection)).pathLift_geometryStrong
      (P.twoRight cell.1)
  exact canonicalInnerFiberComparator
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection) (P.twoLeft cell.1))
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection) (P.twoRight cell.1))
    (strictReselectedTwoCellBase data reselection cell)

/-- Factorization equation of the generated strict comparator. -/
theorem strictCanonicalTwoCellComparator_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift)
    (cell : StrictTwoCell data) :
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection)
      (P.twoLeft cell.1)).comp
      (CompositeFiberAut.hom
        (innerFiberInclusion (data.lift.geometry (P.twoTarget cell.1))
          (strictCanonicalTwoCellComparator data reselection cell))) =
    upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection)
      (P.twoRight cell.1) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoLeft cell.1)).base
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoLeft cell.1)) :=
    (upperReselectLiftData data.lift
      (strictToUpperReselection data.lift reselection)).pathLift_geometryStrong
      (P.twoLeft cell.1)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoRight cell.1)).base
      (upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoRight cell.1)) :=
    (upperReselectLiftData data.lift
      (strictToUpperReselection data.lift reselection)).pathLift_geometryStrong
      (P.twoRight cell.1)
  exact canonicalInnerFiberComparator_fac
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection) (P.twoLeft cell.1))
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection) (P.twoRight cell.1))
    (strictReselectedTwoCellBase data reselection cell)

/-- The inner canonical comparison is the restriction of the total comparison. -/
theorem strictCanonicalTwoCellComparator_inclusion
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift)
    (cell : StrictTwoCell data) :
    innerFiberInclusion (data.lift.geometry (P.twoTarget cell.1))
        (strictCanonicalTwoCellComparator data reselection cell) =
      upperCanonicalTwoCellComparator data
        (strictToUpperReselection data.lift reselection) cell.1 := by
  let left := upperReselectedPathLift data.lift
    (strictToUpperReselection data.lift reselection) (P.twoLeft cell.1)
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left :=
    (upperReselectLiftData data.lift
      (strictToUpperReselection data.lift reselection)).pathLift_compositeStrong
      (P.twoLeft cell.1)
  apply CompositeFiberAut.ext_of_strong_fac left
  exact (strictCanonicalTwoCellComparator_fac data reselection cell).trans
    (upperCanonicalTwoCellComparator_fac data
      (strictToUpperReselection data.lift reselection) cell.1).symm

/-- The separately defined strict raw defect in `H_G`. -/
noncomputable def strictRawTwoCellDefect
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift)
    (cell : StrictTwoCell data) :
    InnerFiberAut (data.lift.geometry (P.twoTarget cell.1)) :=
  strictAuthoredComparator data cell *
    (strictCanonicalTwoCellComparator data reselection cell)⁻¹

/-- Inclusion of the strict raw defect is restriction of the total raw defect. -/
theorem strictRawTwoCellDefect_inclusion
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift)
    (cell : StrictTwoCell data) :
    innerFiberInclusion (data.lift.geometry (P.twoTarget cell.1))
        (strictRawTwoCellDefect data reselection cell) =
      upperRawTwoCellDefect data
        (strictToUpperReselection data.lift reselection) cell.1 := by
  rw [strictRawTwoCellDefect, upperRawTwoCellDefect, map_mul, map_inv,
    strictCanonicalTwoCellComparator_inclusion]
  rfl

/-- `H_G`-valued strict cochains on the maximal strict cell subtype. -/
abbrev StrictDefectCochain {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U) :=
  (cell : StrictTwoCell data) →
    InnerFiberAut (data.lift.geometry (P.twoTarget cell.1))

/-- Strict raw cochain after one global edge coordinate. -/
noncomputable def strictRawDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift) :
    StrictDefectCochain data :=
  fun cell => strictRawTwoCellDefect data reselection cell

/-- Independent identity cochain in the strict sector. -/
noncomputable def strictIdentityDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : StrictDefectCochain data :=
  fun _ => 1

/-- Strict orbit vanishing under edge-level `H_G` gauges. -/
def StrictTransportObstructionVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∃ reselection : StrictEdgeReselection data.lift,
    strictRawDefectCochain data reselection = strictIdentityDefectCochain data

/-- One global strict edge coordinate satisfies all authored path equations. -/
def StrictCoherentAt {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift) : Prop :=
  ∀ cell : StrictTwoCell data,
    (upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection)
      (P.twoLeft cell.1)).comp
      (CompositeFiberAut.hom
        (innerFiberInclusion (data.lift.geometry (P.twoTarget cell.1))
          (strictAuthoredComparator data cell))) =
    upperReselectedPathLift data.lift
      (strictToUpperReselection data.lift reselection)
      (P.twoRight cell.1)

/-- Existence of one global strict coordinate satisfying all strict faces. -/
def StrictCoherentizable {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∃ reselection : StrictEdgeReselection data.lift,
    StrictCoherentAt data reselection

/-- A strict raw defect is identity exactly when authored and canonical cells agree. -/
theorem strictRawTwoCellDefect_eq_one_iff
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift)
    (cell : StrictTwoCell data) :
    strictRawTwoCellDefect data reselection cell = 1 ↔
      strictAuthoredComparator data cell =
        strictCanonicalTwoCellComparator data reselection cell := by
  unfold strictRawTwoCellDefect
  constructor
  · intro equality
    calc
      strictAuthoredComparator data cell =
          (strictAuthoredComparator data cell *
            (strictCanonicalTwoCellComparator data reselection cell)⁻¹) *
              strictCanonicalTwoCellComparator data reselection cell := by
        simp [mul_assoc]
      _ = 1 * strictCanonicalTwoCellComparator data reselection cell :=
        congrArg (fun element =>
          element * strictCanonicalTwoCellComparator data reselection cell)
          equality
      _ = strictCanonicalTwoCellComparator data reselection cell := one_mul _
  · intro equality
    rw [equality]
    exact mul_inv_cancel _

/-- Global strict path coherence is equivalent to identity of the strict raw cochain. -/
theorem strictCoherentAt_iff_rawCochain_identity
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : StrictEdgeReselection data.lift) :
    StrictCoherentAt data reselection ↔
      strictRawDefectCochain data reselection =
        strictIdentityDefectCochain data := by
  constructor
  · intro coherent
    funext cell
    have authoredEqCanonical : strictAuthoredComparator data cell =
        strictCanonicalTwoCellComparator data reselection cell := by
      let lift := upperReselectedPathLift data.lift
        (strictToUpperReselection data.lift reselection)
        (P.twoLeft cell.1)
      letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
          lift.base.base lift :=
        (upperReselectLiftData data.lift
          (strictToUpperReselection data.lift reselection)).pathLift_compositeStrong
          (P.twoLeft cell.1)
      apply Subtype.ext
      apply CompositeFiberAut.ext_of_strong_fac lift
      exact (coherent cell).trans
        (strictCanonicalTwoCellComparator_fac data reselection cell).symm
    exact (strictRawTwoCellDefect_eq_one_iff data reselection cell).2
      authoredEqCanonical
  · intro rawIdentity cell
    have rawCell : strictRawTwoCellDefect data reselection cell = 1 :=
      congrFun rawIdentity cell
    have authoredEqCanonical :=
      (strictRawTwoCellDefect_eq_one_iff data reselection cell).1 rawCell
    rw [authoredEqCanonical]
    exact strictCanonicalTwoCellComparator_fac data reselection cell

/-- The strict obstruction theorem; the equivalence is proved, not definitional. -/
theorem strictTransportObstructionVanishes_iff_coherentizable
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    StrictTransportObstructionVanishes data ↔ StrictCoherentizable data := by
  constructor
  · rintro ⟨reselection, rawIdentity⟩
    exact ⟨reselection,
      (strictCoherentAt_iff_rawCochain_identity data reselection).2 rawIdentity⟩
  · rintro ⟨reselection, coherent⟩
    exact ⟨reselection,
      (strictCoherentAt_iff_rawCochain_identity data reselection).1 coherent⟩

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
