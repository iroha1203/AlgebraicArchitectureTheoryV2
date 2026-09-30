import ResearchLean.AG.RelativeRepairComposition.CoverEquation
import ResearchLean.AG.RelativeRepairComposition.TowerRestriction

/-!
# Actual native repairs and original-index affine equations

Coordinate changes retain the entire actual edge correction and every original
vertex label. The affine right-hand side is generated from the original tower's
actual defect and fixed-face coherence.
## Implementation notes

G-130 B needs both the original K and each restricted native presentation.
The accepted full relative coordinate isomorphisms identify actual supported
corrections and gauges with the original-index families. The actual defect and
fixed-face coherence generate the affine right-hand side. Keeping the original
K bridge avoids substituting an all-cell subtype presentation for the required
source; quotienting gauges would discard the specified original vertex labels.
-/

namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace ActualEquation
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))

/-- The global original-index right-hand side is the same actual reference defect. -/
noncomputable def defectFamily : RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P :=
  (RelativeCover.original2 T.toTower.localCoefficients P).symm
    ⟨T.toTower.defect, ActualRelative.defect_mem_relative T P hfixed⟩

/-- Native restriction of the generated face family is the actual restricted defect. -/
theorem native_defect_value (U : ClosedRegion K) :
    (RelativeCover.native2 T.toTower.localCoefficients U P
      (CoverEquation.defect T.toTower.localCoefficients P (defectFamily T P hfixed) U)).1 =
      (ClosedRegion.restrictTower U T).toTower.defect := by
  rw [ClosedRegion.restrict_defect]
  rfl

/-- With all corrections allowed, the original fixed-edge set is precisely P. -/
theorem fixed_edges_all : fixedEdgesForRange P.edges ∅ ∅ = P.edges := by
  simp [fixedEdgesForRange]

variable (U : ClosedRegion K)

/-- Native actual labels are exactly the full relative labels on the restricted presentation. -/
theorem native_supportedC0_eq :
    supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges =
    RelativeComplex.C0Group (ClosedRegion.restrictCoefficients U T.toTower.localCoefficients)
      (ClosedRegion.nativeIntersection U P) ∅ ∅ := by
  simpa [fixedEdgesForRange] using
    ActualRelative.supportedC0_eq (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P) ∅ ∅

/-- Native actual corrections are exactly the full relative edge subgroup. -/
theorem native_supportedC1_eq :
    supportedC1 (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges =
    RelativeComplex.C1Group (ClosedRegion.restrictCoefficients U T.toTower.localCoefficients)
      (ClosedRegion.nativeIntersection U P) ∅ ∅ := by
  simpa [fixedEdgesForRange] using
    ActualRelative.supportedC1_eq (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P) ∅ ∅

/-- Reindex every permitted native vertex label to its original vertex name. -/
noncomputable def nativeGaugeEquiv :
    supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges ≃+
    RelativeCover.C0 T.toTower.localCoefficients U P :=
  (AddEquiv.addSubgroupCongr (native_supportedC0_eq T P U)).trans
    (RelativeCover.nativeSupported0 T.toTower.localCoefficients P U).symm

/-- Original-index edge coordinates are the complete supported native edge cochains. -/
noncomputable def nativeEdgeEquiv : RelativeCover.C1 T.toTower.localCoefficients U P ≃+
    supportedC1 (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges :=
  (RelativeCover.nativeSupported1 T.toTower.localCoefficients P U).trans
    (AddEquiv.addSubgroupCongr (native_supportedC1_eq T P U).symm)

/-- Every native vertex value survives the label coordinate change. -/
theorem native_gauge_value
    (b : supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)
    (v : U.vertices) : (nativeGaugeEquiv T P U b).1 v = b.1 v := rfl

/-- The inverse label change restores each native vertex value. -/
theorem native_gauge_inverse_value (b : RelativeCover.C0 T.toTower.localCoefficients U P)
    (v : U.vertices) : ((nativeGaugeEquiv T P U).symm b).1 v = b.1 v := rfl

/-- The edge coordinate change retains every value under the original edge-name bijection. -/
theorem native_edge_value (h : RelativeCover.C1 T.toTower.localCoefficients U P)
    (e : EdgeName (K := ClosedRegion.presentation U)) :
    (nativeEdgeEquiv T P U h).1 e = h.1 (ClosedRegion.edgeNameEquiv U e) := rfl

/-- The inverse edge change reads precisely the same native named edge. -/
theorem native_edge_inverse_value
    (h : supportedC1 (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges)
    (e : U.edges) : ((nativeEdgeEquiv T P U).symm h).1 e =
      h.1 ((ClosedRegion.edgeNameEquiv U).symm e) := rfl

/-- Gauge coboundaries are preserved by both complete coordinate changes. -/
theorem native_d0 (b : supportedC0 (ClosedRegion.restrictTower U T)
    (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges) :
    nativeEdgeEquiv T P U
      (RelativeCover.d0 T.toTower.localCoefficients U P (nativeGaugeEquiv T P U b)) =
      ⟨AbelianLiftingObstruction.d0 (ClosedRegion.restrictTower U T).toTower.localCoefficients b.1,
        supportedC0_d0_mem _ _ _ b⟩ := by
  apply Subtype.ext
  apply (ClosedRegion.nativeC1Equiv U T.toTower.localCoefficients).injective
  change (ClosedRegion.nativeC1Equiv U T.toTower.localCoefficients)
      ((ClosedRegion.nativeC1Equiv U T.toTower.localCoefficients).symm
        ((RelativeCover.d0 T.toTower.localCoefficients U P
          (nativeGaugeEquiv T P U b)).1)) =
    (ClosedRegion.nativeC1Equiv U T.toTower.localCoefficients)
      (AbelianLiftingObstruction.d0 (ClosedRegion.restrictCoefficients U T.toTower.localCoefficients) b.1)
  rw [AddEquiv.apply_symm_apply, ClosedRegion.native_d0_eq]
  rfl

/-- Reindexing native correction equations uses the actual restricted reference defect. -/
noncomputable def nativeEquationEquiv :
    SupportedCorrection (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges ≃
    CoverEquation.Solution T.toTower.localCoefficients P (defectFamily T P hfixed) U where
  toFun h := ⟨(nativeEdgeEquiv T P U).symm h.1, by
    apply (RelativeCover.native2 T.toTower.localCoefficients U P).injective
    apply Subtype.ext
    have hd := congrArg Subtype.val
      (RelativeCover.native_supported_d1 T.toTower.localCoefficients P U
        ((nativeEdgeEquiv T P U).symm h.1))
    change _ = -_
    rw [hd]
    change AbelianLiftingObstruction.d1
      (ClosedRegion.restrictTower U T).toTower.localCoefficients h.1.1 = _
    rw [h.2, ← native_defect_value T P hfixed U]
    rfl⟩
  invFun h := ⟨nativeEdgeEquiv T P U h.1, by
    have hd := congrArg Subtype.val
      (RelativeCover.native_supported_d1 T.toTower.localCoefficients P U h.1)
    change (RelativeCover.native2 T.toTower.localCoefficients U P
        (RelativeCover.d1 T.toTower.localCoefficients U P h.1)).1 =
      AbelianLiftingObstruction.d1 (ClosedRegion.restrictTower U T).toTower.localCoefficients
        (nativeEdgeEquiv T P U h.1).1 at hd
    rw [← hd, h.2, map_neg]
    change -(RelativeCover.native2 T.toTower.localCoefficients U P
      (CoverEquation.defect T.toTower.localCoefficients P (defectFamily T P hfixed) U)).1 = _
    rw [native_defect_value T P hfixed U]⟩
  left_inv h := Subtype.ext ((nativeEdgeEquiv T P U).apply_symm_apply h.1)
  right_inv h := Subtype.ext ((nativeEdgeEquiv T P U).symm_apply_apply h.1)

/-- Every correction edge value survives the affine object map. -/
theorem native_equation_value
    (h : SupportedCorrection (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges)
    (e : U.edges) : (nativeEquationEquiv T P hfixed U h).1.1 e =
      h.1.1 ((ClosedRegion.edgeNameEquiv U).symm e) := rfl

/-- The inverse affine object map restores every native correction edge value. -/
theorem native_equation_inverse_value
    (h : CoverEquation.Solution T.toTower.localCoefficients P (defectFamily T P hfixed) U)
    (e : EdgeName (K := ClosedRegion.presentation U)) :
    ((nativeEquationEquiv T P hfixed U).symm h).1.1 e =
      h.1.1 (ClosedRegion.edgeNameEquiv U e) := rfl

/-- The object change is equivariant for every full original vertex label. -/
theorem native_equation_equivariant
    (b : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges))
    (h : SupportedCorrection (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges) :
    nativeEquationEquiv T P hfixed U (b • h) =
      (nativeGaugeEquiv T P U).toMultiplicative b • nativeEquationEquiv T P hfixed U h := by
  apply Subtype.ext
  apply (nativeEdgeEquiv T P U).injective
  change (nativeEdgeEquiv T P U) ((nativeEdgeEquiv T P U).symm
      (correctionGauge _ _ _ b.toAdd h).1) =
    nativeEdgeEquiv T P U
      (((nativeEdgeEquiv T P U).symm h.1) +
        RelativeCover.d0 T.toTower.localCoefficients U P (nativeGaugeEquiv T P U b.toAdd))
  rw [AddEquiv.apply_symm_apply, map_add, AddEquiv.apply_symm_apply, native_d0]
  rfl

/-- Complete native supported corrections and affine equations have equivalent action groupoids. -/
noncomputable def nativeCorrectionEquationEquivalence :
    CorrectionGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges ≌
    CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U :=
  changedLabelEquivalence (nativeGaugeEquiv T P U).toMultiplicative
    (nativeEquationEquiv T P hfixed U) (native_equation_equivariant T P hfixed U)

/-- Actual repair coordinates and affine edge coordinates are inverse on all objects. -/
noncomputable def nativeRepairEquiv :
    SupportedRepair (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges ≃
    CoverEquation.Solution T.toTower.localCoefficients P (defectFamily T P hfixed) U :=
  (repairEquiv (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges).trans
    (nativeEquationEquiv T P hfixed U)

/-- The actual repair coordinates intertwine every native vertex reidentification. -/
theorem native_repair_equivariant
    (b : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges))
    (R : SupportedRepair (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges) :
    nativeRepairEquiv T P hfixed U (b • R) =
      (nativeGaugeEquiv T P U).toMultiplicative b • nativeRepairEquiv T P hfixed U R := by
  change nativeEquationEquiv T P hfixed U
      (repairCoord _ _ (repairGauge _ _ _ b.toAdd R)) = _
  rw [coord_gauge]
  exact native_equation_equivariant T P hfixed U b (repairCoord _ _ R)

/-- Independent actual repairs have the same affine equations and every native gauge arrow. -/
noncomputable def nativeRepairEquationEquivalence :
    RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges ≌
    CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U :=
  changedLabelEquivalence (nativeGaugeEquiv T P U).toMultiplicative
    (nativeRepairEquiv T P hfixed U) (native_repair_equivariant T P hfixed U)

/-- The actual repair functor retains every original correction edge value. -/
theorem native_repair_obj_value
    (R : RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)
    (e : U.edges) :
    ((nativeRepairEquationEquivalence T P hfixed U).functor.obj R).back.1.1 e =
      (ClosedRegion.restrictTower U T).solutionCorrection R.back.1
        ((ClosedRegion.edgeNameEquiv U).symm e) := rfl

/-- Every gauge morphism keeps its value at every original vertex. -/
theorem native_repair_map_value
    {R Q : RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges}
    (b : R ⟶ Q) (v : U.vertices) :
    ((nativeRepairEquationEquivalence T P hfixed U).functor.map b).1.toAdd.1 v =
      b.1.toAdd.1 v := rfl

/-- The inverse functor restores every native vertex value of an affine arrow. -/
theorem native_repair_inverse_map_value
    {h k : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U}
    (b : h ⟶ k) (v : U.vertices) :
    ((nativeRepairEquationEquivalence T P hfixed U).inverse.map b).1.toAdd.1 v =
      b.1.toAdd.1 v := rfl

/-- Affine restoration constructs the original actual choice at each native edge. -/
theorem native_repair_inverse_choice
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U)
    {i j : (ClosedRegion.presentation U).Vertex} (e : (ClosedRegion.presentation U).Edge i j) :
    ((nativeRepairEquationEquivalence T P hfixed U).inverse.obj h).back.1.choice e =
      (ClosedRegion.restrictTower U T).correctionChoice
        ((nativeEdgeEquiv T P U h.back.1).1) e := rfl

/-- The equivalence unit transports each actual object with the identity label. -/
theorem native_repair_unit_label
    (R : RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges) :
    ((nativeRepairEquationEquivalence T P hfixed U).unitIso.hom.app R).1 =
      (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
        (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) :=
  action_eqToHom_label (changed_label_left_obj
    (nativeGaugeEquiv T P U).toMultiplicative (nativeRepairEquiv T P hfixed U)
    (native_repair_equivariant T P hfixed U) R).symm

/-- The equivalence counit restores each affine object with the identity label. -/
theorem native_repair_counit_label
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U) :
    ((nativeRepairEquationEquivalence T P hfixed U).counitIso.hom.app h).1 =
      (1 : Multiplicative (RelativeCover.C0 T.toTower.localCoefficients U P)) :=
  action_eqToHom_label (changed_label_right_obj
    (nativeGaugeEquiv T P U).toMultiplicative (nativeRepairEquiv T P hfixed U)
    (native_repair_equivariant T P hfixed U) h)

/-- The inverse counit transports each affine object with the identity gauge label. -/
theorem native_repair_counit_inv_label
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U) :
    ((nativeRepairEquationEquivalence T P hfixed U).counitIso.inv.app h).1 =
      (1 : Multiplicative (RelativeCover.C0 T.toTower.localCoefficients U P)) :=
  action_eqToHom_label (changed_label_right_obj
    (nativeGaugeEquiv T P U).toMultiplicative (nativeRepairEquiv T P hfixed U)
    (native_repair_equivariant T P hfixed U) h).symm

/-- Full original actual labels are precisely the accepted relative degree-zero group. -/
theorem original_supportedC0_eq : supportedC0 T P.vertices P.edges =
    RelativeComplex.C0Group T.toTower.localCoefficients P ∅ ∅ := by
  simpa [fixedEdgesForRange] using ActualRelative.supportedC0_eq T P ∅ ∅

/-- Full original actual correction coordinates are precisely the relative degree-one group. -/
theorem original_supportedC1_eq : supportedC1 T P.edges =
    RelativeComplex.C1Group T.toTower.localCoefficients P ∅ ∅ := by
  simpa [fixedEdgesForRange] using ActualRelative.supportedC1_eq T P ∅ ∅

/-- Original vertex labels are reindexed to the complete original-index family. -/
noncomputable def originalGaugeEquiv : supportedC0 T P.vertices P.edges ≃+
    RelativeCover.C0 T.toTower.localCoefficients ClosedRegion.all P :=
  (AddEquiv.addSubgroupCongr (original_supportedC0_eq T P)).trans
    (RelativeCover.originalSupported0 T.toTower.localCoefficients P).symm

/-- The original-index edge family is the complete actual supported correction subgroup. -/
noncomputable def originalEdgeEquiv : RelativeCover.C1 T.toTower.localCoefficients ClosedRegion.all P ≃+
    supportedC1 T P.edges :=
  (RelativeCover.originalSupported1 T.toTower.localCoefficients P).trans
    (AddEquiv.addSubgroupCongr (original_supportedC1_eq T P).symm)

/-- Every original vertex retains its entire gauge value. -/
theorem original_gauge_value (b : supportedC0 T P.vertices P.edges) (v : K.Vertex) :
    (originalGaugeEquiv T P b).1 ⟨v, Set.mem_univ v⟩ = b.1 v := rfl

/-- The inverse coordinate change restores every original vertex label. -/
theorem original_gauge_inverse_value
    (b : RelativeCover.C0 T.toTower.localCoefficients ClosedRegion.all P) (v : K.Vertex) :
    ((originalGaugeEquiv T P).symm b).1 v = b.1 ⟨v, Set.mem_univ v⟩ := rfl

/-- Every original edge retains its complete correction value. -/
theorem original_edge_value
    (h : RelativeCover.C1 T.toTower.localCoefficients ClosedRegion.all P) (e : EdgeName (K := K)) :
    (originalEdgeEquiv T P h).1 e = h.1 ⟨e, Set.mem_univ e⟩ := rfl

/-- The full original coordinate change preserves each original gauge coboundary. -/
theorem original_d0 (b : supportedC0 T P.vertices P.edges) :
    originalEdgeEquiv T P
      (RelativeCover.d0 T.toTower.localCoefficients ClosedRegion.all P (originalGaugeEquiv T P b)) =
      ⟨AbelianLiftingObstruction.d0 T.toTower.localCoefficients b.1,
        supportedC0_d0_mem _ _ _ b⟩ := by
  apply Subtype.ext
  have hd := congrArg Subtype.val
    (RelativeCover.original_supported_d0 T.toTower.localCoefficients P (originalGaugeEquiv T P b))
  change (originalEdgeEquiv T P
      (RelativeCover.d0 T.toTower.localCoefficients ClosedRegion.all P (originalGaugeEquiv T P b))).1 =
    AbelianLiftingObstruction.d0 T.toTower.localCoefficients b.1 at hd
  exact hd

/-- The generated full face family is the identical original actual defect. -/
theorem original_defect_value :
    (RelativeCover.original2 T.toTower.localCoefficients P
      (CoverEquation.defect T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all)).1 =
      T.toTower.defect := by
  rw [CoverEquation.defect_all]
  exact congrArg Subtype.val ((RelativeCover.original2 T.toTower.localCoefficients P).apply_symm_apply _)

/-- Actual original correction equations correspond to the generated global affine equation. -/
noncomputable def originalEquationEquiv : SupportedCorrection T P.edges ≃
    CoverEquation.Solution T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all where
  toFun h := ⟨(originalEdgeEquiv T P).symm h.1, by
    apply (RelativeCover.original2 T.toTower.localCoefficients P).injective
    apply Subtype.ext
    have hd := congrArg Subtype.val
      (RelativeCover.original_supported_d1 T.toTower.localCoefficients P
        ((originalEdgeEquiv T P).symm h.1))
    rw [map_neg]
    change _ = -_
    rw [hd]
    change AbelianLiftingObstruction.d1 T.toTower.localCoefficients h.1.1 = _
    rw [h.2, original_defect_value]⟩
  invFun h := ⟨originalEdgeEquiv T P h.1, by
    have hd := congrArg Subtype.val
      (RelativeCover.original_supported_d1 T.toTower.localCoefficients P h.1)
    change (RelativeCover.original2 T.toTower.localCoefficients P
        (RelativeCover.d1 T.toTower.localCoefficients ClosedRegion.all P h.1)).1 =
      AbelianLiftingObstruction.d1 T.toTower.localCoefficients (originalEdgeEquiv T P h.1).1 at hd
    rw [← hd, h.2, map_neg]
    change -(RelativeCover.original2 T.toTower.localCoefficients P
      (CoverEquation.defect T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all)).1 = _
    rw [original_defect_value]⟩
  left_inv h := Subtype.ext ((originalEdgeEquiv T P).apply_symm_apply h.1)
  right_inv h := Subtype.ext ((originalEdgeEquiv T P).symm_apply_apply h.1)

/-- Original affine coordinate changes intertwine every permitted original vertex label. -/
theorem original_equation_equivariant
    (b : Multiplicative (supportedC0 T P.vertices P.edges)) (h : SupportedCorrection T P.edges) :
    originalEquationEquiv T P hfixed (b • h) =
      (originalGaugeEquiv T P).toMultiplicative b • originalEquationEquiv T P hfixed h := by
  apply Subtype.ext
  apply (originalEdgeEquiv T P).injective
  change (originalEdgeEquiv T P) ((originalEdgeEquiv T P).symm
      (correctionGauge _ _ _ b.toAdd h).1) =
    originalEdgeEquiv T P (((originalEdgeEquiv T P).symm h.1) +
      RelativeCover.d0 T.toTower.localCoefficients ClosedRegion.all P (originalGaugeEquiv T P b.toAdd))
  rw [AddEquiv.apply_symm_apply, map_add, AddEquiv.apply_symm_apply, original_d0]
  rfl

/-- Actual original repairs and full affine original-index solutions correspond on all objects. -/
noncomputable def originalRepairEquiv : SupportedRepair T P.edges ≃
    CoverEquation.Solution T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all :=
  (repairEquiv T P.edges).trans (originalEquationEquiv T P hfixed)

/-- Original actual repair coordinates intertwine every original vertex reidentification. -/
theorem original_repair_equivariant
    (b : Multiplicative (supportedC0 T P.vertices P.edges)) (R : SupportedRepair T P.edges) :
    originalRepairEquiv T P hfixed (b • R) =
      (originalGaugeEquiv T P).toMultiplicative b • originalRepairEquiv T P hfixed R := by
  change originalEquationEquiv T P hfixed
      (repairCoord _ _ (repairGauge _ _ _ b.toAdd R)) = _
  rw [coord_gauge]
  exact original_equation_equivariant T P hfixed b (repairCoord _ _ R)

/-- Independent actual repairs on original K have precisely the full affine action groupoid. -/
noncomputable def originalRepairEquationEquivalence : RepairGroupoid T P.vertices P.edges ≌
    CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all :=
  changedLabelEquivalence (originalGaugeEquiv T P).toMultiplicative
    (originalRepairEquiv T P hfixed) (original_repair_equivariant T P hfixed)

/-- Forward actual coordinates keep every original correction edge value. -/
theorem original_repair_obj_value (R : RepairGroupoid T P.vertices P.edges) (e : EdgeName (K := K)) :
    ((originalRepairEquationEquivalence T P hfixed).functor.obj R).back.1.1 ⟨e, Set.mem_univ e⟩ =
      T.solutionCorrection R.back.1 e := rfl

/-- Inverse global affine restoration reconstructs each actual original edge choice. -/
theorem original_repair_inverse_choice
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all)
    {i j : K.Vertex} (e : K.Edge i j) :
    ((originalRepairEquationEquivalence T P hfixed).inverse.obj h).back.1.choice e =
      T.correctionChoice (originalEdgeEquiv T P h.back.1).1 e := rfl

/-- Forward repair arrows keep all original vertex values, including stabilizers. -/
theorem original_repair_map_value {R Q : RepairGroupoid T P.vertices P.edges}
    (b : R ⟶ Q) (v : K.Vertex) :
    ((originalRepairEquationEquivalence T P hfixed).functor.map b).1.toAdd.1 ⟨v, Set.mem_univ v⟩ =
      b.1.toAdd.1 v := rfl

/-- Inverse repair arrows restore every original vertex label. -/
theorem original_repair_inverse_map_value
    {h k : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all}
    (b : h ⟶ k) (v : K.Vertex) :
    ((originalRepairEquationEquivalence T P hfixed).inverse.map b).1.toAdd.1 v =
      b.1.toAdd.1 ⟨v, Set.mem_univ v⟩ := rfl

/-- The original actual-object unit has identity label. -/
theorem original_repair_unit_label (R : RepairGroupoid T P.vertices P.edges) :
    ((originalRepairEquationEquivalence T P hfixed).unitIso.hom.app R).1 =
      (1 : Multiplicative (supportedC0 T P.vertices P.edges)) :=
  action_eqToHom_label (changed_label_left_obj
    (originalGaugeEquiv T P).toMultiplicative (originalRepairEquiv T P hfixed)
    (original_repair_equivariant T P hfixed) R).symm

/-- The original affine-object counit has identity label. -/
theorem original_repair_counit_label
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all) :
    ((originalRepairEquationEquivalence T P hfixed).counitIso.hom.app h).1 =
      (1 : Multiplicative (RelativeCover.C0 T.toTower.localCoefficients ClosedRegion.all P)) :=
  action_eqToHom_label (changed_label_right_obj
    (originalGaugeEquiv T P).toMultiplicative (originalRepairEquiv T P hfixed)
    (original_repair_equivariant T P hfixed) h)

/-- Restoring native affine coordinates gives every prescribed correction edge value. -/
theorem native_repair_inverse_obj_value
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U)
    (e : EdgeName (K := ClosedRegion.presentation U)) :
    (ClosedRegion.restrictTower U T).solutionCorrection
      ((nativeRepairEquationEquivalence T P hfixed U).inverse.obj h).back.1 e =
        h.back.1.1 (ClosedRegion.edgeNameEquiv U e) := by
  change (ClosedRegion.restrictTower U T).solutionCorrection
      ((ClosedRegion.restrictTower U T).solutionOfCorrection
        ((nativeEquationEquiv T P hfixed U).symm h.back).1.1
        ((nativeEquationEquiv T P hfixed U).symm h.back).2) e = _
  rw [(ClosedRegion.restrictTower U T).solutionCorrection_solutionOfCorrection]
  rfl

/-- Native affine restoration after actual coordinates restores the entire actual repair. -/
theorem native_repair_left_obj
    (R : RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges) :
    (nativeRepairEquationEquivalence T P hfixed U).inverse.obj
      ((nativeRepairEquationEquivalence T P hfixed U).functor.obj R) = R :=
  changed_label_left_obj (nativeGaugeEquiv T P U).toMultiplicative
    (nativeRepairEquiv T P hfixed U) (native_repair_equivariant T P hfixed U) R

/-- Native actual coordinates after affine restoration restore the entire affine solution. -/
theorem native_repair_right_obj
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) U) :
    (nativeRepairEquationEquivalence T P hfixed U).functor.obj
      ((nativeRepairEquationEquivalence T P hfixed U).inverse.obj h) = h :=
  changed_label_right_obj (nativeGaugeEquiv T P U).toMultiplicative
    (nativeRepairEquiv T P hfixed U) (native_repair_equivariant T P hfixed U) h

/-- Original supported correction coordinates retain each named original edge value. -/
theorem original_equation_value (h : SupportedCorrection T P.edges) (e : EdgeName (K := K)) :
    (originalEquationEquiv T P hfixed h).1.1 ⟨e, Set.mem_univ e⟩ = h.1.1 e := rfl

/-- The inverse original affine equation map restores every supported edge value. -/
theorem original_equation_inverse_value
    (h : CoverEquation.Solution T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all)
    (e : EdgeName (K := K)) :
    ((originalEquationEquiv T P hfixed).symm h).1.1 e = h.1.1 ⟨e, Set.mem_univ e⟩ := rfl

/-- Global actual restoration gives every specified original affine correction edge. -/
theorem original_repair_inverse_obj_value
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all)
    (e : EdgeName (K := K)) :
    T.solutionCorrection ((originalRepairEquationEquivalence T P hfixed).inverse.obj h).back.1 e =
      h.back.1.1 ⟨e, Set.mem_univ e⟩ := by
  change T.solutionCorrection (T.solutionOfCorrection
    ((originalEquationEquiv T P hfixed).symm h.back).1.1
    ((originalEquationEquiv T P hfixed).symm h.back).2) e = _
  rw [T.solutionCorrection_solutionOfCorrection]
  rfl

/-- Original affine restoration after actual coordinates restores all actual edge choices. -/
theorem original_repair_left_obj (R : RepairGroupoid T P.vertices P.edges) :
    (originalRepairEquationEquivalence T P hfixed).inverse.obj
      ((originalRepairEquationEquivalence T P hfixed).functor.obj R) = R :=
  changed_label_left_obj (originalGaugeEquiv T P).toMultiplicative
    (originalRepairEquiv T P hfixed) (original_repair_equivariant T P hfixed) R

/-- Original actual coordinates after restoration restore the complete global affine solution. -/
theorem original_repair_right_obj
    (h : CoverEquation.Groupoid T.toTower.localCoefficients P (defectFamily T P hfixed) ClosedRegion.all) :
    (originalRepairEquationEquivalence T P hfixed).functor.obj
      ((originalRepairEquationEquivalence T P hfixed).inverse.obj h) = h :=
  changed_label_right_obj (originalGaugeEquiv T P).toMultiplicative
    (originalRepairEquiv T P hfixed) (original_repair_equivariant T P hfixed) h

end ActualEquation
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.ActualEquation
