import ResearchLean.AG.RepairObservationDuality.KPlusActualRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials
import ResearchLean.AG.RepairObservationDuality.FiniteRepairPlanning

/-!
# G-131 E: the full original K+ native equation

## Implementation notes

The entire kernel at each original vertex is used. Both native authored face
rows are evaluated before fixing a/b corrections. The numerical matrix and
signed RHS come from those same words, not from W5's different presentation.
The full kernel bases and fixed-edge cochain coordinates retain every native
correction value required by GOAL E and n1017 §5.3. Coordinates restricted to
the differential's image would lose output values, so that alternative is
not used. Importing W5's three-edge equation would omit the original c-loop;
the matrix is instead generated from this four-edge native differential.
-/
namespace AAT.AG.RepairObservationDuality.KPlusNativeEquation
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open RelativeRepairComposition NativeAffine KPlusInput KPlusActualRepairs PrimitiveQueries
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
variable (v : Values)
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (originalTower v))

/-- The entire original categorical kernel is the full F2 translation module. -/
noncomputable def kernelCoordinate (i : geometry.Vertex) : (M).A i ≃ₗ[ZMod 2] ZMod 2 :=
  NativeAffine.linearCoefficient geometry (reference v) (reference v) comparison (linear_faces v) i
/-- The full original basis includes every native coefficient. -/
noncomputable def bases : FiniteFamily.Bases (k := ZMod 2) (M).A where
  dimension _ := 1
  coordinate i := (kernelCoordinate v i).trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (ZMod 2)).symm
/-- Each original full basis component is its whole kernel scalar. -/
theorem basis_value (i : geometry.Vertex) (a : (M).A i) :
    (bases v).coordinate i a ⟨0,by change 0 < 1; decide⟩ = kernelCoordinate v i a := rfl
/-- Reading the full original coefficient at a typed edge. -/
noncomputable def edgeValue (h : C1 M) (e : EdgeName (K := geometry)) : ZMod 2 :=
  kernelCoordinate v e.2.1 (h e)
/-- The whole correction family is reconstructed before imposing either face equation. -/
noncomputable def cochain (h : Values) : C1 M :=
  fun e => (kernelCoordinate v e.2.1).symm (correctionValue h e.2.2.1)
/-- All four original whole edge coefficients are retained. -/
theorem cochain_value (h : Values) (e : EdgeName (K := geometry)) :
    edgeValue v (cochain v h) e = correctionValue h e.2.2.1 :=
  (kernelCoordinate v e.2.1).apply_symm_apply _
/-- The physically fixed a/b coefficients vanish in the constructed full family. -/
theorem cochain_fixed (h : Values) (e : EdgeName (K := geometry)) (he : e ∈ fixedRegion.edges) :
    cochain v h e = 0 := by
  rcases he with rfl | rfl <;>
    simp only [cochain,name_value,correction_a,correction_b,map_zero]
/-- Every arbitrary native coefficient at an original edge is recovered at its canonical name. -/
theorem edgeValue_name (h : C1 M) (e : EdgeName (K := geometry)) :
    edgeValue v h (name e.2.2.1) = edgeValue v h e := congrArg (edgeValue v h) (name_edge e)
/-- Every full native correction fixing a/b has exactly the two unconstrained whole u/z values. -/
theorem full_cochain (h : C1 M)
    (hf : ∀ e ∈ fixedRegion.edges, h e = 0) :
    cochain v (fun j => edgeValue v h (name (if j then edgeC else edgeE))) = h := by
  funext e
  apply (kernelCoordinate v e.2.1).injective
  change edgeValue v (cochain v _) e = edgeValue v h e
  rw [cochain_value,← edgeValue_name v h e]
  generalize e.2.2.1 = n
  fin_cases n
  · change correctionValue _ edgeE = _
    rw [correction_e]
    rfl
  · have ha := hf (name edgeA) (Or.inl rfl)
    change correctionValue _ edgeA = _
    rw [correction_a]
    change 0 = edgeValue v h (name edgeA)
    change 0 = kernelCoordinate v _ (h (name edgeA))
    rw [ha,map_zero]
  · have hb := hf (name edgeB) (Or.inr rfl)
    change correctionValue _ edgeB = _
    rw [correction_b]
    change 0 = edgeValue v h (name edgeB)
    change 0 = kernelCoordinate v _ (h (name edgeB))
    rw [hb,map_zero]
  · change correctionValue _ edgeC = _
    rw [correction_c]
    rfl
/-- The first full native row is the actual original e-a word correction. -/
theorem native_first (h : C1 M) :
    kernelCoordinate v vertexT (d1 M h false) =
      edgeValue v h (name edgeE) - edgeValue v h (name edgeA) := by
  refine (NativeAffine.d1_value geometry (reference v) (reference v) comparison (linear_faces v) h false).trans ?_
  simp only [geometry,vectorPath,GroupExtension.pathValue]
  change edgeValue v h (name edgeE) + 0 - (edgeValue v h (name edgeA) + 0) = _
  abel
/-- The second full native row is the original c-after-e minus b word correction. -/
theorem native_second (h : C1 M) :
    kernelCoordinate v vertexT (d1 M h true) =
      edgeValue v h (name edgeE) + edgeValue v h (name edgeC) - edgeValue v h (name edgeB) := by
  refine (NativeAffine.d1_value geometry (reference v) (reference v) comparison (linear_faces v) h true).trans ?_
  simp only [geometry,ite_true,vectorPath,GroupExtension.pathValue]
  change (1 * reference v (name edgeC).2.2).linear (edgeValue v h (name edgeE)) +
    (edgeValue v h (name edgeC) + 0) - (edgeValue v h (name edgeB) + 0) = _
  rw [reference_c]
  change edgeValue v h (name edgeE) + (edgeValue v h (name edgeC) + 0) -
    (edgeValue v h (name edgeB) + 0) = _
  abel
/-- Full inverse translations evaluate the entire original inverse map. -/
theorem translation_inverse_apply (a x : ZMod 2) :
    ((translation (k := ZMod 2) a)⁻¹ : Op) x = -a + x := by
  change (AffineEquiv.constVAdd (ZMod 2) (ZMod 2) a).symm x = _
  rw [AffineEquiv.constVAdd_symm]
  rfl
/-- The actual original native signed defect is the full physical input pair. -/
theorem signed_defect (f : Bool) :
    kernelCoordinate v vertexT (-(originalTower v).toTower.defect f) = v f := by
  rw [map_neg]
  have hv := NativeAffine.defect_value geometry (reference v) (reference v) comparison (linear_faces v) f
  rw [reference_left_path,reference_right_path,comparison_zero,zero_translation,one_mul,one_mul,
    translation_inverse_apply,add_zero] at hv
  exact (congrArg Neg.neg hv).trans (neg_neg (v f))
/-- The original full two-row differential with a/b physically fixed and c permitted. -/
def differential : Values →ₗ[ZMod 2] Values where
  toFun h f := if f then h false + h true else h false
  map_add' h g := by ext f; cases f <;> simp [add_add_add_comm]
  map_smul' t h := by ext f; cases f <;> simp [mul_add]
/-- The actual signed defect has b0=0 and B=I. -/
def rhsLinear : Values →ₗ[ZMod 2] Values := LinearMap.id
/-- Basic API for both whole differential rows. -/
theorem differential_apply (h : Values) (f : Bool) :
    differential h f = if f then h false + h true else h false := rfl
/-- Basic API for both physical RHS values. -/
theorem rhsLinear_apply (w : Values) : rhsLinear w = w := rfl
/-- The generated two-row map is the same native d1 on every full allowed correction. -/
theorem original_differential (h : Values) (f : Bool) :
    kernelCoordinate v vertexT (d1 M (cochain v h) f) = differential h f := by
  cases f
  · rw [native_first,cochain_value,cochain_value]
    simp only [name_value,correction_e,correction_a,sub_zero,differential_apply,Bool.false_eq_true,if_false]
  · rw [native_second,cochain_value,cochain_value,cochain_value]
    simp only [name_value,correction_e,correction_c,correction_b,sub_zero,differential_apply,if_true]
/-- The same full matrix equation is precisely the two independent original real faces. -/
theorem equation_iff (h : Values) :
    differential h = affineRhs rhsLinear 0 v ↔ Equations v h := by
  rw [equations_iff]
  constructor
  · intro he
    exact ⟨by simpa [differential_apply,affineRhs_apply,rhsLinear_apply] using congrFun he false,
      by simpa [differential_apply,affineRhs_apply,rhsLinear_apply] using congrFun he true⟩
  · rintro ⟨h0,h1⟩
    ext f
    cases f <;> simpa [differential_apply,affineRhs_apply,rhsLinear_apply] using (by assumption)
/-- Every original input has a full numeric solution when its c candidate is permitted. -/
theorem solvable : Solvable differential (affineRhs rhsLinear 0) v := by
  refine ⟨fun j => if j then v true - v false else v false,?_⟩
  apply (equation_iff v _).mpr
  simp [equations_iff]
/-- The full solver matrix is generated solely from the known native differential. -/
noncomputable def matrix : Matrix Bool Bool (ZMod 2) := LinearMap.toMatrix' differential
/-- Generated matrix evaluation retains the whole original two-row linear map. -/
theorem matrix_differential : FiniteMatrixSolver.differential matrix = differential := Matrix.toLin'_toMatrix' _
/-- Every full numerical answer restores all original actual operations with both original faces. -/
noncomputable def restore (h : Values) (he : differential h = affineRhs rhsLinear 0 v) :
    RealRepairs v := fromCoordinates v h ((equation_iff v h).mp he)
/-- Restoration keeps both whole acquired output coordinates. -/
theorem restore_values (h : Values) (he : differential h = affineRhs rhsLinear 0 v) :
    coordinates (restore v h he) = h := coordinates_from v h _
/-- The same full native categorical repair is recovered through G-130's equivalence. -/
noncomputable def restore_native (h : Values) (he : differential h = affineRhs rhsLinear 0 v) :
    SupportedRepair (originalTower v) fixedRegion.edges :=
  (nativeCoordinatesEquiv v).symm ⟨h,(equation_iff v h).mp he⟩
/-- No whole output coordinate is lost in native restoration. -/
theorem restore_native_values (h : Values) (he : differential h = affineRhs rhsLinear 0 v) :
    ((nativeCoordinatesEquiv v) (restore_native v h he)).1 = h := by
  exact congrArg Subtype.val ((nativeCoordinatesEquiv v).apply_symm_apply _)

/-- The restored native repair and independently restored actual repair have every whole map in common. -/
theorem restore_native_real (h : Values) (he : differential h = affineRhs rhsLinear 0 v) :
    NativeAffine.repairEquivalence geometry (reference v) (reference v) comparison (linear_faces v)
      fixedRegion.edges (restore_native v h he) = restore v h he := by
  apply (actualCoordinatesEquiv v).injective
  change (nativeCoordinatesEquiv v) (restore_native v h he) = actualCoordinatesEquiv v (restore v h he)
  rw [show (nativeCoordinatesEquiv v) (restore_native v h he) =
    ⟨h,(equation_iff v h).mp he⟩ from (nativeCoordinatesEquiv v).apply_symm_apply _]
  apply Subtype.ext
  exact (restore_values v h he).symm
/-- All original native correction coefficients are the same full numerical e/a/b/c values. -/
theorem restore_native_correction (h : Values) (he : differential h = affineRhs rhsLinear 0 v)
    (e : EdgeName (K := geometry)) :
    kernelCoordinate v e.2.1 ((originalTower v).solutionCorrection (restore_native v h he).1 e) =
      correctionValue h e.2.2.1 := by
  have hv := NativeAffine.real_correction_native geometry (reference v) (reference v) comparison
    (linear_faces v) fixedRegion.edges (restore_native v h he) e
  change NativeAffine.realCorrection geometry (reference v) comparison fixedRegion.edges
      (NativeAffine.repairEquivalence geometry (reference v) (reference v) comparison (linear_faces v)
        fixedRegion.edges (restore_native v h he)) e =
    kernelCoordinate v e.2.1 ((originalTower v).solutionCorrection (restore_native v h he).1 e) at hv
  rw [← hv,restore_native_real]
  exact fromCoordinates_correction v h _ e

end AAT.AG.RepairObservationDuality.KPlusNativeEquation
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.KPlusNativeEquation
