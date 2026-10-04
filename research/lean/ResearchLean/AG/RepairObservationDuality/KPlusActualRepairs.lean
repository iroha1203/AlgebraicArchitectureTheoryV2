import ResearchLean.AG.RepairObservationDuality.KPlusInput
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection

/-!
# G-131 E: complete numerical values and independent actual K+ repairs

## Implementation notes

Repairs are the existing independent native-affine repair type, defined by
whole original maps, both authored word equalities and fixed a/b operations.
Coordinates are read from those operations after that definition. Conversely
the numeric pair constructs all four real maps before verifying the faces.
The G-130 native correspondence then restores the same full categorical repair.
-/
namespace AAT.AG.RepairObservationDuality.KPlusActualRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open RelativeRepairComposition NativeAffine KPlusInput
set_option autoImplicit false
set_option maxRecDepth 4096

/-- Independent whole actual repairs when the original candidate c is permitted. -/
abbrev RealRepairs (v : Values) := NativeAffine.Repair geometry (reference v) comparison fixedRegion.edges

/-- The full correction family has u on e, z on c and zero on both physical inputs. -/
def correctionValue (h : Values) (e : Fin 4) : ZMod 2 :=
  if e = edgeE then h false else if e = edgeC then h true else 0

/-- Basic API: the entire always correction is the acquired u. -/
theorem correction_e (h : Values) : correctionValue h edgeE = h false := by simp [correctionValue]
/-- Basic API: the entire permitted candidate correction is the acquired z. -/
theorem correction_c (h : Values) : correctionValue h edgeC = h true := by
  simp [correctionValue,edgeE,edgeC]
/-- Basic API: the original fixed a correction is zero. -/
theorem correction_a (h : Values) : correctionValue h edgeA = 0 := by
  simp [correctionValue,edgeE,edgeA,edgeC]
/-- Basic API: the original fixed b correction is zero. -/
theorem correction_b (h : Values) : correctionValue h edgeB = 0 := by
  simp [correctionValue,edgeE,edgeB,edgeC]

/-- Basic API: the zero correction is the identity on the entire actual operation carrier. -/
theorem zero_translation : translation (k := ZMod 2) (0 : ZMod 2) = (1 : Op) := by
  apply AffineEquiv.ext
  intro x
  exact zero_add x

/-- Whole repaired original maps are numeric correction translations followed by their actual references. -/
noncomputable def operation (v h : Values) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => translation (k := ZMod 2) (correctionValue h e.1) * reference v e

/-- Basic API: the full always edge is translation by the acquired u value. -/
theorem operation_e_apply (v h : Values) (x : ZMod 2) :
    operation v h (name edgeE).2.2 x = x + h false := by
  rw [operation,reference_e,mul_one]
  simp [correctionValue,name_value,edgeE,add_comm]
/-- Basic API: the full candidate loop is translation by the acquired z value. -/
theorem operation_c_apply (v h : Values) (x : ZMod 2) :
    operation v h (name edgeC).2.2 x = x + h true := by
  rw [operation,reference_c,mul_one]
  simp [correctionValue,name_value,edgeE,edgeC,add_comm]
/-- Basic API: numeric reconstruction preserves the entire original a operation. -/
theorem operation_a (v h : Values) : operation v h (name edgeA).2.2 = reference v (name edgeA).2.2 := by
  simp [operation,correctionValue,name_value,edgeE,edgeA,edgeC,zero_translation]
/-- Basic API: numeric reconstruction preserves the entire original b operation. -/
theorem operation_b (v h : Values) : operation v h (name edgeB).2.2 = reference v (name edgeB).2.2 := by
  simp [operation,correctionValue,name_value,edgeE,edgeB,edgeC,zero_translation]
/-- Every numeric reconstructed map retains the original projected linear part. -/
theorem operation_linear (v h : Values) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    (operation v h e).linear = (reference v e).linear := by
  change projection (operation v h e) = projection (reference v e)
  rw [operation,map_mul,projection_translation,one_mul]

/-- Each complete original left word evaluates u, or u+z in the second face. -/
theorem left_apply (v h : Values) (f : Bool) (x : ZMod 2) :
    GroupExtension.pathValue geometry (operation v h) (geometry.twoLeft f) x =
      x + (if f then h false + h true else h false) := by
  cases f
  · rw [left_path_false]
    exact operation_e_apply v h x
  · rw [left_path_true]
    change operation v h (name edgeC).2.2 (operation v h (name edgeE).2.2 x) = x + (h false + h true)
    rw [operation_e_apply,operation_c_apply,add_assoc]
/-- Each complete original right word retains the corresponding fixed physical input. -/
theorem right_apply (v h : Values) (f : Bool) (x : ZMod 2) :
    GroupExtension.pathValue geometry (operation v h) (geometry.twoRight f) x = x + v f := by
  rw [right_path]
  cases f
  · change operation v h (name edgeA).2.2 x = _
    rw [operation_a,reference_a_apply]
  · change operation v h (name edgeB).2.2 x = _
    rw [operation_b,reference_b_apply]

/-- Both same original real face equalities are precisely their complete numerical equations. -/
theorem face_iff (v h : Values) (f : Bool) :
    translation (k := ZMod 2) (comparison f) *
      GroupExtension.pathValue geometry (operation v h) (geometry.twoLeft f) =
      GroupExtension.pathValue geometry (operation v h) (geometry.twoRight f) ↔
      (if f then h false + h true else h false) = v f := by
  rw [comparison_zero,zero_translation,one_mul]
  constructor
  · intro he
    have h0 := congrArg (fun g : Op => g 0) he
    simpa only [left_apply,right_apply,zero_add] using h0
  · intro he
    apply AffineEquiv.ext
    intro x
    rw [left_apply,right_apply,he]

/-- The independent two face equations on fully evaluated u and z. -/
def Equations (v h : Values) : Prop := h false = v false ∧ h false + h true = v true
/-- Basic API: both numerical equations are required independently. -/
theorem equations_iff (v h : Values) : Equations v h ↔ h false = v false ∧ h false + h true = v true := Iff.rfl
/-- The numeric predicate has a valid and an invalid complete tuple on the same input. -/
theorem equations_examples : Equations (0 : Values) 0 ∧ ¬ Equations (0 : Values) (fun _ => 1) := by
  simp [equations_iff]

/-- The whole always/candidate values of any independent actual repair. -/
def coordinates {v : Values} (R : RealRepairs v) : Values :=
  fun j => R.operation (name (if j then edgeC else edgeE)).2.2 0
/-- Basic API: the acquired u is the entire actual always operation's zero value. -/
theorem coordinates_false {v : Values} (R : RealRepairs v) :
    coordinates R false = R.operation (name edgeE).2.2 0 := rfl
/-- Basic API: the acquired z is the entire actual candidate operation's zero value. -/
theorem coordinates_true {v : Values} (R : RealRepairs v) :
    coordinates R true = R.operation (name edgeC).2.2 0 := rfl
/-- Every independent map is determined by its original linear part and actual zero value. -/
theorem actual_operation_apply {v : Values} (R : RealRepairs v)
    {i j : geometry.Vertex} (e : geometry.Edge i j) (x : ZMod 2) :
    R.operation e x = x + R.operation e 0 := by
  rw [NativeAffine.operation_apply,R.linear,reference_linear]
  rfl

/-- Reading a repair's two values reconstructs all four whole original maps. -/
theorem coordinates_operations {v : Values} (R : RealRepairs v) :
    @operation v (coordinates R) = @R.operation := by
  have ha := R.fixed_value (name edgeA) (Or.inl rfl)
  have hb := R.fixed_value (name edgeB) (Or.inr rfl)
  funext i j e
  have ho := congrArg (fun n : EdgeName (K := geometry) => operation v (coordinates R) n.2.2)
    (name_edge ⟨i,j,e⟩)
  have hr := congrArg (fun n : EdgeName (K := geometry) => R.operation n.2.2)
    (name_edge ⟨i,j,e⟩)
  dsimp only at ho hr
  rw [← ho,← hr]
  generalize e.1 = n
  fin_cases n
  · apply AffineEquiv.ext
    intro x
    change operation v (coordinates R) (name edgeE).2.2 x = _
    rw [operation_e_apply,actual_operation_apply,coordinates_false]
    rfl
  · change operation v (coordinates R) (name edgeA).2.2 = R.operation (name edgeA).2.2
    rw [operation_a,ha]
  · change operation v (coordinates R) (name edgeB).2.2 = R.operation (name edgeB).2.2
    rw [operation_b,hb]
  · apply AffineEquiv.ext
    intro x
    change operation v (coordinates R) (name edgeC).2.2 x = _
    rw [operation_c_apply,actual_operation_apply,coordinates_true]
    rfl

/-- Both actual authored faces imply the same complete numeric equations. -/
theorem coordinates_equations {v : Values} (R : RealRepairs v) : Equations v (coordinates R) := by
  have hf : ∀ f : Bool, (if f then coordinates R false + coordinates R true else coordinates R false) = v f := by
    intro f
    have h := R.face f
    rw [← coordinates_operations R] at h
    exact (face_iff v (coordinates R) f).mp h
  exact ⟨hf false,hf true⟩

/-- Whole numeric reconstruction retains the same original fixed a and b maps. -/
theorem operation_fixed (v h : Values) (e : EdgeName (K := geometry))
    (he : e ∈ fixedRegion.edges) : operation v h e.2.2 = reference v e.2.2 := by
  rcases he with rfl | rfl
  · exact operation_a v h
  · exact operation_b v h

/-- Every correct fully acquired numeric pair restores the independent actual repair of these same faces. -/
noncomputable def fromCoordinates (v h : Values) (he : Equations v h) : RealRepairs v where
  operation := operation v h
  linear := operation_linear v h
  face f := (face_iff v h f).mpr (by cases f; exact he.1; exact he.2)
  fixed_value := operation_fixed v h

/-- Restored actual corrections keep every original e/a/b/c coefficient against the same reference. -/
theorem fromCoordinates_correction (v h : Values) (he : Equations v h)
    (e : EdgeName (K := geometry)) :
    NativeAffine.realCorrection geometry (reference v) comparison fixedRegion.edges
      (fromCoordinates v h he) e = correctionValue h e.2.2.1 := by
  rw [NativeAffine.real_correction_value]
  change (operation v h e.2.2 * (reference v e.2.2)⁻¹) 0 = _
  rw [operation,mul_assoc,mul_inv_cancel,mul_one]
  exact add_zero _

/-- Reading the restored repair returns both complete acquired coordinates. -/
theorem coordinates_from (v h : Values) (he : Equations v h) : coordinates (fromCoordinates v h he) = h := by
  ext j
  cases j
  · rw [coordinates_false]
    change operation v h (name edgeE).2.2 0 = h false
    rw [operation_e_apply,zero_add]
  · rw [coordinates_true]
    change operation v h (name edgeC).2.2 0 = h true
    rw [operation_c_apply,zero_add]
/-- Restoring every independent actual repair's values retains its whole original operation family. -/
theorem from_coordinates {v : Values} (R : RealRepairs v) :
    fromCoordinates v (coordinates R) (coordinates_equations R) = R := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact congrFun (congrFun (congrFun (coordinates_operations R) i) j) e

/-- All independent actual repairs and all complete numeric solutions have both inverses. -/
noncomputable def actualCoordinatesEquiv (v : Values) : RealRepairs v ≃ {h : Values // Equations v h} where
  toFun R := ⟨coordinates R,coordinates_equations R⟩
  invFun h := fromCoordinates v h.1 h.2
  left_inv := from_coordinates
  right_inv h := Subtype.ext (coordinates_from v h.1 h.2)
/-- G-130 restores every complete numeric solution to the same full original native repair. -/
noncomputable def nativeCoordinatesEquiv (v : Values) :
    SupportedRepair (originalTower v) fixedRegion.edges ≃ {h : Values // Equations v h} :=
  (NativeAffine.repairEquivalence geometry (reference v) (reference v) comparison
    (linear_faces v) fixedRegion.edges).trans (actualCoordinatesEquiv v)

end AAT.AG.RepairObservationDuality.KPlusActualRepairs
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.KPlusActualRepairs
