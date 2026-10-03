import ResearchLean.AG.RepairObservationDuality.W1PhysicalInputs
import ResearchLean.AG.RelativeRepairComposition.W1RelativeCoefficients
import ResearchLean.AG.RepairObservationDuality.FiniteRepairPlanning

/-!
# G-131 E: full W1 numerical values and the original native equation

## Implementation notes

All four scalar coordinates u,h,z,v are output data. The first two rows are
the original native relative differential, evaluated in its entire kernel
basis. Two extra zero rows encode the original forbidden candidate masks;
they do not discard private h or identify the distinct original b/c names.
This constrained presentation is equivalent to the original supported source
and to the independently specified actual repairs. Its matrix is generated
before values are acquired, and its RHS comes from the actual native defect.
-/
namespace AAT.AG.RepairObservationDuality.W1NumericalEquation
open TransportCoherence AbelianLiftingObstruction
open RelativeRepairComposition W1AffineInput W1Regions W1ActualRepairs W1RelativeCoefficients
open W1PhysicalInputs
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Permissions for the distinct original b and c names, in that order. -/
abbrev Permissions := Bool → Bool

/-- The permitted original candidate subset; no always edge is a candidate. -/
def allowed (p : Permissions) : Set (EdgeName (K := geometry)) :=
  {e | (e = name edgeB ∧ p false = true) ∨ (e = name edgeC ∧ p true = true)}

/-- Membership keeps original candidate b distinct from c. -/
theorem b_mem (p : Permissions) : name edgeB ∈ allowed p ↔ p false = true := by
  simp [allowed, name, edgeB, edgeC, geometry]

/-- Membership keeps original candidate c distinct from b. -/
theorem c_mem (p : Permissions) : name edgeC ∈ allowed p ↔ p true = true := by
  simp [allowed, name, edgeB, edgeC, geometry]

/-- Every selected name remains an original candidate. -/
theorem allowed_subset (p : Permissions) : allowed p ⊆ candidates := by
  rintro e (⟨rfl,_⟩ | ⟨rfl,_⟩)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Nonempty permissions are exactly either of the two distinct original candidate names. -/
theorem allowed_nonempty_iff (p : Permissions) :
    (allowed p).Nonempty ↔ p false = true ∨ p true = true := by
  constructor
  · rintro ⟨e,(⟨_,hb⟩ | ⟨_,hc⟩)⟩
    · exact Or.inl hb
    · exact Or.inr hc
  · rintro (hb | hc)
    · exact ⟨name edgeB,(b_mem p).mpr hb⟩
    · exact ⟨name edgeC,(c_mem p).mpr hc⟩

/-- Every original candidate subset is represented without identifying its names. -/
theorem all_subsets (S : Set (EdgeName (K := geometry)))
    (hS : S ⊆ candidates) : ∃ p : Permissions, allowed p = S := by
  classical
  refine ⟨fun j => decide (name (if j then edgeC else edgeB) ∈ S),?_⟩
  ext e
  constructor
  · rintro (⟨rfl,h⟩ | ⟨rfl,h⟩) <;> simpa using h
  · intro he
    rcases hS he with hb | hc
    · exact Or.inl ⟨hb,by simpa [← hb] using he⟩
    · change e = name edgeC at hc
      exact Or.inr ⟨hc,by simpa [← hc] using he⟩

/-- The entire original correction data, including the unrestricted private h. -/
abbrev Corrections := Fin 4 → ZMod 3

/-- Recover the whole original authored operation parameters from all coordinates. -/
def parameters (a : Corrections) : W1ActualRepairs.Parameters := ⟨a 0,a 1,a 2,a 3⟩

/-- Basic API: the full original u field is the first acquired coordinate. -/
theorem parameters_u (a : Corrections) : (parameters a).u = a 0 := rfl

/-- Basic API: the full private h field is the second acquired coordinate. -/
theorem parameters_h (a : Corrections) : (parameters a).h = a 1 := rfl

/-- Basic API: the original candidate b field is the third acquired coordinate. -/
theorem parameters_z (a : Corrections) : (parameters a).z = a 2 := rfl

/-- Basic API: the original candidate c field is the fourth acquired coordinate. -/
theorem parameters_v (a : Corrections) : (parameters a).v = a 3 := rfl

/-- The full constrained native differential, with support encoded by two zero rows. -/
def differential (p : Permissions) : Corrections →ₗ[ZMod 3] Corrections where
  toFun a := ![a 0 + a 2, a 0 - a 2 + a 3,
    if p false then 0 else a 2, if p true then 0 else a 3]
  map_add' a b := by
    ext i
    fin_cases i <;> cases p false <;> cases p true <;>
      simp [add_sub_add_comm,add_assoc,add_left_comm,add_comm]
  map_smul' t a := by
    ext i
    fin_cases i <;> cases p false <;> cases p true <;> simp [mul_add,mul_sub]

/-- The affine linear RHS places the actual x,y in the two original face rows. -/
def rhsLinear : Values →ₗ[ZMod 3] Corrections where
  toFun v := ![v false,v true,0,0]
  map_add' a b := by ext i; fin_cases i <;> simp
  map_smul' t a := by ext i; fin_cases i <;> simp

/-- Basic API for all four known differential rows. -/
theorem differential_apply (p : Permissions) (a : Corrections) :
    differential p a = ![a 0 + a 2,a 0 - a 2 + a 3,
      if p false then 0 else a 2,if p true then 0 else a 3] := rfl

/-- Basic API for the entire generated RHS. -/
theorem rhsLinear_apply (v : Values) : rhsLinear v = ![v false,v true,0,0] := rfl

/-- The first two rows are exactly the same original full native differential on every correction. -/
theorem original_differential (x y : ZMod 3) (a : Corrections) (f : Bool) :
    faceCoordinates true x y
      (FiniteCoefficients.differential1 ((originalTower true x y).toTower.localCoefficients)
        (W1FiniteCoefficients.original_linear true x y) ClosedRegion.all fixedRegion
        (relativeCochain true x y (a 0) (a 1) (a 2) (a 3))) f =
      differential (fun _ => true) a (if f then 1 else 0) := by
  cases f
  · rw [relative_d1_first,relativeCochain_value,relativeCochain_value]
    simp [W1AuthoredOperations.correctionValue,name,edgeE,edgeA,edgeB,differential,geometry]
  · rw [relative_d1_second_negative,relativeCochain_value,relativeCochain_value,relativeCochain_value]
    simp [W1AuthoredOperations.correctionValue,name,edgeE,edgeA,edgeB,edgeC,differential,geometry]

/-- The same actual signed defect supplies both original face RHS values; b0 is zero. -/
theorem original_rhs (v : Values) (f : Bool) :
    faceCoordinates true (v false) (v true) (-actualDefect true (v false) (v true)) f =
      affineRhs rhsLinear 0 v (if f then 1 else 0) := by
  rw [signedDefect_coordinates]
  cases f <;> simp [affineRhs_apply,rhsLinear]

/-- The complete equation is precisely both original authored Laws and both original candidate masks. -/
theorem equation_iff (p : Permissions) (v : Values) (a : Corrections) :
    differential p a = affineRhs rhsLinear 0 v ↔
      Equations true (v false) (v true) (parameters a) ∧ Allowed (allowed p) (parameters a) := by
  rw [differential_apply]
  simp only [affineRhs_apply,zero_add,rhsLinear_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at h0 h1 h2 h3
    refine ⟨⟨h0,h1⟩,?_,?_⟩
    · intro hb
      have hp : p false = false := Bool.eq_false_iff.mpr (fun ht => hb ((b_mem p).mpr ht))
      simpa [parameters,hp] using h2
    · intro hc
      have hp : p true = false := Bool.eq_false_iff.mpr (fun ht => hc ((c_mem p).mpr ht))
      simpa [parameters,hp] using h3
  · rintro ⟨he,ha⟩
    ext i
    fin_cases i
    · exact he.1
    · exact he.2
    · cases hp : p false
      · exact ha.1 (by rw [b_mem,hp]; decide)
      · simp

    · cases hp : p true
      · exact ha.2 (by rw [c_mem,hp]; decide)
      · simp

/-- Exact feasibility retains the zero obstruction or either distinct permitted candidate. -/
theorem solvable_iff (p : Permissions) (v : Values) :
    Solvable (differential p) (affineRhs rhsLinear 0) v ↔
      v true = v false ∨ p false = true ∨ p true = true := by
  constructor
  · rintro ⟨a,ha⟩
    by_cases hb : p false = true
    · exact Or.inr (Or.inl hb)
    by_cases hc : p true = true
    · exact Or.inr (Or.inr hc)
    have h := (equation_iff p v a).mp ha
    have hz := h.2.1 (by simpa [b_mem] using hb)
    have hv := h.2.2 (by simpa [c_mem] using hc)
    change a 2 = 0 at hz
    change a 3 = 0 at hv
    have hx : a 0 = v false := by simpa [parameters,hz] using h.1.1
    have hy : a 0 = v true := by simpa [parameters,hz,hv] using h.1.2
    exact Or.inl (hy.symm.trans hx)
  · rintro (he | hb | hc)
    · refine ⟨![v false,0,0,0],?_⟩
      rw [differential_apply]
      ext i
      fin_cases i <;> simp [affineRhs_apply,rhsLinear_apply,he]
    · let u := 2 * (v false + v true)
      have hchar : ∀ x y : ZMod 3, 2 * (x + y) - (x - 2 * (x + y)) = y := by decide
      refine ⟨![u,0,v false - u,0],?_⟩
      rw [differential_apply]
      ext i
      fin_cases i
      · simp [affineRhs_apply,rhsLinear_apply]
      · simpa [affineRhs_apply,rhsLinear_apply,u] using hchar (v false) (v true)
      · simp [hb,affineRhs_apply,rhsLinear_apply]
      · simp [affineRhs_apply,rhsLinear_apply]
    · refine ⟨![v false,0,0,v true - v false],?_⟩
      rw [differential_apply]
      ext i
      fin_cases i <;> simp [hc,affineRhs_apply,rhsLinear_apply]

/-- The residual native cokernel detects exactly the same full original feasibility. -/
theorem residual_kernel_iff (p : Permissions) (v : Values) :
    v ∈ LinearMap.ker ((LinearMap.range (differential p)).mkQ.comp rhsLinear) ↔
      v true = v false ∨ p false = true ∨ p true = true := by
  change (LinearMap.range (differential p)).mkQ (rhsLinear v) = 0 ↔ _
  have h : (∃ a, differential p a = rhsLinear v) ↔
      Solvable (differential p) (affineRhs rhsLinear 0) v := by
    simp only [solvable_iff_exists,affineRhs_apply,zero_add]
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range (differential p))).trans
    (h.trans (solvable_iff p v))

/-- Full numerical solvability is the independently specified same original actual repair. -/
theorem actual_iff (p : Permissions) (X : Inputs) :
    Nonempty (RealRepairs true (values X false) (values X true) (allowed p)) ↔
      Solvable (differential p) (affineRhs rhsLinear 0) (values X) := by
  constructor
  · rintro ⟨R⟩
    let q := W1ActualRepairs.parameters R
    refine ⟨![q.u,q.h,q.z,q.v],(equation_iff p (values X) _).mpr ?_⟩
    exact ⟨parameters_equations R,parameters_allowed R⟩
  · rintro ⟨a,ha⟩
    have h := (equation_iff p (values X) a).mp ha
    exact ⟨actualRepair true (values X false) (values X true) (allowed p) (parameters a) h.1 h.2⟩

/-- Full returned coordinates restore the actual original operation family and its fixed arrows. -/
noncomputable def restore (p : Permissions) (X : Inputs) (a : Corrections)
    (ha : differential p a = affineRhs rhsLinear 0 (values X)) :
    RealRepairs true (values X false) (values X true) (allowed p) :=
  actualRepair true (values X false) (values X true) (allowed p) (parameters a)
    ((equation_iff p (values X) a).mp ha).1 ((equation_iff p (values X) a).mp ha).2

/-- Restoration retains all original numerical parameters, including private h. -/
theorem restore_parameters (p : Permissions) (X : Inputs) (a : Corrections)
    (ha : differential p a = affineRhs rhsLinear 0 (values X)) :
    W1ActualRepairs.parameters (restore p X a ha) = parameters a :=
  actualRepair_parameters true _ _ _ _ _ _

/-- Every full private h is permitted on the zero input, while the original masks still prohibit nonzero candidate values. -/
theorem private_values (p : Permissions) (r : ZMod 3) :
    differential p ![0,r,0,0] = affineRhs rhsLinear 0 (0 : Values) := by
  rw [differential_apply]
  ext i
  fin_cases i <;> simp [affineRhs_apply,rhsLinear_apply]

/-- The original empty mask rejects the actual nonzero ry input, but either original single candidate permits it. -/
theorem permission_examples :
    ¬ Solvable (differential (fun _ => false)) (affineRhs rhsLinear 0) (fun j => if j then 1 else 0) ∧
    Solvable (differential (fun j => !j)) (affineRhs rhsLinear 0) (fun j => if j then 1 else 0) ∧
    Solvable (differential (fun j => j)) (affineRhs rhsLinear 0) (fun j => if j then 1 else 0) := by
  simp [solvable_iff]

/-- D's known finite matrix is generated from the complete constrained original differential. -/
noncomputable def matrix (p : Permissions) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  LinearMap.toMatrix' (differential p)

/-- The known matrix acts as the exact complete original differential. -/
theorem matrix_differential (p : Permissions) : FiniteMatrixSolver.differential (matrix p) = differential p :=
  Matrix.toLin'_toMatrix' _

end AAT.AG.RepairObservationDuality.W1NumericalEquation
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1NumericalEquation
