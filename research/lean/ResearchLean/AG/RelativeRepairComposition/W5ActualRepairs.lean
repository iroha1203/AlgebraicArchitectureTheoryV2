import ResearchLean.AG.RelativeRepairComposition.W5AuthoredOperations
import ResearchLean.AG.RelativeRepairComposition.W5Regions

/-!
# W5's independent whole actual repairs and full original shared value

Independent repairs are actual affine maps with original projections, faces
and fixed inputs. Reading the shared operation at zero then derives both
input equations. Every shared value satisfying those equations restores all
three whole original maps, with exact inverses.
-/
namespace AAT.AG.RelativeRepairComposition.W5ActualRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput W5Regions W5AuthoredOperations

/-- All independent whole original repairs retain both physical input operations. -/
abbrev RealRepairs (b₁ b₂ : ZMod 2) :=
  NativeAffine.Repair geometry (reference b₁ b₂) comparison fixedRegion.edges
/-- The original full actual repair groupoid retains every permitted vertex label. -/
abbrev ActualCategory (b₁ b₂ : ZMod 2) :=
  NativeAffine.Groupoid geometry (reference b₁ b₂) (reference b₁ b₂) comparison
    (linear_faces b₁ b₂) fixedRegion.vertices fixedRegion.edges
/-- The original tower's independent full native repair groupoid. -/
abbrev NativeCategory (b₁ b₂ : ZMod 2) :=
  RepairGroupoid (originalTower b₁ b₂) fixedRegion.vertices fixedRegion.edges

/-- The original actual shared-edge map supplies its whole zero value. -/
def value {b₁ b₂ : ZMod 2} (R : RealRepairs b₁ b₂) : ZMod 2 :=
  R.operation (name edgeE).2.2 0
/-- Every actual original operation is determined by its original linear part and zero value. -/
theorem actual_operation_apply {b₁ b₂ : ZMod 2} (R : RealRepairs b₁ b₂)
    {i j : geometry.Vertex} (e : geometry.Edge i j) (x : ZMod 2) :
    R.operation e x = x + R.operation e 0 := by
  rw [NativeAffine.operation_apply,R.linear,reference_linear]
  rfl
/-- The whole restored family equals every original actual map, retaining both physical inputs. -/
theorem value_operations {b₁ b₂ : ZMod 2} (R : RealRepairs b₁ b₂) :
    @operation b₁ b₂ (value R) = @R.operation := by
  have ha := R.fixed_value (name edgeA) (Or.inl rfl)
  have hb := R.fixed_value (name edgeB) (Or.inr rfl)
  funext i j e
  rcases e with ⟨e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e
  · apply AffineEquiv.ext
    intro x
    change operation b₁ b₂ (value R) (name edgeE).2.2 x = _
    rw [operation_e_apply,actual_operation_apply]
    rfl
  · change operation b₁ b₂ (value R) (name edgeA).2.2 = R.operation (name edgeA).2.2
    rw [ha]
    apply AffineEquiv.ext
    intro x
    rw [operation_a_apply]
    simp [reference,name,edgeA,add_comm]
  · change operation b₁ b₂ (value R) (name edgeB).2.2 = R.operation (name edgeB).2.2
    rw [hb]
    apply AffineEquiv.ext
    intro x
    rw [operation_b_apply]
    simp [reference,name,edgeA,edgeB,add_comm]

/-- Every original actual face derives its relevant shared-value equation. -/
theorem value_face {b₁ b₂ : ZMod 2} (R : RealRepairs b₁ b₂) (f : Bool) :
    value R = inputValue b₁ b₂ f := by
  have hf := R.face f
  rw [← value_operations R] at hf
  exact (face_iff b₁ b₂ (value R) f).mp hf
/-- Both independent actual face equations hold for the same original shared operation. -/
theorem value_inputs {b₁ b₂ : ZMod 2} (R : RealRepairs b₁ b₂) :
    value R = b₁ ∧ value R = b₂ := ⟨value_face R false,value_face R true⟩

/-- Every restored family preserves the original physical a,b literally, before any face condition. -/
theorem operation_fixed (b₁ b₂ u : ZMod 2) (e : EdgeName (K := geometry))
    (he : e ∈ fixedRegion.edges) : operation b₁ b₂ u e.2.2 = reference b₁ b₂ e.2.2 := by
  rcases he with he | he <;> subst e
  · apply AffineEquiv.ext
    intro x
    rw [operation_a_apply]
    simp [reference,name,edgeA,add_comm]
  · apply AffineEquiv.ext
    intro x
    rw [operation_b_apply]
    simp [reference,name,edgeA,edgeB,add_comm]
/-- Both derived input equations construct an independent whole original repair. -/
noncomputable def fromValue (b₁ b₂ u : ZMod 2) (h₁ : u = b₁) (h₂ : u = b₂) :
    RealRepairs b₁ b₂ where
  operation := operation b₁ b₂ u
  linear := operation_linear b₁ b₂ u
  face f := by
    apply (face_iff b₁ b₂ u f).mpr
    cases f
    · exact h₁
    · exact h₂
  fixed_value := operation_fixed b₁ b₂ u
/-- Reading the restored whole shared operation recovers the same value. -/
theorem value_from (b₁ b₂ u : ZMod 2) (h₁ : u = b₁) (h₂ : u = b₂) :
    value (fromValue b₁ b₂ u h₁ h₂) = u := by
  change operation b₁ b₂ u (name edgeE).2.2 0 = u
  rw [operation_e_apply,zero_add]
/-- Restoring the derived value recovers all original operations of every independent repair. -/
theorem from_value {b₁ b₂ : ZMod 2} (R : RealRepairs b₁ b₂) :
    fromValue b₁ b₂ (value R) (value_inputs R).1 (value_inputs R).2 = R := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact congrFun (congrFun (congrFun (value_operations R) i) j) e
/-- Whole independent original repairs and the exact derived shared values have both inverses. -/
noncomputable def actualValueEquiv (b₁ b₂ : ZMod 2) :
    RealRepairs b₁ b₂ ≃ {u : ZMod 2 // u = b₁ ∧ u = b₂} where
  toFun R := ⟨value R,value_inputs R⟩
  invFun u := fromValue b₁ b₂ u.1 u.2.1 u.2.2
  left_inv := from_value
  right_inv u := Subtype.ext (value_from b₁ b₂ u.1 u.2.1 u.2.2)
/-- The same full native correspondence retains the original operations and derived shared values. -/
noncomputable def nativeValueEquiv (b₁ b₂ : ZMod 2) :
    SupportedRepair (originalTower b₁ b₂) fixedRegion.edges ≃
      {u : ZMod 2 // u = b₁ ∧ u = b₂} :=
  (NativeAffine.repairEquivalence geometry (reference b₁ b₂) (reference b₁ b₂)
    comparison (linear_faces b₁ b₂) fixedRegion.edges).trans (actualValueEquiv b₁ b₂)
/-- The whole original native and actual groupoids preserve all physically permitted arrows. -/
noncomputable def wholeAffineEquivalence (b₁ b₂ : ZMod 2) :
    NativeCategory b₁ b₂ ≌ ActualCategory b₁ b₂ :=
  NativeAffine.groupoidEquivalence geometry (reference b₁ b₂) (reference b₁ b₂)
    comparison (linear_faces b₁ b₂) fixedRegion.vertices fixedRegion.edges

end AAT.AG.RelativeRepairComposition.W5ActualRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5ActualRepairs
