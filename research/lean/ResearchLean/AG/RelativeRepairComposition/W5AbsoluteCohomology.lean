import ResearchLean.AG.RelativeRepairComposition.W5RelativeObstruction

/-! # Absolute H2 of the same complete original W5 input

All three original edge corrections are retained when P is empty. The original
face differential is onto the whole two-face kernel family. Its complete
absolute H2 vanishes, while the same native relative class records the original
physical fixed inputs.
-/
namespace AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W5AffineInput W5Regions W5OriginalDifferentials W5RelativeCoefficients W5RelativeObstruction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (b₁ b₂ : ZMod 2)
local notation "T" => originalTower b₁ b₂
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower b₁ b₂))
/-- A full original edge family restores any two original face coordinates without physical fixing. -/
noncomputable def absoluteCochain (r : Bool → ZMod 2) : C1 M :=
  fun e => (kernelCoordinate b₁ b₂ e.2.1).symm
    (if e.2.2.1 = edgeE then 0 else if e.2.2.1 = edgeA then -r false else -r true)
/-- The same complete original face differential evaluates the restored whole face family. -/
theorem absolute_d1_value (r : Bool → ZMod 2) (f : Bool) :
    kernelCoordinate b₁ b₂ vertexT (d1 M (absoluteCochain b₁ b₂ r) f) = r f := by
  rw [W5OriginalDifferentials.d1_value]
  change (kernelCoordinate b₁ b₂ vertexT) ((kernelCoordinate b₁ b₂ vertexT).symm _) -
    (kernelCoordinate b₁ b₂ vertexT) ((kernelCoordinate b₁ b₂ vertexT).symm _) = _
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  cases f <;> simp [name,edgeE,edgeA,edgeB]
/-- The entire original absolute face differential is surjective, derived from its original authored words. -/
theorem absolute_d1_surjective : Function.Surjective (d1Hom M) := by
  intro c
  refine ⟨absoluteCochain b₁ b₂ (fun f => kernelCoordinate b₁ b₂ vertexT (c f)),?_⟩
  funext f
  apply (kernelCoordinate b₁ b₂ vertexT).injective
  exact absolute_d1_value b₁ b₂ _ f
/-- The same unrestricted original edge family is an actual member of the absolute supported group. -/
noncomputable def absoluteSupported (a : C1 M) : RelativeComplex.C1Group M ClosedRegion.empty ∅ ∅ :=
  ⟨a,by
    intro e he
    have hz : e ∈ (∅ : Set (EdgeName (K := geometry))) := by
      simp [fixedEdgesForRange,ClosedRegion.empty] at he
    exact hz.elim⟩
/-- The entire original absolute relative/support differential is onto every whole original face family. -/
theorem absolute_supported_surjective :
    Function.Surjective (RelativeComplex.d1Supported M ClosedRegion.empty ∅ ∅) := by
  intro c
  obtain ⟨a,ha⟩ := absolute_d1_surjective b₁ b₂ c.1
  exact ⟨absoluteSupported b₁ b₂ a,Subtype.ext ha⟩
/-- Every class of the same original absolute H2 is zero by the complete original differential. -/
theorem absolute_h2_zero (h : RelativeComplex.H2 M ClosedRegion.empty ∅ ∅) : h = 0 := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective
    (RelativeComplex.d1ToZ2 M ClosedRegion.empty ∅ ∅).range h
  apply (RelativeComplex.h2_eq_zero_iff M ClosedRegion.empty ∅ ∅ z).mpr
  obtain ⟨a,ha⟩ := absolute_supported_surjective b₁ b₂ z.1
  exact ⟨a,Subtype.ext ha⟩
/-- Forgetting physical fixed cells keeps every same original relative face coefficient. -/
noncomputable def forgetPhysicalFace : RelativeComplex.relativeC2 M fixedRegion →+
    RelativeComplex.relativeC2 M ClosedRegion.empty where
  toFun c := ⟨c.1,by funext f; exact f.2.elim⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
/-- The relative-to-absolute face comparison preserves the actual defect on each original authored face. -/
theorem forget_actual_defect (f : Bool) :
    (forgetPhysicalFace b₁ b₂
      (ActualRelative.obstructionCocycle T fixedRegion (fixed_faces b₁ b₂) (original_syzygy b₁ b₂)).1).1 f =
        (T).toTower.defect f := rfl

end AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology
