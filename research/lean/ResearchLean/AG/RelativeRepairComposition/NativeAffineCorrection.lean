import ResearchLean.AG.RelativeRepairComposition.NativeAffineRepairs

/-! # Correction values of the independently specified original real affine repairs -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable (fixed : Set (EdgeName (K := K)))
local notation "T" => tower K L R c hfaces
local notation "Q" => repairEquivalence K L R c hfaces fixed
local notation "pi" => projection (k := k) (A := A)

/-- Every original native repair edge is the actual correction translation followed by the same real reference. -/
theorem native_repair_correction_value (s : SupportedRepair (T) fixed)
    {i j : K.Vertex} (e : K.Edge i j) :
    ((Q) s).operation e =
      translation (k := k) (coefficient K L R c hfaces j ((T).solutionCorrection s.1 ⟨i,j,e⟩)) * R e := by
  have h := congrArg (GroupExtension.upperEquiv pi).symm
    ((T).correctionChoice_solutionCorrection s.1 e)
  dsimp only [OriginalTowerPresentation.correctionChoice] at h
  rw [map_mul] at h
  change (show Operations k A from FiberAut.hom
    (kernelInclusion (GroupExtension.projection pi) (GroupExtension.terminal (A ≃ₗ[k] A))
      ((T).original.object j) (Additive.toMul ((T).solutionCorrection s.1 ⟨i,j,e⟩)))) *
        (R e * (L e)⁻¹) = (show Operations k A from FiberAut.hom (s.1.choice e)) at h
  rw [coefficient_inclusion] at h
  change (show Operations k A from FiberAut.hom (s.1.choice e)) * L e = _
  rw [← h, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

/-- The independently evaluated original correction is the value at zero of actual repair times inverse reference. -/
def realCorrection (s : Repair K R c fixed) (e : EdgeName (K := K)) : A :=
  (s.operation e.2.2 * (R e.2.2)⁻¹) 0

/-- The full native original correction and independent real evaluation are the same vector at the same edge name. -/
theorem real_correction_native (s : SupportedRepair (T) fixed) (e : EdgeName (K := K)) :
    realCorrection K R c fixed ((Q) s) e =
      coefficient K L R c hfaces e.2.1 ((T).solutionCorrection s.1 e) := by
  unfold realCorrection
  rw [native_repair_correction_value, mul_assoc, mul_inv_cancel, mul_one]
  simp

/-- Every independent original affine repair is recovered exactly by its evaluated correction and original reference. -/
theorem real_correction_restore (s : Repair K R c fixed) {i j : K.Vertex} (e : K.Edge i j) :
    s.operation e = translation (k := k) (realCorrection K R c fixed s ⟨i,j,e⟩) * R e := by
  have hp : projection (s.operation e * (R e)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change (s.operation e).linear * (R e).linear⁻¹ = 1
    rw [s.linear e, mul_inv_cancel]
  have h := (projection_eq_one_iff (s.operation e * (R e)⁻¹)).mp hp
  have hv := congrArg (fun g : Operations k A => g * R e) h
  change (s.operation e * (R e)⁻¹) * R e =
    translation (k := k) ((s.operation e * (R e)⁻¹) 0) * R e at hv
  rw [mul_assoc, inv_mul_cancel, mul_one] at hv
  exact hv

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
