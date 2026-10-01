import ResearchLean.AG.RelativeRepairComposition.NativeAffineEvaluation
import ResearchLean.AG.RelativeRepairComposition.SupportedRepairs

/-!
# Independently specified original affine repairs

The operations below are the actual repaired affine edges. Their projections,
word equalities and physical fixed values are specified before coordinates.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
local notation "π" => projection (k := k) (A := A)

/-- Original affine operations obeying the fixed projected edges, authored faces and physical anchors. -/
structure Repair (fixed : Set (EdgeName (K := K))) where
  /-- Every repaired original edge is a full invertible affine operation. -/
  operation : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A
  /-- Every original reference linear component is retained. -/
  linear : ∀ {i j : K.Vertex} (e : K.Edge i j), (operation e).linear = (R e).linear
  /-- All original temporal word relations retain the designated real comparison. -/
  face : ∀ f : K.TwoCell,
    translation (k := k) (c f) * GroupExtension.pathValue K operation (K.twoLeft f) =
      GroupExtension.pathValue K operation (K.twoRight f)
  /-- The actual affine operation equals the original reference on each physical fixed edge. -/
  fixed_value : ∀ e ∈ fixed, operation e.2.2 = R e.2.2

/-- Equality of all original affine edge operations determines the entire independent repair. -/
@[ext] theorem Repair.ext {fixed : Set (EdgeName (K := K))}
    (s t : Repair K R c fixed)
    (h : ∀ {i j : K.Vertex} (e : K.Edge i j), s.operation e = t.operation e) : s = t := by
  have he : @s.operation = @t.operation := by funext i j e; exact h e
  cases s
  cases t
  cases he
  rfl

/-- Reselecting an original edge evaluates its actual choice followed by the same L. -/
def chosenOperation
    (choice : ∀ {i j : K.Vertex}, K.Edge i j →
      FiberAut (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
        ((original K L).object j)) {i j : K.Vertex} (e : K.Edge i j) : Operations k A :=
  (show Operations k A from FiberAut.hom (choice e)) * L e

/-- Every original categorical choice retains its exact real affine edge value. -/
theorem chosen_edge_value
    (choice : ∀ {i j : K.Vertex}, K.Edge i j →
      FiberAut (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
        ((original K L).object j)) {i j : K.Vertex} (e : K.Edge i j) :
    (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) choice).edgeLift e = chosenOperation K L choice e := rfl

/-- Full original chosen paths evaluate the same ordered repaired affine operations. -/
theorem chosen_path_value
    (choice : ∀ {i j : K.Vertex}, K.Edge i j →
      FiberAut (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
        ((original K L).object j)) {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) choice).pathLift w = GroupExtension.pathValue K (chosenOperation K L choice) w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (show Operations k A from
      (selectedUpper K _ _ (original K L) choice).pathLift w) * chosenOperation K L choice e = _
    rw [ih]
    rfl

variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable (fixed : Set (EdgeName (K := K)))

/-- Full native supported repairs evaluate to independently specified real affine repairs. -/
noncomputable def toRepair (s : SupportedRepair (tower K L R c hfaces) fixed) :
    Repair K R c fixed where
  operation := chosenOperation K L s.1.choice
  linear e := by
    have hc := congrArg FiberAut.hom (s.1.choice_core e)
    change π (FiberAut.hom (s.1.choice e)) = π (R e * (L e)⁻¹) at hc
    change π (chosenOperation K L s.1.choice e) = π (R e)
    rw [chosenOperation, map_mul, hc, map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
  face f := by
    have hf := s.1.face f
    change (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) s.1.choice).pathLift (K.twoLeft f) ≫ translation (k := k) (c f) =
        (selectedUpper K _ _ (original K L) s.1.choice).pathLift (K.twoRight f) at hf
    rw [chosen_path_value, chosen_path_value] at hf
    exact hf
  fixed_value e he := by
    have h := s.2 e he
    change (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) s.1.choice).edgeLift e.2.2 =
        (tower K L R c hfaces).toTower.upper.edgeLift e.2.2 at h
    rw [chosen_edge_value, tower_reference_edge] at h
    exact h

/-- An independent real affine repair returns the original native choices R' times inverse L. -/
noncomputable def fromRepair (s : Repair K R c fixed) :
    SupportedRepair (tower K L R c hfaces) fixed := by
  let choice : ∀ {i j : K.Vertex}, K.Edge i j →
      FiberAut (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
        ((original K L).object j) := fun e => GroupExtension.upperEquiv π (s.operation e * (L e)⁻¹)
  have hop : @chosenOperation k _ A _ _ K L choice = @s.operation := by
    funext i j e
    change (s.operation e * (L e)⁻¹) * L e = s.operation e
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨{ choice := choice, choice_core := ?_, face := ?_ }, ?_⟩
  · intro i j e
    change fiberPushforward (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A)) _
      (GroupExtension.upperEquiv π (s.operation e * (L e)⁻¹)) =
        GroupExtension.lowerEquiv (π (R e * (L e)⁻¹))
    rw [GroupExtension.pushforward_eq]
    apply congrArg GroupExtension.lowerEquiv
    rw [map_mul, map_mul]
    exact congrArg (fun M : A ≃ₗ[k] A => M * π ((L e)⁻¹)) (s.linear e)
  · intro f
    change (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) choice).pathLift (K.twoLeft f) ≫ translation (k := k) (c f) =
        (selectedUpper K _ _ (original K L) choice).pathLift (K.twoRight f)
    rw [chosen_path_value, chosen_path_value, hop]
    exact s.face f
  · intro e he
    change (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) choice).edgeLift e.2.2 =
        (tower K L R c hfaces).toTower.upper.edgeLift e.2.2
    rw [chosen_edge_value, tower_reference_edge, hop]
    exact s.fixed_value e he

/-- All independent original affine repairs and all native actual repairs are mutually inverse. -/
noncomputable def repairEquivalence : SupportedRepair (tower K L R c hfaces) fixed ≃
    Repair K R c fixed where
  toFun := toRepair K L R c hfaces fixed
  invFun := fromRepair K L R c hfaces fixed
  left_inv s := by
    apply Subtype.ext
    apply Solution.ext
    intro i j e
    apply Subtype.ext
    apply Iso.ext
    change ((show Operations k A from FiberAut.hom (s.1.choice e)) * L e) * (L e)⁻¹ =
      FiberAut.hom (s.1.choice e)
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  right_inv s := by
    apply Repair.ext
    intro i j e
    change (s.operation e * (L e)⁻¹) * L e = s.operation e
    simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Forward coordinates preserve every original real repaired affine operation. -/
theorem repairEquivalence_value (s : SupportedRepair (tower K L R c hfaces) fixed)
    {i j : K.Vertex} (e : K.Edge i j) :
    (repairEquivalence K L R c hfaces fixed s).operation e =
      (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
        (original K L) s.1.choice).edgeLift e := rfl

/-- Reconstruction recovers each independent original affine operation exactly. -/
theorem repairEquivalence_inverse_value (s : Repair K R c fixed)
    {i j : K.Vertex} (e : K.Edge i j) :
    (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) ((repairEquivalence K L R c hfaces fixed).symm s).1.choice).edgeLift e =
        s.operation e := by
  change (s.operation e * (L e)⁻¹) * L e = s.operation e
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
