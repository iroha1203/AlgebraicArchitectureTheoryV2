import ResearchLean.AG.RelativeRepairComposition.NativeAffineKernel
import ResearchLean.AG.AbelianLiftingObstruction.GroupExtension

/-!
# Original affine edges and reference edges in the full native tower

The original edge is arbitrary. Its reference lift is the actual operation
R times inverse L, so core reselection recovers R while retaining L.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
local notation "π" => projection (k := k) (A := A)

/-- Every given original affine edge remains the original arrow of the real tower. -/
noncomputable def original : LiftData K.toFiniteTransportTwoPresentation
    (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A)) where
  object _ := SingleObj.star (Operations k A)
  edgeBase _ := 𝟙 _
  edgeLift e := L e
  edgeStrong e := GroupExtension.selectedStrong π (L e)

/-- Original paths evaluate precisely the same ordered affine operations. -/
theorem original_path_value {i j : K.Vertex} (w : K.Path i j) :
    (original K L).pathLift w = GroupExtension.pathValue K L w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (show Operations k A from (original K L).pathLift w) * L e = _
    rw [ih]
    rfl

/-- The reference lift is the original affine difference R times inverse L. -/
noncomputable def referenceLift {i j : K.Vertex} (e : K.Edge i j) :
    FiberAut (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
      ((original K L).object j) :=
  GroupExtension.upperEquiv π (R e * (L e)⁻¹)

/-- The fixed core is the linear projection of the same original reference lift. -/
noncomputable def core {i j : K.Vertex} (e : K.Edge i j) :
    FiberAut (GroupExtension.terminal (A ≃ₗ[k] A))
      ((GroupExtension.projection π).obj ((original K L).object j)) :=
  GroupExtension.lowerEquiv (π (R e * (L e)⁻¹))

/-- The actual reference lift projects to its fixed core value. -/
theorem referenceLift_core {i j : K.Vertex} (e : K.Edge i j) :
    fiberPushforward (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      ((original K L).object j) (referenceLift K L R e) = core K L R e :=
  GroupExtension.pushforward_eq π _

/-- Reselection preserves L explicitly and returns exactly the original reference R. -/
theorem selected_edge_value {i j : K.Vertex} (e : K.Edge i j) :
    (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) (referenceLift K L R)).edgeLift e = R e := by
  change (R e * (L e)⁻¹) * L e = R e
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- All original typed reference paths keep the exact ordered affine word. -/
theorem selected_path_value {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper K (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      (original K L) (referenceLift K L R)).pathLift w = GroupExtension.pathValue K R w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (show Operations k A from
      (selectedUpper K _ _ (original K L) (referenceLift K L R)).pathLift w) *
      (show Operations k A from
        (selectedUpper K _ _ (original K L) (referenceLift K L R)).edgeLift e) = _
    rw [ih, selected_edge_value]
    rfl

/-- Original affine arrows are strong for the lower projection as well. -/
theorem original_lower_strong {i j : K.Vertex} (e : K.Edge i j) :
    (GroupExtension.terminal (A ≃ₗ[k] A)).IsStronglyCocartesian
      ((original K L).edgeBase e)
      ((GroupExtension.projection π).map ((original K L).edgeLift e)) :=
  GroupExtension.selectedLowerStrong π (L e)

/-- A designated original translation supplies the authored comparison operation. -/
noncomputable def comparator (c : K.TwoCell → A) (f : K.TwoCell) :
    FiberAut (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
      ((original K L).object (K.twoTarget f)) :=
  GroupExtension.upperEquiv π (translation (k := k) (c f))

/-- All designated translation comparisons centralize the entire actual categorical kernel. -/
theorem comparator_centralizes (c : K.TwoCell → A) (f : K.TwoCell)
    (a : Kernel (GroupExtension.projection π) (GroupExtension.terminal (A ≃ₗ[k] A))
      ((original K L).object (K.twoTarget f))) :
    comparator K L c f * kernelInclusion _ _ _ a =
      kernelInclusion _ _ _ a * comparator K L c f := by
  obtain ⟨x, rfl⟩ := (GroupExtension.kernelEquiv π).surjective a
  apply Subtype.ext
  apply Iso.ext
  change translation (k := k) (c f) * x.1 = x.1 * translation (k := k) (c f)
  exact ((centralizes_kernel_iff (translation (k := k) (c f))).mpr (by simp)) x

/-- Primitive reference linear face relations generate core alignment, with no repair assumption. -/
theorem core_alignment (c : K.TwoCell → A)
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (f : K.TwoCell) :
    (GroupExtension.projection π).map
        ((selectedUpper K _ _ (original K L) (referenceLift K L R)).pathLift (K.twoLeft f)) ≫
      (GroupExtension.projection π).map (FiberAut.hom (comparator K L c f)) =
    (GroupExtension.projection π).map
      ((selectedUpper K _ _ (original K L) (referenceLift K L R)).pathLift (K.twoRight f)) := by
  rw [selected_path_value, selected_path_value]
  change π (translation (k := k) (c f)) * π (GroupExtension.pathValue K R (K.twoLeft f)) =
    π (GroupExtension.pathValue K R (K.twoRight f))
  rw [projection_translation, one_mul]
  exact hfaces f

/-- Primitive original and reference affine operations generate A's full original tower. -/
noncomputable def tower (c : K.TwoCell → A)
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) :
    OriginalTowerPresentation K (GroupExtension.projection π)
      (GroupExtension.terminal (A ≃ₗ[k] A)) where
  original := original K L
  originalLowerStrong := original_lower_strong K L
  core := core K L R
  lift := referenceLift K L R
  lift_core := referenceLift_core K L R
  faceBase f := by
    change (show PUnit.{1} from (original K L).pathBase (K.twoLeft f)) =
      (show PUnit.{1} from (original K L).pathBase (K.twoRight f))
    exact Subsingleton.elim _ _
  comparator := comparator K L c
  coreAlignment := core_alignment K L R c hfaces
  kernelComm _ := GroupExtension.kernel_comm π kernel_comm
  edgeBijective e := by
    simpa only [selected_edge_value] using GroupExtension.transport_bijective π (R e)
  comparatorCentralizes := comparator_centralizes K L c

/-- The generated tower still contains the same arbitrary original affine arrow. -/
@[simp] theorem tower_original_edge (c : K.TwoCell → A)
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear)
    {i j : K.Vertex} (e : K.Edge i j) :
    (tower K L R c hfaces).original.edgeLift e = L e := rfl

/-- The generated selected tower contains precisely the same original reference affine arrow. -/
theorem tower_reference_edge (c : K.TwoCell → A)
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear)
    {i j : K.Vertex} (e : K.Edge i j) :
    (tower K L R c hfaces).toTower.upper.edgeLift e = R e := selected_edge_value K L R e

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
