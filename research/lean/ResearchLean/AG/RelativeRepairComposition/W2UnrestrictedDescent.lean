import ResearchLean.AG.RelativeRepairComposition.W2FiniteCoefficients
import ResearchLean.AG.RelativeRepairComposition.NativeDescent

/-!
# Unrestricted B on the same original W2 tower and physical endpoints

Permitting both original candidate edges restores the unrestricted original
repair groupoid. The accepted full descent theorem applies to this same closed
cover and physical P. It retains the whole overlap isomorphism and every
compatible original vertex label.
-/
namespace AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W2AffineInput W2Regions W2ActualRepairs W2FiniteCoefficients
local notation "T" => originalTower

/-- Permitting both candidates restores the same original physical edge set. -/
theorem unrestricted_fixed : fixedEdges candidates = fixedRegion.edges := by
  simp only [fixedEdges, Set.diff_self, Set.union_empty]

/-- The full actual native homotopy pullback uses the same original tower, cover and physical P. -/
abbrev Descent := NativeDescent.Descent T fixedRegion fixed_faces leftRegion rightRegion

/-- All original unrestricted native repairs and compatible arrows satisfy B on this exact input. -/
noncomputable def nativeEquivalence : NativeCategory candidates ≌ Descent := by
  change RepairGroupoid originalTower fixedRegion.vertices (fixedEdges candidates) ≌
    NativeDescent.Descent originalTower fixedRegion fixed_faces leftRegion rightRegion
  rw [unrestricted_fixed]
  exact NativeDescent.equivalence T fixedRegion fixed_faces leftRegion rightRegion regions_cover

/-- Every original unrestricted full affine object and arrow has the same full native descent groupoid. -/
noncomputable def actualEquivalence : ActualCategory candidates ≌ Descent :=
  (wholeAffineEquivalence candidates).symm.trans nativeEquivalence

/-- The whole original comma groupoid keeps all invertible compatible arrows. -/
theorem descent_is_groupoid : IsGroupoid Descent :=
  NativeDescent.is_groupoid T fixedRegion fixed_faces leftRegion rightRegion

/-- Unrestricted descent keeps every original selected actual edge in U. -/
theorem left_choice (R : RepairGroupoid T fixedRegion.vertices fixedRegion.edges)
    {i j : leftRegion.vertices} (e : ClosedRegion.Edge leftRegion i j) :
    (((NativeDescent.equivalence T fixedRegion fixed_faces leftRegion rightRegion regions_cover).functor.obj R).left).back.1.choice e =
      R.back.1.choice e.1 :=
  NativeDescent.equivalence_left_choice T fixedRegion fixed_faces leftRegion rightRegion regions_cover R e

/-- Unrestricted descent keeps every original selected actual edge in V. -/
theorem right_choice (R : RepairGroupoid T fixedRegion.vertices fixedRegion.edges)
    {i j : rightRegion.vertices} (e : ClosedRegion.Edge rightRegion i j) :
    (((NativeDescent.equivalence T fixedRegion fixed_faces leftRegion rightRegion regions_cover).functor.obj R).right).back.1.choice e =
      R.back.1.choice e.1 :=
  NativeDescent.equivalence_right_choice T fixedRegion fixed_faces leftRegion rightRegion regions_cover R e

/-- Every unrestricted U arrow preserves its whole original vertex kernel label. -/
theorem left_label {R Q : RepairGroupoid T fixedRegion.vertices fixedRegion.edges}
    (b : R ⟶ Q) (v : leftRegion.vertices) :
    (((NativeDescent.equivalence T fixedRegion fixed_faces leftRegion rightRegion regions_cover).functor.map b).left).1.toAdd.1 v =
      b.1.toAdd.1 v.1 :=
  NativeDescent.equivalence_left_map_value T fixedRegion fixed_faces leftRegion rightRegion regions_cover b v

/-- Every unrestricted V arrow preserves its whole original vertex kernel label. -/
theorem right_label {R Q : RepairGroupoid T fixedRegion.vertices fixedRegion.edges}
    (b : R ⟶ Q) (v : rightRegion.vertices) :
    (((NativeDescent.equivalence T fixedRegion fixed_faces leftRegion rightRegion regions_cover).functor.map b).right).1.toAdd.1 v =
      b.1.toAdd.1 v.1 :=
  NativeDescent.equivalence_right_map_value T fixedRegion fixed_faces leftRegion rightRegion regions_cover b v

/-- The whole unrestricted forward object has the identity original overlap gauge. -/
theorem seam_label (R : RepairGroupoid T fixedRegion.vertices fixedRegion.edges) :
    (((NativeDescent.equivalence T fixedRegion fixed_faces leftRegion rightRegion regions_cover).functor.obj R).hom).1 =
      (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower overlap T)
        (ClosedRegion.nativeIntersection overlap fixedRegion).vertices
        (ClosedRegion.nativeIntersection overlap fixedRegion).edges)) :=
  NativeDescent.equivalence_seam_label T fixedRegion fixed_faces leftRegion rightRegion regions_cover R

end AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent
