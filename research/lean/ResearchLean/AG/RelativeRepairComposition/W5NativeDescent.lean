import ResearchLean.AG.RelativeRepairComposition.W5ActualArrows
import ResearchLean.AG.RelativeRepairComposition.W5RelativeCoefficients
import ResearchLean.AG.RelativeRepairComposition.NativeDescent

/-!
# Full B on the same original W5 tower and physical fixed inputs

The original shared edge is always correctable, with no candidates. The full
descent theorem uses this same original cover and physical P, retaining the
complete overlap isomorphism and every compatible original vertex label.
-/
namespace AAT.AG.RelativeRepairComposition.W5NativeDescent
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput W5Regions W5ActualRepairs W5LocalRepairs W5RelativeCoefficients
variable (b₁ b₂ : ZMod 2)
local notation "T" => originalTower b₁ b₂

/-- The full actual native homotopy pullback uses the same original tower, cover and physical P. -/
abbrev Descent := NativeDescent.Descent T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion

/-- Every whole actual local object is equivalent to the same original restricted native repair. -/
noncomputable def localObjectEquiv (U : ClosedRegion geometry) :
    SupportedRepair (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U fixedRegion).edges ≃
      LocalRepairs b₁ b₂ U :=
  NativeAffine.repairEquivalence (ClosedRegion.presentation U)
    (restrictOperations U (reference b₁ b₂)) (restrictOperations U (reference b₁ b₂))
    (fun f => comparison f.1) (restricted_faces U (reference b₁ b₂) (linear_faces b₁ b₂))
    (ClosedRegion.restrictedEdges U fixedRegion.edges)
/-- Whole local groupoids retain both inverse object maps and every full original label. -/
noncomputable def localAffineEquivalence (U : ClosedRegion geometry) :
    NativeDescent.LocalGroupoid T fixedRegion U ≌ LocalCategory b₁ b₂ U :=
  NativeAffine.groupoidEquivalence (ClosedRegion.presentation U)
    (restrictOperations U (reference b₁ b₂)) (restrictOperations U (reference b₁ b₂))
    (fun f => comparison f.1) (restricted_faces U (reference b₁ b₂) (linear_faces b₁ b₂))
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U fixedRegion.edges)
/-- The entire original native overlap groupoid has the same discrete F2 objects and all arrows. -/
noncomputable def nativeOverlapDiscreteEquivalence :
    NativeDescent.LocalGroupoid T fixedRegion overlap ≌ Discrete (ZMod 2) :=
  (localAffineEquivalence b₁ b₂ overlap).trans (W5ActualArrows.overlapDiscreteEquivalence b₁ b₂)

/-- The independently constructed local affine plan supplies the same full native local object. -/
noncomputable def nativeLocalPlan (side : Bool) : NativeDescent.LocalGroupoid T fixedRegion (region side) :=
  ((localObjectEquiv b₁ b₂ (region side)).symm (localPlan b₁ b₂ side) :
    NativeDescent.LocalGroupoid T fixedRegion (region side))
/-- Every physically permitted original native local gauge label is zero, derived from the fixed endpoints. -/
theorem native_local_label_zero (U : ClosedRegion geometry)
    (a : supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U fixedRegion).vertices
      (ClosedRegion.nativeIntersection U fixedRegion).edges) : a = 0 := by
  apply Subtype.ext
  funext v
  exact a.2.1 v (Set.mem_univ _)

/-- All original native repairs and compatible arrows satisfy B on this exact input. -/
noncomputable def nativeEquivalence : NativeCategory b₁ b₂ ≌ Descent b₁ b₂ :=
  NativeDescent.equivalence T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover

/-- Every original full affine object and arrow has the same full native descent groupoid. -/
noncomputable def actualEquivalence : ActualCategory b₁ b₂ ≌ Descent b₁ b₂ :=
  (wholeAffineEquivalence b₁ b₂).symm.trans (nativeEquivalence b₁ b₂)

/-- The whole original comma groupoid keeps all invertible compatible arrows. -/
theorem descent_is_groupoid : IsGroupoid (Descent b₁ b₂) :=
  NativeDescent.is_groupoid T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion

/-- Original descent keeps every original selected actual edge in U. -/
theorem left_choice (R : RepairGroupoid T fixedRegion.vertices fixedRegion.edges)
    {i j : leftRegion.vertices} (e : ClosedRegion.Edge leftRegion i j) :
    (((NativeDescent.equivalence T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover).functor.obj R).left).back.1.choice e =
      R.back.1.choice e.1 :=
  NativeDescent.equivalence_left_choice T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover R e

/-- Original descent keeps every original selected actual edge in V. -/
theorem right_choice (R : RepairGroupoid T fixedRegion.vertices fixedRegion.edges)
    {i j : rightRegion.vertices} (e : ClosedRegion.Edge rightRegion i j) :
    (((NativeDescent.equivalence T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover).functor.obj R).right).back.1.choice e =
      R.back.1.choice e.1 :=
  NativeDescent.equivalence_right_choice T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover R e

/-- Every original U arrow preserves its whole original vertex kernel label. -/
theorem left_label {R Q : RepairGroupoid T fixedRegion.vertices fixedRegion.edges}
    (b : R ⟶ Q) (v : leftRegion.vertices) :
    (((NativeDescent.equivalence T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover).functor.map b).left).1.toAdd.1 v =
      b.1.toAdd.1 v.1 :=
  NativeDescent.equivalence_left_map_value T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover b v

/-- Every original V arrow preserves its whole original vertex kernel label. -/
theorem right_label {R Q : RepairGroupoid T fixedRegion.vertices fixedRegion.edges}
    (b : R ⟶ Q) (v : rightRegion.vertices) :
    (((NativeDescent.equivalence T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover).functor.map b).right).1.toAdd.1 v =
      b.1.toAdd.1 v.1 :=
  NativeDescent.equivalence_right_map_value T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover b v

/-- The whole original forward object has the identity original overlap gauge. -/
theorem seam_label (R : RepairGroupoid T fixedRegion.vertices fixedRegion.edges) :
    (((NativeDescent.equivalence T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover).functor.obj R).hom).1 =
      (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower overlap T)
        (ClosedRegion.nativeIntersection overlap fixedRegion).vertices
        (ClosedRegion.nativeIntersection overlap fixedRegion).edges)) :=
  NativeDescent.equivalence_seam_label T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion regions_cover R

end AAT.AG.RelativeRepairComposition.W5NativeDescent
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5NativeDescent
