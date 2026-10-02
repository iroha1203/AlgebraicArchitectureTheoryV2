import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalCorrections

/-!
# All local original vertex labels and their fresh displacement

## Implementation notes

Fresh displacement is read only when the chosen edge belongs to the region.
The original source label then exists by edge closure. No displacement is
manufactured by extending an excluded region globally. The independent new
relative label family keeps every original value and its actual fixed zero.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen) (U P : ClosedRegion K) (hp : chosen ∉ P.edges)

/-- Read every old local label, including all fixed original vertices. -/
noncomputable def collapseLocal0 :
    RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) →+
    RelativeCover.C0 T.toTower.localCoefficients U P where
  toFun b := ⟨fun v => b.1 ⟨.inl v.1,v.2⟩,fun v hv => b.2 ⟨.inl v.1,v.2⟩ hv⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Read the full fresh displacement only in a region containing the chosen edge. -/
noncomputable def displacementLocal0
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    localSupplement T chosen F U := by
  classical
  exact ⟨if hu : chosen ∈ U.edges then
    b.1 ⟨.inr (),hu⟩ - rho1AddEquiv T chosen F (b.1 ⟨.inl chosen.1,(U.edge_closed _ hu).1⟩)
    else 0,by intro hu; simp only [dif_neg hu]⟩

/-- In an included region displacement is the entire actual first coboundary coordinate. -/
theorem displacementLocal0_in
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) (hu : chosen ∈ U.edges) :
    (displacementLocal0 T chosen F U P b).1 =
      b.1 ⟨.inr (),hu⟩ - rho1AddEquiv T chosen F (b.1 ⟨.inl chosen.1,(U.edge_closed _ hu).1⟩) := by
  classical
  simp only [displacementLocal0,dif_pos hu]

/-- An excluded region has no fresh displacement. -/
theorem displacementLocal0_out
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) (hu : chosen ∉ U.edges) :
    (displacementLocal0 T chosen F U P b).1 = 0 :=
  localSupplement_zero T chosen F U hu _

/-- Restore every original local label and the arbitrary full fresh displacement. -/
noncomputable def expandLocal0
    (b : RelativeCover.C0 T.toTower.localCoefficients U P) (t : localSupplement T chosen F U) :
    RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) := by
  refine ⟨fun v => ?_,?_⟩
  · rcases v with ⟨v,hv⟩
    cases v with
    | inl v => exact b.1 ⟨v,hv⟩
    | inr _ => exact t.1 + rho1AddEquiv T chosen F (b.1 ⟨chosen.1,(U.edge_closed _ hv).1⟩)
  · rintro ⟨v,hv⟩ hf
    cases v with
    | inl v => exact b.2 ⟨v,hv⟩ hf
    | inr _ => exact False.elim (hp hf)

/-- Restoration keeps each full old local vertex label. -/
theorem expandLocal0_old
    (b : RelativeCover.C0 T.toTower.localCoefficients U P) (t : localSupplement T chosen F U)
    (v : U.vertices) :
    (expandLocal0 T chosen F U P hp b t).1 ⟨.inl v.1,v.2⟩ = b.1 v := rfl

/-- Restoration places displacement plus actual first transport at the fresh vertex. -/
theorem expandLocal0_fresh
    (b : RelativeCover.C0 T.toTower.localCoefficients U P) (t : localSupplement T chosen F U)
    (hu : chosen ∈ U.edges) :
    (expandLocal0 T chosen F U P hp b t).1 ⟨.inr (),hu⟩ =
      t.1 + rho1AddEquiv T chosen F (b.1 ⟨chosen.1,(U.edge_closed _ hu).1⟩) := rfl

/-- The independent new local label group is old labels paired with the complete supplement. -/
noncomputable def local0Equiv :
    RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) ≃+
    (RelativeCover.C0 T.toTower.localCoefficients U P × localSupplement T chosen F U) where
  toFun b := (collapseLocal0 T chosen F U P b,displacementLocal0 T chosen F U P b)
  invFun b := expandLocal0 T chosen F U P hp b.1 b.2
  left_inv b := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    cases v with
    | inl _ => rfl
    | inr u =>
      cases u
      change (displacementLocal0 T chosen F U P b).1 +
        rho1AddEquiv T chosen F (b.1 ⟨.inl chosen.1,(U.edge_closed _ hv).1⟩) = b.1 ⟨.inr (),hv⟩
      rw [displacementLocal0_in T chosen F U P b hv]
      exact sub_add_cancel _ _
  right_inv b := by
    apply Prod.ext
    · apply Subtype.ext; funext v; rfl
    · apply Subtype.ext
      by_cases hu : chosen ∈ U.edges
      · rw [displacementLocal0_in T chosen F U P _ hu]
        change (b.2.1 + rho1AddEquiv T chosen F (b.1.1 ⟨chosen.1,(U.edge_closed _ hu).1⟩)) -
          rho1AddEquiv T chosen F (b.1.1 ⟨chosen.1,(U.edge_closed _ hu).1⟩) = b.2.1
        exact add_sub_cancel_right _ _
      · rw [displacementLocal0_out T chosen F U P _ hu]
        exact (localSupplement_zero T chosen F U hu b.2).symm
  map_add' b c := by
    apply Prod.ext
    · exact map_add (collapseLocal0 T chosen F U P) b c
    · apply Subtype.ext
      change (displacementLocal0 T chosen F U P (b+c)).1 =
        (displacementLocal0 T chosen F U P b).1 + (displacementLocal0 T chosen F U P c).1
      by_cases hu : chosen ∈ U.edges
      · rw [displacementLocal0_in T chosen F U P (b+c) hu,
          displacementLocal0_in T chosen F U P b hu,displacementLocal0_in T chosen F U P c hu]
        change (b.1 ⟨.inr (),hu⟩ + c.1 ⟨.inr (),hu⟩) -
          rho1AddEquiv T chosen F
            (b.1 ⟨.inl chosen.1,(U.edge_closed _ hu).1⟩ + c.1 ⟨.inl chosen.1,(U.edge_closed _ hu).1⟩) = _
        rw [map_add]
        abel
      · rw [displacementLocal0_out T chosen F U P (b+c) hu,
          displacementLocal0_out T chosen F U P b hu,displacementLocal0_out T chosen F U P c hu]
        exact (add_zero _).symm

/-- The full original coordinate of the local label equivalence is literal restriction. -/
theorem local0Equiv_old
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) (v : U.vertices) :
    (local0Equiv T chosen F U P hp b).1.1 v = b.1 ⟨.inl v.1,v.2⟩ := rfl

/-- The entire supplemental coordinate is exactly the independently read displacement. -/
theorem local0Equiv_displacement
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    (local0Equiv T chosen F U P hp b).2 = displacementLocal0 T chosen F U P b := rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
