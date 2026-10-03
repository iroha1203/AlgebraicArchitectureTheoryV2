import ResearchLean.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors

/-! # Complete unrestricted W3 patch equivalences

Every full reference arrow is retained, and every independent local repair
is reached by an actual original-vertex gauge. Thus each original one-edge
patch is BA as a whole category, for either loop transport.
-/
namespace AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalEquivalences
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
open W3LocalRepairs W3LocalLabels W3LocalFullLabels W3LocalGauge W3EmptyGroupoids
open W3UnrestrictedLocalFunctors
attribute [local instance] localAction

/-- All actual unrestricted U objects and full original arrows form the entire BA category. -/
noncomputable def leftEquivalence (sheared : Bool) : BA ≌ LocalCategory sheared leftRegion candidates := by
  let F := leftFunctor sheared
  letI : F.Full := {
    map_surjective := by
      intro R Q f
      refine ⟨Multiplicative.ofAdd (f.1.toAdd.1 leftS), ?_⟩
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (leftFullLabelEquiv sheared).injective
      exact Prod.ext rfl (left_reference_labels sheared f).symm }
  letI : F.Faithful := {
    map_injective := by
      intro R Q f g h
      exact Multiplicative.toAdd.injective (congrArg (fun k => k.1.toAdd.1 leftS) h) }
  letI : F.EssSurj := {
    mem_essImage := by
      intro R
      let b := freeLabel sheared leftRegion 0 (R.back.operation leftEdge.2.2 0)
      have hb : b +ᵥ (leftReference sheared).back = R.back := by
        apply (left_gauge_eq sheared candidates b _ _).mpr
        change (localReferenceRepair sheared leftRegion candidates).operation leftEdge.2.2 0 +
          (freeLabel sheared leftRegion 0 (R.back.operation leftEdge.2.2 0)).1 leftT -
            (freeLabel sheared leftRegion 0 (R.back.operation leftEdge.2.2 0)).1 leftS =
              R.back.operation leftEdge.2.2 0
        rw [local_reference_zero,left_source,left_target]
        simp
      refine ⟨SingleObj.star (Multiplicative A), ⟨?_⟩⟩
      exact (Groupoid.isoEquivHom (F.obj (SingleObj.star (Multiplicative A))) R).symm
        ⟨Multiplicative.ofAdd b,hb⟩ }
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-- All actual unrestricted V objects and full original arrows form the entire BA category with full T. -/
noncomputable def rightEquivalence (sheared : Bool) : BA ≌ LocalCategory sheared rightRegion candidates := by
  let F := rightFunctor sheared
  letI : F.Full := {
    map_surjective := by
      intro R Q f
      refine ⟨Multiplicative.ofAdd (f.1.toAdd.1 rightT), ?_⟩
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (rightFullLabelEquiv sheared).injective
      exact Prod.ext (right_reference_labels sheared f).symm rfl }
  letI : F.Faithful := {
    map_injective := by
      intro R Q f g h
      exact Multiplicative.toAdd.injective (congrArg (fun k => k.1.toAdd.1 rightT) h) }
  letI : F.EssSurj := {
    mem_essImage := by
      intro R
      let b := freeLabel sheared rightRegion (R.back.operation rightEdge.2.2 0) 0
      have hb : b +ᵥ (rightReference sheared).back = R.back := by
        apply (right_gauge_eq sheared candidates b _ _).mpr
        change (localReferenceRepair sheared rightRegion candidates).operation rightEdge.2.2 0 +
          (freeLabel sheared rightRegion (R.back.operation rightEdge.2.2 0) 0).1 rightS -
            linearAction sheared ((freeLabel sheared rightRegion (R.back.operation rightEdge.2.2 0) 0).1 rightT) =
              R.back.operation rightEdge.2.2 0
        rw [local_reference_zero,right_source,right_target,(linearAction sheared).map_zero]
        simp
      refine ⟨SingleObj.star (Multiplicative A), ⟨?_⟩⟩
      exact (Groupoid.isoEquivHom (F.obj (SingleObj.star (Multiplicative A))) R).symm
        ⟨Multiplicative.ofAdd b,hb⟩ }
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

end AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalEquivalences
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalEquivalences
