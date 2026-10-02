import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalDifferentials

/-!
# Every local equation solution and every original label action

## Implementation notes

The two solution sets use their independently defined local differentials.
The comparison is restricted only after the full local cochain equivalence
and its differential identity have been proved. The supplement remains the
entire allowed fresh kernel. The signed actual defect is compared separately
from an arbitrary right-hand side. No section or generated relation is copied.
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

/-- The independently defined new equation holds exactly for the collapsed old equation. -/
theorem local_equation_iff
    (rhs : RelativeCover.C2 T.toTower.localCoefficients U P)
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    RelativeCover.d1 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) h =
      (local2Equiv T chosen F U P).symm rhs ↔
    RelativeCover.d1 T.toTower.localCoefficients U P (local1Equiv T chosen F U P hp h).1 = rhs := by
  constructor
  · intro hh
    have hv := congrArg (local2Equiv T chosen F U P) hh
    rwa [local_d1,AddEquiv.apply_symm_apply] at hv
  · intro hh
    apply (local2Equiv T chosen F U P).injective
    rw [local_d1,AddEquiv.apply_symm_apply]
    exact hh

/-- All independently given local solutions, with all fresh freedom and both inverse laws. -/
noncomputable def localEquationEquiv (rhs : RelativeCover.C2 T.toTower.localCoefficients U P) :
    {h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) //
      RelativeCover.d1 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) h =
        (local2Equiv T chosen F U P).symm rhs} ≃
    ({h : RelativeCover.C1 T.toTower.localCoefficients U P //
      RelativeCover.d1 T.toTower.localCoefficients U P h = rhs} × localSupplement T chosen F U) where
  toFun h := (⟨(local1Equiv T chosen F U P hp h.1).1,
    (local_equation_iff T chosen F U P hp rhs h.1).mp h.2⟩,
    (local1Equiv T chosen F U P hp h.1).2)
  invFun h := ⟨(local1Equiv T chosen F U P hp).symm (h.1.1,h.2),by
    apply (local_equation_iff T chosen F U P hp rhs _).mpr
    rw [AddEquiv.apply_symm_apply]
    exact h.1.2⟩
  left_inv h := Subtype.ext ((local1Equiv T chosen F U P hp).symm_apply_apply h.1)
  right_inv h := by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      exact congrArg Prod.fst ((local1Equiv T chosen F U P hp).apply_symm_apply (h.1.1,h.2))
    · change (local1Equiv T chosen F U P hp
        ((local1Equiv T chosen F U P hp).symm (h.1.1,h.2))).2 = h.2
      exact congrArg Prod.snd ((local1Equiv T chosen F U P hp).apply_symm_apply (h.1.1,h.2))

/-- The full local equation comparison reads the same old correction and full fresh coordinate. -/
theorem localEquationEquiv_coordinates (rhs : RelativeCover.C2 T.toTower.localCoefficients U P)
    (h : {h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) //
      RelativeCover.d1 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) h =
        (local2Equiv T chosen F U P).symm rhs}) :
    ((localEquationEquiv T chosen F U P hp rhs h).1.1,
      (localEquationEquiv T chosen F U P hp rhs h).2) =
    local1Equiv T chosen F U P hp h.1 := rfl

/-- Every supplied old solution and every supplemental value are recovered after restoration. -/
theorem localEquationEquiv_inverse_coordinates (rhs : RelativeCover.C2 T.toTower.localCoefficients U P)
    (h : {h : RelativeCover.C1 T.toTower.localCoefficients U P //
      RelativeCover.d1 T.toTower.localCoefficients U P h = rhs}) (r : localSupplement T chosen F U) :
    local1Equiv T chosen F U P hp ((localEquationEquiv T chosen F U P hp rhs).symm (h,r)).1 =
      (h.1,r) := (local1Equiv T chosen F U P hp).apply_symm_apply _

/-- Every full original label acts by old d0 and translation of the entire supplement. -/
theorem local_label_action
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P))
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local1Equiv T chosen F U P hp
      (h + RelativeCover.d0 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) b) =
    ((local1Equiv T chosen F U P hp h).1 +
      RelativeCover.d0 T.toTower.localCoefficients U P (local0Equiv T chosen F U P hp b).1,
      (local1Equiv T chosen F U P hp h).2 + (local0Equiv T chosen F U P hp b).2) := by
  rw [map_add,local_d0]
  rfl

/-- The signed actual defect equation holds on exactly the same complete local faces. -/
theorem local_actual_equation_iff
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    (∀ f : U.faces,
      (RelativeCover.d1 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) h).1 f =
        -((originalTower T chosen F).toTower.defect f.1)) ↔
    (∀ f : U.faces,
      (RelativeCover.d1 T.toTower.localCoefficients U P
        (local1Equiv T chosen F U P hp h).1).1 f = -(T.toTower.defect f.1)) := by
  have hd := local_d1 T chosen F U P hp h
  constructor
  · intro hh f
    have hv := congrArg (fun c : RelativeCover.C2 T.toTower.localCoefficients U P => c.1 f) hd
    exact hv.symm.trans ((hh f).trans (local_rhs T chosen F U f))
  · intro hh f
    have hv := congrArg (fun c : RelativeCover.C2 T.toTower.localCoefficients U P => c.1 f) hd
    exact hv.trans ((hh f).trans (local_rhs T chosen F U f).symm)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
