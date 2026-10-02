import ResearchLean.AG.RelativeRepairComposition.LocalizedRelativeFamilies
import ResearchLean.AG.RelativeRepairComposition.SubdivisionCochainDecomposition
import ResearchLean.AG.RelativeRepairComposition.SubdivisionClosedCovers
import ResearchLean.AG.RelativeRepairComposition.RelativeCoverComplex

/-!
# Every local correction and the full supplemental factor

## Implementation notes

The two local relative families are independently defined on their actual
closed regions. Degreewise zero extension exposes the global correction map.
An excluded chosen edge forces both factors to zero. An included chosen edge
retains every full first-factor correction; the second is forced by the same
actual transported sum. No global extension chain-map property is used.
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

/-- The whole fresh kernel when chosen is local, and the zero subgroup otherwise. -/
def localSupplement : AddSubgroup ((originalTower T chosen F).toTower.localCoefficients.A (.inr ())) where
  carrier := {r | chosen ∉ U.edges → r = 0}
  zero_mem' := fun _ => rfl
  add_mem' := by intro r s hr hs hn; rw [hr hn,hs hn,add_zero]
  neg_mem' := by intro r hr hn; rw [hr hn,neg_zero]

/-- Supplemental membership uses only the original region incidence. -/
theorem mem_localSupplement (r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    r ∈ localSupplement T chosen F U ↔ (chosen ∉ U.edges → r = 0) := Iff.rfl

/-- Any full fresh value is allowed when the original chosen edge is local. -/
theorem localSupplement_full (hu : chosen ∈ U.edges)
    (r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    r ∈ localSupplement T chosen F U := fun hn => False.elim (hn hu)

/-- Every supplemental value is zero in a region excluding the chosen edge. -/
theorem localSupplement_zero (hu : chosen ∉ U.edges) (r : localSupplement T chosen F U) :
    r.1 = 0 := r.2 hu

/-- Collapse of a localized correction keeps all original local and fixed zero conditions. -/
noncomputable def collapseLocalized1
    (h : Family.localized (fun e : EdgeName (K := presentation K chosen) =>
      (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
      (expandedRegion K chosen U).edges (expandedRegion K chosen P).edges) :
    Family.localized (fun e : EdgeName (K := K) => T.toTower.localCoefficients.A e.2.1)
      U.edges P.edges := ⟨collapseCorrection T chosen F h.1,by
    intro e hi
    by_cases he : e = chosen
    · subst e
      have hu : chosen ∉ U.edges := by
        rcases hi with hu | hf
        · exact hu
        · exact False.elim (hp hf)
      rw [collapseCorrection_chosen]
      have h1 := Family.localized_zero _ h (firstEdgeName K chosen) (Or.inl hu)
      have h2 := Family.localized_zero _ h (secondEdgeName K chosen) (Or.inl hu)
      rw [h1,h2,map_zero,add_zero]
    · rw [collapseCorrection_old T chosen F _ e he]
      exact Family.localized_zero _ h (oldEdgeName K chosen e he) hi⟩

/-- The first actual factor value satisfies precisely the local supplemental condition. -/
def firstLocalized1
    (h : Family.localized (fun e : EdgeName (K := presentation K chosen) =>
      (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
      (expandedRegion K chosen U).edges (expandedRegion K chosen P).edges) :
    localSupplement T chosen F U :=
  ⟨h.1 (firstEdgeName K chosen),fun hu => Family.localized_zero _ h _ (Or.inl hu)⟩

/-- Restore the complete independently defined new localized correction. -/
noncomputable def expandLocalized1
    (h : Family.localized (fun e : EdgeName (K := K) => T.toTower.localCoefficients.A e.2.1)
      U.edges P.edges) (r : localSupplement T chosen F U) :
    Family.localized (fun e : EdgeName (K := presentation K chosen) =>
      (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
      (expandedRegion K chosen U).edges (expandedRegion K chosen P).edges :=
  ⟨expandCorrection T chosen F h.1 r.1,by
    intro e hi
    obtain ⟨n,rfl⟩ := (edgeNameEquiv K chosen).symm.surjective e
    cases n with
    | inl e =>
      change expandCorrection T chosen F h.1 r.1 (oldEdgeName K chosen e.1 e.2) = 0
      rw [expandCorrection_old]
      exact Family.localized_zero _ h e.1 hi
    | inr b =>
      have hu : chosen ∉ U.edges := by
        rcases hi with hu | hf
        · exact hu
        · exact False.elim (hp hf)
      cases b
      · change expandCorrection T chosen F h.1 r.1 (firstEdgeName K chosen) = 0
        rw [expandCorrection_first]; exact r.2 hu
      · change expandCorrection T chosen F h.1 r.1 (secondEdgeName K chosen) = 0
        rw [expandCorrection_second,Family.localized_zero _ h chosen (Or.inl hu),r.2 hu,map_zero,sub_zero]⟩

/-- The full localized correction splits into old correction and every allowed fresh value. -/
noncomputable def localized1Equiv :
    Family.localized (fun e : EdgeName (K := presentation K chosen) =>
      (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
      (expandedRegion K chosen U).edges (expandedRegion K chosen P).edges ≃+
    (Family.localized (fun e : EdgeName (K := K) => T.toTower.localCoefficients.A e.2.1)
      U.edges P.edges × localSupplement T chosen F U) where
  toFun h := (collapseLocalized1 T chosen F U P hp h,firstLocalized1 T chosen F U P h)
  invFun h := expandLocalized1 T chosen F U P hp h.1 h.2
  left_inv h := Subtype.ext (expand_collapse T chosen F h.1)
  right_inv h := Prod.ext (Subtype.ext (collapse_expand T chosen F h.1.1 h.2.1))
    (Subtype.ext (expandCorrection_first T chosen F h.1.1 h.2.1))
  map_add' h k := Prod.ext (Subtype.ext (collapseCorrection_add T chosen F h.1 k.1))
    (Subtype.ext rfl)

/-- All independently generated local relative corrections, with the entire factor freedom. -/
noncomputable def local1Equiv :
    RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) ≃+
    (RelativeCover.C1 T.toTower.localCoefficients U P × localSupplement T chosen F U) :=
  (Family.localizedEquiv _ _ _).trans ((localized1Equiv T chosen F U P hp).trans
    (AddEquiv.prodCongr (Family.localizedEquiv _ _ _).symm (AddEquiv.refl _)))

/-- The old local coordinate is the same actual collapse of the zero-extended new family. -/
theorem local1Equiv_old
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) (e : U.edges) :
    (local1Equiv T chosen F U P hp h).1.1 e =
      collapseCorrection T chosen F
        (Family.extend _ (expandedRegion K chosen U).edges h.1) e.1 := rfl

/-- The supplemental coordinate is the complete first-factor value of degreewise extension. -/
theorem local1Equiv_first
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    (local1Equiv T chosen F U P hp h).2.1 =
      Family.extend (fun e : EdgeName (K := presentation K chosen) =>
        (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
        (expandedRegion K chosen U).edges h.1 (firstEdgeName K chosen) := rfl

/-- The entire old zero extension is the same actual collapsed new zero extension. -/
theorem local1Equiv_extend
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    Family.extend (fun e : EdgeName (K := K) => T.toTower.localCoefficients.A e.2.1)
      U.edges (local1Equiv T chosen F U P hp h).1.1 =
    collapseCorrection T chosen F
      (Family.extend _ (expandedRegion K chosen U).edges h.1) :=
  congrArg Subtype.val ((Family.localizedEquiv _ U.edges P.edges).apply_symm_apply
    (collapseLocalized1 T chosen F U P hp (Family.localizedEquiv _ _ _ h)))

/-- Every retained local value is unchanged by the comparison. -/
theorem local1Equiv_retained
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P))
    (e : U.edges) (he : e.1 ≠ chosen) :
    (local1Equiv T chosen F U P hp h).1.1 e =
      h.1 ⟨oldEdgeName K chosen e.1 he,e.2⟩ := by
  rw [local1Equiv_old,collapseCorrection_old T chosen F _ e.1 he]
  exact Family.extend_on (fun e : EdgeName (K := presentation K chosen) =>
    (originalTower T chosen F).toTower.localCoefficients.A e.2.1) _ _ _ e.2

/-- The chosen local coordinate is the full actual transported sum of both factors. -/
theorem local1Equiv_chosen
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) (hu : chosen ∈ U.edges) :
    (local1Equiv T chosen F U P hp h).1.1 ⟨chosen,hu⟩ =
      (let a : KernelCoefficient p q (T.original.object chosen.2.1) := h.1 ⟨secondEdgeName K chosen,hu⟩
       a + rho2Add T chosen F (h.1 ⟨firstEdgeName K chosen,hu⟩)) := by
  rw [local1Equiv_old,collapseCorrection_chosen]
  dsimp only
  rw [Family.extend_on (fun e : EdgeName (K := presentation K chosen) =>
      (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
      (expandedRegion K chosen U).edges h.1 (secondEdgeName K chosen) hu,
    Family.extend_on (fun e : EdgeName (K := presentation K chosen) =>
      (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
      (expandedRegion K chosen U).edges h.1 (firstEdgeName K chosen) hu]

/-- Every arbitrary old retained correction survives restoration. -/
theorem local1Equiv_inverse_old
    (h : RelativeCover.C1 T.toTower.localCoefficients U P) (r : localSupplement T chosen F U)
    (e : U.edges) (he : e.1 ≠ chosen) :
    ((local1Equiv T chosen F U P hp).symm (h,r)).1 ⟨oldEdgeName K chosen e.1 he,e.2⟩ = h.1 e := by
  change expandCorrection T chosen F (Family.extend _ U.edges h.1) r.1
    (oldEdgeName K chosen e.1 he) = h.1 e
  rw [expandCorrection_old]
  exact Family.extend_on _ _ _ _ e.2

/-- The first restored local factor keeps every arbitrary full supplemental value. -/
theorem local1Equiv_inverse_first
    (h : RelativeCover.C1 T.toTower.localCoefficients U P) (r : localSupplement T chosen F U)
    (hu : chosen ∈ U.edges) :
    ((local1Equiv T chosen F U P hp).symm (h,r)).1 ⟨firstEdgeName K chosen,hu⟩ = r.1 :=
  expandCorrection_first T chosen F (Family.extend _ U.edges h.1) r.1

/-- The second restored local factor is forced by the same old correction and actual transport. -/
theorem local1Equiv_inverse_second
    (h : RelativeCover.C1 T.toTower.localCoefficients U P) (r : localSupplement T chosen F U)
    (hu : chosen ∈ U.edges) :
    ((local1Equiv T chosen F U P hp).symm (h,r)).1 ⟨secondEdgeName K chosen,hu⟩ =
      (let a : KernelCoefficient p q (T.original.object chosen.2.1) := h.1 ⟨chosen,hu⟩
       a - rho2Add T chosen F r.1) := by
  change expandCorrection T chosen F (Family.extend _ U.edges h.1) r.1
    (secondEdgeName K chosen) = _
  rw [expandCorrection_second,Family.extend_on _ _ _ _ hu]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
