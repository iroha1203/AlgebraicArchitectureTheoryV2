import ResearchLean.AG.RelativeRepairComposition.SubdivisionOriginalTower
import ResearchLean.AG.RelativeRepairComposition.SupportedRepairs

/-!
# All full-kernel corrections before permissions

Collapse keeps every retained edge correction and replaces the selected edge
by the sum of the second correction and the actual transport of the first.
Restoration retains an arbitrary full first-factor value. Its second value is
uniquely forced by the chosen old correction.

## Implementation notes

The full first-factor correction is a free coordinate, and the second is forced by the old correction and actual second transport. Selecting only zero first correction would produce a section, but would not describe all independently given new repairs.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)

/-- The additive form of the generated full actual second-factor kernel transport. -/
noncomputable def rho2Add : Additive (Kernel p q F.middle) →+
    Additive (Kernel p q (T.original.object chosen.2.1)) where
  toFun a := Additive.ofMul ((rho2 T chosen F) (Additive.toMul a))
  map_zero' := by change Additive.ofMul ((rho2 T chosen F) 1) = 0; rw [map_one]; rfl
  map_add' a b := by
    change Additive.ofMul ((rho2 T chosen F) (Additive.toMul a * Additive.toMul b)) = _
    rw [map_mul]
    rfl

/-- Collapse every full new correction to its original named edge correction. -/
noncomputable def collapseCorrection
    (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    C1 T.toTower.localCoefficients := by
  classical
  exact fun e => if he : e = chosen then
    he.symm ▸ (let a : KernelCoefficient p q (T.original.object chosen.2.1) := h (secondEdgeName K chosen);
      a + (rho2Add T chosen F) (h (firstEdgeName K chosen)))
    else h (oldEdgeName K chosen e he)

/-- Restore all full new corrections from the old correction and an arbitrary first-factor value. -/
noncomputable def expandCorrection (h : C1 T.toTower.localCoefficients)
    (r : Additive (Kernel p q F.middle)) :
    C1 (originalTower T chosen F).toTower.localCoefficients :=
  fun e => edgeValue K chosen
    (fun j => (originalTower T chosen F).toTower.localCoefficients.A j)
    (fun {i j} e => h ⟨i,j,e⟩) r
      (let a : KernelCoefficient p q (T.original.object chosen.2.1) := h chosen
       a - (rho2Add T chosen F) r) e.2.2

/-- Collapse has exactly the full actual two-factor sum at the selected complete name. -/
theorem collapseCorrection_chosen
    (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    collapseCorrection T chosen F h chosen =
      (let a : KernelCoefficient p q (T.original.object chosen.2.1) := h (secondEdgeName K chosen)
       a + (rho2Add T chosen F) (h (firstEdgeName K chosen))) := by
  classical
  simp [collapseCorrection]

/-- Collapse retains the full original correction at every other complete named edge. -/
theorem collapseCorrection_old
    (h : C1 (originalTower T chosen F).toTower.localCoefficients)
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    collapseCorrection T chosen F h e = h (oldEdgeName K chosen e he) := by
  classical
  simp only [collapseCorrection,dif_neg he]

/-- Restoration retains every arbitrary full old correction at each retained complete name. -/
theorem expandCorrection_old (h : C1 T.toTower.localCoefficients)
    (r : Additive (Kernel p q F.middle)) (e : EdgeName (K := K)) (he : e ≠ chosen) :
    expandCorrection T chosen F h r (oldEdgeName K chosen e he) = h e := by
  exact edgeValue_old K chosen _ _ _ _ e he

/-- The first restored factor has exactly the arbitrary supplied full value. -/
theorem expandCorrection_first (h : C1 T.toTower.localCoefficients)
    (r : Additive (Kernel p q F.middle)) :
    expandCorrection T chosen F h r (firstEdgeName K chosen) = r := by
  exact edgeValue_first K chosen _ _ _ _

/-- The second restored factor has the unique full value forced by the old correction and the first factor. -/
theorem expandCorrection_second (h : C1 T.toTower.localCoefficients)
    (r : Additive (Kernel p q F.middle)) :
    expandCorrection T chosen F h r (secondEdgeName K chosen) =
      (let a : KernelCoefficient p q (T.original.object chosen.2.1) := h chosen
       a - (rho2Add T chosen F) r) := by
  exact edgeValue_second K chosen _ _ _ _

/-- All old full correction values are recovered after restoration with any first-factor value. -/
theorem collapse_expand (h : C1 T.toTower.localCoefficients)
    (r : Additive (Kernel p q F.middle)) :
    collapseCorrection T chosen F (expandCorrection T chosen F h r) = h := by
  classical
  funext e
  by_cases he : e = chosen
  · subst e
    rw [collapseCorrection_chosen,expandCorrection_first,expandCorrection_second]
    exact sub_add_cancel _ _
  · rw [collapseCorrection_old T chosen F _ e he,expandCorrection_old]

/-- Every full new correction is restored by its collapsed old correction and its actual first value. -/
theorem expand_collapse (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    expandCorrection T chosen F (collapseCorrection T chosen F h) (h (firstEdgeName K chosen)) = h := by
  funext e
  rcases e with ⟨i,j,e⟩
  apply edge_induction chosen _ _ _ _ e
  · intro e he
    change expandCorrection T chosen F (collapseCorrection T chosen F h)
      (h (firstEdgeName K chosen)) (oldEdgeName K chosen e he) = h (oldEdgeName K chosen e he)
    rw [expandCorrection_old,collapseCorrection_old]
  · change expandCorrection T chosen F (collapseCorrection T chosen F h)
      (h (firstEdgeName K chosen)) (firstEdgeName K chosen) = h (firstEdgeName K chosen)
    rw [expandCorrection_first]
  · change expandCorrection T chosen F (collapseCorrection T chosen F h)
      (h (firstEdgeName K chosen)) (secondEdgeName K chosen) = h (secondEdgeName K chosen)
    rw [expandCorrection_second,collapseCorrection_chosen]
    exact add_sub_cancel_right _ _

/-- The full new correction space is exactly all old corrections paired with the full new-object kernel. -/
noncomputable def correctionEquiv :
    C1 (originalTower T chosen F).toTower.localCoefficients ≃
      C1 T.toTower.localCoefficients × Additive (Kernel p q F.middle) where
  toFun h := ⟨collapseCorrection T chosen F h,h (firstEdgeName K chosen)⟩
  invFun h := expandCorrection T chosen F h.1 h.2
  left_inv := expand_collapse T chosen F
  right_inv h := Prod.ext (collapse_expand T chosen F h.1 h.2) (expandCorrection_first T chosen F h.1 h.2)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
