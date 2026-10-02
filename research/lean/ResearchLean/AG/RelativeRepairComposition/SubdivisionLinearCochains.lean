import ResearchLean.AG.RelativeRepairComposition.SubdivisionLinearCoefficients
import ResearchLean.AG.RelativeRepairComposition.SubdivisionCochainDecomposition

/-!
# Linear coordinates for the same full actual subdivision collapse

The linear maps retain the earlier actual cochain values and both inverse
restorations. The full fresh kernel remains an unrestricted factor.

## Implementation notes

Linearity is proved on the original named values. The previous additive
equivalences supply both inverse laws; no linear equivalence or preservation
certificate is provided as new input.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.LinearCochains
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)

include hlinear in
/-- The entire actual correction collapse is linear at every original complete edge name. -/
theorem collapse_smul (t : k) (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    collapseCorrection T chosen F (t • h) = t • collapseCorrection T chosen F h := by
  funext e
  by_cases he : e = chosen
  · subst e
    simp only [collapseCorrection_chosen,Pi.smul_apply]
    let a : T.toTower.localCoefficients.A chosen.2.1 := h (secondEdgeName K chosen)
    let r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) :=
      h (firstEdgeName K chosen)
    change t • a + rho2AddEquiv T chosen F (t • r) =
      t • (a + rho2AddEquiv T chosen F r)
    rw [LinearCoefficients.rho2_smul T chosen F hlinear,smul_add]
  · rw [collapseCorrection_old T chosen F _ e he]
    change t • h (oldEdgeName K chosen e he) = t • collapseCorrection T chosen F h e
    rw [collapseCorrection_old T chosen F _ e he]

/-- The full degree-one linear equivalence is the same actual collapse and full first value. -/
noncomputable def cochain1LinearEquiv : C1 (originalTower T chosen F).toTower.localCoefficients ≃ₗ[k]
    (C1 T.toTower.localCoefficients × (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) where
  toAddEquiv := cochain1Equiv T chosen F
  map_smul' t h := Prod.ext (collapse_smul T chosen F hlinear t h) rfl

/-- Its first coordinate is exactly the previous actual correction collapse. -/
theorem cochain1LinearEquiv_collapse (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain1LinearEquiv T chosen F hlinear h).1 = collapseCorrection T chosen F h := rfl

/-- Its second coordinate retains every arbitrary whole first-factor kernel value. -/
theorem cochain1LinearEquiv_first (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain1LinearEquiv T chosen F hlinear h).2 = h (firstEdgeName K chosen) := rfl

/-- Inverse linear coordinates restore all actual named corrections from the full old and fresh values. -/
theorem cochain1LinearEquiv_inverse (h : C1 T.toTower.localCoefficients)
    (r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    (cochain1LinearEquiv T chosen F hlinear).symm (h,r) = expandCorrection T chosen F h r := rfl

/-- Full degree-zero linear coordinates retain the old labels and the whole fresh displacement. -/
noncomputable def cochain0LinearEquiv : C0 (originalTower T chosen F).toTower.localCoefficients ≃ₗ[k]
    (C0 T.toTower.localCoefficients × (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) where
  toAddEquiv := cochain0Equiv T chosen F
  map_smul' t b := by
    apply Prod.ext
    · rfl
    · change t • b (.inr ()) - rho1AddEquiv T chosen F (t • b (.inl chosen.1)) =
        t • (b (.inr ()) - rho1AddEquiv T chosen F (b (.inl chosen.1)))
      rw [LinearCoefficients.rho1_smul,smul_sub]

/-- The first degree-zero coordinate is precisely the retained complete old label. -/
theorem cochain0LinearEquiv_old (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain0LinearEquiv (k := k) T chosen F b).1 = collapseVertex T chosen F b := rfl

/-- The full fresh degree-zero coordinate is its actual first-factor coboundary. -/
theorem cochain0LinearEquiv_fresh (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain0LinearEquiv (k := k) T chosen F b).2 =
      b (.inr ()) - rho1AddEquiv T chosen F (b (.inl chosen.1)) := rfl

/-- The inverse keeps all old labels and restores the complete shifted fresh label. -/
theorem cochain0LinearEquiv_inverse (b : C0 T.toTower.localCoefficients)
    (r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    (cochain0LinearEquiv (k := k) T chosen F).symm (b,r) =
      expandVertex T chosen F b (r + rho1AddEquiv T chosen F (b chosen.1)) := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.LinearCochains
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.LinearCochains
