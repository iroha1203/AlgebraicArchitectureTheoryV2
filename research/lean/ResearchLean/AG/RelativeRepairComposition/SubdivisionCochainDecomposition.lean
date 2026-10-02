import ResearchLean.AG.RelativeRepairComposition.SubdivisionCoefficientPaths

/-!
# The full additive degree-zero and degree-one subdivision coordinates

Degree one is the old correction paired with the entire first-factor kernel.
Degree zero is the old vertex label paired with its fresh displacement from
actual first-factor transport. In these coordinates d0 is old d0 paired with
identity on the full intermediate kernel, and d1 forgets only that free factor.

## Implementation notes

The fresh degree-zero coordinate is b_w minus rho1(b_source), because the actual
first-factor coboundary is exactly this value. Using b_w alone would leave an
extra old-label term in the supplemental differential. The degree-one map is
precisely the accepted actual correction collapse, with arbitrary first value;
it does not choose a section or omit independently given cochains.
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

/-- The same full actual correction collapse as an additive homomorphism. -/
noncomputable def collapseC1Hom : C1 (originalTower T chosen F).toTower.localCoefficients →+
    C1 T.toTower.localCoefficients :=
  AddMonoidHom.mk' (collapseCorrection T chosen F) (collapseCorrection_add T chosen F)

/-- Every original named value of the additive map is the actual correction collapse value. -/
theorem collapseC1Hom_apply (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    collapseC1Hom T chosen F h = collapseCorrection T chosen F h := rfl

/-- Full degree one splits by the same actual collapse and the unrestricted first-factor value. -/
noncomputable def cochain1Equiv : C1 (originalTower T chosen F).toTower.localCoefficients ≃+
    (C1 T.toTower.localCoefficients × (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :=
  { correctionEquiv T chosen F with
    map_add' h k := Prod.ext (collapseCorrection_add T chosen F h k) rfl }

/-- The first coordinate is literally the original actual collapse. -/
theorem cochain1Equiv_collapse (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain1Equiv T chosen F h).1 = collapseCorrection T chosen F h := rfl

/-- The second coordinate keeps the complete actual first-factor correction. -/
theorem cochain1Equiv_first (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain1Equiv T chosen F h).2 = h (firstEdgeName K chosen) := rfl

/-- The inverse is the actual restoration with an arbitrary full first-factor value. -/
theorem cochain1Equiv_inverse (h : C1 T.toTower.localCoefficients)
    (r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    (cochain1Equiv T chosen F).symm (h,r) = expandCorrection T chosen F h r := rfl

/-- Full degree zero splits by old labels and their actual fresh first-factor coboundary. -/
noncomputable def cochain0Equiv : C0 (originalTower T chosen F).toTower.localCoefficients ≃+
    (C0 T.toTower.localCoefficients × (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) where
  toFun b := ⟨collapseVertex T chosen F b,
    b (.inr ()) - rho1AddEquiv T chosen F (b (.inl chosen.1))⟩
  invFun b := expandVertex T chosen F b.1 (b.2 + rho1AddEquiv T chosen F (b.1 chosen.1))
  left_inv b := by
    funext v
    cases v with
    | inl _ => rfl
    | inr u =>
      cases u
      change (b (.inr ()) - rho1AddEquiv T chosen F (b (.inl chosen.1))) +
        rho1AddEquiv T chosen F (b (.inl chosen.1)) = b (.inr ())
      exact sub_add_cancel _ _
  right_inv b := by
    apply Prod.ext
    · rfl
    · change (b.2 + rho1AddEquiv T chosen F (b.1 chosen.1)) -
        rho1AddEquiv T chosen F (b.1 chosen.1) = b.2
      exact add_sub_cancel_right _ _
  map_add' b c := by
    apply Prod.ext
    · rfl
    · let bs : T.toTower.localCoefficients.A chosen.1 := b (.inl chosen.1)
      let cs : T.toTower.localCoefficients.A chosen.1 := c (.inl chosen.1)
      change (b (.inr ()) + c (.inr ())) - rho1AddEquiv T chosen F (bs + cs) =
        (b (.inr ()) - rho1AddEquiv T chosen F bs) +
          (c (.inr ()) - rho1AddEquiv T chosen F cs)
      rw [map_add]
      abel

/-- The entire old vertex label is unchanged by the degree-zero coordinate map. -/
theorem cochain0Equiv_old (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain0Equiv T chosen F b).1 = collapseVertex T chosen F b := rfl

/-- The fresh coordinate is the full first-factor coboundary value. -/
theorem cochain0Equiv_fresh (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    (cochain0Equiv T chosen F b).2 =
      b (.inr ()) - rho1AddEquiv T chosen F (b (.inl chosen.1)) := rfl

/-- Inverse degree-zero coordinates restore every old label and the forced shifted fresh value. -/
theorem cochain0Equiv_inverse (b : C0 T.toTower.localCoefficients)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    (cochain0Equiv T chosen F).symm (b,t) =
      expandVertex T chosen F b (t + rho1AddEquiv T chosen F (b chosen.1)) := rfl

/-- The actual first-factor coboundary is precisely the full supplemental degree-zero coordinate. -/
theorem d0_first (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    d0 (originalTower T chosen F).toTower.localCoefficients b (firstEdgeName K chosen) =
      (cochain0Equiv T chosen F b).2 := by
  change b (.inr ()) -
    (originalTower T chosen F).toTower.localCoefficients.edge (firstEdge K chosen)
      (b (.inl chosen.1)) = _
  rw [coefficient_edge_first]
  rfl

/-- The original vertex differential splits into old d0 and the identity of the entire new-object kernel. -/
theorem cochain1Equiv_d0 (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    cochain1Equiv T chosen F (d0 (originalTower T chosen F).toTower.localCoefficients b) =
      (d0 T.toTower.localCoefficients (cochain0Equiv T chosen F b).1,
        (cochain0Equiv T chosen F b).2) :=
  Prod.ext (collapse_d0 T chosen F b) (d0_first T chosen F b)

/-- The full original face differential reads the same old collapse coordinate and no fresh coordinate. -/
theorem cochain1Equiv_d1 (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    d1 (originalTower T chosen F).toTower.localCoefficients h =
      d1 T.toTower.localCoefficients (cochain1Equiv T chosen F h).1 :=
  d1_collapse T chosen F h

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
