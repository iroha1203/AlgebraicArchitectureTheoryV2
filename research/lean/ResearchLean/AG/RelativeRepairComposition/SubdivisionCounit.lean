import ResearchLean.AG.RelativeRepairComposition.SubdivisionExpandFunctor

/-!
# Actual natural comparison with the freely varying new vertex

The canonical restored repair is reidentified with the actual repair by zero
labels at every old vertex and its full first-factor correction at the fresh
vertex. This is an actual invertible arrow in the repair groupoid.

## Implementation notes

The comparison uses the actual first correction as its fresh label and zero at every old vertex. Its inverse is constructed with the negative full label, rather than leaving invertibility to implicit instance search; this also exposes all strict shared values.
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
variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))

/-- The comparison has zero old labels and the entire actual first correction at the fresh vertex. -/
noncomputable def counitLabel
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) :=
  expandAllowedLabel T chosen F vertices fixed 0 (firstCorrection T chosen F R.1)

/-- Every original vertex comparison label is zero. -/
theorem counitLabel_old
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) (v : K.Vertex) :
    (counitLabel T chosen F vertices fixed R).1 (.inl v) = 0 := rfl

/-- The full fresh comparison label is exactly the actual first-factor correction. -/
theorem counitLabel_fresh
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    (counitLabel T chosen F vertices fixed R).1 (.inr ()) = firstCorrection T chosen F R.1 := rfl

variable (hchosen : chosen ∉ fixed)

/-- This comparison is an actual gauge from the restored collapsed repair to the original actual repair. -/
theorem counitLabel_gauge
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    repairGauge (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)
      (counitLabel T chosen F vertices fixed R)
      (expandSupported T chosen F fixed (collapseSupported T chosen F fixed hchosen R) 0) = R := by
  apply (gauge_equation_iff T chosen F vertices fixed hchosen _ _ _).mpr
  constructor
  · change repairGauge T vertices fixed
      (collapseAllowedLabel T chosen F vertices fixed hchosen
        (expandAllowedLabel T chosen F vertices fixed 0 (firstCorrection T chosen F R.1)))
      (collapseSupported T chosen F fixed hchosen
        (expandSupported T chosen F fixed (collapseSupported T chosen F fixed hchosen R) 0)) = _
    rw [collapse_expand_allowed,collapse_expand_supported]
    exact Subtype.ext (T.vertexGauge_zero (collapseSupported T chosen F fixed hchosen R).1)
  · change firstCorrection T chosen F R.1 =
      firstCorrection T chosen F (expandSupported T chosen F fixed
        (collapseSupported T chosen F fixed hchosen R) 0).1 +
      ((counitLabel T chosen F vertices fixed R).1 (.inr ()) -
        rho1AddEquiv T chosen F ((counitLabel T chosen F vertices fixed R).1 (.inl chosen.1)))
    rw [firstCorrection_expandSupported,counitLabel_fresh,counitLabel_old,map_zero,sub_zero,zero_add]

/-- The actual groupoid counit arrow restores the original freely varying fresh vertex. -/
noncomputable def counitHom
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    ((collapseFunctor T chosen F vertices fixed hchosen) ⋙
      (expandFunctor T chosen F vertices fixed hchosen)).obj R ⟶ R :=
  ⟨Multiplicative.ofAdd (counitLabel T chosen F vertices fixed R.back),
    counitLabel_gauge T chosen F vertices fixed hchosen R.back⟩

/-- The actual counit morphism has zero comparison at each original vertex. -/
theorem counitHom_label_old
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (v : K.Vertex) :
    (Multiplicative.toAdd (counitHom T chosen F vertices fixed hchosen R).1).1 (.inl v) = 0 := rfl

/-- The actual counit morphism has full first-factor correction as its fresh-vertex label. -/
theorem counitHom_label_fresh
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    (Multiplicative.toAdd (counitHom T chosen F vertices fixed hchosen R).1).1 (.inr ()) =
      firstCorrection T chosen F R.back.1 := rfl

/-- Collapse of the counit preserves all old vertices with the identity original label. -/
theorem collapse_counit_label
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
      (counitHom T chosen F vertices fixed hchosen R)).1 = 0 :=
  collapse_expand_allowed T chosen F vertices fixed hchosen 0 _

/-- The actual counit is natural for every full original morphism, using the bijection on all native Hom sets. -/
theorem counit_naturality
    {R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)}
    (f : R ⟶ Q) :
    (((collapseFunctor T chosen F vertices fixed hchosen) ⋙
      (expandFunctor T chosen F vertices fixed hchosen)).map f) ≫
        counitHom T chosen F vertices fixed hchosen Q =
      counitHom T chosen F vertices fixed hchosen R ≫ f := by
  apply (collapseHomEquiv T chosen F vertices fixed hchosen _ _).injective
  rw [collapseHomEquiv_apply,collapseHomEquiv_apply,Functor.map_comp,Functor.map_comp]
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
      (counitHom T chosen F vertices fixed hchosen Q)).1 +
    Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
      ((expandFunctor T chosen F vertices fixed hchosen).map
        ((collapseFunctor T chosen F vertices fixed hchosen).map f))).1 =
    Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map f).1 +
      Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
        (counitHom T chosen F vertices fixed hchosen R)).1
  rw [collapse_counit_label,collapse_counit_label,collapse_expand_functor_label,zero_add,add_zero]

set_option maxHeartbeats 2000000 in
/-- The actual counit arrow and its inverse full original label form an explicit categorical isomorphism. -/
noncomputable def counitComponent
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    ((collapseFunctor T chosen F vertices fixed hchosen) ⋙
      (expandFunctor T chosen F vertices fixed hchosen)).obj R ≅ R where
  hom := counitHom T chosen F vertices fixed hchosen R
  inv := ⟨Multiplicative.ofAdd (-(counitLabel T chosen F vertices fixed R.back)), by
    change (Multiplicative.ofAdd (counitLabel T chosen F vertices fixed R.back))⁻¹ • R.back =
      expandSupported T chosen F fixed (collapseSupported T chosen F fixed hchosen R.back) 0
    exact inv_smul_eq_iff.mpr (counitHom T chosen F vertices fixed hchosen R).2.symm⟩
  hom_inv_id := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change -(counitLabel T chosen F vertices fixed R.back) + counitLabel T chosen F vertices fixed R.back = 0
    exact neg_add_cancel _
  inv_hom_id := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change counitLabel T chosen F vertices fixed R.back + -(counitLabel T chosen F vertices fixed R.back) = 0
    exact add_neg_cancel _

/-- The component's forward arrow is precisely the actual original counit arrow. -/
theorem counitComponent_hom
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    (counitComponent T chosen F vertices fixed hchosen R).hom =
      counitHom T chosen F vertices fixed hchosen R := rfl

set_option maxHeartbeats 400000 in
/-- The actual natural isomorphism preserves all old names and freely restores the new vertex. -/
noncomputable def counitIso :
    (collapseFunctor T chosen F vertices fixed hchosen) ⋙
      (expandFunctor T chosen F vertices fixed hchosen) ≅
    𝟭 (RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :=
  NatIso.ofComponents
    (F := (collapseFunctor T chosen F vertices fixed hchosen) ⋙ (expandFunctor T chosen F vertices fixed hchosen))
    (G := 𝟭 (RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)))
    (fun R => counitComponent T chosen F vertices fixed hchosen R)
    (by
      intro R Q f
      simp only [counitComponent_hom,Functor.id_map]
      exact counit_naturality T chosen F vertices fixed hchosen f)

/-- The natural comparison's component is precisely the actual counit arrow. -/
theorem counitIso_hom_app
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    (counitIso T chosen F vertices fixed hchosen).hom.app R =
      counitHom T chosen F vertices fixed hchosen R := rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
