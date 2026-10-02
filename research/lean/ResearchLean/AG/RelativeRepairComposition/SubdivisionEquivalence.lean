import ResearchLean.AG.RelativeRepairComposition.SubdivisionUnit

/-!
# Actual full repair-groupoid equivalence from original edge subdivision

The functor restores zero first correction, the inverse collapses actual
factors, and every old vertex label is retained in both directions. The unit
has identity labels; the counit is the full actual first correction at the
free new vertex and zero at every old vertex.

## Implementation notes

The native CategoryTheory equivalence assembles independently constructed functors and natural isomorphisms. Replacing the category by isomorphism classes would lose the full original labels, stabilizers and strict external-arrow comparison.
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
variable (hchosen : chosen ∉ fixed)

/-- All actual original repairs and all original reidentifications are equivalent after actual internal-edge subdivision. -/
noncomputable def equivalence : RepairGroupoid T vertices fixed ≌
    RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) where
  functor := expandFunctor T chosen F vertices fixed hchosen
  inverse := collapseFunctor T chosen F vertices fixed hchosen
  unitIso := unitIso T chosen F vertices fixed hchosen
  counitIso := counitIso T chosen F vertices fixed hchosen
  functor_unitIso_comp R := by
    apply (collapseHomEquiv T chosen F vertices fixed hchosen _ _).injective
    rw [collapseHomEquiv_apply,collapseHomEquiv_apply,CategoryTheory.Functor.map_comp ]
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
        ((counitIso T chosen F vertices fixed hchosen).hom.app
          ((expandFunctor T chosen F vertices fixed hchosen).obj R))).1 +
      Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
        ((expandFunctor T chosen F vertices fixed hchosen).map
          ((unitIso T chosen F vertices fixed hchosen).hom.app R))).1 = 0
    rw [counitIso_hom_app]
    rw [collapse_counit_label T chosen F vertices fixed hchosen
      ((expandFunctor T chosen F vertices fixed hchosen).obj R)]
    rw [collapse_expand_functor_label T chosen F vertices fixed hchosen
      ((unitIso T chosen F vertices fixed hchosen).hom.app R)]
    rw [unitIso_label T chosen F vertices fixed hchosen R]
    change 0 + 0 = (0 : supportedC0 T vertices fixed)
    exact zero_add _

/-- Every old label value is preserved by the equivalence functor on every original actual morphism. -/
theorem equivalence_functor_label_old {R Q : RepairGroupoid T vertices fixed} (f : R ⟶ Q) (v : K.Vertex) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).functor.map f).1).1 (.inl v) =
      (Multiplicative.toAdd f.1).1 v :=
  expandFunctor_label_old T chosen F vertices fixed hchosen f v

/-- Every old label value is preserved by the equivalence inverse on every new actual morphism. -/
theorem equivalence_inverse_label_old
    {R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)}
    (f : R ⟶ Q) (v : K.Vertex) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).inverse.map f).1).1 v =
      (Multiplicative.toAdd f.1).1 (.inl v) :=
  collapseFunctor_label_old T chosen F vertices fixed hchosen f v

/-- The equivalence restores zero full first correction for each old actual repair. -/
theorem equivalence_functor_first (R : RepairGroupoid T vertices fixed) :
    firstCorrection T chosen F ((equivalence T chosen F vertices fixed hchosen).functor.obj R).back.1 = 0 :=
  expandFunctor_first T chosen F vertices fixed hchosen R

/-- The actual natural comparison is zero at every original vertex. -/
theorem equivalence_counit_old
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (v : K.Vertex) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).counitIso.hom.app R).1).1 (.inl v) = 0 := by
  change (Multiplicative.toAdd ((counitIso T chosen F vertices fixed hchosen).hom.app R).1).1 (.inl v) = 0
  rw [counitIso_hom_app]
  exact counitHom_label_old T chosen F vertices fixed hchosen R v

/-- The actual natural comparison freely restores the full first correction as the new-vertex label. -/
theorem equivalence_counit_fresh
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).counitIso.hom.app R).1).1 (.inr ()) =
      firstCorrection T chosen F R.back.1 := by
  change (Multiplicative.toAdd ((counitIso T chosen F vertices fixed hchosen).hom.app R).1).1 (.inr ()) = _
  rw [counitIso_hom_app]
  exact counitHom_label_fresh T chosen F vertices fixed hchosen R

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
