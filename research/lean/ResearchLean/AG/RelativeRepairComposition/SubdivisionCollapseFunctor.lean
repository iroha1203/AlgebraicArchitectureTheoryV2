import ResearchLean.AG.RelativeRepairComposition.SubdivisionHomLift

/-!
# Actual groupoid collapse with all original morphisms

The functor acts on independent supported actual repairs and restricts each
full original vertex label. Every arrow between arbitrary new repairs has a
unique preimage above each old arrow, by the full fresh-label formula.

## Implementation notes

The native action category keeps every allowed vertex label, including ineffective stabilizers. Collapse restricts that full label; its inverse Hom map adds the uniquely forced fresh value between arbitrary new objects. A quotient of labels or a restriction to restored objects would drop original morphisms and would not give the required full native Hom equivalence.
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

/-- Collapse the independent actual repair groupoid and every full original vertex label. -/
noncomputable def collapseFunctor :
    RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) ⥤
      RepairGroupoid T vertices fixed where
  obj R := (collapseSupported T chosen F fixed hchosen R.back : RepairGroupoid T vertices fixed)
  map {R _} f := ⟨(collapseAllowedLabel T chosen F vertices fixed hchosen).toMultiplicative f.1, by
    exact (collapseSupported_gauge T chosen F vertices fixed hchosen (Multiplicative.toAdd f.1) R.back).symm.trans
      (congrArg (collapseSupported T chosen F fixed hchosen) f.2)⟩
  map_id _ := by
    apply Subtype.ext
    change collapseAllowedLabel T chosen F vertices fixed hchosen 0 = 0
    exact map_zero _
  map_comp f g := by
    apply Subtype.ext
    change collapseAllowedLabel T chosen F vertices fixed hchosen
      (Multiplicative.toAdd g.1 + Multiplicative.toAdd f.1) =
      collapseAllowedLabel T chosen F vertices fixed hchosen (Multiplicative.toAdd g.1) +
        collapseAllowedLabel T chosen F vertices fixed hchosen (Multiplicative.toAdd f.1)
    exact map_add _ _ _

/-- Each old vertex value of an actual mapped morphism is exactly its old original value. -/
theorem collapseFunctor_label_old
    {R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)}
    (f : R ⟶ Q) (v : K.Vertex) :
    (Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map f).1).1 v =
      (Multiplicative.toAdd f.1).1 (.inl v) := rfl

/-- Every full native morphism between arbitrary new repairs corresponds to precisely one old native morphism. -/
noncomputable def collapseHomEquiv
    (R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    (R ⟶ Q) ≃
      ((collapseFunctor T chosen F vertices fixed hchosen).obj R ⟶
        (collapseFunctor T chosen F vertices fixed hchosen).obj Q) where
  toFun := (collapseFunctor T chosen F vertices fixed hchosen).map
  invFun f := ⟨Multiplicative.ofAdd
    (liftGaugeLabel T chosen F vertices fixed R.back Q.back (Multiplicative.toAdd f.1)),
    liftGaugeLabel_gauge T chosen F vertices fixed hchosen R.back Q.back (Multiplicative.toAdd f.1) f.2⟩
  left_inv f := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact (liftGaugeLabel_unique T chosen F vertices fixed hchosen R.back Q.back
      (collapseAllowedLabel T chosen F vertices fixed hchosen (Multiplicative.toAdd f.1))
      (Multiplicative.toAdd f.1) rfl f.2).symm
  right_inv f := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact liftGaugeLabel_collapse T chosen F vertices fixed hchosen R.back Q.back (Multiplicative.toAdd f.1)

/-- The forward full native Hom equivalence is precisely the actual functor map. -/
theorem collapseHomEquiv_apply
    (R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (f : R ⟶ Q) :
    collapseHomEquiv T chosen F vertices fixed hchosen R Q f =
      (collapseFunctor T chosen F vertices fixed hchosen).map f := rfl

/-- The full inverse native Hom map uses the forced value in the entire actual new-object kernel. -/
theorem collapseHomEquiv_inverse_fresh
    (R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (f : (collapseFunctor T chosen F vertices fixed hchosen).obj R ⟶
      (collapseFunctor T chosen F vertices fixed hchosen).obj Q) :
    (Multiplicative.toAdd ((collapseHomEquiv T chosen F vertices fixed hchosen R Q).symm f).1).1 (.inr ()) =
      liftFreshValue T chosen F vertices fixed R.back Q.back (Multiplicative.toAdd f.1) := rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
