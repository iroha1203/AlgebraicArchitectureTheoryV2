import ResearchLean.AG.RelativeRepairComposition.SubdivisionCollapseFunctor
import ResearchLean.AG.RelativeRepairComposition.SubdivisionZeroSection

/-!
# The actual inverse functor by zero first-factor restoration

Every object restores the same original actual choices with zero first-factor
correction. Every original morphism keeps all original labels and has the full
actual transported source label at the fresh vertex.

## Implementation notes

The inverse functor uses zero first correction together with the full transported fresh label from zeroSectionLabel. This makes identity and composition follow from its additive hom while preserving all old labels. An arbitrary restoration parameter at each object would require parameter differences in the arrow map; using zero without the transported label would fail the actual gauge equation.
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

/-- Restore actual supported repairs and every full old morphism, using zero first-factor correction. -/
noncomputable def expandFunctor : RepairGroupoid T vertices fixed ⥤
    RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) where
  obj R := (expandSupported T chosen F fixed R.back 0 :
    RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
  map {R Q} f := ⟨(zeroSectionLabel T chosen F vertices fixed).toMultiplicative f.1,
    zeroSectionLabel_gauge T chosen F vertices fixed hchosen (Multiplicative.toAdd f.1) R.back Q.back f.2⟩
  map_id _ := by
    apply Subtype.ext
    change zeroSectionLabel T chosen F vertices fixed 0 = 0
    exact map_zero _
  map_comp f g := by
    apply Subtype.ext
    change zeroSectionLabel T chosen F vertices fixed
      (Multiplicative.toAdd g.1 + Multiplicative.toAdd f.1) =
      zeroSectionLabel T chosen F vertices fixed (Multiplicative.toAdd g.1) +
        zeroSectionLabel T chosen F vertices fixed (Multiplicative.toAdd f.1)
    exact map_add _ _ _

/-- Every original vertex value of a restored actual morphism is the original full label value. -/
theorem expandFunctor_label_old {R Q : RepairGroupoid T vertices fixed} (f : R ⟶ Q) (v : K.Vertex) :
    (Multiplicative.toAdd ((expandFunctor T chosen F vertices fixed hchosen).map f).1).1 (.inl v) =
      (Multiplicative.toAdd f.1).1 v := rfl

/-- The actual fresh-vertex label of a restored morphism is the generated full first-factor transport. -/
theorem expandFunctor_label_fresh {R Q : RepairGroupoid T vertices fixed} (f : R ⟶ Q) :
    (Multiplicative.toAdd ((expandFunctor T chosen F vertices fixed hchosen).map f).1).1 (.inr ()) =
      rho1AddEquiv T chosen F ((Multiplicative.toAdd f.1).1 chosen.1) := rfl

/-- Every restored actual groupoid object has zero full first-factor correction. -/
theorem expandFunctor_first (R : RepairGroupoid T vertices fixed) :
    firstCorrection T chosen F ((expandFunctor T chosen F vertices fixed hchosen).obj R).back.1 = 0 :=
  firstCorrection_expandSupported T chosen F fixed R.back 0

/-- Collapse after the inverse functor recovers the identical original actual groupoid object. -/
theorem collapse_expand_functor_obj (R : RepairGroupoid T vertices fixed) :
    (collapseFunctor T chosen F vertices fixed hchosen).obj
      ((expandFunctor T chosen F vertices fixed hchosen).obj R) = R := by
  exact (congrArg (fun U : SupportedRepair T fixed => (U : RepairGroupoid T vertices fixed))
    (collapse_expand_supported T chosen F fixed hchosen R.back 0)).trans (ActionCategory.back_coe R)

/-- On every actual restored arrow the composite functors preserve its complete original label. -/
theorem collapse_expand_functor_label {R Q : RepairGroupoid T vertices fixed} (f : R ⟶ Q) :
    (Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
      ((expandFunctor T chosen F vertices fixed hchosen).map f)).1) = Multiplicative.toAdd f.1 :=
  collapse_zeroSectionLabel T chosen F vertices fixed hchosen (Multiplicative.toAdd f.1)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
