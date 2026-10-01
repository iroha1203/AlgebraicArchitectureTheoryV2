import ResearchLean.AG.RelativeRepairComposition.SubdivisionCounit

/-!
# Identity-labeled comparison on the original actual repair groupoid

Collapse of zero-first-factor restoration is the identical original actual
repair. Its equality comparison has identity label, and the full composite
functor keeps every original morphism label.

## Implementation notes

The object comparison is equality of actual restored-then-collapsed repairs, hence the native eqToIso has identity label. A chosen arbitrary comparison would require separate proofs that the complete old labels and all shared values are retained.
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

/-- The identity-labeled original-object comparison is natural on all original actual morphisms. -/
theorem unit_naturality {R Q : RepairGroupoid T vertices fixed} (f : R ⟶ Q) :
    f ≫ eqToHom (collapse_expand_functor_obj T chosen F vertices fixed hchosen Q).symm =
      eqToHom (collapse_expand_functor_obj T chosen F vertices fixed hchosen R).symm ≫
        (collapseFunctor T chosen F vertices fixed hchosen).map
          ((expandFunctor T chosen F vertices fixed hchosen).map f) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd (eqToHom
      (collapse_expand_functor_obj T chosen F vertices fixed hchosen Q).symm).1 + Multiplicative.toAdd f.1 =
    Multiplicative.toAdd ((collapseFunctor T chosen F vertices fixed hchosen).map
      ((expandFunctor T chosen F vertices fixed hchosen).map f)).1 +
    Multiplicative.toAdd (eqToHom
      (collapse_expand_functor_obj T chosen F vertices fixed hchosen R).symm).1
  rw [action_eqToHom_label,action_eqToHom_label,collapse_expand_functor_label]
  change 0 + Multiplicative.toAdd f.1 = Multiplicative.toAdd f.1 + 0
  rw [zero_add,add_zero]

/-- The original actual repair groupoid is naturally identified with restoration followed by collapse. -/
noncomputable def unitIso : 𝟭 (RepairGroupoid T vertices fixed) ≅
    (expandFunctor T chosen F vertices fixed hchosen) ⋙
      (collapseFunctor T chosen F vertices fixed hchosen) :=
  NatIso.ofComponents
    (F := 𝟭 (RepairGroupoid T vertices fixed))
    (G := (expandFunctor T chosen F vertices fixed hchosen) ⋙ (collapseFunctor T chosen F vertices fixed hchosen))
    (fun R => eqToIso (collapse_expand_functor_obj T chosen F vertices fixed hchosen R).symm)
    (by intro R Q f; exact unit_naturality T chosen F vertices fixed hchosen f)

/-- Every original unit comparison has precisely the identity full original label. -/
theorem unitIso_label (R : RepairGroupoid T vertices fixed) :
    ((unitIso T chosen F vertices fixed hchosen).hom.app R).1 =
      (1 : Multiplicative (supportedC0 T vertices fixed)) := by
  change (eqToHom (collapse_expand_functor_obj T chosen F vertices fixed hchosen R).symm).1 = _
  exact action_eqToHom_label _

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
