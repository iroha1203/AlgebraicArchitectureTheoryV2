import ResearchLean.AG.RelativeRepairComposition.AffineEquation

/-!
# Full label coordinates for a singleton repair object family

An independent equivalence of the whole object family with Unit proves that
every label fixes its object. The projection keeps the complete label group,
so it yields its one-object category without quotienting any automorphism.
-/
namespace AAT.AG.RelativeRepairComposition.W2SingletonCoordinates
open CategoryTheory
universe uG uH uX
variable {G : Type uG} {H : Type uH} {X : Type uX}
variable [Group G] [Group H] [MulAction G X]

/-- Mapping the original action category keeps every full group label in the specified coordinates. -/
def labelFunctor (φ : G ≃* H) : ActionCategory G X ⥤ SingleObj H where
  obj _ := SingleObj.star H
  map f := φ f.1
  map_id _ := φ.map_one
  map_comp f g := φ.map_mul g.1 f.1

/-- Independent singleton object coordinates and complete label coordinates give a whole category equivalence. -/
noncomputable def equivalence (e : X ≃ Unit) (φ : G ≃* H) :
    ActionCategory G X ≌ SingleObj H := by
  let F := labelFunctor (X := X) φ
  letI : F.Full := {
    map_surjective := by
      intro x y f
      refine ⟨⟨φ.symm f, ?_⟩, ?_⟩
      · exact e.injective (Subsingleton.elim _ _)
      · exact φ.apply_symm_apply f }
  letI : F.Faithful := {
    map_injective := by
      intro x y f g h
      apply Subtype.ext
      exact φ.injective h }
  letI : F.EssSurj := {
    mem_essImage := by
      intro y
      refine ⟨(e.symm () : ActionCategory G X), ⟨?_⟩⟩
      exact eqToIso (Unit.ext _ _) }
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-- The whole equivalence's forward arrow reads the complete original label. -/
theorem forward_label (e : X ≃ Unit) (φ : G ≃* H)
    {x y : ActionCategory G X} (f : x ⟶ y) :
    (equivalence e φ).functor.map f = φ f.1 := rfl

end AAT.AG.RelativeRepairComposition.W2SingletonCoordinates
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2SingletonCoordinates
