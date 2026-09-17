import ResearchLean.AG.LocalSemanticReconstruction.InducedComponentCriteria
import Mathlib.Data.Set.Finite.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Finite determining vertex sets and finite component types

The graph criteria from the preceding cycle imply that a finite vertex subset
can both meet every full component and retain full connectivity exactly when
the full component type is finite.  In the finite direction, the subset is
constructed as the range of the canonical quotient representative choice, so
it contains exactly one chosen vertex for each component.
-/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace InducedComponent

/-- The canonical chosen vertex representative of a full component. -/
noncomputable def representative (F : FixedFDirectedMultigraph) :
    FixedFComponent F → F.Vertex :=
  Quotient.out

@[simp]
theorem componentMk_representative (F : FixedFDirectedMultigraph)
    (component : FixedFComponent F) :
    fixedFComponentMk F (representative F component) = component :=
  Quotient.out_eq component

/-- The vertex predicate consisting of one canonical representative from each
full component. -/
def RepresentativeVertex (F : FixedFDirectedMultigraph) : F.Vertex → Prop :=
  Set.range (representative F)

/-- When the component type is finite, its chosen representative vertices form
a finite subset of the full vertex type. -/
theorem representativeVertex_finite (F : FixedFDirectedMultigraph)
    [Finite (FixedFComponent F)] :
    Set.Finite { vertex | RepresentativeVertex F vertex } := by
  change (Set.range (representative F)).Finite
  let rangeMap : FixedFComponent F → Set.range (representative F) :=
    fun component => ⟨representative F component, ⟨component, rfl⟩⟩
  letI : Finite (Set.range (representative F)) :=
    Finite.of_surjective rangeMap (by
      rintro ⟨vertex, component, equality⟩
      refine ⟨component, ?_⟩
      exact Subtype.ext equality)
  exact Set.toFinite _

/-- The chosen representative subset meets every full component. -/
theorem representativeVertex_meetsEveryFullComponent
    (F : FixedFDirectedMultigraph) :
    MeetsEveryFullComponent F (RepresentativeVertex F) := by
  intro vertex
  let component := fixedFComponentMk F vertex
  let retained : (graph F (RepresentativeVertex F)).Vertex :=
    ⟨representative F component, ⟨component, rfl⟩⟩
  refine ⟨retained, ?_⟩
  apply (fixedFComponentMk_eq_iff F retained.1 vertex).mp
  exact componentMk_representative F component

/-- Two chosen representatives in one full component are the same selected
vertex, so the representative subset retains full connectivity. -/
theorem representativeVertex_retainsFullConnectivity
    (F : FixedFDirectedMultigraph) :
    RetainsFullConnectivity F (RepresentativeVertex F) := by
  rintro ⟨first, ⟨firstComponent, rfl⟩⟩
    ⟨second, ⟨secondComponent, rfl⟩⟩ hreachable
  have hcomponents : firstComponent = secondComponent := by
    calc
      firstComponent =
          fixedFComponentMk F (representative F firstComponent) :=
        (componentMk_representative F firstComponent).symm
      _ = fixedFComponentMk F (representative F secondComponent) :=
        (fixedFComponentMk_eq_iff F _ _).mpr hreachable
      _ = secondComponent :=
        componentMk_representative F secondComponent
  subst secondComponent
  exact Relation.EqvGen.refl _

/-- Existence of a finite vertex subset satisfying both graph criteria. -/
def HasFiniteDeterminingVertices (F : FixedFDirectedMultigraph) : Prop :=
  ∃ S : F.Vertex → Prop,
    Set.Finite { vertex | S vertex } ∧
      MeetsEveryFullComponent F S ∧ RetainsFullConnectivity F S

/-- A finite determining vertex subset exists exactly when the full component
type is finite. -/
theorem hasFiniteDeterminingVertices_iff
    (F : FixedFDirectedMultigraph) :
    HasFiniteDeterminingVertices F ↔ Finite (FixedFComponent F) := by
  constructor
  · rintro ⟨S, hfinite, hmeets, _hretains⟩
    letI : Finite { vertex // S vertex } := by
      exact Set.Finite.to_subtype hfinite
    apply Finite.of_surjective
      (fun retained : { vertex // S vertex } =>
        fixedFComponentMk F retained.1)
    intro component
    obtain ⟨vertex, rfl⟩ := Quotient.exists_rep component
    obtain ⟨retained, hreachable⟩ := hmeets vertex
    refine ⟨retained, ?_⟩
    exact (fixedFComponentMk_eq_iff F retained.1 vertex).mpr hreachable
  · intro hfinite
    letI : Finite (FixedFComponent F) := hfinite
    exact ⟨RepresentativeVertex F, representativeVertex_finite F,
      representativeVertex_meetsEveryFullComponent F,
      representativeVertex_retainsFullConnectivity F⟩

/-- Existence of a finite vertex subset on which component-family restriction
is both separating and extending. -/
def HasFiniteDeterminingRestriction (F : FixedFDirectedMultigraph)
    (Value : Type*) : Prop :=
  ∃ S : F.Vertex → Prop,
    Set.Finite { vertex | S vertex } ∧
      Function.Injective
        (ComponentRestriction.precompose (Value := Value) (toFull F S)) ∧
      Function.Surjective
        (ComponentRestriction.precompose (Value := Value) (toFull F S))

/-- For nontrivial component values, a finite separating-and-extending
restriction exists exactly when the full component type is finite. -/
theorem hasFiniteDeterminingRestriction_iff
    {Value : Type*} [Nontrivial Value] (F : FixedFDirectedMultigraph) :
    HasFiniteDeterminingRestriction F Value ↔ Finite (FixedFComponent F) := by
  rw [← hasFiniteDeterminingVertices_iff]
  constructor
  · rintro ⟨S, hfinite, hseparates, hextends⟩
    exact ⟨S, hfinite,
      (precompose_toFull_injective_iff_meetsEveryFullComponent F S).mp
        hseparates,
      (precompose_toFull_surjective_iff_retainsFullConnectivity F S).mp
        hextends⟩
  · rintro ⟨S, hfinite, hmeets, hretains⟩
    exact ⟨S, hfinite,
      (precompose_toFull_injective_iff_meetsEveryFullComponent F S).mpr
        hmeets,
      (precompose_toFull_surjective_iff_retainsFullConnectivity F S).mpr
        hretains⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.InducedComponent

end InducedComponent

end AAT.AG.LocalSemanticReconstruction
