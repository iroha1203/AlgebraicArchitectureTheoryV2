import ResearchLean.AG.LocalSemanticReconstruction.FiniteDeterminingComponents
import Formal.Util.AssertStandardAxioms

/-!
# Permutation-family restriction criteria

This file specializes the G-124(D) component-family criteria to the accepted
hidden permutation family `FixedFComponentPermutationFamily F K`.  Under
`[Nontrivial K]`, the permutation value type is nontrivial, so separation,
extension, and finite determining-set existence inherit the graph criteria.

The same criteria are then transported through the accepted equivalence from
operation-preserving following changes to component-indexed permutations.
-/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace PermutationRestriction

/-- The accepted full-component hidden permutation family. -/
abbrev FullFamily (F : FixedFDirectedMultigraph) (K : Type*) :=
  FixedFComponentPermutationFamily F K

/-- Hidden permutation families on components of the graph induced by `S`. -/
abbrev InducedFamily (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop)
    (K : Type*) :=
  FixedFComponentPermutationFamily (InducedComponent.graph F S) K

/-- Restrict a full-component permutation family to induced components. -/
def restrict (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop)
    (K : Type*) : FullFamily F K → InducedFamily F S K :=
  ComponentRestriction.precompose (InducedComponent.toFull F S)

/-- Permutation-family readings separate exactly when `S` meets every full
component. -/
theorem restrict_injective_iff_meetsEveryFullComponent
    {K : Type*} [Nontrivial K]
    (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop) :
    Function.Injective (restrict F S K) ↔
      InducedComponent.MeetsEveryFullComponent F S :=
  InducedComponent.precompose_toFull_injective_iff_meetsEveryFullComponent
    (Value := Equiv.Perm K) F S

/-- Every induced-component permutation family extends exactly when `S`
retains full connectivity. -/
theorem restrict_surjective_iff_retainsFullConnectivity
    {K : Type*} [Nontrivial K]
    (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop) :
    Function.Surjective (restrict F S K) ↔
      InducedComponent.RetainsFullConnectivity F S :=
  InducedComponent.precompose_toFull_surjective_iff_retainsFullConnectivity
    (Value := Equiv.Perm K) F S

/-- The accepted operation-preserving following-change type over a visible
graph automorphism. -/
abbrev PreservingChange (F : FixedFDirectedMultigraph) (K : Type*)
    (u : FixedFGraphAutomorphism F) :=
  { change : FixedFFollowingStateChange F K u //
    change.PreservesNamedOperations }

/-- Read an operation-preserving following change on the components induced
by `S`, through the accepted component-permutation classification. -/
def restrictPreservingChange
    (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop) (K : Type*)
    (u : FixedFGraphAutomorphism F) :
    PreservingChange F K u → InducedFamily F S K :=
  restrict F S K ∘
    FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies

/-- The induced-component reading separates actual preserving changes exactly
when `S` meets every full component. -/
theorem restrictPreservingChange_injective_iff_meetsEveryFullComponent
    {K : Type*} [Nontrivial K]
    (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop)
    (u : FixedFGraphAutomorphism F) :
    Function.Injective (restrictPreservingChange F S K u) ↔
      InducedComponent.MeetsEveryFullComponent F S := by
  rw [← restrict_injective_iff_meetsEveryFullComponent (K := K) F S]
  let classification :=
    FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
      (F := F) (K := K) (u := u)
  constructor
  · intro hrestrict first second hequal
    obtain ⟨firstChange, rfl⟩ := classification.surjective first
    obtain ⟨secondChange, rfl⟩ := classification.surjective second
    exact congrArg classification
      (hrestrict (by simpa [restrictPreservingChange, classification] using hequal))
  · intro hrestrict
    exact hrestrict.comp classification.injective

/-- Every induced-component permutation family extends to an actual preserving
change exactly when `S` retains full connectivity. -/
theorem restrictPreservingChange_surjective_iff_retainsFullConnectivity
    {K : Type*} [Nontrivial K]
    (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop)
    (u : FixedFGraphAutomorphism F) :
    Function.Surjective (restrictPreservingChange F S K u) ↔
      InducedComponent.RetainsFullConnectivity F S := by
  rw [← restrict_surjective_iff_retainsFullConnectivity (K := K) F S]
  let classification :=
    FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
      (F := F) (K := K) (u := u)
  constructor
  · intro hsurjective family
    obtain ⟨change, hchange⟩ := hsurjective family
    exact ⟨classification change,
      by simpa [restrictPreservingChange, classification] using hchange⟩
  · intro hsurjective family
    obtain ⟨fullFamily, hfullFamily⟩ := hsurjective family
    obtain ⟨change, rfl⟩ := classification.surjective fullFamily
    exact ⟨change,
      by simpa [restrictPreservingChange, classification] using hfullFamily⟩

/-- Existence of a finite induced-component reading that both separates and
extends actual preserving following changes. -/
def HasFiniteDeterminingPreservingRestriction
    (F : FixedFDirectedMultigraph) (K : Type*)
    (u : FixedFGraphAutomorphism F) : Prop :=
  ∃ S : F.Vertex → Prop,
    Set.Finite { vertex | S vertex } ∧
      Function.Injective (restrictPreservingChange F S K u) ∧
      Function.Surjective (restrictPreservingChange F S K u)

/-- For at least two hidden values, a finite determining reading for actual
preserving changes exists exactly when the full component type is finite. -/
theorem hasFiniteDeterminingPreservingRestriction_iff
    {K : Type*} [Nontrivial K]
    (F : FixedFDirectedMultigraph) (u : FixedFGraphAutomorphism F) :
    HasFiniteDeterminingPreservingRestriction F K u ↔
      Finite (FixedFComponent F) := by
  rw [← InducedComponent.hasFiniteDeterminingVertices_iff]
  constructor
  · rintro ⟨S, hfinite, hseparates, hextends⟩
    exact ⟨S, hfinite,
      (restrictPreservingChange_injective_iff_meetsEveryFullComponent
        (K := K) F S u).mp hseparates,
      (restrictPreservingChange_surjective_iff_retainsFullConnectivity
        (K := K) F S u).mp hextends⟩
  · rintro ⟨S, hfinite, hmeets, hretains⟩
    exact ⟨S, hfinite,
      (restrictPreservingChange_injective_iff_meetsEveryFullComponent
        (K := K) F S u).mpr hmeets,
      (restrictPreservingChange_surjective_iff_retainsFullConnectivity
        (K := K) F S u).mpr hretains⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.PermutationRestriction

end PermutationRestriction

end AAT.AG.LocalSemanticReconstruction
