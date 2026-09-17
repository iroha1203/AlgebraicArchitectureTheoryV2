import Mathlib.Logic.Function.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Restriction criteria for component-indexed families

The restriction of a component-indexed family along a map `q : A → B` is
precomposition.  For a nontrivial value type, separation of global families is
equivalent to surjectivity of `q`, while extension of every local family is
equivalent to injectivity of `q`.  This is the set-theoretic core used later
for the G-124(D) graph-component criterion.
-/

namespace AAT.AG.LocalSemanticReconstruction

namespace ComponentRestriction

/-- Restrict a `B`-indexed family along `q : A → B`. -/
def precompose {A B Value : Type*} (q : A → B) :
    (B → Value) → (A → Value) :=
  fun family => family ∘ q

/-- With at least two values, restriction separates global families exactly
when every global index is represented locally. -/
theorem precompose_injective_iff_surjective
    {A B Value : Type*} [Nontrivial Value] (q : A → B) :
    Function.Injective (precompose (Value := Value) q) ↔
      Function.Surjective q := by
  classical
  constructor
  · intro hinjective globalIndex
    by_contra hnotRepresented
    obtain ⟨first, second, hne⟩ := exists_pair_ne Value
    let firstFamily : B → Value := fun _ => first
    let secondFamily : B → Value :=
      fun index => if index = globalIndex then second else first
    have hrestriction :
        precompose q firstFamily = precompose q secondFamily := by
      funext localIndex
      have hneIndex : q localIndex ≠ globalIndex := by
        intro equality
        exact hnotRepresented ⟨localIndex, equality⟩
      simp [precompose, firstFamily, secondFamily, hneIndex]
    have hfamily := hinjective hrestriction
    have hat := congrFun hfamily globalIndex
    exact hne (by simpa [firstFamily, secondFamily] using hat)
  · intro hsurjective firstFamily secondFamily hrestriction
    funext globalIndex
    obtain ⟨localIndex, rfl⟩ := hsurjective globalIndex
    exact congrFun hrestriction localIndex

/-- With at least two values, every local family extends exactly when distinct
local indices remain distinct after passage to global components. -/
theorem precompose_surjective_iff_injective
    {A B Value : Type*} [Nontrivial Value] (q : A → B) :
    Function.Surjective (precompose (Value := Value) q) ↔
      Function.Injective q := by
  classical
  constructor
  · intro hsurjective firstIndex secondIndex hsame
    by_contra hneIndex
    obtain ⟨first, second, hne⟩ := exists_pair_ne Value
    let localFamily : A → Value :=
      fun index => if index = firstIndex then first else second
    obtain ⟨globalFamily, hglobalFamily⟩ := hsurjective localFamily
    have hlocal : localFamily firstIndex = localFamily secondIndex := by
      rw [← congrFun hglobalFamily firstIndex,
        ← congrFun hglobalFamily secondIndex]
      exact congrArg globalFamily hsame
    have hsecondFirst : secondIndex ≠ firstIndex := Ne.symm hneIndex
    exact hne (by simpa [localFamily, hneIndex, hsecondFirst] using hlocal)
  · intro hinjective localFamily
    obtain ⟨default, _other, _⟩ := exists_pair_ne Value
    refine ⟨Function.extend q localFamily (fun _ => default), ?_⟩
    funext localIndex
    exact hinjective.extend_apply localFamily (fun _ => default) localIndex

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.ComponentRestriction

end ComponentRestriction

end AAT.AG.LocalSemanticReconstruction
