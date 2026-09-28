import ResearchLean.AG.ProtocolHolonomy.TwoVertexTorsor
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Tactic.FinCases
import Formal.Util.AssertStandardAxioms

/-!
# The original visible projection is reduction C₄ → C₂

The cyclic presentations are not chosen with a prescribed generator. Any
surjective group homomorphism from cyclic four to cyclic two is the standard
modulo-two reduction, so the actual A2 projection gives a commuting square
with these presentations.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The standard modulo-two map, with additive ZMod groups written
multiplicatively as required by the original A2 group. -/
def twoVertexModTwo :
    Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative
    ((ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom)

private def generatorFour : Multiplicative (ZMod 4) :=
  Multiplicative.ofAdd 1

private def generatorTwo : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd 1

/-- Reduction modulo two is the unique surjective group homomorphism
from cyclic four to cyclic two. -/
theorem twoVertex_surjective_C4_C2_unique
    (f : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2))
    (hf : Function.Surjective f) : f = twoVertexModTwo := by
  have hcases4 (x : Multiplicative (ZMod 4)) :
      x = 1 ∨ x = generatorFour ∨ x = generatorFour ^ 2 ∨
        x = generatorFour ^ 3 := by
    fin_cases x <;> decide
  have hcases2 (x : Multiplicative (ZMod 2)) :
      x = 1 ∨ x = generatorTwo := by
    fin_cases x <;> decide
  have hgen : f generatorFour = generatorTwo := by
    rcases hcases2 (f generatorFour) with h | h
    · exfalso
      have hall : ∀ x : Multiplicative (ZMod 4), f x = 1 := by
        intro x
        rcases hcases4 x with hx | hx | hx | hx
        · simp [hx]
        · simp [hx, h]
        · simp [hx, h]
        · simp [hx, h]
      obtain ⟨x, hx⟩ := hf generatorTwo
      have hx' := hall x
      rw [hx'] at hx
      exact (by decide : (1 : Multiplicative (ZMod 2)) ≠ generatorTwo) hx
    · exact h
  have hqgen : twoVertexModTwo generatorFour = generatorTwo := by decide
  apply MonoidHom.ext
  intro x
  rcases hcases4 x with hx | hx | hx | hx
  · simp [hx]
  · rw [hx, hgen, hqgen]
  · rw [hx, map_pow, map_pow, hgen, hqgen]
  · rw [hx, map_pow, map_pow, hgen, hqgen]

/-- A cyclic-two presentation of the exact selected visible H. -/
noncomputable def twoVertexC2 :
    Multiplicative (ZMod 2) ≃* twoVertexInput.H := by
  rw [← twoVertex_H_card_two]
  exact zmodCyclicMulEquiv twoVertex_H_isCyclic

/-- The actual original A2 visible projection, restated without a private
abbreviation. -/
def twoVertexActualProjection :
    twoVertexData.ChangeGroup twoVertexInput.H →* twoVertexInput.H :=
  ReversibleData.ChangeGroup.projection

private noncomputable def twoVertexPresentedProjection :
    Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  twoVertexC2.symm.toMonoidHom.comp
    (twoVertexActualProjection.comp twoVertexC4.toMonoidHom)

private theorem twoVertex_presentedProjection_surjective :
    Function.Surjective twoVertexPresentedProjection := by
  intro z
  obtain ⟨h, rfl⟩ := twoVertexC2.symm.surjective z
  obtain ⟨a, rfl⟩ := twoVertex_projection_surjective h
  obtain ⟨x, rfl⟩ := twoVertexC4.surjective a
  exact ⟨x, rfl⟩

/-- The actual visible projection becomes the standard quotient C₄ → C₂
under the constructed group isomorphisms. -/
theorem twoVertex_projection_is_mod_two
    (z : Multiplicative (ZMod 4)) :
    twoVertexC2.symm (twoVertexActualProjection (twoVertexC4 z)) =
      twoVertexModTwo z := by
  have h := twoVertex_surjective_C4_C2_unique
    twoVertexPresentedProjection twoVertex_presentedProjection_surjective
  exact congrArg (fun f : Multiplicative (ZMod 4) →*
      Multiplicative (ZMod 2) => f z) h

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexModTwo
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_surjective_C4_C2_unique
#print axioms AAT.AG.ProtocolHolonomy.twoVertexC2
#print axioms AAT.AG.ProtocolHolonomy.twoVertexActualProjection
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_projection_is_mod_two
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
