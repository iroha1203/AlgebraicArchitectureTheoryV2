import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleConormalSheafification
import Formal.AG.SemanticRepair.Conormal.LawGeneratedLargeCoefficientCech
import Formal.Util.AssertStandardAxioms
import Mathlib.Tactic

/-!
# Canonical tuple profile for the Boolean-circle cover

This file computes the actual overlap objects used by the repository's
canonical-tuple Cech complex.  Degree-one overlaps contain at most two selected
indices, while a degree-two overlap is the unique deep context exactly when
its three entries exhaust `Fin 3`.  These are geometric computations only; no
cocycle or cohomology conclusion is accepted as input data.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedBooleanCircleTupleProfile

open CategoryTheory
open AAT.AG
open LawGeneratedBooleanCircleSite
open LawGeneratedBooleanCircleLawCore
open LawGeneratedBooleanCircleRawConormalSheaf
open LawGeneratedIdealPowerSequence
open LawGeneratedLargeCoefficientCech

local instance : DecidableEq geometry.cover.Index := Classical.decEq _

/-- The selected indices appearing in a canonical tuple. -/
def tupleSupport (n : Nat) (sigma : Tuple geometry n) : Finset (Fin 3) :=
  Finset.univ.image sigma

/-- A degree-zero canonical overlap is its displayed singleton chart. -/
theorem overlapObject_zero_ctx (sigma : Tuple geometry 0) :
    (overlapObject geometry 0 sigma).ctx = context {sigma 0} := by
  rfl

/-- A degree-one canonical overlap is the union of its two singleton charts. -/
theorem overlapObject_one_ctx (sigma : Tuple geometry 1) :
    (overlapObject geometry 1 sigma).ctx =
      context ({sigma 0, sigma 1} : Finset (Fin 3)) := by
  simp [overlapObject, tupleGeometry,
    Site.FinitePosetCoverGeometry.canonicalTupleCoverGeometryFromOverlap,
    Site.FinitePosetCoverGeometry.canonicalTupleOverlapFromOverlap,
    site, contextOverlap, overlapContext, geometry, base,
    cover, chartContextIndex, Site.ContextCategoryObject.of, recognized_context,
    indexOf_context]

/-- A degree-two canonical overlap is the union of its three singleton charts. -/
theorem overlapObject_two_ctx (sigma : Tuple geometry 2) :
    (overlapObject geometry 2 sigma).ctx =
      context ({sigma 0, sigma 1, sigma 2} : Finset (Fin 3)) := by
  simp [overlapObject, tupleGeometry,
    Site.FinitePosetCoverGeometry.canonicalTupleCoverGeometryFromOverlap,
    Site.FinitePosetCoverGeometry.canonicalTupleOverlapFromOverlap,
    site, contextOverlap, overlapContext, geometry, base,
    cover, chartContextIndex, Site.ContextCategoryObject.of, recognized_context,
    indexOf_context]

/-- No two selected indices exhaust `Fin 3`. -/
theorem pair_ne_univ (a b : Fin 3) :
    ({a, b} : Finset (Fin 3)) ≠ Finset.univ := by
  intro h
  have hc := congrArg Finset.card h
  have hle : ({a, b} : Finset (Fin 3)).card ≤ 2 := Finset.card_le_two
  norm_num at hc
  omega

/-- Every canonical pair overlap lies outside the deep context. -/
theorem pairOverlap_not_deep (sigma : Tuple geometry 1) :
    ¬ Deep (overlapObject geometry 1 sigma) := by
  rintro ⟨_, h⟩
  apply pair_ne_univ (sigma 0) (sigma 1)
  rw [overlapObject_one_ctx, indexOf_context] at h
  exact h

/-- A canonical triple overlap is deep exactly when its entries exhaust the cover. -/
theorem tripleOverlap_deep_iff (sigma : Tuple geometry 2) :
    Deep (overlapObject geometry 2 sigma) ↔
      ({sigma 0, sigma 1, sigma 2} : Finset (Fin 3)) = Finset.univ := by
  rw [Deep, overlapObject_two_ctx, indexOf_context]
  simp only [recognized_context, true_and]

/-- Repeated canonical triples are not deep. -/
theorem tripleOverlap_not_deep_of_repeat (sigma : Tuple geometry 2)
    (h : sigma 0 = sigma 1 ∨ sigma 0 = sigma 2 ∨ sigma 1 = sigma 2) :
    ¬ Deep (overlapObject geometry 2 sigma) := by
  rw [tripleOverlap_deep_iff]
  intro hall
  rcases h with h01 | h02 | h12
  · apply pair_ne_univ (sigma 1) (sigma 2)
    simpa [h01] using hall
  · apply pair_ne_univ (sigma 2) (sigma 1)
    simpa [h02, Finset.pair_comm] using hall
  · apply pair_ne_univ (sigma 0) (sigma 2)
    simpa [h12] using hall

/-- The oriented circle triple `0,1,2` reaches the unique deep context. -/
theorem triple012_deep :
    Deep (overlapObject geometry 2
      (fun i : Fin 3 => i)) := by
  rw [tripleOverlap_deep_iff]
  decide

/-! ## The raw square-zero circle cocycle -/

/-- Active-value evaluation is additive. -/
@[simp] theorem activeValue_zero (W : site.category) :
    activeValue W 0 = 0 := by
  change (((activeIdealEquiv W).symm 0).1 : AmbientRing) = 0
  rw [map_zero]
  rfl

@[simp] theorem activeValue_add (W : site.category)
    (x y : Raw.Conormal squareZeroCore W) :
    activeValue W (x + y) = activeValue W x + activeValue W y := by
  change (((activeIdealEquiv W).symm (x + y)).1 : AmbientRing) =
    ((activeIdealEquiv W).symm x).1 + ((activeIdealEquiv W).symm y).1
  rw [map_add]
  rfl

@[simp] theorem activeValue_neg (W : site.category)
    (x : Raw.Conormal squareZeroCore W) :
    activeValue W (-x) = -activeValue W x := by
  change (((activeIdealEquiv W).symm (-x)).1 : AmbientRing) =
    -((activeIdealEquiv W).symm x).1
  rw [map_neg]
  rfl

/-- The displayed raw generator is preserved between nondeep contexts. -/
theorem squareZeroConormalGenerator_restrict
    {source target : site.category} (f : source ⟶ target)
    (hs : ¬ Deep source) (ht : ¬ Deep target) :
    Raw.conormalRestrict squareZeroCore f
        (squareZeroConormalGenerator target ht) =
      squareZeroConormalGenerator source hs := by
  apply activeValue_injective source
  rw [conormalRestrict_activeValue source target hs f]
  simp [squareZeroConormalGenerator, activeValue_toCotangent]

/-- The raw generator evaluated in the ambient ring is the fixed square-zero element. -/
@[simp] theorem activeValue_squareZeroConormalGenerator
    (W : site.category) (hW : ¬ Deep W) :
    activeValue W (squareZeroConormalGenerator W hW) = squareZeroGenerator := by
  simp [squareZeroConormalGenerator, activeValue_toCotangent]

@[simp] theorem squareZeroGenerator_add_self :
    squareZeroGenerator + squareZeroGenerator = 0 := by
  ext <;> simp [squareZeroGenerator]
  change (2 : ZMod 2) = 0
  decide

/-- The circle one-cochain: the generator on nonrepeated ordered pairs and zero on repeats. -/
noncomputable def rawOmega :
    Cochain geometry rawConormal 1 := by
  classical
  exact fun sigma => if sigma 0 = sigma 1 then 0
    else squareZeroConormalGenerator
      (overlapObject geometry 1 sigma) (pairOverlap_not_deep sigma)

@[simp] theorem activeValue_rawOmega (sigma : Tuple geometry 1) :
    activeValue (overlapObject geometry 1 sigma) (rawOmega sigma) =
      if sigma 0 = sigma 1 then 0 else squareZeroGenerator := by
  classical
  by_cases h : sigma 0 = sigma 1
  · simp [rawOmega, h]
  · simp [rawOmega, h]

/-- Active values commute with a raw face restriction into a nondeep tuple overlap. -/
theorem activeValue_faceRestriction
    (n : Nat) (c : Cochain geometry rawConormal n)
    (sigma : Tuple geometry (n + 1)) (i : Fin (n + 2))
    (h : ¬ Deep (overlapObject geometry (n + 1) sigma)) :
    activeValue (overlapObject geometry (n + 1) sigma)
        (faceRestriction geometry rawConormal n c sigma i) =
      activeValue (overlapObject geometry n (face geometry n sigma i))
        (c (face geometry n sigma i)) := by
  exact conormalRestrict_activeValue _ _ h _ _

/-- Three elements of `Fin 3` either repeat or exhaust the type. -/
theorem fin3_repeat_or_univ (a b c : Fin 3) :
    a = b ∨ a = c ∨ b = c ∨
      ({a, b, c} : Finset (Fin 3)) = Finset.univ := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp <;> decide

@[simp] theorem face_two_zero_zero (sigma : Tuple geometry 2) :
    face geometry 1 sigma 0 0 = sigma 1 := rfl

@[simp] theorem face_two_zero_one (sigma : Tuple geometry 2) :
    face geometry 1 sigma 0 1 = sigma 2 := rfl

@[simp] theorem face_two_one_zero (sigma : Tuple geometry 2) :
    face geometry 1 sigma 1 0 = sigma 0 := rfl

@[simp] theorem face_two_one_one (sigma : Tuple geometry 2) :
    face geometry 1 sigma 1 1 = sigma 2 := rfl

@[simp] theorem face_two_two_zero (sigma : Tuple geometry 2) :
    face geometry 1 sigma 2 0 = sigma 0 := rfl

@[simp] theorem face_two_two_one (sigma : Tuple geometry 2) :
    face geometry 1 sigma 2 1 = sigma 1 := rfl

/-- The raw circle one-cochain is killed by the actual canonical-tuple differential. -/
theorem rawOmega_cocycle :
    d1 geometry rawConormal rawOmega = 0 := by
  classical
  funext sigma
  change d1 geometry rawConormal rawOmega sigma = 0
  by_cases hdeep : Deep (overlapObject geometry 2 sigma)
  · exact squareZero_conormal_eq_zero_of_deep _ hdeep _
  · apply activeValue_injective (overlapObject geometry 2 sigma)
    rw [activeValue_zero]
    dsimp [d1, differential]
    simp [Fin.sum_univ_succ]
    rw [activeValue_add, activeValue_add, activeValue_neg]
    rw [activeValue_faceRestriction 1 rawOmega sigma 0 hdeep,
      activeValue_faceRestriction 1 rawOmega sigma 1 hdeep,
      activeValue_faceRestriction 1 rawOmega sigma 2 hdeep]
    simp only [activeValue_rawOmega]
    have hrepeat : sigma 0 = sigma 1 ∨ sigma 0 = sigma 2 ∨ sigma 1 = sigma 2 := by
      rcases fin3_repeat_or_univ (sigma 0) (sigma 1) (sigma 2) with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact False.elim (hdeep ((tripleOverlap_deep_iff sigma).2 h))
    rcases hrepeat with h01 | h02 | h12
    · simp [h01, squareZeroGenerator]
    · by_cases h12 : sigma 1 = sigma 2
      · simp [h02, h12]
      · have h21 : ¬ sigma 2 = sigma 1 := fun h => h12 h.symm
        simp [h02, h12, h21, squareZeroGenerator_add_self]
    · simp [h12, squareZeroGenerator]

end LawGeneratedBooleanCircleTupleProfile
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleTupleProfile
