import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials

/-!
# Primitive affine translation updates on every original typed word

## Implementation notes

Updates multiply each original operation by a real terminal translation. Word
values are evaluated independently before identifying their translation terms
with vectorPath. This keeps all occurrences and the suffix transport; accepting
a supplied affine word formula would bypass the primitive composition step.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]

/-- Composition of the two actual translations adds their full vectors. -/
theorem translation_mul (a b : A) :
    translation (k := k) a * translation (k := k) b = translation (k := k) (a + b) := by
  apply AffineEquiv.ext
  intro x
  change a + (b + x) = (a + b) + x
  exact (add_assoc _ _ _).symm

/-- The zero translation is the actual identity operation. -/
@[simp] theorem translation_zero : translation (k := k) (0 : A) = 1 := by
  apply AffineEquiv.ext
  intro x
  exact zero_add x

/-- Inversion of an actual translation negates its full vector. -/
theorem translation_inv (a : A) :
    (translation (k := k) a)⁻¹ = translation (k := k) (-a) := by
  symm
  apply (eq_inv_iff_mul_eq_one).mpr
  rw [translation_mul, neg_add_cancel, translation_zero]

/-- Moving a translation across an actual operation uses precisely its linear component. -/
theorem operation_mul_translation (g : Operations k A) (a : A) :
    g * translation (k := k) a = translation (k := k) (g.linear a) * g := by
  have h := congrArg (fun z : Operations k A => z * g) (conjugation_translation g a)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

variable (K : FiniteTransportPresentation.{uG})
variable (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)

/-- Every updated original edge is realized as a full invertible affine operation. -/
def translatedOperations (h : EdgeName (K := K) → A) :
    ∀ {i j : K.Vertex}, K.Edge i j → Operations k A :=
  fun e => translation (k := k) (h ⟨_, _, e⟩) * R e

/-- Every primitive translation update preserves the original edge linear component. -/
theorem translated_linear (h : EdgeName (K := K) → A) {i j : K.Vertex} (e : K.Edge i j) :
    (translatedOperations K R h e).linear = (R e).linear := by
  change projection (translation (k := k) (h ⟨_,_,e⟩) * R e) = projection (R e)
  rw [map_mul, projection_translation, one_mul]

/-- Every full updated word has the same original linear component. -/
theorem translated_word_linear (h : EdgeName (K := K) → A)
    {i j : K.Vertex} (w : K.Path i j) :
    (GroupExtension.pathValue K (translatedOperations K R h) w).linear =
      (GroupExtension.pathValue K R w).linear := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change projection (GroupExtension.pathValue K (translatedOperations K R h) w *
      translatedOperations K R h e) = projection (GroupExtension.pathValue K R w * R e)
    rw [map_mul, map_mul]
    change (GroupExtension.pathValue K (translatedOperations K R h) w).linear *
      (translatedOperations K R h e).linear = (GroupExtension.pathValue K R w).linear * (R e).linear
    rw [ih, translated_linear]

/-- Real composition derives the full translation sum, including every original repeated edge occurrence. -/
theorem translated_word (h : EdgeName (K := K) → A)
    {i j : K.Vertex} (w : K.Path i j) :
    GroupExtension.pathValue K (translatedOperations K R h) w =
      translation (k := k) (vectorPath K R h w) * GroupExtension.pathValue K R w := by
  induction w with
  | nil _ => change 1 = translation (k := k) (0 : A) * 1; simp
  | cons e w ih =>
    change GroupExtension.pathValue K (translatedOperations K R h) w *
      (translation (k := k) (h ⟨_,_,e⟩) * R e) =
        translation (k := k) ((GroupExtension.pathValue K R w).linear (h ⟨_,_,e⟩) +
          vectorPath K R h w) * (GroupExtension.pathValue K R w * R e)
    rw [ih]
    calc
      (translation (k := k) (vectorPath K R h w) * GroupExtension.pathValue K R w) *
        (translation (k := k) (h ⟨_,_,e⟩) * R e) =
        (translation (k := k) (vectorPath K R h w) *
          (GroupExtension.pathValue K R w * translation (k := k) (h ⟨_,_,e⟩))) * R e := by
            simp only [mul_assoc]
      _ = (translation (k := k) (vectorPath K R h w) *
        translation (k := k) ((GroupExtension.pathValue K R w).linear (h ⟨_,_,e⟩))) *
          (GroupExtension.pathValue K R w * R e) := by
            rw [operation_mul_translation]
            simp only [mul_assoc]
      _ = _ := by rw [translation_mul, add_comm]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
