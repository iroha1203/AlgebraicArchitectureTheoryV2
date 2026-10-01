import ResearchLean.AG.RelativeRepairComposition.AffineTranslationWords

/-!
# Defect updates derived from primitive original affine compositions

## Implementation notes

The defect vector evaluates the actual comparator and both reference words at
zero. The constant and linear update are then derived from their product. A
supplied right-hand-side family would omit this connection to primitive values.
The original face linear alignment is used only to identify the word quotient
as an entire-kernel translation, not to assume a successful repair.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)

/-- The primitive original defect is the value of its actual affine comparison product. -/
def realDefectVector (f : K.TwoCell) : A :=
  (translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) *
    (GroupExtension.pathValue K R (K.twoRight f))⁻¹) 0

/-- Equal original word linear parts make their actual quotient an entire-kernel translation. -/
theorem reference_word_quotient (f : K.TwoCell)
    (hf : (GroupExtension.pathValue K R (K.twoLeft f)).linear =
      (GroupExtension.pathValue K R (K.twoRight f)).linear) :
    GroupExtension.pathValue K R (K.twoLeft f) *
      (GroupExtension.pathValue K R (K.twoRight f))⁻¹ =
        translation (k := k) ((GroupExtension.pathValue K R (K.twoLeft f) *
          (GroupExtension.pathValue K R (K.twoRight f))⁻¹) 0) := by
  apply (projection_eq_one_iff _).mp
  rw [map_mul, map_inv]
  change (GroupExtension.pathValue K R (K.twoLeft f)).linear *
    ((GroupExtension.pathValue K R (K.twoRight f)).linear)⁻¹ = 1
  rw [hf, mul_inv_cancel]

/-- Primitive evaluation decomposes the original defect into comparison and reference residual values. -/
theorem real_defect_residual (f : K.TwoCell) :
    realDefectVector K R c f = c f +
      (GroupExtension.pathValue K R (K.twoLeft f) *
        (GroupExtension.pathValue K R (K.twoRight f))⁻¹) 0 := by
  unfold realDefectVector
  rw [mul_assoc]
  rfl

/-- Primitive terminal translations derive the same complete original affine defect update. -/
theorem translated_defect (h : EdgeName (K := K) → A) (u : K.TwoCell → A)
    (f : K.TwoCell)
    (hf : (GroupExtension.pathValue K R (K.twoLeft f)).linear =
      (GroupExtension.pathValue K R (K.twoRight f)).linear) :
    realDefectVector K (translatedOperations K R h) (c + u) f =
      realDefectVector K R c f + u f + vectorPath K R h (K.twoLeft f) -
        vectorPath K R h (K.twoRight f) := by
  unfold realDefectVector
  rw [translated_word, translated_word, mul_inv_rev, translation_inv]
  have hw := reference_word_quotient K R f hf
  have he :
      translation (k := k) ((c + u) f) *
          (translation (k := k) (vectorPath K R h (K.twoLeft f)) *
            GroupExtension.pathValue K R (K.twoLeft f)) *
          ((GroupExtension.pathValue K R (K.twoRight f))⁻¹ *
            translation (k := k) (-vectorPath K R h (K.twoRight f))) =
        translation (k := k) ((c + u) f) *
          translation (k := k) (vectorPath K R h (K.twoLeft f)) *
          (GroupExtension.pathValue K R (K.twoLeft f) *
            (GroupExtension.pathValue K R (K.twoRight f))⁻¹) *
          translation (k := k) (-vectorPath K R h (K.twoRight f)) := by
    simp only [mul_assoc]
  rw [he, hw, translation_mul, translation_mul, translation_mul]
  change ((c f + u f) + vectorPath K R h (K.twoLeft f) +
    (GroupExtension.pathValue K R (K.twoLeft f) *
      (GroupExtension.pathValue K R (K.twoRight f))⁻¹) 0 +
    -vectorPath K R h (K.twoRight f)) + 0 = _
  rw [mul_assoc]
  change _ = (c f + (GroupExtension.pathValue K R (K.twoLeft f) *
    (GroupExtension.pathValue K R (K.twoRight f))⁻¹) 0) + u f +
      vectorPath K R h (K.twoLeft f) - vectorPath K R h (K.twoRight f)
  abel

/-- The primitive full vector is exactly the defect of the same original native affine tower. -/
theorem real_defect_native
    (L : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (f : K.TwoCell) :
    coefficient K L R c hfaces (K.twoTarget f) ((tower K L R c hfaces).toTower.defect f) =
      realDefectVector K R c f := defect_value K L R c hfaces f

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
