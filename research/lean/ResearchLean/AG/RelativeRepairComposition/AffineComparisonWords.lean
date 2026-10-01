import ResearchLean.AG.RelativeRepairComposition.AffineTranslationWords
import ResearchLean.AG.RelativeRepairComposition.AffineVectorLinear

/-!
# Primitive comparison operations and the complete three-cell law

## Implementation notes

Each oriented comparison and every occurrence in a typed pasting is evaluated
as its real affine operation. Equality of the two original routes is therefore
equivalent to the generated vector differential being zero. Changing reference
translations preserves every outgoing linear transport in these expressions.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)

/-- Every complete original path correction sum uses the same linear transport after reference translations change. -/
theorem translated_vector_path (h : EdgeName (K := K) → A)
    (a : EdgeName (K := K) → A) {i j : K.Vertex} (w : K.Path i j) :
    vectorPath K (translatedOperations K R h) a w = vectorPath K R a w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (GroupExtension.pathValue K (translatedOperations K R h) w).linear (a ⟨_,_,e⟩) +
      vectorPath K (translatedOperations K R h) a w = _
    rw [translated_word_linear, ih]
    rfl

/-- The actual oriented comparison is precisely its full transported translation. -/
theorem face_operation_translation (c : K.TwoCell → A) {s t : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation s t) :
    faceOperation K R c f = translation (k := k) (vectorFace K R c f) := by
  cases ho : f.orientation <;>
    simp only [faceOperation, vectorFace, ho, translation_inv, conjugation_translation, map_neg]

/-- The actual complete pasting evaluates the sum of all original oriented occurrences. -/
theorem pasting_operation_translation (c : K.TwoCell → A) {s t : K.Vertex} {w z : K.Path s t}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingOperation K R c p = translation (k := k) (vectorPasting K R c p) := by
  induction p with
  | nil _ => exact (translation_zero).symm
  | cons step tail ih =>
    change pastingOperation K R c tail * faceOperation K R c step.face = _
    rw [ih, face_operation_translation, translation_mul]
    simp only [vectorPasting, add_comm]

/-- The original real three-cell route equality is equivalent to its full generated differential equation. -/
theorem three_operation_iff (c : K.TwoCell → A) (s : K.ThreeCell) :
    pastingOperation K R c (K.threeLeft s) = pastingOperation K R c (K.threeRight s) ↔
      vectorPastingDifferential K R c s = 0 := by
  rw [pasting_operation_translation, pasting_operation_translation]
  change translation (k := k) (vectorPasting K R c (K.threeLeft s)) =
    translation (k := k) (vectorPasting K R c (K.threeRight s)) ↔
    vectorPasting K R c (K.threeLeft s) - vectorPasting K R c (K.threeRight s) = 0
  constructor
  · intro h
    have hv := congrArg (fun g : Operations k A => g 0) h
    simpa only [translation_apply, add_zero, sub_eq_zero] using hv
  · intro h
    rw [sub_eq_zero] at h
    rw [h]

/-- Reference translation updates preserve the real contribution of each original oriented whiskered face. -/
theorem translated_vector_face (h : EdgeName (K := K) → A) (c : K.TwoCell → A)
    {s t : K.Vertex} (f : WhiskeredFace K.toFiniteTransportTwoPresentation s t) :
    vectorFace K (translatedOperations K R h) c f = vectorFace K R c f := by
  cases ho : f.orientation <;>
    simp only [vectorFace, ho, translated_word_linear]

/-- Reference translation updates preserve every original occurrence in a complete typed pasting. -/
theorem translated_vector_pasting (h : EdgeName (K := K) → A) (c : K.TwoCell → A)
    {s t : K.Vertex} {w z : K.Path s t}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    vectorPasting K (translatedOperations K R h) c p = vectorPasting K R c p := by
  induction p with
  | nil _ => rfl
  | cons step tail ih =>
    change vectorFace K (translatedOperations K R h) c step.face +
      vectorPasting K (translatedOperations K R h) c tail = _
    rw [translated_vector_face, ih]
    rfl

/-- The full original comparison differential is independent of reference translations. -/
theorem translated_pasting_differential (h : EdgeName (K := K) → A) :
    vectorPastingDifferential K (translatedOperations K R h) = vectorPastingDifferential K R := by
  ext c s
  change vectorPasting K (translatedOperations K R h) c (K.threeLeft s) -
    vectorPasting K (translatedOperations K R h) c (K.threeRight s) = _
  rw [translated_vector_pasting, translated_vector_pasting]
  rfl

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
