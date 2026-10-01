import ResearchLean.AG.RelativeRepairComposition.AffinePrimitiveFamily
import ResearchLean.AG.RelativeRepairComposition.AffineComparisonWords
import ResearchLean.AG.RelativeRepairComposition.NativeAffineRanges

/-!
# Input laws generate every parameter's original affine law

## Implementation notes

The base primitive route equalities and the linear comparison annihilator imply
the whole family's three-cell law. The base physical fixed-face equality and the
generated defect annihilator imply its fixed-face law. These conditions concern
only the original affine inputs and parameter maps, before any repair is sought.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG uV
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (θL θR : V →ₗ[k] (EdgeName (K := K) → A)) (η : V →ₗ[k] (K.TwoCell → A))

/-- The full primitive face residual is the translation by its independently evaluated defect vector. -/
theorem face_residual_translation (f : K.TwoCell)
    (hf : (GroupExtension.pathValue K R (K.twoLeft f)).linear =
      (GroupExtension.pathValue K R (K.twoRight f)).linear) :
    translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) *
      (GroupExtension.pathValue K R (K.twoRight f))⁻¹ =
        translation (k := k) (realDefectVector K R c f) := by
  rw [real_defect_residual, mul_assoc, reference_word_quotient K R f hf, translation_mul]
  simp only [translation_apply, add_zero]

/-- Primitive fixed-face coherence is equivalent to its actual full defect value being zero. -/
theorem face_coherent_iff_defect_zero (f : K.TwoCell)
    (hf : (GroupExtension.pathValue K R (K.twoLeft f)).linear =
      (GroupExtension.pathValue K R (K.twoRight f)).linear) :
    translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
      GroupExtension.pathValue K R (K.twoRight f) ↔ realDefectVector K R c f = 0 := by
  constructor
  · intro h
    have he := face_residual_translation K R c f hf
    rw [h, mul_inv_cancel] at he
    have hv := congrArg (fun g : Operations k A => g 0) he
    change 0 = realDefectVector K R c f + 0 at hv
    simpa only [add_zero] using hv.symm
  · intro h
    have he := face_residual_translation K R c f hf
    rw [h, translation_zero] at he
    exact (mul_inv_eq_one.mp he)

/-- Base original route laws and the full linear comparison annihilator generate every parameter's actual three-cell laws. -/
theorem family_three_law
    (hthree : ∀ s : K.ThreeCell,
      pastingOperation K R c (K.threeLeft s) = pastingOperation K R c (K.threeRight s))
    (hη : (vectorPastingDifferential K R).comp η = 0) (v : V) (s : K.ThreeCell) :
    pastingOperation K (familyReference K R θR v) (familyComparisons K c η v) (K.threeLeft s) =
      pastingOperation K (familyReference K R θR v) (familyComparisons K c η v) (K.threeRight s) := by
  apply (three_operation_iff _ _ _ s).mpr
  unfold familyReference familyComparisons
  rw [translated_pasting_differential, map_add]
  have hbase := (three_operation_iff K R c s).mp (hthree s)
  have hparam := congrArg (fun F : V →ₗ[k] (K.ThreeCell → A) => F v s) hη
  change (vectorPastingDifferential K R) c s + (vectorPastingDifferential K R) (η v) s = 0
  change (vectorPastingDifferential K R) (η v) s = 0 at hparam
  rw [hbase, hparam, add_zero]

/-- Base fixed-face coherence and the generated defect annihilator generate every parameter's actual fixed-face law. -/
theorem family_fixed_face
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear)
    (fixedFaces : Set K.TwoCell)
    (hfixed : ∀ f ∈ fixedFaces,
      translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
        GroupExtension.pathValue K R (K.twoRight f))
    (hB : ∀ v : V, ∀ f ∈ fixedFaces, familyDefectLinear K R θR η v f = 0)
    (v : V) (f : K.TwoCell) (hf : f ∈ fixedFaces) :
    translation (k := k) (familyComparisons K c η v f) *
      GroupExtension.pathValue K (familyReference K R θR v) (K.twoLeft f) =
        GroupExtension.pathValue K (familyReference K R θR v) (K.twoRight f) := by
  apply (face_coherent_iff_defect_zero _ _ _ f (family_aligned K R θR hfaces v f)).mpr
  rw [family_defect_affine K R c θR η hfaces v f,
    (face_coherent_iff_defect_zero K R c f (hfaces f)).mp (hfixed f hf), hB v f hf, add_zero]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
