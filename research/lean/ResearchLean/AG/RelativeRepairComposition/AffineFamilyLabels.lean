import ResearchLean.AG.RelativeRepairComposition.AffineTranslationWords
import ResearchLean.AG.RelativeRepairComposition.NativeAffineGaugeLabels

/-!
# The entire original real gauge subgroup is reused under value updates

## Implementation notes

Every original vertex vector, its fixed-vertex zero condition and all fixed-edge
linear transport conditions are retained. Reference translation updates change
no one of these conditions. The equality concerns the full subgroup of labels,
including all nonzero labels that act as stabilizers.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)

/-- Every full original gauge-label subgroup is identical after translating primitive reference values, for any fixed vertices and edges. -/
theorem translated_gauge_labels (h : EdgeName (K := K) → A)
    (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    gaugeLabels K (translatedOperations K R h) vertices fixed = gaugeLabels K R vertices fixed := by
  apply AddSubgroup.ext
  intro b
  change ((∀ v ∈ vertices, b v = 0) ∧ ∀ e ∈ fixed,
      b e.2.1 = (translatedOperations K R h e.2.2).linear (b e.1)) ↔
    ((∀ v ∈ vertices, b v = 0) ∧ ∀ e ∈ fixed, b e.2.1 = (R e.2.2).linear (b e.1))
  simp only [translated_linear]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
