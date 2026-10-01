import ResearchLean.AG.RelativeRepairComposition.AffineContextInput
import ResearchLean.AG.RelativeRepairComposition.AffineEmbeddedPastings

/-!
# Shared primitive laws derived from the original whole actual input

The common W's alignment, complete three-cell law and fixed-face law are
obtained by reading the actual embedded original words. They are not additional
certificates passed to the contextual equivalence application.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {W : FiniteTransportPresentation.{uG}}
variable {LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k A}
variable {cW : W.TwoCell → A} {PW : ClosedRegion W} {CW : Set (EdgeName (K := W))}
variable (I : AffineContextInput W LW RW cW PW CW)
include I

/-- Actual face alignment of the whole input derives the original shared full linear face law. -/
theorem shared_aligned : ∀ f : W.TwoCell,
    (GroupExtension.pathValue W RW (W.twoLeft f)).linear =
      (GroupExtension.pathValue W RW (W.twoRight f)).linear := by
  intro f
  have hl := word_value_heq I.references (I.embedding.path (W.twoLeft f))
    (I.geometry.twoLeft (I.embedding.face f))
    (I.embedding.face_source f).symm (I.embedding.face_target f).symm (I.embedding.face_left f)
  have hr := word_value_heq I.references (I.embedding.path (W.twoRight f))
    (I.geometry.twoRight (I.embedding.face f))
    (I.embedding.face_source f).symm (I.embedding.face_target f).symm (I.embedding.face_right f)
  rw [embedded_reference_word I.embedding RW I.references I.shared_reference] at hl hr
  exact (congrArg AffineEquiv.linear hl).trans
    ((I.aligned (I.embedding.face f)).trans (congrArg AffineEquiv.linear hr).symm)

/-- All original shared three-cell laws follow through both complete mapped typed routes. -/
theorem shared_three_law : ∀ f : W.ThreeCell,
    pastingOperation W RW cW (W.threeLeft f) = pastingOperation W RW cW (W.threeRight f) :=
  embedded_three_law I.embedding RW I.references cW I.comparisons
    I.shared_reference I.shared_comparison I.three_law

/-- The shared physical fixed-face law is derived from its exact original whole fixed face. -/
theorem shared_fixed_law : ∀ f ∈ PW.faces,
    translation (k := k) (cW f) * GroupExtension.pathValue W RW (W.twoLeft f) =
      GroupExtension.pathValue W RW (W.twoRight f) := by
  intro f hf
  have hl := word_value_heq I.references (I.embedding.path (W.twoLeft f))
    (I.geometry.twoLeft (I.embedding.face f))
    (I.embedding.face_source f).symm (I.embedding.face_target f).symm (I.embedding.face_left f)
  have hr := word_value_heq I.references (I.embedding.path (W.twoRight f))
    (I.geometry.twoRight (I.embedding.face f))
    (I.embedding.face_source f).symm (I.embedding.face_target f).symm (I.embedding.face_right f)
  rw [embedded_reference_word I.embedding RW I.references I.shared_reference] at hl hr
  rw [hl,hr,← I.shared_comparison]
  exact I.fixed_faces (I.embedding.face f) ((I.shared_fixed_faces f).mpr hf)

end AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
