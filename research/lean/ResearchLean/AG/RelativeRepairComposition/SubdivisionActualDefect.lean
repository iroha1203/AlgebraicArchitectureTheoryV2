import ResearchLean.AG.RelativeRepairComposition.SubdivisionCoefficientPaths
import ResearchLean.AG.RelativeRepairComposition.SubdivisionFixedLaws

/-!
# The original actual face defect under the same two-factor subdivision

The actual canonical comparison is forced by the same complete selected paths.
The authored comparison remains the original one. Their original ordered
quotient therefore defines the same element of the entire actual kernel.

## Implementation notes

Strong uniqueness compares the actual canonical morphisms before reading their
kernel difference. Assuming a defect correspondence would leave this material
condition undischarged; comparing only projections would lose kernel values.
The inclusion is injective on the full kernel, so the resulting equality retains
the original defect itself, including its sign in additive coordinates.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- The actual canonical face comparison factors its two complete selected reference paths. -/
theorem canonical_face_fac (f : K.TwoCell) :
    T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.toTower.canonicalFace f) =
      T.toTower.upper.pathLift (K.twoRight f) := by
  rw [T.toTower.canonicalFace_eq_initial]
  exact initialCanonicalFaceComparator_fac T.toTower.toTransportData f

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)

/-- The same complete actual selected paths force exactly the same full canonical comparison. -/
theorem canonical_face_substitute (f : K.TwoCell) :
    (originalTower T chosen F).toTower.canonicalFace f = T.toTower.canonicalFace f := by
  apply FiberAut.ext_of_strong_fac (T.toTower.upper.pathLift (K.twoLeft f))
    (T.toTower.upper.pathLift_isStronglyCocartesian (K.twoLeft f))
  have hn := canonical_face_fac (originalTower T chosen F) f
  change (originalTower T chosen F).toTower.upper.pathLift
      (substitutePath K chosen (K.twoLeft f)) ≫
      FiberAut.hom ((originalTower T chosen F).toTower.canonicalFace f) =
    (originalTower T chosen F).toTower.upper.pathLift
      (substitutePath K chosen (K.twoRight f)) at hn
  rw [originalTower_selected_path, originalTower_selected_path] at hn
  exact hn.trans (canonical_face_fac T f).symm

/-- The actual full-kernel face defect is literally the same original element. -/
theorem faceDefect_substitute (f : K.TwoCell) :
    (originalTower T chosen F).toTower.faceDefect f = T.toTower.faceDefect f := by
  apply kernelInclusion_injective p q (T.original.object (K.twoTarget f))
  let cn : FiberAut (p ⋙ q) (T.original.object (K.twoTarget f)) :=
    (originalTower T chosen F).toTower.canonicalFace f
  let co : FiberAut (p ⋙ q) (T.original.object (K.twoTarget f)) := T.toTower.canonicalFace f
  calc
    _ = T.comparator f * cn⁻¹ := (originalTower T chosen F).toTower.faceDefect_inclusion f
    _ = T.comparator f * co⁻¹ :=
      congrArg (fun a : FiberAut (p ⋙ q) (T.original.object (K.twoTarget f)) =>
        T.comparator f * a⁻¹) (canonical_face_substitute T chosen F f)
    _ = _ := (T.toTower.faceDefect_inclusion f).symm

/-- All original actual additive defect coordinates are preserved, without a preservation premise. -/
theorem defect_substitute :
    (originalTower T chosen F).toTower.defect = T.toTower.defect := by
  funext f
  exact congrArg (fun a : Kernel p q (T.original.object (K.twoTarget f)) => Additive.ofMul a)
    (faceDefect_substitute T chosen F f)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
