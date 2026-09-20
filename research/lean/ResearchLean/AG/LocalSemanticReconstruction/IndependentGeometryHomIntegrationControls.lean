import ResearchLean.AG.LocalSemanticReconstruction.IndependentHomRefutations
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullSeparation
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOverlapLaws
import Formal.Util.AssertStandardAxioms

/-!
# Integrated controls for complete primitive geometry Homs

Concrete coefficient-changing Homs exercise common-query separation, and a
one-sided overlap mutation exercises the common overlap point law.

Implementation notes: existing rejected fixtures remain in their component
modules. This file adds only the missing complete-Hom and overlap connections;
it does not duplicate the earlier counterexamples or add a testing wrapper.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations

noncomputable section

universe u v

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction LawAlgebra Site
open IndependentGeometryTableAssembly
open IndependentGeometryHomPrimitive

variable {U : AtomCarrier.{u}}

/-- Projection onto the second integer factor. -/
def secondProjection : (ℤ × ℤ) →+* ℤ := RingHom.snd ℤ ℤ

/-- The two explicit coefficient-change Homs have the same object action but
different coefficient maps. -/
theorem explicit_projection_homs_distinct (P : AATCorePackage U)
    (g : SelectedGeometryReading P) :
    explicitCoefficientHom P g projection ≠
      explicitCoefficientHom P g secondProjection := by
  intro h
  have hv := congrArg (fun f => f.coefficientHom (1, 0)) h
  change (1 : ℤ) = 0 at hv
  exact one_ne_zero hv

/-- The representative coefficient-change Homs also have the same object
action but different coefficient maps. -/
theorem representative_projection_homs_distinct (P : AATCorePackage U)
    (g : SelectedGeometryReading P) :
    representativeCoefficientHom P g projection ≠
      representativeCoefficientHom P g secondProjection := by
  intro h
  have hv := congrArg (fun f => f.geometry.coefficientHom (1, 0)) h
  change (1 : ℤ) = 0 at hv
  exact one_ne_zero hv

/-- Regard a coefficient-change Hom on the exact primitive object readings of
its two endpoints. -/
def explicitCoefficientHomOnRead (P : AATCorePackage U)
    (g : SelectedGeometryReading P) (h : (ℤ × ℤ) →+* ℤ) :
    ExplicitExactGeometryHom
      (assemble (read (unitPackage P g (ℤ × ℤ))))
      (assemble (read (unitPackage P g ℤ))) := by
  rw [assemble_read, assemble_read]
  exact explicitCoefficientHom P g h

/-- Regard a representative coefficient-change Hom on the exact primitive
object readings of its two endpoints. -/
def representativeCoefficientHomOnRead (P : AATCorePackage U)
    (g : SelectedGeometryReading P) (h : (ℤ × ℤ) →+* ℤ) :
    GeometryTotalHom
      (assemble (read (unitPackage P g (ℤ × ℤ))))
      (assemble (read (unitPackage P g ℤ))) := by
  rw [assemble_read, assemble_read]
  exact representativeCoefficientHom P g h

/-- A concrete common explicit query separates two Homs with identical object
action and different coefficient behavior. -/
theorem explicit_projection_homs_distinct_query (P : AATCorePackage U)
    (g : SelectedGeometryReading P) :
    ∃ q, IndependentGeometryHomPrimitive.NativeReader.readExplicit
        (explicitCoefficientHomOnRead P g projection) q ≠
      IndependentGeometryHomPrimitive.NativeReader.readExplicit
        (explicitCoefficientHomOnRead P g secondProjection) q := by
  apply IndependentGeometryHomPrimitive.NativeReader.explicit_distinct_query
  intro h
  apply explicit_projection_homs_distinct P g
  simpa [explicitCoefficientHomOnRead] using h

/-- A concrete common representative query separates the same two directed
coefficient changes. -/
theorem representative_projection_homs_distinct_query (P : AATCorePackage U)
    (g : SelectedGeometryReading P) :
    ∃ q, IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        (representativeCoefficientHomOnRead P g projection) q ≠
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        (representativeCoefficientHomOnRead P g secondProjection) q := by
  apply IndependentGeometryHomPrimitive.NativeReader.representative_distinct_query
  intro h
  apply representative_projection_homs_distinct P g
  simpa [representativeCoefficientHomOnRead] using h

end

end AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Overlap

noncomputable section

universe u v

open Site AtomFoundation

variable {U : AtomCarrier.{u}} {mode : Mode} {A B : ArchitectureObject U}

/-- If all overlap guards fire, changing only one required target order cell
to false is rejected even when the opposite order cell remains true. -/
theorem one_sided_order_rejected
    (s : IndependentOverlapCandidate.Table A)
    (t : IndependentOverlapCandidate.Table B)
    (d : IndependentContextPrimitive.Table B)
    (h : Table.{u, v} U mode)
    (W X Y R : ArchCtx A) (base left right S T : ArchCtx B)
    (hW : h (.atObjects A B (.context .backward W base)) = true)
    (hX : h (.atObjects A B (.context .backward X left)) = true)
    (hY : h (.atObjects A B (.context .backward Y right)) = true)
    (hR : (s (.matching W X Y R)).down = true)
    (hS : (t (.matching base left right S)).down = true)
    (hT : h (.atObjects A B (.context .forward R T)) = true)
    (hleft : (d (.le T S)).down)
    (hright : ¬ (d (.le S T)).down) :
    (d (.le T S)).down ∧ ¬ PointLaws s t d h := by
  refine ⟨hleft, ?_⟩
  intro hp
  exact hright (hp W X Y base left right R S T hW hX hY hR hS hT).2

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Overlap

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Overlap
