import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullLocalComposition
import Formal.Util.AssertStandardAxioms

/-!
# Native composition compatibility and local associativity

The local operations were constructed from primitive points and coherent
auxiliary rows. Their complete native comparison now proves compatibility
with every original Hom and the associativity law on the local quotient.
All computational roles participate through the full reading equivalences.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t r z : ObjectData.{u, v} U)

/-- Reading arbitrary original representative Homs commutes with the primitive local composite. -/
theorem representativeLocal_read_comp
    (F : GeometryTotalHom (assemble s) (assemble t)) (G : GeometryTotalHom (assemble t) (assemble r)) :
    representativeLocal s t r (NativeReader.localRepresentative F) (NativeReader.localRepresentative_points s t F)
      (NativeReader.localRepresentative G) (NativeReader.localRepresentative_points t r G) =
      NativeReader.localRepresentative (GeometryTotalHom.comp F G) := by
  rw [representativeLocal_eq_native, NativeReader.localRepresentative_assemble, NativeReader.localRepresentative_assemble]

/-- Primitive representative local composition is associative on all lawful local classes. -/
theorem representativeLocal_assoc
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
    (hp : FullRepresentative.PointLaws s t p)
    (q : InvariantWitness.Local.{u, v}
      (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .representative)
    (hq : FullRepresentative.PointLaws t r q)
    (w : InvariantWitness.Local.{u, v}
      (assemble r).core.reading.invariantReading (assemble z).core.reading.invariantReading .representative)
    (hw : FullRepresentative.PointLaws r z w) :
    representativeLocal s r z (representativeLocal s t r p hp q hq) (representativeLocal_points s t r p hp q hq) w hw =
      representativeLocal s t z p hp (representativeLocal t r z q hq w hw) (representativeLocal_points t r z q hq w hw) := by
  simp only [representativeLocal_eq_native, NativeReader.localRepresentative_assemble]
  exact congrArg NativeReader.localRepresentative
    (@Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      (assemble s) (assemble t) (assemble r) (assemble z)
      (FullRepresentative.assembleHom s t p hp) (FullRepresentative.assembleHom t r q hq)
      (FullRepresentative.assembleHom r z w hw))

/-- Reading arbitrary original explicit Homs commutes with the primitive local composite. -/
theorem explicitLocal_read_comp
    (F : ExplicitExactGeometryHom (assemble s) (assemble t)) (G : ExplicitExactGeometryHom (assemble t) (assemble r)) :
    explicitLocal s t r (NativeReader.localExplicit F) (NativeReader.localExplicit_points s t F)
      (NativeReader.localExplicit G) (NativeReader.localExplicit_points t r G) =
      NativeReader.localExplicit (ExplicitExactGeometryHom.comp F G) := by
  rw [explicitLocal_eq_native, NativeReader.localExplicit_assemble, NativeReader.localExplicit_assemble]

/-- Primitive explicit local composition is associative on all lawful local classes. -/
theorem explicitLocal_assoc
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
    (hp : FullExplicit.PointLaws s t p)
    (q : InvariantWitness.Local.{u, v}
      (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
    (hq : FullExplicit.PointLaws t r q)
    (w : InvariantWitness.Local.{u, v}
      (assemble r).core.reading.invariantReading (assemble z).core.reading.invariantReading .explicit)
    (hw : FullExplicit.PointLaws r z w) :
    explicitLocal s r z (explicitLocal s t r p hp q hq) (explicitLocal_points s t r p hp q hq) w hw =
      explicitLocal s t z p hp (explicitLocal t r z q hq w hw) (explicitLocal_points t r z q hq w hw) := by
  simp only [explicitLocal_eq_native, NativeReader.localExplicit_assemble]
  exact congrArg NativeReader.localExplicit
    (ExplicitExactGeometryHom.comp_assoc (FullExplicit.assembleHom s t p hp)
      (FullExplicit.assembleHom t r q hq) (FullExplicit.assembleHom r z w hw))

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
