import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullTableComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullSeparation
import Formal.Util.AssertStandardAxioms

/-!
# Primitive table composition compared with complete native Hom composition

The previously constructed point tables are compared with the original full
Hom composites, retaining every core, coefficient, raw, and realization field.
Full input point laws supply the original complete assemblers for this proof;
they do not change the primitive table construction.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t r : ObjectData.{u, v} U)

/-- All directly composed representative points read the original complete geometry Hom composite. -/
theorem composeRepresentative_eq_full_native
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
    (hp : FullRepresentative.PointLaws s t p)
    (q : InvariantWitness.Local.{u, v}
      (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .representative)
    (hq : FullRepresentative.PointLaws t r q) :
    composeRepresentative s t r p hp.package q hq.package hp.realization hp.coefficient =
      NativeReader.readRepresentative
        (GeometryTotalHom.comp (FullRepresentative.assembleHom s t p hp) (FullRepresentative.assembleHom t r q hq)) := by
  refine (composeRepresentative_eq_native s t r p hp.package q hq.package
    hp.realization hq.realization hp.coefficient hq.coefficient).trans ?_
  change NativeReader.readWith .representative _ _ _ _ = NativeReader.readWith .representative _ _ _ _
  congr 1
  funext a
  cases a

/-- All directly composed explicit points read the original full Hom composite, including actual context actions. -/
theorem composeExplicit_eq_full_native
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
    (hp : FullExplicit.PointLaws s t p)
    (q : InvariantWitness.Local.{u, v}
      (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
    (hq : FullExplicit.PointLaws t r q) :
    composeExplicit s t r p hp.package q hq.package hp.raw hq.raw hp.realization hq.realization hp.coefficient =
      NativeReader.readExplicit
        (ExplicitExactGeometryHom.comp (FullExplicit.assembleHom s t p hp) (FullExplicit.assembleHom t r q hq)) :=
  composeExplicit_eq_native s t r p hp.package q hq.package hp.raw hq.raw
    hp.realization hq.realization hp.coefficient hq.coefficient

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
