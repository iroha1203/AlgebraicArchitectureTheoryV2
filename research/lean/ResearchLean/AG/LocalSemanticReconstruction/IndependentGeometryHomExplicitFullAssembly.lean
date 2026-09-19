import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawComponents
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationComponents
import Formal.Util.AssertStandardAxioms

/-!
# Full explicit geometry Hom assembly from independent primitive data

Implementation notes: all six native geometry Hom components are constructed
on the same independently assembled source and target objects. Local laws
refer to primitive object stages and the retained common Hom points of the
invariant quotient. No completed native map or certificate is a local field.
The converse common reader and whole-Hom inverse proofs remain separate work.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.FullExplicit

noncomputable section

universe u v

open RealizationReconstruction IndependentGeometryTableAssembly GeometryComponents

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)

/-- Primitive point laws for every component of the original complete explicit geometry Hom. -/
structure PointLaws : Prop where
  /-- All core maps are built from primitive preservation laws and the invariant quotient. -/
  package : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table
  /-- The nine original coverage implications. -/
  coverage : CoveragePoints s t p
  /-- Both overlap order comparisons at primitive context points. -/
  overlap : OverlapPoints s t p
  /-- Directed coefficient graph and primitive ring-operation preservation. -/
  coefficient : CoefficientPoints s t p
  /-- Independent raw inverse graphs and finite sparse polynomial comparisons. -/
  raw : ExplicitRawPoints s t p
  /-- Independent fiber equivalences and all actual context-action point laws. -/
  realization : ExplicitPoints s t p

/-- Assemble every native field of the full explicit geometry Hom from independent local data. -/
def assembleHom (hp : PointLaws s t p) : ExplicitExactGeometryHom (assemble s) (assemble t) where
  base := base s t p hp.package
  coverage := GeometryComponents.coverage s t p hp.package hp.coverage
  overlap := GeometryComponents.overlap s t p hp.package hp.overlap
  coefficientHom := coefficientMap s t p hp.coefficient
  raw := explicitRaw s t p hp.package hp.coefficient hp.raw
  realization := explicitRealization s t p hp.package hp.realization

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.FullExplicit

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.FullExplicit
