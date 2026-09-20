import ResearchLean.AG.LocalSemanticReconstruction.IndependentPolynomialCoefficientPoints
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawCandidateReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentContextPrimitiveReadings
import Formal.Util.AssertStandardAxioms

/-!
# Representative raw laws on primitive object and Hom responses

Implementation notes: representative transport preserves coordinate, relation,
label, and local-data declarations literally. Sparse polynomial responses use
equal presence flags and coefficient graph points. The image clause is guarded
by one primitive target refinement response, so no actual site arrow is needed
in the local law. Coefficient references come from primitive carrier/zero data.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRaw

noncomputable section

universe u v

open Site

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U}

/-- Representative raw transport is also indexed by the primitive inverse context points. -/
def contextPoints (h : Table.{u, v} U .representative) (W : ArchCtx A) (V : ArchCtx B) : Bool :=
  h (.atObjects A B (.context .backward W V))

/-- All representative raw rules compare primitive responses and directed coefficient points. -/
structure PointLaws (s : IndependentRawCandidate.Table.{u, v} A)
    (t : IndependentRawCandidate.Table.{u, v} B) (ct : IndependentContextPrimitive.Table B)
    (rk rl : IndependentRawCandidate.CoefficientRef.{v}) (h : Table.{u, v} U .representative) : Prop where
  /-- Raw coordinate carriers are literally preserved at inverse context pairs. -/
  coordinate : ∀ W V, contextPoints h W V = true → (s (.coordinate W)).down = (t (.coordinate V)).down
  /-- Raw relation carriers are literally preserved at the same context pairs. -/
  relation : ∀ W V, contextPoints h W V = true → (s (.relation W)).down = (t (.relation V)).down
  /-- Each candidate label response, including inactivity, is preserved. -/
  label : ∀ W V C (c : C), contextPoints h W V = true → (s (.label W C c)).down = (t (.label V C c)).down
  /-- Each dependent local-data carrier response, including inactivity, is preserved. -/
  localData : ∀ W V C (c : C), contextPoints h W V = true →
    (s (.localData W C c)).down = (t (.localData V C c)).down
  /-- Relation polynomials preserve presence and every coefficient at the original coordinate names. -/
  polynomial : ∀ W V C I (i : I), contextPoints h W V = true →
    IndependentPolynomialCoefficientPoints.OptionalPoints
      (fun a b => h (.coefficient (.edge rk.1 rl.1 a b)))
      (s (.polynomial W C I rk i)).down (t (.polynomial V C I rl i)).down
  /-- On each readable target pair, variable images preserve presence and every coefficient. -/
  image : ∀ W X V Y C D (d : D), contextPoints h W V = true → contextPoints h X Y = true →
    (ct (.le V Y)).down → IndependentPolynomialCoefficientPoints.OptionalPoints
      (fun a b => h (.coefficient (.edge rk.1 rl.1 a b)))
      (s (.image W X C D rk d)).down (t (.image V Y C D rl d)).down

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRaw
