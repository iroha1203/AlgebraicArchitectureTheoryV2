import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectDependentCircuitLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for active-object coverage laws

Each coverage implication anchors its predicate row.  Carrier- and role-sensitive
queries additionally anchor the equation index, equation role, or signature axis
from which their activation condition is computed.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

noncomputable section

universe u v w

open Site IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}}

namespace Coverage

abbrev coverageRows
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :=
  IndependentGeometryPrimitive.coverageTable (rows t ha A hA)

abbrev equationSystem
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc) :=
  IndependentCoreTableAssembly.equation
    (IndependentGeometryPrimitive.equationData (rows t ha A hA) hc he)

def coverageAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentCoveragePrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (ObjectMatchingFinite.matchCell (.object A) true)
    (.and (.cell (.atObject A (.coverage q))
      (some ((rows t ha A hA) (.coverage q)))) body)

@[simp] theorem coverageAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentCoveragePrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) :
    (coverageAnchor t ha A hA q body).evaluate t ↔ body.evaluate t := by
  simp only [coverageAnchor, ObjectFormula.evaluate,
    ObjectMatchingFinite.matchCell_evaluate, hA, true_and]
  exact and_iff_right
    (IndependentGeometryPrimitive.some_dependent t ha A hA (.coverage q)).symm

def signatureAxisAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (.cell (.signature .axis) (t (.signature .axis))) body

@[simp] theorem signatureAxisAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, w} U) :
    (signatureAxisAnchor t body).evaluate t ↔ body.evaluate t := by
  simp [signatureAxisAnchor, ObjectFormula.evaluate]

def activeAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentCoveragePrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  match q with
  | .requiredEquation I i _
  | .equationVisible _ I i _ =>
      equationAnchor t ha A hA .index
        (equationAnchor t ha A hA (.role I i) body)
  | .selectedWitness _ _ _
  | .witnessVisible _ _ _ _ => equationAnchor t ha A hA .index body
  | .requiredAxis _ _
  | .axisReadable _ _ _ => signatureAxisAnchor t body
  | .requiredSupport _
  | .supportVisible _ _
  | .boundaryVisible _ _ => body

@[simp] theorem activeAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentCoveragePrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) :
    (activeAnchor t ha A hA q body).evaluate t ↔ body.evaluate t := by
  cases q <;> simp [activeAnchor]

def pointFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (_hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (q : IndependentCoveragePrimitive.Query A) : ObjectFormula.{u, v, 0} U :=
  .and (ObjectMatchingFinite.matchCell (.object A) true)
    (activeAnchor t ha A hA q
      (.cell (.atObject A (.coverage q)) (some (ULift.up True))))

@[simp] theorem pointFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (q : IndependentCoveragePrimitive.Query A) :
    (pointFormula t ha A hA hf hc he q).evaluate t ↔
      coverageRows t ha A hA q := by
  simp only [pointFormula, ObjectFormula.evaluate,
    ObjectMatchingFinite.matchCell_evaluate, hA, true_and,
    activeAnchor_evaluate]
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA (.coverage q)]
  constructor
  · intro h
    have h' := Option.some.inj h
    have h'' := congrArg ULift.down h'
    exact (eq_iff_iff.1 h'').2 True.intro
  · intro h
    congr 2
    apply ULift.ext
    exact propext (iff_true_intro h)

def Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc) : Prop :=
  ∀ q, (pointFormula t ha A hA hf hc he q).evaluate t →
    IndependentCoveragePrimitive.Active
      (equationSystem t ha A hA hc he)
      (IndependentGeometryPrimitive.assembledSignature t hf) q

theorem coverageLaws_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc) :
    IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he ↔
      Instances t ha A hA hf hc he := by
  constructor
  · intro hl q hq
    exact hl q ((pointFormula_evaluate t ha A hA hf hc he q).1 hq)
  · intro hi q hq
    exact hi q ((pointFormula_evaluate t ha A hA hf hc he q).2 hq)

end Coverage

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
