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

@[simp] theorem equationSystem_index
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc) :
    (equationSystem t ha A hA hc he).Index =
      IndependentEquationPrimitive.index (equationRows t ha A hA) := rfl

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

/-- Closed formula for the activation condition of one coverage row.  Required
equation queries read the exact role cell; the remaining guarded queries use
the selected index or axis cell named by `activeAnchor`. -/
noncomputable def activationFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (q : IndependentCoveragePrimitive.Query A) : ObjectFormula.{u, v, 0} U := by
  classical
  exact activeAnchor t ha A hA q <| match q with
    | .requiredEquation I i _
    | .equationVisible _ I i _ =>
        if _hI : I = IndependentEquationPrimitive.index (equationRows t ha A hA) then
          Equation.roleTypedFormula t ha A hA I i (some .required)
        else .falsity
    | .selectedWitness I _ _
    | .witnessVisible _ I _ _ =>
        if _hI : I = IndependentEquationPrimitive.index (equationRows t ha A hA) then
          .truth
        else .falsity
    | .requiredAxis I _
    | .axisReadable _ I _ =>
        if _hI : I = (IndependentGeometryPrimitive.assembledSignature t hf).Axis then
          .truth
        else .falsity
    | .requiredSupport _
    | .supportVisible _ _
    | .boundaryVisible _ _ => .truth

@[simp] theorem requiredRoleFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) :
    (Equation.roleTypedFormula t ha A hA _ i (some .required)).evaluate t ↔
      (equationSystem t ha A hA hc he).Required i := by
  simp only [Equation.roleTypedFormula, equationAnchor_evaluate]
  rw [equationCell_evaluate_iff t ha A hA]
  let row := (equationRows t ha A hA (.role
    (IndependentEquationPrimitive.index (equationRows t ha A hA)) i)).down
  have hr : row.isSome := (he.choose.role _ i).2 rfl
  change equationRows t ha A hA (.role _ i) = ULift.up (some .required) ↔
    row.get hr = .required
  constructor
  · intro h
    have h' := congrArg ULift.down h
    exact Option.some.inj ((Option.some_get hr).trans h')
  · intro h
    apply ULift.ext
    exact (Option.some_get hr).symm.trans (congrArg some h)

@[simp] theorem activationFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (q : IndependentCoveragePrimitive.Query A) :
    (activationFormula t ha A hA hf hc he q).evaluate t ↔
      IndependentCoveragePrimitive.Active
        (equationSystem t ha A hA hc he)
        (IndependentGeometryPrimitive.assembledSignature t hf) q := by
  classical
  cases q with
  | requiredSupport a =>
      simp [activationFormula, IndependentCoveragePrimitive.Active, ObjectFormula.evaluate]
  | requiredEquation I i a =>
      by_cases hI : I = IndependentEquationPrimitive.index (equationRows t ha A hA)
      · subst I
        simpa [activationFormula, IndependentCoveragePrimitive.Active,
          equationSystem_index, ObjectFormula.evaluate] using
          (requiredRoleFormula_evaluate t ha A hA hc he i)
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
  | selectedWitness I i a =>
      by_cases hI : I = IndependentEquationPrimitive.index (equationRows t ha A hA)
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
  | requiredAxis I i =>
      by_cases hI : I = (IndependentGeometryPrimitive.assembledSignature t hf).Axis
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
  | supportVisible W a =>
      simp [activationFormula, IndependentCoveragePrimitive.Active, ObjectFormula.evaluate]
  | equationVisible W I i a =>
      by_cases hI : I = IndependentEquationPrimitive.index (equationRows t ha A hA)
      · subst I
        simpa [activationFormula, IndependentCoveragePrimitive.Active,
          equationSystem_index, ObjectFormula.evaluate] using
          (requiredRoleFormula_evaluate t ha A hA hc he i)
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
  | witnessVisible W I i a =>
      by_cases hI : I = IndependentEquationPrimitive.index (equationRows t ha A hA)
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
  | axisReadable W I i =>
      by_cases hI : I = (IndependentGeometryPrimitive.assembledSignature t hf).Axis
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
      · simp [activationFormula, IndependentCoveragePrimitive.Active, hI,
          ObjectFormula.evaluate]
  | boundaryVisible W V =>
      simp [activationFormula, IndependentCoveragePrimitive.Active, ObjectFormula.evaluate]

def pointFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (_hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (q : IndependentCoveragePrimitive.Query A) : ObjectFormula.{u, v, 0} U :=
  .and (ObjectMatchingFinite.matchCell (.object A) true)
    (.implies
      (.cell (.atObject A (.coverage q)) (some (ULift.up True)))
      (activationFormula t ha A hA _hf hc _he q))

@[simp] theorem pointFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (q : IndependentCoveragePrimitive.Query A) :
    (pointFormula t ha A hA hf hc he q).evaluate t ↔
      (coverageRows t ha A hA q →
        IndependentCoveragePrimitive.Active
          (equationSystem t ha A hA hc he)
          (IndependentGeometryPrimitive.assembledSignature t hf) q) := by
  simp only [pointFormula, ObjectFormula.evaluate,
    ObjectMatchingFinite.matchCell_evaluate, hA, true_and,
    activationFormula_evaluate]
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA (.coverage q)]
  constructor
  · intro h hq
    apply h
    congr 2
    apply ULift.ext
    exact propext (iff_true_intro hq)
  · intro h hq
    apply h
    have h' := Option.some.inj hq
    have h'' := congrArg ULift.down h'
    exact (eq_iff_iff.1 h'').2 True.intro

def Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc) : Prop :=
  ∀ q, (pointFormula t ha A hA hf hc he q).evaluate t

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
  · intro hl q
    exact (pointFormula_evaluate t ha A hA hf hc he q).2 (hl q)
  · intro hi q
    exact (pointFormula_evaluate t ha A hA hf hc he q).1 (hi q)

end Coverage

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
