import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectDependentEquationLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for active-object circuit laws

Circuit activation names the equation-index row and the exact finite-code row.
Each soundness witness also names the residual coordinate and observable zero
used by its nonvanishing check.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

noncomputable section

universe u v w

open Site IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}}

namespace Circuit

abbrev circuitRows (t : IndependentGeometryPrimitive.Table.{u, v} U) :=
  IndependentGeometryPrimitive.circuit t

def circuitCell (q : IndependentEquationPrimitive.Circuit.Query.{u})
    (value : Option (CircuitDetectorCode U)) : ObjectFormula.{u, v, w} U :=
  .cell (.circuit q) (ULift.up value)

theorem circuitCell_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentEquationPrimitive.Circuit.Query.{u})
    (value : Option (CircuitDetectorCode U)) :
    (circuitCell q value : ObjectFormula.{u, v, w} U).evaluate t ↔
      circuitRows t q = value := by
  change t (.circuit q) = ULift.up value ↔ (t (.circuit q)).down = value
  constructor
  · exact fun h => congrArg ULift.down h
  · exact fun h => ULift.ext _ _ h

def circuitAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentEquationPrimitive.Circuit.Query.{u})
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (.cell (.circuit q) (t (.circuit q))) body

@[simp] theorem circuitAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentEquationPrimitive.Circuit.Query.{u})
    (body : ObjectFormula.{u, v, w} U) :
    (circuitAnchor t q body).evaluate t ↔ body.evaluate t := by
  simp [circuitAnchor, ObjectFormula.evaluate]

def typedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (J : Type u) (j : J) : ObjectFormula.{u, v, 0} U :=
  equationAnchor t ha A hA .index
    (circuitAnchor t (.code J j)
      (.equal ((circuitRows t (.code J j)).isSome = true)
        (J = IndependentEquationPrimitive.index (equationRows t ha A hA))))

def TypedInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop :=
  ∀ J j, (typedFormula t ha A hA J j).evaluate t

theorem typed_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :
    IndependentEquationPrimitive.Circuit.IsTyped
        (IndependentEquationPrimitive.index (equationRows t ha A hA)) (circuitRows t) ↔
      TypedInstances t ha A hA := by
  constructor
  · intro ht J j
    simp only [typedFormula, equationAnchor_evaluate, circuitAnchor_evaluate,
      ObjectFormula.evaluate]
    exact propext (ht J j)
  · intro hi J j
    have h := hi J j
    simp only [typedFormula, equationAnchor_evaluate, circuitAnchor_evaluate,
      ObjectFormula.evaluate] at h
    exact eq_iff_iff.1 h

def witnessFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA))
    (hct : IndependentEquationPrimitive.Circuit.IsTyped
      (IndependentEquationPrimitive.index (equationRows t ha A hA)) (circuitRows t))
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA))
    (B : ArchitectureObject U) (d : FiniteCircuitDatum U) (W : ArchCtx A) (a : U.Atom) :
    ObjectFormula.{u, v, u} U :=
  equationAnchor t ha A hA .index
    (circuitAnchor t (.code _ i)
      (Equation.residualAnchor t ha A hA hc ht W B i a
        (Equation.observableActiveAnchor t ha A hA hc ht W .zero
          (.and
            (.equal (ULift.up (d.Matches B) : ULift.{u} Prop) (ULift.up True))
            (.and
              (.equal
                (ULift.up
                  ((IndependentEquationPrimitive.Circuit.code (circuitRows t) hct i).eval d) :
                    ULift.{u} Bool)
                (ULift.up true))
              (.notEqual (Equation.residualValue t ha A hA hc ht W B i a)
                (Equation.observableActive t ha A hA hc ht W .zero)))))))

def LawInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA))
    (hct : IndependentEquationPrimitive.Circuit.IsTyped
      (IndependentEquationPrimitive.index (equationRows t ha A hA)) (circuitRows t)) : Prop :=
  ∀ (i : IndependentEquationPrimitive.index (equationRows t ha A hA))
    (B : ArchitectureObject U) (d : FiniteCircuitDatum U),
    d.Matches B →
    (IndependentEquationPrimitive.Circuit.code (circuitRows t) hct i).eval d = true →
      ∃ (W : ArchCtx A) (a : U.Atom),
        (witnessFormula t ha A hA hc ht hct i B d W a).evaluate t

theorem lawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA))
    (hct : IndependentEquationPrimitive.Circuit.IsTyped
      (IndependentEquationPrimitive.index (equationRows t ha A hA)) (circuitRows t)) :
    IndependentEquationPrimitive.Circuit.IsLawful
        (equationRows t ha A hA) ht (circuitRows t) hct ↔
      LawInstances t ha A hA hc ht hct := by
  constructor
  · intro hl i B d hm he
    obtain ⟨W, a, hn⟩ := hl i B d hm he
    refine ⟨W, a, ?_⟩
    simp only [witnessFormula, equationAnchor_evaluate, circuitAnchor_evaluate,
      Equation.residualAnchor_evaluate, Equation.observableActiveAnchor_evaluate,
      ObjectFormula.evaluate]
    exact ⟨ULift.ext _ _ (eq_true hm), ULift.ext _ _ he, hn⟩
  · intro hi i B d hm he
    obtain ⟨W, a, hw⟩ := hi i B d hm he
    refine ⟨W, a, ?_⟩
    simp only [witnessFormula, equationAnchor_evaluate, circuitAnchor_evaluate,
      Equation.residualAnchor_evaluate, Equation.observableActiveAnchor_evaluate,
      ObjectFormula.evaluate] at hw
    exact hw.2.2

structure Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) : Prop where
  typed : TypedInstances t ha A hA
  lawful : LawInstances t ha A hA hc ht ((typed_iff_instances t ha A hA).2 typed)

theorem typedLawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) :
    (∃ hct : IndependentEquationPrimitive.Circuit.IsTyped
        (IndependentEquationPrimitive.index (equationRows t ha A hA)) (circuitRows t),
      IndependentEquationPrimitive.Circuit.IsLawful
        (equationRows t ha A hA) ht (circuitRows t) hct) ↔
      Instances t ha A hA hc ht := by
  constructor
  · rintro ⟨hct, hl⟩
    let hi := (typed_iff_instances t ha A hA).1 hct
    refine ⟨hi, ?_⟩
    apply (lawful_iff_instances t ha A hA hc ht
      ((typed_iff_instances t ha A hA).2 hi)).1
    simpa only [Subsingleton.elim hct ((typed_iff_instances t ha A hA).2 hi)] using hl
  · rintro ⟨hct, hl⟩
    exact ⟨(typed_iff_instances t ha A hA).2 hct,
      (lawful_iff_instances t ha A hA hc ht _).2 hl⟩

end Circuit

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
