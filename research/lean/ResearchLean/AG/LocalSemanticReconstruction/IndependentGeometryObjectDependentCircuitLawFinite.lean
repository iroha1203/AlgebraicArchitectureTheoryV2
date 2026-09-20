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
    (J : Type u) (j : J) (value : Option (CircuitDetectorCode U)) :
    ObjectFormula.{u, v, 0} U :=
  equationAnchor t ha A hA .index
    (circuitCell (.code J j) value)

structure TypedInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop where
  some : ∀ J j, J = IndependentEquationPrimitive.index (equationRows t ha A hA) →
    ∃ value, (typedFormula t ha A hA J j (some value)).evaluate t
  none : ∀ J j, J ≠ IndependentEquationPrimitive.index (equationRows t ha A hA) →
    (typedFormula t ha A hA J j none).evaluate t

theorem typed_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :
    IndependentEquationPrimitive.Circuit.IsTyped
        (IndependentEquationPrimitive.index (equationRows t ha A hA)) (circuitRows t) ↔
      TypedInstances t ha A hA := by
  constructor
  · intro ht
    constructor
    · intro J j hJ
      have hs := (ht J j).2 hJ
      cases hv : circuitRows t (.code J j) with
      | none => simp [hv] at hs
      | some value =>
          refine ⟨value, ?_⟩
          simp only [typedFormula, equationAnchor_evaluate]
          exact (circuitCell_evaluate_iff t _ _).2 hv
    · intro J j hJ
      have hn := IndependentInvariantSignaturePrimitive.option_none _ (mt (ht J j).1 hJ)
      simp only [typedFormula, equationAnchor_evaluate]
      exact (circuitCell_evaluate_iff t _ _).2 hn
  · intro hi J j
    constructor
    · intro hs
      by_contra hJ
      have hn := hi.none J j hJ
      simp only [typedFormula, equationAnchor_evaluate] at hn
      have he := (circuitCell_evaluate_iff t _ _).1 hn
      rw [he] at hs
      exact Bool.noConfusion hs
    · intro hJ
      obtain ⟨value, hv⟩ := hi.some J j hJ
      simp only [typedFormula, equationAnchor_evaluate] at hv
      have he := (circuitCell_evaluate_iff t _ _).1 hv
      rw [he]
      rfl

def witnessFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA))
    (_hct : IndependentEquationPrimitive.Circuit.IsTyped
      (IndependentEquationPrimitive.index (equationRows t ha A hA)) (circuitRows t))
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA))
    (B : ArchitectureObject U) (_d : FiniteCircuitDatum U) (W : ArchCtx A) (a : U.Atom) :
    ObjectFormula.{u, v, u} U :=
  equationAnchor t ha A hA .index
    (circuitAnchor t (.code _ i)
      (Equation.residualAnchor t ha A hA hc ht W B i a
        (Equation.observableActiveAnchor t ha A hA hc ht W .zero
          (.implies
            (equationCell A (.residual W B
              (IndependentEquationPrimitive.index (equationRows t ha A hA))
              (IndependentEquationPrimitive.observableType
                (equationRows t ha A hA) W) i a)
              (ULift.up (some (Equation.observableActive t ha A hA hc ht W .zero))))
            .falsity))))

@[simp] theorem witnessFormula_evaluate
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
    (witnessFormula t ha A hA hc ht hct i B d W a).evaluate t ↔
      Equation.residualValue t ha A hA hc ht W B i a ≠
        Equation.observableActive t ha A hA hc ht W .zero := by
  simp only [witnessFormula, equationAnchor_evaluate, circuitAnchor_evaluate,
    Equation.residualAnchor_evaluate, Equation.observableActiveAnchor_evaluate,
    ObjectFormula.evaluate]
  rw [equationCell_evaluate_iff t ha A hA]
  let q : IndependentEquationPrimitive.Query A := .residual W B
    (IndependentEquationPrimitive.index (equationRows t ha A hA))
    (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) i a
  have hq : (equationRows t ha A hA q).down.isSome :=
    (ht.residual W B _ _ i a).2 ⟨rfl, rfl⟩
  constructor
  · intro hn hz
    apply hn
    apply ULift.ext
    exact (Option.some_get hq).symm.trans (congrArg some hz)
  · intro hn he
    apply hn
    have he' := congrArg ULift.down he
    exact Option.some.inj ((Option.some_get hq).trans he')

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
    exact ⟨W, a, (witnessFormula_evaluate t ha A hA hc ht hct i B d W a).2 hn⟩
  · intro hi i B d hm he
    obtain ⟨W, a, hw⟩ := hi i B d hm he
    exact ⟨W, a, (witnessFormula_evaluate t ha A hA hc ht hct i B d W a).1 hw⟩

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
