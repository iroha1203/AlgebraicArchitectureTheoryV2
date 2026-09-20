import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomObservableNaturality
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextExpressions
import Formal.Util.AssertStandardAxioms

/-!
# Finite common-query support for observable restriction squares

Each naturality instance reads two restriction responses and four Hom points.
The closed syntax and its support are defined before object tables are chosen.
Evaluation is invariant under agreement on this finite support for arbitrary
tables. On active object rows, the instances are exactly the primitive laws
already proved equivalent to native restriction naturality.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ObservableFinite

noncomputable section

universe u v

open Site

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U} {mode : Mode}

/-- One restriction response, including the two optional activation levels. -/
def restrictionPoint (t : IndependentGeometryPrimitive.Table.{u, v} U) (A : ArchitectureObject U)
    (W X : ArchCtx A) (K L : Type u) (x : L) (rx : K) : Prop :=
  t (.atObject A (.equation (.restriction W X K L x))) = some ⟨⟨some rx⟩⟩

/-- Active common rows identify the restriction-response proposition with its equation point. -/
theorem restrictionPoint_iff (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (ha : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W X : ArchCtx A) (K L : Type u) (x : L) (rx : K) :
    restrictionPoint t A W X K L x rx ↔
      ((IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht A ha))
        (.restriction W X K L x)).down = some rx := by
  unfold restrictionPoint
  rw [← IndependentGeometryPrimitive.some_dependent t ht A ha (.equation (.restriction W X K L x))]
  constructor
  · intro he
    exact congrArg (fun z => z.down.down) (Option.some.inj he)
  · intro he
    exact congrArg some (ULift.ext _ _ (ULift.ext _ _ he))

/-- Closed syntax for observable point squares; its leaves contain only explicit query arguments. -/
inductive Expr (A B : ArchitectureObject U) where
  /-- Source restriction at one explicit value. -/
  | source (W X : ArchCtx A) (K L : Type u) (x : L) (rx : K)
  /-- Target restriction at one explicit value. -/
  | target (V Y : ArchCtx B) (K L : Type u) (x : L) (rx : K)
  /-- Forward context graph point. -/
  | context (W : ArchCtx A) (V : ArchCtx B)
  /-- Forward observable graph point. -/
  | observable (W : ArchCtx A) (V : ArchCtx B) (K L : Type u) (x : K) (y : L)
  /-- Conjunction of finite expressions. -/
  | and (p q : Expr A B)
  /-- Implication between finite expressions. -/
  | implies (p q : Expr A B)

/-- Evaluate the fixed syntax directly on common object/object/Hom tables. -/
def evaluate (s t : IndependentGeometryPrimitive.Table.{u, v} U) (h : Table.{u, v} U mode) :
    Expr A B → Prop
  | .source W X K L x rx => restrictionPoint s A W X K L x rx
  | .target V Y K L x rx => restrictionPoint t B V Y K L x rx
  | .context W V => h (.atObjects A B (.context .forward W V)) = true
  | .observable W V K L x y => h (.atObjects A B (.observable .forward W V (.edge K L x y))) = true
  | .and p q => evaluate s t h p ∧ evaluate s t h q
  | .implies p q => evaluate s t h p → evaluate s t h q

/-- Finite addresses in the common declarations, independent of every table value. -/
def support : Expr A B → ContextFinite.Support.{u, v} U mode
  | .source W X K L x _ => ({.atObject A (.equation (.restriction W X K L x))}, ∅, ∅)
  | .target V Y K L x _ => (∅, {.atObject B (.equation (.restriction V Y K L x))}, ∅)
  | .context W V => (∅, ∅, {.atObjects A B (.context .forward W V)})
  | .observable W V K L x y => (∅, ∅, {.atObjects A B (.observable .forward W V (.edge K L x y))})
  | .and p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)
  | .implies p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)

/-- Arbitrary tables agreeing at these finite addresses give the same expression value. -/
theorem evaluate_iff_of_support (s t s' t' : IndependentGeometryPrimitive.Table.{u, v} U)
    (h h' : Table.{u, v} U mode) (e : Expr A B)
    (hs : ∀ q ∈ (support (mode := mode) e).1, s q = s' q)
    (ht : ∀ q ∈ (support (mode := mode) e).2.1, t q = t' q)
    (hh : ∀ q ∈ (support (mode := mode) e).2.2, h q = h' q) :
    evaluate s t h e ↔ evaluate s' t' h' e := by
  classical
  induction e with
  | source W X K L x rx =>
      have he := hs (.atObject A (.equation (.restriction W X K L x))) (by simp [support])
      simp only [evaluate, restrictionPoint, he]
  | target V Y K L x rx =>
      have he := ht (.atObject B (.equation (.restriction V Y K L x))) (by simp [support])
      simp only [evaluate, restrictionPoint, he]
  | context W V =>
      have he := hh (.atObjects A B (.context .forward W V)) (by simp [support])
      simp only [evaluate, he]
  | observable W V K L x y =>
      have he := hh (.atObjects A B (.observable .forward W V (.edge K L x y))) (by simp [support])
      simp only [evaluate, he]
  | and p q hp hq =>
      exact and_congr
        (hp (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))
        (hq (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))
  | implies p q hp hq =>
      exact imp_congr
        (hp (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))
        (hq (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))

/-- A restriction square uses two context points, two restriction responses, and two observable points. -/
def restrictionRule (W X : ArchCtx A) (V Y : ArchCtx B) (K L K' L' : Type u)
    (x : L) (y : L') (rx : K) (ry : K') : Expr A B :=
  .implies (.and (.context W V) (.and (.context X Y)
    (.and (.source W X K L x rx) (.and (.target V Y K' L' y ry) (.observable X Y L L' x y)))))
    (.observable W V K K' rx ry)

/-- On active common rows, all restriction-rule instances are exactly the primitive naturality laws. -/
theorem pointLaws_iff_expressions (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hs : IndependentGeometryPrimitive.IsActiveTyped s) (ht : IndependentGeometryPrimitive.IsActiveTyped t)
    (ha : IndependentGeometryPrimitive.matching s (.object A) = true)
    (hb : IndependentGeometryPrimitive.matching t (.object B) = true) (h : Table.{u, v} U mode) :
    ObservableNatural.PointLaws
      (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent s hs A ha))
      (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht B hb)) h ↔
      ∀ (W X : ArchCtx A) (V Y : ArchCtx B) (K L K' L' : Type u)
        (x : L) (y : L') (rx : K) (ry : K'),
        evaluate s t h (restrictionRule W X V Y K L K' L' x y rx ry) := by
  simp only [ObservableNatural.PointLaws, restrictionRule, evaluate, and_imp,
    restrictionPoint_iff s hs A ha, restrictionPoint_iff t ht B hb]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ObservableFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ObservableFinite
