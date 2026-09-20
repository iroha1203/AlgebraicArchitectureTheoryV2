import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationNaturality
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextExpressions
import Formal.Util.AssertStandardAxioms

/-!
# Finite common-query support for operation naturality

The closed syntax reads an operation-action response from either object table
or a Boolean from the common Hom table. Each action-square instance uses two
response points and five Hom points. Finite support is constructed from the
syntax and preserves evaluation for arbitrary, including unvalidated, tables.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.OperationFinite

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Primitive operation-action leaves and common Hom cells, closed under finite logical combinations. -/
inductive Expr (U : AtomCarrier.{u}) (mode : Mode) where
  /-- One source operation action at explicit endpoint and carrier references. -/
  | source (A B : ArchitectureObject U) (K : Type u) (op : K) (a ax : U.Atom)
  /-- One target operation action at explicit endpoint and carrier references. -/
  | target (A B : ArchitectureObject U) (K : Type u) (op : K) (a ax : U.Atom)
  /-- One point of the common Hom declaration. -/
  | hom (q : Query.{u, v} U mode)
  /-- Conjunction of finite expressions. -/
  | and (p q : Expr U mode)
  /-- Implication between finite expressions. -/
  | implies (p q : Expr U mode)

/-- Evaluation reads only the explicit primitive action responses and Hom Booleans. -/
def evaluate (s t : IndependentGeometryPrimitive.Table.{u, v} U) (h : Table.{u, v} U mode) :
    Expr U mode → Prop
  | .source A B K op a ax => (s (.operation (.action A B K op a))).down.down = some ax
  | .target A B K op a ax => (t (.operation (.action A B K op a))).down.down = some ax
  | .hom q => h q = true
  | .and p q => evaluate s t h p ∧ evaluate s t h q
  | .implies p q => evaluate s t h p → evaluate s t h q

/-- Three finite sets of common-query addresses, determined entirely by syntax. -/
def support : Expr.{u, v} U mode → ContextFinite.Support.{u, v} U mode
  | .source A B K op a _ => ({.operation (.action A B K op a)}, ∅, ∅)
  | .target A B K op a _ => (∅, {.operation (.action A B K op a)}, ∅)
  | .hom q => (∅, ∅, {q})
  | .and p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)
  | .implies p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)

/-- Arbitrary tables agreeing on these finite sets give the same operation-formula value. -/
theorem evaluate_iff_of_support (s t s' t' : IndependentGeometryPrimitive.Table.{u, v} U)
    (h h' : Table.{u, v} U mode) (e : Expr U mode)
    (hs : ∀ q ∈ (support e).1, s q = s' q)
    (ht : ∀ q ∈ (support e).2.1, t q = t' q)
    (hh : ∀ q ∈ (support e).2.2, h q = h' q) :
    evaluate s t h e ↔ evaluate s' t' h' e := by
  classical
  induction e with
  | source A B K op a ax =>
      have he := hs (.operation (.action A B K op a)) (by simp [support])
      simp only [evaluate, he]
  | target A B K op a ax =>
      have he := ht (.operation (.action A B K op a)) (by simp [support])
      simp only [evaluate, he]
  | hom q =>
      have he := hh q (by simp [support])
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

/-- The action square is one finite implication on its seven explicit primitive points. -/
def actionRule (A B A' B' : ArchitectureObject U) (K L : Type u)
    (op : K) (op' : L) (a b ax bx : U.Atom) : Expr.{u, v} U mode :=
  .implies (.and (.hom (.object A A')) (.and (.hom (.object B B'))
    (.and (.hom (.operation A B A' B' (.edge K L op op'))) (.and (.hom (.atom .forward a b))
      (.and (.source A B K op a ax) (.target A' B' L op' b bx))))))
    (.hom (.atom .forward ax bx))

/-- Every primitive operation law instance is exactly an instance of the closed common-query syntax. -/
theorem pointLaws_iff_expressions (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) :
    OperationNatural.PointLaws (IndependentGeometryPrimitive.operation s) (IndependentGeometryPrimitive.operation t) h ↔
      ∀ (A B A' B' : ArchitectureObject U) (K L : Type u)
        (op : K) (op' : L) (a b ax bx : U.Atom), evaluate s t h (actionRule A B A' B' K L op op' a b ax bx) := by
  simp only [OperationNatural.PointLaws, actionRule, evaluate, IndependentGeometryPrimitive.operation, and_imp]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.OperationFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.OperationFinite
