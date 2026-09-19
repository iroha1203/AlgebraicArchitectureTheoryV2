import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomEquationLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextExpressions
import Formal.Util.AssertStandardAxioms

/-!
# Finite expressions for equation-role and coordinate preservation

Leaves read one primitive equation response or one common Hom Boolean. The
syntax contains conjunction and implication, with no completed map, arbitrary
predicate, or hidden family equality as a constructor. Its support is a
finite subset of each common source/target/Hom declaration. Role, violation,
and residual rules below instantiate this syntax and are exactly the point
laws used by the native equation-transport assembler.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationFinite

noncomputable section

universe u v w z

open Site

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U} {mode : Mode}

/-- A single primitive equation response in an active common object row. -/
def point (t : IndependentGeometryPrimitive.Table.{u, v} U) (A : ArchitectureObject U)
    (q : IndependentEquationPrimitive.Query A) (value : q.Value) : Prop :=
  t (.atObject A (.equation q)) = some ⟨value⟩

/-- Reading an active common equation row identifies the response exactly. -/
theorem point_iff (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (ha : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentEquationPrimitive.Query A) (value : q.Value) :
    point t A q value ↔
      IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht A ha) q = value := by
  unfold point
  rw [← IndependentGeometryPrimitive.some_dependent t ht A ha (.equation q)]
  constructor
  · intro he
    exact congrArg ULift.down (Option.some.inj he)
  · intro he
    exact congrArg some (ULift.ext _ _ he)

/-- Equality with a lifted response is exactly equality of its primitive value. -/
theorem lifted_eq_iff {α : Type w} (x : ULift.{z} α) (y : α) : x = ⟨y⟩ ↔ x.down = y := by
  constructor
  · intro h
    exact congrArg ULift.down h
  · exact ULift.ext _ _

/-- The optional role leaf is exactly one active role response. -/
theorem role_point_iff (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (ha : IndependentGeometryPrimitive.matching t (.object A) = true)
    (I : Type u) (i : I) (r : EquationRole) :
    point t A (.role I i) ⟨some r⟩ ↔
      (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht A ha)
        (.role I i)).down = some r :=
  (point_iff t ht A ha _ _).trans (lifted_eq_iff _ _)

/-- The optional violation leaf is exactly one active symbolic-coordinate response. -/
theorem violation_point_iff (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (ha : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (I K : Type u) (i : I) (a : U.Atom) (x : K) :
    point t A (.violation W I K i a) ⟨some x⟩ ↔
      (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht A ha)
        (.violation W I K i a)).down = some x :=
  (point_iff t ht A ha _ _).trans (lifted_eq_iff _ _)

/-- The optional residual leaf is exactly one active object-dependent response. -/
theorem residual_point_iff (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (ha : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (M : ArchitectureObject U) (I K : Type u) (i : I) (a : U.Atom) (x : K) :
    point t A (.residual W M I K i a) ⟨some x⟩ ↔
      (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht A ha)
        (.residual W M I K i a)).down = some x :=
  (point_iff t ht A ha _ _).trans (lifted_eq_iff _ _)

/-- Closed expression syntax over equation point responses and common Hom cells. -/
inductive Expr (A B : ArchitectureObject U) (mode : Mode) where
  /-- Compare one source equation response with an explicit primitive value. -/
  | source (q : IndependentEquationPrimitive.Query A) (value : q.Value)
  /-- Compare one target equation response with an explicit primitive value. -/
  | target (q : IndependentEquationPrimitive.Query B) (value : q.Value)
  /-- Read one explicit common Hom Boolean point. -/
  | hom (q : Query.{u, v} U mode)
  /-- Conjunction of two expressions. -/
  | and (p q : Expr A B mode)
  /-- Implication between two expressions. -/
  | implies (p q : Expr A B mode)

/-- Evaluate through the three common tables, before or after any validation. -/
def evaluate (s t : IndependentGeometryPrimitive.Table.{u, v} U) (h : Table.{u, v} U mode) :
    Expr A B mode → Prop
  | .source q value => point s A q value
  | .target q value => point t B q value
  | .hom q => h q = true
  | .and p q => evaluate s t h p ∧ evaluate s t h q
  | .implies p q => evaluate s t h p → evaluate s t h q

/-- The source, target, and Hom support sets are constructed from syntax alone. -/
def support : Expr.{u, v} A B mode → ContextFinite.Support.{u, v} U mode
  | .source q _ => ({.atObject A (.equation q)}, ∅, ∅)
  | .target q _ => (∅, {.atObject B (.equation q)}, ∅)
  | .hom q => (∅, ∅, {q})
  | .and p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)
  | .implies p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)

/-- Agreement on the explicit finite support preserves evaluation for arbitrary common tables. -/
theorem evaluate_iff_of_support (s t s' t' : IndependentGeometryPrimitive.Table.{u, v} U)
    (h h' : Table.{u, v} U mode) (e : Expr A B mode)
    (hs : ∀ q ∈ (support e).1, s q = s' q)
    (ht : ∀ q ∈ (support e).2.1, t q = t' q)
    (hh : ∀ q ∈ (support e).2.2, h q = h' q) :
    evaluate s t h e ↔ evaluate s' t' h' e := by
  classical
  induction e with
  | source q value =>
      have he := hs (.atObject A (.equation q)) (by simp [support])
      simp only [evaluate, point, he]
  | target q value =>
      have he := ht (.atObject B (.equation q)) (by simp [support])
      simp only [evaluate, point, he]
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

/-- A role rule reads one equation point and one role response on each side. -/
def roleRule (I J : Type u) (i : I) (j : J) (r : EquationRole) : Expr.{u, v} A B mode :=
  .implies (.and (.hom (.atObjects A B (.equation .forward (.edge I J i j))))
    (.source (.role I i) ⟨some r⟩)) (.target (.role J j) ⟨some r⟩)

/-- A violation rule keeps both response points and the context, equation, Atom, and observable graph points. -/
def violationRule (W : ArchCtx A) (V : ArchCtx B) (I J K L : Type u)
    (i : I) (j : J) (a b : U.Atom) (x : K) (y : L) : Expr.{u, v} A B mode :=
  .implies (.and (.hom (.atObjects A B (.context .forward W V)))
    (.and (.hom (.atObjects A B (.equation .forward (.edge I J i j))))
      (.and (.hom (.atom .forward a b))
        (.and (.source (.violation W I K i a) ⟨some x⟩)
          (.target (.violation V J L j b) ⟨some y⟩)))))
    (.hom (.atObjects A B (.observable .forward W V (.edge K L x y))))

/-- A residual rule adds the directed object graph point to the coordinate square. -/
def residualRule (W : ArchCtx A) (V : ArchCtx B) (M N : ArchitectureObject U) (I J K L : Type u)
    (i : I) (j : J) (a b : U.Atom) (x : K) (y : L) : Expr.{u, v} A B mode :=
  .implies (.and (.hom (.atObjects A B (.context .forward W V)))
    (.and (.hom (.object M N)) (.and (.hom (.atObjects A B (.equation .forward (.edge I J i j))))
      (.and (.hom (.atom .forward a b))
        (.and (.source (.residual W M I K i a) ⟨some x⟩)
          (.target (.residual V N J L j b) ⟨some y⟩))))))
    (.hom (.atObjects A B (.observable .forward W V (.edge K L x y))))

variable (s t : IndependentGeometryPrimitive.Table.{u, v} U)
variable (hs : IndependentGeometryPrimitive.IsActiveTyped s) (ht : IndependentGeometryPrimitive.IsActiveTyped t)
variable (ha : IndependentGeometryPrimitive.matching s (.object A) = true)
variable (hb : IndependentGeometryPrimitive.matching t (.object B) = true) (h : Table.{u, v} U mode)

/-- All finite role-rule instances are exactly the common row's primitive role preservation. -/
theorem role_points_iff_expressions : EquationLaws.RolePoints
    (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent s hs A ha))
    (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht B hb)) h ↔
      ∀ (I J : Type u) (i : I) (j : J) (r : EquationRole),
        evaluate s t h (roleRule (A := A) (B := B) I J i j r) := by
  simp only [EquationLaws.RolePoints, roleRule, evaluate, and_imp, role_point_iff s hs A ha,
    role_point_iff t ht B hb]

/-- All finite violation-rule instances give exactly the primitive symbolic-coordinate law. -/
theorem violation_points_iff_expressions : EquationLaws.ViolationPoints
    (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent s hs A ha))
    (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht B hb)) h ↔
      ∀ (W : ArchCtx A) (V : ArchCtx B) (I J K L : Type u)
        (i : I) (j : J) (a b : U.Atom) (x : K) (y : L),
        evaluate s t h (violationRule W V I J K L i j a b x y) := by
  simp only [EquationLaws.ViolationPoints, violationRule, evaluate, and_imp, violation_point_iff s hs A ha,
    violation_point_iff t ht B hb]

/-- All finite residual-rule instances give exactly the primitive object-dependent coordinate law. -/
theorem residual_points_iff_expressions : EquationLaws.ResidualPoints
    (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent s hs A ha))
    (IndependentGeometryPrimitive.equationTable (IndependentGeometryPrimitive.dependent t ht B hb)) h ↔
      ∀ (W : ArchCtx A) (V : ArchCtx B) (M N : ArchitectureObject U) (I J K L : Type u)
        (i : I) (j : J) (a b : U.Atom) (x : K) (y : L),
        evaluate s t h (residualRule W V M N I J K L i j a b x y) := by
  simp only [EquationLaws.ResidualPoints, residualRule, evaluate, and_imp, residual_point_iff s hs A ha,
    residual_point_iff t ht B hb]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationFinite
