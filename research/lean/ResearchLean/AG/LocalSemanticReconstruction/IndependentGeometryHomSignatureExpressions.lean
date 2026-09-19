import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomSignatureLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextExpressions
import Formal.Util.AssertStandardAxioms

/-!
# Finite common-query expressions for signature Hom preservation

Selected predicates retain their primitive role and candidate axis arguments.
Coordinate leaves read one optional primitive value at one architecture object.
Each formula has finite source/target/Hom support independent of its values.
All selected-status and coordinate-preservation instances are exactly formulas
in this closed syntax on the same common declarations.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.SignatureFinite

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Closed signature formula syntax contains only primitive point roles and logical connectives. -/
inductive Expr (U : AtomCarrier.{u}) (mode : Mode) where
  /-- A source selected-axis predicate at one candidate axis. -/
  | sourceSelected (I : Type u) (i : I)
  /-- A target selected-axis predicate at one candidate axis. -/
  | targetSelected (I : Type u) (i : I)
  /-- One source coordinate response at a candidate coordinate carrier. -/
  | sourceCoordinate (I : Type u) (i : I) (K : Type u) (M : ArchitectureObject U) (x : K)
  /-- One target coordinate response at a candidate coordinate carrier. -/
  | targetCoordinate (I : Type u) (i : I) (K : Type u) (M : ArchitectureObject U) (x : K)
  /-- One common Hom graph point. -/
  | hom (q : Query.{u, v} U mode)
  /-- Conjunction of two finite expressions. -/
  | and (p q : Expr U mode)
  /-- Implication between finite expressions. -/
  | implies (p q : Expr U mode)
  /-- Logical equivalence of primitive predicate readings. -/
  | iff (p q : Expr U mode)

/-- Evaluation reads the original common source/target predicate or coordinate response and Hom cells. -/
def evaluate (s t : IndependentGeometryPrimitive.Table.{u, v} U) (h : Table.{u, v} U mode) :
    Expr U mode → Prop
  | .sourceSelected I i => (s (.signature (.selected I i))).down.down
  | .targetSelected I i => (t (.signature (.selected I i))).down.down
  | .sourceCoordinate I i K M x => (s (.signature (.coordinate I i K M))).down.down = some x
  | .targetCoordinate I i K M x => (t (.signature (.coordinate I i K M))).down.down = some x
  | .hom q => h q = true
  | .and p q => evaluate s t h p ∧ evaluate s t h q
  | .implies p q => evaluate s t h p → evaluate s t h q
  | .iff p q => evaluate s t h p ↔ evaluate s t h q

/-- The three finite sets of primitive addresses are fixed entirely by the expression constructors. -/
def support : Expr.{u, v} U mode → ContextFinite.Support.{u, v} U mode
  | .sourceSelected I i => ({.signature (.selected I i)}, ∅, ∅)
  | .targetSelected I i => (∅, {.signature (.selected I i)}, ∅)
  | .sourceCoordinate I i K M _ => ({.signature (.coordinate I i K M)}, ∅, ∅)
  | .targetCoordinate I i K M _ => (∅, {.signature (.coordinate I i K M)}, ∅)
  | .hom q => (∅, ∅, {q})
  | .and p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)
  | .implies p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)
  | .iff p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1, (support p).2.2 ∪ (support q).2.2)

/-- Agreement at the finite support preserves evaluation for any common tables. -/
theorem evaluate_iff_of_support (s t s' t' : IndependentGeometryPrimitive.Table.{u, v} U)
    (h h' : Table.{u, v} U mode) (e : Expr U mode)
    (hs : ∀ q ∈ (support e).1, s q = s' q)
    (ht : ∀ q ∈ (support e).2.1, t q = t' q)
    (hh : ∀ q ∈ (support e).2.2, h q = h' q) :
    evaluate s t h e ↔ evaluate s' t' h' e := by
  classical
  induction e with
  | sourceSelected I i =>
      have he := hs (.signature (.selected I i)) (by simp [support])
      simp only [evaluate, he]
  | targetSelected I i =>
      have he := ht (.signature (.selected I i)) (by simp [support])
      simp only [evaluate, he]
  | sourceCoordinate I i K M x =>
      have he := hs (.signature (.coordinate I i K M)) (by simp [support])
      simp only [evaluate, he]
  | targetCoordinate I i K M x =>
      have he := ht (.signature (.coordinate I i K M)) (by simp [support])
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
  | iff p q hp hq =>
      exact iff_congr
        (hp (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))
        (hq (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))

/-- The selected rule compares the source/target predicates at a single true axis graph pair. -/
def selectedRule (I J : Type u) (i : I) (j : J) : Expr.{u, v} U mode :=
  .implies (.hom (.signatureAxis (.edge I J i j))) (.iff (.sourceSelected I i) (.targetSelected J j))

/-- Coordinate preservation uses two response points and three object/axis/coordinate Hom points. -/
def coordinateRule (M N : ArchitectureObject U) (I J K L : Type u)
    (i : I) (j : J) (x : K) (y : L) : Expr.{u, v} U mode :=
  .implies (.and (.hom (.object M N)) (.and (.hom (.signatureAxis (.edge I J i j)))
    (.and (.sourceCoordinate I i K M x) (.targetCoordinate J j L N y))))
    (.hom (.signatureCoordinate .forward I J i j (.edge K L x y)))

/-- All selected-rule instances are exactly the primitive selected-status preservation law. -/
theorem selected_points_iff_expressions (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) :
    SignatureLaws.SelectedPoints (IndependentGeometryPrimitive.signature s) (IndependentGeometryPrimitive.signature t) h ↔
      ∀ (I J : Type u) (i : I) (j : J), evaluate s t h (selectedRule I J i j) := by
  rfl

/-- All coordinate-rule instances are exactly the primitive coordinate-preservation law. -/
theorem coordinate_points_iff_expressions (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) :
    SignatureLaws.CoordinatePoints (IndependentGeometryPrimitive.signature s) (IndependentGeometryPrimitive.signature t) h ↔
      ∀ (M N : ArchitectureObject U) (I J K L : Type u)
        (i : I) (j : J) (x : K) (y : L), evaluate s t h (coordinateRule M N I J K L i j x y) := by
  simp only [SignatureLaws.CoordinatePoints, coordinateRule, evaluate, IndependentGeometryPrimitive.signature, and_imp]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.SignatureFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.SignatureFinite
