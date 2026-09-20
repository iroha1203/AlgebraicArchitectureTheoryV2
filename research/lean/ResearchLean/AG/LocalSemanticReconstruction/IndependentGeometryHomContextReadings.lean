import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence
import Formal.Util.AssertStandardAxioms

/-!
# Context-equivalence points on the common Hom declaration

Forward/backward rows are total-functional, while their composites satisfy
both preorder comparisons. No inverse object equality is required. The
native thin-category equivalence is constructed only after the point rules,
with both reading inverses. Context preorder relations are evaluated at the
explicit context arguments of each local condition.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Context

noncomputable section

universe u v

open Site CategoryTheory

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U}

/-- Context point pairs are indexed before selecting either native context preorder. -/
abbrev PointTable (A B : ArchitectureObject U) := Direction → ArchCtx A → ArchCtx B → Bool

/-- Local thin-equivalence conditions compare graph pairs and individual preorder points. -/
structure IsLawful (r : ArchCtx A → ArchCtx A → Prop) (s : ArchCtx B → ArchCtx B → Prop)
    (p : PointTable A B) : Prop where
  /-- Exactly one forward context image per source context. -/
  forward : ∀ W, ∃! V, p .forward W V = true
  /-- Exactly one backward context image per target context. -/
  backward : ∀ V, ∃! W, p .backward W V = true
  /-- Forward true graph pairs preserve one source refinement point. -/
  forward_mono : ∀ W X V Y, p .forward W V = true → p .forward X Y = true → r W X → s V Y
  /-- Backward true graph pairs preserve one target refinement point. -/
  backward_mono : ∀ W X V Y, p .backward W V = true → p .backward X Y = true → s V Y → r W X
  /-- Both unit comparisons at a two-step point chain. -/
  unit : ∀ W V X, p .forward W V = true → p .backward X V = true → r W X ∧ r X W
  /-- Both counit comparisons at the opposite two-step chain. -/
  counit : ∀ V W Y, p .backward W V = true → p .forward W Y = true → s Y V ∧ s V Y

variable (C : ContextPreorderCategory A) (D : ContextPreorderCategory B)

/-- Wrap primitive context pairs as the predecessor's two raw object graphs. -/
def graphData (p : PointTable A B) :
    ContextObservableGraphCoherence.ThinEquivalenceGraphData (ContextCategoryObject C) (ContextCategoryObject D) :=
  ⟨⟨fun W V => p .forward W.ctx V.ctx⟩, ⟨fun V W => p .backward W.ctx V.ctx⟩⟩

/-- The forward primitive row law gives totality and uniqueness on native thin-category objects. -/
theorem forward_total (p : PointTable A B) (h : IsLawful C.le D.le p) :
    PrimitiveFunctionGraph.IsTotalFunctional (graphData C D p).forward := by
  constructor
  intro W
  obtain ⟨V, hv, hu⟩ := h.forward W.ctx
  refine ⟨⟨V⟩, hv, ?_⟩
  rintro ⟨Y⟩ hy
  exact congrArg (ContextCategoryObject.mk) (hu Y hy)

/-- The backward row law retains its target-to-source direction after native wrapping. -/
theorem backward_total (p : PointTable A B) (h : IsLawful C.le D.le p) :
    PrimitiveFunctionGraph.IsTotalFunctional (graphData C D p).backward := by
  constructor
  intro V
  obtain ⟨W, hw, hu⟩ := h.backward V.ctx
  refine ⟨⟨W⟩, hw, ?_⟩
  rintro ⟨X⟩ hx
  exact congrArg (ContextCategoryObject.mk) (hu X hx)

/-- All native thin-equivalence conditions are consequences of true pairs and local preorder comparisons. -/
def code (p : PointTable A B) (h : IsLawful C.le D.le p) :
    ContextObservableGraphCoherence.ThinEquivalenceGraphCode (ContextCategoryObject C) (ContextCategoryObject D) := by
  let f : PrimitiveFunctionGraph.GraphCode (ContextCategoryObject C) (ContextCategoryObject D) :=
    ⟨(graphData C D p).forward, forward_total C D p h⟩
  let g : PrimitiveFunctionGraph.GraphCode (ContextCategoryObject D) (ContextCategoryObject C) :=
    ⟨(graphData C D p).backward, backward_total C D p h⟩
  refine ⟨graphData C D p, forward_total C D p h, backward_total C D p h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W X hWX
    exact h.forward_mono _ _ _ _ (f.edge_target W) (f.edge_target X) hWX
  · intro V Y hVY
    exact h.backward_mono _ _ _ _ (g.edge_target V) (g.edge_target Y) hVY
  · intro W
    exact (h.unit _ _ _ (f.edge_target W) (g.edge_target (f.assemble W))).1
  · intro W
    exact (h.unit _ _ _ (f.edge_target W) (g.edge_target (f.assemble W))).2
  · intro V
    exact (h.counit _ _ _ (g.edge_target V) (f.edge_target (g.assemble V))).1
  · intro V
    exact (h.counit _ _ _ (g.edge_target V) (f.edge_target (g.assemble V))).2

/-- Read predecessor primitive graph data back at raw context references. -/
def flatten (g : ContextObservableGraphCoherence.ThinEquivalenceGraphCode
    (ContextCategoryObject C) (ContextCategoryObject D)) : PointTable A B
  | .forward, W, V => g.val.forward.edge ⟨W⟩ ⟨V⟩
  | .backward, W, V => g.val.backward.edge ⟨V⟩ ⟨W⟩

/-- Native graph-code premises imply precisely the pointwise thin-equivalence rules. -/
theorem flatten_isLawful (g : ContextObservableGraphCoherence.ThinEquivalenceGraphCode
    (ContextCategoryObject C) (ContextCategoryObject D)) : IsLawful C.le D.le (flatten C D g) := by
  constructor
  · intro W
    obtain ⟨V, hv, hu⟩ := g.forwardCode.row_existsUnique ⟨W⟩
    refine ⟨V.ctx, hv, ?_⟩
    intro Y hy
    exact congrArg ContextCategoryObject.ctx (hu ⟨Y⟩ hy)
  · intro V
    obtain ⟨W, hw, hu⟩ := g.backwardCode.row_existsUnique ⟨V⟩
    refine ⟨W.ctx, hw, ?_⟩
    intro X hx
    exact congrArg ContextCategoryObject.ctx (hu ⟨X⟩ hx)
  · intro W X V Y hWV hXY hWX
    have heV := g.forwardCode.target_eq_of_edge hWV
    have heY := g.forwardCode.target_eq_of_edge hXY
    have hn := g.property.forward_mono (show (⟨W⟩ : ContextCategoryObject C) ≤ ⟨X⟩ from hWX)
    change g.forwardCode.target ⟨W⟩ ≤ g.forwardCode.target ⟨X⟩ at hn
    rw [heV, heY] at hn
    exact hn
  · intro W X V Y hWV hXY hVY
    have heW := g.backwardCode.target_eq_of_edge hWV
    have heX := g.backwardCode.target_eq_of_edge hXY
    have hn := g.property.backward_mono (show (⟨V⟩ : ContextCategoryObject D) ≤ ⟨Y⟩ from hVY)
    change g.backwardCode.target ⟨V⟩ ≤ g.backwardCode.target ⟨Y⟩ at hn
    rw [heW, heX] at hn
    exact hn
  · intro W V X hWV hXV
    have heV := g.forwardCode.target_eq_of_edge hWV
    have heX := g.backwardCode.target_eq_of_edge hXV
    have h1 := g.property.unit_hom ⟨W⟩
    have h2 := g.property.unit_inv ⟨W⟩
    change (⟨W⟩ : ContextCategoryObject C) ≤ g.backwardCode.target (g.forwardCode.target ⟨W⟩) at h1
    change g.backwardCode.target (g.forwardCode.target ⟨W⟩) ≤ (⟨W⟩ : ContextCategoryObject C) at h2
    rw [heV, heX] at h1 h2
    exact ⟨h1, h2⟩
  · intro V W Y hWV hWY
    have heW := g.backwardCode.target_eq_of_edge hWV
    have heY := g.forwardCode.target_eq_of_edge hWY
    have h1 := g.property.counit_hom ⟨V⟩
    have h2 := g.property.counit_inv ⟨V⟩
    change g.forwardCode.target (g.backwardCode.target ⟨V⟩) ≤ (⟨V⟩ : ContextCategoryObject D) at h1
    change (⟨V⟩ : ContextCategoryObject D) ≤ g.forwardCode.target (g.backwardCode.target ⟨V⟩) at h2
    rw [heW, heY] at h1 h2
    exact ⟨h1, h2⟩

/-- Collecting and re-flattening restores every raw context pair. -/
theorem flatten_code (p : PointTable A B) (h : IsLawful C.le D.le p) :
    flatten C D (code C D p h) = p := by
  funext direction W V
  cases direction <;> rfl

/-- No extra unit/counit choices survive the exact predecessor-code reconstruction. -/
theorem code_flatten (g : ContextObservableGraphCoherence.ThinEquivalenceGraphCode
    (ContextCategoryObject C) (ContextCategoryObject D)) :
    code C D (flatten C D g) (flatten_isLawful C D g) = g := by
  apply ContextObservableGraphCoherence.ThinEquivalenceGraphCode.ext
  · apply PrimitiveFunctionGraph.GraphData.ext
    funext W V
    rfl
  · apply PrimitiveFunctionGraph.GraphData.ext
    funext V W
    rfl

/-- Exact primitive point presentations of every native thin-equivalence graph code. -/
def codeEquiv : {p : PointTable A B // IsLawful C.le D.le p} ≃
    ContextObservableGraphCoherence.ThinEquivalenceGraphCode (ContextCategoryObject C) (ContextCategoryObject D) where
  toFun p := code C D p.val p.property
  invFun g := ⟨flatten C D g, flatten_isLawful C D g⟩
  left_inv p := Subtype.ext (flatten_code C D p.val p.property)
  right_inv := code_flatten C D

/-- Every native context-category equivalence has an exact common primitive point presentation. -/
def readingEquiv : ((ContextCategoryObject C) ≌ (ContextCategoryObject D)) ≃
    {p : PointTable A B // IsLawful C.le D.le p} :=
  ContextObservableGraphCoherence.ThinEquivalenceGraphCode.equivEquivalence.symm.trans (codeEquiv C D).symm

/-- Native context equivalence assembly from primitive point laws. -/
def assemble (p : PointTable A B) (h : IsLawful C.le D.le p) :
    (ContextCategoryObject C) ≌ (ContextCategoryObject D) := (readingEquiv C D).symm ⟨p, h⟩

/-- Native context equivalences are read only through their two object point graphs. -/
def read (e : (ContextCategoryObject C) ≌ (ContextCategoryObject D)) : PointTable A B :=
  (readingEquiv C D e).val

/-- Native context-equivalence readings satisfy all pointwise preorder conditions. -/
theorem read_isLawful (e : (ContextCategoryObject C) ≌ (ContextCategoryObject D)) :
    IsLawful C.le D.le (read C D e) := (readingEquiv C D e).property

/-- Full native context equivalences, including both functors, survive the primitive round trip. -/
theorem assemble_read (e : (ContextCategoryObject C) ≌ (ContextCategoryObject D)) :
    assemble C D (read C D e) (read_isLawful C D e) = e := (readingEquiv C D).left_inv e

/-- Every raw forward/backward context pair survives native assembly and re-reading. -/
theorem read_assemble (p : PointTable A B) (h : IsLawful C.le D.le p) :
    read C D (assemble C D p h) = p := congrArg Subtype.val ((readingEquiv C D).right_inv ⟨p, h⟩)

/-- The actual common Hom declaration supplies these context rows without any native preorder parameter. -/
def points {mode : Mode} (t : Table.{u, v} U mode) (A B : ArchitectureObject U) : PointTable A B :=
  fun direction W V => t (.atObjects A B (.context direction W V))

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Context

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Context
