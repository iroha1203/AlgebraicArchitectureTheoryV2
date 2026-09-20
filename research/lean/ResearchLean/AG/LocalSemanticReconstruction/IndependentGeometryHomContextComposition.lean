import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierComposition
import Formal.Util.AssertStandardAxioms

/-!
# Direct context-point identity and composition

Implementation notes: the two raw context graphs compose in opposite orders.
Their exact-one row targets are chosen from primitive points. The original
preorder comparisons, rather than inverse object equality, prove closure.
The native category equivalence occurs only in the comparison theorems.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Context

noncomputable section

universe u

open Site CategoryTheory

variable {U : AtomCarrier.{u}} {A B E : ArchitectureObject U}
variable (C : ContextPreorderCategory A) (D : ContextPreorderCategory B) (F : ContextPreorderCategory E)

/-- Compose raw forward context points in forward order and raw backward points in reverse order. -/
def compose (p : PointTable A B) (hp : IsLawful C.le D.le p)
    (q : PointTable B E) (hq : IsLawful D.le F.le q) : PointTable A E
  | .forward, W, Z => IndependentIndexedCarrierGraph.composeIndex (p .forward) hp.forward (q .forward) W Z
  | .backward, W, Z => IndependentIndexedCarrierGraph.composeIndex (fun Z V => q .backward V Z) hq.backward
      (fun V W => p .backward W V) Z W

/-- Direct context point composition agrees with the original composite thin-category equivalence. -/
theorem compose_eq_read (p : PointTable A B) (hp : IsLawful C.le D.le p)
    (q : PointTable B E) (hq : IsLawful D.le F.le q) :
    compose C D F p hp q hq = read C F ((assemble C D p hp).trans (assemble D F q hq)) := by
  funext d W Z
  cases d with
  | forward =>
    have he : read C F ((assemble C D p hp).trans (assemble D F q hq)) .forward W Z =
        (PrimitiveFunctionGraph.GraphCode.comp (code C D p hp).forwardCode (code D F q hq).forwardCode).edge ⟨W⟩ ⟨Z⟩ :=
      congrArg (fun r => r.edge ⟨W⟩ ⟨Z⟩)
        (ContextObservableGraphCoherence.ThinEquivalenceGraphCode.comp_forward (code C D p hp) (code D F q hq))
    apply Bool.eq_iff_iff.mpr
    rw [he]
    constructor
    · intro h
      obtain ⟨V, hpV, hqV⟩ := (IndependentIndexedCarrierGraph.composeIndex_iff _ hp.forward _ W Z).1 h
      exact (PrimitiveFunctionGraph.GraphCode.comp_edge_eq_true_iff _ _ _ _).2 ⟨⟨V⟩, hpV, hqV⟩
    · intro h
      obtain ⟨V, hpV, hqV⟩ := (PrimitiveFunctionGraph.GraphCode.comp_edge_eq_true_iff _ _ _ _).1 h
      exact (IndependentIndexedCarrierGraph.composeIndex_iff _ hp.forward _ W Z).2 ⟨V.ctx, hpV, hqV⟩
  | backward =>
    have he : read C F ((assemble C D p hp).trans (assemble D F q hq)) .backward W Z =
        (PrimitiveFunctionGraph.GraphCode.comp (code D F q hq).backwardCode (code C D p hp).backwardCode).edge ⟨Z⟩ ⟨W⟩ :=
      congrArg (fun r => r.edge ⟨Z⟩ ⟨W⟩)
        (ContextObservableGraphCoherence.ThinEquivalenceGraphCode.comp_backward (code C D p hp) (code D F q hq))
    apply Bool.eq_iff_iff.mpr
    rw [he]
    constructor
    · intro h
      obtain ⟨V, hqV, hpV⟩ := (IndependentIndexedCarrierGraph.composeIndex_iff
        (fun Z V => q .backward V Z) hq.backward (fun V W => p .backward W V) Z W).1 h
      exact (PrimitiveFunctionGraph.GraphCode.comp_edge_eq_true_iff _ _ _ _).2 ⟨⟨V⟩, hqV, hpV⟩
    · intro h
      obtain ⟨V, hqV, hpV⟩ := (PrimitiveFunctionGraph.GraphCode.comp_edge_eq_true_iff _ _ _ _).1 h
      exact (IndependentIndexedCarrierGraph.composeIndex_iff
        (fun Z V => q .backward V Z) hq.backward (fun V W => p .backward W V) Z W).2 ⟨V.ctx, hqV, hpV⟩

/-- Direct context point composition retains both monotonicity directions and both unit/counit comparisons. -/
theorem compose_isLawful (p : PointTable A B) (hp : IsLawful C.le D.le p)
    (q : PointTable B E) (hq : IsLawful D.le F.le q) : IsLawful C.le F.le (compose C D F p hp q hq) := by
  rw [compose_eq_read]
  exact read_isLawful C F _

/-- Native context assembly sends primitive point composition to the original equivalence composition. -/
theorem assemble_compose (p : PointTable A B) (hp : IsLawful C.le D.le p)
    (q : PointTable B E) (hq : IsLawful D.le F.le q) :
    assemble C F (compose C D F p hp q hq) (compose_isLawful C D F p hp q hq) =
      (assemble C D p hp).trans (assemble D F q hq) := by
  have he : (⟨compose C D F p hp q hq, compose_isLawful C D F p hp q hq⟩ : {r // IsLawful C.le F.le r}) =
      ⟨read C F ((assemble C D p hp).trans (assemble D F q hq)), read_isLawful C F _⟩ :=
    Subtype.ext (compose_eq_read C D F p hp q hq)
  exact (congrArg (readingEquiv C F).symm he).trans (assemble_read C F _)

/-- A forward context composite is fixed by one first image point and one second output point. -/
theorem compose_forward_support (p p' : PointTable A B) (hp : IsLawful C.le D.le p) (hp' : IsLawful C.le D.le p')
    (q q' : PointTable B E) (hq : IsLawful D.le F.le q) (hq' : IsLawful D.le F.le q') (W : ArchCtx A) (Z : ArchCtx E)
    (h1 : p .forward W (IndependentIndexedCarrierGraph.index (p .forward) hp.forward W) =
      p' .forward W (IndependentIndexedCarrierGraph.index (p .forward) hp.forward W))
    (h2 : q .forward (IndependentIndexedCarrierGraph.index (p .forward) hp.forward W) Z =
      q' .forward (IndependentIndexedCarrierGraph.index (p .forward) hp.forward W) Z) :
    compose C D F p hp q hq .forward W Z = compose C D F p' hp' q' hq' .forward W Z :=
  IndependentIndexedCarrierGraph.composeIndex_point_support _ _ hp.forward hp'.forward _ _ W Z h1 h2

/-- A backward context composite reads the second backward image before the first backward output. -/
theorem compose_backward_support (p p' : PointTable A B) (hp : IsLawful C.le D.le p) (hp' : IsLawful C.le D.le p')
    (q q' : PointTable B E) (hq : IsLawful D.le F.le q) (hq' : IsLawful D.le F.le q') (W : ArchCtx A) (Z : ArchCtx E)
    (h1 : q .backward (IndependentIndexedCarrierGraph.index (fun Z V => q .backward V Z) hq.backward Z) Z =
      q' .backward (IndependentIndexedCarrierGraph.index (fun Z V => q .backward V Z) hq.backward Z) Z)
    (h2 : p .backward W (IndependentIndexedCarrierGraph.index (fun Z V => q .backward V Z) hq.backward Z) =
      p' .backward W (IndependentIndexedCarrierGraph.index (fun Z V => q .backward V Z) hq.backward Z)) :
    compose C D F p hp q hq .backward W Z = compose C D F p' hp' q' hq' .backward W Z :=
  IndependentIndexedCarrierGraph.composeIndex_point_support
    (fun Z V => q .backward V Z) (fun Z V => q' .backward V Z) hq.backward hq'.backward
    (fun V W => p .backward W V) (fun V W => p' .backward W V) Z W h1 h2

/-- Raw context identity consists of diagonal points in each direction's input order. -/
def identity (A : ArchitectureObject U) : PointTable A A := by
  classical
  exact fun d W V => match d with
    | .forward => decide (W = V)
    | .backward => decide (V = W)

/-- The diagonal raw context table reads the native identity equivalence. -/
theorem identity_eq_read : identity A = read C C (CategoryTheory.Equivalence.refl) := by
  classical
  funext d W V
  cases d with
  | forward =>
    change decide (W = V) = decide ((⟨W⟩ : ContextCategoryObject C) = ⟨V⟩)
    simp only [ContextCategoryObject.mk.injEq]
  | backward =>
    change decide (V = W) = decide ((⟨V⟩ : ContextCategoryObject C) = ⟨W⟩)
    simp only [ContextCategoryObject.mk.injEq]

/-- Raw diagonal context points satisfy the original preorder-equivalence laws. -/
theorem identity_isLawful : IsLawful C.le C.le (identity A) := by
  rw [identity_eq_read C]
  exact read_isLawful C C _

/-- The direct context identity assembles to the original native identity equivalence. -/
theorem assemble_identity : assemble C C (identity A) (identity_isLawful C) = CategoryTheory.Equivalence.refl := by
  have he : (⟨identity A, identity_isLawful C⟩ : {r // IsLawful C.le C.le r}) =
      ⟨read C C CategoryTheory.Equivalence.refl, read_isLawful C C _⟩ := Subtype.ext (identity_eq_read C)
  exact (congrArg (readingEquiv C C).symm he).trans (assemble_read C C _)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Context

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Context
