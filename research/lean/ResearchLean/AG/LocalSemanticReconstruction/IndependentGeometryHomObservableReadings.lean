import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInverseRows
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedRingGraphs
import Formal.Util.AssertStandardAxioms

/-!
# Observable ring-equivalence families from the common Hom rows

The common forward-context graph selects the active observable fiber. Its
candidate inverse rows and primitive ring preservation construct every native
ring-equivalence family over the assembled context functor. Both inverse
readings include every inactive context/carrier row. Restriction naturality
is a separate preservation condition, not assumed by this family equivalence.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Observable

noncomputable section

universe u v

open Site CategoryTheory

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U} {mode : Mode}

/-- Observable point rows are projected directly from the common query, with the backward pair reversed. -/
def points (h : Table.{u, v} U mode) (A B : ArchitectureObject U) :
    IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx B)
  | .edge W V q => InverseRows.observable h A B W V q

/-- The raw context selected by the native functor is exactly the independent point-row index. -/
theorem context_index_eq (C : ContextPreorderCategory A) (D : ContextPreorderCategory B)
    (p : Context.PointTable A B) (hp : Context.IsLawful C.le D.le p) (W : ArchCtx A) :
    ((Context.assemble C D p hp).functor.obj ⟨W⟩).ctx =
      IndependentIndexedCarrierGraph.index (p .forward) hp.forward W := by
  change ((Context.code C D p hp).forwardCode.assemble ⟨W⟩).ctx = _
  symm
  exact (IndependentIndexedCarrierGraph.indexGraph (p .forward) hp.forward).target_eq_of_edge
    ((Context.code C D p hp).forwardCode.edge_target ⟨W⟩)

variable (C : ContextPreorderCategory A) (D : ContextPreorderCategory B)
variable (h : Table.{u, v} U mode) (hc : Context.IsLawful C.le D.le (Context.points h A B))
variable (S : ArchCtx A → Type u) (T : ArchCtx B → Type u)
variable [∀ W, CommRing (S W)] [∀ V, CommRing (T V)]

/-- The directed common forward-context graph used to activate observable rows. -/
def contextPoints (W : ArchCtx A) (V : ArchCtx B) : Bool := h (.atObjects A B (.context .forward W V))

/-- Native context wrapping and the proved index equation identify the two dependent ring-family types. -/
def nativeFamilyEquiv :
    (∀ W, S W ≃+* T (IndependentIndexedCarrierGraph.index (contextPoints h) hc.forward W)) ≃
      (∀ W : ContextCategoryObject C,
        S W.ctx ≃+* T (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)) where
  toFun f W := cast (congrArg (fun V => S W.ctx ≃+* T V)
    (context_index_eq C D (Context.points h A B) hc W.ctx).symm) (f W.ctx)
  invFun g W := cast (congrArg (fun V => S W ≃+* T V)
    (context_index_eq C D (Context.points h A B) hc W)) (g ⟨W⟩)
  left_inv f := by
    funext W
    simp only [cast_cast, cast_eq]
  right_inv g := by
    funext W
    cases W
    simp only [cast_cast, cast_eq]

/-- Observable family laws are candidate graph activation, inverse points, and primitive ring preservation. -/
abbrev IsLawful := IndependentIndexedRingGraph.IsLawful (contextPoints h) S T (points h A B)

/-- At any true context pair, construct its ring equivalence directly from that pair's point rows. -/
def atPair (hl : IsLawful h S T) (W : ArchCtx A) (V : ArchCtx B)
    (hp : contextPoints h W V = true) : S W ≃+* T V :=
  IndependentRingCarrierGraph.assembleEquiv (InverseRows.observable h A B W V)
    ⟨hl.graphs.active W V hp, hl.ring W V hp⟩

/-- A forward common point is true exactly at the reconstructed observable image. -/
theorem atPair_forward_iff (hl : IsLawful h S T) (W : ArchCtx A) (V : ArchCtx B)
    (hp : contextPoints h W V = true) (x : S W) (y : T V) :
    h (.atObjects A B (.observable .forward W V (.edge (S W) (T V) x y))) = true ↔
      atPair h S T hl W V hp x = y :=
  (IndependentCarrierGraph.graph (S W) (T V) _ (hl.graphs.active W V hp).forward.2).edge_eq_true_iff_target_eq x y

/-- The backward common point keeps source/target order while reading the native inverse image. -/
theorem atPair_backward_iff (hl : IsLawful h S T) (W : ArchCtx A) (V : ArchCtx B)
    (hp : contextPoints h W V = true) (x : S W) (y : T V) :
    h (.atObjects A B (.observable .backward W V (.edge (S W) (T V) x y))) = true ↔
      (atPair h S T hl W V hp).symm y = x :=
  (IndependentCarrierGraph.graph (T V) (S W) _ (hl.graphs.active W V hp).backward.2).edge_eq_true_iff_target_eq y x

/-- Changing a candidate target by equality only transports its dependent ring type. -/
theorem atPair_cast (hl : IsLawful h S T) (W : ArchCtx A) (V Y : ArchCtx B) (he : V = Y)
    (hv : contextPoints h W V = true) (hy : contextPoints h W Y = true) :
    cast (congrArg (fun X => S W ≃+* T X) he) (atPair h S T hl W V hv) =
      atPair h S T hl W Y hy := by
  cases he
  rfl

/-- Every native ring-equivalence family over the reconstructed context functor has an exact point presentation. -/
def readingEquiv :
    (∀ W : ContextCategoryObject C,
      S W.ctx ≃+* T (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)) ≃
      {t : IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx B) //
        IndependentIndexedRingGraph.IsLawful (contextPoints h) S T t} :=
  (nativeFamilyEquiv C D h hc S T).symm.trans
    (IndependentIndexedRingGraph.readingEquiv (contextPoints h) hc.forward S T)

/-- Construct the full native observable family from the common Hom's primitive row projection. -/
def assemble (hl : IsLawful h S T) :
    ∀ W : ContextCategoryObject C,
      S W.ctx ≃+* T (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx) :=
  (readingEquiv C D h hc S T).symm ⟨points h A B, hl⟩

/-- The context used by the native functor has its original true forward common point. -/
theorem forward_point (W : ContextCategoryObject C) :
    contextPoints h W.ctx (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx) = true :=
  (Context.code C D (Context.points h A B) hc).forwardCode.edge_target W

/-- The native observable-family component is exactly the ring equivalence built at its true context pair. -/
theorem assemble_eq_atPair (hl : IsLawful h S T) (W : ContextCategoryObject C) :
    assemble C D h hc S T hl W =
      atPair h S T hl W.ctx (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)
        (forward_point C D h hc W) := by
  change cast (congrArg (fun V => S W.ctx ≃+* T V)
      (context_index_eq C D (Context.points h A B) hc W.ctx).symm)
      (atPair h S T hl W.ctx (IndependentIndexedCarrierGraph.index (contextPoints h) hc.forward W.ctx)
        ((IndependentIndexedCarrierGraph.active_iff (contextPoints h) hc.forward W.ctx _).2 rfl)) = _
  exact atPair_cast h S T hl W.ctx _ _
    (context_index_eq C D (Context.points h A B) hc W.ctx).symm _ _

/-- Every candidate observable context/carrier point is restored after native family assembly. -/
theorem read_assemble (hl : IsLawful h S T) :
    (readingEquiv C D h hc S T (assemble C D h hc S T hl)).val = points h A B :=
  congrArg Subtype.val ((readingEquiv C D h hc S T).apply_symm_apply ⟨points h A B, hl⟩)

/-- All native observable ring-family components survive the point-reading round trip. -/
theorem assemble_read
    (f : ∀ W : ContextCategoryObject C,
      S W.ctx ≃+* T (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)) :
    (readingEquiv C D h hc S T).symm (readingEquiv C D h hc S T f) = f :=
  (readingEquiv C D h hc S T).symm_apply_apply f

/-- The observable point rows separate every native ring-equivalence family over this context map. -/
theorem read_injective : Function.Injective (fun f => (readingEquiv C D h hc S T f).val) := by
  intro f g he
  exact (readingEquiv C D h hc S T).injective (Subtype.ext he)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Observable

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Observable
