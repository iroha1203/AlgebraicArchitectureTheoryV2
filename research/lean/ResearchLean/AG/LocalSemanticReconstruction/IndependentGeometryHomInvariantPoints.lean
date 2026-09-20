import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantQuotient
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInvariantSignaturePrimitiveReadings
import Formal.Util.AssertStandardAxioms

/-!
# Invariant transport laws on primitive object readings

The source and target of these rules are primitive invariant tables. Kind tags,
carrier references, and individual evaluations select the rule. Completed
invariants appear only in the theorem connecting these rules to native assembly.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

namespace Primitive

open IndependentInvariantSignaturePrimitive

/-- One function-evaluation rule reads two value cells, one object cell, and one auxiliary cell. -/
def FunctionPoint (s t : Invariants.Table U) (M N K L : Type u) (i : M) (j : N)
    (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w : IndependentInverseGraph.Table.{u, u})
    (A B : ArchitectureObject U) (x : K) (y : L) : Prop :=
  h (.object A B) = true → (s (.value M i K A)).down = some x →
    (t (.value N j L B)).down = some y → w (.forward (.edge K L x y)) = true

/-- One predicate rule reads its two predicate cells and the object edge. -/
def PredicatePoint (s t : Invariants.Table U) (M N : Type u) (i : M) (j : N)
    (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (A B : ArchitectureObject U) : Prop :=
  h (.object A B) = true → ((s (.predicate M i A)).down ↔ (t (.predicate N j B)).down)

/-- Closed kind dispatch uses only the two original kind responses and primitive point rules. -/
def Row (s t : Invariants.Table U) (M N : Type u) (i : M) (j : N)
    (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w : IndependentInverseGraph.Table.{u, u}) : Prop :=
  match s (.kind M i), t (.kind N j) with
  | some (.function K), some (.function L) =>
      IndependentInverseGraph.IsLawful K L w ∧ ∀ A B x y, FunctionPoint s t M N K L i j h w A B x y
  | some .predicate, some .predicate => ∀ A B, PredicatePoint s t M N i j h A B
  | _, _ => False

/-- A selected primitive value response is exactly the value assembled from that response. -/
theorem value_response (s : Invariants.Table U) (hs : Invariants.IsTyped s)
    (i : Invariants.index s) (K : Type u) (hk : Invariants.kind s hs i = .function K)
    (A : ArchitectureObject U) :
    (s (.value _ i K A)).down = some (Invariants.value s hs i K hk A) :=
  (Option.some_get _).symm

/-- Primitive row rules and assembled native row rules agree for both kinds and reject mixed kinds. -/
theorem row_iff (s t : Invariants.Table U) (hs : Invariants.IsTyped s) (ht : Invariants.IsTyped t)
    (i : Invariants.index s) (j : Invariants.index t)
    (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w : IndependentInverseGraph.Table.{u, u}) :
    Row s t _ _ i j h w ↔ RowLaw (Invariants.invariant s hs i) (Invariants.invariant t ht j) h w := by
  cases hk : Invariants.kind s hs i with
  | function K =>
    rw [Invariants.invariant_function s hs i K hk]
    cases hl : Invariants.kind t ht j with
    | function L =>
      rw [Invariants.invariant_function t ht j L hl]
      simp only [Row, Invariants.kind_some s hs i, Invariants.kind_some t ht j, hk, hl, RowLaw]
      constructor
      · rintro ⟨hg, hp⟩
        refine ⟨hg, fun A B hAB => ?_⟩
        exact hp A B _ _ hAB (value_response s hs i K hk A) (value_response t ht j L hl B)
      · rintro ⟨hg, hp⟩
        refine ⟨hg, ?_⟩
        intro A B x y hAB hx hy
        have hx' : Invariants.value s hs i K hk A = x :=
          Option.some.inj ((value_response s hs i K hk A).symm.trans hx)
        have hy' : Invariants.value t ht j L hl B = y :=
          Option.some.inj ((value_response t ht j L hl B).symm.trans hy)
        subst x
        subst y
        exact hp A B hAB
    | predicate =>
      rw [Invariants.invariant_predicate t ht j hl]
      simp [Row, Invariants.kind_some s hs i, Invariants.kind_some t ht j, hk, hl, RowLaw]
  | predicate =>
    rw [Invariants.invariant_predicate s hs i hk]
    cases hl : Invariants.kind t ht j with
    | function L =>
      rw [Invariants.invariant_function t ht j L hl]
      simp [Row, Invariants.kind_some s hs i, Invariants.kind_some t ht j, hk, hl, RowLaw]
    | predicate =>
      rw [Invariants.invariant_predicate t ht j hl]
      simp [Row, Invariants.kind_some s hs i, Invariants.kind_some t ht j, hk, hl,
        RowLaw, PredicatePoint]

/-- Point rules for every active index produce the original invariant preservation proof. -/
theorem transports_of_rows (s t : Invariants.Table U) (hs : Invariants.IsTyped s)
    (ht : Invariants.IsTyped t)
    (r : Retained.{u, v} (Invariants.assemble s hs) (Invariants.assemble t ht) mode)
    (w : Table.{u})
    (hr : ∀ (i : Invariants.index s) (j : Invariants.index t), r.table (.invariant (.edge _ _ i j)) = true →
      Row s t _ _ i j r.table (row w _ _ i j)) :
    ∀ i, Invariant.TransportedAlong (Invariants.invariant s hs i)
      (Invariants.invariant t ht (r.indexMap i)) id r.objectMap := by
  intro i
  apply transported_of_row r _ _ (row w _ _ i (r.indexMap i))
  exact (row_iff s t hs ht i _ _ _).1 (hr i _ ((r.index_point_iff i _).2 rfl))

/-- Four explicit cells form a support for each function-preservation instance. -/
theorem functionPoint_of_same_cells (s s' t t' : Invariants.Table U)
    (M N K L : Type u) (i : M) (j : N)
    (h h' : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w w' : IndependentInverseGraph.Table.{u, u})
    (A B : ArchitectureObject U) (x : K) (y : L)
    (hs : s (.value M i K A) = s' (.value M i K A))
    (ht : t (.value N j L B) = t' (.value N j L B))
    (hh : h (.object A B) = h' (.object A B))
    (hw : w (.forward (.edge K L x y)) = w' (.forward (.edge K L x y))) :
    FunctionPoint s t M N K L i j h w A B x y ↔ FunctionPoint s' t' M N K L i j h' w' A B x y := by
  unfold FunctionPoint
  rw [hs, ht, hh, hw]

/-- Three explicit cells form a support for each predicate-preservation instance. -/
theorem predicatePoint_of_same_cells (s s' t t' : Invariants.Table U)
    (M N : Type u) (i : M) (j : N)
    (h h' : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (A B : ArchitectureObject U)
    (hs : s (.predicate M i A) = s' (.predicate M i A))
    (ht : t (.predicate N j B) = t' (.predicate N j B))
    (hh : h (.object A B) = h' (.object A B)) :
    PredicatePoint s t M N i j h A B ↔ PredicatePoint s' t' M N i j h' A B := by
  unfold PredicatePoint
  rw [hs, ht, hh]

end Primitive

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
