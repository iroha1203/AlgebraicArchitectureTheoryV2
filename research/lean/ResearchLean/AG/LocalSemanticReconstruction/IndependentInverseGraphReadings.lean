import ResearchLean.AG.LocalSemanticReconstruction.IndependentCarrierGraphReadings
import Formal.Util.AssertStandardAxioms

/-!
# Pointwise inverse graphs before carrier selection

Two direction-tagged candidate-carrier graphs are related by a two-cell
inverse condition. The native inverse functions are derived from exact-one
rows and this point condition; no function inverse equation is stored as a
local field. The common query type precedes the selected two carriers.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentInverseGraph

noncomputable section

universe u v

/-- Direction-tagged candidate point pairs, before any native carriers are selected. -/
inductive Query where
  /-- Forward carrier-graph cell. -/
  | forward (q : IndependentCarrierGraph.Query.{u, v})
  /-- Backward carrier-graph cell, in target-to-source order. -/
  | backward (q : IndependentCarrierGraph.Query.{v, u})

/-- Each local response is one Boolean. -/
abbrev Table := Query.{u, v} → Bool

/-- Forward primitive cells form a candidate-carrier graph table. -/
def forward (t : Table.{u, v}) : IndependentCarrierGraph.Table.{u, v} := fun q => t (.forward q)

/-- Backward primitive cells form the opposite-direction candidate-carrier graph table. -/
def backward (t : Table.{u, v}) : IndependentCarrierGraph.Table.{v, u} := fun q => t (.backward q)

/-- The two total-functional directions are inverse exactly at each raw point pair. -/
structure IsLawful (α : Type u) (β : Type v) (t : Table.{u, v}) : Prop where
  /-- Forward totality, uniqueness, and inactive-carrier normalization. -/
  forward : IndependentCarrierGraph.IsLawful α β (IndependentInverseGraph.forward t)
  /-- Backward totality, uniqueness, and inactive-carrier normalization. -/
  backward : IndependentCarrierGraph.IsLawful β α (IndependentInverseGraph.backward t)
  /-- A forward pair is true exactly when its reversed backward pair is true. -/
  inverse : ∀ x : α, ∀ y : β,
    t (.forward (.edge α β x y)) = true ↔ t (.backward (.edge β α y x)) = true

variable (α : Type u) (β : Type v)

/-- Assemble the native equivalence using unique graph outputs and the pointwise inverse condition. -/
def assemble (t : Table.{u, v}) (h : IsLawful α β t) : α ≃ β where
  toFun := IndependentCarrierGraph.assemble α β (forward t) h.forward
  invFun := IndependentCarrierGraph.assemble β α (backward t) h.backward
  left_inv x := IndependentCarrierGraph.assemble_eq_of_edge β α (backward t) h.backward
    ((h.inverse x _).1 (IndependentCarrierGraph.edge_assemble α β (forward t) h.forward x))
  right_inv y := IndependentCarrierGraph.assemble_eq_of_edge α β (forward t) h.forward
    ((h.inverse _ y).2 (IndependentCarrierGraph.edge_assemble β α (backward t) h.backward y))

/-- Read both native directions as their primitive candidate point-pair graphs. -/
def read (e : α ≃ β) : Table.{u, v}
  | .forward q => IndependentCarrierGraph.read α β e q
  | .backward q => IndependentCarrierGraph.read β α e.symm q

/-- Every native equivalence satisfies the independent totality and two-cell inverse rules. -/
theorem read_isLawful (e : α ≃ β) : IsLawful α β (read α β e) where
  forward := IndependentCarrierGraph.read_isLawful α β e
  backward := IndependentCarrierGraph.read_isLawful β α e.symm
  inverse x y := by
    change IndependentCarrierGraph.read α β e (.edge α β x y) = true ↔
      IndependentCarrierGraph.read β α e.symm (.edge β α y x) = true
    rw [IndependentCarrierGraph.read_edge, IndependentCarrierGraph.read_edge]
    constructor
    · intro h
      rw [← h]
      exact e.symm_apply_apply x
    · intro h
      rw [← h]
      exact e.apply_symm_apply y

/-- Assembly restores every native equivalence, rather than only a selected subfamily. -/
theorem assemble_read (e : α ≃ β) : assemble α β (read α β e) (read_isLawful α β e) = e := by
  apply Equiv.ext
  intro x
  exact congrFun (IndependentCarrierGraph.assemble_read α β e) x

/-- Both candidate graphs, including all inactive carriers, are restored after assembly. -/
theorem read_assemble (t : Table.{u, v}) (h : IsLawful α β t) :
    read α β (assemble α β t h) = t := by
  funext q
  cases q with
  | forward q => exact congrFun (IndependentCarrierGraph.read_assemble α β (forward t) h.forward) q
  | backward q => exact congrFun (IndependentCarrierGraph.read_assemble β α (backward t) h.backward) q

/-- Native equivalences and the independent candidate point tables have exact inverse presentations. -/
def readingEquiv : (α ≃ β) ≃ {t : Table.{u, v} // IsLawful α β t} where
  toFun e := ⟨read α β e, read_isLawful α β e⟩
  invFun t := assemble α β t.val t.property
  left_inv := assemble_read α β
  right_inv t := Subtype.ext (read_assemble α β t.val t.property)

/-- Point readings separate every forward and inverse native equivalence. -/
theorem read_injective : Function.Injective (read α β) := by
  intro e f h
  exact (readingEquiv α β).injective (Subtype.ext h)

/-- Each inverse-law instance has exactly its two primitive graph cells as a finite support. -/
def inverseSupport (x : α) (y : β) : Finset Query.{u, v} := by
  classical
  exact {.forward (.edge α β x y), .backward (.edge β α y x)}

/-- Arbitrary tables agreeing at the two inverse cells agree on this inverse-law instance. -/
theorem inverse_iff_of_support (t s : Table.{u, v}) (x : α) (y : β)
    (h : ∀ q ∈ inverseSupport α β x y, t q = s q) :
    (t (.forward (.edge α β x y)) = true ↔ t (.backward (.edge β α y x)) = true) ↔
      (s (.forward (.edge α β x y)) = true ↔ s (.backward (.edge β α y x)) = true) := by
  classical
  rw [h (.forward (.edge α β x y)) (by simp [inverseSupport]),
    h (.backward (.edge β α y x)) (by simp [inverseSupport])]

/-- A single forward/backward point mismatch refutes the equivalence laws. -/
theorem inverse_mismatch_rejected (t : Table.{u, v}) (x : α) (y : β)
    (hf : t (.forward (.edge α β x y)) = true) (hb : t (.backward (.edge β α y x)) = false) :
    ¬ IsLawful α β t := by
  intro h
  exact Bool.noConfusion (hb.symm.trans ((h.inverse x y).1 hf))

end

end AAT.AG.LocalSemanticReconstruction.IndependentInverseGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentInverseGraph
