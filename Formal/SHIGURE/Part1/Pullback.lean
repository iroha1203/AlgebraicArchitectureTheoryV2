import Formal.SHIGURE.Part1.Models
import Formal.SHIGURE.Part1.PositiveLogic
import Formal.SHIGURE.Part1.Reading

/-! # Model pullback along a theory interpretation

Theorem 2.4 uses the existing semantics of the pulled-back structures from
Reading. Graph comparison from Appendix A.3 gives term equality on the same
carriers, and structure maps preserve the interpreted primitive graphs.

## Implementation notes

Maps carry the original structure-map components on the renamed sorts.
Comparing the function-valued part at all inputs and its domain will give
strict equalities for composition, identity and equivalent representatives.
These equalities allow the model categories to be assembled into the ordinary
contravariant functor to mathlib's category of categories. Natural
isomorphisms with separate coherence data would also express the
comparison. Matching primitive interpretations on the same carriers
gives the stronger, strict comparison used here.
-/

universe u

namespace SHIGURE.Assignment

variable {S T : Type u} {Γ : List S} {X Y : T → Type u}

/-- Mapping carrier values commutes with retyping an assignment to the translated sorts. -/
theorem mapSorts_map (sorts : S → T) (xs : Assignment (X ∘ sorts) Γ) (f : ∀ s, X s → Y s) :
    (xs.map (fun s => f (sorts s))).mapSorts sorts = (xs.mapSorts sorts).map f := by
  apply ext_mapSorts sorts
  intro s i
  simp only [mapSorts_apply, map_apply]

end SHIGURE.Assignment

namespace SHIGURE.Interpretation

open CategoryTheory

variable {S T : Theory.{u}}

/-- Equation (2.5) applied to the graph of a term gives the same values under translation. -/
theorem pullback_evaluates_iff (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) {Γ : List S.signature.SortType} {s : S.signature.SortType}
    (t : Term S.signature Γ s) (xs : Assignment (u.pullbackStructure B model).carrier Γ)
    (y : (u.pullbackStructure B model).carrier s) :
    t.Evaluates (u.pullbackStructure B model) xs y ↔
      (u.translation.term t).Evaluates B (xs.mapSorts u.onSort) y := by
  rw [← Term.mem_eval_iff, ← Term.holds_graph_iff,
    ← Term.mem_eval_iff, ← Term.holds_graph_iff, u.pullback_formula_iff, Assignment.mapSorts_cons]
  exact ((u.translation.graph_equivalent t).holds_iff B model _).symm

/-- The possibly partial evaluation is equal on the aligned carriers in Theorem 2.4. -/
theorem pullback_eval_eq (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) {Γ : List S.signature.SortType} {s : S.signature.SortType}
    (t : Term S.signature Γ s) (xs : Assignment (u.pullbackStructure B model).carrier Γ) :
    t.eval (u.pullbackStructure B model) xs = (u.translation.term t).eval B (xs.mapSorts u.onSort) := by
  apply Part.ext
  intro y
  rw [Term.mem_eval_iff, Term.mem_eval_iff]
  exact u.pullback_evaluates_iff B model t xs y

/-- A term is defined in the pullback exactly when its translation is defined in the target model. -/
theorem pullback_mem_domain_iff (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) {Γ : List S.signature.SortType} {s : S.signature.SortType}
    (t : Term S.signature Γ s) (xs : Assignment (u.pullbackStructure B model).carrier Γ) :
    xs ∈ t.domain (u.pullbackStructure B model) ↔
      xs.mapSorts u.onSort ∈ (u.translation.term t).domain B := by
  rw [Term.mem_domain_iff, Term.mem_domain_iff, u.pullback_eval_eq]

/-- The underlying structure of the pulled-back model is given by the interpretation. -/
noncomputable def pullbackModel (u : Interpretation S T) (B : Model T) : Model S :=
  ⟨u.pullbackStructure B.obj B.property, u.pullback_isModel B.obj B.property⟩

/-- Model pullback uses exactly the Chapter 1 pullback structure. -/
theorem pullbackModel_obj (u : Interpretation S T) (B : Model T) :
    (u.pullbackModel B).obj = u.pullbackStructure B.obj B.property :=
  rfl

variable {B C : Model T}

/-- Reindexed components carry each interpreted graph by Theorem 1.8 on the replacement term. -/
private theorem pullbackGraph_map (u : Interpretation S T) (f : B ⟶ C)
    (op : Operation S.signature)
    (xs : Assignment (u.pullbackModel B).obj.carrier op.arity.inputs)
    (y : (u.pullbackModel B).obj.carrier op.arity.output)
    (held : (u.pullbackModel B).obj.Graph op xs y) :
    (u.pullbackModel C).obj.Graph op (xs.map (fun s => f.hom.onSort (u.onSort s)))
      (f.hom.onSort (u.onSort op.arity.output) y) := by
  apply (u.pullback_graph_iff C.obj C.property _ _ _).2
  rw [Assignment.mapSorts_map]
  exact f.hom.evaluates_map _ _ _ ((u.pullback_graph_iff B.obj B.property _ _ _).1 held)

/-- A raw model map pulls back by reading its component at each translated sort, as in (2.4). -/
noncomputable def pullbackStructureMap (u : Interpretation S T) (f : B ⟶ C) :
    StructureMap (u.pullbackModel B).obj (u.pullbackModel C).obj where
  onSort s := f.hom.onSort (u.onSort s)
  total_comm g xs := by
    have held := ((u.pullbackModel B).obj.graph_total_iff g xs _).2 rfl
    exact (((u.pullbackModel C).obj.graph_total_iff g _ _).1
      (u.pullbackGraph_map f (.total g) xs _ held)).symm
  relation_mem r xs held := by
    apply (u.pullback_relation_iff C.obj C.property r _).2
    rw [Assignment.mapSorts_map]
    exact f.hom.holds_map _ _ ((u.pullback_relation_iff B.obj B.property r xs).1 held)
  partial_mem p xs held := by
    apply (u.pullback_partialDomain_iff C.obj C.property p _).2
    rw [Assignment.mapSorts_map]
    exact f.hom.holds_map _ _ ((u.pullback_partialDomain_iff B.obj B.property p xs).1 held)
  partial_comm p xs := by
    have held := ((u.pullbackModel B).obj.graph_partial_iff p xs.val _).2 ⟨xs.property, rfl⟩
    obtain ⟨_, value⟩ := ((u.pullbackModel C).obj.graph_partial_iff p _ _).1
      (u.pullbackGraph_map f (.partialOp p) xs.val _ held)
    exact value.symm
  quantity_comm q xs := by
    have held := ((u.pullbackModel B).obj.graph_quantity_iff q xs _).2 rfl
    exact (((u.pullbackModel C).obj.graph_quantity_iff q _ _).1
      (u.pullbackGraph_map f (.quantity q) xs _ held)).symm

/-- Model pullback is functorial in the structural arrows, as claimed by (2.4). -/
noncomputable def pullback (u : Interpretation S T) : Model T ⥤ Model S where
  obj := u.pullbackModel
  map f := ObjectProperty.homMk (u.pullbackStructureMap f)
  map_id B := by
    apply Model.hom_ext
    intro s x
    exact (Model.id_apply B (u.onSort s) x).trans (Model.id_apply (u.pullbackModel B) s x).symm
  map_comp f g := by
    apply Model.hom_ext
    intro s x
    exact (Model.comp_apply f g (u.onSort s) x).trans
      (Model.comp_apply (ObjectProperty.homMk (u.pullbackStructureMap f))
        (ObjectProperty.homMk (u.pullbackStructureMap g)) s x).symm

/-- The model pullback functor acts on objects by the interpreted structure. -/
theorem pullback_obj (u : Interpretation S T) (B : Model T) :
    u.pullback.obj B = u.pullbackModel B :=
  rfl

/-- Every component of the pulled-back arrow is the component at its translated sort. -/
@[simp] theorem pullback_map_apply (u : Interpretation S T) (f : B ⟶ C) (s : S.signature.SortType)
    (x : (u.pullback.obj B).obj.carrier s) :
    (u.pullback.map f).hom.onSort s x = f.hom.onSort (u.onSort s) x :=
  rfl

end SHIGURE.Interpretation
