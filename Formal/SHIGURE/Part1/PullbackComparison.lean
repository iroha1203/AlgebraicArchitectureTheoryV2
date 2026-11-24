import Formal.SHIGURE.Part1.Pullback
import Mathlib.CategoryTheory.EqToHom

/-! # Exact comparison of model pullbacks

Theorem 2.4 compares structures on equal carrier families by their primitive
facts. Those facts recover each relation, domain and operation value. This
proves equality of the functors and independence of their interpretation
representatives on the actual quotient of Appendix A.
-/

universe u

namespace SHIGURE.Assignment

variable {S T U : Type u} {Γ : List S} {Y : U → Type u}

/-- Reindexing the tuple by the composite reads the same variables as two successive retypings. -/
theorem mapSorts_comp_pull (f : S → T) (g : T → U) (xs : Assignment (Y ∘ g ∘ f) Γ) :
    (xs.mapSorts (g ∘ f)).pull (Renaming.castContext List.map_map) =
      ((xs.mapSorts f).mapSorts g) := by
  let direct := (xs.mapSorts (g ∘ f)).pull (Renaming.castContext List.map_map)
  let successive := (xs.mapSorts f).mapSorts g
  show direct = successive
  apply ext_mapSorts g
  refine @Var.forall_mapSorts S T Γ f (fun {_} i =>
    direct (i.mapSorts g) = successive (i.mapSorts g)) ?_
  intro s i
  dsimp only [direct, successive]
  simp only [pull_apply, Renaming.castContext_mapSorts_twice, mapSorts_apply]

/-- Reading an identity-retyped tuple in the original context recovers the input. -/
theorem mapSorts_id_pull {X : S → Type u} (xs : Assignment X Γ) :
    (xs.mapSorts id).pull (Renaming.castContext (List.map_id Γ).symm) = xs := by
  apply ext
  intro s i
  rw [pull_apply, ← Renaming.mapSorts_id_eq_castContext, mapSorts_apply]

end SHIGURE.Assignment

namespace SHIGURE.Formula

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType}

/-- A transported formula reads the assignment at the corresponding original positions. -/
theorem holds_castContext (same : Γ = Δ) (p : Formula sig Γ) (A : Structure sig)
    (xs : Assignment A.carrier Δ) :
    (p.castContext same).Holds A xs ↔ p.Holds A (xs.pull (Renaming.castContext same)) := by
  rw [castContext_eq_rename, holds_rename]

end SHIGURE.Formula

namespace SHIGURE.Structure

variable {sig : Signature.{u}}

/-- Theorem 2.4 uses equal carriers and equivalent satisfaction of all positive
formulas at corresponding assignments. The atomic instances of the comparison
recover the relations, domains and values that determine the structure. -/
theorem eq_of_formula_holds_iff {A B : Structure sig} (carriers : A.carrier = B.carrier)
    (same : ∀ {Γ : List sig.SortType} (p : Formula sig Γ) (xs : Assignment A.carrier Γ),
      p.Holds A xs ↔ p.Holds B (cast (congrArg (fun X => Assignment X Γ) carriers) xs)) :
    A = B := by
  rcases A with ⟨X, aTotal, aRelation, aDomain, aPartial, aQuantity⟩
  rcases B with ⟨Y, bTotal, bRelation, bDomain, bPartial, bQuantity⟩
  cases carriers
  let A : Structure sig := ⟨X, aTotal, aRelation, aDomain, aPartial, aQuantity⟩
  let B : Structure sig := ⟨X, bTotal, bRelation, bDomain, bPartial, bQuantity⟩
  have rel : aRelation = bRelation := by
    funext r
    apply Set.ext
    intro xs
    have checked := same (.atom (.rel r (fun i => i))) xs
    simpa only [Formula.holds_atom, Atomic.holds_rel, Assignment.pull_id, cast_eq] using checked
  have domain : aDomain = bDomain := by
    funext p
    apply Set.ext
    intro xs
    have checked := same (.atom (.domain p (fun i => i))) xs
    simpa only [Formula.holds_atom, Atomic.holds_domain, Assignment.pull_id, cast_eq] using checked
  have graphs (op : Operation sig) (xs : Assignment X op.arity.inputs) (y : X op.arity.output) :
      A.Graph op xs y ↔ B.Graph op xs y := by
    have checked := same (.atom (.graph op (fun i => .there i) .here)) (Assignment.cons y xs)
    simpa only [Formula.holds_atom, Atomic.holds_graph, Assignment.pull_cons_there,
      Assignment.pull_id, Assignment.cons_here, cast_eq] using checked
  refine Structure.ext (A := A) (B := B) rfl ?_ (heq_of_eq rel) (heq_of_eq domain) ?_ ?_
  · apply heq_of_eq
    funext f xs
    have held := (A.graph_total_iff f xs _).2 rfl
    exact ((B.graph_total_iff f xs _).1 ((graphs (.total f) xs _).1 held)).symm
  · apply partialValue_heq domain
    intro p xs hx
    have held := (A.graph_partial_iff p xs.val _).2 ⟨xs.property, rfl⟩
    obtain ⟨_, value⟩ := (B.graph_partial_iff p xs.val _).1 ((graphs (.partialOp p) xs.val _).1 held)
    exact value.symm
  · apply heq_of_eq
    funext q xs
    have held := (A.graph_quantity_iff q xs _).2 rfl
    exact ((B.graph_quantity_iff q xs _).1 ((graphs (.quantity q) xs _).1 held)).symm

end SHIGURE.Structure

namespace SHIGURE.Model

open CategoryTheory

/-- A model equality transports its identity arrow along the equality of each carrier. -/
theorem eqToHom_apply {T : Theory.{u}} {A B : Model T} (same : A = B)
    (s : T.signature.SortType) (x : A.obj.carrier s) :
    (InducedCategory.Hom.hom (eqToHom same)).onSort s x =
      cast (congrArg (fun M : Model T => M.obj.carrier s) same) x := by
  cases same
  rw [eqToHom_refl, id_apply]
  rfl

end SHIGURE.Model

namespace SHIGURE.Interpretation

open CategoryTheory

variable {S T U : Theory.{u}}

/-- The identity interpretation transports each model back to the same structure. -/
private theorem pullback_identity_obj (B : Model T) : (identity T).pullback.obj B = B := by
  apply ObjectProperty.FullSubcategory.ext
  refine Structure.eq_of_formula_holds_iff rfl ?_
  intro Γ p xs
  simp only [cast_eq]
  refine ((identity T).pullback_formula_iff B.obj B.property p xs).trans ?_
  refine ((Translation.identityFormula_cast_equivalent p).holds_iff B.obj B.property _).trans ?_
  have tuple :
      (xs.mapSorts (identity T).onSort).pull (Renaming.castContext (List.map_id Γ).symm) = xs :=
    Assignment.mapSorts_id_pull xs
  rw [Formula.holds_castContext, tuple]

/-- Theorem 2.4: pulling back along the identity gives the identity functor. -/
theorem pullback_identity (T : Theory.{u}) : (identity T).pullback = 𝟭 (Model T) := by
  refine Functor.ext pullback_identity_obj ?_
  intro B C f
  apply Model.hom_ext
  intro s x
  simp only [Functor.id_map, Model.comp_apply, Model.eqToHom_apply, pullback_map_apply]
  rfl

/-- The composite and the two successive pullbacks recover the same model object. -/
private theorem pullback_comp_obj (v : Interpretation T U) (u : Interpretation S T) (C : Model U) :
    (v.comp u).pullback.obj C = u.pullback.obj (v.pullback.obj C) := by
  apply ObjectProperty.FullSubcategory.ext
  refine Structure.eq_of_formula_holds_iff rfl ?_
  intro Γ p xs
  simp only [cast_eq]
  have onFirst := u.pullback_formula_iff (v.pullback.obj C).obj (v.pullback.obj C).property p xs
  have onSecond := v.pullback_formula_iff C.obj C.property (u.translation.formula p)
    (xs.mapSorts u.onSort)
  have combined := (v.translation.comp_formula_equivalent u.translation p).holds_iff C.obj C.property
    (xs.mapSorts ((v.comp u).onSort))
  have tuple :
      (xs.mapSorts (v.comp u).onSort).pull
        (Renaming.castContext (List.map_map (f := u.onSort) (g := v.onSort) (l := Γ))) =
        (xs.mapSorts u.onSort).mapSorts v.onSort :=
    Assignment.mapSorts_comp_pull u.onSort v.onSort xs
  rw [Formula.holds_castContext, tuple] at combined
  exact ((v.comp u).pullback_formula_iff C.obj C.property p xs).trans
    (combined.trans (onFirst.trans onSecond).symm)

/-- Theorem 2.4: pullback reverses the order of composition as a strict equality of functors. -/
theorem pullback_comp (v : Interpretation T U) (u : Interpretation S T) :
    (v.comp u).pullback = v.pullback ⋙ u.pullback := by
  refine Functor.ext (pullback_comp_obj v u) ?_
  intro A B f
  apply Model.hom_ext
  intro s x
  simp only [Functor.comp_map, Model.comp_apply, Model.eqToHom_apply, pullback_map_apply]
  rfl

/-- Theorem 2.4: equivalent interpretations induce the same model functor. -/
theorem pullback_eq_of_equivalent {v u : Interpretation S T} (same : v.Equivalent u) :
    v.pullback = u.pullback := by
  have sorts := same.onSort_eq
  rcases v with ⟨f, trV, totalV, quantityV, domainV, reflectV, lawsV⟩
  rcases u with ⟨g, trU, totalU, quantityU, domainU, reflectU, lawsU⟩
  cases sorts
  let left : Interpretation S T := ⟨f, trV, totalV, quantityV, domainV, reflectV, lawsV⟩
  let right : Interpretation S T := ⟨f, trU, totalU, quantityU, domainU, reflectU, lawsU⟩
  have replacements := same.translation_equivalent
  show left.pullback = right.pullback
  refine Functor.ext (fun B => ?_) ?_
  · apply ObjectProperty.FullSubcategory.ext
    refine Structure.eq_of_formula_holds_iff rfl ?_
    intro Γ p xs
    simp only [cast_eq]
    exact (left.pullback_formula_iff B.obj B.property p xs).trans
      ((replacements.formula_holds_iff B.obj B.property p (xs.mapSorts f)).trans
        (right.pullback_formula_iff B.obj B.property p xs).symm)
  · intro A B f
    apply Model.hom_ext
    intro s x
    simp only [Model.comp_apply, Model.eqToHom_apply, pullback_map_apply]
    rfl

end SHIGURE.Interpretation
