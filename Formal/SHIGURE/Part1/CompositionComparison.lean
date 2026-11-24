import Formal.SHIGURE.Part1.TranslationComparison

/-! # Comparison of composite translations

Two successive sort maps and the composite sort map present the same
typed contexts. The canonical transport between them retains all
variable positions, including those under binders.
-/

universe u

namespace SHIGURE.Renaming

variable {S T U : Type u} {Γ Δ : List S}

/-- The variable map induced by equality of the two contexts. -/
def castContext (same : Γ = Δ) : Renaming Γ Δ :=
  fun i => cast (congrArg (fun C => Var C _) same) i

/-- Context equality under a binder keeps that variable and transports the older positions. -/
theorem castContext_cons {s : S} (same : Γ = Δ) :
    @castContext S (s :: Γ) (s :: Δ) (congrArg (List.cons s) same) =
      @lift S Γ Δ s (castContext same) := by
  cases same
  funext t i
  cases i <;> rfl

/-- Reindexing a context equality simply reindexes the equality of lists. -/
theorem mapSorts_castContext (f : S → T) (same : Γ = Δ) :
    @mapSorts S T Γ Δ f (castContext same) =
      @castContext T (Γ.map f) (Δ.map f) (congrArg (List.map f) same) := by
  cases same
  exact mapSorts_id f

/-- Each variable has the same position after successive and composite retyping. -/
theorem castContext_mapSorts_twice (f : S → T) (g : T → U)
    {s : S} (i : Var Γ s) :
    castContext (List.map_map (g := g) (f := f) (l := Γ)) ((i.mapSorts f).mapSorts g) =
      i.mapSorts (g ∘ f) := by
  induction i with
  | @here Γ s =>
    change castContext (congrArg (List.cons (g (f s))) (List.map_map (g := g) (f := f) (l := Γ)))
      Var.here = Var.here
    rw [castContext_cons (List.map_map (g := g) (f := f) (l := Γ))]
    rfl
  | @there Γ s t i ih =>
    change castContext (congrArg (List.cons (g (f t))) (List.map_map (g := g) (f := f) (l := Γ)))
      ((i.mapSorts f).mapSorts g).there = (i.mapSorts (g ∘ f)).there
    rw [castContext_cons (List.map_map (g := g) (f := f) (l := Γ))]
    exact congrArg Var.there ih

/-- The context transport commutes with renaming variables on the two retypings. -/
theorem castContext_comp_mapSorts_twice (f : S → T) (g : T → U) (ρ : Renaming Γ Δ) :
    @comp U ((Γ.map f).map g) ((Δ.map f).map g) (Δ.map (g ∘ f))
      (castContext List.map_map) (mapSorts g (mapSorts f ρ)) =
      @comp U ((Γ.map f).map g) (Γ.map (g ∘ f)) (Δ.map (g ∘ f))
        (mapSorts (g ∘ f) ρ) (castContext List.map_map) := by
  apply ext_mapSorts g
  refine @Var.forall_mapSorts S T Γ f (fun {_} i =>
    castContext List.map_map (mapSorts g (mapSorts f ρ) (i.mapSorts g)) =
      mapSorts (g ∘ f) ρ (castContext List.map_map (i.mapSorts g))) ?_
  intro s i
  simp only [mapSorts_apply, castContext_mapSorts_twice]

/-- Retyping by the identity map transports the original context to its mapped form. -/
theorem mapSorts_id_eq_castContext {S : Type u} {Γ : List S} :
    (fun {_} (i : Var Γ _) => i.mapSorts id) =
      @castContext S Γ (Γ.map id) (List.map_id Γ).symm := by
  funext s i
  induction i with
  | @here Γ s =>
    change Var.here = castContext (congrArg (List.cons s) (List.map_id Γ).symm) Var.here
    rw [castContext_cons (List.map_id Γ).symm]
    rfl
  | @there Γ s t i ih =>
    change (i.mapSorts id).there = castContext (congrArg (List.cons t) (List.map_id Γ).symm) i.there
    rw [castContext_cons (List.map_id Γ).symm]
    exact congrArg Var.there ih

end SHIGURE.Renaming

namespace SHIGURE.Formula

variable {sig : Signature.{u}} {Γ Δ E Γ' Δ' : List sig.SortType}

/-- Transporting a formula renames it along the context equality. -/
theorem castContext_eq_rename (same : Γ = Δ) (p : Formula sig Γ) :
    p.castContext same = p.rename (Renaming.castContext same) := by
  cases same
  exact (Formula.rename_id _).symm

/-- Two consecutive context transports equal their composite. -/
theorem castContext_trans (h : Γ = Δ) (k : Δ = E) (p : Formula sig Γ) :
    (p.castContext h).castContext k = p.castContext (h.trans k) := by
  cases h
  cases k
  rfl

/-- Transport along reflexivity returns the same formula. -/
@[simp] theorem castContext_rfl (p : Formula sig Γ) : p.castContext rfl = p := rfl

/-- A commuting square of variable maps gives a commuting square of formula transports. -/
theorem rename_castContext_comm (src : Γ = Γ') (dst : Δ = Δ') (p : Formula sig Γ)
    (ρ : Renaming Γ Δ) (ρ' : Renaming Γ' Δ')
    (square : @Renaming.comp sig.SortType Γ Δ Δ' (Renaming.castContext dst) ρ =
      @Renaming.comp sig.SortType Γ Γ' Δ' ρ' (Renaming.castContext src)) :
    (p.rename ρ).castContext dst = (p.castContext src).rename ρ' := by
  simp only [castContext_eq_rename, rename_comp, square]

/-- Equality of contexts transports both parts of a conjunction. -/
theorem castContext_conj (same : Γ = Δ) (p q : Formula sig Γ) :
    (p.conj q).castContext same = (p.castContext same).conj (q.castContext same) := by
  cases same
  rfl

/-- Equality of contexts transports both parts of a disjunction. -/
theorem castContext_disj (same : Γ = Δ) (p q : Formula sig Γ) :
    (p.disj q).castContext same = (p.castContext same).disj (q.castContext same) := by
  cases same
  rfl

/-- Equality of contexts transports the body of an existential under its binder. -/
theorem castContext_ex (same : Γ = Δ) {s : sig.SortType} (p : Formula sig (s :: Γ)) :
    p.ex.castContext same = (p.castContext (congrArg (List.cons s) same)).ex := by
  cases same
  rfl

/-- Truth is invariant under transport of the context. -/
@[simp] theorem castContext_truth (same : Γ = Δ) :
    (Formula.truth : Formula sig Γ).castContext same = .truth := by
  cases same
  rfl

/-- Falsehood is invariant under transport of the context. -/
@[simp] theorem castContext_falsehood (same : Γ = Δ) :
    (Formula.falsehood : Formula sig Γ).castContext same = .falsehood := by
  cases same
  rfl

end SHIGURE.Formula

namespace SHIGURE.Term

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType} {s : sig.SortType}

/-- The graph of a transported term also transports its older context. -/
theorem castContext_graph (same : Γ = Δ) (t : Term sig Γ s) :
    (t.castContext same).graph = t.graph.castContext (congrArg (List.cons s) same) := by
  cases same
  rfl

/-- The definedness of a transported term transports its context. -/
theorem castContext_defined (same : Γ = Δ) (t : Term sig Γ s) :
    (t.castContext same).defined = t.defined.castContext same := by
  cases same
  rfl

end SHIGURE.Term

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ Δ : List T.signature.SortType} {p q : Formula T.signature Γ}

/-- Both ends of a sequent can use the new presentation of the same context. -/
def castContext (same : Γ = Δ) (d : Derivation T p q) :
    Derivation T (p.castContext same) (q.castContext same) := by
  cases same
  exact d

/-- Mutual derivability is stable under transport of both contexts. -/
theorem Equivalent.castContext (same : Γ = Δ) (h : Equivalent T p q) :
    Equivalent T (p.castContext same) (q.castContext same) := by
  cases same
  exact h

end SHIGURE.Derivation

namespace SHIGURE.Translation

variable {S T U : Theory.{u}}
  {f : S.signature.SortType → T.signature.SortType} {g : T.signature.SortType → U.signature.SortType}

/-- Translating a formula transports its context equality along the sort map. -/
theorem formula_castContext {Γ Δ : List S.signature.SortType}
    (tr : Translation S.signature T.signature f) (same : Γ = Δ) (p : Formula S.signature Γ) :
    tr.formula (p.castContext same) = (tr.formula p).castContext (congrArg (List.map f) same) := by
  cases same
  rfl

/-- The same primitive graph is derivable under a composite replacement and two successive replacements. -/
theorem comp_atomic_equivalent (v : Translation T.signature U.signature g)
    (u : Translation S.signature T.signature f) {Γ : List S.signature.SortType} (a : Atomic S.signature Γ) :
    Derivation.Equivalent U ((v.comp u).atomic a)
      ((v.formula (u.atomic a)).castContext List.map_map) := by
  cases a with
  | eq x y =>
    change Derivation.Equivalent U (.atom (.eq (x.mapSorts (g ∘ f)) (y.mapSorts (g ∘ f))))
      ((Formula.atom (.eq ((x.mapSorts f).mapSorts g) ((y.mapSorts f).mapSorts g))).castContext List.map_map)
    simp only [Formula.castContext_eq_rename, Formula.rename_atom, Atomic.rename_eq,
      Renaming.castContext_mapSorts_twice]
    exact .refl _
  | rel r inputs =>
    simp only [atomic_rel, comp_relation, formula_rename]
    rw [Formula.rename_castContext_comm _ _ _ _ _ (Renaming.castContext_comp_mapSorts_twice f g inputs)]
    exact .refl _
  | domain p inputs =>
    simp only [atomic_domain, comp_partialDomain, formula_rename]
    rw [Formula.rename_castContext_comm _ _ _ _ _ (Renaming.castContext_comp_mapSorts_twice f g inputs)]
    exact .refl _
  | graph op inputs y =>
    simp only [atomic_graph, comp_operation, Term.castContext_graph, formula_rename]
    have natural := Renaming.castContext_comp_mapSorts_twice f g (Renaming.cons y inputs)
    simp only [Renaming.mapSorts_cons] at natural
    simp only [Renaming.mapSorts_cons]
    rw [← Formula.rename_castContext_comm _ _ _ _ _ natural]
    exact ((v.graph_equivalent (u.operation op)).rename _).castContext _

/-- Appendix A.3: composite and iterated formula translations are mutually derivable. -/
theorem comp_formula_equivalent (v : Translation T.signature U.signature g)
    (u : Translation S.signature T.signature f) {Γ : List S.signature.SortType} (p : Formula S.signature Γ) :
    Derivation.Equivalent U ((v.comp u).formula p)
      ((v.formula (u.formula p)).castContext List.map_map) := by
  induction p with
  | atom a => exact v.comp_atomic_equivalent u a
  | truth => simp only [formula_truth, Formula.castContext_truth]; exact .refl _
  | falsehood => simp only [formula_falsehood, Formula.castContext_falsehood]; exact .refl _
  | conj p q hp hq => simpa only [formula_conj, Formula.castContext_conj] using hp.conj hq
  | disj p q hp hq => simpa only [formula_disj, Formula.castContext_disj] using hp.disj hq
  | ex p ih => simpa only [formula_ex, Formula.castContext_ex] using ih.ex

end SHIGURE.Translation
