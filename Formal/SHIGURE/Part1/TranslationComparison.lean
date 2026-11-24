import Formal.SHIGURE.Part1.PositiveTranslation
import Formal.SHIGURE.Part1.StrictArguments
import Formal.SHIGURE.Part1.SubstitutionDerivations

/-! # Comparing translated syntax by derivations

Appendix A.3 compares the formulas themselves using positive derivations.
The congruence rules retain the original witnesses and support comparison
under all the positive logical constructors.
-/

universe u

namespace SHIGURE.Derivation.Equivalent

variable {T : Theory.{u}} {Γ Δ : List T.signature.SortType}
  {p q r z : Formula T.signature Γ}

/-- Pair two proof trees to obtain mutual derivability. -/
theorem of_derivations (forward : Derivation T p q) (backward : Derivation T q p) :
    Equivalent T p q :=
  ⟨⟨forward⟩, ⟨backward⟩⟩

/-- Mutual derivability is stable under renaming its variables. -/
theorem rename (h : Equivalent T p q) (ρ : Renaming Γ Δ) :
    Equivalent T (p.rename ρ) (q.rename ρ) := by
  obtain ⟨pq⟩ := h.forward
  obtain ⟨qp⟩ := h.backward
  exact of_derivations (.rename ρ pq) (.rename ρ qp)

/-- Conjunction preserves mutual derivability of both conjuncts. -/
theorem conj (hp : Equivalent T p q) (hr : Equivalent T r z) :
    Equivalent T (p.conj r) (q.conj z) := by
  obtain ⟨pq⟩ := hp.forward
  obtain ⟨qp⟩ := hp.backward
  obtain ⟨rz⟩ := hr.forward
  obtain ⟨zr⟩ := hr.backward
  exact of_derivations (andMono pq rz) (andMono qp zr)

/-- Disjunction preserves mutual derivability of both alternatives. -/
theorem disj (hp : Equivalent T p q) (hr : Equivalent T r z) :
    Equivalent T (p.disj r) (q.disj z) := by
  obtain ⟨pq⟩ := hp.forward
  obtain ⟨qp⟩ := hp.backward
  obtain ⟨rz⟩ := hr.forward
  obtain ⟨zr⟩ := hr.backward
  exact of_derivations (orMono pq rz) (orMono qp zr)

/-- Existential quantification preserves mutual derivability of the bodies. -/
theorem ex {s : T.signature.SortType} {p q : Formula T.signature (s :: Γ)} (h : Equivalent T p q) :
    Equivalent T p.ex q.ex := by
  obtain ⟨pq⟩ := h.forward
  obtain ⟨qp⟩ := h.backward
  exact of_derivations pq.existsMono qp.existsMono

/-- Binding a finite witness block preserves mutual derivability of the bodies. -/
theorem existsMany {Λ : List T.signature.SortType} {p q : Formula T.signature (Λ ++ Γ)}
    (h : Equivalent T p q) : Equivalent T (Formula.existsMany Λ p) (Formula.existsMany Λ q) := by
  obtain ⟨pq⟩ := h.forward
  obtain ⟨qp⟩ := h.backward
  exact of_derivations pq.existsManyMono qp.existsManyMono

/-- Finite conjunction compares its components at every typed position. -/
theorem conjoin {Λ : List T.signature.SortType} {p q : ∀ {s}, Var Λ s → Formula T.signature Γ}
    (h : ∀ {s} (i : Var Λ s), Equivalent T (p i) (q i)) :
    Equivalent T (Formula.conjoin Λ p) (Formula.conjoin Λ q) := by
  induction Λ with
  | nil => exact .refl _
  | cons s Λ ih => exact (h Var.here).conj (ih fun i => h (.there i))

end SHIGURE.Derivation.Equivalent

namespace SHIGURE.Translation

variable {S T : Theory.{u}} {f : S.signature.SortType → T.signature.SortType}

/-- Appendix A.3: identity translation preserves formulas up to mutual derivability. -/
theorem identityFormula_equivalent {Γ : List T.signature.SortType} (p : Formula T.signature Γ) :
    Derivation.Equivalent T ((identity T.signature).formula p) (p.rename (fun i => i.mapSorts id)) :=
  .of_derivations (identityFormula T p).1 (identityFormula T p).2

/-- Equivalent translations give mutual derivations for every original atom. -/
theorem Equivalent.atomic {l r : Translation S.signature T.signature f} (same : Equivalent l r)
    {Γ : List S.signature.SortType} (a : Atomic S.signature Γ) :
    Derivation.Equivalent T (l.atomic a) (r.atomic a) := by
  cases a with
  | eq x y => exact .refl _
  | rel rel args => exact (same.relation rel).rename (args.mapSorts f)
  | domain op args => exact (same.partialDomain op).rename (args.mapSorts f)
  | graph op args out => exact (same.operation_graph op).rename (Renaming.cons (out.mapSorts f) (args.mapSorts f))

/-- Appendix A.3: equivalent translations of primitives give equivalent translations of formulas. -/
theorem Equivalent.formula {l r : Translation S.signature T.signature f} (same : Equivalent l r)
    {Γ : List S.signature.SortType} (p : Formula S.signature Γ) :
    Derivation.Equivalent T (l.formula p) (r.formula p) := by
  induction p with
  | atom a => exact same.atomic a
  | truth => exact .refl _
  | falsehood => exact .refl _
  | conj _ _ left right => exact left.conj right
  | disj _ _ left right => exact left.disj right
  | ex _ body => exact body.ex

end SHIGURE.Translation

namespace SHIGURE.Translation

variable {S T : Theory.{u}} {f : S.signature.SortType → T.signature.SortType}

/-- Appendix A.3: translating a term's instantiated graph agrees with the translated term's graph. -/
theorem graphAt_equivalent (tr : Translation S.signature T.signature f)
    {Γ : List S.signature.SortType} {s : S.signature.SortType} (t : Term S.signature Γ s) :
    ∀ {E : List S.signature.SortType} (ambient : Renaming Γ E) (out : Var E s),
      Derivation.Equivalent T ((tr.term t).graphAt (ambient.mapSorts f) (out.mapSorts f))
        (tr.formula (t.graphAt ambient out)) := by
  induction t with
  | var i =>
    intro E ambient out
    simp only [term_var, Term.graphAt_var, formula_atom, atomic_eq, Renaming.mapSorts_apply]
    exact .refl _
  | @app Γ op args ih =>
    intro E ambient out
    let Λ := op.arity.inputs
    let images : ∀ {s}, Var (Λ.map f) s → Term T.signature (Γ.map f) s :=
      Var.reindex f (fun i => tr.term (args i))
    have strict := Derivation.strictGraph_equivalent (T := T) (tr.operation op) images
      (ambient.mapSorts f) (out.mapSorts f)
    rw [term_app]
    refine strict.trans ?_
    simp only [Term.graphAt_app, formula_existsMany, formula_conj, Formula.rename_conj]
    apply Derivation.Equivalent.existsMany
    apply Derivation.Equivalent.conj
    · rw [formula_conjoin, Formula.rename_conjoin]
      apply Derivation.Equivalent.conjoin
      refine @Var.forall_mapSorts _ _ Λ f (fun {_} i =>
        Derivation.Equivalent T
          ((images i).graphAt (Renaming.comp (Var.shift (Λ.map f)) (ambient.mapSorts f)) (i.inLeft (E.map f)))
          ((Var.reindex f (C := fun _ => Formula T.signature ((Λ ++ E).map f))
            (fun j => tr.formula ((args j).graphAt (Renaming.comp (Var.shift Λ) ambient) (j.inLeft E))) i).rename
              (Renaming.mapAppend f Λ))) ?_
      intro s i
      simp only [images, Var.reindex_mapSorts]
      have same := ih i (Renaming.comp (Var.shift Λ) ambient) (i.inLeft E)
      simpa only [Term.graphAt_rename, Renaming.mapAppend_comp_mapSorts_shift, Renaming.mapAppend_inLeft] using
        (same.rename (Renaming.mapAppend f Λ))
    · simp only [formula_atom, atomic_graphAt, Term.graphAt_rename, Renaming.mapAppend_comp_mapSorts_inLeft,
        Renaming.mapAppend_shift]
      exact .refl _
  | @letBind Γ b s init body hi hb =>
    intro E ambient out
    have shifted :
        @Renaming.mapSorts S.signature.SortType T.signature.SortType Γ (b :: E) f
          (fun i => Var.there (ambient i)) =
          (fun {_} i => Var.there (t := f b) ((ambient.mapSorts f) i)) := by
      apply Renaming.ext_mapSorts f
      intro t i
      simp only [Renaming.mapSorts_apply]
      rfl
    simp only [term_letBind, Term.graphAt_letBind, formula_ex, formula_conj]
    apply Derivation.Equivalent.ex
    apply Derivation.Equivalent.conj
    · simpa only [shifted, Var.mapSorts_here] using hi (fun i => .there (ambient i)) .here
    · simpa only [Renaming.mapSorts_lift, Var.mapSorts_there] using hb (Renaming.lift ambient) (.there out)

/-- Appendix A.3: the canonical value graph commutes with translation up to mutual derivability. -/
theorem graph_equivalent (tr : Translation S.signature T.signature f)
    {Γ : List S.signature.SortType} {s : S.signature.SortType} (t : Term S.signature Γ s) :
    Derivation.Equivalent T (tr.term t).graph (tr.formula t.graph) := by
  simpa only [Term.graph_eq_graphAt, Renaming.mapSorts_there, Var.mapSorts_here] using
    (tr.graphAt_equivalent t (fun i => .there i) .here)

/-- Appendix A.3: definedness commutes with translation up to mutual derivability. -/
theorem defined_equivalent (tr : Translation S.signature T.signature f)
    {Γ : List S.signature.SortType} {s : S.signature.SortType} (t : Term S.signature Γ s) :
    Derivation.Equivalent T (tr.term t).defined (tr.formula t.defined) :=
  (tr.graph_equivalent t).ex

/-- Equivalent replacements give equivalent value graphs for every translated term. -/
theorem Equivalent.graph {l r : Translation S.signature T.signature f} (same : Equivalent l r)
    {Γ : List S.signature.SortType} {s : S.signature.SortType} (t : Term S.signature Γ s) :
    Derivation.Equivalent T (l.term t).graph (r.term t).graph :=
  (l.graph_equivalent t).trans ((same.formula t.graph).trans (r.graph_equivalent t).symm)

end SHIGURE.Translation

namespace SHIGURE.Interpretation

variable {S T : Theory.{u}}

/-- Equivalent interpretations translate any formula to mutually derivable formulas. -/
theorem Equivalent.formula {l r : Interpretation S T} (same : l.Equivalent r)
    {Γ : List S.signature.SortType} (p : Formula S.signature Γ) :
    Derivation.Equivalent T
      ((l.translation.formula p).castContext (congrArg (List.map · Γ) same.onSort_eq))
      (r.translation.formula p) := by
  have sorts := same.onSort_eq
  have replaced := same.translation_equivalent
  cases l
  cases r
  cases sorts
  exact replaced.formula p

/-- Equivalent interpretations translate a term to mutually derivable value graphs. -/
theorem Equivalent.graph {l r : Interpretation S T} (same : l.Equivalent r)
    {Γ : List S.signature.SortType} {s : S.signature.SortType} (t : Term S.signature Γ s) :
    Derivation.Equivalent T
      ((l.translation.term t).graph.castContext (congrArg (List.map · (s :: Γ)) same.onSort_eq))
      (r.translation.term t).graph := by
  have sorts := same.onSort_eq
  have replaced := same.translation_equivalent
  cases l
  cases r
  cases sorts
  exact replaced.graph t

end SHIGURE.Interpretation
