import Formal.SHIGURE.Part1.GraphDerivations
import Formal.SHIGURE.Part1.IdentityInterpretation

/-! # Translating positive derivations

Proposition A.2. Translation preserves the binding of typed variables,
transports the structural axioms of the source signature, and sends any
source proof tree to a proof tree over the target theory.

## Implementation notes

The result is a target proof tree. Translating a semantic consequence alone
would require a completeness theorem to recover that tree.
-/

universe u

namespace SHIGURE.Renaming

variable {S T : Type u} {Γ Δ E : List S} (f : S → T)

/-- A renaming on the translated context is determined by the original positions. -/
theorem ext_mapSorts {D : List T} {ρ σ : Renaming (Γ.map f) D}
    (h : ∀ {s} (i : Var Γ s), ρ (i.mapSorts f) = σ (i.mapSorts f)) : @ρ = @σ := by
  induction Γ with
  | nil =>
    funext _ i
    exact nomatch i
  | cons s Γ ih =>
    let r : Renaming (Γ.map f) D := fun i => ρ (.there i)
    let q : Renaming (Γ.map f) D := fun i => σ (.there i)
    have tail : @r = @q := ih (fun i => h (.there i))
    funext _ i
    cases i with
    | here => exact h Var.here
    | there i => exact congrArg (fun (a : Renaming (Γ.map f) D) => a i) tail

/-- Translation of a composite renaming composes the translated renamings. -/
theorem mapSorts_comp (σ : Renaming Δ E) (ρ : Renaming Γ Δ) :
    @mapSorts S T Γ E f (comp σ ρ) =
      @comp T (Γ.map f) (Δ.map f) (E.map f) (mapSorts f σ) (mapSorts f ρ) := by
  apply ext_mapSorts f
  intro s i
  simp only [mapSorts_apply, comp_apply]

/-- Translation of a lifted renaming keeps the fresh head and translates the tail. -/
theorem mapSorts_lift {s : S} (ρ : Renaming Γ Δ) :
    @mapSorts S T (s :: Γ) (s :: Δ) f (lift ρ) =
      @lift T (Γ.map f) (Δ.map f) (f s) (mapSorts f ρ) := by
  apply ext_mapSorts f
  intro t i
  cases i with
  | here => rw [mapSorts_apply]; rfl
  | there i =>
    change _ = Var.there (t := f s) (mapSorts f ρ (i.mapSorts f))
    rw [mapSorts_apply, mapSorts_apply]; rfl

/-- Translating a substitution for the head position substitutes its translated variable. -/
theorem mapSorts_openHead {s : S} (x : Var Γ s) :
    @mapSorts S T (s :: Γ) Γ f (openHead x) =
      @openHead T (Γ.map f) (f s) (x.mapSorts f) := by
  apply ext_mapSorts f
  intro t i
  rw [mapSorts_apply]
  cases i <;> rfl

end SHIGURE.Renaming

namespace SHIGURE.Renaming

variable {S T : Type u} {Γ Δ E : List S}

/-- Retyping preserves the chosen head position and tail renaming. -/
theorem mapSorts_cons (f : S → T) {s : S} (head : Var Δ s) (tail : Renaming Γ Δ) :
    @mapSorts S T (s :: Γ) Δ f (cons head tail) =
      @cons T (Γ.map f) (Δ.map f) (f s) (head.mapSorts f) (mapSorts f tail) := by
  apply ext_mapSorts f
  intro t i
  cases i with
  | here => rw [mapSorts_apply]; rfl
  | there i =>
    change _ = mapSorts f tail (i.mapSorts f)
    rw [mapSorts_apply, mapSorts_apply]; rfl

end SHIGURE.Renaming

namespace SHIGURE.Translation

variable {S T : Signature.{u}} {f : S.SortType → T.SortType}

/-- Translate an atom before or after renaming its free variables. -/
theorem atomic_rename (tr : Translation S T f) {Γ Δ : List S.SortType}
    (a : Atomic S Γ) (ρ : Renaming Γ Δ) :
    tr.atomic (a.rename ρ) = (tr.atomic a).rename (Renaming.mapSorts f ρ) := by
  cases a with
  | eq x y =>
    simp only [Atomic.rename_eq, atomic_eq, Formula.rename_atom, Renaming.mapSorts_apply]
  | rel r inputs =>
    change (tr.relation r).rename (Renaming.mapSorts f (Renaming.comp ρ inputs)) =
      ((tr.relation r).rename (Renaming.mapSorts f inputs)).rename (Renaming.mapSorts f ρ)
    rw [Formula.rename_comp, Renaming.mapSorts_comp]
  | domain p inputs =>
    change (tr.partialDomain p).rename (Renaming.mapSorts f (Renaming.comp ρ inputs)) =
      ((tr.partialDomain p).rename (Renaming.mapSorts f inputs)).rename (Renaming.mapSorts f ρ)
    rw [Formula.rename_comp, Renaming.mapSorts_comp]
  | graph op inputs y =>
    change (tr.operation op).graph.rename
        (Renaming.cons ((ρ y).mapSorts f) (Renaming.mapSorts f (Renaming.comp ρ inputs))) =
      ((tr.operation op).graph.rename
        (Renaming.cons (y.mapSorts f) (Renaming.mapSorts f inputs))).rename (Renaming.mapSorts f ρ)
    rw [Formula.rename_comp, Renaming.comp_cons, Renaming.mapSorts_comp, Renaming.mapSorts_apply]

/-- Translating a formula commutes with free-variable renaming. -/
theorem formula_rename (tr : Translation S T f) {Γ Δ : List S.SortType}
    (p : Formula S Γ) (ρ : Renaming Γ Δ) :
    tr.formula (p.rename ρ) = (tr.formula p).rename (Renaming.mapSorts f ρ) := by
  induction p generalizing Δ with
  | atom a => exact tr.atomic_rename a ρ
  | truth => rfl
  | falsehood => rfl
  | conj p q hp hq =>
    simp only [Formula.rename_conj, formula_conj, hp ρ, hq ρ]
  | disj p q hp hq =>
    simp only [Formula.rename_disj, formula_disj, hp ρ, hq ρ]
  | ex p ih =>
    simp only [Formula.rename_ex, formula_ex, ih, Renaming.mapSorts_lift]

end SHIGURE.Translation


namespace SHIGURE.Renaming

variable {S T : Type u} {Γ : List S}

/-- Retyping a weakening inserts the variable of the corresponding target sort. -/
theorem mapSorts_there (f : S → T) (s : S) :
    @mapSorts S T Γ (s :: Γ) f (fun i => Var.there i) =
      (fun {_} i => Var.there (t := f s) i) := by
  apply ext_mapSorts f
  intro t i
  rw [mapSorts_apply]
  rfl

/-- The identity renaming also acts as identity on the retyped context. -/
theorem mapSorts_id (f : S → T) :
    @mapSorts S T Γ Γ f (fun i => i) = (fun {_} i => i) := by
  apply ext_mapSorts f
  intro s i
  exact mapSorts_apply f (fun j => j) i

end SHIGURE.Renaming

namespace SHIGURE.Translation

variable {S T : Signature.{u}} {f : S.SortType → T.SortType}

/-- A translated primitive graph is the value graph of its replacement at the actual variables. -/
theorem atomic_graphAt (tr : Translation S T f) {Γ : List S.SortType}
    (op : Operation S) (inputs : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    tr.atomic (.graph op inputs y) =
      (tr.operation op).graphAt (inputs.mapSorts f) (y.mapSorts f) := by
  rw [atomic_graph, Term.graphAt_eq_rename_graph]

/-- A translated output-existence formula asks for the definedness of the replacement term. -/
theorem formula_hasOutput (tr : Translation S T f) (op : Operation S) :
    tr.formula (GraphAxiom.hasOutput op) = (tr.operation op).defined := by
  rw [GraphAxiom.hasOutput_eq_ex_graph, formula_ex, formula_atom, atomic_graphAt, Renaming.mapSorts_there,
    Var.mapSorts_here, Term.defined_eq_ex_graph, Term.graph_eq_graphAt]

end SHIGURE.Translation

namespace SHIGURE.Interpretation

variable {S T : Theory.{u}}

/-- Proposition A.2, second step: the replacement data derive each translated structural axiom. -/
noncomputable def translateGraphAxiom (u : Interpretation S T) (ax : GraphAxiom S.signature) :
    Derivation T (u.translation.formula ax.toLaw.input) (u.translation.formula ax.toLaw.conclusion) := by
  cases ax with
  | functional op =>
    simp only [GraphAxiom.toLaw_functional, Translation.formula_conj, Translation.formula_atom, Translation.atomic_graphAt]
    exact Derivation.termGraphFunctional _ _ _ _
  | totality f =>
    simpa only [GraphAxiom.toLaw_totality, Translation.formula_truth, Translation.formula_hasOutput] using u.total f
  | quantityTotality q =>
    simpa only [GraphAxiom.toLaw_quantityTotality, Translation.formula_truth, Translation.formula_hasOutput] using u.quantity q
  | graphImpliesDomain p =>
    simp only [GraphAxiom.toLaw_graphImpliesDomain, Translation.formula_atom, Translation.atomic_graphAt,
      Translation.atomic_domain, Renaming.mapSorts_there]
    exact .cut (Derivation.graphAtDefined _ _ .here) (.rename (fun i => .there i) (u.definedPartial p))
  | domainImpliesGraph p =>
    simpa only [GraphAxiom.toLaw_domainImpliesGraph, Translation.formula_atom, Translation.atomic_domain,
      Renaming.mapSorts_id, Formula.rename_id, Translation.formula_hasOutput] using u.partialDefined p

/-- Proposition A.2: an interpretation sends every source derivation to a target derivation. -/
noncomputable def translateDerivation (u : Interpretation S T) {Γ : List S.signature.SortType}
    {p q : Formula S.signature Γ} (d : Derivation S p q) :
    Derivation T (u.translation.formula p) (u.translation.formula q) := by
  induction d with
  | refl p => exact .refl _
  | cut _ _ left right => exact .cut left right
  | required name => exact u.preserves name
  | graph ax => exact u.translateGraphAxiom ax
  | rename ρ _ proof =>
    rw [u.translation.formula_rename, u.translation.formula_rename]
    exact .rename (ρ.mapSorts u.onSort) proof
  | truth p => exact .truth _
  | falsehood p => exact .falsehood _
  | andLeft p q => exact .andLeft _ _
  | andRight p q => exact .andRight _ _
  | andIntro _ _ left right => exact .andIntro left right
  | orLeft p q => exact .orLeft _ _
  | orRight p q => exact .orRight _ _
  | orElim _ _ left right => exact .orElim left right
  | existsIntro body x =>
    simpa only [Translation.formula_rename, Renaming.mapSorts_openHead, Translation.formula_ex] using
      (Derivation.existsIntro (T := T) (u.translation.formula body) (x.mapSorts u.onSort))
  | existsElim _ proof =>
    apply Derivation.existsElim
    simpa only [Translation.formula_conj, Translation.formula_rename, Renaming.mapSorts_there] using proof
  | eqRefl x => exact .eqRefl (x.mapSorts u.onSort)
  | eqSubst p x y =>
    simp only [Translation.formula_conj, Translation.formula_rename, Renaming.mapSorts_openHead]
    exact .eqSubst (u.translation.formula p) (x.mapSorts u.onSort) (y.mapSorts u.onSort)

end SHIGURE.Interpretation

namespace SHIGURE.Var

variable {S T : Type u} {Γ : List S}

/-- Every position in a retyped context comes from its corresponding original position. -/
theorem forall_mapSorts (f : S → T) {P : ∀ {s}, Var (Γ.map f) s → Prop}
    (h : ∀ {s} (i : Var Γ s), P (i.mapSorts f)) : ∀ {t} (i : Var (Γ.map f) t), P i := by
  induction Γ with
  | nil => intro t i; exact nomatch i
  | cons s Γ ih =>
    intro t i
    cases i with
    | here => exact h .here
    | there i => exact ih (P := fun j => P (.there j)) (fun j => h (.there j)) i

end SHIGURE.Var

namespace SHIGURE.Renaming

variable {S T : Type u} {Γ Δ : List S}

/-- Split the retyped concatenation into the two retyped context blocks. -/
def mapAppend (f : S → T) : (Λ : List S) → Renaming ((Λ ++ Γ).map f) (Λ.map f ++ Γ.map f)
  | [] => fun i => i
  | _ :: Λ => lift (mapAppend f Λ)

/-- Splitting off an empty block changes no variable positions. -/
theorem mapAppend_nil (f : S → T) : @mapAppend S T Γ f [] = (fun {_} i => i) := rfl

/-- Splitting a nonempty block preserves its head and splits the tail. -/
theorem mapAppend_cons (f : S → T) (s : S) (Λ : List S) :
    @mapAppend S T Γ f (s :: Λ) =
      @lift T ((Λ ++ Γ).map f) (Λ.map f ++ Γ.map f) (f s) (mapAppend f Λ) := rfl

/-- Retyping and splitting a concatenation leaves a leading position at its original index. -/
@[simp] theorem mapAppend_inLeft (f : S → T) {Λ : List S} {s : S} (i : Var Λ s) :
    mapAppend f Λ ((i.inLeft Γ).mapSorts f) = (i.mapSorts f).inLeft (Γ.map f) := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg Var.there ih

/-- Retyping and splitting a concatenation shifts each ambient position past the leading block. -/
@[simp] theorem mapAppend_shift (f : S → T) (Λ : List S) {s : S} (i : Var Γ s) :
    mapAppend f Λ ((i.shift Λ).mapSorts f) = (i.mapSorts f).shift (Λ.map f) := by
  induction Λ with
  | nil => rfl
  | cons t Λ ih => exact congrArg Var.there ih

/-- A retyped ambient map into a concatenation uses the same trailing positions. -/
theorem mapAppend_comp_mapSorts_shift (f : S → T) (Λ : List S) (ρ : Renaming Γ Δ) :
    @comp T (Γ.map f) ((Λ ++ Δ).map f) (Λ.map f ++ Δ.map f)
      (mapAppend f Λ) (mapSorts f (comp (Var.shift Λ) ρ)) =
      @comp T (Γ.map f) (Δ.map f) (Λ.map f ++ Δ.map f) (Var.shift (Λ.map f)) (mapSorts f ρ) := by
  apply ext_mapSorts f
  intro s i
  simp only [comp_apply, mapSorts_apply, mapAppend_shift]

/-- The retyped map into the leading block stays in the leading block after splitting. -/
theorem mapAppend_comp_mapSorts_inLeft (f : S → T) (Λ : List S) :
    @comp T (Λ.map f) ((Λ ++ Γ).map f) (Λ.map f ++ Γ.map f)
      (mapAppend f Λ) (mapSorts f (Var.inLeft Γ)) = (fun {_} i => i.inLeft (Γ.map f)) := by
  apply ext_mapSorts f
  intro s i
  simp only [comp_apply, mapSorts_apply, mapAppend_inLeft]

end SHIGURE.Renaming

namespace SHIGURE.Translation

variable {S T : Signature.{u}} {f : S.SortType → T.SortType}

/-- A translated finite conjunction uses the same positions after sort reindexing. -/
theorem formula_conjoin (tr : Translation S T f) {Γ : List S.SortType} (Λ : List S.SortType)
    (p : ∀ {s}, Var Λ s → Formula S Γ) :
    tr.formula (Formula.conjoin Λ p) =
      Formula.conjoin (Λ.map f) (Var.reindex f (C := fun _ => Formula T (Γ.map f)) (fun i => tr.formula (p i))) := by
  induction Λ with
  | nil => simp only [Formula.conjoin_nil, formula_truth, List.map_nil]
  | cons s Λ ih =>
    simp only [Formula.conjoin_cons, formula_conj, List.map_cons, Var.reindex_here, Var.reindex_there, ih]

/-- Translating a block of existentials only retypes the witness and ambient positions. -/
theorem formula_existsMany (tr : Translation S T f) {Γ : List S.SortType} (Λ : List S.SortType)
    (p : Formula S (Λ ++ Γ)) :
    tr.formula (Formula.existsMany Λ p) =
      Formula.existsMany (Λ.map f) ((tr.formula p).rename (Renaming.mapAppend f Λ)) := by
  induction Λ with
  | nil => simp only [Formula.existsMany_nil, List.map_nil, Renaming.mapAppend_nil, Formula.rename_id]
  | cons s Λ ih =>
    simp only [Formula.existsMany_cons, ih, formula_ex, Formula.rename_ex, List.map_cons, Renaming.mapAppend_cons]

end SHIGURE.Translation
