import Formal.SHIGURE.Part1.DerivationLemmas

/-! # Syntactic derivations for value graphs

Appendix A.3 starts by proving functionality for the graph of every term.
The proof opens both witness blocks, identifies their arguments with
recursively derived equalities, and then uses the structural graph
axiom. The strict binding case identifies the two bound values before
applying functionality to the two bodies.

## Implementation notes

The derivation under two witness blocks keeps the original context as a common
tail. The ambient renaming also works for empty sort carriers because the
proof eliminates bound variables only after obtaining their witnesses.
-/

universe u

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ : List T.signature.SortType}

/-- Eliminate a block of witnesses while retaining a separate antecedent. -/
def existsManyElimWith : {Λ : List T.signature.SortType} →
    {c q : Formula T.signature Γ} → {body : Formula T.signature (Λ ++ Γ)} →
    Derivation T ((c.rename (Var.shift Λ)).conj body) (q.rename (Var.shift Λ)) →
    Derivation T (c.conj (Formula.existsMany Λ body)) q
  | [], _, _, _, d => by
    simpa only [Var.shift_nil, Formula.rename_id, Formula.existsMany_nil] using d
  | s :: Λ, c, q, body, d => by
    rw [Formula.existsMany_cons]
    apply existsManyElimWith (Λ := Λ) (body := body.ex)
    apply Derivation.existsElim
    rw [Formula.rename_comp, Formula.rename_comp]
    change Derivation T
      ((c.rename (fun i => Renaming.comp (fun j => Var.there (t := s) j) (Var.shift Λ) i)).conj body)
      (q.rename (fun i => Renaming.comp (fun j => Var.there (t := s) j) (Var.shift Λ) i))
    rw [← Renaming.shift_cons_comp]
    exact d

end SHIGURE.Derivation

namespace SHIGURE.Renaming

variable {S : Type u} {Γ Δ : List S}

/-- Lift a free-variable map past a block of bound variables. -/
def liftMany (ρ : Renaming Γ Δ) : (Λ : List S) → Renaming (Λ ++ Γ) (Λ ++ Δ)
  | [], _, i => ρ i
  | _ :: Λ, _, i => lift (liftMany ρ Λ) i

/-- Lifting past the empty block preserves the original renaming. -/
theorem liftMany_nil (ρ : Renaming Γ Δ) :
    @liftMany S Γ Δ ρ [] = (fun {t : S} (i : Var Γ t) => ρ i) :=
  rfl

/-- Lifting past a nonempty block keeps the head and lifts past the remaining positions. -/
theorem liftMany_cons (ρ : Renaming Γ Δ) (s : S) (Λ : List S) :
    @liftMany S Γ Δ ρ (s :: Λ) = @lift S (Λ ++ Γ) (Λ ++ Δ) s (liftMany ρ Λ) := rfl

/-- A lifted map retains the positions of the bound block. -/
@[simp] theorem liftMany_inLeft (ρ : Renaming Γ Δ) {Λ : List S} {s : S}
    (i : Var Λ s) : liftMany ρ Λ (i.inLeft Γ) = i.inLeft Δ := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg Var.there ih

/-- A lifted map acts on a free position under the bound block. -/
@[simp] theorem liftMany_shift (ρ : Renaming Γ Δ) (Λ : List S) {s : S}
    (i : Var Γ s) : liftMany ρ Λ (i.shift Λ) = (ρ i).shift Λ := by
  induction Λ with
  | nil =>
    have source : i.shift [] = i := congrArg (fun f : Renaming Γ Γ => f i) Var.shift_nil
    have target : (ρ i).shift [] = ρ i := congrArg (fun f : Renaming Δ Δ => f (ρ i)) Var.shift_nil
    rw [source, target]
    rfl
  | cons t Λ ih =>
    rw [Var.shift_cons, Var.shift_cons]
    exact congrArg Var.there ih

end SHIGURE.Renaming

namespace SHIGURE.Formula

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType}

/-- Renaming under a finite block of existential witnesses lifts the free variables. -/
theorem rename_existsMany (ρ : Renaming Γ Δ) : (Λ : List sig.SortType) →
    (p : Formula sig (Λ ++ Γ)) →
    (existsMany Λ p).rename ρ = existsMany Λ (p.rename (Renaming.liftMany ρ Λ))
  | [], p => rfl
  | _ :: Λ, p => by
    rw [existsMany_cons, rename_existsMany ρ Λ p.ex]
    rfl

end SHIGURE.Formula

namespace SHIGURE.Term

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}

/-- Renaming a graph formula composes its input map and reindexes its output. -/
theorem graphAt_rename (t : Term sig Γ s) :
    ∀ {Δ E : List sig.SortType} (ρ : Renaming Γ Δ) (y : Var Δ s) (σ : Renaming Δ E),
      (t.graphAt ρ y).rename σ = t.graphAt (Renaming.comp σ ρ) (σ y) := by
  induction t with
  | var i => intros; rfl
  | @app Γ op terms ih =>
    intro Δ E ρ y σ
    have shiftComp :
        @Renaming.comp sig.SortType Γ (op.arity.inputs ++ Δ) (op.arity.inputs ++ E)
          (Renaming.liftMany σ op.arity.inputs) (fun i => (ρ i).shift op.arity.inputs) =
        (fun {_} i => (σ (ρ i)).shift op.arity.inputs) := by
      funext t i
      exact Renaming.liftMany_shift σ op.arity.inputs (ρ i)
    simp only [graphAt_app, Formula.rename_existsMany, Formula.rename_conj, Formula.rename_conjoin,
      ih, Formula.rename_atom, Atomic.rename_graph, Renaming.liftMany_inLeft,
      Renaming.liftMany_shift, shiftComp, Renaming.comp_apply]
  | letBind init body hi hb =>
    intro Δ E ρ y σ
    simp only [graphAt_letBind, Formula.rename_ex, Formula.rename_conj, hi, hb, ← Renaming.lift_comp]
    rfl

/-- The canonical value graph can be instantiated with any variables of the required types. -/
theorem graphAt_eq_rename_graph (t : Term sig Γ s) {Δ : List sig.SortType}
    (ρ : Renaming Γ Δ) (y : Var Δ s) : t.graphAt ρ y = t.graph.rename (Renaming.cons y ρ) := by
  rw [graph_eq_graphAt, graphAt_rename]
  rfl

end SHIGURE.Term

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ Λ Θ : List T.signature.SortType}

/-- Use both witness blocks while retaining the same ambient variables. -/
def existsManyBothElim
    {p : Formula T.signature (Λ ++ Γ)} {q : Formula T.signature (Θ ++ Γ)}
    {r : Formula T.signature Γ}
    (d : Derivation T
      ((p.rename (Var.shift Θ)).conj (q.rename (Renaming.liftMany (Var.shift Λ) Θ)))
      (r.rename (fun i => (i.shift Λ).shift Θ))) :
    Derivation T ((Formula.existsMany Λ p).conj (Formula.existsMany Θ q)) r := by
  have inside : Derivation T (p.conj ((Formula.existsMany Θ q).rename (Var.shift Λ)))
      (r.rename (Var.shift Λ)) := by
    rw [Formula.rename_existsMany]
    apply existsManyElimWith
    simpa only [Formula.rename_comp, Renaming.comp_apply] using d
  have reverseInside : Derivation T (((Formula.existsMany Θ q).rename (Var.shift Λ)).conj p)
      (r.rename (Var.shift Λ)) :=
    .cut (.andIntro (.andRight _ _) (.andLeft _ _)) inside
  exact .cut (.andIntro (.andRight _ _) (.andLeft _ _)) (existsManyElimWith reverseInside)

end SHIGURE.Derivation

namespace SHIGURE.Renaming

variable {S : Type u} {Γ Δ E : List S} {s : S}

/-- Composing after a cons renaming maps its head and tail separately. -/
theorem comp_cons (σ : Renaming Δ E) (head : Var Δ s) (tail : Renaming Γ Δ) :
    @comp S (s :: Γ) Δ E σ (cons head tail) = @cons S Γ E s (σ head) (comp σ tail) := by
  funext t i
  cases i <;> rfl

/-- Composing after a lifted renaming separately maps its bound and free positions. -/
theorem comp_lift (σ : Renaming (s :: Δ) E) (ρ : Renaming Γ Δ) :
    @comp S (s :: Γ) (s :: Δ) E σ (lift ρ) =
      @cons S Γ E s (σ .here) (comp (fun i => σ (.there i)) ρ) := by
  funext t i
  cases i <;> rfl

end SHIGURE.Renaming

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ : List T.signature.SortType}

/-- An instantiated value graph entails the corresponding definedness formula. -/
def graphAtDefined {Δ : List T.signature.SortType} {s : T.signature.SortType}
    (t : Term T.signature Γ s) (ρ : Renaming Γ Δ) (y : Var Δ s) :
    Derivation T (t.graphAt ρ y) (t.defined.rename ρ) := by
  rw [t.graphAt_eq_rename_graph, Term.defined_eq_ex_graph, Formula.rename_ex]
  simpa only [Formula.rename_comp, Renaming.openHead_comp_lift] using
    (Derivation.existsIntro (T := T) (t.graph.rename (Renaming.lift ρ)) y)

/-- The primitive graph axiom instantiated at the supplied input and output variables. -/
def primitiveFunctional (op : Operation T.signature) (inputs : Renaming op.arity.inputs Γ)
    (y z : Var Γ op.arity.output) :
    Derivation T
      ((Formula.atom (.graph op inputs y)).conj (Formula.atom (.graph op inputs z)))
      (.atom (.eq y z)) := by
  have rule := Derivation.graph (T := T) (.functional op)
  rw [GraphAxiom.toLaw_functional] at rule
  have instantiated := rule.rename (Renaming.cons y (Renaming.cons z inputs))
  simpa only [Formula.rename_conj, Formula.rename_atom, Atomic.rename_graph, Atomic.rename_eq,
    Renaming.cons_here, Renaming.cons_there] using instantiated

/-- Replace equal input witnesses in an instantiated primitive graph. -/
def primitiveGraphCongr (op : Operation T.signature) (left right : Renaming op.arity.inputs Γ)
    (y : Var Γ op.arity.output) :
    Derivation T ((Formula.equalArguments op.arity.inputs left right).conj (.atom (.graph op left y)))
      (.atom (.graph op right y)) := by
  let body : Formula T.signature (op.arity.inputs ++ Γ) :=
    .atom (.graph op (Var.inLeft Γ) (Var.shift op.arity.inputs y))
  simpa only [body, Formula.rename_atom, Atomic.rename_graph, Renaming.append_inLeft, Renaming.append_id_shift]
    using (renameAlongEqual (T := T) body left right (fun i => i))

/-- Proposition A.2, first step: value graphs of terms are syntactically functional. -/
noncomputable def termGraphFunctional {s : T.signature.SortType} (t : Term T.signature Γ s) :
    ∀ {Δ : List T.signature.SortType} (ρ : Renaming Γ Δ) (y z : Var Δ s),
      Derivation T ((t.graphAt ρ y).conj (t.graphAt ρ z)) (.atom (.eq y z)) := by
  induction t with
  | var x =>
    intro Δ ρ y z
    simp only [Term.graphAt_var]
    exact .eqSubst (.atom (.eq .here (.there z))) (ρ x) y
  | @app Γ op terms ih =>
    intro Δ ρ y z
    let Λ := op.arity.inputs
    let lift : Renaming Δ (Λ ++ Δ) := Var.shift Λ
    let old : Renaming Δ (Λ ++ (Λ ++ Δ)) := Renaming.comp (Var.shift Λ) lift
    let left : Renaming Λ (Λ ++ (Λ ++ Δ)) := fun i => (i.inLeft Δ).shift Λ
    let right : Renaming Λ (Λ ++ (Λ ++ Δ)) := Var.inLeft (Λ ++ Δ)
    let body (w : Var Δ op.arity.output) : Formula T.signature (Λ ++ Δ) :=
      (Formula.conjoin Λ fun i => (terms i).graphAt (Renaming.comp lift ρ) (i.inLeft Δ)).conj
        (.atom (.graph op (Var.inLeft Δ) (lift w)))
    let leftInputs := Formula.conjoin Λ fun i => (terms i).graphAt (Renaming.comp old ρ) (left i)
    let rightInputs := Formula.conjoin Λ fun i => (terms i).graphAt (Renaming.comp old ρ) (right i)
    let leftGraph : Formula T.signature (Λ ++ (Λ ++ Δ)) := .atom (.graph op left (old y))
    let rightGraph : Formula T.signature (Λ ++ (Λ ++ Δ)) := .atom (.graph op right (old z))
    have reduceLeft : (body y).rename (Var.shift Λ) = leftInputs.conj leftGraph := by
      simp only [body, leftInputs, leftGraph, Formula.rename_conj, Formula.rename_conjoin,
        Term.graphAt_rename, Formula.rename_atom, Atomic.rename_graph, old, left]
      rfl
    have renameInputs :
        @Renaming.comp T.signature.SortType Γ (Λ ++ Δ) (Λ ++ (Λ ++ Δ))
          (Renaming.liftMany lift Λ) (Renaming.comp lift ρ) =
        @Renaming.comp T.signature.SortType Γ Δ (Λ ++ (Λ ++ Δ)) old ρ := by
      funext s i
      exact Renaming.liftMany_shift lift Λ (ρ i)
    have reduceRight : (body z).rename (Renaming.liftMany lift Λ) = rightInputs.conj rightGraph := by
      simp only [body, rightInputs, rightGraph, Formula.rename_conj, Formula.rename_conjoin,
        Term.graphAt_rename, Formula.rename_atom, Atomic.rename_graph, renameInputs, right,
        Renaming.liftMany_inLeft]
      rw [show lift z = (z.shift Λ) from rfl, Renaming.liftMany_shift]
      rfl
    let premises := (leftInputs.conj leftGraph).conj (rightInputs.conj rightGraph)
    have equate : Derivation T premises (Formula.equalArguments Λ right left) :=
      conjoinIntro _ fun i =>
        .cut (.andIntro
          (.cut (.andRight _ _) (.cut (.andLeft _ _) (conjoinAt _ i)))
          (.cut (.andLeft _ _) (.cut (.andLeft _ _) (conjoinAt _ i))))
          (ih i (Renaming.comp old ρ) (right i) (left i))
    have onLeft : Derivation T premises (.atom (.graph op left (old z))) :=
      .cut (.andIntro equate (.cut (.andRight _ _) (.andRight _ _))) (primitiveGraphCongr op right left (old z))
    have conclude : Derivation T premises (.atom (.eq (old y) (old z))) :=
      .cut (.andIntro (.cut (.andLeft _ _) (.andRight _ _)) onLeft) (primitiveFunctional op left (old y) (old z))
    simp only [Term.graphAt_app]
    change Derivation T ((Formula.existsMany Λ (body y)).conj (Formula.existsMany Λ (body z))) _
    apply existsManyBothElim
    rw [reduceLeft, reduceRight]
    exact conclude
  | @letBind Γ b s init body ihInit ihBody =>
    intro Δ ρ y z
    let D := b :: b :: Δ
    let old : Renaming Δ D := fun v => .there (.there v)
    let args : Renaming Γ D := Renaming.comp old ρ
    let left : Var D b := .there .here
    let right : Var D b := .here
    let graph (w : Var Δ s) : Formula T.signature (b :: Δ) :=
      (init.graphAt (fun i => .there (ρ i)) .here).conj (body.graphAt (Renaming.lift ρ) (.there w))
    let leftInit := init.graphAt args left
    let rightInit := init.graphAt args right
    let leftBody := body.graphAt (Renaming.cons left args) (old y)
    let rightBody := body.graphAt (Renaming.cons right args) (old z)
    have singleton {Ω : List T.signature.SortType} :
        (fun {a} (v : Var Ω a) => Var.shift [b] v) =
          (fun {a} (v : Var Ω a) => Var.there (t := b) v) := by
      funext a v
      rw [Var.shift_cons]
      exact congrArg Var.there (congrArg (fun f : Renaming Ω Ω => f v) Var.shift_nil)
    have reduceLeft : (graph y).rename (Var.shift [b]) = leftInit.conj leftBody := by
      simp only [graph, Formula.rename_conj, Term.graphAt_rename, Renaming.comp_lift,
        leftInit, leftBody, args, left, singleton]
      rfl
    have reduceRight : (graph z).rename (Renaming.liftMany (Var.shift [b]) [b]) =
        rightInit.conj rightBody := by
      simp only [graph, Formula.rename_conj, Term.graphAt_rename, Renaming.comp_lift,
        rightInit, rightBody, args, right, singleton]
      rfl
    let premises := (leftInit.conj leftBody).conj (rightInit.conj rightBody)
    have equate : Derivation T premises (.atom (.eq right left)) :=
      .cut (.andIntro (.cut (.andRight _ _) (.andLeft _ _)) (.cut (.andLeft _ _) (.andLeft _ _)))
        (ihInit args right left)
    let changingWitness := body.graphAt (Renaming.cons .here (fun i => .there (args i))) (.there (old z))
    have rewritten : Derivation T ((Formula.atom (.eq right left)).conj rightBody)
        (body.graphAt (Renaming.cons left args) (old z)) := by
      simpa only [changingWitness, Term.graphAt_rename, Renaming.comp_cons,
        Renaming.openHead_here, Renaming.openHead_there, rightBody, Renaming.comp_apply] using
        (Derivation.eqSubst (T := T) changingWitness right left)
    have bodyOnLeft := Derivation.cut
      (Derivation.andIntro equate (Derivation.cut (.andRight _ _) (.andRight _ _))) rewritten
    have conclude : Derivation T premises (.atom (.eq (old y) (old z))) :=
      .cut (.andIntro (.cut (.andLeft _ _) (.andRight _ _)) bodyOnLeft)
        (ihBody (Renaming.cons left args) (old y) (old z))
    simp only [Term.graphAt_letBind]
    rw [← Formula.existsMany_singleton (graph y), ← Formula.existsMany_singleton (graph z)]
    apply existsManyBothElim
    rw [reduceLeft, reduceRight]
    have singletonAt {Ω : List T.signature.SortType} {a} (v : Var Ω a) :
        Var.shift [b] v = .there v :=
      congrArg (fun f : Renaming Ω (b :: Ω) => f v) singleton
    simpa only [Formula.rename_atom, Atomic.rename_eq, singletonAt, old] using conclude

end SHIGURE.Derivation
