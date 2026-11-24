import Formal.SHIGURE.Part1.BoundArguments
import Formal.SHIGURE.Part1.Interpretation

/-! # Witness order for strict arguments

A strict application binds its input values in argument order. Its
parallel graph formula uses one existential witness block. The two
orders use the same variables and support the same proof rules.

## Implementation notes

The nested order preserves the scope of strict evaluation. The parallel block
has the order used in the expansion of operation graphs. Both directions
reintroduce the same typed witnesses with explicit renamings.
-/

universe u

namespace SHIGURE.Renaming

variable {S : Type u} {Γ Δ : List S} {s : S}

/-- Moving a head keeps the tail witnesses as the leading block. -/
@[simp] theorem insertAfter_inLeft (Λ : List S) {t : S} (i : Var Λ t) :
    insertAfter (s := s) Λ (i.inLeft Γ) = i.inLeft (s :: Γ) := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg Var.there ih

/-- Moving a head places it between the witness block and every free variable. -/
@[simp] theorem insertAfter_shift (Λ : List S) {t : S} (i : Var Γ t) :
    insertAfter (s := s) Λ (i.shift Λ) = (Var.there (t := s) i).shift Λ := by
  induction Λ with
  | nil => rfl
  | cons t Λ ih => exact congrArg Var.there ih

/-- The moved head is the parameter that follows the remaining witnesses. -/
@[simp] theorem moveHead_here (Λ : List S) :
    moveHead (Γ := Γ) (s := s) Λ .here = (Var.here : Var (s :: Γ) s).shift Λ :=
  rfl

/-- A tail witness keeps its position after the head is moved. -/
@[simp] theorem moveHead_witness (Λ : List S) {t : S} (i : Var Λ t) :
    moveHead (s := s) Λ (.there (i.inLeft Γ)) = i.inLeft (s :: Γ) :=
  insertAfter_inLeft Λ i

/-- Moving the head sends an outer-context variable to the old parameter positions. -/
@[simp] theorem moveHead_outer (Λ : List S) {t : S} (i : Var Γ t) :
    moveHead Λ (i.shift (s :: Λ)) = (Var.there (t := s) i).shift Λ :=
  insertAfter_shift Λ i

/-- Filling the tail witnesses and the moved head fills the original block. -/
theorem fill_moveHead {Λ : List S} (witness : Renaming (s :: Λ) Δ) (ambient : Renaming Γ Δ) :
    @comp S ((s :: Λ) ++ Γ) (Λ ++ s :: Γ) Δ
      (append (fun i => witness (.there i)) (cons (witness .here) ambient)) (moveHead Λ) =
      @append S Γ Δ (s :: Λ) witness ambient := by
  rw [append_moveHead]
  funext t i
  cases i <;> rfl

/-- The moved head and all free variables together form the shifted ambient substitution. -/
theorem moveHead_comp_shift (Λ : List S) :
    @comp S Γ ((s :: Λ) ++ Γ) (Λ ++ s :: Γ) (moveHead Λ) (Var.shift (s :: Λ)) =
      @comp S Γ (s :: Γ) (Λ ++ s :: Γ) (Var.shift Λ) (fun i => Var.there i) := by
  funext t i
  exact moveHead_outer (s := s) Λ i

end SHIGURE.Renaming

namespace SHIGURE.Formula

variable {sig : Signature.{u}} {Γ : List sig.SortType}

/-- Choose the first witness, then choose the remaining witnesses in its extended context. -/
def sequentialWitnesses : {Γ : List sig.SortType} → (Λ : List sig.SortType) →
    (∀ {s}, Var Λ s → Formula sig (s :: Γ)) → Formula sig (Λ ++ Γ) → Formula sig Γ
  | _, [], _, body => body
  | _, _ :: Λ, condition, body =>
    ((condition .here).conj
      (sequentialWitnesses Λ
        (fun i => (condition (.there i)).rename (Renaming.lift (fun j => .there j)))
        (body.rename (Renaming.moveHead Λ)))).ex

/-- Moving the head separates its own condition from the conditions on the tail. -/
theorem witnessConjunction_moveHead {Λ : List sig.SortType} {s : sig.SortType}
    (condition : ∀ {t}, Var (s :: Λ) t → Formula sig (t :: Γ)) :
    (witnessConjunction (s :: Λ) condition).rename (Renaming.moveHead Λ) =
      ((condition .here).rename (Var.shift Λ)).conj
        (witnessConjunction Λ
          (fun i => (condition (.there i)).rename (Renaming.lift (fun j => .there j)))) := by
  have headMap :
      @Renaming.comp sig.SortType (s :: Γ) ((s :: Λ) ++ Γ) (Λ ++ s :: Γ) (Renaming.moveHead Λ)
        (Renaming.cons (Var.here.inLeft Γ) (Var.shift (s :: Λ))) = (fun {_} i => i.shift Λ) := by
    funext t i
    cases i with
    | here => rfl
    | there i => exact Renaming.moveHead_outer (s := s) Λ i
  have otherMap {t : sig.SortType} (i : Var Λ t) :
      @Renaming.comp sig.SortType (t :: Γ) ((s :: Λ) ++ Γ) (Λ ++ s :: Γ) (Renaming.moveHead Λ)
        (Renaming.cons ((Var.there (t := s) i).inLeft Γ) (Var.shift (s :: Λ))) =
      @Renaming.comp sig.SortType (t :: Γ) (t :: s :: Γ) (Λ ++ s :: Γ)
        (Renaming.cons (i.inLeft (s :: Γ)) (Var.shift Λ)) (Renaming.lift (fun i => .there i)) := by
    funext sort j
    cases j with
    | here => exact Renaming.moveHead_witness (s := s) (Γ := Γ) Λ i
    | there j => exact Renaming.moveHead_outer (s := s) Λ j
  simp only [witnessConjunction, conjoin, rename_conj, rename_conjoin, rename_comp, headMap, otherMap]

end SHIGURE.Formula

namespace SHIGURE.Derivation

variable {T : Theory.{u}}

/-- Introduce one witness while reindexing the remaining variables. -/
def existsIntroAlong {Γ Δ : List T.signature.SortType} {s : T.signature.SortType}
    (ambient : Renaming Γ Δ) (witness : Var Δ s) (body : Formula T.signature (s :: Γ)) :
    Derivation T (body.rename (Renaming.cons witness ambient)) (body.ex.rename ambient) := by
  rw [Formula.rename_ex]
  simpa only [Formula.rename_comp, Renaming.openHead_comp_lift] using
    (Derivation.existsIntro (T := T) (body.rename (Renaming.lift ambient)) witness)

/-- Introduce sequential witnesses from a tuple of already selected variables. -/
def sequentialIntro : ∀ {Γ Δ : List T.signature.SortType} (Λ : List T.signature.SortType)
    (condition : ∀ {s}, Var Λ s → Formula T.signature (s :: Γ))
    (body : Formula T.signature (Λ ++ Γ)) (witness : Renaming Λ Δ) (ambient : Renaming Γ Δ),
    Derivation T (((Formula.witnessConjunction Λ condition).conj body).rename (Renaming.append witness ambient))
      ((Formula.sequentialWitnesses Λ condition body).rename ambient) := by
  intro Γ Δ Λ
  induction Λ generalizing Γ with
  | nil => intros; exact .andRight _ _
  | cons s Λ ih =>
    intro condition body witness ambient
    let tail (t : T.signature.SortType) (i : Var Λ t) : Formula T.signature (t :: s :: Γ) :=
      (condition (.there i)).rename (Renaming.lift (fun j => .there j))
    let w : Renaming Λ Δ := fun i => witness (.there i)
    let chosen : Renaming (s :: Γ) Δ := Renaming.cons (witness .here) ambient
    let placed : Formula T.signature (Λ ++ s :: Γ) := body.rename (Renaming.moveHead Λ)
    let rest := Formula.sequentialWitnesses Λ (fun i => tail _ i) placed
    have headRead :
        @Renaming.comp T.signature.SortType (s :: Γ) (Λ ++ s :: Γ) Δ
          (Renaming.append w chosen) (Var.shift Λ) = @chosen := by
      funext t i
      exact Renaming.append_shift w chosen i
    have split : Derivation T
        (((Formula.witnessConjunction (s :: Λ) condition).conj body).rename (Renaming.append witness ambient))
        (((condition .here).rename chosen).conj
          (((Formula.witnessConjunction Λ (fun i => tail _ i)).conj placed).rename (Renaming.append w chosen))) := by
      rw [← Renaming.fill_moveHead witness ambient, ← Formula.rename_comp, Formula.rename_conj,
        Formula.witnessConjunction_moveHead, Formula.rename_conj]
      simp only [Formula.rename_conj, Formula.rename_comp, headRead, w, chosen, placed, tail]
      exact .andIntro (.cut (.andLeft _ _) (.andLeft _ _))
        (.andIntro (.cut (.andLeft _ _) (.andRight _ _)) (.andRight _ _))
    have next := andMono (.refl ((condition .here).rename chosen))
      (ih (fun i => tail _ i) placed w chosen)
    have pack := existsIntroAlong (T := T) ambient (witness .here) ((condition .here).conj rest)
    rw [Formula.rename_conj] at pack
    exact .cut split (.cut next pack)

/-- Use sequential witnesses with a separate assumption in the ambient context. -/
def sequentialElimWith : ∀ {Γ : List T.signature.SortType} (Λ : List T.signature.SortType)
    (condition : ∀ {s}, Var Λ s → Formula T.signature (s :: Γ))
    {body : Formula T.signature (Λ ++ Γ)} {guards goal : Formula T.signature Γ},
    Derivation T ((guards.rename (Var.shift Λ)).conj ((Formula.witnessConjunction Λ condition).conj body))
      (goal.rename (Var.shift Λ)) →
    Derivation T (guards.conj (Formula.sequentialWitnesses Λ condition body)) goal := by
  intro Γ Λ
  induction Λ generalizing Γ with
  | nil =>
    intro condition body guards goal d
    simp only [Var.shift, Formula.rename_id] at d
    exact .cut (.andIntro (.andLeft _ _) (.andIntro (.truth _) (.andRight _ _))) d
  | cons s Λ ih =>
    intro condition body guards goal d
    let weaken : Renaming Γ (s :: Γ) := fun i => .there i
    let tail (t : T.signature.SortType) (i : Var Λ t) : Formula T.signature (t :: s :: Γ) :=
      (condition (.there i)).rename (Renaming.lift weaken)
    let onHead := condition (Var.here : Var (s :: Λ) s)
    let kept := (guards.rename weaken).conj onHead
    let placed : Formula T.signature (Λ ++ s :: Γ) := body.rename (Renaming.moveHead Λ)
    let lift : Renaming (s :: Γ) (Λ ++ s :: Γ) := Var.shift Λ
    let witnesses := Formula.witnessConjunction Λ (fun i => tail _ i)
    have moved : Derivation T
        (((guards.rename weaken).rename lift).conj (((onHead.rename lift).conj witnesses).conj placed))
        ((goal.rename weaken).rename lift) := by
      simpa only [Formula.rename_conj, Formula.witnessConjunction_moveHead, Formula.rename_comp,
        Renaming.moveHead_comp_shift, weaken, lift, tail, placed, onHead, witnesses] using
        (Derivation.rename (Renaming.moveHead Λ) d)
    have regroup : Derivation T ((kept.rename lift).conj (witnesses.conj placed))
        (((guards.rename weaken).rename lift).conj (((onHead.rename lift).conj witnesses).conj placed)) := by
      simp only [kept, Formula.rename_conj]
      exact .andIntro (.cut (.andLeft _ _) (.andLeft _ _)) (.andIntro
        (.andIntro (.cut (.andLeft _ _) (.andRight _ _)) (.cut (.andRight _ _) (.andLeft _ _)))
        (.cut (.andRight _ _) (.andRight _ _)))
    have useTail := ih (fun i => tail _ i) (.cut regroup moved)
    apply Derivation.existsElim
    exact .cut (.andIntro
      (.andIntro (.andLeft _ _) (.cut (.andRight _ _) (.andLeft _ _)))
      (.cut (.andRight _ _) (.andRight _ _))) useTail

/-- Sequential and parallel existential witness blocks are mutually derivable. -/
theorem sequentialWitnesses_equivalent {Γ : List T.signature.SortType} (Λ : List T.signature.SortType)
    (condition : ∀ {s}, Var Λ s → Formula T.signature (s :: Γ)) (body : Formula T.signature (Λ ++ Γ)) :
    Equivalent T (Formula.sequentialWitnesses Λ condition body)
      (Formula.existsMany Λ ((Formula.witnessConjunction Λ condition).conj body)) := by
  let premises := (Formula.witnessConjunction Λ condition).conj body
  let seq := Formula.sequentialWitnesses Λ condition body
  let values : Renaming Λ (Λ ++ Γ) := Var.inLeft Γ
  let lift : Renaming Γ (Λ ++ Γ) := Var.shift Λ
  have useWitnesses : Derivation T premises ((Formula.existsMany Λ premises).rename lift) := by
    simpa only [values, lift, Renaming.append_blocks, Formula.rename_id] using
      (existsManyIntroAlong (T := T) values lift premises)
  have forward : Derivation T seq (Formula.existsMany Λ premises) :=
    .cut (.andIntro (.truth _) (.refl _))
      (sequentialElimWith Λ condition (.cut (.andRight _ _) useWitnesses))
  have reintroduce : Derivation T premises (seq.rename lift) := by
    simpa only [values, lift, Renaming.append_blocks, Formula.rename_id] using
      (sequentialIntro (T := T) Λ condition body values lift)
  exact ⟨⟨forward⟩, ⟨existsManyElim reintroduce⟩⟩

end SHIGURE.Derivation

namespace SHIGURE.Renaming

variable {S : Type u} {Γ Δ : List S} {s : S}

/-- Ambient reindexing commutes with moving the first witness past the rest. -/
theorem liftMany_moveHead (ambient : Renaming Γ Δ) (Λ : List S) :
    @comp S ((s :: Λ) ++ Γ) (Λ ++ s :: Γ) (Λ ++ s :: Δ)
      (liftMany (lift ambient) Λ) (moveHead Λ) =
      @comp S ((s :: Λ) ++ Γ) ((s :: Λ) ++ Δ) (Λ ++ s :: Δ)
        (moveHead Λ) (liftMany ambient (s :: Λ)) := by
  apply ext_append (Λ := s :: Λ)
  · intro t i
    cases i with
    | here =>
      simp only [comp_apply, liftMany_inLeft]
      change liftMany (lift ambient) Λ ((Var.here : Var (s :: Γ) s).shift Λ) =
        (Var.here : Var (s :: Δ) s).shift Λ
      rw [liftMany_shift]
      rfl
    | there j =>
      simp only [comp_apply, liftMany_inLeft]
      change liftMany (lift ambient) Λ (moveHead Λ (.there (j.inLeft Γ))) = moveHead Λ (.there (j.inLeft Δ))
      simp only [moveHead_witness, liftMany_inLeft]
  · intro t i
    simp only [comp_apply, liftMany_shift, moveHead_outer]
    rfl

end SHIGURE.Renaming

namespace SHIGURE.Term

variable {sig : Signature.{u}}

/-- The graph of strict argument binding uses one sequential witness for each input value. -/
theorem letArguments_graphAt (Λ : List sig.SortType) :
    ∀ {Γ E : List sig.SortType} {s : sig.SortType}
      (args : ∀ {t}, Var Λ t → Term sig Γ t) (body : Term sig (Λ ++ Γ) s)
      (ambient : Renaming Γ E) (y : Var E s),
      (letArguments args body).graphAt ambient y =
        Formula.sequentialWitnesses Λ
          (fun i => (args i).graphAt (fun j => .there (ambient j)) .here)
          (body.graphAt (Renaming.liftMany ambient Λ) (y.shift Λ)) := by
  induction Λ with
  | nil => intros; rfl
  | cons t Λ ih =>
    intro Γ E s args body ambient y
    simp only [letArguments, graphAt, ih, Formula.sequentialWitnesses, graphAt_rename,
      graphAt_renameTerm, Renaming.liftMany_moveHead, Renaming.moveHead_outer]
    rfl

end SHIGURE.Term

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ E Λ : List T.signature.SortType} {s : T.signature.SortType}

/-- The graph of a strict application is equivalent to the parallel argument-value graph formula. -/
theorem strictGraph_equivalent (replacement : Term T.signature Λ s)
    (args : ∀ {t}, Var Λ t → Term T.signature Γ t)
    (ambient : Renaming Γ E) (y : Var E s) :
    Equivalent T ((replacement.applyStrict args).graphAt ambient y)
      (Formula.existsMany Λ
        ((Formula.conjoin Λ fun i => (args i).graphAt (Renaming.comp (Var.shift Λ) ambient) (i.inLeft E)).conj
          (replacement.graphAt (Var.inLeft E) (y.shift Λ)))) := by
  rw [Term.applyStrict, Term.letArguments_graphAt]
  have compare := sequentialWitnesses_equivalent (T := T) Λ
    (fun i => (args i).graphAt (fun j => .there (ambient j)) .here)
    ((replacement.rename (Var.inLeft Γ)).graphAt (Renaming.liftMany ambient Λ) (y.shift Λ))
  have sameBody :
      @Renaming.comp T.signature.SortType Λ (Λ ++ Γ) (Λ ++ E)
        (Renaming.liftMany ambient Λ) (Var.inLeft Γ) = (fun {_} i => i.inLeft E) := by
    funext t i
    exact Renaming.liftMany_inLeft ambient i
  simpa only [Formula.witnessConjunction, Term.graphAt_rename, Term.graphAt_renameTerm, sameBody] using compare

end SHIGURE.Derivation
