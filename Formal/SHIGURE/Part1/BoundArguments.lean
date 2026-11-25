import Formal.SHIGURE.Part1.GraphDerivations
import Formal.SHIGURE.Part1.Substitution

/-! # Derivations for finite blocks of value witnesses

Appendix A uses finite blocks of existential variables for partial
arguments. The rules below compare those bound values to values whose
graphs are already derived in the ambient context.

## Implementation notes

The premises supply proof trees for each argument graph. Graph functionality
compares those values with the existential witnesses, so the same arguments
can be supplied to any body in the bound context.
A semantic comparison would only give equal values in models. The
local proof in the witness context can be cut into a later derivation.
-/

universe u

namespace SHIGURE.Renaming

variable {S : Type u} {Γ Δ E : List S}

/-- Composition with a renaming out of an appended context acts on both blocks. -/
theorem comp_append (outer : Renaming Δ E) :
    ∀ {Λ : List S} (left : Renaming Λ Δ) (right : Renaming Γ Δ),
      @comp S (Λ ++ Γ) Δ E outer (append left right) =
        @append S Γ E Λ (comp outer left) (comp outer right) := by
  intro Λ
  induction Λ with
  | nil => intros; rfl
  | cons s Λ ih =>
    intro left right
    funext t i
    cases i with
    | here => rfl
    | there i =>
      exact congrArg (fun (ρ : Renaming (Λ ++ Γ) E) => ρ i) (ih (fun v => left (.there v)) right)

/-- A renaming out of an appended context is determined by both blocks. -/
theorem ext_append {Λ : List S} {left right : Renaming (Λ ++ Γ) E}
    (leftBlock : ∀ {s} (i : Var Λ s), left (i.inLeft Γ) = right (i.inLeft Γ))
    (rightBlock : ∀ {s} (i : Var Γ s), left (i.shift Λ) = right (i.shift Λ)) : @left = @right := by
  induction Λ with
  | nil =>
    funext s i
    have shift : i.shift [] = i := congrArg (fun ρ : Renaming Γ Γ => ρ i) Var.shift_nil
    simpa only [shift] using rightBlock i
  | cons s Λ ih =>
    let leftTail : Renaming (Λ ++ Γ) E := fun i => left (.there i)
    let rightTail : Renaming (Λ ++ Γ) E := fun i => right (.there i)
    have tail : @leftTail = @rightTail := ih (fun i => leftBlock (.there i)) (fun i => by
      simpa only [Var.shift_cons] using rightBlock i)
    funext t i
    cases i with
    | here => exact leftBlock .here
    | there i => exact congrArg (fun (ρ : Renaming (Λ ++ Γ) E) => ρ i) tail

/-- Filling a lifted witness block preserves the selected variable map on ambient inputs. -/
theorem fill_liftMany {Λ : List S} (witness : Renaming Λ E) (ambient : Renaming Γ E) :
    @comp S (Λ ++ Γ) (Λ ++ E) E (append witness (fun i => i)) (liftMany ambient Λ) =
      @append S Γ E Λ witness ambient := by
  apply ext_append
  · intro s i
    simp only [comp_apply, liftMany_inLeft, append_inLeft]
  · intro s i
    simp only [comp_apply, liftMany_shift, append_shift]

end SHIGURE.Renaming

namespace SHIGURE.Term

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}

/-- Renaming a term composes the input map used to read its value graph. -/
theorem graphAt_renameTerm (t : Term sig Γ s) :
    ∀ {Δ E : List sig.SortType} (first : Renaming Γ Δ) (second : Renaming Δ E) (out : Var E s),
      (t.rename first).graphAt second out = t.graphAt (Renaming.comp second first) out := by
  induction t with
  | var i => intros; rfl
  | app op terms ih =>
    intro Δ E first second out
    simp only [rename_app, graphAt_app, ih]
    rfl
  | letBind init body hi hb =>
    intro Δ E first second out
    simp only [rename_letBind, graphAt_letBind, hi, hb, ← Renaming.lift_comp]
    rfl

end SHIGURE.Term

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ Δ : List T.signature.SortType}

/-- Introduce the chosen witnesses after reindexing the ambient variables. -/
def existsManyIntroAlong {Λ : List T.signature.SortType}
    (witness : Renaming Λ Δ) (ambient : Renaming Γ Δ) (p : Formula T.signature (Λ ++ Γ)) :
    Derivation T (p.rename (Renaming.append witness ambient)) ((Formula.existsMany Λ p).rename ambient) := by
  rw [Formula.rename_existsMany]
  simpa only [Formula.rename_comp, Renaming.fill_liftMany] using
    (existsManyIntro (T := T) witness (p.rename (Renaming.liftMany ambient Λ)))

/-- Given evaluated argument values, binding the value witnesses is equivalent to supplying those values. -/
noncomputable def useBoundValues {Λ : List T.signature.SortType}
    (terms : ∀ {s}, Var Λ s → Term T.signature Δ s)
    (ambient : Renaming Δ Γ) (values : Renaming Λ Γ) (assumption : Formula T.signature Γ)
    (value : ∀ {s} (i : Var Λ s), Derivation T assumption ((terms i).graphAt ambient (values i)))
    (body : Formula T.signature (Λ ++ Γ)) :
    let lift : Renaming Γ (Λ ++ Γ) := Var.shift Λ
    let graph := Formula.conjoin Λ fun i => (terms i).graphAt (Renaming.comp lift ambient) (i.inLeft Γ)
    let bound := Formula.existsMany Λ (graph.conj body)
    let filled := body.rename (Renaming.append values (fun i => i))
    Derivation T (assumption.conj bound) filled × Derivation T (assumption.conj filled) bound := by
  dsimp only
  let lift : Renaming Γ (Λ ++ Γ) := Var.shift Λ
  let left : Renaming Λ (Λ ++ Γ) := Var.inLeft Γ
  let right : Renaming Λ (Λ ++ Γ) := fun i => (values i).shift Λ
  let graphs := Formula.conjoin Λ fun i => (terms i).graphAt (Renaming.comp lift ambient) (left i)
  let res := body.rename (Renaming.append values (fun i => i))
  let assumptions := (assumption.rename lift).conj (graphs.conj body)
  have equal : Derivation T assumptions (Formula.equalArguments Λ left right) := by
    apply conjoinIntro
    intro s i
    have found : Derivation T assumptions ((terms i).graphAt (Renaming.comp lift ambient) (left i)) :=
      .cut (.andRight _ _) (.cut (.andLeft _ _) (conjoinAt _ i))
    have fixed : Derivation T assumptions ((terms i).graphAt (Renaming.comp lift ambient) (right i)) := by
      rw [← Term.graphAt_rename]
      exact .cut (.andLeft _ _) (.rename lift (value i))
    exact .cut (.andIntro found fixed) (termGraphFunctional (terms i) _ _ _)
  have matchBody : Derivation T ((Formula.equalArguments Λ left right).conj body) (res.rename lift) := by
    simpa only [left, right, lift, res, Renaming.append_blocks, Formula.rename_id,
      Formula.rename_comp, Renaming.comp_append] using
      (renameAlongEqual (T := T) body left right lift)
  have forward : Derivation T assumptions (res.rename lift) :=
    .cut (.andIntro equal (.cut (.andRight _ _) (.andRight _ _))) matchBody
  have instantiate : graphs.rename (Renaming.append values (fun i => i)) =
      Formula.conjoin Λ (fun i => (terms i).graphAt ambient (values i)) := by
    simp only [graphs, Formula.rename_conjoin, Term.graphAt_rename, left, Renaming.append_inLeft]
    have same :
        @Renaming.comp T.signature.SortType Δ (Λ ++ Γ) Γ (Renaming.append values (fun i => i))
            (Renaming.comp lift ambient) = @ambient := by
      funext s i
      exact Renaming.append_id_shift values (ambient i)
    simp only [same]
  have backward : Derivation T (assumption.conj res) (Formula.existsMany Λ (graphs.conj body)) := by
    have pack := existsManyIntro (T := T) values (graphs.conj body)
    rw [Formula.rename_conj, instantiate] at pack
    exact .cut (.andIntro (.cut (.andLeft _ _) (conjoinIntro _ value)) (.andRight _ _)) pack
  exact ⟨existsManyElimWith forward, backward⟩

/-- The same bound-value comparison after a renaming of ambient variables. -/
noncomputable def useBoundValuesAlong {Λ : List T.signature.SortType}
    (terms : ∀ {s}, Var Λ s → Term T.signature Δ s)
    (ambient : Renaming Δ Γ) (values : Renaming Λ Γ) (assumption : Formula T.signature Γ)
    (value : ∀ {s} (i : Var Λ s), Derivation T assumption ((terms i).graphAt ambient (values i)))
    (body : Formula T.signature (Λ ++ Δ)) :
    let bound := (Formula.bindArguments Λ terms body).rename ambient
    let filled := body.rename (Renaming.append values ambient)
    Derivation T (assumption.conj bound) filled × Derivation T (assumption.conj filled) bound := by
  dsimp only
  have liftShift :
      @Renaming.comp T.signature.SortType Δ (Λ ++ Δ) (Λ ++ Γ)
        (Renaming.liftMany ambient Λ) (Var.shift Λ) =
      @Renaming.comp T.signature.SortType Δ Γ (Λ ++ Γ) (Var.shift Λ) ambient := by
    funext s i
    exact Renaming.liftMany_shift ambient Λ i
  simp only [Formula.bindArguments_eq_existsMany, Formula.rename_existsMany, Formula.rename_conj,
    Formula.rename_conjoin, Term.graphAt_rename, Renaming.liftMany_inLeft, liftShift]
  simpa only [Formula.rename_comp, Renaming.fill_liftMany] using
    (useBoundValues terms ambient values assumption value (body.rename (Renaming.liftMany ambient Λ)))

/-- The equality rules derive transitivity on any three variables of the same sort. -/
def eqTrans {s : T.signature.SortType} (x y z : Var Γ s) :
    Derivation T ((Formula.atom (.eq x y)).conj (.atom (.eq y z))) (.atom (.eq x z)) :=
  .cut (.andIntro (.andRight _ _) (.andLeft _ _)) (.eqSubst (.atom (.eq (.there x) .here)) y z)

/-- Substitution of equals changes the output variable of an instantiated term graph. -/
def replaceGraphOutput {s : T.signature.SortType} (t : Term T.signature Δ s)
    (ambient : Renaming Δ Γ) (y z : Var Γ s) :
    Derivation T ((Formula.atom (.eq y z)).conj (t.graphAt ambient y)) (t.graphAt ambient z) := by
  simpa only [Formula.rename_comp, Renaming.openHead_comp_lift, ← t.graphAt_eq_rename_graph] using
    (Derivation.eqSubst (T := T) (t.graph.rename (Renaming.lift ambient)) y z)

/-- Two defined terms are equal exactly when their specified values are equal. -/
noncomputable def useTermEquality {s : T.signature.SortType} (t t' : Term T.signature Δ s)
    (ambient : Renaming Δ Γ) (y z : Var Γ s) (assumption : Formula T.signature Γ)
    (left : Derivation T assumption (t.graphAt ambient y)) (right : Derivation T assumption (t'.graphAt ambient z)) :
    let expanded := (Formula.termEq t t').rename ambient
    let eq := Formula.atom (.eq y z)
    Derivation T (assumption.conj expanded) eq × Derivation T (assumption.conj eq) expanded := by
  dsimp only
  let weaken : Renaming Γ (s :: Γ) := fun v => .there v
  let read : Renaming Δ (s :: Γ) := Renaming.comp weaken ambient
  let body := (t.graphAt read .here).conj (t'.graphAt read .here)
  let eq := Formula.atom (.eq y z)
  have expanded : (Formula.termEq t t').rename ambient = body.ex := by
    have lifted : @Renaming.lift T.signature.SortType Δ Γ s ambient =
        @Renaming.cons T.signature.SortType Δ (s :: Γ) s .here read := by
      funext sort i
      cases i <;> rfl
    rw [Formula.termEq_eq_ex, Formula.rename_ex, Formula.rename_conj, lifted, ← t.graphAt_eq_rename_graph,
      ← t'.graphAt_eq_rename_graph]
  rw [expanded]
  let inside := (assumption.rename weaken).conj body
  have leftValue : Derivation T inside (t.graphAt read (.there y)) := by
    rw [← Term.graphAt_rename]
    exact .cut (.andLeft _ _) (.rename weaken left)
  have rightValue : Derivation T inside (t'.graphAt read (.there z)) := by
    rw [← Term.graphAt_rename]
    exact .cut (.andLeft _ _) (.rename weaken right)
  have agreesLeft := Derivation.cut (.andIntro leftValue (.cut (.andRight _ _) (.andLeft _ _)))
    (termGraphFunctional t read (.there y) .here)
  have agreesRight := Derivation.cut (.andIntro (.cut (.andRight _ _) (.andRight _ _)) rightValue)
    (termGraphFunctional t' read .here (.there z))
  have forward : Derivation T inside (eq.rename weaken) :=
    .cut (.andIntro agreesLeft agreesRight) (eqTrans (.there y) .here (.there z))
  have atSameValue : Derivation T (assumption.conj eq) (t'.graphAt ambient y) := by
    exact .cut (.andIntro (.cut (.andRight _ _) (eqSymm y z)) (.cut (.andLeft _ _) right))
      (replaceGraphOutput t' ambient z y)
  have filled : body.rename (Renaming.openHead y) = (t.graphAt ambient y).conj (t'.graphAt ambient y) := by
    simp only [body, Formula.rename_conj, Term.graphAt_rename]
    rfl
  have pack := Derivation.existsIntro (T := T) body y
  rw [filled] at pack
  exact ⟨.existsElim forward, .cut (.andIntro (.cut (.andLeft _ _) left) atSameValue) pack⟩

end SHIGURE.Derivation

namespace SHIGURE.Formula

variable {sig : Signature.{u}} {Γ : List sig.SortType}

/-- Put separately witnessed formulas into one context, with one variable for every witness. -/
def witnessConjunction (Λ : List sig.SortType)
    (condition : ∀ {s}, Var Λ s → Formula sig (s :: Γ)) : Formula sig (Λ ++ Γ) :=
  conjoin Λ fun i => (condition i).rename (Renaming.cons (i.inLeft Γ) (Var.shift Λ))

/-- Each condition of the witness conjunction uses the corresponding leading variable. -/
theorem witnessConjunction_eq_conjoin (Λ : List sig.SortType)
    (condition : ∀ {s}, Var Λ s → Formula sig (s :: Γ)) :
    witnessConjunction Λ condition =
      conjoin Λ (fun i => (condition i).rename (Renaming.cons (i.inLeft Γ) (Var.shift Λ))) := rfl

/-- The head condition introduces the head witness and the rest share the existing ambient positions. -/
theorem witnessConjunction_cons {Λ : List sig.SortType} {s : sig.SortType}
    (condition : ∀ {t}, Var (s :: Λ) t → Formula sig (t :: Γ)) :
    witnessConjunction (s :: Λ) condition =
      ((condition .here).rename (Renaming.lift (Var.shift Λ))).conj
        ((witnessConjunction Λ fun i => condition (.there i)).rename (fun i => .there i)) := by
  simp only [witnessConjunction_eq_conjoin, conjoin_cons, rename_conjoin, rename_comp, Renaming.comp_cons,
    Renaming.shift_cons_comp, Renaming.comp_apply]
  rfl

end SHIGURE.Formula

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ : List T.signature.SortType}

/-- A finite conjunction of existentials yields a block of witnesses for all its conjuncts. -/
def packExistences : ∀ {Λ : List T.signature.SortType}
    (condition : ∀ {s}, Var Λ s → Formula T.signature (s :: Γ)),
    Derivation T (Formula.conjoin Λ fun i => (condition i).ex)
      (Formula.existsMany Λ (Formula.witnessConjunction Λ condition)) := by
  intro Λ
  induction Λ with
  | nil => intro condition; exact .refl _
  | cons s Λ ih =>
    intro condition
    let head := condition (Var.here : Var (s :: Λ) s)
    let tail := Formula.witnessConjunction Λ (fun i => condition (.there i))
    let together := Formula.witnessConjunction (s :: Λ) condition
    let result := Formula.existsMany (s :: Λ) together
    let lift : Renaming Γ (Λ ++ Γ) := Var.shift Λ
    have shape : together = ((head.rename (Renaming.lift lift)).conj (tail.rename (fun i => .there i))) :=
      Formula.witnessConjunction_cons condition
    have atAllWitnesses : Derivation T together ((result.rename lift).rename (fun i => .there i)) := by
      simpa only [Renaming.append_blocks, Formula.rename_id, Formula.rename_comp] using
        (existsManyIntroAlong (T := T) (Var.inLeft Γ : Renaming (s :: Λ) ((s :: Λ) ++ Γ))
          (Var.shift (s :: Λ)) together)
    have swapped : Derivation T (tail.conj (head.ex.rename lift)) (result.rename lift) := by
      rw [Formula.rename_ex]
      apply Derivation.existsElim
      rw [shape] at atAllWitnesses
      exact .cut (.andIntro (.andRight _ _) (.andLeft _ _)) atAllWitnesses
    have withTail : Derivation T ((head.ex.rename lift).conj tail) (result.rename lift) :=
      .cut (.andIntro (.andRight _ _) (.andLeft _ _)) swapped
    exact .cut (andMono (.refl _) (ih (fun i => condition (.there i)))) (existsManyElimWith withTail)

end SHIGURE.Derivation
