import Formal.SHIGURE.Part1.Derivations

/-! # Derived rules for finite contexts

The primitive rules of Appendix A.1 suffice to introduce and eliminate a
block of fresh existential witnesses. These derived rules keep the
projection to the ambient context explicit and are used to compare the
expanded value graph of a primitive application with a graph atom.
-/

universe u

namespace SHIGURE

namespace Renaming

variable {S : Type u} {Γ Δ E : List S}

/-- Compose sort-preserving variable maps. -/
def comp (σ : Renaming Δ E) (ρ : Renaming Γ Δ) : Renaming Γ E :=
  fun i => σ (ρ i)

/-- Bind a variable from either part of an appended context to its selected target. -/
def append : {Λ : List S} → Renaming Λ E → Renaming Γ E → Renaming (Λ ++ Γ) E
  | [], _, right => right
  | _ :: _, left, right => cons (left .here) (append (fun i => left (.there i)) right)

/-- Renaming the left block of a concatenation selects the left map. -/
@[simp] theorem append_inLeft {Λ : List S} (left : Renaming Λ E) (right : Renaming Γ E)
    {s : S} (i : Var Λ s) : append left right (i.inLeft Γ) = left i := by
  induction i with
  | here => rfl
  | there i ih => exact ih (fun j => left (.there j))

/-- Renaming a variable past the prefix selects the right map. -/
@[simp] theorem append_shift {Λ : List S} (left : Renaming Λ E) (right : Renaming Γ E)
    {s : S} (i : Var Γ s) : append left right (i.shift Λ) = right i := by
  induction Λ with
  | nil =>
    have same : i.shift [] = i := congrArg (fun f : Renaming Γ Γ => f i) Var.shift_nil
    rw [same]
    rfl
  | cons s Λ ih =>
    rw [Var.shift_cons]
    exact ih (fun j => left (.there j))

/-- Composition is determined coordinatewise. -/
@[simp] theorem comp_apply (σ : Renaming Δ E) (ρ : Renaming Γ Δ) {s : S} (i : Var Γ s) :
    comp σ ρ i = σ (ρ i) :=
  rfl

/-- Lifting past a bound variable respects composition of free-variable maps. -/
theorem lift_comp {s : S} (σ : Renaming Δ E) (ρ : Renaming Γ Δ) :
    @lift S Γ E s (comp σ ρ) = @comp S (s :: Γ) (s :: Δ) (s :: E) σ.lift ρ.lift := by
  funext t i
  cases i <;> rfl

/-- A bound variable and a renamed free context can be specialized together. -/
theorem openHead_lift_shift {s : S} :
    @comp S (s :: Γ) (s :: s :: Γ) (s :: Γ) (openHead Var.here)
      (lift (fun i => Var.there (t := s) i)) = (fun {_} i => i) := by
  funext t i
  cases i <;> rfl

/-- Instantiating a lifted variable map sets the head and retains its tail. -/
theorem openHead_comp_lift {s : S} (x : Var E s) (ρ : Renaming Γ E) :
    @comp S (s :: Γ) (s :: E) E (openHead x) (lift ρ) = @cons S Γ E s x ρ := by
  funext t i
  cases i <;> rfl

/-- A variable inserted after a prefix is ignored when reading the old coordinates. -/
theorem append_insertAfter {s : S} (x : Var E s) (right : Renaming Γ E) :
    ∀ {Λ : List S} (left : Renaming Λ E) {t : S} (i : Var (Λ ++ Γ) t),
      append left (cons x right) (insertAfter Λ i) = append left right i := by
  intro Λ
  induction Λ with
  | nil => intros; rfl
  | cons s Λ ih =>
    intro left t i
    cases i with
    | here => rfl
    | there j => exact ih (fun k => left (.there k)) j

/-- Moving a variable past a block and then renaming has the same selected coordinates. -/
theorem append_moveHead {s : S} {Λ : List S} (x : Var E s)
    (left : Renaming Λ E) (right : Renaming Γ E) :
    @comp S (s :: (Λ ++ Γ)) (Λ ++ s :: Γ) E (append left (cons x right))
      (moveHead Λ) = @cons S (Λ ++ Γ) E s x (append left right) := by
  funext t i
  cases i with
  | here => exact append_shift left (cons x right) Var.here
  | there j => exact append_insertAfter x right left j

/-- Shifting a variable by a nonempty block is the composite of two shifts. -/
theorem shift_cons_comp {s : S} (Λ : List S) :
    (fun {t} (i : Var Γ t) => Var.shift (s :: Λ) i) =
      (fun {t} (i : Var Γ t) => Renaming.comp (fun j => Var.there (t := s) j) (Var.shift Λ) i) := by
  funext _ i
  rw [Renaming.comp_apply]
  exact Var.shift_cons Λ i

/-- Joining the inclusions of both blocks recovers the identity on the full context. -/
theorem append_blocks {Λ : List S} :
    @append S Γ (Λ ++ Γ) Λ (Var.inLeft Γ) (Var.shift Λ) = (fun {_} i => i) := by
  funext t i
  induction Λ with
  | nil =>
    rw [Var.shift_nil]
    rfl
  | cons s Λ ih =>
    cases i with
    | here => exact Var.inLeft_here Γ
    | there j =>
      change append (fun k => (Var.there (t := s) k).inLeft Γ)
        (fun k => Var.shift (s :: Λ) k) j = Var.there j
      simp only [Var.inLeft_there, Var.shift_cons]
      have go : ∀ {Θ : List S} (left : Renaming Θ (Λ ++ Γ))
          (right : Renaming Γ (Λ ++ Γ)) {r : S} (k : Var (Θ ++ Γ) r),
          append (fun i => Var.there (t := s) (left i)) (fun i => Var.there (t := s) (right i)) k =
            Var.there (t := s) (append left right k) := by
        intro Θ
        induction Θ with
        | nil => intros; rfl
        | cons s Θ inner =>
          intro left right r k
          cases k with
          | here => rfl
          | there old => exact inner (fun i => left (.there i)) right old
      rw [go, ih j]

/-- Selecting an old position while leaving it fixed recovers that position. -/
@[simp] theorem append_id_shift {Λ : List S} (left : Renaming Λ Γ)
    {s : S} (i : Var Γ s) : append left (fun j => j) (i.shift Λ) = i :=
  append_shift left (fun j => j) i

end Renaming

namespace Formula

variable {sig : Signature.{u}} {Γ Δ E : List sig.SortType}

/-- Applying two renamings to a formula composes the variable maps. -/
theorem rename_comp (p : Formula sig Γ) :
    ∀ {Δ E : List sig.SortType} (ρ : Renaming Γ Δ) (σ : Renaming Δ E),
      (p.rename ρ).rename σ = p.rename (σ.comp ρ) := by
  induction p with
  | atom a => intros; cases a <;> rfl
  | truth => intros; rfl
  | falsehood => intros; rfl
  | conj p q hp hq =>
    intro Δ E ρ σ
    simp only [Formula.rename_conj, hp, hq]
  | disj p q hp hq =>
    intro Δ E ρ σ
    simp only [Formula.rename_disj, hp, hq]
  | ex p hp =>
    intro Δ E ρ σ
    simp only [rename_ex, hp, Renaming.lift_comp]

/-- Renaming positions by the identity leaves the formula unchanged. -/
@[simp] theorem rename_id (p : Formula sig Γ) : p.rename (fun i => i) = p := by
  induction p with
  | atom a => cases a <;> rfl
  | truth => rfl
  | falsehood => rfl
  | conj p q hp hq => simp only [rename_conj, hp, hq]
  | disj p q hp hq => simp only [rename_disj, hp, hq]
  | @ex Γ s p hp =>
    have eq : @Renaming.lift sig.SortType Γ Γ s (fun i => i) = (fun {_} i => i) := by
      funext t i
      cases i <;> rfl
    simp only [rename_ex, eq, hp]

/-- A block of equality conditions compares two tuples of variables in the same context. -/
def equalArguments (Λ : List sig.SortType) (left right : Renaming Λ Γ) :
    Formula sig Γ :=
  conjoin Λ (fun i => .atom (.eq (left i) (right i)))

/-- Renaming a finite conjunction renames each component. -/
theorem rename_conjoin (Λ : List sig.SortType) (f : ∀ {s}, Var Λ s → Formula sig Γ)
    (ρ : Renaming Γ Δ) :
    (conjoin Λ f).rename ρ = conjoin Λ (fun i => (f i).rename ρ) := by
  induction Λ with
  | nil => rfl
  | cons s Λ ih =>
    exact congrArg (fun p => ((f .here).rename ρ).conj p) (ih (fun i => f (.there i)))

end Formula

namespace Derivation

variable {T : Theory.{u}} {Γ Λ : List T.signature.SortType} {s : T.signature.SortType}
  {p q r z : Formula T.signature Γ}

/-- Map a derivation through both projections of a conjunction. -/
def andMono (hp : Derivation T p q) (hr : Derivation T r z) :
    Derivation T (p.conj r) (q.conj z) :=
  .andIntro (.cut (.andLeft p r) hp) (.cut (.andRight p r) hr)

/-- Map a derivation through a disjunction, keeping its two branches separate. -/
def orMono (hp : Derivation T p q) (hr : Derivation T r z) :
    Derivation T (p.disj r) (q.disj z) :=
  .cut (.andIntro (.truth _) (.refl _))
    (.orElim (.cut (.andRight _ _) (.cut hp (.orLeft _ _)))
      (.cut (.andRight _ _) (.cut hr (.orRight _ _))))

/-- Apply existence elimination with the context-free assumption true. -/
def existsElimPlain {body : Formula T.signature (s :: Γ)}
    (d : Derivation T body (q.rename (fun i => .there i))) : Derivation T body.ex q :=
  .cut (.andIntro (.truth _) (.refl _)) (.existsElim (.cut (.andRight _ _) d))

/-- An implication between bodies induces an implication between their existential closures. -/
def existsMono {body target : Formula T.signature (s :: Γ)}
    (d : Derivation T body target) : Derivation T body.ex target.ex := by
  apply existsElimPlain
  refine .cut d ?_
  have introRule := (Derivation.existsIntro (T := T)
    (target.rename (Renaming.lift (fun i => Var.there (t := s) i))) Var.here)
  simpa only [Formula.rename_comp, Renaming.openHead_lift_shift, Formula.rename_id, Formula.rename_ex]
    using introRule

/-- Parallel implication remains valid when a whole block is existentially bound. -/
def existsManyMono : {Λ : List T.signature.SortType} →
    {p q : Formula T.signature (Λ ++ Γ)} →
    Derivation T p q → Derivation T (Formula.existsMany Λ p) (Formula.existsMany Λ q)
  | [], _, _, d => d
  | _ :: Λ, p, q, d => existsManyMono (Λ := Λ) (p := p.ex) (q := q.ex) (existsMono d)

/-- Eliminate a block of witnesses from a conclusion that mentions only the old context. -/
def existsManyElim : {Λ : List T.signature.SortType} →
    {body : Formula T.signature (Λ ++ Γ)} →
    Derivation T body (q.rename (Var.shift Λ)) → Derivation T (Formula.existsMany Λ body) q
  | [], _, d => by simpa only [Var.shift_nil, Formula.rename_id] using d
  | s :: Λ, _, d => by
    apply existsManyElim (Λ := Λ)
    apply existsElimPlain
    rw [Formula.rename_comp]
    change Derivation T _ (q.rename (fun i => Renaming.comp (fun j => Var.there (t := s) j) (Var.shift Λ) i))
    rw [← Renaming.shift_cons_comp]
    exact d

/-- Introduce a block of witnesses taken from variables in the ambient context. -/
def existsManyIntro : {Λ : List T.signature.SortType} →
    (witness : Renaming Λ Γ) → (body : Formula T.signature (Λ ++ Γ)) →
    Derivation T (body.rename (Renaming.append witness (fun i => i))) (Formula.existsMany Λ body)
  | [], _, body => by
    change Derivation T (body.rename (fun i => i)) body
    rw [Formula.rename_id]
    exact .refl body
  | _ :: Λ, witness, body => by
    let tail : Renaming Λ Γ := fun i => witness (.there i)
    let head : Var (Λ ++ Γ) _ := (witness .here).shift Λ
    let filled := body.rename (Renaming.openHead head)
    have same : (filled.rename (Renaming.append tail (fun i => i))) =
        body.rename (Renaming.append witness (fun i => i)) := by
      simp only [filled, Formula.rename_comp]
      congr 1
      funext t i
      cases i with
      | here => exact Renaming.append_shift tail (fun j => j) (witness .here)
      | there i => rfl
    rw [← same]
    exact .cut (existsManyIntro tail filled) (existsManyMono (.existsIntro body head))

/-- Read any component of a finite conjunction. -/
def conjoinAt : {Λ : List T.signature.SortType} →
    (f : ∀ {s}, Var Λ s → Formula T.signature Γ) → {s : T.signature.SortType} →
    (i : Var Λ s) → Derivation T (Formula.conjoin Λ f) (f i)
  | _, _, _, .here => .andLeft _ _
  | _, f, _, .there i => .cut (.andRight _ _) (conjoinAt (fun j => f (.there j)) i)

/-- Build a finite conjunction from proofs with a shared antecedent. -/
def conjoinIntro : {Λ : List T.signature.SortType} →
    (f : ∀ {s}, Var Λ s → Formula T.signature Γ) →
    (∀ {s} (i : Var Λ s), Derivation T p (f i)) → Derivation T p (Formula.conjoin Λ f)
  | [], _, _ => .truth _
  | _ :: _, f, proof => .andIntro (proof .here)
      (conjoinIntro (fun i => f (.there i)) (fun i => proof (.there i)))

/-- Symmetry of variable equality is derived from reflexivity and equality substitution. -/
def eqSymm (x y : Var Γ s) : Derivation T (.atom (.eq x y)) (.atom (.eq y x)) :=
  .cut (.andIntro (.refl _) (.cut (.truth _) (.eqRefl x)))
    (.eqSubst (.atom (.eq .here (.there x))) x y)

/-- Change the direction of every equality in an argument tuple. -/
def equalArgumentsSymm (left right : Renaming Λ Γ) :
    Derivation T (Formula.equalArguments Λ left right) (Formula.equalArguments Λ right left) :=
  conjoinIntro (fun i => .atom (.eq (right i) (left i)))
    (fun i => .cut (conjoinAt (fun j => .atom (.eq (left j) (right j))) i)
      (eqSymm (left i) (right i)))

/-- Changing a block of equal variables in a formula is derivable from the equality rule. -/
def renameAlongEqual : {Λ Δ : List T.signature.SortType} →
    (body : Formula T.signature (Λ ++ Δ)) → (left right : Renaming Λ Γ) →
    (ambient : Renaming Δ Γ) →
    Derivation T ((Formula.equalArguments Λ left right).conj (body.rename (Renaming.append left ambient)))
      (body.rename (Renaming.append right ambient))
  | [], _, _, _, _, _ => .andRight _ _
  | s :: Λ, Δ, body, left, right, ambient => by
    let leftTail : Renaming Λ Γ := fun i => left (.there i)
    let rightTail : Renaming Λ Γ := fun i => right (.there i)
    let openBody := body.rename (Renaming.lift (Renaming.append leftTail ambient))
    let middle := body.rename (Renaming.cons (right .here) (Renaming.append leftTail ambient))
    have headStep : Derivation T
        ((Formula.atom (.eq (left .here) (right .here))).conj
          (body.rename (Renaming.append left ambient))) middle := by
      simpa only [openBody, middle, Formula.rename_comp, Renaming.openHead_comp_lift, Renaming.append]
        using (Derivation.eqSubst (T := T) openBody (left .here) (right .here))
    have tailStep := renameAlongEqual (body.rename (Renaming.moveHead (Γ := Δ) Λ))
      leftTail rightTail (Renaming.cons (right .here) ambient)
    have tailStep' : Derivation T ((Formula.equalArguments Λ leftTail rightTail).conj middle)
        (body.rename (Renaming.append right ambient)) := by
      simpa only [middle, Formula.rename_comp, Renaming.append_moveHead, Renaming.append, rightTail]
        using tailStep
    exact .cut (.andIntro (.cut (.andLeft _ _) (.andRight _ _))
      (.cut (.andIntro (.cut (.andLeft _ _) (.andLeft _ _)) (.andRight _ _)) headStep)) tailStep'

/-- An application to variables has the same derivable graph as its primitive graph atom. -/
def primitiveGraph (op : Operation T.signature) (inputs : Renaming op.arity.inputs Γ)
    (y : Var Γ op.arity.output) :
    Derivation T
      ((Term.app op (fun i => Term.var (inputs i))).graphAt (fun i => i) y)
      (.atom (.graph op inputs y)) ×
    Derivation T (.atom (.graph op inputs y))
      ((Term.app op (fun i => Term.var (inputs i))).graphAt (fun i => i) y) := by
  let Λ := op.arity.inputs
  let left : Renaming Λ (Λ ++ Γ) := Var.inLeft Γ
  let right : Renaming Λ (Λ ++ Γ) := fun i => (inputs i).shift Λ
  let lift : Renaming Γ (Λ ++ Γ) := Var.shift Λ
  let graphAtom : Formula T.signature Γ := .atom (.graph op inputs y)
  let atomOnWitnesses : Formula T.signature (Λ ++ Γ) := .atom (.graph op left (lift y))
  let body := (Formula.equalArguments Λ right left).conj atomOnWitnesses
  have atomAfterChange : atomOnWitnesses.rename (Renaming.append right lift) =
      graphAtom.rename lift := by
    simp only [atomOnWitnesses, graphAtom, Formula.rename_atom, Atomic.rename_graph, left, right,
      Renaming.append_inLeft, lift, Renaming.append_shift]
  have d := renameAlongEqual (T := T) (Γ := Λ ++ Γ) atomOnWitnesses left right lift
  rw [atomAfterChange] at d
  have toAtom : Derivation T body (graphAtom.rename lift) := by
    have d' : Derivation T ((Formula.equalArguments Λ left right).conj atomOnWitnesses)
        (graphAtom.rename lift) := by
      simpa only [left, lift, Renaming.append_blocks, Formula.rename_id]
        using d
    exact .cut (andMono (equalArgumentsSymm right left) (.refl _)) d'
  have introBlock := existsManyIntro (T := T) inputs body
  have filledOld {t : T.signature.SortType} (i : Var Γ t) :
      Renaming.append inputs (fun j => j) (i.shift Λ) = i :=
    Renaming.append_id_shift inputs i
  have filled : body.rename (Renaming.append inputs (fun i => i)) =
      (Formula.equalArguments Λ inputs inputs).conj graphAtom := by
    simp only [body, Formula.rename_conj, Formula.rename_atom, Formula.equalArguments,
      Formula.rename_conjoin, Atomic.rename_eq, Atomic.rename_graph, atomOnWitnesses, graphAtom, right, left, lift,
      filledOld, Renaming.append_inLeft]
  rw [filled] at introBlock
  have reflexiveTuple : Derivation T graphAtom (Formula.equalArguments Λ inputs inputs) :=
    conjoinIntro (fun i => .atom (.eq (inputs i) (inputs i)))
      (fun i => .cut (.truth _) (.eqRefl (inputs i)))
  rw [Term.graphAt_app_vars]
  change Derivation T (Formula.existsMany Λ body) graphAtom ×
    Derivation T graphAtom (Formula.existsMany Λ body)
  exact ⟨existsManyElim toAtom, .cut (.andIntro reflexiveTuple (.refl _)) introBlock⟩

end Derivation

end SHIGURE
