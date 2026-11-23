import Formal.SHIGURE.Part1.Laws
import Mathlib.Algebra.Ring.MinimalAxioms

/-! # Declared value rings and residuals

The value ring of Definition 1.5 is determined by the interpretation of its
named symbols and the satisfaction of its ring Laws.

## Implementation notes

The ring expression fragment builds the positive equality Laws in the
general term language. Its direct interpretation uses the functions named
by the signature, which gives a comparison from Law satisfaction to
mathlib's algebraic identities. The mathlib constructor supplies derived
operations such as subtraction from these functions.

An external `CommRing` instance on the carrier would also supply subtraction,
but its operations could differ from the ones interpreted by the structure.
The selected symbols keep their declaration tags and may include quantities
because Definition 1.2 treats them as marked total operations. The associated
profile equality rules out symbols of the wrong arity or sort.
Writing each ring identity directly with general terms would require proving
total evaluation for each displayed term separately. The small expression
grammar lets one induction supply those proofs and translates every identity
back into the general syntax before forming its Law.
-/

universe u

namespace SHIGURE

/-- The declared ordinary operations or quantities of a commutative ring at a specified sort. -/
structure RingVocabulary (sig : Signature.{u}) (s : sig.SortType) where
  /-- The zero symbol. -/
  zero : TypedTotal sig ⟨[], s⟩
  /-- The unit symbol. -/
  one : TypedTotal sig ⟨[], s⟩
  /-- The addition symbol. -/
  add : TypedTotal sig ⟨[s, s], s⟩
  /-- The additive inverse symbol. -/
  neg : TypedTotal sig ⟨[s], s⟩
  /-- The multiplication symbol. -/
  mul : TypedTotal sig ⟨[s, s], s⟩

namespace RingVocabulary

variable {sig : Signature.{u}} {s : sig.SortType}

/-- The zero element interpreted by the declared zero symbol. -/
def zeroValue (ring : RingVocabulary sig s) (A : Structure sig) : A.carrier s :=
  ring.zero.value A Assignment.empty

/-- The unit interpreted by the declared unit symbol. -/
def oneValue (ring : RingVocabulary sig s) (A : Structure sig) : A.carrier s :=
  ring.one.value A Assignment.empty

/-- Addition interpreted by the declared addition symbol. -/
def addValue (ring : RingVocabulary sig s) (A : Structure sig)
    (x y : A.carrier s) : A.carrier s :=
  ring.add.value A (Assignment.cons x (Assignment.cons y Assignment.empty))

/-- Additive inverse interpreted by the declared negation symbol. -/
def negValue (ring : RingVocabulary sig s) (A : Structure sig) (x : A.carrier s) :
    A.carrier s :=
  ring.neg.value A (Assignment.cons x Assignment.empty)

/-- Multiplication interpreted by the declared multiplication symbol. -/
def mulValue (ring : RingVocabulary sig s) (A : Structure sig)
    (x y : A.carrier s) : A.carrier s :=
  ring.mul.value A (Assignment.cons x (Assignment.cons y Assignment.empty))

/-- The expression fragment used to write the ring Laws at one sort. -/
inductive Expr {S : Type u} (Γ : List S) (s : S) : Type u
  | var : Var Γ s → Expr Γ s
  | zero
  | one
  | add : Expr Γ s → Expr Γ s → Expr Γ s
  | neg : Expr Γ s → Expr Γ s
  | mul : Expr Γ s → Expr Γ s → Expr Γ s

namespace Expr

variable {Γ : List sig.SortType}

/-- Translate a ring expression to the signature's declared total operations. -/
def toTerm (ring : RingVocabulary sig s) : Expr Γ s → Term sig Γ s
  | .var index => .var index
  | .zero => ring.zero.term (@Term.argsNil sig Γ)
  | .one => ring.one.term (@Term.argsNil sig Γ)
  | .add x y => ring.add.term ((toTerm ring x).argsCons ((toTerm ring y).argsCons Term.argsNil))
  | .neg x => ring.neg.term ((toTerm ring x).argsCons Term.argsNil)
  | .mul x y => ring.mul.term ((toTerm ring x).argsCons ((toTerm ring y).argsCons Term.argsNil))

/-- Evaluate an expression using the interpreted functions of the declared ring. -/
def value (ring : RingVocabulary sig s) (A : Structure sig) (e : Assignment A.carrier Γ) :
    Expr Γ s → A.carrier s
  | .var index => e index
  | .zero => ring.zeroValue A
  | .one => ring.oneValue A
  | .add x y => ring.addValue A (value ring A e x) (value ring A e y)
  | .neg x => ring.negValue A (value ring A e x)
  | .mul x y => ring.mulValue A (value ring A e x) (value ring A e y)

/-- Two evaluated terms supply the two arguments of a binary ring operation. -/
private theorem evaluates_pair {A : Structure sig} {e : Assignment A.carrier Γ}
    {a b : Term sig Γ s} {x y : A.carrier s}
    (ha : a.Evaluates A e x) (hb : b.Evaluates A e y) :
    ∀ {t} (index : Var [s, s] t),
      (a.argsCons (b.argsCons Term.argsNil) index).Evaluates A e
        ((Assignment.cons x (Assignment.cons y Assignment.empty)) index) := by
  intro t index
  cases index with
  | here => exact ha
  | there index =>
    cases index with
    | here => exact hb
    | there index => nomatch index

/-- The translated term evaluates to the compositional interpretation of the ring expression. -/
theorem evaluates_toTerm (ring : RingVocabulary sig s) (A : Structure sig)
    (e : Assignment A.carrier Γ) (expr : Expr Γ s) :
    (expr.toTerm ring).Evaluates A e (expr.value ring A e) := by
  induction expr with
  | var index => rfl
  | zero =>
    exact ring.zero.evaluates_term _ A e Assignment.empty (fun index => nomatch index)
  | one =>
    exact ring.one.evaluates_term _ A e Assignment.empty (fun index => nomatch index)
  | add x y hx hy =>
    exact ring.add.evaluates_term _ A e
      (Assignment.cons (x.value ring A e) (Assignment.cons (y.value ring A e) Assignment.empty))
      (evaluates_pair hx hy)
  | neg x hx =>
    apply ring.neg.evaluates_term
    intro t index
    cases index with
    | here => exact hx
    | there index => nomatch index
  | mul x y hx hy =>
    exact ring.mul.evaluates_term _ A e
      (Assignment.cons (x.value ring A e) (Assignment.cons (y.value ring A e) Assignment.empty))
      (evaluates_pair hx hy)

/-- The unconditional equality of two expressions in the same variable context. -/
def equality (ring : RingVocabulary sig s) (lhs rhs : Expr Γ s) : Law sig :=
  Law.equality (lhs.toTerm ring) (rhs.toTerm ring)

/-- Satisfaction of the equality Law is pointwise equality of the interpreted expressions. -/
theorem holds_equality_iff (ring : RingVocabulary sig s) (lhs rhs : Expr Γ s)
    (A : Structure sig) : (equality ring lhs rhs).Holds A ↔
      ∀ e : Assignment A.carrier Γ, lhs.value ring A e = rhs.value ring A e := by
  rw [equality, Law.holds_equality_iff]
  constructor
  · intro h e
    obtain ⟨y, hleft, hright⟩ := h e
    exact (Term.evaluates_unique A (lhs.toTerm ring) e (lhs.evaluates_toTerm ring A e) hleft).trans
      (Term.evaluates_unique A (rhs.toTerm ring) e hright (rhs.evaluates_toTerm ring A e))
  · intro h e
    refine ⟨lhs.value ring A e, lhs.evaluates_toTerm ring A e, ?_⟩
    rw [h e]
    exact rhs.evaluates_toTerm ring A e

end Expr

/-- The equations in mathlib's minimal presentation of a commutative ring. -/
inductive LawName
  | addAssoc | zeroAdd | negAdd | mulAssoc | mulComm | oneMul | mulAdd

/-- The variable contexts and equations of the declared ring Laws. -/
def law (ring : RingVocabulary sig s) : LawName → Law sig
  | .addAssoc =>
    let x : Expr [s, s, s] s := .var .here
    let y : Expr [s, s, s] s := .var (.there .here)
    let z : Expr [s, s, s] s := .var (.there (.there .here))
    Expr.equality ring (.add (.add x y) z) (.add x (.add y z))
  | .zeroAdd =>
    let x : Expr [s] s := .var .here
    Expr.equality ring (.add .zero x) x
  | .negAdd =>
    let x : Expr [s] s := .var .here
    Expr.equality ring (.add (.neg x) x) .zero
  | .mulAssoc =>
    let x : Expr [s, s, s] s := .var .here
    let y : Expr [s, s, s] s := .var (.there .here)
    let z : Expr [s, s, s] s := .var (.there (.there .here))
    Expr.equality ring (.mul (.mul x y) z) (.mul x (.mul y z))
  | .mulComm =>
    let x : Expr [s, s] s := .var .here
    let y : Expr [s, s] s := .var (.there .here)
    Expr.equality ring (.mul x y) (.mul y x)
  | .oneMul =>
    let x : Expr [s] s := .var .here
    Expr.equality ring (.mul .one x) x
  | .mulAdd =>
    let x : Expr [s, s, s] s := .var .here
    let y : Expr [s, s, s] s := .var (.there .here)
    let z : Expr [s, s, s] s := .var (.there (.there .here))
    Expr.equality ring (.mul x (.add y z)) (.add (.mul x y) (.mul x z))

/-- The commutative ring reconstructed from the declared functions and satisfied Laws. -/
def commRing (ring : RingVocabulary sig s) (A : Structure sig)
    (h : ∀ name, (ring.law name).Holds A) : CommRing (A.carrier s) := by
  letI : Zero (A.carrier s) := ⟨ring.zeroValue A⟩
  letI : One (A.carrier s) := ⟨ring.oneValue A⟩
  letI : Add (A.carrier s) := ⟨ring.addValue A⟩
  letI : Neg (A.carrier s) := ⟨ring.negValue A⟩
  letI : Mul (A.carrier s) := ⟨ring.mulValue A⟩
  refine CommRing.ofMinimalAxioms ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b c
    exact (Expr.holds_equality_iff ring _ _ A).1 (h .addAssoc)
      (Assignment.cons a (Assignment.cons b (Assignment.cons c Assignment.empty)))
  · intro a
    exact (Expr.holds_equality_iff ring _ _ A).1 (h .zeroAdd) (Assignment.cons a Assignment.empty)
  · intro a
    exact (Expr.holds_equality_iff ring _ _ A).1 (h .negAdd) (Assignment.cons a Assignment.empty)
  · intro a b c
    exact (Expr.holds_equality_iff ring _ _ A).1 (h .mulAssoc)
      (Assignment.cons a (Assignment.cons b (Assignment.cons c Assignment.empty)))
  · intro a b
    exact (Expr.holds_equality_iff ring _ _ A).1 (h .mulComm)
      (Assignment.cons a (Assignment.cons b Assignment.empty))
  · intro a
    exact (Expr.holds_equality_iff ring _ _ A).1 (h .oneMul) (Assignment.cons a Assignment.empty)
  · intro a b c
    exact (Expr.holds_equality_iff ring _ _ A).1 (h .mulAdd)
      (Assignment.cons a (Assignment.cons b (Assignment.cons c Assignment.empty)))

end RingVocabulary

/-- An ordered equality of two terms whose common result sort may carry a ring. -/
structure RingEquation (sig : Signature.{u}) where
  /-- The Law's context. -/
  context : List sig.SortType
  /-- The sort at which the subtraction is taken. -/
  result : sig.SortType
  /-- The ring symbols and associated Laws of the result sort. -/
  ring : RingVocabulary sig result
  /-- The designated inputs. -/
  input : Formula sig context
  /-- First term in the ordered equality. -/
  left : Term sig context result
  /-- Second term in the ordered equality. -/
  right : Term sig context result

namespace RingEquation

variable {sig : Signature.{u}}

/-- Form the Law whose conclusion is the expanded equality of the ordered terms. -/
def toLaw (eqn : RingEquation sig) : Law sig :=
  ⟨eqn.context, eqn.input, Formula.termEq eqn.left eqn.right⟩

/-- The set `J` of designated inputs at which both terms are defined. -/
def jointInputs (eqn : RingEquation sig) (A : Structure sig) :
    Set (Assignment A.carrier eqn.context) :=
  eqn.toLaw.inputSet A ∩ (eqn.left.domain A ∩ eqn.right.domain A)

/-- The first evaluated term on the joint input set. -/
noncomputable def leftValue (eqn : RingEquation sig) (A : Structure sig)
    (e : eqn.jointInputs A) : A.carrier eqn.result :=
  (eqn.left.eval A e.val).get ((eqn.left.mem_domain_iff A e.val).1 e.property.2.1)

/-- The second evaluated term on the joint input set. -/
noncomputable def rightValue (eqn : RingEquation sig) (A : Structure sig)
    (e : eqn.jointInputs A) : A.carrier eqn.result :=
  (eqn.right.eval A e.val).get ((eqn.right.mem_domain_iff A e.val).1 e.property.2.2)

/-- The residual (1.6) in the order declared by the equality. -/
noncomputable def residual (eqn : RingEquation sig) (A : Structure sig)
    (ringLaws : ∀ name, (eqn.ring.law name).Holds A) (e : eqn.jointInputs A) :
    A.carrier eqn.result :=
  letI := eqn.ring.commRing A ringLaws
  eqn.leftValue A e - eqn.rightValue A e

/-- Subtraction in the reconstructed ring uses the declared addition and inverse. -/
theorem residual_eq_add_neg (eqn : RingEquation sig) (A : Structure sig)
    (ringLaws : ∀ name, (eqn.ring.law name).Holds A) (e : eqn.jointInputs A) :
    eqn.residual A ringLaws e =
      eqn.ring.addValue A (eqn.leftValue A e) (eqn.ring.negValue A (eqn.rightValue A e)) :=
  rfl

/-- The evaluated left value belongs to the left term's partial value. -/
theorem leftValue_mem (eqn : RingEquation sig) (A : Structure sig) (e : eqn.jointInputs A) :
    eqn.leftValue A e ∈ eqn.left.eval A e.val := ⟨_, rfl⟩

/-- The evaluated right value belongs to the right term's partial value. -/
theorem rightValue_mem (eqn : RingEquation sig) (A : Structure sig) (e : eqn.jointInputs A) :
    eqn.rightValue A e ∈ eqn.right.eval A e.val := ⟨_, rfl⟩

/-- On a joint input the residual is zero precisely when the evaluated terms agree. -/
theorem residual_zero_iff_values (eqn : RingEquation sig) (A : Structure sig)
    (ringLaws : ∀ name, (eqn.ring.law name).Holds A) (e : eqn.jointInputs A) :
    eqn.residual A ringLaws e = eqn.ring.zeroValue A ↔ eqn.leftValue A e = eqn.rightValue A e := by
  letI := eqn.ring.commRing A ringLaws
  change eqn.leftValue A e - eqn.rightValue A e = 0 ↔ _
  exact sub_eq_zero

/-- At each joint input, equality satisfaction is equivalent to zero residual in the declared ring. -/
theorem holds_at_iff_residual_zero (eqn : RingEquation sig) (A : Structure sig)
    (ringLaws : ∀ name, (eqn.ring.law name).Holds A) (e : eqn.jointInputs A) :
    eqn.toLaw.conclusion.Holds A e.val ↔ eqn.residual A ringLaws e = eqn.ring.zeroValue A := by
  rw [residual_zero_iff_values]
  change (Formula.termEq eqn.left eqn.right).Holds A e.val ↔ _
  rw [Formula.holds_termEq]
  constructor
  · rintro ⟨value, hleft, hright⟩
    exact (Part.mem_unique (eqn.leftValue_mem A e) hleft).trans
      (Part.mem_unique hright (eqn.rightValue_mem A e))
  · intro heq
    exact ⟨eqn.leftValue A e, eqn.leftValue_mem A e, heq.symm ▸ eqn.rightValue_mem A e⟩

/-- A ring-valued equality Law requires totality on the input set and a zero residual. -/
theorem holds_iff_jointInputs_and_residual_zero (eqn : RingEquation sig)
    (A : Structure sig) (ringLaws : ∀ name, (eqn.ring.law name).Holds A) :
    eqn.toLaw.Holds A ↔ eqn.jointInputs A = eqn.toLaw.inputSet A ∧
      ∀ e : eqn.jointInputs A, eqn.residual A ringLaws e = eqn.ring.zeroValue A := by
  constructor
  · intro h
    constructor
    · apply Set.Subset.antisymm
      · exact fun _ he => he.1
      · intro e he
        obtain ⟨value, hleft, hright⟩ :=
          (Formula.holds_termEq eqn.left eqn.right A e).1 (h e he)
        exact ⟨he, (eqn.left.mem_domain_iff A e).2 hleft.choose,
          (eqn.right.mem_domain_iff A e).2 hright.choose⟩
    · intro e
      exact (eqn.holds_at_iff_residual_zero A ringLaws e).1 (h e.val e.property.1)
  · rintro ⟨hjoint, hzero⟩ e he
    let x : eqn.jointInputs A := ⟨e, hjoint.symm ▸ he⟩
    exact (eqn.holds_at_iff_residual_zero A ringLaws x).2 (hzero x)

end RingEquation

end SHIGURE
