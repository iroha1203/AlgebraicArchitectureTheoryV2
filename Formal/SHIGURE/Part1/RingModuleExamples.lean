import Formal.SHIGURE.Part1.RingEquations
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Int.Defs

/-! # Commutative rings with a module, Example 1.6

The scalar sort and the module sort have distinct addition and zero symbols.
The scalar action is a total operation with one argument of each sort.
-/

namespace SHIGURE.Chapter1.RingModule

/-- The two sorts of the ring and module language. -/
inductive SortName
  | scalar
  | vector

/-- The named operations of the two-sorted ring and module language. -/
inductive Symbol
  | scalarZero
  | scalarOne
  | scalarAdd
  | scalarNeg
  | scalarMul
  | vectorZero
  | vectorAdd
  | vectorNeg
  | action

private def signatureWithPartial (P : Type) : Signature where
  SortType := SortName
  Total := Symbol
  Rel := Empty
  Partial := P
  Quantity := Empty
  totalArity
    | .scalarZero => ⟨[], .scalar⟩
    | .scalarOne => ⟨[], .scalar⟩
    | .scalarAdd => ⟨[.scalar, .scalar], .scalar⟩
    | .scalarNeg => ⟨[.scalar], .scalar⟩
    | .scalarMul => ⟨[.scalar, .scalar], .scalar⟩
    | .vectorZero => ⟨[], .vector⟩
    | .vectorAdd => ⟨[.vector, .vector], .vector⟩
    | .vectorNeg => ⟨[.vector], .vector⟩
    | .action => ⟨[.scalar, .vector], .vector⟩
  relInputs := fun r => nomatch r
  partialArity := fun _ => ⟨[.scalar], .scalar⟩
  quantityArity := fun q => nomatch q

/-- The sort profiles of the operations in Example 1.6. -/
def signature : Signature := signatureWithPartial Empty

private def scalarVocabularyFor (P : Type) : RingVocabulary (signatureWithPartial P) .scalar where
  zero := ⟨.ordinary Symbol.scalarZero, rfl⟩
  one := ⟨.ordinary Symbol.scalarOne, rfl⟩
  add := ⟨.ordinary Symbol.scalarAdd, rfl⟩
  neg := ⟨.ordinary Symbol.scalarNeg, rfl⟩
  mul := ⟨.ordinary Symbol.scalarMul, rfl⟩

/-- The scalar ring vocabulary of the ring and module signature. -/
def scalarVocabulary : RingVocabulary signature .scalar := scalarVocabularyFor Empty

/-- Every operation of this algebraic signature is total. -/
instance : IsEmpty signature.Partial := ⟨fun p => nomatch p⟩

variable {Γ : List SortName}

/-- The scalar zero term. -/
def scalarZero : Term signature Γ .scalar :=
  Term.app (sig := signature) (.total Symbol.scalarZero) (@Term.argsNil signature Γ)

/-- The scalar unit term. -/
def scalarOne : Term signature Γ .scalar :=
  Term.app (sig := signature) (.total Symbol.scalarOne) (@Term.argsNil signature Γ)

/-- Scalar addition as a term operation. -/
def scalarAdd (a b : Term signature Γ .scalar) : Term signature Γ .scalar :=
  Term.app (sig := signature) (.total Symbol.scalarAdd) (a.argsCons (b.argsCons Term.argsNil))

/-- Scalar additive inverse as a term operation. -/
def scalarNeg (a : Term signature Γ .scalar) : Term signature Γ .scalar :=
  Term.app (sig := signature) (.total Symbol.scalarNeg) (a.argsCons Term.argsNil)

/-- Scalar multiplication as a term operation. -/
def scalarMul (a b : Term signature Γ .scalar) : Term signature Γ .scalar :=
  Term.app (sig := signature) (.total Symbol.scalarMul) (a.argsCons (b.argsCons Term.argsNil))

/-- The zero term of the module sort. -/
def vectorZero : Term signature Γ .vector :=
  Term.app (sig := signature) (.total Symbol.vectorZero) (@Term.argsNil signature Γ)

/-- Addition of module terms. -/
def vectorAdd (a b : Term signature Γ .vector) : Term signature Γ .vector :=
  Term.app (sig := signature) (.total Symbol.vectorAdd) (a.argsCons (b.argsCons Term.argsNil))

/-- Additive inverse of a module term. -/
def vectorNeg (a : Term signature Γ .vector) : Term signature Γ .vector :=
  Term.app (sig := signature) (.total Symbol.vectorNeg) (a.argsCons Term.argsNil)

/-- Apply the action of a scalar term to a module term. -/
def action (a : Term signature Γ .scalar) (v : Term signature Γ .vector) :
    Term signature Γ .vector :=
  Term.app (sig := signature) (.total Symbol.action) (a.argsCons (v.argsCons Term.argsNil))

/-- Associativity at any of the two sorts. -/
private def associative {s : SortName}
    (op : ∀ {Γ : List SortName}, Term signature Γ s → Term signature Γ s → Term signature Γ s) :
    Law signature :=
  let x : Term signature [s, s, s] s := .var .here
  let y : Term signature [s, s, s] s := .var (.there .here)
  let z : Term signature [s, s, s] s := .var (.there (.there .here))
  Law.equality (op (op x y) z) (op x (op y z))

/-- Commutativity at either sort. -/
private def commutative {s : SortName}
    (op : ∀ {Γ : List SortName}, Term signature Γ s → Term signature Γ s → Term signature Γ s) :
    Law signature :=
  let x : Term signature [s, s] s := .var .here
  let y : Term signature [s, s] s := .var (.there .here)
  Law.equality (op x y) (op y x)

/-- An equation asserting a left unit for a binary operation. -/
private def leftUnit {s : SortName}
    (op : ∀ {Γ : List SortName}, Term signature Γ s → Term signature Γ s → Term signature Γ s)
    (unit : ∀ {Γ : List SortName}, Term signature Γ s) : Law signature :=
  let x : Term signature [s] s := .var .here
  Law.equality (op unit x) x

/-- An equation asserting a left inverse for addition. -/
private def leftInverse {s : SortName}
    (add : ∀ {Γ : List SortName}, Term signature Γ s → Term signature Γ s → Term signature Γ s)
    (neg : ∀ {Γ : List SortName}, Term signature Γ s → Term signature Γ s)
    (zero : ∀ {Γ : List SortName}, Term signature Γ s) : Law signature :=
  let x : Term signature [s] s := .var .here
  Law.equality (add (neg x) x) zero

/-- The required equations for a commutative ring and a module over it. -/
inductive LawName
  | scalarAddAssoc | scalarAddComm | scalarZeroAdd | scalarNegAdd
  | scalarMulAssoc | scalarMulComm | scalarOneMul | scalarMulAdd
  | vectorAddAssoc | vectorAddComm | vectorZeroAdd | vectorNegAdd
  | actionAssoc | actionUnit | actionVectorAdd | actionScalarAdd

/-- The named equations of the ring and module theory. -/
def law : LawName → Law signature
  | .scalarAddAssoc => associative scalarAdd
  | .scalarAddComm => commutative scalarAdd
  | .scalarZeroAdd => leftUnit scalarAdd scalarZero
  | .scalarNegAdd => leftInverse scalarAdd scalarNeg scalarZero
  | .scalarMulAssoc => associative scalarMul
  | .scalarMulComm => commutative scalarMul
  | .scalarOneMul => leftUnit scalarMul scalarOne
  | .scalarMulAdd =>
    let x : Term signature [.scalar, .scalar, .scalar] .scalar := .var .here
    let y : Term signature [.scalar, .scalar, .scalar] .scalar := .var (.there .here)
    let z : Term signature [.scalar, .scalar, .scalar] .scalar := .var (.there (.there .here))
    Law.equality (scalarMul x (scalarAdd y z)) (scalarAdd (scalarMul x y) (scalarMul x z))
  | .vectorAddAssoc => associative vectorAdd
  | .vectorAddComm => commutative vectorAdd
  | .vectorZeroAdd => leftUnit vectorAdd vectorZero
  | .vectorNegAdd => leftInverse vectorAdd vectorNeg vectorZero
  | .actionAssoc =>
    let a : Term signature [.scalar, .scalar, .vector] .scalar := .var .here
    let b : Term signature [.scalar, .scalar, .vector] .scalar := .var (.there .here)
    let x : Term signature [.scalar, .scalar, .vector] .vector := .var (.there (.there .here))
    Law.equality (action (scalarMul a b) x) (action a (action b x))
  | .actionUnit =>
    let x : Term signature [.vector] .vector := .var .here
    Law.equality (action scalarOne x) x
  | .actionVectorAdd =>
    let a : Term signature [.scalar, .vector, .vector] .scalar := .var .here
    let x : Term signature [.scalar, .vector, .vector] .vector := .var (.there .here)
    let y : Term signature [.scalar, .vector, .vector] .vector := .var (.there (.there .here))
    Law.equality (action a (vectorAdd x y)) (vectorAdd (action a x) (action a y))
  | .actionScalarAdd =>
    let a : Term signature [.scalar, .scalar, .vector] .scalar := .var .here
    let b : Term signature [.scalar, .scalar, .vector] .scalar := .var (.there .here)
    let x : Term signature [.scalar, .scalar, .vector] .vector := .var (.there (.there .here))
    Law.equality (action (scalarAdd a b) x) (vectorAdd (action a x) (action b x))

/-- The two-sorted theory of Example 1.6. -/
def theory : Theory where
  signature := signature
  LawName := LawName
  law := law

private abbrev carrier (R M : Type) : SortName → Type
  | .scalar => R
  | .vector => M

private def total (P R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    (f : Symbol) → Assignment (carrier R M) ((signatureWithPartial P).totalArity f).inputs →
      carrier R M ((signatureWithPartial P).totalArity f).output
  | .scalarZero => fun _ => (0 : R)
  | .scalarOne => fun _ => (1 : R)
  | .scalarAdd => fun xs => (xs .here : R) + (xs (.there .here) : R)
  | .scalarNeg => fun xs => -(xs .here : R)
  | .scalarMul => fun xs => (xs .here : R) * (xs (.there .here) : R)
  | .vectorZero => fun _ => (0 : M)
  | .vectorAdd => fun xs => (xs .here : M) + (xs (.there .here) : M)
  | .vectorNeg => fun xs => -(xs .here : M)
  | .action => fun xs => (xs .here : R) • (xs (.there .here) : M)

/-- Interpret the operation symbols using an actual mathlib commutative ring and module. -/
def realization (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Structure signature where
  carrier := carrier R M
  total := total Empty R M
  relation := fun r => nomatch r
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := fun q => nomatch q

section TotalValues

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
variable (e : Assignment (realization R M).carrier Γ)

/-- Evaluation of the `scalarZero` term in the standard realization. -/
@[simp] theorem totalValue_scalarZero :
    (scalarZero).totalValue (realization R M) e =
      (0 : R) := rfl

/-- Evaluation of the `scalarOne` term in the standard realization. -/
@[simp] theorem totalValue_scalarOne :
    (scalarOne).totalValue (realization R M) e =
      (1 : R) := rfl

/-- Evaluation of the `scalarAdd` term in the standard realization. -/
@[simp] theorem totalValue_scalarAdd (a b : Term signature Γ .scalar) :
    (scalarAdd a b).totalValue (realization R M) e =
      @Add.add R _ (a.totalValue (realization R M) e) (b.totalValue (realization R M) e) := rfl

/-- Evaluation of the `scalarNeg` term in the standard realization. -/
@[simp] theorem totalValue_scalarNeg (a : Term signature Γ .scalar) :
    (scalarNeg a).totalValue (realization R M) e =
      @Neg.neg R _ (a.totalValue (realization R M) e) := rfl

/-- Evaluation of the `scalarMul` term in the standard realization. -/
@[simp] theorem totalValue_scalarMul (a b : Term signature Γ .scalar) :
    (scalarMul a b).totalValue (realization R M) e =
      @Mul.mul R _ (a.totalValue (realization R M) e) (b.totalValue (realization R M) e) := rfl

/-- Evaluation of the `vectorZero` term in the standard realization. -/
@[simp] theorem totalValue_vectorZero :
    (vectorZero).totalValue (realization R M) e =
      (0 : M) := rfl

/-- Evaluation of the `vectorAdd` term in the standard realization. -/
@[simp] theorem totalValue_vectorAdd (a b : Term signature Γ .vector) :
    (vectorAdd a b).totalValue (realization R M) e =
      @Add.add M _ (a.totalValue (realization R M) e) (b.totalValue (realization R M) e) := rfl

/-- Evaluation of the `vectorNeg` term in the standard realization. -/
@[simp] theorem totalValue_vectorNeg (a : Term signature Γ .vector) :
    (vectorNeg a).totalValue (realization R M) e =
      @Neg.neg M _ (a.totalValue (realization R M) e) := rfl

/-- Evaluation of the `action` term in the standard realization. -/
@[simp] theorem totalValue_action (a : Term signature Γ .scalar) (v : Term signature Γ .vector) :
    (action a v).totalValue (realization R M) e =
      @SMul.smul R M _ (a.totalValue (realization R M) e) (v.totalValue (realization R M) e) := rfl

end TotalValues


/-- Standard ring and module operations satisfy every named equation. -/
theorem realization_holds (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    theory.Holds (realization R M) := by
  intro name
  cases name <;> apply (Law.holds_equality_totalValue_iff _ _ (realization R M)).2 <;> intro e
  · exact @add_assoc R _ (e .here) (e (.there .here)) (e (.there (.there .here)))
  · exact @add_comm R _ (e .here) (e (.there .here))
  · exact @zero_add R _ (e .here)
  · exact @neg_add_cancel R _ (e .here)
  · exact @mul_assoc R _ (e .here) (e (.there .here)) (e (.there (.there .here)))
  · exact @mul_comm R _ (e .here) (e (.there .here))
  · exact @one_mul R _ (e .here)
  · exact @mul_add R _ _ _ (e .here) (e (.there .here)) (e (.there (.there .here)))
  · exact @add_assoc M _ (e .here) (e (.there .here)) (e (.there (.there .here)))
  · exact @add_comm M _ (e .here) (e (.there .here))
  · exact @zero_add M _ (e .here)
  · exact @neg_add_cancel M _ (e .here)
  · exact @mul_smul R M _ _ (e .here) (e (.there .here)) (e (.there (.there .here)))
  · exact @one_smul R M _ _ (e .here)
  · exact @smul_add R M _ _ (e .here) (e (.there .here)) (e (.there (.there .here)))
  · exact @add_smul R M _ _ _ (e .here) (e (.there .here)) (e (.there (.there .here)))

/-- The integer realization with the scalar zero symbol reassigned to one. -/
def wrongZero : Structure signature :=
  { realization Int Int with
    total := fun f => match f with
      | .scalarZero => fun _ => (1 : Int)
      | other => (realization Int Int).total other }

/-- The altered structure fails the scalar additive identity Law at zero. -/
theorem wrongZero_not_model : ¬ theory.Holds wrongZero := by
  intro h
  have zeroLaw := (Law.holds_equality_totalValue_iff _ _ wrongZero).1 (h LawName.scalarZeroAdd)
  let e : Assignment wrongZero.carrier [.scalar] := Assignment.cons (0 : Int) Assignment.empty
  have bad := zeroLaw e
  change (1 : Int) + 0 = 0 at bad
  exact (by decide : (1 : Int) + 0 ≠ 0) bad

private theorem scalarLaws (P R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (A : Structure (signatureWithPartial P))
    (hCarrier : A.carrier = carrier R M) (hTotal : hCarrier ▸ A.total = total P R M) :
    ∀ name, ((scalarVocabularyFor P).law name).Holds A := by
  cases A with
  | mk carrierA totalA rel domain partialValue quantity =>
    dsimp at hCarrier
    subst carrierA
    dsimp at hTotal
    subst totalA
    intro name
    cases name <;> apply (RingVocabulary.Expr.holds_equality_iff _ _ _ _).2 <;> intro e
    · exact @add_assoc R _ (e .here) (e (.there .here)) (e (.there (.there .here)))
    · exact @zero_add R _ (e .here)
    · exact @neg_add_cancel R _ (e .here)
    · exact @mul_assoc R _ (e .here) (e (.there .here)) (e (.there (.there .here)))
    · exact @mul_comm R _ (e .here) (e (.there .here))
    · exact @one_mul R _ (e .here)
    · exact @mul_add R _ _ _ (e .here) (e (.there .here)) (e (.there (.there .here)))

/-- The declared scalar ring Laws hold in the standard realization. -/
theorem realization_scalarLaws (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    ∀ name, (scalarVocabulary.law name).Holds (realization R M) :=
  scalarLaws Empty R M _ rfl rfl

/-- Extend the language by a unary scalar operation defined at zero. -/
def partialSignature : Signature := signatureWithPartial Unit

/-- The integer realization with a partial identity at zero. -/
def partialInteger : Structure partialSignature where
  carrier := carrier Int Int
  total := total Unit Int Int
  relation := fun r => nomatch r
  partialDomain := fun _ => {xs | xs.head = (0 : Int)}
  partialValue := fun _ x => x.val.head
  quantity := fun q => nomatch q

private def zeroOnlyArgs {s : SortName} (i : Var [.scalar] s) :
    Term partialSignature [.scalar] s :=
  match i with
  | .here => .var .here
  | .there previous => nomatch previous

private def zeroOnly : RingEquation partialSignature where
  context := [.scalar]
  input := .truth
  result := .scalar
  ring := scalarVocabularyFor Unit
  left := Term.app (sig := partialSignature) (.partialOp ()) zeroOnlyArgs
  right := .var .here

private theorem zeroOnly_evaluates (e : Assignment partialInteger.carrier [.scalar]) (y : Int) :
    zeroOnly.left.Evaluates partialInteger e y ↔ e.head = (0 : Int) ∧ e.head = y := by
  have hArgs : ∀ {s} (i : Var [SortName.scalar] s),
      (zeroOnlyArgs i).Evaluates partialInteger e (e i) := by
    intro s i
    cases i with
    | here => rfl
    | there previous => nomatch previous
  refine (Term.evaluates_app_at (sig := partialSignature) (.partialOp ())
    zeroOnlyArgs partialInteger e e hArgs y).trans ?_
  rw [partialInteger.graph_partial_iff]
  exact ⟨fun ⟨hd, hv⟩ => ⟨hd, hv⟩, fun ⟨hd, hv⟩ => ⟨hd, hv⟩⟩

/-- The partially defined equation has a joint input at zero. -/
theorem zeroOnly_joint_nonempty : (zeroOnly.jointInputs partialInteger).Nonempty := by
  let e : Assignment partialInteger.carrier [.scalar] := Assignment.cons (0 : Int) Assignment.empty
  exact ⟨e, True.intro, ⟨(0 : Int), (zeroOnly_evaluates e 0).2 ⟨rfl, rfl⟩⟩, ⟨(0 : Int), rfl⟩⟩

/-- The residual vanishes on its joint inputs, while at one the Law's input condition alone holds. -/
theorem zeroOnly_residual_and_missing_input :
    (∀ e : zeroOnly.jointInputs partialInteger,
      zeroOnly.residual partialInteger (scalarLaws Unit Int Int _ rfl rfl) e =
        zeroOnly.ring.zeroValue partialInteger) ∧
    zeroOnly.jointInputs partialInteger ≠ zeroOnly.toLaw.inputSet partialInteger := by
  constructor
  · intro e
    apply (zeroOnly.holds_at_iff_residual_zero partialInteger _ e).1
    apply (Formula.holds_termEq _ _ _ _).2
    obtain ⟨y, hy⟩ := e.property.2.1
    exact ⟨y, (Term.mem_eval_iff _ _ _ _).2 hy,
      (Term.mem_eval_iff _ _ _ _).2 ((zeroOnly_evaluates e.val y).1 hy).2⟩
  · intro same
    let e : Assignment partialInteger.carrier [.scalar] :=
      Assignment.cons (1 : Int) Assignment.empty
    have joint : e ∈ zeroOnly.jointInputs partialInteger := same ▸ (True.intro :
      e ∈ zeroOnly.toLaw.inputSet partialInteger)
    obtain ⟨y, hy⟩ := joint.2.1
    exact (by decide : (1 : Int) ≠ 0) ((zeroOnly_evaluates e y).1 hy).1

private def oneEqualsZero {sig : Signature} {s : sig.SortType} (ring : RingVocabulary sig s) :
    RingEquation sig where
  context := []
  input := .truth
  result := s
  ring := ring
  left := ring.one.term Term.argsNil
  right := ring.zero.term Term.argsNil

private theorem oneEqualsZero_residual {sig : Signature} {s : sig.SortType}
    (ring : RingVocabulary sig s) (A : Structure sig)
    (h : ∀ name, (ring.law name).Holds A) :
    (oneEqualsZero ring).jointInputs A = (oneEqualsZero ring).toLaw.inputSet A ∧
    ∃ e : (oneEqualsZero ring).jointInputs A,
      (oneEqualsZero ring).residual A h e = ring.addValue A (ring.oneValue A)
        (ring.negValue A (ring.zeroValue A)) := by
  have evalOne (e : Assignment A.carrier []) :
      (oneEqualsZero ring).left.Evaluates A e (ring.oneValue A) :=
    ring.one.evaluates_term Term.argsNil A e Assignment.empty (fun i => nomatch i)
  have evalZero (e : Assignment A.carrier []) :
      (oneEqualsZero ring).right.Evaluates A e (ring.zeroValue A) :=
    ring.zero.evaluates_term Term.argsNil A e Assignment.empty (fun i => nomatch i)
  have joint (e : Assignment A.carrier []) : e ∈ (oneEqualsZero ring).jointInputs A :=
    ⟨True.intro, ⟨ring.oneValue A, evalOne e⟩, ⟨ring.zeroValue A, evalZero e⟩⟩
  refine ⟨Set.Subset.antisymm (fun _ he => he.1) (fun e _ => joint e), ?_⟩
  let e : (oneEqualsZero ring).jointInputs A := ⟨Assignment.empty, joint Assignment.empty⟩
  have left : (oneEqualsZero ring).leftValue A e = ring.oneValue A :=
    Part.mem_unique ((oneEqualsZero ring).leftValue_mem A e)
      ((Term.mem_eval_iff _ _ _ _).2 (evalOne e.val))
  have right : (oneEqualsZero ring).rightValue A e = ring.zeroValue A :=
    Part.mem_unique ((oneEqualsZero ring).rightValue_mem A e)
      ((Term.mem_eval_iff _ _ _ _).2 (evalZero e.val))
  refine ⟨e, ?_⟩
  rw [RingEquation.residual_eq_add_neg, left, right]
  rfl

/-- Both closed terms are defined on the full input set, but the ordered residual is one. -/
theorem oneEqualsZero_total_nonzero :
    (oneEqualsZero scalarVocabulary).jointInputs (realization Int Int) =
      (oneEqualsZero scalarVocabulary).toLaw.inputSet (realization Int Int) ∧
    ∃ e : (oneEqualsZero scalarVocabulary).jointInputs (realization Int Int),
      (oneEqualsZero scalarVocabulary).residual (realization Int Int)
        (realization_scalarLaws Int Int) e = (1 : Int) :=
  oneEqualsZero_residual scalarVocabulary (realization Int Int) (realization_scalarLaws Int Int)

private def quantitySignature : Signature :=
  { signature with
    Total := Empty
    totalArity := fun f => nomatch f
    Quantity := Symbol
    quantityArity := signature.totalArity }

private def quantityInteger : Structure quantitySignature where
  carrier := carrier Int Int
  total := fun f => nomatch f
  relation := fun r => nomatch r
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := total Empty Int Int

private def quantityVocabulary : RingVocabulary quantitySignature .scalar where
  zero := ⟨.quantity Symbol.scalarZero, rfl⟩
  one := ⟨.quantity Symbol.scalarOne, rfl⟩
  add := ⟨.quantity Symbol.scalarAdd, rfl⟩
  neg := ⟨.quantity Symbol.scalarNeg, rfl⟩
  mul := ⟨.quantity Symbol.scalarMul, rfl⟩

private theorem quantityLaws : ∀ name, (quantityVocabulary.law name).Holds quantityInteger := by
  have laws := realization_scalarLaws Int Int
  intro name
  cases name <;> apply (RingVocabulary.Expr.holds_equality_iff _ _ _ _).2 <;> intro e
  · exact (RingVocabulary.Expr.holds_equality_iff _ _ _ _).1 (laws .addAssoc) e
  · exact (RingVocabulary.Expr.holds_equality_iff _ _ _ _).1 (laws .zeroAdd) e
  · exact (RingVocabulary.Expr.holds_equality_iff _ _ _ _).1 (laws .negAdd) e
  · exact (RingVocabulary.Expr.holds_equality_iff _ _ _ _).1 (laws .mulAssoc) e
  · exact (RingVocabulary.Expr.holds_equality_iff _ _ _ _).1 (laws .mulComm) e
  · exact (RingVocabulary.Expr.holds_equality_iff _ _ _ _).1 (laws .oneMul) e
  · exact (RingVocabulary.Expr.holds_equality_iff _ _ _ _).1 (laws .mulAdd) e

/-- The ordered residual is also one when every ring operation is declared as a quantity. -/
theorem quantity_oneEqualsZero_total_nonzero :
    (oneEqualsZero quantityVocabulary).jointInputs quantityInteger =
      (oneEqualsZero quantityVocabulary).toLaw.inputSet quantityInteger ∧
    ∃ e : (oneEqualsZero quantityVocabulary).jointInputs quantityInteger,
      (oneEqualsZero quantityVocabulary).residual quantityInteger quantityLaws e = (1 : Int) :=
  oneEqualsZero_residual quantityVocabulary quantityInteger quantityLaws

end SHIGURE.Chapter1.RingModule
