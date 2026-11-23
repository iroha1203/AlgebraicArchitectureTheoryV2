import Formal.SHIGURE.Part1.Laws
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

/-- The sort profile of each operation in Example 1.6. -/
def signature : Signature where
  SortType := SortName
  Total := Symbol
  Rel := Empty
  Partial := Empty
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
  partialArity := fun p => nomatch p
  quantityArity := fun q => nomatch q

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

/-- Interpret the operation symbols using an actual mathlib commutative ring and module. -/
def realization (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Structure signature where
  carrier
    | .scalar => R
    | .vector => M
  total
    | .scalarZero => fun _ => (0 : R)
    | .scalarOne => fun _ => (1 : R)
    | .scalarAdd => fun xs => (xs .here : R) + (xs (.there .here) : R)
    | .scalarNeg => fun xs => -(xs .here : R)
    | .scalarMul => fun xs => (xs .here : R) * (xs (.there .here) : R)
    | .vectorZero => fun _ => (0 : M)
    | .vectorAdd => fun xs => (xs .here : M) + (xs (.there .here) : M)
    | .vectorNeg => fun xs => -(xs .here : M)
    | .action => fun xs => (xs .here : R) • (xs (.there .here) : M)
  relation := fun r => nomatch r
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := fun q => nomatch q

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

end SHIGURE.Chapter1.RingModule
