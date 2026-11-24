import Formal.SHIGURE.Part1.Models
import Mathlib.CategoryTheory.EssentialImage

/-! # Chapter 2 examples -/

namespace SHIGURE

open CategoryTheory

namespace Chapter2.IdempotentSwap

/-- One sort and one unary total operation. -/
def signature : Signature.{0} where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[()], ()⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- The unary signature with no required Laws. -/
def unrestricted : Theory.{0} := ⟨signature, Empty, fun n => nomatch n⟩

/-- The structure in which the unary function exchanges the two points. -/
def swap : Structure signature where
  carrier _ := Bool
  total _ xs := !(xs .here)
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

private def f (t : Term signature [()] ()) : Term signature [()] () :=
  .app (.total ()) (t.argsCons Term.argsNil)

/-- The Law requiring two applications to equal one application. -/
def idempotence : Law signature :=
  Law.equality (f (f (.var .here))) (f (.var .here))

/-- The extension requiring the operation to be idempotent. -/
def extended : LawExtension unrestricted :=
  ⟨Unit, fun _ => idempotence, fun n => nomatch n⟩

/-- The two-point swap is a model of the unrestricted theory. -/
def swapModel : Model unrestricted := ⟨swap, fun n => nomatch n⟩

private theorem applies_swap {t : Term signature [()] ()} {xs : Assignment swap.carrier [()]}
    {y : Bool} (evaluated : t.Evaluates swap xs y) : (f t).Evaluates swap xs (!y) := by
  apply (Term.evaluates_app_iff _ _ _ _ _).2
  refine ⟨Assignment.cons y Assignment.empty, ?_, (swap.graph_total_iff _ _ _).2 rfl⟩
  intro s i
  cases i with
  | here => exact evaluated
  | there i => exact nomatch i

/-- The two-point swap does not satisfy the added idempotence Law. -/
theorem swap_fails_idempotence : ¬ idempotence.Holds swap := by
  intro law
  let xs : Assignment swap.carrier [()] := Assignment.cons false Assignment.empty
  have variable_value : (Term.var (sig := signature) (Γ := [()]) .here).Evaluates swap xs false := by
    exact (Term.evaluates_var_iff _ _ _ _).2 rfl
  have first := applies_swap variable_value
  have second := applies_swap first
  obtain ⟨y, left, right⟩ := (Formula.holds_termEq _ _ swap xs).1 (law xs True.intro)
  have equalLeft := (f (f (.var .here))).evaluates_unique swap xs ((Term.mem_eval_iff _ _ _ _).1 left) second
  have equalRight := (f (.var .here)).evaluates_unique swap xs ((Term.mem_eval_iff _ _ _ _).1 right) first
  have impossible := equalLeft.symm.trans equalRight
  cases impossible

/-- The two-point swap is outside the essential image of the forgetful functor. -/
theorem swap_not_mem_essImage : ¬ extended.forget.essImage swapModel := by
  rintro ⟨A, ⟨e⟩⟩
  let underlying := unrestricted.modelProperty.ι.mapIso e
  exact swap_fails_idempotence (Structure.law_holds_of_iso underlying (A.property ()))

/-- Proposition 2.3's forgetful functor can fail to be essentially surjective. -/
theorem forget_not_essSurj : ¬ extended.forget.EssSurj :=
  fun h => swap_not_mem_essImage (h.mem_essImage swapModel)

end Chapter2.IdempotentSwap

end SHIGURE
