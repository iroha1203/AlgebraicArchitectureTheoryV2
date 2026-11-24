import Formal.SHIGURE.Part1.Chapter2Examples
import Formal.SHIGURE.Part1.InverseInterpretations
import Formal.SHIGURE.Part1.TotalModels

/-! # Witnesses for the model pullback and the total category

The syntactic comparison is exercised on a two-point model and rejects a
constant forward term whose two input values cannot be recovered. The
total-category example changes theory and composes noninvertible state
maps across the change.
-/

namespace SHIGURE.Chapter2.PullbackWitnesses

open CategoryTheory

/-- A single sort with no primitive symbols, used to isolate the two unary inverse sequents. -/
private def signature : Signature.{0} where
  SortType := Unit
  Total := Empty
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity x := nomatch x
  relInputs x := nomatch x
  partialArity x := nomatch x
  quantityArity x := nomatch x

/-- The theory on the bare carrier. -/
private def theory : Theory.{0} := ⟨signature, Empty, fun name => nomatch name⟩

/-- The variable is defined because its own position witnesses its value graph. -/
private def variableTotal {H : Theory.{0}} (s : H.signature.SortType) :
    Derivation H .truth (Term.var (Γ := [s]) Var.here).defined := by
  let var : Term H.signature [s] s := .var .here
  exact .cut (.eqRefl Var.here) (.existsIntro var.graph Var.here)

/-- Applying the identity unary term to the same variable returns that variable by derivation. -/
private def variableRoundTrip {H : Theory.{0}} (s : H.signature.SortType) :
    Derivation H .truth
      (Formula.termEq (Γ := [s]) ((Term.var Var.here).applyUnary (.var .here)) (.var .here)) := by
  let var : Term H.signature [s] s := .var .here
  let compared : Formula H.signature [s, s] := ((var.applyUnary var).graph).conj var.graph
  refine .cut ?_ (.existsIntro compared Var.here)
  let bound : Formula H.signature [s, s] :=
    Formula.conj (.atom (.eq (.there .here) .here)) (.atom (.eq .here (.there .here)))
  have strict : Derivation H .truth bound.ex :=
    .cut (.andIntro (.eqRefl Var.here) (.eqRefl Var.here)) (.existsIntro bound Var.here)
  exact .andIntro strict (.eqRefl Var.here)

/-- The identity interpretation composed with itself is compared by the two unary variables. -/
private noncomputable def comparison :
    Interpretation.SyntacticComparison ((Interpretation.identity theory).comp (Interpretation.identity theory)) where
  alpha _ := .var .here
  beta _ := .var .here
  alpha_total s := variableTotal s
  beta_total s := variableTotal s
  beta_alpha s := variableRoundTrip s
  alpha_beta s := variableRoundTrip s
  total f := nomatch f
  quantity q := nomatch q
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p

/-- This actual pair of syntactic comparisons constructs the claimed mathlib equivalence. -/
noncomputable def equivalentModels : Model theory ≌ Model theory :=
  Interpretation.modelEquivalence _ _ comparison comparison

/-- Give the bare sort an arbitrary specified carrier. -/
private def structureOn (X : Type) : Structure signature where
  carrier _ := X
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The two-point structure satisfies the theory with no required Laws. -/
private def booleanModel : Model theory := ⟨structureOn Bool, fun n => nomatch n⟩

/-- The forward component of the comparison recovers either of the two Boolean points. -/
theorem comparison_on_points (x : Bool) : comparison.alphaValue booleanModel () x = x :=
  Term.evaluates_unique _ _ _ (comparison.alpha_evaluates booleanModel () x)
    ((Term.evaluates_var_iff Var.here booleanModel.obj _ x).2 rfl)

/-- Add a required true sequent to the bare theory, so the cross-theory arrows have different bases. -/
private def markedTheory : Theory.{0} :=
  ⟨signature, Unit, fun _ => ⟨[], .truth, .truth⟩⟩

/-- The marked theory admits every carrier because its required sequent is true. -/
private def markedModel (X : Type) : Model markedTheory :=
  ⟨structureOn X, fun _ _ _ => True.intro⟩

/-- The identity name map views a marked model as a model for the original theory. -/
private def interpretMarked : Interpretation theory markedTheory where
  onSort := id
  translation := Translation.identity signature
  total f := nomatch f
  quantity q := nomatch q
  partialDefined p := nomatch p
  definedPartial p := nomatch p
  preserves n := nomatch n

/-- The change of theory collapses the two original states to the single marked state. -/
private noncomputable def cross :
    TotalModel.ofModel theory booleanModel ⟶ TotalModel.ofModel markedTheory (markedModel Unit) :=
  TotalModel.homMk (Theory.ofInterpretation interpretMarked) (ObjectProperty.homMk {
    onSort _ _ := ()
    total_comm f := nomatch f
    relation_mem r := nomatch r
    partial_mem p := nomatch p
    partial_comm p := nomatch p
    quantity_comm q := nomatch q })

/-- A marked state arrow sends the single state to the distinguished Boolean point. -/
private noncomputable def pickTrue :
    TotalModel.ofModel markedTheory (markedModel Unit) ⟶ TotalModel.ofModel markedTheory (markedModel Bool) :=
  TotalModel.homMk (𝟙 markedTheory) (ObjectProperty.homMk {
    onSort _ _ := true
    total_comm f := nomatch f
    relation_mem r := nomatch r
    partial_mem p := nomatch p
    partial_comm p := nomatch p
    quantity_comm q := nomatch q })

/-- Projection of the cross-theory composite retains its nontrivial base change. -/
theorem composed_base :
    TotalModel.projection.map (cross ≫ pickTrue) = Theory.ofInterpretation interpretMarked := by
  rw [Functor.map_comp]
  exact Category.comp_id _

/-- Equation (2.7) on the concrete composite first collapses and then selects the marked point. -/
theorem composed_state (x : Bool) :
    (TotalModel.state (cross ≫ pickTrue)).hom.onSort () x = true := by
  rw [TotalModel.state_comp, Model.comp_apply, Model.comp_apply, Model.eqToHom_apply]
  rfl

open Chapter2.IdempotentSwap in
/-- A two-point model whose only unary operation discards its input. -/
private def constantModel : Model unrestricted :=
  ⟨{ identityStructure with total := fun _ _ => false }, fun n => nomatch n⟩

/-- A constant unary comparison term cannot satisfy the inverse sequents in Corollary 2.4a(b). -/
theorem constant_term_cannot_compare :
    ¬ ∃ d : Interpretation.SyntacticComparison (Interpretation.identity Chapter2.IdempotentSwap.unrestricted),
      d.alpha () = Term.primitive (.total ()) := by
  rintro ⟨d, same⟩
  have collapses (x : Bool) : d.alphaValue constantModel () x = false := by
    apply Term.evaluates_unique _ _ _ (d.alpha_evaluates constantModel () x)
    rw [same]
    apply (Term.primitive_evaluates_iff _ _ _ _).2
    exact (constantModel.obj.graph_total_iff _ _ _).2 rfl
  exact Bool.noConfusion ((d.alpha_bijective constantModel ()).injective
    ((collapses false).trans (collapses true).symm))

end SHIGURE.Chapter2.PullbackWitnesses

namespace SHIGURE.Chapter2.InverseTermWitnesses

open CategoryTheory
open Chapter2.IdempotentSwap

/-- Use the only unary operation as the forward and inverse term. -/
private def unary : Term signature [()] () :=
  (Translation.identity signature).operation (.total ())

/-- A sorted family of the unary term on the one-sort signature. -/
private def unaryAt (s : signature.SortType) : Term signature [s] s := by
  cases s
  exact unary

/-- The required inverse sequent says that applying the unary term twice returns its input. -/
private def inverseFormula : Formula signature [()] :=
  Formula.termEq (unary.applyUnary unary) (.var .here)

/-- The required operation sequent says the chosen terms commute with the old unary operation. -/
private def operationFormula : Formula signature [()] :=
  Formula.termEq (unary.applyUnary (Term.primitive (.total ())))
    (unary.applyStrict fun i => Interpretation.comparisonArguments (H := unrestricted) id unaryAt [()] i)

/-- A theory with the two written sequents needed by the nonidentity unary comparison. -/
private def involutive : Theory.{0} where
  signature := signature
  LawName := Bool
  law
    | false => ⟨[()], .truth, inverseFormula⟩
    | true => ⟨[()], .truth, operationFormula⟩

/-- The replacement term of the identity interpretation acts as the swap at every assignment. -/
private theorem unary_evaluates (xs : Assignment swap.carrier [()]) :
    unary.Evaluates swap xs (!(xs .here)) := by
  refine (Term.evaluates_app_iff (.total ()) _ swap xs _).2
    ⟨xs, ?_, (swap.graph_total_iff () xs _).2 rfl⟩
  intro s i
  cases i with
  | here => exact (Term.evaluates_var_iff Var.here swap xs _).2 rfl
  | there i => exact nomatch i

/-- Evaluating the same unary term again on the swap value recovers the input. -/
private theorem unary_evaluates_twice (xs : Assignment swap.carrier [()]) :
    unary.Evaluates swap (Assignment.cons (!(xs .here)) Assignment.empty) (xs .here) := by
  simpa only [Assignment.cons_here, Bool.not_not] using
    unary_evaluates (Assignment.cons (!(xs .here)) Assignment.empty)

/-- The swap on two points satisfies both comparison sequents. -/
private def involutiveModel : Model involutive := by
  refine ⟨swap, ?_⟩
  intro name
  cases name
  · intro xs _
    have twice := unary_evaluates_twice xs
    have evaluated := (Term.evaluates_applyUnary_iff unary unary swap xs _ (unary_evaluates xs) _).2 twice
    have variableValue := (Term.evaluates_var_iff Var.here swap xs (xs .here)).2 rfl
    exact (Formula.holds_termEq _ _ _ _).2
      ⟨xs .here, (Term.mem_eval_iff _ _ _ _).2 evaluated, (Term.mem_eval_iff _ _ _ _).2 variableValue⟩
  · intro xs _
    let moved : Assignment swap.carrier [()] := Assignment.cons (!(xs .here)) Assignment.empty
    have twice := unary_evaluates_twice xs
    have primitiveValue := (Term.primitive_evaluates_iff swap (.total ()) xs _).2
      ((swap.graph_total_iff () xs _).2 rfl)
    have left := (Term.evaluates_applyUnary_iff unary (Term.primitive (.total ())) swap xs _
      primitiveValue _).2 twice
    have arguments :
        (Interpretation.comparisonArguments (H := unrestricted) id unaryAt [()]).EvaluatesAt swap xs moved := by
      intro s i
      cases i with
      | here =>
        exact (Term.evaluates_applyUnary_iff unary (.var .here) swap xs _
          ((Term.evaluates_var_iff Var.here swap xs _).2 rfl) _).2
          (unary_evaluates (Assignment.cons (xs .here) Assignment.empty))
      | there i => exact nomatch i
    have right := (Term.evaluates_applyStrict_of_evaluatesAt unary _ swap xs moved arguments _).2 twice
    exact (Formula.holds_termEq _ _ _ _).2
      ⟨xs .here, (Term.mem_eval_iff _ _ _ _).2 left, (Term.mem_eval_iff _ _ _ _).2 right⟩

/-- The comparison makes use of both required sequents and the primitive totality rule. -/
private def comparison : Interpretation.SyntacticComparison (Interpretation.identity involutive) where
  alpha := unaryAt
  beta := unaryAt
  alpha_total s := by
    cases s
    exact (Interpretation.identity involutive).total ()
  beta_total s := by
    cases s
    exact (Interpretation.identity involutive).total ()
  beta_alpha s := by
    cases s
    exact Derivation.required (T := involutive) false
  alpha_beta s := by
    cases s
    exact Derivation.required (T := involutive) false
  total f := by
    cases f
    exact Derivation.required (T := involutive) true
  quantity q := nomatch q
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p

/-- The model isomorphism really moves the first point, using evaluation of the alpha term. -/
theorem forward_moves_point : (comparison.modelIso involutiveModel).hom.hom.onSort () false = true := by
  rw [Interpretation.SyntacticComparison.modelIso_hom_apply]
  exact Term.evaluates_unique _ _ _ (comparison.alpha_evaluates involutiveModel () false)
    (unary_evaluates (Assignment.cons false Assignment.empty))

/-- The inverse model isomorphism evaluates the beta term on the second point. -/
theorem inverse_recovers_point : (comparison.modelIso involutiveModel).inv.hom.onSort () true = false := by
  rw [Interpretation.SyntacticComparison.modelIso_inv_apply]
  exact Term.evaluates_unique _ _ _ (comparison.beta_evaluates involutiveModel () true)
    (unary_evaluates (Assignment.cons true Assignment.empty))

end SHIGURE.Chapter2.InverseTermWitnesses
