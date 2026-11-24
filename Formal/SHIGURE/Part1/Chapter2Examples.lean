import Formal.SHIGURE.Part1.ObservedModels
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

/-- Form the unary operation application used to write the idempotence Law. -/
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

/-- An evaluated input gives an evaluated unary application in any structure of this signature. -/
private theorem applies {A : Structure signature} {t : Term signature [()] ()}
    {xs : Assignment A.carrier [()]} {y : A.carrier ()} (evaluated : t.Evaluates A xs y) :
    (f t).Evaluates A xs (A.total () (Assignment.cons y Assignment.empty)) := by
  apply (Term.evaluates_app_iff _ _ _ _ _).2
  refine ⟨Assignment.cons y Assignment.empty, ?_, (A.graph_total_iff _ _ _).2 rfl⟩
  intro s i
  cases i with
  | here => exact evaluated
  | there i => exact nomatch i

/-- The identity operation on the same two points supplies an extended model. -/
def identityStructure : Structure signature where
  carrier _ := Bool
  total _ xs := xs .here
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The identity operation satisfies the idempotence Law for every assignment. -/
theorem identity_satisfies_idempotence : idempotence.Holds identityStructure := by
  intro xs _
  let x := xs .here
  have variable_value : (Term.var (sig := signature) (Γ := [()]) .here).Evaluates identityStructure xs x :=
    (Term.evaluates_var_iff _ _ _ _).2 rfl
  have first : (f (.var .here)).Evaluates identityStructure xs x := applies variable_value
  have second : (f (f (.var .here))).Evaluates identityStructure xs x := applies first
  exact (Formula.holds_termEq _ _ identityStructure xs).2
    ⟨x, (Term.mem_eval_iff _ _ _ _).2 second, (Term.mem_eval_iff _ _ _ _).2 first⟩

/-- The idempotent theory has an actual model on the two points. -/
def identityModel : Model extended.theory :=
  ⟨identityStructure, fun _ => identity_satisfies_idempotence⟩

/-- The two-point swap does not satisfy the added idempotence Law. -/
theorem swap_fails_idempotence : ¬ idempotence.Holds swap := by
  intro law
  let xs : Assignment swap.carrier [()] := Assignment.cons false Assignment.empty
  have variable_value : (Term.var (sig := signature) (Γ := [()]) .here).Evaluates swap xs false := by
    exact (Term.evaluates_var_iff _ _ _ _).2 rfl
  have first : (f (.var .here)).Evaluates swap xs true := applies variable_value
  have second : (f (f (.var .here))).Evaluates swap xs false := applies first
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

/-- The extra Law requires a witness in the original sort. -/
private def inhabitedLaw : Law signature :=
  ⟨[], .truth, .ex (s := ()) (.atom (.eq .here .here))⟩

/-- Add inhabitance to a theory already requiring idempotence. -/
private def addsInhabited : LawExtension extended.theory :=
  ⟨Bool, fun | false => idempotence | true => inhabitedLaw, fun _ => ⟨false, rfl⟩⟩

/-- Identity on two points satisfies both required Laws after the addition. -/
private def modelOfBoth : Model addsInhabited.theory :=
  ⟨identityStructure, fun name => by
    cases name
    · exact identity_satisfies_idempotence
    · exact fun _ _ => ⟨false, rfl⟩⟩

/-- Forgetting the added Law preserves the earlier idempotence Law on this model. -/
theorem retains_old_law_after_extension : idempotence.Holds (addsInhabited.forget.obj modelOfBoth).obj :=
  (addsInhabited.forget.obj modelOfBoth).property ()

/-- Replacing idempotence by inhabitance alone fails the requirement to retain the old Law. -/
theorem inhabitance_alone_does_not_extend :
    ¬ ∃ candidate : LawExtension extended.theory, ∀ name, candidate.law name = inhabitedLaw := by
  rintro ⟨candidate, allInhabited⟩
  obtain ⟨name, keepsOld⟩ := candidate.includes ()
  have lawEq : inhabitedLaw = idempotence := (allInhabited name).symm.trans keepsOld
  have inhabitance : inhabitedLaw.Holds swap := fun _ _ => ⟨false, rfl⟩
  exact swap_fails_idempotence (lawEq ▸ inhabitance)

end Chapter2.IdempotentSwap

namespace Chapter2.ReflectionWitnesses

/-- Use unary relation and partial operation symbols to test the two reflection conditions independently. -/
private def signature : Signature.{0} where
  SortType := Unit
  Total := Empty
  Rel := Unit
  Partial := Unit
  Quantity := Empty
  totalArity n := nomatch n
  relInputs _ := [()]
  partialArity _ := ⟨[()], ()⟩
  quantityArity n := nomatch n

/-- Choose independently whether the relation and the partial domain contain every input. -/
private def structureWith (related defined : Bool) : Structure signature where
  carrier _ := Bool
  total n := nomatch n
  relation _ := fun _ => related = true
  partialDomain _ := fun _ => defined = true
  partialValue _ xs := xs.val .here
  quantity n := nomatch n

/-- The map from the empty relation and domain sends each point to itself. -/
private def promote (r p : Bool) : StructureMap (structureWith false false) (structureWith r p) where
  onSort _ := id
  total_comm n := nomatch n
  relation_mem _ _ h := Bool.noConfusion h
  partial_mem _ _ h := Bool.noConfusion h
  partial_comm _ _ := rfl
  quantity_comm n := nomatch n

/-- A tuple on which to test whether the promoted structure reflects membership. -/
private def tuple : Assignment (structureWith false false).carrier [()] :=
  Assignment.cons false Assignment.empty

/-- With only the relation enlarged, the identity on carriers reflects the domain alone. -/
theorem only_domain_reflected :
    (∀ s, Function.Bijective ((promote true false).onSort s)) ∧
      (promote true false).ReflectsDomains ∧ ¬ (promote true false).ReflectsRelations := by
  refine ⟨fun _ => Function.bijective_id, fun _ _ h => h, ?_⟩
  intro reflects
  exact Bool.noConfusion (show false = true from reflects () tuple rfl)

/-- With only the domain enlarged, the identity on carriers reflects the relation alone. -/
theorem only_relation_reflected :
    (∀ s, Function.Bijective ((promote false true).onSort s)) ∧
      (promote false true).ReflectsRelations ∧ ¬ (promote false true).ReflectsDomains := by
  refine ⟨fun _ => Function.bijective_id, fun _ _ h => h, ?_⟩
  intro reflects
  exact Bool.noConfusion (show false = true from reflects () tuple rfl)

/-- Exchange the points in a structure where the relation and domain are full. -/
private def swap : StructureMap (structureWith true true) (structureWith true true) where
  onSort _ := Bool.not
  total_comm n := nomatch n
  relation_mem _ _ _ := rfl
  partial_mem _ _ _ := rfl
  partial_comm _ _ := rfl
  quantity_comm n := nomatch n

/-- The swap with the full relation and domain is an isomorphism. -/
theorem swap_isIso :
    IsIso (show structureWith true true ⟶ structureWith true true from swap) :=
  (Structure.isIso_iff_bijective_reflects swap).2
    ⟨fun _ => Function.Involutive.bijective Bool.not_not, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Keep the whole signature so that its partial domain is part of the fixed reduct. -/
private def whole : Subsignature signature signature :=
  ⟨SignatureNames.identity signature,
    ⟨Function.injective_id, Function.injective_id, Function.injective_id,
      Function.injective_id, Function.injective_id⟩⟩

/-- Both choices of partial domain are models of the theory with no Laws. -/
private def unrestricted : Theory.{0} := ⟨signature, Empty, fun name => nomatch name⟩

/-- Interpret the same carrier with either the empty or the full partial domain. -/
private def domainModel (defined : Bool) : Model unrestricted :=
  ⟨structureWith false defined, fun name => nomatch name⟩

/-- Fix the whole reduct of the model with the empty domain. -/
private def fixedData : Structure signature :=
  whole.val.restrict (domainModel false).obj

/-- The model with the empty partial domain has exactly the prescribed reduct. -/
theorem empty_domain_is_fixed : Nonempty (FixedModel unrestricted whole fixedData) :=
  ⟨⟨domainModel false, rfl⟩⟩

/-- The full-domain model cannot be a fixed object with the prescribed empty domain. -/
theorem full_domain_fails_fixed_reduct :
    ¬ ∃ A : FixedModel unrestricted whole fixedData, A.model = domainModel true := by
  rintro ⟨A, sameModel⟩
  have same : whole.val.restrict (domainModel true).obj = fixedData :=
    (congrArg (fun M : Model unrestricted => whole.val.restrict M.obj) sameModel).symm.trans A.fixed
  have domains : (whole.val.restrict (domainModel true).obj).partialDomain = fixedData.partialDomain := by
    have carried := congrArg (fun X : Structure signature => HEq X.partialDomain fixedData.partialDomain) same
    exact eq_of_heq (Eq.mpr carried HEq.rfl)
  have present : tuple ∈ (whole.val.restrict (domainModel true).obj).partialDomain () := rfl
  rw [domains] at present
  exact Bool.noConfusion (show false = true from present)

end Chapter2.ReflectionWitnesses

namespace Chapter2.ObservationWitnesses

open IdempotentSwap

/-- Place two Boolean observations on the same original carrier. -/
private def shape : ObservationShape unrestricted.signature :=
  ⟨Bool, fun _ => (), fun _ => Bool⟩

/-- In this model both observations forget the point. -/
private def constant : ObservedModel unrestricted shape := ⟨swapModel, fun _ _ => true⟩

/-- In this model both observations return the point. -/
private def identity : ObservedModel unrestricted shape := ⟨swapModel, fun _ x => x⟩

/-- The two-point exchange commutes with the original unary operation. -/
private def originalSwap : StructureMap swapModel.obj swapModel.obj where
  onSort _ := Bool.not
  total_comm _ _ := rfl
  relation_mem r := nomatch r
  partial_mem p := nomatch p
  partial_comm p := nomatch p
  quantity_comm q := nomatch q

/-- The exchange is an observed arrow when both observations are constant. -/
private def constantSwap : ObservedModel.Hom constant constant :=
  ObservedModel.Hom.mk (ObjectProperty.homMk originalSwap) (fun _ _ => rfl)

/-- A constant observation identifies the observed values of the two distinct points. -/
theorem constant_observation_agrees :
    constant.observe false false = constant.observe false true ∧ (false : Bool) ≠ true :=
  ⟨rfl, fun h => Bool.noConfusion h⟩

/-- The swap preserves both constant observations. -/
theorem swap_preserves_constant : ObservedModel.Preserves constant constant (ObjectProperty.homMk originalSwap) :=
  constantSwap.commutes

/-- The same structural swap changes the identity observation at the first point. -/
theorem swap_fails_identity_observation :
    ¬ ObservedModel.Preserves identity identity (ObjectProperty.homMk originalSwap) := by
  intro observed
  exact Bool.noConfusion (show true = false from observed false false)

/-- A genuine observed swap becomes a fixed-data arrow, with each value component fixed. -/
theorem encoded_swap_fixes_values :
    FixedModel.FixesCarriers constant.encode constant.encode
      (ObservedModel.encodeHom constantSwap).modelHom :=
  (ObservedModel.encodeHom constantSwap).fixes

/-- Move only the first value carrier while preserving the two constant operations. -/
private def movesOneValue : StructureMap constant.extendStructure constant.extendStructure where
  onSort
    | .inl _ => id
    | .inr false => fun _ => true
    | .inr true => id
  total_comm f _ := by
    cases f with
    | inl _ => rfl
    | inr i => cases i <;> rfl
  relation_mem r := nomatch r
  partial_mem p := nomatch p
  partial_comm p := nomatch p
  quantity_comm q := nomatch q

/-- A map changing one value sort can preserve the operations and still fail the fixed condition. -/
theorem moving_value_fails_fixed :
    ¬ FixedModel.FixesCarriers constant.encode constant.encode (ObjectProperty.homMk movesOneValue) := by
  intro fixed
  exact Bool.noConfusion (show true = false from fixed false false)

/-- Keep the arities of the discrete value signature and identify its two sort names. -/
private def collapseValues : SignatureNames shape.valueSignature shape.valueSignature where
  onSort _ := false
  onTotal := id
  onRel := id
  onPartial := id
  onQuantity := id
  totalArity n := PEmpty.elim n
  relInputs n := PEmpty.elim n
  partialArity n := PEmpty.elim n
  quantityArity n := PEmpty.elim n

/-- The value signature embeds into the enlarged signature by its distinct names. -/
theorem values_are_included : shape.values.val.IsInclusion :=
  shape.values.property

/-- Identifying both value sort names preserves arities and fails the inclusion condition. -/
theorem collapsing_names_fails_inclusion : ¬ collapseValues.IsInclusion := by
  intro inclusion
  exact Bool.noConfusion (inclusion.1 (a₁ := false) (a₂ := true) rfl)

end Chapter2.ObservationWitnesses

end SHIGURE
