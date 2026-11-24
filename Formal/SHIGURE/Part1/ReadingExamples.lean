import Formal.SHIGURE.Part1.IdentityInterpretation
import Formal.SHIGURE.Part1.Reading
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Int.Cast.Lemmas

/-! # Evaluation in the assigned cover pieces

Compare a quantified formula on a retained relation and verify that an
unassigned primitive is unavailable in the target of the comparison.
-/

namespace SHIGURE.Chapter1.CoverTransport

/-- Distinguish two nullary relations so one can be kept and the other forgotten. -/
private def signature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Bool
  Partial := Empty
  Quantity := Empty
  totalArity f := nomatch f
  relInputs _ := []
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- There are no Laws beyond the primitive relation declarations. -/
private def presentation : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Empty
      statement := fun name => nomatch name
      role := fun name => nomatch name }
  derived name := nomatch name

/-- The retained relation holds and the other relation fails. -/
private def data : Structure signature where
  carrier _ := Bool
  total f := nomatch f
  relation r := if (show Bool from r) then ∅ else Set.univ
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The side of the cover assigned by the comparison retains just one relation. -/
private def piece : DeclarationContext presentation where
  declarations := {d | d = .sort () ∨ d = .relation false}
  closed := by
    rintro a (rfl | rfl) d hd
    · exact hd.elim
    · obtain ⟨_, h, _⟩ := hd
      cases h

/-- The whole context retains both relations. -/
private def whole : DeclarationContext presentation := ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩

/-- The original cover consists of the whole context. -/
private def source : Reading.{0, 0, 0, 0} where
  presentation := presentation
  structureData := data
  observation := StateObservation.ofSort () Bool id
  context := whole
  cover := ⟨Unit, fun _ => whole, fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := data
  familyObservation := none
  ValueStructure := fun _ => Unit
  valueStructure := ()
  coefficients := none

/-- The two target pieces cover the whole context, but only one is assigned. -/
private def target : Reading.{0, 0, 0, 0} :=
  { source with
    cover :=
      { Index := Bool
        piece := fun i => if i then piece else whole
        subset := fun _ _ _ => Set.mem_univ _
        covers := fun h => ⟨false, h⟩ } }

/-- The two-piece target cover differs from the original one-piece cover. -/
theorem cover_change_is_not_fixed : ¬ source.SameContext target := by
  intro same
  have index : Unit = Bool := congrArg DeclarationCover.Index (eq_of_heq same.cover)
  have small : Subsingleton Bool := index ▸ (inferInstance : Subsingleton Unit)
  exact (by decide : false ≠ true) (@Subsingleton.elim Bool small false true)

/-- Emptying the retained relation cannot be certified as the same native source. -/
theorem different_relations_disagree_on_retained_structure :
    ¬ (RestrictedStructure.restrict whole data).Agrees
      (RestrictedStructure.restrict whole { data with relation := fun _ => ∅ }) := by
  intro same
  let atom : Atomic signature [] := .rel false (fun i => nomatch i)
  have supported : Declaration.atomicSupport (P := presentation) atom ⊆ whole.declarations :=
    fun _ _ => Set.mem_univ _
  have fact : (RestrictedStructure.restrict whole data).evaluation.atomic Assignment.empty atom supported :=
    Set.mem_univ _
  exact (same.preserves atom supported Assignment.empty fact).elim

/-- Restrict the source to one relation and transport its support to the assigned piece. -/
private def coverChange : ReadingContextChange source target (Interpretation.identity presentation.theory) where
  retained := piece
  inside := fun _ _ => Set.mem_univ _
  supporting := fun _ => Interpretation.identity presentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces := fun _ => {true}
  localSupport := by
    intro i a ha _ d hd
    refine ⟨true, Set.mem_singleton _, ?_⟩
    change d = .sort () ∨ d = .relation false
    rcases ha with rfl | rfl
    · exact Or.inl (Set.mem_singleton_iff.1 hd)
    · rcases hd with hsort | hrelation
      · obtain ⟨_, h, _⟩ := hsort
        cases h
      · exact Or.inr (Set.mem_singleton_iff.1 hrelation)

/-- The identity state map and the selected cover change belong to one comparison. -/
private def comparison : ReadingComparison source target where
  interpretation := Interpretation.identity presentation.theory
  targetModel := fun name => nomatch name.val
  state :=
    { onSort := fun _ x => x
      total_comm := fun f => nomatch f
      relation_mem := by
        intro r e h
        cases r
        · exact Set.mem_univ _
        · exact h.elim
      partial_mem := fun p => nomatch p
      partial_comm := fun p => nomatch p
      quantity_comm := fun q => nomatch q }
  contexts := .identity _
  declarationChange := .changed coverChange
  coefficientChange := PUnit.unit
  value := id
  commutes := fun _ => rfl
  restrictedObservations := coverChange.observationSquare_of_all _ _ _
    (fun _ => Or.inl rfl) (fun _ => rfl)

/-- An equivalent representative mentions the relation outside the selected piece. -/
private def alternateIdentity : Interpretation presentation.theory presentation.theory where
  onSort := id
  translation :=
    { operation := fun op => match op with
        | .total f => nomatch f
        | .quantity q => nomatch q
        | .partialOp p => nomatch p
      relation := fun r => ((Translation.identity signature).relation r).conj
        (Formula.truth.disj ((Translation.identity signature).relation true))
      partialDomain p := nomatch p }
  total f := nomatch f
  quantity q := nomatch q
  partialDefined p := nomatch p
  definedPartial p := nomatch p
  preserves n := nomatch n.val

/-- Each relation replacement is mutually derivable with its original expression. -/
private theorem alternateIdentity_equivalent :
    alternateIdentity.Equivalent (Interpretation.identity presentation.theory) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro op
    cases op <;> rename_i name <;> exact nomatch name
  · intro r
    exact ⟨⟨.andLeft _ _⟩, ⟨.andIntro (.refl _) (.cut (.truth _) (.orLeft _ _))⟩⟩
  · intro p
    exact nomatch p

/-- Changing the representative of the identity still admits a fixed declaration comparison. -/
def alternate_fixed_context : source.ContextCompatibility source alternateIdentity :=
  .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- The selected context uses the supported representative of this same interpretation. -/
private def alternateCoverChange : ReadingContextChange source target alternateIdentity where
  retained := coverChange.retained
  inside := coverChange.inside
  supporting := coverChange.supporting
  equivalent := fun _ => alternateIdentity_equivalent.symm
  pieces := coverChange.pieces
  localSupport := coverChange.localSupport

/-- The alternative representative uses the same state and covered evaluation. -/
private def alternateComparison : ReadingComparison source target where
  interpretation := alternateIdentity
  targetModel := comparison.targetModel
  state :=
    { onSort := fun _ x => x
      total_comm f := nomatch f
      relation_mem := by
        intro r e held
        exact ⟨comparison.state.relation_mem r e held, Or.inl True.intro⟩
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .changed alternateCoverChange
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl
  restrictedObservations := alternateCoverChange.observationSquare_of_all _ _ _
    (fun _ => Or.inl rfl) (fun _ => rfl)

/-- An existential can use the actual value of the retained nullary relation. -/
private def formula : Formula signature [] :=
  .ex (s := ()) (.atom (.rel false (fun i => nomatch i)))

/-- The support of that existential fits inside the retained source piece. -/
private theorem formulaSupported :
    Declaration.formulaSupport formula ⊆ (coverChange.sourcePiece ()).declarations := by
  intro d hd
  refine ⟨?_, Set.mem_univ _⟩
  rcases hd with hsort | hformula
  · obtain ⟨_, h, _⟩ := hsort
    cases h
  · exact hformula.imp Set.mem_singleton_iff.1 Set.mem_singleton_iff.1

/-- The local comparison really evaluates the relation in the assigned target piece. -/
theorem existential_transports_in_assigned_piece :
    (RestrictedEvaluation.restrict (coverChange.targetPiece ()) data).holds
      (comparison.interpretation.translation.formula formula)
      (coverChange.local_formula_support () formula formulaSupported)
      (comparison.interpretation.mapStates comparison.state Assignment.empty) :=
  comparison.transport_restricted_formula ⟨coverChange, rfl⟩ () formula formulaSupported
    Assignment.empty ⟨false, Set.mem_univ _⟩

/-- The same local evaluator works for the equivalent representative that mentions a forgotten relation. -/
theorem equivalent_representative_transports_in_assigned_piece :
    (RestrictedEvaluation.restrict (alternateCoverChange.targetPiece ()) data).holds
      ((coverChange.supporting ()).translation.formula formula)
      (alternateCoverChange.local_formula_support () formula formulaSupported)
      ((alternateCoverChange.equivalent ()).retype
        (alternateComparison.interpretation.mapStates alternateComparison.state Assignment.empty)) :=
  alternateComparison.transport_restricted_formula ⟨alternateCoverChange, rfl⟩ () formula formulaSupported
    Assignment.empty ⟨false, Set.mem_univ _⟩

/-- The deliberately unassigned relation cannot be read in the assigned target pieces. -/
theorem other_relation_is_not_assigned :
    Declaration.relation true ∉ (coverChange.targetPiece ()).declarations := by
  rintro ⟨i, hi, h⟩
  have same : i = true := Set.mem_singleton_iff.1 hi
  subst i
  change Declaration.relation (P := presentation) true = Declaration.sort () ∨
    Declaration.relation (P := presentation) true = Declaration.relation false at h
  rcases h with impossible | impossible <;> cases impossible

/-- The nullary formula that reads the chosen relation symbol. -/
private def selectedRelation (r : Bool) : Formula signature [] :=
  .atom (.rel r (fun i => nomatch i))

/-- A common primitive relation can be represented by either of two equivalent target relations. -/
private def interchangeableRelations : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Bool
      statement := fun r => ⟨[], selectedRelation r, selectedRelation (!r)⟩
      role := fun _ => .required }
  derived _ h := by cases h

/-- Both required Laws are satisfied by this target model. -/
private def bothRelationsHold : Structure signature := { data with relation := fun _ => Set.univ }

/-- Choose which target relation gives the retained source relation. -/
private def toInterchangeable (r : Bool) : Interpretation presentation.theory interchangeableRelations.theory where
  onSort := id
  translation :=
    { operation op := match op with
        | .total f => nomatch f
        | .quantity q => nomatch q
        | .partialOp p => nomatch p
      relation _ := selectedRelation r
      partialDomain p := nomatch p }
  total f := nomatch f
  quantity q := nomatch q
  partialDefined p := nomatch p
  definedPartial p := nomatch p
  preserves n := nomatch n.val

/-- The two replacements use different symbols and the displayed Laws give mutual derivability. -/
private theorem interchangeable_equivalent (r : Bool) :
    (toInterchangeable r).Equivalent (toInterchangeable false) := by
  cases r
  · exact Interpretation.Equivalent.refl _
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro op
      cases op <;> rename_i name <;> exact nomatch name
    · intro _
      change Derivation.Equivalent interchangeableRelations.theory (selectedRelation true) (selectedRelation false)
      exact ⟨⟨Derivation.required (T := interchangeableRelations.theory) ⟨true, rfl⟩⟩,
        ⟨Derivation.required (T := interchangeableRelations.theory) ⟨false, rfl⟩⟩⟩
    · intro p
      exact nomatch p

/-- Both source pieces contain the same retained relation. -/
private def sourceWithOverlap : Reading.{0, 0, 0, 0} :=
  { source with cover := ⟨Bool, fun _ => whole, fun _ _ h => h, fun h => ⟨false, h⟩⟩ }

/-- One target piece contains the sort and its own relation. -/
private def interchangeablePiece (r : Bool) : DeclarationContext interchangeableRelations where
  declarations := {d | d = .sort () ∨ d = .relation r}
  closed := by
    rintro a (rfl | rfl) d hd
    · exact hd.elim
    · obtain ⟨_, h, _⟩ := hd
      cases h

/-- The Laws are present in a separate piece that the comparison does not select. -/
private def targetWithSeparatePieces : Reading.{0, 0, 0, 0} where
  presentation := interchangeableRelations
  structureData := bothRelationsHold
  observation := .ofSort () Bool id
  context := ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩
  cover :=
    { Index := Option Bool
      piece := fun i => match i with
        | none => ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩
        | some r => interchangeablePiece r
      subset _ _ _ := Set.mem_univ _
      covers h := ⟨none, h⟩ }
  Family := Unit
  realize _ := bothRelationsHold
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := none

/-- Each source piece selects only the target relation it can evaluate. -/
private def piecewiseTranslation : ReadingContextChange sourceWithOverlap targetWithSeparatePieces
    (toInterchangeable false) where
  retained := piece
  inside _ _ := Set.mem_univ _
  supporting := toInterchangeable
  equivalent := interchangeable_equivalent
  pieces i := {some i}
  localSupport := by
    intro i a kept _ d above
    refine ⟨some i, Set.mem_singleton _, ?_⟩
    change d = .sort () ∨ d = .relation i
    rcases kept with rfl | rfl
    · exact Or.inl (Set.mem_singleton_iff.1 above)
    · rcases above with hsort | hrelation
      · obtain ⟨_, h, _⟩ := hsort
        cases h
      · exact Or.inr (Set.mem_singleton_iff.1 hrelation)

/-- Different supported translation representatives give a comparison on the actual model. -/
def locally_distinct_translations_compare :
    ReadingComparison sourceWithOverlap targetWithSeparatePieces where
  interpretation := toInterchangeable false
  targetModel _ _ _ := Set.mem_univ _
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem _ _ _ := Set.mem_univ _
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .changed piecewiseTranslation
  declaredObservations := .external
  observationSupport := ⟨False.elim, False.elim⟩
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl
  restrictedObservations := piecewiseTranslation.observationSquare_of_all _ _ _
    (fun _ => Or.inl rfl) (fun _ => rfl)

/-- The separate pieces agree where both translate the same source formula. -/
theorem locally_distinct_translations_agree_on_overlap :
    (RestrictedEvaluation.restrict (piecewiseTranslation.targetPiece false) bothRelationsHold).holds
      ((toInterchangeable false).translation.formula formula)
      (piecewiseTranslation.local_formula_support false formula formulaSupported)
      ((piecewiseTranslation.equivalent false).retype Assignment.empty) ↔
    (RestrictedEvaluation.restrict (piecewiseTranslation.targetPiece true) bothRelationsHold).holds
      ((toInterchangeable true).translation.formula formula)
      (piecewiseTranslation.local_formula_support true formula formulaSupported)
      ((piecewiseTranslation.equivalent true).retype Assignment.empty) :=
  locally_distinct_translations_compare.restricted_evaluation_agrees_on_overlap
    ⟨piecewiseTranslation, rfl⟩ false true formula formulaSupported formulaSupported Assignment.empty

/-- Require the selected nullary relation in the presentation of a coefficient scheme. -/
private def modelPresentation : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Unit
      statement := fun _ => ⟨[], .truth, .atom (.rel false (fun i => nomatch i))⟩
      role := fun _ => .required }
  derived _ h := by cases h

/-- Retain the complete presentation used to test coefficient Law satisfaction. -/
private def modelContext : DeclarationContext modelPresentation :=
  ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩

/-- The two Law-testing realizations share the integer base ring. -/
private def lawModelBase : CoefficientRing := ⟨Int, inferInstance⟩

/-- Choose a realization whose required relation holds exactly when the flag is true. -/
private def lawTestingStructure (satisfies : Bool) : Structure signature :=
  if satisfies then data else { data with relation := fun _ => ∅ }

/-- The interpreted Law on the retained declarations uses the same test structure. -/
private def retainedModel (satisfies : Bool) : RestrictedStructure modelContext :=
  RestrictedStructure.restrict modelContext (lawTestingStructure satisfies)

/-- Use set-valued evaluation of the declared Law in both realized structures. -/
private def lawModelScheme : CoefficientScheme modelContext lawModelBase where
  Realization _ := Bool
  structureOf _ := retainedModel
  structure_retained _ a := (retainedModel a).hasOnlyRetainedSorts_of_all (fun s => Set.mem_univ (Declaration.sort s))
  category _ :=
    { Hom := fun a b => PLift (a = b)
      id := fun _ => ⟨rfl⟩
      comp := fun f g => ⟨f.down.trans g.down⟩
      id_comp := fun _ => Subsingleton.elim _ _
      comp_id := fun _ => Subsingleton.elim _ _
      assoc := fun _ _ _ => Subsingleton.elim _ _ }
  mapPoints f _ _ x := f.down ▸ x
  mapPoints_preserves f := by
    rcases f with ⟨rfl⟩
    intro _ _ _ _ held
    exact held
  mapPoints_id _ _ _ _ := rfl
  mapPoints_comp f g _ _ _ := by
    rcases f with ⟨rfl⟩
    rcases g with ⟨rfl⟩
    rfl
  permitsPoints _ _ _ _ _ := True
  permitsPoints_congr := by intros; rfl
  Native := Bool
  nativeStructure := retainedModel
  native_retained a := (retainedModel a).hasOnlyRetainedSorts_of_all (fun s => Set.mem_univ (Declaration.sort s))
  realizeNative _ := id
  nativePoints _ _ _ _ := id
  nativePoints_permitted _ _ _ _ := True.intro
  interpretLaw _ a := (retainedModel a).satisfies
  change _ := id
  changePoints _ _ _ _ := id

/-- With the same coefficients and rule, the required relation distinguishes two realizations. -/
theorem coefficient_scheme_evaluates_required_law (R : CoefficientAlgebra lawModelBase) :
    lawModelScheme.IsPointModel R true ∧ ¬ lawModelScheme.IsPointModel R false := by
  constructor
  · intro name kept e holds
    exact Set.mem_univ _
  · intro model
    exact (model ⟨(), rfl⟩ (Set.mem_univ _) Assignment.empty True.intro).elim

/-- An arbitrary Law interpretation cannot certify an invalid set-valued point model. -/
theorem point_model_depends_on_actual_structure (R : CoefficientAlgebra lawModelBase) :
    ¬ ({ lawModelScheme with interpretLaw := fun _ _ _ _ => True }).IsPointModel R false :=
  (coefficient_scheme_evaluates_required_law R).2

/-- The state observation exists even when the structure fails a required Law. -/
private def lawTestingReading (satisfies : Bool) : Reading.{0, 0, 0, 0} where
  presentation := modelPresentation
  structureData := lawTestingStructure satisfies
  observation := StateObservation.ofSort () Unit (fun _ => ())
  context := modelContext
  cover := ⟨Unit, fun _ => modelContext, fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := lawTestingStructure satisfies
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := none

/-- A false required relation on the source precludes a comparison of models. -/
theorem model_reading_comparison_requires_source_model :
    ¬ Nonempty (ModelReadingComparison (lawTestingReading false) (lawTestingReading true)) := by
  rintro ⟨comparison⟩
  exact (comparison.sourceModel ⟨(), rfl⟩ Assignment.empty True.intro).elim

/-- The structure reading still compares to a model when its source fails a required Law. -/
def nonmodel_state_comparison : ReadingComparison (lawTestingReading false) (lawTestingReading true) where
  interpretation := Interpretation.identity modelPresentation.theory
  targetModel _ _ _ := Set.mem_univ _
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem _ _ held := held.elim
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl

end SHIGURE.Chapter1.CoverTransport

namespace SHIGURE.Chapter1.RetainedCoefficientInputs

/-- The two sorts have independent carriers and no symbols. -/
private def signature : Signature where
  SortType := Bool
  Total := Empty
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity f := nomatch f
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- There are no Law declarations. -/
private def presentation : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Empty
      statement := fun name => nomatch name
      role := fun name => nomatch name }
  derived name := nomatch name

/-- The ordinary reading keeps states of both sorts. -/
private def ordinary : Structure signature where
  carrier _ := Int
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The coefficient scheme retains the first sort. -/
private def retained : DeclarationContext presentation where
  declarations := {.sort false}
  closed := by
    intro d hd e he
    have same : d = .sort false := Set.mem_singleton_iff.1 hd
    subst d
    exact he.elim

/-- Vary the forgotten carrier while keeping the retained integer carrier. -/
private def ambient (full : Bool) : Structure signature where
  carrier := fun
    | false => Int
    | true => if full then Int else Empty
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The realized retained sort is unchanged across both choices. -/
private def realized (full : Bool) : RestrictedStructure retained :=
  RestrictedStructure.restrict retained (ambient full)

/-- The context retains only the false sort. -/
private theorem retained_sort (s : signature.SortType) (kept : Declaration.sort s ∈ retained.declarations) :
    s = false := by
  have same : Declaration.sort (P := presentation) s = .sort false := Set.mem_singleton_iff.1 kept
  cases same
  rfl

/-- Both the native and the realized carrier in the scheme use only the retained sort. -/
private def scalarRealization (R : Type) : RestrictedStructure retained where
  carrier
    | false => R
    | true => PUnit
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The forgotten sort has the designated inert carrier. -/
private theorem scalarRealization_retained (R : Type) : (scalarRealization R).HasOnlyRetainedSorts := by
  intro s forgotten
  cases s
  · exact (forgotten (Set.mem_singleton _)).elim
  · rfl

/-- A hidden integer carrier cannot be installed as part of a schematic structure. -/
theorem scheme_cannot_keep_forgotten_carrier : ¬ (realized true).HasOnlyRetainedSorts := by
  intro retainedOnly
  have omitted : Declaration.sort true ∉ retained.declarations := by
    intro member
    exact Bool.noConfusion (retained_sort true member)
  have same : Int = PUnit := retainedOnly true omitted
  have singleton : Subsingleton Int := same.symm ▸ (inferInstanceAs (Subsingleton PUnit))
  exact (by decide : (0 : Int) ≠ 1) (@Subsingleton.elim Int singleton 0 1)

/-- The kept carrier agrees across the two ambient structures. -/
private theorem retained_carrier_eq (source target : Bool) (s : signature.SortType)
    (kept : Declaration.sort s ∈ retained.declarations) :
    (realized source).carrier s = (realized target).carrier s := by
  cases retained_sort s kept
  rfl

/-- Retained facts transport along the supplied carrier identifications. -/
private theorem retained_preserves (source target : RestrictedStructure retained)
    (same : ∀ s (_kept : Declaration.sort s ∈ retained.declarations), source.carrier s = target.carrier s) :
    source.Preserves target (fun s kept x => same s kept ▸ x) := by
  intro Γ a supported e held
  cases a with
  | @eq s i j =>
    have kept : Declaration.sort s ∈ retained.declarations :=
      supported (Or.inl ⟨s, i.sort_mem, rfl⟩)
    exact congrArg (fun x => same s kept ▸ x) held
  | rel r _ => exact nomatch r
  | domain p _ => exact nomatch p
  | graph op _ _ => cases op <;> rename_i symbol <;> exact nomatch symbol

/-- The ambient structures agree after restricting to the kept sort. -/
private theorem ambient_agrees (source target : Bool) : (realized source).Agrees (realized target) :=
  ⟨retained_carrier_eq source target, retained_preserves _ _ _, retained_preserves _ _ _⟩

/-- The ambient and schematic structures agree at the kept declarations. -/
private theorem ambient_agrees_scheme (full : Bool) : (realized full).Agrees (scalarRealization Int) := by
  have same (s : signature.SortType) (kept : Declaration.sort s ∈ retained.declarations) :
      (realized full).carrier s = (scalarRealization Int).carrier s := by
    cases retained_sort s kept
    rfl
  exact ⟨same, retained_preserves _ _ _, retained_preserves _ _ _⟩

/-- Use the integers as the base and the initial coefficients. -/
private def integers : CoefficientRing := ⟨Int, inferInstance⟩

/-- No scheme can use the forgotten sort's inhabitation to distinguish these source structures. -/
theorem permission_cannot_test_forgotten_carrier (scheme : CoefficientScheme retained integers)
    (R : CoefficientAlgebra integers) (a : scheme.Realization R)
    (points : scheme.SelectedPointMap R a (realized false).carrier ({false} : Set Bool))
    (testsForgotten : ∀ X points,
      scheme.permitsPoints R a X ({false} : Set Bool) points ↔ Nonempty (X.carrier true)) : False := by
  have kept : ∀ s ∈ ({false} : Set Bool), Declaration.sort s ∈ retained.declarations := by
    intro s hs
    cases Set.mem_singleton_iff.1 hs
    exact Set.mem_singleton _
  have permission := (testsForgotten (realized true)
    (fun s hs x => points s hs ((ambient_agrees true false).carrier_eq s (kept s hs) ▸ x))).2
      ⟨(0 : Int)⟩
  obtain ⟨empty⟩ := (testsForgotten (realized false) points).1
    ((scheme.permitsPoints_congr R a (ambient_agrees true false) kept points).1 permission)
  exact nomatch empty

/-- Changing coefficients sends the designated states by the retained-sort map. -/
private def scheme : CoefficientScheme retained integers where
  Realization _ := Bool
  structureOf _ _ := scalarRealization Int
  structure_retained _ _ := scalarRealization_retained Int
  category _ :=
    { Hom := fun a b => PLift (a = b)
      id := fun _ => ⟨rfl⟩
      comp := fun f g => ⟨f.down.trans g.down⟩
      id_comp := fun _ => Subsingleton.elim _ _
      comp_id := fun _ => Subsingleton.elim _ _
      assoc := fun _ _ _ => Subsingleton.elim _ _ }
  mapPoints _ _ _ := id
  mapPoints_preserves _ := by
    intro Γ a supported e held
    exact held
  mapPoints_id _ _ _ _ := rfl
  mapPoints_comp _ _ _ _ _ := rfl
  permitsPoints _ _ _ _ _ := True
  permitsPoints_congr := by intros; rfl
  Native := Bool
  nativeStructure _ := scalarRealization Int
  native_retained _ := scalarRealization_retained Int
  realizeNative _ := id
  nativePoints _ _ _ _ := id
  nativePoints_permitted _ _ _ _ := True.intro
  interpretLaw _ _ := (scalarRealization Int).satisfies
  change _ _ := false
  changePoints _ _ _ _ := id

/-- Observe the retained coordinate only, even though the ordinary tuple has two coordinates. -/
private def selected : CoefficientReading retained ordinary (.ofList [false, true]) where
  base := integers
  algebra := ⟨integers, RingHom.id Int⟩
  scheme := scheme
  realization := false
  selection := .ofRenaming (Δ := [false]) (fun
    | .here => .here
    | .there i => nomatch i)
  supported i := Set.mem_singleton_iff.2 (congrArg Declaration.sort (List.mem_singleton.1 i.2.sort_mem))
  realizePoint s hs := by
    cases s
    · exact id
    · exact False.elim (by
        obtain ⟨i, hi⟩ := hs
        exact (by decide : true ≠ false) (hi.symm.trans (List.mem_singleton.1 i.2.sort_mem)))
  pointOrigin := .declared PUnit.unit True.intro (by
    intro spot chosen
    cases spot
    · exact ⟨rfl, rfl⟩
    · obtain ⟨i, hi⟩ := chosen
      exact Bool.noConfusion (hi.symm.trans (List.mem_singleton.1 i.2.sort_mem)))
  evaluateOn _ R _ e := R.fromBase (e ⟨false, .here⟩)

/-- The realized value is the first coordinate for any values of the forgotten coordinate. -/
theorem evaluation_reads_retained_input (s t : Int) :
    selected.evaluate (ObservationProduct.ofAssignment
      (Assignment.cons s (Assignment.cons t Assignment.empty))) = s :=
  rfl

/-- The second original position is outside the selected coefficient inputs. -/
theorem forgotten_coordinate_unread :
    (⟨true, .there .here⟩ : (ObservationProduct.ofList [false, true]).Index) ∉
      Set.range selected.selection.inputs := by
  rintro ⟨⟨s, i⟩, h⟩
  cases i with
  | here => cases h
  | there i => exact nomatch i

/-- The scalar rule maps the retained points even when the forgotten target carrier is empty. -/
theorem change_without_forgotten_map :
    ((scheme.changePoints (R := selected.algebra) (target := integers) (RingHom.id Int) true)
      false (Set.mem_singleton _) (2 : Int)) = (2 : Int) ∧
    ¬ Nonempty (∀ s, (realized true).carrier s → (realized false).carrier s) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨f⟩
  exact nomatch f true (0 : Int)

/-- The coefficient carrier and the ordinarily observed carrier use different sorts. -/
private def separateStates (R : Type) : Structure signature where
  carrier
    | false => R
    | true => Bool
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- Realize the retained sort over the selected ring. -/
private def scalarScheme : CoefficientScheme retained integers where
  Realization _ := Unit
  structureOf R _ := scalarRealization R.scalars.Carrier
  structure_retained R _ := scalarRealization_retained R.scalars.Carrier
  category _ :=
    { Hom := fun _ _ => Unit
      id := fun _ => ()
      comp := fun _ _ => ()
      id_comp := fun _ => Subsingleton.elim _ _
      comp_id := fun _ => Subsingleton.elim _ _
      assoc := fun _ _ _ => Subsingleton.elim _ _ }
  mapPoints _ _ _ := id
  mapPoints_preserves _ := by
    intro _ _ _ _ held
    exact held
  mapPoints_id _ _ _ _ := rfl
  mapPoints_comp _ _ _ _ _ := rfl
  permitsPoints _ _ _ _ _ := True
  permitsPoints_congr := by intros; rfl
  Native := Unit
  nativeStructure _ := scalarRealization Int
  native_retained _ := scalarRealization_retained Int
  realizeNative _ _ := ()
  nativePoints R _ s kept := by
    cases s
    · exact fun x => R.fromBase x
    · cases Set.mem_singleton_iff.1 kept
  nativePoints_permitted _ _ _ _ := True.intro
  interpretLaw R _ := (scalarRealization R.scalars.Carrier).satisfies
  change _ _ := ()
  changePoints f _ s kept := by
    cases s
    · exact fun x => f x
    · cases Set.mem_singleton_iff.1 kept

/-- Two native entries may realize the same retained structure with different point maps. -/
private def shiftedNativeScheme : CoefficientScheme retained integers :=
  { scalarScheme with
    Native := Bool
    nativeStructure _ := scalarRealization Int
    native_retained _ := scalarRealization_retained Int
    realizeNative _ _ := ()
    nativePoints R shifted s kept := by
      cases retained_sort s kept
      exact fun x => R.fromBase ((show Int from x) + if shifted then 1 else 0)
    nativePoints_permitted _ _ _ _ := True.intro }

/-- Use a single coefficient coordinate at the retained sort. -/
private def retainedProduct : CoefficientProduct signature.SortType := .all (.ofSort false)

/-- Read coefficients using the specified native realization and its designated points. -/
private def nativeCoefficient (full shifted : Bool) :
    CoefficientReading retained (ambient full) retainedProduct where
  base := integers
  algebra := ⟨integers, RingHom.id Int⟩
  scheme := shiftedNativeScheme
  realization := ()
  selection := .all (.ofSort false)
  supported _ := Set.mem_singleton _
  realizePoint s hs x :=
    have kept : Declaration.sort s ∈ retained.declarations := by
      obtain ⟨i, rfl⟩ := hs
      exact Set.mem_singleton _
    shiftedNativeScheme.nativePoints ⟨integers, RingHom.id Int⟩ shifted s kept
      ((ambient_agrees_scheme full).carrier_eq s kept ▸ x)
  pointOrigin := .native shifted rfl (by
    rintro _ ⟨i, rfl⟩
    exact Set.mem_singleton _) (ambient_agrees_scheme full) (fun _ _ _ => rfl)
  evaluateOn _ _ _ e := e PUnit.unit

/-- Forgetting a carrier preserves the fixed application of the same native rule. -/
theorem fixed_native_ignores_forgotten_carrier :
    (nativeCoefficient true false).SameParameters (nativeCoefficient false false) := by
  refine ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, fun _ => HEq.rfl, Or.inr ⟨HEq.rfl, ?_⟩, HEq.rfl, HEq.rfl⟩
  -- Both selected positions have the same native carrier and point map.
  rfl

/-- A forgotten carrier cannot conceal an actual change of the native point correspondence. -/
theorem fixed_native_requires_same_retained_application :
    ¬ (nativeCoefficient true false).SameParameters (nativeCoefficient false true) := by
  intro same
  have application := same.application.elim
    (fun native => native.2.2 (.ofAgreement (ambient_agrees true false))) id
  have bad : (0 : Int) = 1 :=
    congrFun (congrFun (eq_of_heq application.2) PUnit.unit) (0 : Int)
  exact (by decide : (0 : Int) ≠ 1) bad

/-- Equal retained native data cannot select two different point maps through one local rule. -/
theorem native_same_retained_data_with_distinct_maps_fails :
    ¬ (nativeCoefficient true false).RespectsRestriction retained (fun _ h => h) := by
  intro locality
  obtain ⟨rule, _, native⟩ := locality.points
  have agreement (b : Bool) := native PUnit.unit b
    (ambient_agrees_scheme true) (RestrictedStructure.Agrees.refl _)
  have bad := congrFun (Option.some.inj ((agreement false).symm.trans (agreement true))) (0 : Int)
  exact Int.zero_ne_one bad

/-- A permitted native shift is not a map described by this scheme's declared identity policy. -/
theorem shifted_native_map_cannot_use_declared_identity :
    let reading := nativeCoefficient true true
    ¬ (reading.scheme.pointPrograms reading.algebra reading.choice).describes PUnit.unit
      (RestrictedStructure.restrict retained (ambient true))
      (reading.scheme.structureOf reading.algebra reading.realization) false
      (reading.realizePoint false ⟨PUnit.unit, rfl⟩) := by
  dsimp only
  rintro ⟨castType, claimed⟩
  have impossible : (1 : Int) = 0 := congrFun claimed (0 : Int)
  exact Int.one_ne_zero impossible

/-- Use the unique native entry of the unshifted scalar scheme. -/
private def uniformNativeCoefficient : CoefficientReading retained (ambient true) retainedProduct :=
  { nativeCoefficient true false with
    scheme := scalarScheme
    realizePoint s hs x :=
      have kept : Declaration.sort s ∈ retained.declarations := by
        obtain ⟨i, rfl⟩ := hs
        exact Set.mem_singleton _
      scalarScheme.nativePoints ⟨integers, RingHom.id Int⟩ () s kept
        ((ambient_agrees_scheme true).carrier_eq s kept ▸ x)
    pointOrigin := .native () rfl (by
      rintro _ ⟨i, rfl⟩
      exact Set.mem_singleton _) (ambient_agrees_scheme true) (fun _ _ _ => rfl) }

/-- A comparison can certify the local rule of a native realization at every retained input. -/
theorem uniform_native_points_have_local_rule :
    uniformNativeCoefficient.RespectsRestriction retained (fun _ h => h) := by
  classical
  let rule : CoefficientReading.LocalPointRule retained :=
    fun X Y s _ => if same : X.carrier s = Y.carrier s then some (cast same) else none
  refine ⟨(fun _ => Set.mem_singleton _), ⟨rule, ?_, ?_⟩, ?_⟩
  · intro i X Y left right
    cases i
    have xs : Int = X.carrier false := left.carrier_eq _ (Set.mem_singleton _)
    have ys : Int = Y.carrier false := right.carrier_eq _ (Set.mem_singleton _)
    change (if same : X.carrier false = Y.carrier false then some (cast same) else none) =
      some (fun x => cast ys (cast xs.symm x))
    rw [dif_pos (xs.symm.trans ys)]
    have composed {K L M : Type} (left : K = L) (right : K = M) (x : L) :
        cast (left.symm.trans right) x = cast right (cast left.symm x) := by
      cases left
      cases right
      rfl
    exact congrArg some (funext (composed xs ys))
  · dsimp only [CoefficientReading.LocalPointRule.AgreesOnNative]
    intro i a
    cases i
    cases a
    intro _ _
    change (if same : Int = Int then some (cast same) else none) = some (fun (x : Int) => x)
    rw [dif_pos rfl]
    rfl
  · rintro left right ⟨same, tuple⟩
    exact (congrFun tuple PUnit.unit).symm

/-- Select the scalar input in its own product. -/
private def scalarInputs (R : Type) [CommRing R] :
    CoefficientReading retained (separateStates R) (.ofList [false]) where
  base := integers
  algebra := ⟨⟨R, inferInstance⟩, Int.castRingHom R⟩
  scheme := scalarScheme
  realization := ()
  selection := .ofRenaming (Δ := [false]) (fun i => i)
  supported i := Set.mem_singleton_iff.2 (congrArg Declaration.sort (List.mem_singleton.1 i.2.sort_mem))
  realizePoint s hs := by
    cases s
    · exact id
    · exact False.elim (by
        obtain ⟨i, hi⟩ := hs
        exact Bool.noConfusion (hi.symm.trans (List.mem_singleton.1 i.2.sort_mem)))
  pointOrigin := .declared PUnit.unit True.intro (by
    intro spot chosen
    cases spot
    · exact ⟨rfl, rfl⟩
    · obtain ⟨i, hi⟩ := chosen
      exact Bool.noConfusion (hi.symm.trans (List.mem_singleton.1 i.2.sort_mem)))
  evaluateOn _ _ _ e := e ⟨false, .here⟩

/-- Read coefficients at the first sort and take the ordinary observation at the second. -/
private def separateReading (R : Type) [CommRing R] : Reading.{0, 0, 0, 0} where
  presentation := presentation
  structureData := separateStates R
  observation := StateObservation.ofSort true Bool id
  context := retained
  cover := ⟨Unit, fun _ => retained, fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := separateStates R
  familyObservation := none
  ValueStructure := fun _ => Unit
  valueStructure := ()
  coefficients := some ⟨.ofList [false], scalarInputs R⟩

/-- Assign distinct ordinary positions to the two sorts. -/
private def twoOrdinarySorts : ObservationProduct signature.SortType := { Index := Bool, sort := id, nameScope := some "two sorts" }

/-- Choose a coefficient position in an independent namespace. -/
private def differentlyNamedInput : CoefficientProduct signature.SortType :=
  .indexed Bool {true} (fun _ => false) (some "two sorts")

/-- Explicitly share the false-sort position across otherwise independent names. -/
private noncomputable def explicitFalsePosition : SharedInputNames twoOrdinarySorts := by
  classical
  refine ⟨fun Γ _ => if Γ = differentlyNamedInput then some false else none, ?_⟩
  intro Γ j k i first second
  by_cases matched : Γ = differentlyNamedInput
  · subst Γ
    exact Subtype.ext ((Set.mem_singleton_iff.1 j.property).trans (Set.mem_singleton_iff.1 k.property).symm)
  · change (if Γ = differentlyNamedInput then some (false : twoOrdinarySorts.Index) else none) = some i at first
    rw [if_neg matched] at first
    cases first

/-- Use a common position name on an incompatible sort. -/
private noncomputable def sameNameDifferentSort : Reading.{0, 0, 0, 0} :=
  { separateReading Int with
    observation := .ofFunction twoOrdinarySorts Int (fun states => states false)
    sharedInputs := explicitFalsePosition
    observationPlacement := .external }

/-- A same-slot coordinate of another sort leaves the compatible explicit sharing available. -/
theorem compatible_explicit_sharing_survives_name_collision :
    sameNameDifferentSort.SharesInput differentlyNamedInput ⟨true, Set.mem_singleton _⟩ false := by
  refine ⟨rfl, Or.inr ⟨?_, ?_, ?_⟩⟩
  · classical
    simp [sameNameDifferentSort, explicitFalsePosition]
  · rintro ⟨i, named⟩
    cases i
    · exact Bool.noConfusion (eq_of_heq named.2.2.2)
    · exact Bool.noConfusion named.1
  · rintro ⟨j, named⟩
    have position : j.val = true := Set.mem_singleton_iff.1 j.property
    exact Bool.noConfusion (position.symm.trans (eq_of_heq named.2.2.2))

/-- Declare a binary total observation on two distinct input sorts. -/
private def observationSignature : Signature :=
  { signature with Total := Unit, totalArity _ := ⟨[false, true], false⟩ }

/-- Use the observation signature without any Law declarations. -/
private def observationPresentation : PrimitivePresentation where
  signature := observationSignature
  laws :=
    { LawName := Empty
      statement := fun n => nomatch n
      role := fun n => nomatch n }
  derived n := nomatch n

/-- Interpret the binary observation as Boolean conjunction. -/
private def pairedStates : Structure observationSignature where
  carrier _ := Bool
  total _ e := e .here && e (.there .here)
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- Read the declared binary operation by name. -/
private def pairedReading : Reading.{0, 0, 0, 0} where
  presentation := observationPresentation
  structureData := pairedStates
  observation := .ofTotalSymbol (.ordinary ())
  context := ReadingOrigin.whole observationPresentation
  cover := ⟨Unit, fun _ => ReadingOrigin.whole observationPresentation, fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := pairedStates
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := none

/-- A declared observation of two different sorts is covered together with both inputs. -/
theorem declared_observation_covers_both_sorts :
    ∃ i, Declaration.total () ∈ (pairedReading.cover.piece i).declarations ∧
      Declaration.sorts [false, true] ⊆ (pairedReading.cover.piece i).declarations := by
  let declared : pairedReading.DeclaredObservation := ⟨.ordinary (), Set.mem_univ _, rfl⟩
  obtain ⟨i, symbol, arity⟩ := declared.covered
  refine ⟨i, symbol, ?_⟩
  rintro _ ⟨s, kept, rfl⟩
  exact arity ⟨s, List.mem_cons_of_mem _ kept, rfl⟩

/-- Both state sorts remain available while the operation declaration is forgotten. -/
private def pairedSorts : DeclarationContext observationPresentation where
  declarations := {d | ∃ s, d = .sort s}
  closed := by
    rintro _ ⟨s, rfl⟩ d source
    exact source.elim

/-- The target has a covering piece for the operation and a separate sorts-only piece. -/
private def splitPairedReading : Reading.{0, 0, 0, 0} :=
  { pairedReading with
    cover :=
      { Index := Bool
        piece := fun full => if full then pairedReading.context else pairedSorts
        subset := fun _ _ _ => Set.mem_univ _
        covers := fun kept => ⟨true, kept⟩ } }

/-- Assign the sorts-only piece while omitting the declared observation operation. -/
private def forgetPairedOperation : ReadingContextChange pairedReading splitPairedReading
    (Interpretation.identity observationPresentation.theory) where
  retained := pairedSorts
  inside := fun _ _ => Set.mem_univ _
  supporting := fun _ => Interpretation.identity observationPresentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces := fun _ => {false}
  localSupport := by
    rintro _ _ ⟨s, rfl⟩ _ d supported
    exact ⟨false, Set.mem_singleton _, ⟨s, Set.mem_singleton_iff.1 supported⟩⟩

/-- Covering the two inputs still does not permit forgetting the selected observation operation. -/
theorem declared_observation_cannot_use_sort_only_assignment :
    ¬ (Reading.ContextCompatibility.changed forgetPairedOperation).retainsChosenSymbols (.identity _) := by
  intro support
  have actual : forgetPairedOperation.ObservationLocations (.identity _) (some (.ordinary ()))
      (some (.ordinary ())) := support
  obtain ⟨j, selected, kept, _⟩ := actual.targetPiece
  rcases selected with ⟨i, assigned⟩ | impossible
  · have choosesFalse : j = false := Set.mem_singleton_iff.1 assigned
    subst j
    obtain ⟨s, impossible⟩ := kept
    cases impossible
  · exact impossible.elim

/-- Use the same binary state function externally, without selecting any declarations. -/
private def externalPairReading : Reading.{0, 0, 0, 0} :=
  { pairedReading with
    observation := StateObservation.ofContext [false, true] Bool (pairedStates.total ())
    context := ⟨∅, fun absent => absent.elim⟩
    cover := ⟨Empty, (fun i => nomatch i), (fun i => nomatch i), (fun absent => absent.elim)⟩
    coefficients := none
    sharedInputs := .empty _
    observationPlacement := .external
    observationDeclared _ named := nomatch named }

/-- The new operation is selected in a target piece, with no source piece to assign. -/
private def declarePairObservation : ReadingContextChange externalPairReading pairedReading
    (Interpretation.identity observationPresentation.theory) where
  retained := externalPairReading.context
  inside _ kept := kept
  supporting := fun _ => Interpretation.identity observationPresentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces i := nomatch i
  addedTargetPieces := Set.univ
  localSupport i := nomatch i

/-- The actual target primitive reads the two external source states on its selected piece. -/
def external_states_feed_new_declared_observation : ReadingComparison externalPairReading pairedReading where
  interpretation := Interpretation.identity observationPresentation.theory
  targetModel n := nomatch n.val
  state :=
    { onSort _ := id
      total_comm := by
        intro f e
        let u := Interpretation.identity observationPresentation.theory
        have model : observationPresentation.theory.Holds pairedStates := fun n => nomatch n.val
        have graph : (u.pullbackStructure pairedStates model).Graph (.total f)
            (e.map (fun _ => id)) (pairedStates.total f e) := by
          apply (u.pullback_graph_iff pairedStates model _ _ _).2
          apply (Term.mem_eval_iff _ _ _ _).1
          apply (Term.holds_graph_iff _ _ _ _).1
          apply (Translation.identityGraph observationPresentation.theory (.total f)).2.sound pairedStates model
          apply (Formula.holds_atom _ _ _).2
          apply (Atomic.holds_graph _ _ _ _ _).2
          exact (pairedStates.graph_total_iff _ _ _).2 rfl
        exact ((Structure.graph_total_iff _ _ _ _).1 graph).symm
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .changed declarePairObservation
  declaredObservations := by
    change declarePairObservation.ObservationLocations (.identity _) none (some (.ordinary ()))
    refine ReadingContextChange.ObservationLocations.targetOnly
      (change := declarePairObservation) (positions := .identity _) (.ordinary ()) () ?_ ?_ ?_
    · exact Or.inr (Set.mem_univ _)
    · exact Set.mem_univ _
    · intro i
      exact Or.inr (Or.inl ⟨rfl, fun absent => absent.elim⟩)
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl
  restrictedObservations := declarePairObservation.observationSquare_of_available _ _ _
    (fun _ => Or.inr (Or.inl ⟨rfl, fun absent => absent.elim⟩))
    (fun _ => Or.inr (Or.inl ⟨rfl, fun absent => absent.elim⟩)) (fun _ => rfl)

/-- The outer product adds a position that the coefficient evaluation never reads. -/
private def paddedScalarInputs (R : Type) [CommRing R] :
    CoefficientReading retained (separateStates R) (.ofList [false, true]) :=
  { scalarInputs R with
    selection := .ofRenaming (Δ := [false]) (fun
      | .here => .here
      | .there i => nomatch i) }

/-- The reading with a longer outer coefficient product still uses only the scalar position. -/
private def paddedReading (R : Type) [CommRing R] : Reading.{0, 0, 0, 0} :=
  { separateReading R with coefficients := some ⟨.ofList [false, true], paddedScalarInputs R⟩ }

/-- Transport the scalar occurrence without supplying the unread Bool position. -/
private def scalarInputMap :
    ReadingInputMap (scalarInputs Int).selection.used (paddedScalarInputs (Int × Int)).selection.used id where
  extra := .empty
  coordinate j := ⟨.inl ⟨⟨false, .here⟩, ⟨false, .here⟩, rfl⟩, by
    obtain ⟨i, hi⟩ := j.property
    change false = j.val.1
    rw [← hi]
    exact (List.mem_singleton.1 i.2.sort_mem).symm⟩
  extra_used i := nomatch i

/-- One structural map induces both squares on their respective input products. -/
def independent_coefficient_comparison :
    ReadingComparison (separateReading Int) (paddedReading (Int × Int)) where
  interpretation := Interpretation.identity presentation.theory
  targetModel := fun name => nomatch name.val
  state :=
    { onSort := fun
        | false => fun x => (x, x)
        | true => id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := .changed scalarInputMap
    { baseMap := RingHom.id Int
      coefficients := (RingHom.id Int).prod (RingHom.id Int)
      algebra_commutes := by
        change (_ : Int →+* (Int × Int)) = _
        exact Subsingleton.elim _ _
      evaluate_commutes _ := rfl }
  coefficientInputs := by
    constructor
    · intro j i _
      obtain ⟨s, v⟩ := i
      cases v with
      | here => rfl
      | there v => exact nomatch v
    refine ⟨(fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i), (fun _ _ k => nomatch k),
      ?_, (fun k => nomatch k), (fun k => nomatch k)⟩
    intro j i share
    obtain ⟨k, hk⟩ := j.property
    have sortEq : j.val.1 = false := by
      rw [← hk]
      exact List.mem_singleton.1 k.2.sort_mem
    have contradiction : false = true := sortEq.symm.trans share.1
    exact Bool.noConfusion contradiction
  value := id
  commutes _ := rfl

/-- The plain reading has no coefficient evaluation. -/
private def plainReading : Reading.{0, 0, 0, 0} := { separateReading Int with coefficients := none }

/-- The new scalar observation evaluates to zero on the selected sort. -/
private def zeroInputs : CoefficientReading retained (separateStates Int) (.ofList [false, true]) :=
  { paddedScalarInputs Int with
    evaluateOn _ R _ _ :=
      letI := R.scalars.ring
      0 }

/-- Introduce a scalar evaluation independent of the originally observed Bool. -/
def independentlyIntroduceCoefficients : Reading.CoefficientCompatibility plainReading
    ({ separateReading Int with coefficients := some ⟨.ofList [false, true], zeroInputs⟩ } : Reading.{0, 0, 0, 0})
    id (fun _ x => x) :=
  ⟨{ extra := .ofSort false
     coordinate := fun j => ⟨.inr PUnit.unit, by
       obtain ⟨i, hi⟩ := j.property
       change false = j.val.1
       rw [← hi]
       exact (List.mem_singleton.1 i.2.sort_mem).symm⟩
     extra_used := fun _ => ⟨⟨⟨false, .here⟩, ⟨false, .here⟩, rfl⟩, rfl⟩ },
    fun _ => (0 : Int), fun _ => rfl⟩

/-- Forget scalar evaluation while reading the independently selected Bool position. -/
def independentlyForgetCoefficients : Reading.CoefficientCompatibility (paddedReading Int)
    ({ plainReading with observation := StateObservation.ofSort true Bool (fun _ => false) } : Reading.{0, 0, 0, 0})
    id (fun _ x => x) :=
  .compare
    ⟨{ extra := .ofSort true
       coordinate := fun i => ⟨.inr i, rfl⟩
       extra_used := fun i => ⟨i, rfl⟩ },
     fun _ => false, fun _ => rfl⟩

/-- Choose the same coefficient rule while varying the ordinary position's name. -/
private def scalarWithOrdinaryName (scope : Option String) : Reading.{0, 0, 0, 0} :=
  { separateReading Int with
    observation := StateObservation.ofContext [false] Int (fun e => e .here) scope
    coefficients := some ⟨.ofList [false], scalarInputs Int⟩
    sharedInputs := .empty _
    observationPlacement := .external
    observationDeclared _ named := nomatch named }

/-- Match corresponding ordinary positions before changing their sharing specification. -/
private def independentToShared : (scalarWithOrdinaryName none).observation.product.Correspondence
    (scalarWithOrdinaryName (some "typed variables")).observation.product id where
  position := id
  sort_eq _ := rfl
  keepsNamed _ _ named _ _ _ := (named rfl).elim

/-- Fixed coefficient settings cannot make two independent source states supply one shared target state. -/
theorem fixed_parameters_cannot_invent_ordinary_share
    (same : (scalarInputs Int).SameParameters (scalarInputs Int)) :
    ¬ (CoefficientComparison.fixed (onSort := id) (state := fun _ => id) same).UsesInputs
      independentToShared
      ((scalarWithOrdinaryName none).SharesInput (.ofList [false]))
      ((scalarWithOrdinaryName (some "typed variables")).SharesInput (.ofList [false])) := by
  intro shares
  let original : (CoefficientProduct.ofList [false]).product.Index := ⟨false, .here⟩
  let selected : (scalarInputs Int).selection.used.Index := ⟨original, ⟨false, .here⟩, rfl⟩
  have shared : (scalarWithOrdinaryName (some "typed variables")).SharesInput (.ofList [false]) original
      ⟨false, .here⟩ := ⟨rfl, Or.inl ⟨rfl, by decide, rfl, HEq.rfl⟩⟩
  obtain ⟨_, _, _, named | explicit⟩ := shares selected ⟨false, .here⟩ shared
  · have impossible : (some "typed variables" : Option String) = none := named.2.2.1
    cases impossible
  · cases explicit.1

/-- Keep the actual ordinary state as an external input to the coefficient introduction. -/
private def externalScalarSource : Reading.{0, 0, 0, 0} :=
  { scalarWithOrdinaryName none with
    context := ⟨∅, fun absent => absent.elim⟩
    cover := ⟨Empty, (fun i => nomatch i), (fun i => nomatch i), (fun absent => absent.elim)⟩
    coefficients := none
    observationPlacement := .external
    observationDeclared _ named := nomatch named }

/-- Select the target context independently, without retaining any source declarations. -/
private def introduceScalarContext :
    ReadingContextChange externalScalarSource (scalarWithOrdinaryName none)
      (Interpretation.identity presentation.theory) where
  retained := externalScalarSource.context
  inside _ kept := kept
  supporting := fun _ => Interpretation.identity presentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces i := nomatch i
  addedTargetPieces := Set.univ
  localSupport i := nomatch i

/-- Both evaluations use the original source coordinate, with no additional states. -/
private def externalScalarInputs : ReadingInputMap externalScalarSource.observation.product
    (scalarInputs Int).selection.used id where
  extra := .empty
  coordinate j := ⟨.inl j.val, rfl⟩
  extra_used i := nomatch i

/-- The ordinary positions remain available while the target selects a coefficient realization. -/
private theorem externalScalarInputAvailable (i : externalScalarSource.observation.product.Index) :
    i ∈ introduceScalarContext.observationInputs :=
  Or.inr (Or.inl ⟨rfl, fun absent => absent.elim⟩)

/-- Introduce an actual coefficient evaluation on the external input, using its selected target cover. -/
def external_state_feeds_new_coefficient_evaluation :
    ReadingComparison externalScalarSource (scalarWithOrdinaryName none) where
  interpretation := Interpretation.identity presentation.theory
  targetModel n := nomatch n.val
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .changed introduceScalarContext
  coefficientChange := ⟨externalScalarInputs, id, fun _ => rfl⟩
  coefficientInputs := by
    refine ⟨(fun _ _ common => (common.1 rfl).elim), ?_⟩
    refine ⟨(fun k => nomatch k), (fun k => nomatch k), (fun k => nomatch k),
      (fun _ _ k => nomatch k), ?_, (fun k => nomatch k), (fun k => nomatch k)⟩
    intro _ _ shared
    rcases shared.2 with named | explicit
    · cases named.2.2.1
    · cases explicit.1
  coefficientSupport := by
    have all := Set.Subset.antisymm introduceScalarContext.targetRetained_inside
      (fun _ kept => ⟨(), Or.inr (Set.mem_univ _), kept⟩)
    refine ⟨?_, Or.inl all⟩
    intro input
    left
    rw [all]
    obtain ⟨coordinate, identical⟩ := input.property
    rw [← identical]
    exact (scalarInputs Int).supported coordinate
  value := id
  commutes _ := rfl
  restrictedObservations :=
    ⟨fun e => e ⟨⟨false, .here⟩, externalScalarInputAvailable _⟩,
      fun e => e ⟨⟨false, .here⟩, externalScalarInputAvailable _⟩,
      ⟨(fun _ => rfl), Or.inl (StateObservation.restriction_surjective_of_nonempty _ _
        ⟨ObservationProduct.ofAssignment (Assignment.cons (0 : Int) Assignment.empty)⟩)⟩,
      ⟨(fun _ => rfl), Or.inl (StateObservation.restriction_surjective_of_nonempty _ _
        ⟨ObservationProduct.ofAssignment (Assignment.cons (0 : Int) Assignment.empty)⟩)⟩,
      (fun _ => rfl), ⟨(fun _ i _ => externalScalarInputAvailable i), fun _ => rfl⟩⟩

end SHIGURE.Chapter1.RetainedCoefficientInputs

namespace SHIGURE.Chapter1.AdditionalCoefficientInputs

/-- A single original named position with the specified source sort. -/
private def slot {S : Type} (s : S) : ObservationProduct S where
  Index := Unit
  sort := fun _ => s
  nameScope := some "coefficient"

/-- Supply the only target position from an additional original input. -/
private def additional {S T : Type} {s : S} (f : S → T) :
    ReadingInputMap (ObservationProduct.empty : ObservationProduct S) (slot (f s)) f where
  extra := slot s
  coordinate _ := ⟨.inr (), rfl⟩
  extra_used _ := ⟨(), rfl⟩

/-- Even when two sorts have the same image, a name cannot change its original sort. -/
theorem extra_cannot_change_original_sort :
    ¬ (additional (s := true) (fun _ => ())).PreservesNames (slot false) (fun i => nomatch i) := by
  intro preserves
  have same := preserves () () ⟨by decide, rfl, HEq.rfl, rfl⟩
  exact Bool.noConfusion same.2.1

/-- Use two independent ordinary positions of the same sort. -/
private def ordinaryPair : ObservationProduct Unit where
  Index := Bool
  sort := fun _ => ()

/-- Identify the original coefficient position with the first ordinary position. -/
private def sharesFirst (_ : Unit) (j : ordinaryPair.Index) : Prop := j = false
/-- Identify the target coefficient position with the second ordinary position. -/
private def sharesSecond (_ : Unit) (j : ordinaryPair.Index) : Prop := j = true

/-- An additional input can restore the original named coordinate with its original sort. -/
theorem extra_can_restore_unused_name :
    (additional (s := ()) id).PreservesNames (slot ()) (fun i => nomatch i) := by
  rintro ⟨⟩ ⟨⟩ _
  refine ⟨?_, rfl, rfl, HEq.rfl⟩
  rintro ⟨i, _⟩
  exact nomatch i

/-- The identity input map needs its actual source coordinate. -/
theorem unavailable_source_position_cannot_be_used :
    ¬ (ReadingInputMap.identity (slot ())).UsesOnly ∅ :=
  fun uses => (uses () () rfl).elim

/-- Restoring an unused coordinate still shares its actual original ordinary position. -/
theorem extra_keeps_original_sharing :
    (additional (s := ()) id).RespectsOrdinary (.identity ordinaryPair) (slot ())
      (fun i => nomatch i) sharesFirst sharesFirst (fun _ retained => retained = some false) := by
  refine ⟨fun _ => some false, (fun _ _ _ => rfl), ?_, ?_, ?_, (fun _ => rfl), ?_⟩
  · rintro ⟨⟩ ⟨⟩ _ _ _
    rfl
  · intro j i k _ _ o
    exact ⟨fun h => (Option.some.inj h).symm, fun h => congrArg some h.symm⟩
  · intro j i h
    refine ⟨congrArg some h.symm, ?_⟩
    rintro ⟨x, _⟩
    exact nomatch x
  · rintro ⟨⟩ i link
    cases Option.some.inj link
    exact Or.inl ⟨(), false, rfl, rfl, rfl⟩

/-- Sharing with the second ordinary position contradicts the original share with the first. -/
theorem extra_cannot_reassign_original_sharing :
    ¬ (additional (s := ()) id).RespectsOrdinary (.identity ordinaryPair) (slot ())
      (fun i => nomatch i) sharesFirst sharesSecond := by
  rintro ⟨extraShares, _, _, original, follows, _⟩
  have wrong := (follows () true rfl).1
  have same := original () () () ⟨by decide, rfl, HEq.rfl, rfl⟩ rfl true
  exact Bool.noConfusion (same.mp wrong)

/-- Access to another coordinate of the same sort cannot justify the actual share. -/
theorem extra_cannot_borrow_access_from_other_coordinate :
    ¬ (additional (s := ()) id).RespectsOrdinary (.identity ordinaryPair) (slot ())
      (fun i => nomatch i) sharesFirst sharesFirst (fun _ retained => retained = some true) := by
  rintro ⟨extraShares, _, _, _, follows, available, _⟩
  exact Bool.noConfusion (Option.some.inj ((follows () false rfl).1.symm.trans (available ())))

/-- A new coordinate with no shared name or target position cannot invent a provenance. -/
theorem extra_cannot_invent_a_share :
    ¬ (additional (s := ()) id).RespectsOrdinary (.identity ordinaryPair) .empty
      (fun i => nomatch i) (fun _ _ => False) (fun _ _ => False)
      (fun _ retained => retained = some false) := by
  rintro ⟨extraShares, _, _, _, _, access, origin⟩
  rcases origin () false (access ()) with ⟨_, _, impossible, _, _⟩ | ⟨_, _, _, impossible, _⟩
  exacts [impossible, impossible]

/-- In a joint input, a coefficient coordinate linked to false cannot be supplied as true. -/
theorem shared_extra_cannot_supply_a_different_value :
    let ordinaryValues : (ordinaryPair.restrict Set.univ).Values (fun _ => Bool) := fun _ => false
    ∀ joint : (additional (s := ()) id).SharedValues ordinaryValues (fun _ _ => False) (fun _ => some false),
      joint.input.2 () = false := by
  intro ordinaryValues joint
  exact eq_of_heq (joint.extra_eq () ⟨false, Set.mem_univ _⟩ rfl)

/-- The second target coordinate uses an additional state of the other sort. -/
private def twoTargetInputs : ObservationProduct Bool :=
  { Index := Bool, sort := id }

/-- Use the left source state for the retained target coordinate and an extra for the other. -/
private def additionalForSecond : ReadingInputMap (.ofSort false) twoTargetInputs id where
  extra := .ofSort true
  coordinate
    | false => ⟨.inl PUnit.unit, rfl⟩
    | true => ⟨.inr PUnit.unit, rfl⟩
  extra_used i := by cases i; exact ⟨true, rfl⟩

/-- The unused additional state has an empty carrier. -/
private def inputCarrier : Bool → Type
  | false => Int
  | true => Empty

/-- The retained target coordinate still has a value when the excluded extra carrier is empty. -/
theorem discarded_target_needs_no_extra_state :
    IsEmpty (additionalForSecond.Values inputCarrier) ∧
      ∃ extra : (additionalForSecond.extra.restrict (additionalForSecond.usedExtra {false})).Values inputCarrier,
        additionalForSecond.mapToRestrictedTarget (fun _ => id) ((fun _ => (7 : Int)), extra)
          ⟨false, Set.mem_singleton _⟩ = (7 : Int) := by
  refine ⟨⟨fun input => (input.2 PUnit.unit).elim⟩, ?_⟩
  let extra : (additionalForSecond.extra.restrict (additionalForSecond.usedExtra {false})).Values inputCarrier :=
    fun i => False.elim (by
      obtain ⟨j, kept, supplied⟩ := i.property
      have first : j = false := Set.mem_singleton_iff.1 kept
      subst j
      cases supplied)
  exact ⟨extra, rfl⟩

end SHIGURE.Chapter1.AdditionalCoefficientInputs

namespace SHIGURE.Chapter1.IndexedObservation

/-- Countably many state sorts without primitive operations or Laws. -/
private def signature : Signature where
  SortType := Nat
  Total := Empty
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity f := nomatch f
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- Each state sort has two independently observable values. -/
private def states : Structure signature where
  carrier _ := Bool
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- No Laws constrain these coordinates. -/
private def presentation : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Empty
      statement n := nomatch n
      role n := nomatch n }
  derived n := nomatch n

/-- Observe the whole function of Boolean states, with one position of every sort. -/
private def reading : Reading.{0, 0, 0, 0} where
  presentation := presentation
  structureData := states
  observation := .ofFunction { Index := Nat, sort := id } (Nat → Bool) id
  context := ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩
  cover := ⟨Unit, fun _ => ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩,
    fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := states
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := none

/-- The comparison acts on the Boolean state at every natural-number position. -/
def all_sorts_comparison : ReadingComparison reading reading where
  interpretation := Interpretation.identity presentation.theory
  targetModel n := nomatch n.val
  state :=
    { onSort := fun _ => Bool.not
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value e := fun n => !(e n)
  commutes _ := rfl

/-- The observed comparison computes the complement at every coordinate. -/
theorem all_sorts_comparison_at (e : Nat → Bool) (n : Nat) :
    (reading.observation.read (all_sorts_comparison.contexts.mapValues all_sorts_comparison.state.onSort e)) n =
      !(e n) :=
  congrFun (all_sorts_comparison.commutes e) n

/-- Select no declarations for the external observation. -/
private def emptyContext : DeclarationContext presentation :=
  ⟨∅, fun absent => absent.elim⟩

/-- Observe an external state without making its sort part of the declaration selection. -/
private def externalReading (s : Nat) : Reading.{0, 0, 0, 0} :=
  { reading with
    observation := StateObservation.ofSort s Bool id
    context := emptyContext
    cover := ⟨Empty, (fun i => nomatch i), (fun i => nomatch i), (fun absent => absent.elim)⟩
    coefficients := none
    sharedInputs := .empty _
    observationPlacement := .external
    observationDeclared _ named := nomatch named }

/-- Interpret the signature by shifting every natural-number sort to its successor. -/
private def successor : Interpretation presentation.theory presentation.theory where
  onSort := Nat.succ
  translation :=
    { operation op := match op with
        | .total f => nomatch f
        | .partialOp p => nomatch p
        | .quantity q => nomatch q
      relation r := nomatch r
      partialDomain p := nomatch p }
  total f := nomatch f
  quantity q := nomatch q
  partialDefined p := nomatch p
  definedPartial p := nomatch p
  preserves n := nomatch n.val

/-- A comparison can move the observed sort by a nonidentity interpretation at fixed selections. -/
def nonidentity_at_fixed_context : ReadingComparison (externalReading 0) (externalReading 1) where
  interpretation := successor
  targetModel n := nomatch n.val
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := ⟨id, fun _ => rfl, fun _ _ named => (named rfl).elim⟩
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl

/-- Adding a declaration at the target keeps access to the external state being observed. -/
def external_stays_available_when_declarations_are_added :
    ReadingComparison (externalReading 0)
      { externalReading 1 with
        context := reading.context
        cover := reading.cover
        coefficients := none
        observationPlacement := .retained (fun _ => Set.mem_univ _)
        observationDeclared _ named := nomatch named } :=
  { nonidentity_at_fixed_context with
    declarationChange := .changed
      { retained := emptyContext
        inside _ h := h
        supporting := fun _ => successor
        equivalent := fun _ => Interpretation.Equivalent.refl _
        addedTargetPieces := Set.univ
        pieces i := nomatch i
        localSupport i := nomatch i }
    observationSupport := ⟨False.elim, fun _ _ =>
      ⟨Or.inr (Or.inl ⟨rfl, fun h => h.elim⟩), ⟨(), Or.inr (Set.mem_univ _), Set.mem_univ _⟩⟩⟩
    declaredObservations := .external
    restrictedObservations := ReadingContextChange.observationSquare_of_available _ _ _ _
      (fun _ => Or.inr (Or.inl ⟨rfl, fun h => h.elim⟩))
      (fun _ => Or.inr (Or.inl ⟨rfl, fun h => h.elim⟩)) (fun _ => rfl) }

end SHIGURE.Chapter1.IndexedObservation
