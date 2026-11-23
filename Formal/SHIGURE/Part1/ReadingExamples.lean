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
  supporting := Interpretation.identity presentation.theory
  sameSorts := rfl
  sameTranslation := HEq.rfl
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

/-- An equivalent representative conjoins truth with both original relations. -/
private def alternateIdentity : Interpretation presentation.theory presentation.theory where
  onSort := id
  translation :=
    { operation := fun op => match op with
        | .total f => nomatch f
        | .quantity q => nomatch q
        | .partialOp p => nomatch p
      relation := fun r => ((Translation.identity signature).relation r).conj .truth
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
    exact ⟨⟨.andLeft _ _⟩, ⟨.andIntro (.refl _) (.truth _)⟩⟩
  · intro p
    exact nomatch p

/-- Changing the representative of the identity still admits a fixed declaration comparison. -/
def alternate_fixed_context : source.ContextCompatibility source alternateIdentity :=
  .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ alternateIdentity_equivalent

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

/-- The deliberately unassigned relation cannot be read in the assigned target pieces. -/
theorem other_relation_is_not_assigned :
    Declaration.relation true ∉ (coverChange.targetPiece ()).declarations := by
  rintro ⟨i, hi, h⟩
  have same : i = true := Set.mem_singleton_iff.1 hi
  subst i
  change Declaration.relation (P := presentation) true = Declaration.sort () ∨
    Declaration.relation (P := presentation) true = Declaration.relation false at h
  rcases h with impossible | impossible <;> cases impossible

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
    lawModelScheme.IsModel R true ∧ ¬ lawModelScheme.IsModel R false := by
  constructor
  · intro name kept e holds
    exact Set.mem_univ _
  · intro model
    exact (model ⟨(), rfl⟩ (Set.mem_univ _) Assignment.empty True.intro).elim

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
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
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

private theorem retained_carrier_eq (source target : Bool) (s : signature.SortType)
    (kept : Declaration.sort s ∈ retained.declarations) :
    (realized source).carrier s = (realized target).carrier s := by
  cases retained_sort s kept
  rfl

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

private theorem ambient_agrees (source target : Bool) : (realized source).Agrees (realized target) :=
  ⟨retained_carrier_eq source target, retained_preserves _ _ _, retained_preserves _ _ _⟩

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
  pointOrigin := .declared True.intro
  evaluateOn R _ e := R.fromBase (e ⟨false, .here⟩)

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

private def retainedProduct : CoefficientProduct signature.SortType := .all (.ofSort false)

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
  evaluateOn _ _ e := e PUnit.unit

/-- Forgetting a carrier preserves the fixed application of the same native rule. -/
theorem fixed_native_ignores_forgotten_carrier :
    (nativeCoefficient true false).SameParameters (nativeCoefficient false false) := by
  refine ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl, Or.inr ⟨HEq.rfl, ?_⟩, HEq.rfl⟩
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
  pointOrigin := .declared True.intro
  evaluateOn _ _ e := e ⟨false, .here⟩

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
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
  coefficientChange := .changed scalarInputMap
    { baseMap := RingHom.id Int
      coefficients := (RingHom.id Int).prod (RingHom.id Int)
      algebra_commutes := by
        change (_ : Int →+* (Int × Int)) = _
        exact Subsingleton.elim _ _
      evaluate_commutes _ := rfl }
  coefficientInputs := by
    refine ⟨(fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i), ?_⟩
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
    evaluateOn R _ _ :=
      letI := R.scalars.ring
      0 }

/-- Introduce a scalar evaluation independent of the originally observed Bool. -/
def independentlyIntroduceCoefficients : Reading.CoefficientCompatibility plainReading
    ({ separateReading Int with coefficients := some ⟨.ofList [false, true], zeroInputs⟩ } : Reading.{0, 0, 0, 0})
    id (fun _ x => x) :=
  .compare
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

end SHIGURE.Chapter1.RetainedCoefficientInputs

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
  observation := ⟨⟨Nat, id⟩, Nat → Bool, id⟩
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
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
  coefficientChange := PUnit.unit
  value e := fun n => !(e n)
  commutes _ := rfl

/-- The observed comparison computes the complement at every coordinate. -/
theorem all_sorts_comparison_at (e : Nat → Bool) (n : Nat) :
    (reading.observation.read (all_sorts_comparison.contexts.mapValues all_sorts_comparison.state.onSort e)) n =
      !(e n) :=
  congrFun (all_sorts_comparison.commutes e) n

end SHIGURE.Chapter1.IndexedObservation
