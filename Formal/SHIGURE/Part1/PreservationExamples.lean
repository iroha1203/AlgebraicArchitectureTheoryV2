import Formal.SHIGURE.Part1.IdentityInterpretation
import Formal.SHIGURE.Part1.StructureMaps
import Formal.SHIGURE.Part1.Chapter1Examples
import Formal.SHIGURE.Part1.Reading
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Int.Cast.Lemmas

/-! # Example 1.10: partial domains and Law antecedents -/

namespace SHIGURE.Chapter1.DomainTransport

/-- A constant and a single partial endomorphism of one sort. -/
def signature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Unit
  Quantity := Empty
  totalArity := fun _ => ⟨[], ()⟩
  relInputs := fun r => nomatch r
  partialArity := fun _ => ⟨[()], ()⟩
  quantityArity := fun q => nomatch q

/-- The constant is one, and the partial operation acts as the identity where defined. -/
def realization (fullDomain : Bool) : Structure signature where
  carrier := fun _ => Bool
  total := fun _ _ => true
  relation := fun r => nomatch r
  partialDomain := fun _ => {xs | fullDomain = true ∨ xs.head = false}
  partialValue := fun _ xs => xs.val.head
  quantity := fun q => nomatch q

/-- The source structure has both points in the domain. -/
abbrev A := realization true

/-- The target structure has only zero in the domain. -/
abbrev B := realization false

/-- The term for the constant one. -/
def constant {Γ : List Unit} : Term signature Γ () :=
  Term.app (sig := signature) (.total ()) (@Term.argsNil signature Γ)

/-- Apply the partial operation at the input term. -/
def partialTerm {Γ : List Unit} (t : Term signature Γ ()) : Term signature Γ () :=
  Term.app (sig := signature) (.partialOp ()) (t.argsCons Term.argsNil)

/-- Evaluation of the constant requires no input values. -/
theorem evaluates_constant (fullDomain : Bool) {Γ : List Unit}
    (e : Assignment (realization fullDomain).carrier Γ) :
    constant.Evaluates (realization fullDomain) e true :=
  (Term.evaluates_app_at (sig := signature) (.total ()) (@Term.argsNil signature Γ) _ e Assignment.empty
    (fun i => nomatch i) true).2 ((Structure.graph_total_iff _ _ _ _).2 rfl)

/-- At a given value, the partial term evaluates exactly when that value is in its domain and
is the claimed output. -/
theorem evaluates_partial_from_value (fullDomain : Bool) {Γ : List Unit}
    {t : Term signature Γ ()} {e : Assignment (realization fullDomain).carrier Γ} {x y : Bool}
    (hx : t.Evaluates (realization fullDomain) e x) :
    (partialTerm t).Evaluates (realization fullDomain) e y ↔
      (fullDomain = true ∨ x = false) ∧ x = y := by
  let xs : Assignment (realization fullDomain).carrier [()] := Assignment.cons x Assignment.empty
  have hArgs : ∀ {s} (i : Var [()] s),
      (t.argsCons Term.argsNil i).Evaluates (realization fullDomain) e (xs i) := by
    intro s i
    cases i with
    | here => exact hx
    | there previous => nomatch previous
  refine (Term.evaluates_app_at (sig := signature) (.partialOp ())
    (t.argsCons Term.argsNil) _ e xs hArgs y).trans ?_
  rw [Structure.graph_partial_iff]
  exact ⟨fun ⟨hd, hy⟩ => ⟨hd, hy⟩, fun ⟨hd, hy⟩ => ⟨hd, hy⟩⟩

/-- The closed equation at one in Example 1.10(a). -/
def atConstant : Law signature := Law.equality (partialTerm (constant (Γ := []))) constant

/-- The closed equality holds in the source structure. -/
theorem atConstant_holds_A : atConstant.Holds A := by
  apply (Law.holds_equality_iff _ _ _).2
  intro e
  exact ⟨true, (evaluates_partial_from_value true (evaluates_constant true e)).2 ⟨.inl rfl, rfl⟩,
    evaluates_constant true e⟩

/-- At one the target partial operation is undefined, so the closed equality fails. -/
theorem atConstant_fails_B : ¬ atConstant.Holds B := by
  intro h
  obtain ⟨y, hp, _⟩ := (Law.holds_equality_iff _ _ _).1 h Assignment.empty
  rcases ((evaluates_partial_from_value false (evaluates_constant false Assignment.empty)).1 hp).1
    with impossible | impossible <;> cases impossible

/-- The state identity from A to B cannot preserve the partial domain at one. -/
theorem identity_cannot_preserve_domain :
    ¬ ∃ h : StructureMap A B, ∀ (s : Unit) (x : Bool), h.onSort s x = x := by
  rintro ⟨h, onPoints⟩
  let e : Assignment A.carrier [()] := Assignment.cons true Assignment.empty
  have member := h.partial_mem () e (Or.inl rfl)
  change false = true ∨ h.onSort () true = false at member
  rw [onPoints] at member
  rcases member with impossible | impossible <;> cases impossible

/-- The reverse map keeps the two states and preserves both clauses of (1.9) at zero. -/
def includePartialDomain : StructureMap B A where
  onSort := fun _ x => x
  total_comm _ _ := rfl
  relation_mem r := nomatch r
  partial_mem _ _ _ := Or.inl rfl
  partial_comm _ _ := rfl
  quantity_comm q := nomatch q

/-- The reversed state map preserves the existing partial value at zero. -/
theorem zero_evaluation_transports :
    (partialTerm (.var .here)).Evaluates A
      ((Assignment.cons (X := B.carrier) false Assignment.empty).map includePartialDomain.onSort)
      (includePartialDomain.onSort () false) := by
  let e : Assignment B.carrier [()] := Assignment.cons false Assignment.empty
  have hv : (Term.var Var.here).Evaluates B e false := rfl
  exact includePartialDomain.evaluates_map _ e false
    ((evaluates_partial_from_value false hv).2 ⟨Or.inr rfl, rfl⟩)

/-- The Law in the target theory only requires equality on the designated domain. -/
def guarded : Law signature :=
  ⟨[()], .atom (.domain () (fun i => i)),
    Formula.termEq (partialTerm (.var .here)) (.var .here)⟩

/-- The source theory requires the same equality on the entire carrier. -/
def unrestricted : Law signature := Law.equality (Γ := [()]) (partialTerm (.var .here)) (.var .here)

/-- A one-Law theory in the common signature. -/
def theoryOf (condition : Law signature) : Theory where
  signature := signature
  LawName := Unit
  law := fun _ => condition

/-- On the designated domain, the target identity operation yields the input value. -/
theorem guarded_holds_B : (theoryOf guarded).Holds B := by
  intro name e he
  apply (Formula.holds_termEq _ _ _ _).2
  have hvar : (Term.var Var.here).Evaluates B e (e Var.here) := rfl
  exact ⟨e Var.here, (Term.mem_eval_iff _ _ _ _).2
    ((evaluates_partial_from_value false hvar).2 ⟨he, rfl⟩),
    (Term.mem_eval_iff _ _ _ _).2 hvar⟩

/-- The same equality on all points fails in the target at one. -/
theorem unrestricted_fails_B : ¬ unrestricted.Holds B := by
  intro h
  let e : Assignment B.carrier [()] := Assignment.cons true Assignment.empty
  obtain ⟨y, hp, _⟩ := (Law.holds_equality_iff _ _ _).1 h e
  have hvar : (Term.var Var.here).Evaluates B e true := rfl
  rcases ((evaluates_partial_from_value false hvar).1 hp).1 with impossible | impossible <;>
    cases impossible

/-- The identity replacement cannot derive the translated unrestricted Law from the guard. -/
theorem identity_translation_not_interpretation :
    ¬ ∃ u : Interpretation (theoryOf unrestricted) (theoryOf guarded),
      ∃ h : u.onSort = id, (h ▸ u.translation) = Translation.identity signature := by
  rintro ⟨u, h, identityData⟩
  cases u with
  | mk sortMap translation total quantity partialDefined definedPartial preserves =>
    cases h
    cases identityData
    let T := theoryOf guarded
    have source := Translation.identityFormula T unrestricted.input
    have target := Translation.identityFormula T unrestricted.conclusion
    let raw := Derivation.cut source.2 (Derivation.cut (preserves ()) target.1)
    apply unrestricted_fails_B
    intro e he
    let e' : Assignment B.carrier [()] := e
    let ρ : Renaming ([()] : List Unit) [()] :=
      fun i => Var.mapSorts id (Γ := [()]) i
    have pull_eq : e'.pull ρ = e := by
      apply Assignment.ext
      intro s i
      change Var [()] s at i
      cases i with
      | here => rfl
      | there previous => nomatch previous
    have hin : (unrestricted.input.rename ρ).Holds B e' :=
      (Formula.holds_rename B _ _ e').2 (pull_eq.symm ▸ he)
    have hout := (Formula.holds_rename B _ _ e').1 (raw.sound B guarded_holds_B e' hin)
    exact pull_eq ▸ hout

/-- Keeping the guarded Law on both sides gives an actual identity interpretation. -/
def guardedIdentity : Interpretation (theoryOf guarded) (theoryOf guarded) :=
  Interpretation.identity _

/-- Two declared Laws record the unrestricted premise and its guarded consequence. -/
private def lawDeclarations : LawDeclarations signature where
  LawName := Bool
  statement := fun name => if name then guarded else unrestricted
  role := fun name => if name then .derived else .required

/-- The unrestricted Law derives its guarded version using one required premise. -/
private def withDerivedLaw : PrimitivePresentation where
  signature := signature
  laws := lawDeclarations
  derived name h := by
    cases name
    · cases h
    · let name : lawDeclarations.toTheory.LawName := ⟨false, rfl⟩
      exact .cut (.truth _) (.required name)

/-- The guarded Law has a derivation from the designated theory of its presentation. -/
def guardedDerived :
    Derivation withDerivedLaw.theory guarded.input guarded.conclusion :=
  withDerivedLaw.derived true rfl

/-- A declaration context cannot retain the constant while omitting its output sort. -/
theorem constant_without_its_sort_is_not_closed :
    ¬ ∃ U : DeclarationContext withDerivedLaw,
      U.declarations = ({Declaration.total ()} : Set (Declaration withDerivedLaw)) := by
  rintro ⟨U, onlyConstant⟩
  have hf : Declaration.total () ∈ U.declarations := onlyConstant.symm ▸ (Set.mem_singleton _)
  have hs : Declaration.sort () ∈ U.declarations :=
    U.closed hf ⟨(), List.mem_cons_self, rfl⟩
  rw [onlyConstant] at hs
  cases Set.mem_singleton_iff.1 hs

/-- The full declaration selection contains the interpreted graph of the constant. -/
private def whole : DeclarationContext withDerivedLaw :=
  ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩

/-- Local graph evaluation reads the retained constant's actual value at one. -/
theorem restricted_constant_holds :
    let e : Assignment A.carrier [()] := Assignment.cons true Assignment.empty
    let a : Atomic signature [()] := .graph (.total ()) (fun i => nomatch i) .here
    (RestrictedEvaluation.restrict whole A).atomic e a (fun _ _ => Set.mem_univ _) := by
  dsimp only
  apply (RestrictedEvaluation.restrict_atomic_iff _ _ _ _ _).2
  exact (Structure.graph_total_iff (sig := signature) A () _ _).2 rfl

/-- A source variable is replaced by the partial term at the constant one. -/
private def substituteAtOne : Substitution signature [()] [] where
  get
    | .here => partialTerm constant
    | .there i => nomatch i

/-- The sole variable is absent from both formulas. -/
private def unusedLaw : Law signature := ⟨[()], .truth, .truth⟩

/-- Undefined replacements remove inputs even when the Law never mentions the replaced variable. -/
theorem unused_variable_still_requires_definedness :
    Assignment.empty ∈ (unusedLaw.substitute substituteAtOne).inputSet A ∧
      Assignment.empty ∉ (unusedLaw.substitute substituteAtOne).inputSet B := by
  constructor
  · have h : Assignment.empty ∈ substituteAtOne.domain A := by
      intro s i
      cases i with
      | here =>
        exact ⟨true, (evaluates_partial_from_value true (evaluates_constant true _)).2 ⟨.inl rfl, rfl⟩⟩
      | there i => nomatch i
    exact (unusedLaw.mem_inputSet_substitute _ A _).2 ⟨h, True.intro⟩
  · intro h
    obtain ⟨hd, _⟩ := (unusedLaw.mem_inputSet_substitute _ B _).1 h
    obtain ⟨y, he⟩ := hd Var.here
    rcases ((evaluates_partial_from_value false (evaluates_constant false _)).1 he).1
      with impossible | impossible <;> cases impossible

/-- A constant replacement can ignore its argument's value, but the application remains strict. -/
private def ignoringApplication : Term signature [] () :=
  (constant (Γ := [()])).applyStrict ((partialTerm (constant (Γ := []))).argsCons Term.argsNil)

/-- The ignored argument still prevents evaluation at the target's undefined input. -/
theorem strict_application_requires_unused_value :
    ignoringApplication.Evaluates A Assignment.empty true ∧
      ¬ ∃ y, ignoringApplication.Evaluates B Assignment.empty y := by
  constructor
  · apply (Term.evaluates_applyStrict _ _ _ _ _).2
    let xs : Assignment A.carrier [()] := Assignment.cons true Assignment.empty
    refine ⟨xs, ?_, evaluates_constant true xs⟩
    intro s i
    cases i with
    | here => exact (evaluates_partial_from_value true (evaluates_constant true _)).2 ⟨.inl rfl, rfl⟩
    | there i => nomatch i
  · rintro ⟨y, he⟩
    obtain ⟨xs, hx, _⟩ := (Term.evaluates_applyStrict _ _ _ _ _).1 he
    rcases ((evaluates_partial_from_value false (evaluates_constant false _)).1 (hx Var.here)).1
      with impossible | impossible <;> cases impossible

end SHIGURE.Chapter1.DomainTransport

namespace SHIGURE.Chapter1.Observation

/-- A single sort with no operation or relation symbols isolates the observation equation. -/
private def signature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity := fun f => nomatch f
  relInputs := fun r => nomatch r
  partialArity := fun p => nomatch p
  quantityArity := fun q => nomatch q

/-- The presentation has no Law declarations. -/
private def presentation : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Empty
      statement := fun i => nomatch i
      role := fun i => nomatch i }
  derived i := nomatch i

/-- The sole sort has the Boolean carrier. -/
private def points : Structure signature where
  carrier := fun _ => Bool
  total := fun f => nomatch f
  relation := fun r => nomatch r
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := fun q => nomatch q

/-- Every declaration is retained in the observation example. -/
private def whole : DeclarationContext presentation :=
  ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩

/-- The readings share the structure and differ only in what their state observation returns. -/
private def reading (observe : Bool → Bool) : Reading.{0, 0, 0, 0} where
  presentation := presentation
  structureData := points
  observation := StateObservation.ofSort () Bool observe
  context := whole
  cover :=
    { Index := Unit
      piece := fun _ => whole
      subset := fun _ _ h => h
      covers := fun h => ⟨(), h⟩ }
  Family := Bool
  realize := fun _ => points
  familyObservation := some ⟨Bool, id⟩
  ValueStructure := fun _ => Unit
  valueStructure := ()
  coefficients := none

/-- The model proof is vacuous because the presentation declares no Laws. -/
private theorem model : presentation.theory.Holds points :=
  fun name => nomatch name.val

/-- The state comparison fixes both points in the pulled-back Boolean carrier. -/
private def state : StructureMap points
    ((Interpretation.identity presentation.theory).pullbackStructure points model) where
  onSort := fun _ x => x
  total_comm f := nomatch f
  relation_mem r := nomatch r
  partial_mem p := nomatch p
  partial_comm p := nomatch p
  quantity_comm q := nomatch q

/-- A complementary value observation commutes with the Boolean complement on values. -/
def complementaryComparison : ReadingComparison (reading id) (reading Bool.not) where
  interpretation := Interpretation.identity presentation.theory
  targetModel := model
  state := state
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := Bool.not
  commutes := fun _ => rfl

/-- No family with an empty index covers the declared Boolean sort. -/
theorem empty_cover_fails : ¬ ∃ cover : DeclarationCover whole, IsEmpty cover.Index := by
  rintro ⟨cover, hempty⟩
  obtain ⟨i, _⟩ := cover.covers (a := .sort ()) (Set.mem_univ _)
  exact hempty.false i

/-- The global state observation can be selected independently of the declarations. -/
private def missingSort : Reading.{0, 0, 0, 0} :=
  let emptyContext : DeclarationContext presentation := ⟨∅, fun ha => ha.elim⟩
  { (reading Bool.not) with
    context := emptyContext
    cover :=
      { Index := Empty
        piece := fun i => nomatch i
        subset := fun i => nomatch i
        covers := fun h => h.elim }
    observationPlacement := .external
    observationDeclared := fun _ named => nomatch named
    coefficients := none }

/-- With fixed declarations the state observation still reads its actual structure. -/
def sameEmptyContext : ReadingComparison missingSort missingSort where
  interpretation := Interpretation.identity presentation.theory
  targetModel := model
  state := state
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := id
  commutes := fun _ => rfl

/-- A retained declaration must translate into the selected target declarations. -/
theorem missing_target_sort_fails :
    ¬ ∃ transition : ReadingContextChange (reading id) missingSort
        (Interpretation.identity presentation.theory),
      Declaration.sort () ∈ transition.retained.declarations := by
  rintro ⟨transition, hs⟩
  obtain ⟨_, j, _, _⟩ := transition.sort_is_covered () hs
  exact nomatch j

/-- A comparison cannot keep distinguishing observed states through an empty target cover. -/
theorem cannot_compare_external_after_forgetting_input
    (comparison : ReadingComparison (reading id) missingSort) (change : comparison.ContextChange)
    (noneKeptExternally : change.val.keptExternalInputs = ∅) : False := by
  obtain ⟨localRead, _, sourceSquare, _, _⟩ := comparison.observation_square_on_retained change
  have noInput (i : change.val.observationInputs) : False := by
    rcases i.property with kept | ⟨_, outside⟩ | ⟨external, _, _⟩
    · obtain ⟨_, j, _, _⟩ := change.val.sort_is_covered _ kept
      exact nomatch j
    · exact outside (Set.mem_univ _)
    · rw [noneKeptExternally] at external
      exact external.elim
  have localInputs :
      (fun _ : change.val.observationInputs => false) = (fun _ => true) :=
    funext (fun i => (noInput i).elim)
  exact Bool.noConfusion
    ((sourceSquare.1 (fun _ => false)).symm.trans
      ((congrArg localRead localInputs).trans (sourceSquare.1 (fun _ => true))))

/-- The target can produce a constant entirely independently of the forgotten states. -/
private def constantWithEmptyCover : Reading.{0, 0, 0, 0} :=
  { missingSort with
    observation := StateObservation.ofSort () Bool (fun _ => true)
    observationDeclared := fun _ h => nomatch h }

/-- All declarations are forgotten in this comparison of constant observations. -/
private def emptyCoverChange :
    ReadingContextChange (reading (fun _ => false)) constantWithEmptyCover
      (Interpretation.identity presentation.theory) where
  retained := missingSort.context
  inside _ absent := absent.elim
  supporting := fun _ => Interpretation.identity presentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces _ := ∅
  localSupport _ _ absent := absent.elim

/-- The retained empty tuple still has a well-defined comparison of constant observations. -/
def constant_observations_compare_through_empty_cover :
    ReadingComparison (reading (fun _ => false)) constantWithEmptyCover where
  interpretation := Interpretation.identity presentation.theory
  targetModel := model
  state := state
  contexts := .identity _
  declarationChange := .changed emptyCoverChange
  coefficientChange := PUnit.unit
  value := Bool.not
  commutes _ := rfl
  restrictedObservations :=
    ⟨fun _ => false, fun _ => true,
      ⟨(fun _ => rfl), Or.inl (StateObservation.restriction_surjective_of_nonempty _ _ ⟨fun _ => false⟩)⟩,
      ⟨(fun _ => rfl), Or.inl (StateObservation.restriction_surjective_of_nonempty _ _ ⟨fun _ => false⟩)⟩,
      (fun _ => rfl), True.intro⟩

/-- The declaration is forgotten while the comparison explicitly retains the external Boolean state. -/
private def forgetSortKeepExternal : ReadingContextChange (reading id) missingSort
    (Interpretation.identity presentation.theory) where
  retained := missingSort.context
  inside _ absent := absent.elim
  supporting := fun _ => Interpretation.identity presentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  keptExternalInputs := Set.univ
  pieces _ := ∅
  localSupport _ _ absent := absent.elim

/-- The original external observation remains nonconstant after its sort declaration is forgotten. -/
def forget_declaration_keep_external_state : ReadingComparison (reading id) missingSort where
  interpretation := Interpretation.identity presentation.theory
  targetModel := model
  state := state
  contexts := .identity _
  declarationChange := .changed forgetSortKeepExternal
  coefficientChange := PUnit.unit
  value := Bool.not
  commutes _ := rfl
  restrictedObservations := forgetSortKeepExternal.observationSquare_of_available _ _ _
    (fun _ => Or.inr (Or.inr ⟨Set.mem_univ _, rfl, False.elim⟩))
    (fun _ => Or.inr (Or.inr ⟨Set.mem_univ _, rfl, False.elim⟩)) (fun _ => rfl)

/-- Equality in a context of two states reads both variables of the retained sort. -/
private def twoStatesEqual : Atomic signature [(), ()] := .eq .here (.there .here)

/-- Even a symbol-free equality cannot be evaluated on variables of a forgotten sort. -/
theorem forgotten_sort_equality_fails :
    ¬ Declaration.atomicSupport twoStatesEqual ⊆ missingSort.context.declarations := by
  intro support
  have h : Declaration.sort () ∈ missingSort.context.declarations :=
    support (Or.inl ⟨(), List.mem_cons_self, rfl⟩)
  exact h.elim

/-- Formula support accounts for unused free positions and for the sort of an existential. -/
theorem forgotten_sort_formula_fails :
    (¬ Declaration.formulaSupport (.truth : Formula signature [()]) ⊆
      missingSort.context.declarations) ∧
    (¬ Declaration.formulaSupport (.ex (.truth : Formula signature [()])) ⊆
      missingSort.context.declarations) := by
  constructor
  · intro support
    have h : Declaration.sort () ∈ missingSort.context.declarations :=
      support (Or.inl ⟨(), List.mem_cons_self, rfl⟩)
    exact h.elim
  · intro support
    have h : Declaration.sort () ∈ missingSort.context.declarations :=
      support (Or.inr (Or.inl (Set.mem_singleton _)))
    exact h.elim

/-- Cover the same declarations with a new family of pieces. -/
private def secondCover : Reading.{0, 0, 0, 0} :=
  { (reading Bool.not) with
    cover :=
      { Index := Bool
        piece := fun _ => whole
        subset := fun _ _ h => h
        covers := fun h => ⟨true, h⟩ } }

/-- Send the original cover piece to the true-indexed piece of the new cover. -/
private def coverChange : ReadingContextChange (reading id) secondCover
    (Interpretation.identity presentation.theory) where
  retained := whole
  inside := fun _ h => h
  supporting := fun _ => Interpretation.identity presentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces := fun _ => {true}
  localSupport := by
    intros
    exact ⟨true, Set.mem_singleton _, Set.mem_univ _⟩

/-- The state observation and the change of cover are compared together. -/
def comparisonWithCover : ReadingComparison (reading id) secondCover where
  interpretation := Interpretation.identity presentation.theory
  targetModel := model
  state := state
  contexts := .identity _
  declarationChange := .changed coverChange
  coefficientChange := PUnit.unit
  value := Bool.not
  commutes := fun _ => rfl
  restrictedObservations := coverChange.observationSquare_of_all _ _ _
    (fun _ => Set.mem_univ _) (fun _ => rfl)

/-- The comparison transports a quantified formula through the two assigned pieces. -/
theorem retained_equality_transport :
    let p : Formula signature [()] := .ex (.atom twoStatesEqual)
    let e : Assignment points.carrier [()] := Assignment.cons false Assignment.empty
    let supported : Declaration.formulaSupport p ⊆ (coverChange.sourcePiece ()).declarations :=
      fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
    (RestrictedEvaluation.restrict (coverChange.targetPiece ()) secondCover.structureData).holds
      (comparisonWithCover.interpretation.translation.formula p)
      (coverChange.local_formula_support () p supported)
      (comparisonWithCover.interpretation.mapStates comparisonWithCover.state e) := by
  dsimp only
  exact comparisonWithCover.transport_restricted_formula ⟨coverChange, rfl⟩ () _
    (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩) _ ⟨false, rfl⟩

/-- Fixing observed values along the same state map fails (1.12) at the point false. -/
theorem identityValue_fails :
    ¬ ∀ e : (reading id).observation.product.Values points.carrier,
      (reading Bool.not).observation.read
        (complementaryComparison.contexts.mapValues state.onSort e) =
      (reading id).observation.read e := by
  intro h
  have bad : true = false := h (fun _ => false)
  cases bad

end SHIGURE.Chapter1.Observation

namespace SHIGURE.Chapter1.CoefficientTransport

/-- Give the observation signature the carrier of the chosen realization. -/
private def statesOf (R : Type) : Structure Observation.signature where
  carrier := fun _ => R
  total := fun f => nomatch f
  relation := fun r => nomatch r
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := fun q => nomatch q

/-- Equip a concrete scalar type with its named coefficient ring. -/
private def ringOf (R : Type) [CommRing R] : CoefficientRing := ⟨R, inferInstance⟩

/-- The scalar scheme records an offset in each realization. -/
private def offsetScheme (base : CoefficientRing) : CoefficientScheme Observation.whole base where
  Realization R := R.scalars.Carrier
  structureOf R _ := RestrictedStructure.restrict Observation.whole (statesOf R.scalars.Carrier)
  structure_retained _ _ := RestrictedStructure.hasOnlyRetainedSorts_of_all _ (fun s => Set.mem_univ (Declaration.sort s))
  category R :=
    { Hom := fun _ _ => R.scalars.Carrier → R.scalars.Carrier
      id := fun _ => id
      comp := fun f g => g ∘ f }
  mapPoints f _ _ x := f x
  mapPoints_preserves f := by
    intro Γ a _ e held
    cases a with
    | eq x y => exact congrArg f held
    | rel r _ => exact nomatch r
    | domain p _ => exact nomatch p
    | graph op _ _ => cases op <;> rename_i symbol <;> exact nomatch symbol
  mapPoints_id _ _ _ _ := rfl
  mapPoints_comp _ _ _ _ _ := rfl
  permitsPoints _ _ _ _ _ := True
  permitsPoints_congr := by intros; rfl
  Native := base.Carrier
  nativeStructure _ := RestrictedStructure.restrict Observation.whole (statesOf base.Carrier)
  native_retained _ := RestrictedStructure.hasOnlyRetainedSorts_of_all _ (fun s => Set.mem_univ (Declaration.sort s))
  realizeNative R offset := R.fromBase offset
  nativePoints R _ _ _ x := R.fromBase x
  nativePoints_permitted _ _ _ _ := True.intro
  interpretLaw R _ :=
    (RestrictedStructure.restrict Observation.whole (statesOf R.scalars.Carrier)).satisfies
  change f offset := f offset
  changePoints f _ _ _ x := f x

/-- A realization class can contain every small carrier at the selected coefficient algebra. -/
def allSmallRealizations : CoefficientScheme.{0, 1} Observation.whole (ringOf Int) where
  Realization _ := Type
  structureOf _ X := RestrictedStructure.restrict Observation.whole (statesOf X)
  structure_retained _ _ := RestrictedStructure.hasOnlyRetainedSorts_of_all _ (fun s => Set.mem_univ (Declaration.sort s))
  category _ :=
    { Hom := fun X Y => X → Y
      id := fun _ => id
      comp := fun f g => g ∘ f }
  mapPoints f _ _ := f
  mapPoints_preserves f := by
    intro Γ a _ e held
    cases a with
    | eq x y => exact congrArg f held
    | rel r _ => exact nomatch r
    | domain p _ => exact nomatch p
    | graph op _ _ => cases op <;> rename_i symbol <;> exact nomatch symbol
  mapPoints_id _ _ _ _ := rfl
  mapPoints_comp _ _ _ _ _ := rfl
  permitsPoints _ _ _ Γ points := ∀ s (kept : s ∈ Γ), Function.Injective (points s kept)
  permitsPoints_congr := by
    intro R a X Y same sorts kept points
    constructor
    · intro injective s hs x y eq
      let e := same.carrier_eq s (kept s hs)
      have cancel {X Y : Type} (e : X = Y) (x : Y) : cast e (cast e.symm x) = x := by
        cases e
        rfl
      have h : cast e.symm x = cast e.symm y := injective s hs (by
        change points s hs (cast e (cast e.symm x)) = points s hs (cast e (cast e.symm y))
        simpa only [cancel] using eq)
      simpa only [cancel] using congrArg (cast e) h
    · intro injective s hs x y eq
      let e := same.carrier_eq s (kept s hs)
      have h : cast e x = cast e y := injective s hs eq
      simpa using congrArg (cast e.symm) h
  Native := Type
  nativeStructure X := RestrictedStructure.restrict Observation.whole (statesOf X)
  native_retained _ := RestrictedStructure.hasOnlyRetainedSorts_of_all _ (fun s => Set.mem_univ (Declaration.sort s))
  realizeNative _ := id
  nativePoints _ _ _ _ := id
  nativePoints_permitted _ _ _ _ := fun _ _ => Function.injective_id
  interpretLaw _ X := (RestrictedStructure.restrict Observation.whole (statesOf X)).satisfies
  change _ := id
  changePoints _ _ _ _ := id

/-- Select a Boolean realization from the large class while observing small Boolean states. -/
def all_small_realizations_reading : Reading.{0, 1, 1, 1} where
  presentation := Observation.presentation
  structureData := statesOf Bool
  observation := StateObservation.ofSort () Bool id
  context := Observation.whole
  cover := (Observation.reading id).cover
  Family := Type
  realize := statesOf
  familyObservation := some ⟨Type, id⟩
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := some ⟨.ofList [()],
    { base := ringOf Int
      algebra := ⟨ringOf Int, RingHom.id Int⟩
      scheme := allSmallRealizations
      realization := Bool
      selection := .ofRenaming (Δ := [()]) (fun i => i)
      supported _ := Set.mem_univ _
      realizePoint _ _ := id
      pointOrigin := .declared PUnit.unit (fun _ _ => Function.injective_id) (fun _ _ => ⟨rfl, rfl⟩)
      evaluateOn _ R _ _ :=
        letI := R.scalars.ring
        0 }⟩

/-- Every small carrier is represented by its own structure in the observed family. -/
theorem observed_family_has_every_small_carrier (X : Type) :
    (all_small_realizations_reading.realize X).carrier () = X := rfl

/-- The specified coefficient algebra and realization evaluate each state at its chosen offset. -/
private def readRing (R : Type) [CommRing R] (offset : R) :
    CoefficientReading Observation.whole (statesOf R) (.ofList [()]) where
  base := ringOf Int
  algebra := ⟨ringOf R, Int.castRingHom R⟩
  scheme := offsetScheme (ringOf Int)
  realization := offset
  selection := .ofRenaming (Δ := [()]) (fun i => i)
  supported _ := Set.mem_univ _
  realizePoint _ _ x := x
  pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
  evaluateOn _ coefficients data e :=
    letI := coefficients.scalars.ring
    (show coefficients.scalars.Carrier from e ⟨(), .here⟩) +
      (show coefficients.scalars.Carrier from data)

/-- Keeping the sort alone cannot determine an evaluator that uses an additional realization
parameter. The coefficient reading may keep the full realization at its original context. -/
theorem offset_not_determined_by_retained_structure :
    ¬ (readRing Int 0).RespectsRestriction Observation.whole (fun _ h => h) := by
  intro locality
  let reading := readRing Int 0
  let left : reading.RealizedInput reading.algebra := ⟨(0 : Int), fun _ => (0 : Int)⟩
  let right : reading.RealizedInput reading.algebra := ⟨(1 : Int), fun _ => (0 : Int)⟩
  have same : reading.AgreeOn (fun _ h => h) locality.supported left right :=
    ⟨RestrictedStructure.Agrees.refl _, rfl⟩
  have equal := locality.agrees left right same
  exact (by decide : (0 : Int) + 0 ≠ 0 + 1) equal

/-- Use the identity point rule when the retained carriers agree. -/
private noncomputable def localIdentityRule {W : DeclarationContext Observation.presentation} :
    CoefficientReading.LocalPointRule W :=
  fun X Y s _ => by
    classical
    exact if same : X.carrier s = Y.carrier s then some (cast same) else none

/-- Compare a direct carrier transport with transport via the common carrier. -/
private theorem cast_via_common_carrier {X Y Z : Type} (left : X = Y) (right : X = Z) (y : Y) :
    cast (left.symm.trans right) y = cast right (cast left.symm y) := by
  cases left
  cases right
  rfl

/-- The coefficient method offers independent identity and integer-shift recipes. -/
private def shiftedPointScheme : CoefficientScheme Observation.whole (ringOf Int) :=
  { offsetScheme (ringOf Int) with
    pointPrograms _ _ :=
      { Selector := Bool
        describes selected X Y s f := if selected then
          ∃ (source : X.carrier s = Int) (target : Y.carrier s = Int),
            f = fun x => cast target.symm (cast source x + 1)
          else (CoefficientPointPrograms.identity.{0, 0} Observation.whole).describes PUnit.unit X Y s f
        unique := by
          rintro choice X Y s f g
          cases choice
          · exact (CoefficientPointPrograms.identity.{0, 0} _).unique PUnit.unit X Y s
          · rintro ⟨_, _, same⟩ ⟨_, _, same'⟩
            exact same.trans same'.symm
        source_congr := by
          intro choice X X' Y same s kept f described
          cases choice
          · exact (CoefficientPointPrograms.identity.{0, 0} _).source_congr PUnit.unit same s kept described
          · obtain ⟨source, target, rfl⟩ := described
            refine ⟨(same.carrier_eq s kept).symm.trans source, target, ?_⟩
            funext x
            simp only [cast_cast] } }

/-- Evaluate the designated integer point at the selected coordinate. -/
private def pointReading : CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) :=
  { readRing Int 0 with
    scheme := shiftedPointScheme
    pointOrigin := .declared false True.intro (fun _ _ => ⟨rfl, rfl⟩)
    evaluateOn := fun _ _ _ e => e ⟨(), .here⟩ }

/-- Reading the designated point factors through the retained carrier and tuple. -/
private theorem pointReading_local {W : DeclarationContext Observation.presentation}
    (inside : W.declarations ⊆ Observation.whole.declarations)
    (kept : ∀ i : pointReading.selection.selected.Index,
      Declaration.sort (pointReading.selection.selected.sort i) ∈ W.declarations) :
    pointReading.RespectsRestriction W inside := by
  refine ⟨kept, ⟨localIdentityRule, ?_, ?_⟩, ?_⟩
  · intro i X Y left right
    classical
    have x := left.carrier_eq _ (kept i)
    have y := right.carrier_eq _ (kept i)
    change (if same : X.carrier i.1 = Y.carrier i.1 then some (cast same) else none) =
      some (fun z => cast y (cast x.symm z))
    rw [dif_pos (show X.carrier i.1 = Y.carrier i.1 from x.symm.trans y)]
    exact congrArg some (funext (cast_via_common_carrier x y))
  · apply (CoefficientReading.LocalPointRule.agreesOnDeclared_iff localIdentityRule pointReading inside kept false).2
    intro X a points _ describes _ _ i
    classical
    let Y := pointReading.scheme.structureOf pointReading.algebra a
    obtain ⟨same, exactPoint⟩ := describes (pointReading.selection.selected.sort i) ⟨i, rfl⟩
    change (if eq : X.carrier i.1 = Y.carrier i.1 then some (cast eq) else none) =
      some (points i.1 ⟨i, rfl⟩)
    rw [dif_pos (show X.carrier i.1 = Y.carrier i.1 from same)]
    exact congrArg some exactPoint.symm
  · rintro left right ⟨same, tuple⟩
    have eq := congrFun tuple ⟨(), .here⟩
    exact eq.symm

/-- The comparison supplies its own local rule for the integer point map. -/
theorem point_evaluation_respects_restriction :
    pointReading.RespectsRestriction Observation.whole (fun _ h => h) :=
  pointReading_local _ (fun _ => Set.mem_univ _)

/-- A purported local identity rule cannot justify a different designated point correspondence. -/
theorem local_point_rule_cannot_hide_shift :
    let reading : CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) := { readRing Int 0 with
      scheme := shiftedPointScheme
      realizePoint := fun _ _ x => (show Int from x) + 1
      pointOrigin := .declared true True.intro (fun _ _ => ⟨rfl, rfl, rfl⟩)
      evaluateOn := fun _ _ _ e => e ⟨(), .here⟩ }
    ¬ localIdentityRule.AgreesWith reading (fun _ h => h) (fun _ => Set.mem_univ _) := by
  classical
  dsimp only
  intro locality
  have agrees := locality ⟨(), .here⟩ _ _
    (RestrictedStructure.Agrees.refl _) (RestrictedStructure.Agrees.refl _)
  change (if same : Int = Int then some (cast same) else none) = some (fun x : Int => x + 1) at agrees
  have functions : some (id : Int → Int) = some (fun x : Int => x + 1) := by
    rw [dif_pos (rfl : Int = Int)] at agrees
    exact agrees
  exact (by decide : (0 : Int) ≠ 1) (congrFun (Option.some.inj functions) 0)

/-- An identity coefficient map commutes with evaluation in the same realization. -/
def integerIdentity :
    CoefficientReading.Change (readRing Int 0) (readRing Int 0) id where
  baseMap := RingHom.id Int
  coefficients := RingHom.id Int
  algebra_commutes := by
    change (_ : Int →+* Int) = _
    exact Subsingleton.elim _ _
  evaluate_commutes := fun _ => rfl

/-- Send both coordinates of the realized state to the same integer. -/
private def diagonalStates (e : (ObservationProduct.ofList [()]).Values (statesOf Int).carrier) :
    (ObservationProduct.ofList [()]).Values (statesOf (Int × Int)).carrier :=
  fun i => (e i, e i)

/-- This scheme's own scalar change sends the designated states to zero. -/
private def collapsedScheme : CoefficientScheme Observation.whole (ringOf Int) :=
  { offsetScheme (ringOf Int) with
    changePoints := fun {_} {target} _ _ _ _ _ =>
      letI := target.ring
      (0 : target.Carrier) }

/-- At the chosen integer algebra the underlying realization still reads its actual state. -/
private def collapsedReading : CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) :=
  { readRing Int 4 with scheme := collapsedScheme, pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩) }

/-- The direct square allows a state map different from the scheme's own scalar change. -/
def directDiagonal :
    CoefficientReading.Change collapsedReading (readRing (Int × Int) (4, 4)) diagonalStates where
  baseMap := RingHom.id Int
  coefficients := (RingHom.id Int).prod (RingHom.id Int)
  algebra_commutes := by
    change (_ : Int →+* (Int × Int)) = _
    exact Subsingleton.elim _ _
  evaluate_commutes := fun _ => rfl

/-- The direct diagonal state map cannot factor through the collapsed states. -/
theorem direct_diagonal_does_not_factor :
    ¬ ∃ continuation : (ObservationProduct.ofList [()]).Values
        (collapsedReading.changedStructure directDiagonal.coefficients).carrier →
      (ObservationProduct.ofList [()]).Values (statesOf (Int × Int)).carrier,
      ∀ e, continuation (collapsedReading.changedState directDiagonal.coefficients e) = diagonalStates e := by
  rintro ⟨continuation, agrees⟩
  let zero : (ObservationProduct.ofList [()]).Values (statesOf Int).carrier := fun _ => (0 : Int)
  let one : (ObservationProduct.ofList [()]).Values (statesOf Int).carrier := fun _ => (1 : Int)
  have same : collapsedReading.changedState directDiagonal.coefficients zero =
      collapsedReading.changedState directDiagonal.coefficients one := rfl
  have impossible : (0 : Int) = 1 :=
    congrArg (fun x => (show Int × Int from x ⟨(), .here⟩).1)
      ((agrees zero).symm.trans ((congrArg continuation same).trans (agrees one)))
  exact (by decide : (0 : Int) ≠ 1) impossible

/-- The scheme transports both the nonzero offset and each state along the diagonal map. -/
def integerDiagonal :
    CoefficientReading.Change (readRing Int 4) (readRing (Int × Int) (4, 4)) diagonalStates :=
  CoefficientReading.Change.alongScheme (RingHom.id Int) ((RingHom.id Int).prod (RingHom.id Int))
    (by
      change (_ : Int →+* (Int × Int)) = _
      exact Subsingleton.elim _ _)
    id (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The actual reading returns the state, with an additional selected coefficient evaluation. -/
private def readingOf (R : Type) [CommRing R] (offset : R) : Reading.{0, 0, 0, 0} where
  presentation := Observation.presentation
  structureData := statesOf R
  observation := StateObservation.ofSort () R id
  context := Observation.whole
  cover := (Observation.reading id).cover
  Family := Unit
  realize := fun _ => statesOf R
  familyObservation := none
  ValueStructure := fun _ => Unit
  valueStructure := ()
  coefficients := some ⟨.ofList [()], readRing R offset⟩

/-- Both the observation and the coefficient evaluation use the structural state map. -/
def coefficientComparison : ReadingComparison (readingOf Int 4) (readingOf (Int × Int) (4, 4)) where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel := fun name => nomatch name.val
  state :=
    { onSort := fun _ x => (x, x)
      total_comm := fun f => nomatch f
      relation_mem := fun r => nomatch r
      partial_mem := fun p => nomatch p
      partial_comm := fun p => nomatch p
      quantity_comm := fun q => nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := .changed (ReadingInputMap.identity (readRing Int 4).selection.used)
    { integerDiagonal with
      evaluate_commutes := fun e => integerDiagonal.evaluate_commutes
        (fun _ => e.1 ⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩) }
  coefficientInputs := ⟨ReadingInputMap.identity_usesCoefficientNames _, ReadingInputMap.identity_respectsOrdinary _ _ _⟩
  value := fun x => (x, x)
  commutes := fun _ => rfl

/-- The comparison reads the transported value six at the state two with offset four. -/
theorem coefficient_comparison_at_two :
    (readRing (Int × Int) (4, 4)).evaluate
      (ObservationProduct.ofAssignment (coefficientComparison.interpretation.mapStates coefficientComparison.state
        (Assignment.cons (2 : Int) Assignment.empty))) = ((6, 6) : Int × Int) := by
  exact integerDiagonal.evaluate_commutes (fun _ => (2 : Int))

/-- Comparing these coefficient evaluations requires keeping their integer state sort. -/
theorem cannot_discard_coefficient_sort
    (comparison : ReadingComparison (readingOf Int 4) (readingOf (Int × Int) (4, 4)))
    (change : comparison.ContextChange) : change.val.retained.declarations ≠ ∅ := by
  intro empty
  have support := comparison.coefficientSupport
  rw [change.property] at support
  let input : (readRing Int 4).selection.used.Index := ⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩
  have kept : Declaration.sort () ∈ change.val.retained.declarations := by
    cases chosen : comparison.coefficientChange with
    | fixed same =>
      rw [chosen] at support
      exact support.elim
    | changed inputs square =>
      rw [chosen] at support
      rcases support.1.1 input with kept | ⟨j, available, shared⟩
      · exact kept
      · rcases shared.2 with named | ⟨explicit, _, _⟩
        · have impossible : (some "typed variables" : Option String) = none := named.2.2.1
          cases impossible
        · cases explicit
  rw [empty] at kept
  exact kept.elim

/-- Fixed coefficients do not require the coefficient evaluator to be preserved by a state change. -/
def fixedCoefficientComparison : ReadingComparison (readingOf Int 0) (readingOf Int 0) where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel := fun name => nomatch name.val
  state :=
    { onSort := fun _ x => (show Int from x) + (1 : Int)
      total_comm := fun f => nomatch f
      relation_mem := fun r => nomatch r
      partial_mem := fun p => nomatch p
      partial_comm := fun p => nomatch p
      quantity_comm := fun q => nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := .fixed
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, fun _ => HEq.rfl, Or.inr ⟨HEq.rfl, HEq.rfl⟩, HEq.rfl, HEq.rfl⟩
  coefficientInputs := fun _ _ shared => shared.2.elim (fun h => by cases h.2.2.1) (fun h => by cases h.1)
  value := fun x => (show Int from x) + (1 : Int)
  commutes := fun _ => rfl

/-- An unused extra copy of the integer sort does not change the selected state. -/
private def paddedIntegerInput : CoefficientReading Observation.whole (statesOf Int) (.ofList [(), ()]) :=
  { readRing Int 0 with
    selection := .ofRenaming (Δ := [()]) (fun {s} _ => match s with
      | () => .here) }

/-- Both presentations describe the same single used position. -/
private theorem paddedInteger_names :
    HEq (readRing Int 0).selection.selectedSlots paddedIntegerInput.selection.selectedSlots := by
  apply heq_of_eq
  funext pos
  obtain ⟨s, x⟩ := pos
  cases x with
  | here => rfl
  | there x => exact nomatch x

/-- The padded product has an additional original position. -/
private theorem padded_integer_product_differs :
    ¬ HEq (CoefficientProduct.ofList [()]) (CoefficientProduct.ofList [(), ()]) := by
  intro same
  have index_eq : (ObservationProduct.ofList [()]).Index = (ObservationProduct.ofList [(), ()]).Index :=
    congrArg (fun raw : CoefficientProduct Unit => raw.product.Index) (eq_of_heq same)
  have small : Subsingleton (ObservationProduct.ofList [()]).Index := by
    refine ⟨?_⟩
    rintro ⟨_, i⟩ ⟨_, j⟩
    cases i with
    | here => cases j with
      | here => rfl
      | there j => exact nomatch j
    | there i => exact nomatch i
  have impossible := @Subsingleton.elim (ObservationProduct.ofList [(), ()]).Index
    (index_eq ▸ small) ⟨(), .here⟩ ⟨(), .there .here⟩
  have position := congrArg (fun i : (ObservationProduct.ofList [(), ()]).Index => i.2.position) impossible
  exact (by decide : (0 : Nat) ≠ 1) position

/-- This signature has a value sort without primitive ring operations. -/
private def orderedStateEquation : OrderedEquation Observation.signature where
  context := [(), ()]
  result := ()
  input := .truth
  left := .var .here
  right := .var (.there .here)

/-- Write the equality with its two variables in their designated order. -/
private def writtenStateEquation : OrderedEquation.Written Observation.signature :=
  orderedStateEquation.writeVariables .here (.there .here) rfl rfl

/-- Register an ordered equality with the ring supplied by its interpreted carrier. -/
private def externalRingPresentation : PrimitivePresentation where
  signature := Observation.signature
  laws :=
    { LawName := Unit
      statement _ := writtenStateEquation.toLaw
      role _ := .additional }
  otherOrderedEquation _ := some ⟨writtenStateEquation, rfl⟩
  derived _ isDerived := by cases isDerived

/-- Literal syntax and its ordering can be registered independently of canonical ring symbols. -/
theorem ordered_state_equation_registered :
    externalRingPresentation.orderedEquation () = some ⟨writtenStateEquation, rfl⟩ :=
  rfl

/-- Use the identity structure map on the integer states. -/
private def identityIntegerState : StructureMap (statesOf Int) (statesOf Int) where
  onSort _ := id
  total_comm f := nomatch f
  relation_mem r := nomatch r
  partial_mem p := nomatch p
  partial_comm p := nomatch p
  quantity_comm q := nomatch q

section

/-- Use the integer ring structure on the result carrier in the residual transport example. -/
local instance : CommRing ((statesOf Int).carrier orderedStateEquation.result) :=
  inferInstanceAs (CommRing Int)

/-- Residual transport works directly with the ring homomorphism on the state sort. -/
theorem semantic_ring_residual_map (e : orderedStateEquation.jointInputs (statesOf Int)) :
    orderedStateEquation.residual (statesOf Int) e =
      orderedStateEquation.residual (statesOf Int)
        (orderedStateEquation.mapInput identityIntegerState e) :=
  orderedStateEquation.residual_map identityIntegerState (RingHom.id Int) (fun _ => rfl) e

/-- The same value ring evaluates a substituted equation and the original ordered equation. -/
theorem semantic_ring_residual_substitution
    (θ : Substitution Observation.signature orderedStateEquation.context [()])
    (e : (orderedStateEquation.substitute θ).jointInputs (statesOf Int)) :
    (orderedStateEquation.substitute θ).residual (statesOf Int) e =
      orderedStateEquation.residual (statesOf Int)
        (orderedStateEquation.substituteInput θ (statesOf Int) e) :=
  orderedStateEquation.residual_substitute θ (statesOf Int) e

end

/-- The same declarations can have a different cover at fixed coefficients. -/
private def secondIntegerCover : Reading.{0, 0, 0, 0} :=
  { readingOf Int 0 with
    cover := ⟨Bool, fun _ => Observation.whole, fun _ _ h => h, fun h => ⟨true, h⟩⟩ }

/-- The identity coefficient map preserves the actual evaluation across a cover change. -/
def identity_coefficients_across_cover_change :
    ReadingComparison (readingOf Int 0) secondIntegerCover :=
  { fixedCoefficientComparison with
    state :=
      { onSort _ := id
        total_comm f := nomatch f
        relation_mem r := nomatch r
        partial_mem p := nomatch p
        partial_comm p := nomatch p
        quantity_comm q := nomatch q }
    declarationChange := .changed
      { retained := Observation.whole
        inside := fun _ h => h
        supporting := fun _ => Interpretation.identity Observation.presentation.theory
        equivalent := fun _ => Interpretation.Equivalent.refl _
        pieces := fun _ => {true}
        localSupport := by intros; exact ⟨true, Set.mem_singleton _, Set.mem_univ _⟩ }
    observationSupport := ⟨False.elim, False.elim⟩
    declaredObservations := .external
    coefficientChange := .changed (.identity _)
      { baseMap := RingHom.id Int
        coefficients := RingHom.id Int
        algebra_commutes := rfl
        evaluate_commutes _ := rfl }
    coefficientInputs :=
      ⟨ReadingInputMap.identity_usesCoefficientNames _, ReadingInputMap.identity_respectsOrdinary _ _ _ _⟩
    coefficientSupport :=
      ⟨⟨(fun _ => Or.inl (Set.mem_univ _)), Or.inl rfl⟩,
        ⟨(fun _ => Or.inl ⟨true, Or.inl ⟨PUnit.unit, Set.mem_singleton _⟩, Set.mem_univ _⟩),
          Or.inl (Set.eq_univ_of_forall (fun _ =>
            ⟨true, Or.inl ⟨PUnit.unit, Set.mem_singleton _⟩, Set.mem_univ _⟩))⟩⟩
    value := id
    commutes _ := rfl
    restrictedObservations := ReadingContextChange.observationSquare_of_all _ _ _ _
      (fun _ => Set.mem_univ _) (fun _ => rfl) }

/-- The target lists an extra integer state that the evaluation never uses. -/
private def paddedIntegerReading : Reading.{0, 0, 0, 0} :=
  { readingOf Int 0 with coefficients := some ⟨.ofList [(), ()], paddedIntegerInput⟩ }

/-- Padding the outer product preserves the fixed comparison along the non-linear state map. -/
def fixed_comparison_with_unused_input : ReadingComparison (readingOf Int 0) paddedIntegerReading :=
  { fixedCoefficientComparison with
    declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
    coefficientChange := .fixed
      ⟨rfl, rfl, HEq.rfl, HEq.rfl, paddedInteger_names, rfl,
        fun h => (padded_integer_product_differs h).elim, Or.inr ⟨HEq.rfl, HEq.rfl⟩, HEq.rfl, HEq.rfl⟩
    coefficientInputs := fun _ _ shared => shared.2.elim (fun h => by cases h.2.2.1) (fun h => by cases h.1) }

/-- Sending zero to one in the fixed comparison would fail a coefficient-change square. -/
theorem fixed_comparison_has_no_scalar_change :
    ¬ Nonempty (CoefficientReading.Change (readRing Int 0) (readRing Int 0)
      (fun i j => fixedCoefficientComparison.state.onSort j.1 (i j))) := by
  rintro ⟨data⟩
  let h : Int →+* Int := data.coefficients
  have impossible : (1 : Int) = h 0 :=
    data.evaluate_commutes (fun _ => (0 : Int))
  exact (by decide : (1 : Int) ≠ 0) (impossible.trans h.map_zero)

/-- This selection changes only the point correspondence used to feed the evaluation rule. -/
private def shiftedPoint : CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) :=
  { pointReading with
    realizePoint := fun _ _ x => (show Int from x) + (1 : Int)
    pointOrigin := .declared true True.intro (fun _ _ => ⟨rfl, rfl, rfl⟩) }

/-- A changed point correspondence cannot be hidden in the fixed comparison. -/
theorem point_change_is_not_fixed : ¬ pointReading.SameParameters shiftedPoint := by
  intro same
  rcases same.application with h | h
  · exact h.1
  have impossible : (0 : Int) = 1 :=
    congrFun (congrFun (eq_of_heq h.2) ⟨(), .here⟩) (0 : Int)
  exact (by decide : (0 : Int) ≠ 1) impossible

/-- Changing only the chosen offset still changes the realization. -/
theorem realization_change_is_not_fixed : ¬ (readRing Int 0).SameParameters (readRing Int 1) := by
  intro same
  rcases same.application with h | h
  · exact h.1
  exact (by decide : (0 : Int) ≠ 1) (eq_of_heq h.1)

/-- Read the second position of the same two-position integer product. -/
private def secondIntegerInput : CoefficientReading Observation.whole (statesOf Int) (.ofList [(), ()]) :=
  { paddedIntegerInput with
    selection := .ofRenaming (Δ := [()]) (fun {s} _ => match s with
      | () => .there .here) }

/-- Switching the actual selected position changes the coefficient settings. -/
theorem different_positions_are_not_fixed : ¬ paddedIntegerInput.SameParameters secondIntegerInput := by
  intro same
  have impossible : (0 : Nat) = 1 :=
    congrArg ULift.down (congrFun (eq_of_heq same.names) ⟨(), .here⟩)
  exact Nat.zero_ne_one impossible

/-- The two evaluations choose among the coordinates of the ordinary observation's product. -/
private def sharedObservation
    (coefficients : CoefficientReading Observation.whole (statesOf Int) (.ofList [(), ()])) :
    Reading.{0, 0, 0, 0} :=
  { readingOf Int 0 with
    observation := StateObservation.ofContext [(), ()] Int (fun e => e .here) (some "typed variables")
    coefficients := some ⟨.ofList [(), ()], coefficients⟩
    sharedInputs := .empty _
    observationPlacement := .external }

/-- Relabeling the sole used source position as the second target position would make the
coefficient values agree on that relabeled input. -/
private def relabeledInput :
    ReadingInputMap paddedIntegerInput.selection.used secondIntegerInput.selection.used id where
  extra := .empty
  coordinate j := ⟨.inl ⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩, by cases j.val.1; rfl⟩
  extra_used i := nomatch i

/-- A name shared only by the coefficient products also keeps its original position. -/
theorem cannot_relabel_coefficient_position :
    ¬ ReadingInputMap.UsesCoefficientNames paddedIntegerInput.selection relabeledInput := by
  intro keeps
  let second : secondIntegerInput.selection.used.Index := ⟨⟨(), .there .here⟩, ⟨(), .here⟩, rfl⟩
  have same := keeps second second.val ⟨by decide, rfl, HEq.rfl, rfl⟩
  exact Nat.zero_ne_one
    (congrArg (fun i : (ObservationProduct.ofList [(), ()]).Index => i.2.position) same)

/-- The ordinary identity correspondence rules out that relabeling even though the two
positions have the same sort. -/
theorem cannot_relabel_shared_position :
    ¬ relabeledInput.RespectsOrdinary
      (.identity (sharedObservation paddedIntegerInput).observation.product)
      (CoefficientProduct.ofList [(), ()]).product Subtype.val
      ((sharedObservation paddedIntegerInput).SharesInput (.ofList [(), ()]))
      (fun j i => (sharedObservation secondIntegerInput).SharesInput (.ofList [(), ()]) j.val i) := by
  rintro ⟨extra, _, _, _, respects, _⟩
  let second : secondIntegerInput.selection.used.Index := ⟨⟨(), .there .here⟩, ⟨(), .here⟩, rfl⟩
  have same := respects second second.val ⟨rfl, Or.inl ⟨rfl, by decide, rfl, HEq.rfl⟩⟩
  rcases same.2 with ⟨_, _, _, same⟩ | ⟨same, _, _⟩
  · exact Nat.zero_ne_one (congrArg ULift.down (eq_of_heq same))
  · cases same

/-- The target can forget the second ordinary coordinate while preserving the first. -/
def projected_state_comparison :
    ReadingComparison { sharedObservation paddedIntegerInput with coefficients := none }
      { readingOf Int 0 with coefficients := none } where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel := fixedCoefficientComparison.targetModel
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts :=
    { position _ := ⟨(), .here⟩
      sort_eq _ := rfl
      keepsNamed _ _ _ differentScopes _ _ := by cases differentScopes }
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl

/-- Distinct names in a common product read distinct inputs. -/
theorem cannot_repeat_common_named_position :
    let product : ObservationProduct Unit := { Index := Bool, sort := fun _ => (), nameScope := some "boolean pair" }
    ¬ ∃ positions : product.Correspondence product id, positions.position true = false := by
  dsimp only
  rintro ⟨positions, repeated⟩
  have kept : positions.position true = true := positions.keepsNamed true true (by decide) rfl HEq.rfl rfl
  exact Bool.noConfusion (kept.symm.trans repeated)

/-- A restriction to a singleton keeps its original position in the larger named product. -/
theorem named_subset_keeps_original_position :
    let source : ObservationProduct Unit := { Index := Bool, sort := fun _ => (), nameScope := some "pair" }
    let target := source.restrict ({false} : Set Bool)
    ∀ positions : source.Correspondence target id, positions.position ⟨false, Set.mem_singleton _⟩ = false := by
  dsimp only
  intro positions
  exact positions.keepsNamed _ false (by decide) rfl HEq.rfl rfl

/-- Padding the ordinary product leaves its shared first coordinate at the same name. -/
theorem padded_ordinary_product_keeps_first_name :
    (sharedObservation paddedIntegerInput).SharesInput (.ofList [()]) ⟨(), .here⟩ ⟨(), .here⟩ :=
  ⟨rfl, Or.inl ⟨rfl, by decide, rfl, HEq.rfl⟩⟩

/-- Read the selected position from two independent Boolean states. -/
private def reindexedObservation (right : Bool) : Reading.{0, 0, 0, 0} :=
  { Observation.reading id with
    observation := .ofFunction { Index := Bool, sort := fun _ => () } Bool (fun e => e right)
    sharedInputs := .empty _
    observationPlacement := .external }

/-- Independent observations can explicitly exchange positions of the same index type. -/
def independently_reindexed_comparison : ReadingComparison (reindexedObservation false) (reindexedObservation true) where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel := Observation.complementaryComparison.targetModel
  state := Observation.complementaryComparison.state
  contexts := ⟨Bool.not, fun _ => rfl, fun _ _ unnamed _ _ _ => (unnamed rfl).elim⟩
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl

/-- Ordinary and coefficient singleton inputs without a shared name can carry different values. -/
def independent_singleton_inputs : (readingOf Int 0).JointInput (InputSelection.all (.ofSort ())) where
  ordinary _ := (0 : Int)
  coefficient _ := (1 : Int)
  agrees _ _ shared :=
    shared.2.elim (fun named => (named.2.1 rfl).elim) (fun explicit => by cases explicit.1)

/-- The first `size` positions of the common natural-number slot set are available. -/
private def initialSlots (size : Nat) : CoefficientProduct Observation.signature.SortType :=
  .indexed Nat {i | i < size} (fun _ => ())

/-- Select one actual slot from the available positions. -/
private def readSlot (size index : Nat) (kept : index < size) :
    CoefficientReading Observation.whole (statesOf Int) (initialSlots size) :=
  { readRing Int 0 with
    selection :=
      { selected := .ofSort ()
        inputs _ := ⟨index, kept⟩
        sort_eq _ := rfl }
    supported _ := Set.mem_univ _
    realizePoint _ _ x := x
    pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
    evaluateOn _ _ _ e := e PUnit.unit }

/-- Padding the raw product cannot hide a change of slot in its common coordinate set. -/
theorem different_indexed_slots_are_not_fixed :
    ¬ (readSlot 2 0 (by decide)).SameParameters (readSlot 3 1 (by decide)) := by
  intro same
  exact Nat.zero_ne_one (congrFun (eq_of_heq same.names) PUnit.unit)

/-- The chosen native subsets have either one point or both Boolean points. -/
private def nativeCarrier (full : Bool) := {x : Bool // full = true ∨ x = false}

/-- Use the same inclusion of native subsets into the designated values for both readings. -/
private def nativeScheme : CoefficientScheme Observation.whole (ringOf Int) :=
  { offsetScheme (ringOf Int) with
    Native := Bool
    nativeStructure full := RestrictedStructure.restrict Observation.whole (statesOf (nativeCarrier full))
    native_retained _ := RestrictedStructure.hasOnlyRetainedSorts_of_all _ (fun s => Set.mem_univ (Declaration.sort s))
    realizeNative R full := R.fromBase (if full then (1 : Int) else (0 : Int))
    nativePoints R _ _ _ x := R.fromBase (if x.val then (1 : Int) else (0 : Int))
    nativePoints_permitted _ _ _ _ := True.intro }

/-- The designated points come entirely from the native rule, which is common to both subsets. -/
private def nativeCoefficients (full : Bool) :
    CoefficientReading Observation.whole (statesOf (nativeCarrier full)) (.ofList [()]) where
  base := ringOf Int
  algebra := ⟨ringOf Int, RingHom.id Int⟩
  scheme := nativeScheme
  realization := if full then (1 : Int) else (0 : Int)
  selection := .ofRenaming (Δ := [()]) (fun i => i)
  supported _ := Set.mem_univ _
  realizePoint _ _ x := if x.val then (1 : Int) else (0 : Int)
  pointOrigin := .native full rfl (fun _ _ => Set.mem_univ _) (.refl _) (fun _ _ _ => rfl)
  evaluateOn _ _ offset _ := offset

/-- The ordinary observation uses the false-only or the full native subset. -/
private def nativeReading (full : Bool) : Reading.{0, 0, 0, 0} where
  presentation := Observation.presentation
  structureData := statesOf (nativeCarrier full)
  observation := StateObservation.ofSort () Bool (fun x => if full then x.val else true)
  context := Observation.whole
  cover := (Observation.reading id).cover
  Family := Unit
  realize _ := statesOf (nativeCarrier full)
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := some ⟨.ofList [()], nativeCoefficients full⟩

/-- The native structures have different numbers of states. -/
private theorem native_structures_differ :
    ¬ CoefficientReading.SameRetainedSource Observation.whole Observation.whole
      (statesOf (nativeCarrier false)) (statesOf (nativeCarrier true)) := by
  rintro ⟨same⟩
  have carriers : nativeCarrier false = nativeCarrier true := same.carrier_eq () (Set.mem_univ ())
  have small : Subsingleton (nativeCarrier false) := by
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    exact (x.property.resolve_left (by decide)).trans (y.property.resolve_left (by decide)).symm
  have impossible := @Subsingleton.elim (nativeCarrier true) (carriers ▸ small)
    ⟨false, Or.inr rfl⟩ ⟨true, Or.inl rfl⟩
  exact (by decide : false ≠ true) (congrArg Subtype.val impossible)

/-- The fixed coefficient rule can be applied to different native carriers. -/
def same_native_rule_comparison : ReadingComparison (nativeReading false) (nativeReading true) where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel n := nomatch n.val
  state :=
    { onSort := fun _ _ => ⟨true, Or.inl rfl⟩
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := .fixed
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, fun _ => HEq.rfl,
      Or.inl ⟨True.intro, True.intro, fun h => (native_structures_differ h).elim⟩, HEq.rfl, HEq.rfl⟩
  coefficientInputs := fun _ _ shared => shared.2.elim (fun h => by cases h.2.2.1) (fun h => by cases h.1)
  value := id
  commutes _ := rfl

/-- The same native rule produces different selected realizations and evaluated coefficients. -/
theorem native_realizations_compute_different_values :
    (nativeCoefficients false).evaluate (fun _ => ⟨false, Or.inr rfl⟩) = (0 : Int) ∧
      (nativeCoefficients true).evaluate (fun _ => ⟨true, Or.inl rfl⟩) = (1 : Int) :=
  ⟨rfl, rfl⟩

/-- Infinitely many original positions can use the same integer sort. -/
private def integerSequence : ObservationProduct Observation.signature.SortType :=
  { Index := Nat, sort := fun _ => (), nameScope := some "integer sequence" }

/-- This coefficient observation tests whether every coordinate is zero. -/
private noncomputable def coefficientSequence :
    CoefficientReading Observation.whole (statesOf Int) (CoefficientProduct.all integerSequence) :=
  { readRing Int 0 with
    selection := .all integerSequence
    supported _ := Set.mem_univ _
    realizePoint _ _ x := x
    pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
    evaluateOn _ R _ e := by
      classical
      letI := R.scalars.ring
      exact if ∀ n, (show R.scalars.Carrier from e n) = 0 then 1 else 0 }

/-- Changing any one coordinate of the all-zero input changes the coefficient evaluation. -/
theorem every_coordinate_changes_coefficient (n : Nat) :
    coefficientSequence.evaluate (fun _ => (0 : Int)) = (1 : Int) ∧
      coefficientSequence.evaluate (fun j => if (show Nat from j.val) = n then (1 : Int) else (0 : Int)) =
        (0 : Int) := by
  classical
  change (if ∀ _ : Nat, (0 : Int) = 0 then (1 : Int) else 0) = 1 ∧
    (if ∀ j : Nat, (if j = n then (1 : Int) else 0) = 0 then (1 : Int) else 0) = 0
  constructor
  · have all : ∀ _ : Nat, (0 : Int) = 0 := fun _ => rfl
    rw [if_pos all]
  · have notAll : ¬ ∀ j : Nat, (if j = n then (1 : Int) else 0) = 0 := by
      intro all
      exact (by decide : (1 : Int) ≠ 0) (by simpa only [if_pos rfl] using all n)
    rw [if_neg notAll]

/-- The ordinary coefficient-valued observation uses the very same infinite evaluation. -/
private noncomputable def sequenceReading : Reading.{0, 0, 0, 0} :=
  { readingOf Int 0 with
    observation := .ofFunction integerSequence Int (fun e => coefficientSequence.evaluate (fun i => e i.val))
    coefficients := some ⟨CoefficientProduct.all integerSequence, coefficientSequence⟩
    sharedInputs := .empty _
    observationPlacement := .external }

/-- Restricting the coefficient product to a subset does not rename its indexed slots. -/
theorem proper_subset_keeps_shared_slot :
    let product : CoefficientProduct Observation.signature.SortType := .indexed Nat {i | i < 2} (fun _ => ()) (some "integer sequence")
    let first : product.product.Index := ⟨0, by decide⟩
    sequenceReading.SharesInput product first (0 : Nat) ∧
      ¬ sequenceReading.SharesInput product first (1 : Nat) := by
  dsimp only
  have shared : sequenceReading.SharesInput (.indexed Nat {i | i < 2} (fun _ => ()) (some "integer sequence"))
      ⟨0, by decide⟩ (0 : Nat) := ⟨rfl, Or.inl ⟨rfl, by decide, rfl, HEq.rfl⟩⟩
  exact ⟨shared, fun second => Nat.zero_ne_one (Reading.sharedInput_unique _ _ _ shared second)⟩

/-- The coefficient comparison evaluates the selected infinite product. -/
noncomputable def infinite_coefficient_comparison : ReadingComparison sequenceReading sequenceReading where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel n := nomatch n.val
  state :=
    { onSort := fun _ => id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := .changed (ReadingInputMap.identity coefficientSequence.selection.used)
    { baseMap := RingHom.id Int
      coefficients := RingHom.id Int
      algebra_commutes := rfl
      evaluate_commutes _ := rfl }
  coefficientInputs := ⟨ReadingInputMap.identity_usesCoefficientNames _, ReadingInputMap.identity_respectsOrdinary _ _ _⟩
  value := id
  commutes _ := rfl

/-- The two projections give distinct algebras with the same underlying coefficient ring. -/
private def projectionReading (f : (Int × Int) →+* Int) :
    CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) where
  base := ringOf (Int × Int)
  algebra := ⟨ringOf Int, f⟩
  scheme := offsetScheme (ringOf (Int × Int))
  realization := (0 : Int)
  selection := .ofRenaming (Δ := [()]) (fun i => i)
  supported _ := Set.mem_univ _
  realizePoint _ _ x := x
  pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
  evaluateOn _ R _ e :=
    letI := R.scalars.ring
    (show R.scalars.Carrier from e ⟨(), .here⟩) + R.fromBase ((0, 1) : Int × Int)

/-- Varying only the algebra structure map cannot bypass evaluation compatibility. -/
theorem projection_algebras_cannot_compare :
    ¬ Nonempty (CoefficientComparison (projectionReading (RingHom.fst Int Int))
      (projectionReading (RingHom.snd Int Int)) id (fun _ x => x)) := by
  rintro ⟨comparison⟩
  cases comparison with
  | fixed same =>
    rcases same with ⟨sameBase, sameAlgebra, _, _, _, _, _, _, _⟩
    have sameBase_eq : sameBase = rfl := Subsingleton.elim _ _
    cases sameBase_eq
    classical
    let value (R : CoefficientAlgebra (ringOf (Int × Int))) : Int :=
      if h : R.scalars = ringOf Int then
        (show (ringOf Int).Carrier from h ▸ (R.fromBase ((0, 1) : Int × Int)))
      else 0
    have mapped := congrArg value sameAlgebra
    have impossible : (0 : Int) = 1 := by
      simpa only [value, projectionReading, dif_pos rfl] using mapped
    exact (by decide : (0 : Int) ≠ 1) impossible
  | changed inputs comparison =>
    let f : Int →+* Int := comparison.coefficients
    let e : inputs.Values (statesOf Int).carrier := ⟨fun _ => (0 : Int), fun _ => (0 : Int)⟩
    let j : (projectionReading (RingHom.snd Int Int)).selection.used.Index := ⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩
    have square := comparison.evaluate_commutes e
    change (show Int from inputs.mapValues (fun _ x => x) e j) +
      (1 : Int) = f 0 at square
    have zero := inputs.mapValues_ofSort (fun _ (x : Int) => x) (fun _ => (0 : Int))
      (fun _ => (0 : Int)) (fun _ => rfl) j
    change inputs.mapValues (fun _ x => x) e j = (0 : Int) at zero
    have impossible : (1 : Int) = f 0 := by simpa only [zero, zero_add] using square
    exact (by decide : (1 : Int) ≠ 0) (impossible.trans f.map_zero)

/-- Use the constant evaluation to test base compatibility independently of the evaluation square. -/
private def zeroProjectionReading (f : (Int × Int) →+* Int) :
    CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) :=
  { projectionReading f with
    evaluateOn _ R _ _ :=
      letI := R.scalars.ring
      0 }

/-- The projections compare on constant evaluations when the base coordinates are exchanged. -/
def projection_swap_comparison :
    CoefficientReading.Change (zeroProjectionReading (RingHom.fst Int Int))
      (zeroProjectionReading (RingHom.snd Int Int)) id where
  baseMap := (RingHom.snd Int Int).prod (RingHom.fst Int Int)
  coefficients := RingHom.id Int
  algebra_commutes := RingHom.ext fun _ => rfl
  evaluate_commutes := fun _ => rfl

/-- Even equal evaluations cannot justify the projection change over an unchanged base map. -/
theorem projection_change_cannot_keep_base_map
    (change : CoefficientReading.Change (zeroProjectionReading (RingHom.fst Int Int))
      (zeroProjectionReading (RingHom.snd Int Int)) id) :
    change.baseMap ≠ RingHom.id (Int × Int) := by
  intro same
  have point := DFunLike.congr_fun change.algebra_commutes ((0, 1) : Int × Int)
  change change.coefficients (0 : Int) = (show Int × Int from change.baseMap (0, 1)).2 at point
  rw [same] at point
  let f : Int →+* Int := change.coefficients
  exact (by decide : (0 : Int) ≠ 1) (f.map_zero.symm.trans point)

/-- Two mentions of a state read the same point even in a longer coefficient context. -/
theorem repeated_coefficient_input :
    let base := readRing Int 0
    let repeated : CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) :=
      { base with
        selection := .ofRenaming (Δ := [(), ()]) (fun {s} _ => match s with
          | () => .here)
        supported _ := Set.mem_univ _
        realizePoint := fun _ _ x => x
        pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
        evaluateOn := fun _ _ _ e => e ⟨(), .here⟩ }
    ∀ e : (ObservationProduct.ofList [()]).Values (statesOf Int).carrier,
      repeated.inputTuple e ⟨(), .here⟩ = repeated.inputTuple e ⟨(), .there .here⟩ :=
  fun _ => rfl

/-- The ordinary reading has the same observation and no selected coefficient evaluation. -/
private def plainInteger : Reading.{0, 0, 0, 0} := { readingOf Int 0 with coefficients := none }

/-- The singleton observation and the coefficient input use the same integer state. -/
private def toOrdinaryInput :
    ReadingInputMap (readRing Int 0).selection.used (.ofSort ()) id where
  extra := .empty
  coordinate _ := ⟨.inl ⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩, rfl⟩
  extra_used i := nomatch i

/-- Read the same state when adding the singleton coefficient evaluation. -/
private def toCoefficientInput :
    ReadingInputMap (.ofSort ()) (readRing Int 0).selection.used id where
  extra := .empty
  coordinate j := ⟨.inl PUnit.unit, by cases j.val.1; rfl⟩
  extra_used i := nomatch i

/-- Forgetting coefficients gives an explicit map from the old evaluation to the ordinary value. -/
def forgetCoefficients : Reading.CoefficientCompatibility (readingOf Int 0) plainInteger id
    (fun _ x => x) :=
  .compare ⟨toOrdinaryInput, id, fun e => by
    let x : Int := e.1 ⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩
    change x = x + 0
    exact (Int.add_zero x).symm⟩

/-- Introducing coefficients supplies the corresponding map in the other direction. -/
def introduceCoefficients : Reading.CoefficientCompatibility plainInteger (readingOf Int 0) id
    (fun _ x => x) :=
  ⟨toCoefficientInput, id, fun e => by
    let x : Int := e.1 PUnit.unit
    change x + 0 = x
    exact Int.add_zero x⟩

/-- This coefficient evaluation gives the same result at different observed states. -/
private def constantCoefficient : Reading.{0, 0, 0, 0} :=
  { readingOf Int 0 with
    coefficients := some ⟨.ofList [()], { readRing Int 0 with
      evaluateOn _ R _ _ :=
        letI := R.scalars.ring
        0 }⟩ }

/-- Two coefficient settings at the same algebra with different schemes and rules. -/
private def scalarRule (reading : CoefficientReading Observation.whole (statesOf Int) (.ofList [()])) (value : Nat) :
    CoefficientReading Observation.whole (statesOf Int) (.ofList [()]) :=
  { reading with
    evaluateOn _ R _ _ :=
      letI := R.scalars.ring
      (value : R.scalars.Carrier) }

/-- Fixed coefficients cannot bypass a change from a constant zero rule to a constant one rule. -/
theorem incompatible_coefficient_rules :
    ¬ Nonempty (CoefficientComparison
      (scalarRule (readRing Int 0) 0) (scalarRule collapsedReading 1) id (fun _ x => x)) := by
  rintro ⟨comparison⟩
  cases comparison with
  | fixed same =>
    have equal := eq_of_heq same.rule
    have impossible : (0 : Int) = 1 :=
      congrFun (congrFun (congrFun (congrFun equal PUnit.unit) (readRing Int 0).algebra) (0 : Int))
        (fun _ => (0 : Int))
    exact (by decide : (0 : Int) ≠ 1) impossible
  | changed _ comparison =>
    let f : Int →+* Int := comparison.coefficients
    have impossible : (1 : Int) = f 0 :=
      comparison.evaluate_commutes ⟨fun _ => (0 : Int), fun _ => (0 : Int)⟩
    exact (by decide : (1 : Int) ≠ 0) (impossible.trans f.map_zero)

/-- The forgotten coefficient value cannot distinguish the two ordinary observations. -/
theorem forgetting_does_not_factor_through_scalar :
    ∀ comparison : Reading.CoefficientCompatibility constantCoefficient plainInteger id (fun _ x => x),
      comparison = .project := by
  rintro (_ | ⟨inputs, value, commutes⟩)
  · rfl
  exfalso
  have atValue (x : Int) : x = value (0 : Int) := by
    let e : inputs.Values (statesOf Int).carrier := ⟨fun _ => x, fun _ => x⟩
    have square := commutes e
    change inputs.mapValues (fun _ x => x) e PUnit.unit = value (0 : Int) at square
    have mapped := inputs.mapValues_ofSort (fun _ (a : Int) => a) (fun _ => x) (fun _ => x)
      (fun _ => rfl) PUnit.unit
    exact mapped.symm.trans square
  exact (by decide : (0 : Int) ≠ 1) ((atValue 0).trans (atValue 1).symm)

/-- Forgetting the constant coefficient output leaves the ordinary comparison available. -/
def forget_independent_scalar : ReadingComparison constantCoefficient plainInteger :=
  { fixedCoefficientComparison with
    declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
    coefficientChange := .project
    coefficientInputs := True.intro
    coefficientProjection := fun _ => rfl }

/-- Compare the ordinary view of an independently specified coefficient reading. -/
def compare_independent_scalar_ordinary_view :
    ReadingComparison plainInteger constantCoefficient.ordinaryPart :=
  { fixedCoefficientComparison with
    declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
    coefficientChange := PUnit.unit
    coefficientInputs := True.intro
    coefficientProjection := True.intro }

/-- The ordinary projection of either side carries a single observable value. -/
private def unitObservation (r : Reading.{0, 0, 0, 0}) (s : r.presentation.signature.SortType) :
    Reading.{0, 0, 0, 0} :=
  { r with
    observation := .ofSort s PUnit (fun _ => PUnit.unit)
    ValueStructure _ := Unit
    valueStructure := ()
    sharedInputs := .empty _
    observationPlacement := .external
    observationDeclared _ named := nomatch named }

/-- A variable scalar cannot be introduced by a value map from a single ordinary value. -/
theorem varying_scalar_introduction_needs_value_map :
    IsEmpty ((unitObservation plainInteger ()).CoefficientCompatibility (unitObservation (readingOf Int 0) ())
      id (fun _ x => x)) := by
  constructor
  rintro ⟨inputs, map, square⟩
  have forced (x : Int) : x = map PUnit.unit := by
    let e : inputs.Values (statesOf Int).carrier := ⟨fun _ => x, fun _ => x⟩
    have commutes := square e
    let j : (readRing Int 0).selection.used.Index := ⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩
    change (show Int from inputs.mapValues (fun _ y => y) e j) + (0 : Int) = map PUnit.unit at commutes
    rw [Int.add_zero] at commutes
    have mapped := inputs.mapValues_ofSort (X := (statesOf Int).carrier) (Y := (statesOf Int).carrier)
      (fun _ y => y) (fun _ => x) (fun _ => x) (fun _ => rfl) j
    exact mapped.symm.trans commutes
  exact Int.zero_ne_one ((forced 0).trans (forced 1).symm)

/-- The scalar comparison needs no input once its chosen evaluation is constant. -/
private def nullaryCoefficient : CoefficientReading Observation.whole (statesOf Int) (.ofList []) where
  base := ringOf Int
  algebra := ⟨ringOf Int, RingHom.id Int⟩
  scheme := offsetScheme (ringOf Int)
  realization := (1 : Int)
  selection := .ofRenaming fun i => i
  supported i := nomatch i.2
  realizePoint _ _ := id
  pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
  evaluateOn _ R _ _ :=
    letI := R.scalars.ring
    1

/-- The nullary evaluation retains its offset as explicit coefficient data. -/
private def taggedNullaryCoefficient : CoefficientReading Observation.whole (statesOf Int) (.ofList []) :=
  { nullaryCoefficient with
    scheme := { offsetScheme (ringOf Int) with
      Choice := Int
      pointPrograms _ _ := .identity _ }
    choice := 1
    pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
    evaluateOn parameter R _ _ := R.fromBase parameter }

/-- A coefficient parameter survives the declaration restriction and determines the evaluation. -/
theorem restricted_evaluation_keeps_coefficient_parameter :
    taggedNullaryCoefficient.RespectsRestriction Observation.missingSort.context (fun _ h => h.elim) :=
  ⟨(fun i => nomatch i.2), ⟨(fun _ _ _ _ => none), (fun i => nomatch i.2), (fun _ _ _ _ _ _ _ i => nomatch i.2)⟩, (fun _ _ _ => rfl)⟩

/-- A fixed coefficient parameter cannot make an ambient realization offset local. -/
theorem coefficient_choice_does_not_hide_realization :
    let reading := { taggedNullaryCoefficient with evaluateOn := fun _ _ offset _ => offset }
    ¬ reading.RespectsRestriction Observation.missingSort.context (fun _ h => h.elim) := by
  dsimp only
  intro localRule
  have h : (0 : Int) = 1 := localRule.agrees ⟨(0 : Int), fun i => nomatch i.2⟩
    ⟨(1 : Int), fun i => nomatch i.2⟩ ⟨RestrictedStructure.Agrees.refl _, rfl⟩
  exact Int.zero_ne_one h

/-- One coefficient algebra can localize an evaluation even when another algebra distinguishes offsets. -/
private def selectedCoefficientAlgebra : CoefficientReading Observation.whole (statesOf Int) (.ofList []) where
  base := ringOf (Int × Int)
  algebra := ⟨ringOf Int, RingHom.fst Int Int⟩
  scheme := offsetScheme (ringOf (Int × Int))
  realization := (0 : Int)
  selection := .ofRenaming fun i => i
  supported i := nomatch i.2
  realizePoint _ _ := id
  pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
  evaluateOn _ R offset _ :=
    letI := R.scalars.ring
    R.fromBase ((0, 1) : Int × Int) * (show R.scalars.Carrier from offset)

/-- The selected evaluation localizes without imposing equality on the unused second projection. -/
theorem restriction_uses_only_selected_coefficient_algebra :
    selectedCoefficientAlgebra.RespectsRestriction Observation.missingSort.context (fun _ h => h.elim) ∧
      let unused : CoefficientAlgebra selectedCoefficientAlgebra.base := ⟨ringOf Int, RingHom.snd Int Int⟩
      selectedCoefficientAlgebra.evaluateOn PUnit.unit unused (0 : Int) (fun j => nomatch j.2) ≠
        selectedCoefficientAlgebra.evaluateOn PUnit.unit unused (1 : Int) (fun j => nomatch j.2) := by
  refine ⟨⟨(fun i => nomatch i.2), ⟨(fun _ _ _ _ => none), (fun i => nomatch i.2), (fun _ _ _ _ _ _ _ i => nomatch i.2)⟩, ?_⟩, ?_⟩
  · intro left right _
    change (0 : Int) * (show Int from left.1) = 0 * (show Int from right.1)
    simp
  · change (1 : Int) * 0 ≠ 1 * 1
    decide

/-- Read a constant output from an ordinary product with an empty carrier. -/
private def emptyOrdinaryReading : Reading.{0, 0, 0, 0} :=
  { Observation.reading id with
    structureData := statesOf Empty
    observation := .ofFunction (.ofSort ()) PUnit (fun _ => PUnit.unit)
      (fun _ => some ⟨(fun _ => PUnit.unit), fun _ => rfl⟩)
    realize _ := statesOf Empty
    coefficients := none
    sharedInputs := .empty _
    observationPlacement := .external
    observationDeclared _ named := nomatch named }

/-- A Boolean observation specifies its value even when the original input is empty. -/
private def emptyBoolObservation : StateObservation (statesOf Empty) :=
  .ofFunction (.ofSort ()) Bool (fun _ => false) (fun _ => some ⟨(fun _ => false), fun _ => rfl⟩)

/-- A comparison cannot choose a different value at the only retained empty tuple. -/
theorem restricted_empty_observation_keeps_specified_value :
    ¬ emptyBoolObservation.RespectsRestriction ∅ (fun _ => true) := by
  intro wrong
  have correct : emptyBoolObservation.RespectsRestriction ∅ (fun _ => false) :=
    ⟨(fun _ => rfl), Or.inr rfl⟩
  have maps := correct.unique wrong
  exact Bool.noConfusion (congrFun maps (fun i => i.property.elim))

/-- Read a constant ordinary value and the selected nullary coefficient evaluation. -/
private def nullaryCoefficientReading : Reading.{0, 0, 0, 0} :=
  { readingOf Int 1 with
    observation := .ofFunction .empty PUnit (fun _ => PUnit.unit)
    coefficients := some ⟨.ofList [], nullaryCoefficient⟩
    sharedInputs := .empty _
    observationPlacement := .external
    observationDeclared _ named := nomatch named }

/-- Share the coefficient coordinate with the only position of a named ordinary observation. -/
private noncomputable def sharedScalarTarget : Reading.{0, 0, 0, 0} :=
  { readingOf Int 0 with
    observation := .ofContext [()] Int (fun e => e .here) (some "typed variables")
    coefficients := some ⟨.ofList [()], pointReading⟩
    sharedInputs := .empty _
    observationPlacement := .external }

/-- Use the same ordinary position while selecting a nullary coefficient evaluation. -/
private noncomputable def sharedScalarSource : Reading.{0, 0, 0, 0} :=
  { sharedScalarTarget with coefficients := some ⟨.ofList [], nullaryCoefficient⟩ }

/-- Keep the external position after dropping its source declaration and select the target cover. -/
private noncomputable def keepSharedScalar : ReadingContextChange sharedScalarSource sharedScalarTarget
    (Interpretation.identity Observation.presentation.theory) where
  retained := Observation.missingSort.context
  inside _ h := h.elim
  supporting := fun _ => Interpretation.identity Observation.presentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces _ := ∅
  addedTargetPieces := Set.univ
  keptExternalInputs := Set.univ
  localSupport _ _ h := h.elim

/-- The external observation alone cannot reintroduce a sort into a nullary coefficient evaluation. -/
theorem unshared_ordinary_cannot_restore_coefficient_carrier :
    (sharedScalarSource.coefficientContext keepSharedScalar.retained keepSharedScalar.observationInputs
      nullaryCoefficient.selection).declarations = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  rintro d (inContext | ⟨⟨input, _⟩, _, _, _, _, _⟩)
  · exact inContext
  · exact nomatch input.2

/-- The empty source coefficient tuple supplies the target coordinate through its ordinary share. -/
private noncomputable def sharedScalarInputs : ReadingInputMap
    nullaryCoefficient.selection.used (readRing Int 0).selection.used id where
  extra := .ofSort ()
  coordinate j := ⟨.inr PUnit.unit, by cases j.val.1; rfl⟩
  extra_used k := by
    cases k
    exact ⟨⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩, rfl⟩

/-- The retained ordinary position supplies the actual square after its declaration is forgotten. -/
noncomputable def retained_external_state_feeds_coefficient_square :
    ReadingComparison sharedScalarSource sharedScalarTarget where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel name := nomatch name.val
  state :=
    { onSort _ _ := (1 : Int)
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .changed keepSharedScalar
  observationSupport := ⟨False.elim, False.elim⟩
  declaredObservations := .external
  coefficientChange := .changed sharedScalarInputs
    { baseMap := RingHom.id Int
      coefficients := RingHom.id Int
      algebra_commutes := rfl
      evaluate_commutes _ := rfl }
  coefficientInputs := by
    let first : sharedScalarSource.observation.product.Index := ⟨(), .here⟩
    refine ⟨(fun _ i => nomatch i.2), fun _ => some first, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _
      rfl
    · intro j k _ _ _
      cases j
      cases k
      rfl
    · intro _ i _
      exact nomatch i.2
    · intro _ i _
      obtain ⟨sort, value⟩ := i
      cases sort
      cases value with
      | here => exact ⟨rfl, fun ⟨q, _⟩ => nomatch q.val.2⟩
      | there later => exact nomatch later
    · intro _
      exact Or.inr (Or.inr ⟨first, Or.inr (Or.inr ⟨Set.mem_univ _, rfl, id⟩), rfl, rfl⟩)
    · intro k i same
      cases k
      cases Option.some.inj same
      exact Or.inl ⟨⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩, first,
        ⟨rfl, Or.inl ⟨rfl, by decide, rfl, HEq.rfl⟩⟩, rfl, rfl⟩
  coefficientSupport := by
    refine ⟨⟨(fun input => nomatch input.val.2), Or.inr ?_⟩, ⟨?_, Or.inl ?_⟩⟩
    · exact ⟨(fun i => nomatch i.2), ⟨(fun _ _ _ _ => none), (fun i => nomatch i.2), (fun _ _ _ _ _ _ _ i => nomatch i.2)⟩, (fun _ _ _ => rfl)⟩
    · exact fun _ => Or.inl ⟨PUnit.unit, Or.inr (Set.mem_univ _), Set.mem_univ _⟩
    · exact Set.eq_univ_of_forall (fun _ => ⟨PUnit.unit, Or.inr (Set.mem_univ _), Set.mem_univ _⟩)
  value _ := (1 : Int)
  commutes _ := rfl
  restrictedObservations := keepSharedScalar.observationSquare_of_available (.identity _)
    (fun _ _ => (1 : Int)) (fun _ => (1 : Int))
    (fun i => Or.inr (Or.inr ⟨Set.mem_univ i, rfl, id⟩))
    (fun _ => Or.inr (Or.inr ⟨Set.mem_univ _, rfl, id⟩)) (fun _ => rfl)

/-- Both ends keep a single external coordinate while only the target retains the sort declaration. -/
private noncomputable def keepBothScalarStates : ReadingContextChange sharedScalarTarget sharedScalarTarget
    (Interpretation.identity Observation.presentation.theory) where
  retained := Observation.missingSort.context
  inside _ absent := absent.elim
  supporting := fun _ => Interpretation.identity Observation.presentation.theory
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces _ := ∅
  addedTargetPieces := Set.univ
  keptExternalInputs := Set.univ
  localSupport _ _ absent := absent.elim

/-- The ordinary integer position is retained independently of its declaration. -/
private theorem bothScalarOrdinaryAvailable (i : sharedScalarTarget.observation.product.Index) :
    i ∈ keepBothScalarStates.observationInputs :=
  Or.inr (Or.inr ⟨Set.mem_univ i, rfl, id⟩)

/-- Both coefficient evaluations can read the same state despite the source declaration being forgotten. -/
noncomputable def retained_external_state_feeds_both_evaluations :
    ReadingComparison sharedScalarTarget sharedScalarTarget where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel name := nomatch name.val
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .changed keepBothScalarStates
  observationSupport := ⟨False.elim, False.elim⟩
  declaredObservations := .external
  coefficientChange := .changed (.identity pointReading.selection.used)
    { baseMap := RingHom.id Int
      coefficients := RingHom.id Int
      algebra_commutes := rfl
      evaluate_commutes _ := rfl }
  coefficientInputs :=
    ⟨ReadingInputMap.identity_usesCoefficientNames _, ReadingInputMap.identity_respectsOrdinary _ _ _ _⟩
  coefficientSupport := by
    refine ⟨⟨?_, Or.inr (pointReading_local _ ?_)⟩, ⟨?_, Or.inl ?_⟩⟩
    · intro j
      exact Or.inr ⟨j.val, bothScalarOrdinaryAvailable j.val, rfl,
        Or.inl ⟨rfl, by decide, rfl, HEq.rfl⟩⟩
    · intro i
      cases i.1
      exact Or.inr ⟨⟨⟨(), .here⟩, ⟨(), .here⟩, rfl⟩, ⟨(), .here⟩,
        bothScalarOrdinaryAvailable _, ⟨rfl, Or.inl ⟨rfl, by decide, rfl, HEq.rfl⟩⟩, rfl, Set.mem_univ _⟩
    · exact fun _ => Or.inl ⟨PUnit.unit, Or.inr (Set.mem_univ _), Set.mem_univ _⟩
    · exact Set.eq_univ_of_forall (fun _ => ⟨PUnit.unit, Or.inr (Set.mem_univ _), Set.mem_univ _⟩)
  value := id
  commutes _ := rfl
  restrictedObservations := keepBothScalarStates.observationSquare_of_available (.identity _)
    (fun _ => id) id bothScalarOrdinaryAvailable bothScalarOrdinaryAvailable (fun _ => rfl)

/-- Keep the theory fixed while changing the observation and the coefficients. -/
private def emptyToScalarInterpretation := Interpretation.identity Observation.presentation.theory

/-- Unused empty carriers impose no requirement on the joint evaluation input. -/
theorem joint_input_ignores_unused_empty_position :
    let side : Reading.{0, 0, 0, 0} := { emptyOrdinaryReading with
      observation := .ofFunction .empty PUnit (fun _ => PUnit.unit)
      sharedInputs := .empty _
      observationPlacement := .external
      observationDeclared _ named := nomatch named }
    let raw : CoefficientProduct Unit := .ofList [()]
    let selection : InputSelection raw := .ofRenaming (Δ := []) (fun i => nomatch i)
    IsEmpty (raw.product.Values side.structureData.carrier) ∧ Nonempty (side.JointInput selection) := by
  dsimp only
  refine ⟨⟨fun full => (full ⟨(), .here⟩).elim⟩, ⟨?_, ?_, ?_⟩⟩
  · intro i
    exact nomatch i
  · intro j
    have absent : False := by
      obtain ⟨⟨_, i⟩, _⟩ := j.property
      exact nomatch i
    exact absent.elim
  · intro j i
    exact nomatch i

/-- Forget the empty source sort and use the selected target coefficient cover. -/
private def forgetEmptyState : ReadingContextChange emptyOrdinaryReading nullaryCoefficientReading
    emptyToScalarInterpretation where
  retained := Observation.missingSort.context
  inside _ absent := absent.elim
  supporting := fun _ => emptyToScalarInterpretation
  equivalent := fun _ => Interpretation.Equivalent.refl _
  pieces _ := Set.univ
  localSupport _ _ absent := absent.elim

/-- The nullary target ordinary observation requires no source position. -/
private def forgetEmptyPositions : emptyOrdinaryReading.observation.product.Correspondence
    nullaryCoefficientReading.observation.product id :=
  ⟨(fun j => nomatch j), (fun j => nomatch j), (fun j => nomatch j)⟩

/-- The target coefficient evaluation has neither state inputs nor additional positions. -/
private def nullaryInputs : ReadingInputMap emptyOrdinaryReading.observation.product
    nullaryCoefficient.selection.used id where
  extra := .empty
  coordinate i := nomatch i.val.2
  extra_used i := nomatch i

/-- Specify a scalar value map whose ambient equation has an empty domain. -/
private def initialCoefficientValue (value : Int) :
    Reading.CoefficientCompatibility emptyOrdinaryReading nullaryCoefficientReading id
      (fun _ a => nomatch a) :=
  ⟨nullaryInputs, (fun _ => value), fun e => nomatch e.1 PUnit.unit⟩

/-- Even without an ambient tuple, the retained tuple detects the wrong scalar value. -/
theorem cannot_use_empty_ambient_to_skip_coefficient_square
    (left : forgetEmptyState.SourceObservationValues → PUnit)
    (right : forgetEmptyState.TargetObservationValues forgetEmptyPositions → PUnit) :
    ¬ (initialCoefficientValue 0).respectsRestrictedOrdinary
      forgetEmptyState forgetEmptyPositions left right := by
  rintro ⟨_, square⟩
  have tuple : forgetEmptyState.SourceObservationValues := fun i =>
    False.elim (by
      rcases i.property with kept | ⟨_, outside⟩ | ⟨external, _, _⟩
      · exact kept.elim
      · exact outside (Set.mem_univ _)
      · exact external.elim)
  have bad : (1 : Int) = 0 := square (tuple, fun i => nomatch i)
  exact (by decide : (1 : Int) ≠ 0) bad

/-- The same comparison is valid with the value map that commutes at the retained tuple. -/
def introduces_scalar_at_retained_tuple :
    ReadingComparison emptyOrdinaryReading nullaryCoefficientReading where
  interpretation := emptyToScalarInterpretation
  targetModel name := nomatch name.val
  state :=
    { onSort _ a := nomatch a
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := forgetEmptyPositions
  declarationChange := .changed forgetEmptyState
  coefficientChange := initialCoefficientValue 1
  coefficientInputs := by
    refine ⟨(fun j => nomatch j.val.2), ?_⟩
    exact ⟨(fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i),
      (fun j => nomatch j.val.2), (fun j => nomatch j.val.2), (fun i => nomatch i), (fun i => nomatch i)⟩
  coefficientSupport := by
    refine ⟨(fun j => nomatch j.val.2), Or.inl ?_⟩
    exact Set.eq_univ_of_forall (fun d => ⟨PUnit.unit, Or.inl ⟨PUnit.unit, Set.mem_univ _⟩, Set.mem_univ _⟩)
  value := id
  commutes e := nomatch e PUnit.unit
  restrictedObservations :=
    ⟨fun _ => PUnit.unit, fun _ => PUnit.unit,
      ⟨(fun _ => rfl), Or.inr rfl⟩,
      ⟨(fun _ => rfl), Or.inl (StateObservation.restriction_surjective_of_nonempty _ _ ⟨fun i => nomatch i⟩)⟩,
      (fun _ => rfl), ⟨(fun j => nomatch j.val.2), fun _ => rfl⟩⟩

/-- The zero ring cannot be sent to the integers by a unital coefficient map. -/
theorem zero_ring_to_integer_fails :
    ¬ Nonempty (CoefficientReading.Change (readRing PUnit PUnit.unit) (readRing Int 0)
      (fun _ _ => (0 : Int))) := by
  rintro ⟨data⟩
  let h : PUnit →+* Int := data.coefficients
  have hz : (0 : PUnit) = 1 := Subsingleton.elim _ _
  have bad : (0 : Int) = 1 := h.map_zero.symm.trans ((congrArg (fun x => h x) hz).trans h.map_one)
  exact (by decide : (0 : Int) ≠ 1) bad

/-- An explicit coefficient-change square fails for the different offsets and the identity state map. -/
theorem offset_change_fails :
    ¬ Nonempty (CoefficientReading.Change (readRing Int 0) (readRing Int 1) id) := by
  rintro ⟨data⟩
  let h : Int →+* Int := data.coefficients
  have bad : (1 : Int) = h 0 :=
    data.evaluate_commutes (fun _ => (0 : Int))
  exact (by decide : (1 : Int) ≠ 0) (bad.trans h.map_zero)

end SHIGURE.Chapter1.CoefficientTransport

namespace SHIGURE.Chapter1.InterpretationComparison

/-- A nullary relation can be interpreted by either closed truth value. -/
private def signature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Unit
  Partial := Empty
  Quantity := Empty
  totalArity := fun f => nomatch f
  relInputs := fun _ => []
  partialArity := fun p => nomatch p
  quantityArity := fun q => nomatch q

/-- With no Laws, both replacements satisfy every interpretation obligation. -/
private def theory : Theory where
  signature := signature
  LawName := Empty
  law := fun n => nomatch n

/-- A concrete model with a Boolean sort and a false nullary relation. -/
private def modelData : Structure signature where
  carrier := fun _ => Bool
  total := fun f => nomatch f
  relation := fun _ => ∅
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := fun q => nomatch q

/-- An empty family of required Laws holds in the concrete model. -/
private theorem model : theory.Holds modelData :=
  fun n => nomatch n

/-- Keep the sort map fixed while replacing the only relation with a closed formula. -/
private def interpretation (replacement : Formula signature []) : Interpretation theory theory where
  onSort := id
  translation :=
    { operation := fun op => match op with
        | .total f => nomatch f
        | .partialOp p => nomatch p
        | .quantity q => nomatch q
      relation := fun _ => replacement
      partialDomain := fun p => nomatch p }
  total f := nomatch f
  quantity q := nomatch q
  partialDefined p := nomatch p
  definedPartial p := nomatch p
  preserves n := nomatch n

/-- Soundness excludes mutual derivability of the two closed truth values. -/
theorem truth_falsehood_not_equivalent :
    ¬ Derivation.Equivalent theory (Γ := []) .truth .falsehood := by
  rintro ⟨⟨d⟩, _⟩
  exact d.sound modelData model Assignment.empty True.intro

/-- The primitive translations fail mutual derivability even with the same sort map. -/
theorem translations_not_equivalent :
    ¬ Translation.Equivalent (S := theory) (T := theory)
      (interpretation .truth).translation (interpretation .falsehood).translation :=
  fun h => truth_falsehood_not_equivalent (h.2.1 ())

/-- The two certified interpretations are distinct under the equivalence in Definition 1.9. -/
theorem interpretations_not_equivalent :
    ¬ Interpretation.Equivalent (interpretation .truth) (interpretation .falsehood) := by
  rintro ⟨equal, h⟩
  have rfl : equal = rfl := Subsingleton.elim _ _
  exact translations_not_equivalent h

end SHIGURE.Chapter1.InterpretationComparison

namespace SHIGURE.Chapter1.ResidualTransport

open RingModule

/-- Coordinate projection preserves the interpreted scalar and vector operations. -/
private def project : StructureMap (realization (Int × Int) (Int × Int)) (realization Int Int) where
  onSort
    | .scalar => Prod.fst
    | .vector => Prod.fst
  total_comm f e := by cases f <;> rfl
  relation_mem r := nomatch r
  partial_mem p := nomatch p
  partial_comm p := nomatch p
  quantity_comm q := nomatch q

/-- The closed value equation compares the declared one and zero. -/
private def equation : RingEquation signature where
  context := []
  result := .scalar
  ring := scalarVocabulary
  input := .truth
  left := scalarOne
  right := scalarZero

/-- Register the additional equation and each of the required ring Laws. -/
private def equationLaws : LawDeclarations signature where
  LawName := Sum Unit RingVocabulary.LawName
  statement
    | .inl _ => equation.toLaw
    | .inr i => scalarVocabulary.law i
  role
    | .inl _ => .additional
    | .inr _ => .required

/-- The named equation refers to the exact declarations that supply its ring. -/
private def equationDeclaration : NamedRingEquation equationLaws (.inl ()) :=
  NamedRingEquation.ofAxioms equation.write rfl Sum.inr (fun _ => rfl)

/-- The presentation retains the ordered equality under its registered name. -/
private def namedEquation : PrimitivePresentation where
  signature := signature
  laws := equationLaws
  ringEquation
    | .inl () => some equationDeclaration
    | .inr _ => none
  derived i h := by cases i <;> cases h

/-- Reading the attached equation and applying two substitutions preserves the exact Law. -/
theorem named_equation_keeps_literal_substitutions :
    let θ : Substitution signature [] [] := ⟨fun i => nomatch i⟩
    let data := (equation.write.substitute θ).substitute θ
    namedEquation.ringEquation (.inl ()) = some equationDeclaration ∧
      data.toLaw = ((namedEquation.laws.statement (.inl ())).substitute θ).substitute θ ∧
      data.equation.left = (equation.left.substitute θ).substitute θ ∧
      data.equation.right = (equation.right.substitute θ).substitute θ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Reading the residual retains even the ring Laws absent from the written equality. -/
theorem residual_retains_named_ring_laws (U : DeclarationContext namedEquation)
    (support : U.RetainsRingSupport (.inl ()))
    (i : RingVocabulary.LawName) :
    Declaration.law (P := namedEquation) (.inr i) ∈ U.declarations :=
  support (Declaration.ringLaw_mem_ringEquationSupport (equation := equationDeclaration) rfl (by exact ⟨i, rfl⟩))

/-- The named Laws supply the ring axioms on the integer model. -/
theorem named_integer_ring_laws :
    ∀ i, (equationDeclaration.written.equation.ring.law i).Holds (realization Int Int) :=
  equationDeclaration.axioms_imply (realization Int Int)
    (NamedRingEquation.axioms_hold_of_model (P := namedEquation) equationDeclaration (realization Int Int)
      (fun i => match i with
        | ⟨.inr law, _⟩ => realization_scalarLaws Int Int law)
      (by
        rintro _ ⟨law, rfl⟩
        exact Or.inl rfl))

/-- Add an unused variable of a different sort to each named ring Law. -/
private def paddedAxiom (i : RingVocabulary.LawName) : Law signature :=
  let law := scalarVocabulary.law i
  ⟨.vector :: law.context, law.input.rename (fun j => .there j),
    law.conclusion.rename (fun j => .there j)⟩

/-- The declared vector zero fills the extra variable. -/
private theorem paddedAxiom_holds_iff (A : Structure signature) (i : RingVocabulary.LawName) :
    (paddedAxiom i).Holds A ↔ (scalarVocabulary.law i).Holds A := by
  let law := scalarVocabulary.law i
  constructor
  · intro holds e he
    let extended := Assignment.cons (A.total Symbol.vectorZero Assignment.empty) e
    have input : (law.input.rename (fun j => .there j)).Holds A extended :=
      (Formula.holds_rename A _ _ _).2 (by simpa only [extended, Assignment.pull_cons_there] using he)
    have result := (Formula.holds_rename A law.conclusion (fun j => .there j) extended).1 (holds extended input)
    simpa only [extended, Assignment.pull_cons_there] using result
  · intro holds e he
    exact (Formula.holds_rename A law.conclusion (fun j => .there j) e).2
      (holds _ ((Formula.holds_rename A law.input (fun j => .there j) e).1 he))

/-- The padded ring Laws remain additional Laws in the original presentation. -/
private def paddedLaws : LawDeclarations signature where
  LawName := Sum Unit RingVocabulary.LawName
  statement
    | .inl _ => equation.toLaw
    | .inr i => paddedAxiom i
  role _ := .additional

/-- The total vector constant supplies the witness needed to use the written Law. -/
private def derivePaddedAxiom (i : RingVocabulary.LawName) :
    Derivation (paddedLaws.select (Set.range Sum.inr))
      (scalarVocabulary.law i).input (scalarVocabulary.law i).conclusion := by
  let law := scalarVocabulary.law i
  let T := paddedLaws.select (Set.range Sum.inr)
  let weaken : Renaming [] law.context := fun j => nomatch j
  let graph : Formula signature [.vector] :=
    .atom (.graph (.total Symbol.vectorZero) (fun j => .there j) .here)
  let body := graph.rename (Renaming.lift (s := .vector) weaken)
  have total : Derivation T (.truth : Formula signature []) graph.ex :=
    Derivation.graph (T := T) (.totality Symbol.vectorZero)
  have existsZero : Derivation T (.truth : Formula signature law.context) body.ex :=
    @Derivation.rename T [] law.context .truth graph.ex (@weaken) total
  let name : {a : paddedLaws.LawName // a ∈ Set.range Sum.inr} := ⟨.inr i, ⟨i, rfl⟩⟩
  have padded : Derivation T (paddedAxiom i).input (paddedAxiom i).conclusion :=
    Derivation.required (T := T) name
  exact .cut (.andIntro (.refl _) (.cut (.truth _) existsZero))
    (.existsElim (.cut (.andLeft _ _) padded))

/-- The ordered literal can refer to the chosen additional Laws with their original syntax. -/
private def paddedEquation : NamedRingEquation paddedLaws (.inl ()) where
  written := equation.write
  statement_eq := rfl
  axiomNames := Set.range Sum.inr
  axioms_derive := derivePaddedAxiom

/-- The name and its padded ring Laws belong to the same primitive presentation. -/
def paddedPresentation : PrimitivePresentation where
  signature := signature
  laws := paddedLaws
  ringEquation
    | .inl () => some paddedEquation
    | .inr _ => none
  derived _ h := by cases h

/-- A retained residual keeps a constant used in its proof, even when no written ring Law names it. -/
theorem residual_retains_witness_operation (U : DeclarationContext paddedPresentation)
    (support : U.RetainsRingSupport (.inl ())) :
    Declaration.total (P := paddedPresentation) Symbol.vectorZero ∈ U.declarations := by
  apply support
  apply Declaration.ringProof_mem_ringEquationSupport (equation := paddedEquation) (i := .zeroAdd) rfl
  have derivation_eq : paddedEquation.axioms_derive .zeroAdd = derivePaddedAxiom .zeroAdd := rfl
  rw [derivation_eq]
  unfold derivePaddedAxiom
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Set.mem_singleton _))))))

/-- The selected integer structure satisfies the additional declarations. -/
theorem padded_integer_axioms : paddedEquation.AxiomsHold (realization Int Int) := by
  rintro _ ⟨i, rfl⟩
  exact (paddedAxiom_holds_iff _ i).2 (realization_scalarLaws Int Int i)

/-- A truth formula cannot be attached to any ordered equality as its written conclusion. -/
theorem truth_without_equality_has_no_expansion (eqn : RingEquation signature) :
    ¬ Nonempty (RingEquation.Expansion eqn .truth) := by
  rintro ⟨expansion⟩
  rcases expansion.shape with ⟨_, _, _, impossible⟩ | ⟨_, _, impossible⟩ <;> cases impossible

/-- Register the scalar variable equality using its original atomic notation. -/
private def variableEquation : RingEquation signature where
  context := [.scalar, .scalar]
  result := .scalar
  ring := scalarVocabulary
  input := .truth
  left := .var .here
  right := .var (.there .here)

/-- The scalar ring Laws accompany the atom without changing its written conclusion. -/
private def variableLaws : LawDeclarations signature :=
  { equationLaws with
    statement := fun
      | .inl _ => ⟨[.scalar, .scalar], .truth, .atom (.eq .here (.there .here))⟩
      | .inr i => scalarVocabulary.law i }

/-- The atomic equality records both terms in their original order. -/
def variableEquationDeclaration : NamedRingEquation variableLaws (.inl ()) :=
  .ofAxioms (variableEquation.writeVariables .here (.there .here) rfl rfl) rfl Sum.inr (fun _ => rfl)

/-- Substitution transports the atom's literal Law and the ordered terms together. -/
theorem variable_equation_substitutes (θ : Substitution signature [.scalar, .scalar] []) :
    let written := variableEquationDeclaration.written
    (written.substitute θ).toLaw = (variableLaws.statement (.inl ())).substitute θ ∧
      (written.substitute θ).equation.left = θ .here ∧
      (written.substitute θ).equation.right = θ (.there .here) :=
  ⟨rfl, rfl, rfl⟩

/-- The product ring joint input carries the ordinary declared constants. -/
private def productInput : equation.jointInputs (realization (Int × Int) (Int × Int)) := by
  let A := realization (Int × Int) (Int × Int)
  let e : Assignment A.carrier [] := Assignment.empty
  exact ⟨e, True.intro, ⟨((1 : Int), (1 : Int)), Term.evaluates_totalValue A scalarOne e⟩,
    ⟨((0 : Int), (0 : Int)), Term.evaluates_totalValue A scalarZero e⟩⟩

/-- The non-injective coordinate projection transports the residual of the declared constants. -/
theorem residual_commutes_with_projection :
    Prod.fst (equation.residual (realization (Int × Int) (Int × Int))
      (realization_scalarLaws (Int × Int) (Int × Int)) productInput) =
    equation.residual (realization Int Int) (realization_scalarLaws Int Int)
      (equation.mapInput project productInput) :=
  equation.residual_map project (realization_scalarLaws (Int × Int) (Int × Int))
    (realization_scalarLaws Int Int) productInput

end SHIGURE.Chapter1.ResidualTransport

namespace SHIGURE.Chapter1.TranslationSupport

/-- The source names only a total constant. -/
private def sourceSignature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity := fun _ => ⟨[], ()⟩
  relInputs := fun r => nomatch r
  partialArity := fun p => nomatch p
  quantityArity := fun q => nomatch q

/-- The source places no further Laws on the constant. -/
private def source : PrimitivePresentation where
  signature := sourceSignature
  laws :=
    { LawName := Empty
      statement := fun n => nomatch n
      role := fun n => nomatch n }
  derived n := nomatch n

/-- A required Law gives totality to the target's sole partial constant. -/
private def target : PrimitivePresentation where
  signature := Partial.signature
  laws :=
    { LawName := Unit
      statement := fun _ => ⟨[], .truth, (Partial.missing (Γ := [])).defined⟩
      role := fun _ => .required }
  derived _ h := by cases h

/-- The target premise used to translate the source's total constant. -/
private def totalityPremise : target.theory.LawName := ⟨(), rfl⟩

/-- Translate the source constant to the partial constant whose totality is a required Law. -/
private def translate : Interpretation source.theory target.theory where
  onSort := id
  translation :=
    { operation := fun op => match op with
        | .total _ => Partial.missing
        | .partialOp p => nomatch p
        | .quantity q => nomatch q
      relation := fun r => nomatch r
      partialDomain := fun p => nomatch p }
  total _ := .required totalityPremise
  quantity q := nomatch q
  partialDefined p := nomatch p
  definedPartial p := nomatch p
  preserves n := nomatch n.val

/-- Keeping the translated constant's syntax alone would lose its totality premise. -/
theorem totality_premise_is_retained :
    Declaration.law () ∈ Declaration.translatedSupport translate (.total ()) :=
  Declaration.totality_derivation_support translate () (Declaration.required_mem_derivation totalityPremise)

/-- A selection excluding that required Law cannot support the constant's translation. -/
theorem selection_without_totality_fails :
    ¬ Declaration.translatedSupport translate (.total ()) ⊆
      {d | d ≠ Declaration.law ()} :=
  fun h => h totality_premise_is_retained rfl

end SHIGURE.Chapter1.TranslationSupport

namespace SHIGURE.Chapter1.RestrictedCoefficients

open DomainTransport

/-- Retain the state sort but forget the original constant and partial operation. -/
private def sortOnly : DeclarationContext withDerivedLaw where
  declarations := {.sort ()}
  closed := by
    intro a ha d hd
    have same : a = .sort () := Set.mem_singleton_iff.1 ha
    subst a
    exact hd.elim

/-- With the constant omitted the retained sort can have an empty carrier. -/
private def emptyPoints : RestrictedStructure sortOnly where
  carrier _ := Empty
  total f kept _ := by cases Set.mem_singleton_iff.1 kept
  relation r := nomatch r
  partialDomain p kept := by cases Set.mem_singleton_iff.1 kept
  partialValue p kept _ := by cases Set.mem_singleton_iff.1 kept
  quantity q := nomatch q

/-- The same scheme allows either the original points or an empty carrier. -/
private def points (original : Bool) : RestrictedStructure sortOnly :=
  if original then RestrictedStructure.restrict sortOnly A else emptyPoints

/-- Scalar changes fix these designated points and carry the retained interpretation. -/
private def scheme : CoefficientScheme sortOnly (CoefficientTransport.ringOf Int) where
  Realization _ := Bool
  structureOf _ := points
  structure_retained _ _ := RestrictedStructure.hasOnlyRetainedSorts_of_all _
    (fun s => by cases s; exact Set.mem_singleton _)
  category _ :=
    { Hom := fun a b => PLift (a = b)
      id := fun _ => ⟨rfl⟩
      comp := fun f g => ⟨f.down.trans g.down⟩
      id_comp := fun _ => Subsingleton.elim _ _
      comp_id := fun _ => Subsingleton.elim _ _
      assoc := fun _ _ _ => Subsingleton.elim _ _ }
  mapPoints f s _ x := f.down ▸ x
  mapPoints_preserves f := by
    rcases f with ⟨rfl⟩
    intro Γ a supported e held
    exact held
  mapPoints_id _ _ _ _ := rfl
  mapPoints_comp f g _ _ _ := by
    rcases f with ⟨rfl⟩
    rcases g with ⟨rfl⟩
    rfl
  permitsPoints _ _ _ _ _ := True
  permitsPoints_congr := by intros; rfl
  Native := Bool
  nativeStructure := points
  native_retained _ := RestrictedStructure.hasOnlyRetainedSorts_of_all _
    (fun s => by cases s; exact Set.mem_singleton _)
  realizeNative _ := id
  nativePoints _ _ _ _ := id
  nativePoints_permitted _ _ _ _ := True.intro
  interpretLaw _ a := (points a).satisfies
  change _ := id
  changePoints _ _ _ _ := id

/-- Choose the original points of the scheme on the actual reading structure. -/
def selection : CoefficientReading sortOnly A (.ofList [()]) where
  base := CoefficientTransport.ringOf Int
  algebra := ⟨CoefficientTransport.ringOf Int, RingHom.id Int⟩
  scheme := scheme
  realization := true
  selection := .ofRenaming (Δ := [()]) (fun i => i)
  supported i := by
    cases i.1
    exact Set.mem_singleton _
  realizePoint _ _ x := x
  pointOrigin := .declared PUnit.unit True.intro (fun _ _ => ⟨rfl, rfl⟩)
  evaluateOn _ R _ _ :=
    letI := R.scalars.ring
    0

/-- The retained structure of the other realization is empty. -/
theorem empty_alternative : IsEmpty ((scheme.structureOf selection.algebra false).carrier ()) :=
  ⟨fun x => nomatch x⟩

/-- The same reading can select the local empty realization and read no coefficient inputs. -/
def emptySelection : CoefficientReading sortOnly A (.ofList [()]) where
  base := CoefficientTransport.ringOf Int
  algebra := selection.algebra
  scheme := scheme
  realization := false
  selection := .ofRenaming (Δ := []) (fun i => nomatch i)
  supported i := nomatch i.2
  realizePoint _ h := False.elim (by obtain ⟨i, _⟩ := h; exact nomatch i.2)
  pointOrigin := .declared PUnit.unit True.intro (by
    rintro _ ⟨i, _⟩
    exact nomatch i.2)
  evaluateOn _ R _ _ :=
    letI := R.scalars.ring
    0

/-- The global observation uses Bool, alongside the selected local empty realization. -/
def readingWithEmptyRealization : Reading.{0, 0, 0, 0} where
  presentation := withDerivedLaw
  structureData := A
  observation := StateObservation.ofSort () Bool id
  context := sortOnly
  cover := ⟨Unit, fun _ => sortOnly, fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := A
  familyObservation := none
  ValueStructure := fun _ => Unit
  valueStructure := ()
  coefficients := some ⟨.ofList [()], emptySelection⟩

/-- The selected local realization is empty even though the original reading has a constant. -/
theorem selected_empty_and_unread :
    IsEmpty ((emptySelection.scheme.structureOf emptySelection.algebra emptySelection.realization).carrier ()) ∧
      ∀ e e', emptySelection.evaluate e = emptySelection.evaluate e' :=
  ⟨empty_alternative, fun _ _ => emptySelection.evaluate_eq_of_inputs (by intro i; obtain ⟨j, _⟩ := i.property; exact nomatch j.2)⟩

/-- Keeping the old total constant would force an element of that same sort. -/
theorem no_empty_full_structure : ¬ ∃ B : Structure signature, IsEmpty (B.carrier ()) := by
  rintro ⟨B, noPoint⟩
  exact noPoint.false (B.total () Assignment.empty)

/-- A singleton retained sort selects the corresponding one-sort presentation. -/
private def singleRetainedSort {P : PrimitivePresentation} {U : DeclarationContext P}
    (sort : P.signature.SortType) (kept : U.declarations = {.sort sort}) :
    ReadingOrigin Observation.presentation P U where
  signature :=
    { onSort _ := sort
      onTotal f := nomatch f
      onRel r := nomatch r
      onPartial p := nomatch p
      onQuantity q := nomatch q
      totalArity f := nomatch f
      relInputs r := nomatch r
      partialArity p := nomatch p
      quantityArity q := nomatch q }
  lawName n := nomatch n
  law_eq n := nomatch n
  law_role n := nomatch n
  lawAttachments_eq n := nomatch n
  domainAttachment_eq p := nomatch p
  names :=
    { toFun := fun _ => ⟨.sort sort, kept.symm ▸ Set.mem_singleton _⟩
      invFun := fun _ => .sort ()
      left_inv := by
        intro d
        cases d with
        | sort s => cases s; rfl
        | total f => exact nomatch f
        | relation r => exact nomatch r
        | partialOp p => exact nomatch p
        | quantity q => exact nomatch q
        | law n => exact nomatch n
      right_inv := fun d => Subtype.ext (Set.mem_singleton_iff.1 (kept ▸ d.property)).symm }
  names_eq a := by
    cases a with
    | sort s => cases s; rfl
    | total f => exact nomatch f
    | relation r => exact nomatch r
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q
    | law n => exact nomatch n
  dependencies a _ := by
    cases a with
    | sort _ => rfl
    | total f => exact nomatch f
    | relation r => exact nomatch r
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q
    | law n => exact nomatch n

/-- Present the retained sort as a typed selection of the ambient declarations. -/
private def selectedOrigin : ReadingOrigin Observation.presentation withDerivedLaw sortOnly :=
  singleRetainedSort () rfl

/-- The local state observation uses the empty carrier of the selected presentation. -/
private def emptyLocalReading : Reading.{0, 0, 0, 0} where
  presentation := Observation.presentation
  structureData := CoefficientTransport.statesOf Empty
  observation := StateObservation.ofSort () PUnit Empty.elim
  context := Observation.whole
  cover := (Observation.reading id).cover
  Family := Unit
  realize _ := CoefficientTransport.statesOf Empty
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := none
  observationPlacement := .retained (fun _ => Set.mem_univ _)
  origin := some ⟨withDerivedLaw, sortOnly, selectedOrigin⟩

/-- Equation (1.12) compares the local model in the selected language. -/
def empty_local_reading_comparison : ReadingComparison emptyLocalReading emptyLocalReading where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel n := nomatch n.val
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl

/-- Choose a presentation with a required Law whose conclusion depends on the parameter. -/
private def ambientLawPresentation (conclusion : Bool) : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Unit
      statement _ := ⟨[], .truth, if conclusion then .truth else .falsehood⟩
      role _ := .required }
  derived _ h := by cases h

/-- Select only the sort, omitting the ambient Law and operations. -/
private def ambientSortOnly : DeclarationContext (ambientLawPresentation false) where
  declarations := {.sort ()}
  closed := by
    intro a ha
    cases Set.mem_singleton_iff.1 ha
    exact Set.empty_subset _

/-- Read the selected sort of either ambient structure. -/
private def ambientReading (M : Structure signature) : Reading.{0, 0, 0, 0} where
  presentation := ambientLawPresentation false
  structureData := M
  observation := StateObservation.ofSort () Bool (fun _ => false)
  context := ambientSortOnly
  cover := ⟨Unit, fun _ => ambientSortOnly, fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := M
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := none

/-- Restrict the ambient reading to the typed sort-only presentation. -/
private def selectedReading (M : Structure signature) : Reading.{0, 0, 0, 0} :=
  (ambientReading M).restrict (singleRetainedSort () rfl)
    (StateObservation.ofSort () Bool (fun _ => false)) ()

/-- The selected comparison of the structures in Example 1.10 forgets both the bad Law
and the partial-operation domain that would obstruct the identity map. -/
def compares_after_restricting_ambient_readings : ReadingComparison (selectedReading A) (selectedReading B) where
  interpretation := Interpretation.identity Observation.presentation.theory
  targetModel n := nomatch n.val
  state :=
    { onSort _ := id
      total_comm f := nomatch f
      relation_mem r := nomatch r
      partial_mem p := nomatch p
      partial_comm p := nomatch p
      quantity_comm q := nomatch q }
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
  coefficientChange := PUnit.unit
  value := id
  commutes _ := rfl

/-- A declared observation cannot be compared by discarding its whole declaration support. -/
theorem cannot_discard_declared_observation_sort
    (comparison : ReadingComparison (selectedReading A) (selectedReading B))
    (change : comparison.ContextChange) : change.val.retained.declarations ≠ ∅ := by
  intro empty
  have support := comparison.observationSupport
  rw [change.property] at support
  have member := support.1 True.intro PUnit.unit
  rw [empty] at member
  exact member.elim

/-- Keeping a Law's name and changing its formula does not produce a selected presentation. -/
theorem cannot_change_retained_law :
    ¬ Nonempty (ReadingOrigin (ambientLawPresentation true) (ambientLawPresentation false)
      (ReadingOrigin.whole (ambientLawPresentation false))) := by
  rintro ⟨origin⟩
  have h := congrArg (fun law : Law signature => law.Holds A) (origin.law_eq ())
  have bad : (⟨[], .truth, .falsehood⟩ : Law signature).Holds A :=
    Eq.mp h (fun _ _ => True.intro)
  exact (bad Assignment.empty True.intro).elim

/-- Keep the literal Law while removing the attached ordered terms. -/
private def withoutOrderedTerms : PrimitivePresentation :=
  { CoefficientTransport.externalRingPresentation with otherOrderedEquation _ := none }

/-- Keeping a written Law also keeps its registered ordered terms. -/
theorem cannot_erase_retained_ordered_terms :
    ¬ Nonempty (ReadingOrigin withoutOrderedTerms CoefficientTransport.externalRingPresentation
      (ReadingOrigin.whole CoefficientTransport.externalRingPresentation)) := by
  rintro ⟨origin⟩
  have same := congrArg LawAttachments.equation (origin.lawAttachments_eq ())
  cases same

/-- Choose one of two derivation trees for the same Law. -/
private def proofTreePresentation (usesCut : Bool) : PrimitivePresentation where
  signature := Observation.signature
  laws :=
    { LawName := Unit
      statement _ := ⟨[], .truth, .truth⟩
      role _ := .derived }
  derived _ _ := if usesCut then .cut (.refl .truth) (.refl .truth) else .refl .truth

/-- A selected presentation can keep the exact derivation even when the proof uses a cut. -/
def keeps_derived_tree : ReadingOrigin (proofTreePresentation true) (proofTreePresentation true)
    (ReadingOrigin.whole (proofTreePresentation true)) where
  signature := .identity _
  lawName := id
  names := ⟨fun d => ⟨d, Set.mem_univ _⟩, Subtype.val, fun _ => rfl, fun d => Subtype.ext rfl⟩
  names_eq d := by cases d <;> rfl
  law_eq _ := rfl
  law_role _ := rfl
  lawAttachments_eq _ := rfl
  domainAttachment_eq p := nomatch p
  dependencies _ _ := Iff.rfl

/-- Equal support and the same conclusion cannot justify replacing the attached proof tree. -/
theorem cannot_replace_retained_derivation :
    ¬ Nonempty (ReadingOrigin (proofTreePresentation false) (proofTreePresentation true)
      (ReadingOrigin.whole (proofTreePresentation true))) := by
  rintro ⟨origin⟩
  have same := Option.some.inj (congrArg LawAttachments.proof (origin.lawAttachments_eq ()))
  have rules := congrArg (fun | RecordedDerivation.node _ rule _ => rule) same
  change (ProofRuleData.refl : ProofRuleData Observation.signature Unit) = .cut at rules
  cases rules

end SHIGURE.Chapter1.RestrictedCoefficients
