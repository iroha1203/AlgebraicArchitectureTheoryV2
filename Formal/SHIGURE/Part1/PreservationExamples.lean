import Formal.SHIGURE.Part1.IdentityInterpretation
import Formal.SHIGURE.Part1.StructureMaps
import Formal.SHIGURE.Part1.Chapter1Examples
import Formal.SHIGURE.Part1.Reading
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Ring.Prod

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
private def reading (observe : Bool → Bool) : Reading where
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
  contexts := rfl
  declarationChange :=
    { retained := whole
      inside := fun _ h => h
      observed := fun _ _ => Set.mem_univ _
      pieces := fun _ => Set.univ
      localSupport := by
        intros
        exact ⟨(), Set.mem_univ _, Set.mem_univ _⟩ }
  coefficientChange := PUnit.unit
  value := Bool.not
  commutes := fun _ => rfl

/-- No family with an empty index covers the declared Boolean sort. -/
theorem empty_cover_fails : ¬ ∃ cover : DeclarationCover whole, IsEmpty cover.Index := by
  rintro ⟨cover, hempty⟩
  obtain ⟨i, _⟩ := cover.covers (a := .sort ()) (Set.mem_univ _)
  exact hempty.false i

/-- Omitting the sole declaration from the target cannot transport the state observation. -/
private def missingSort : Reading :=
  let emptyContext : DeclarationContext presentation := ⟨∅, fun ha => ha.elim⟩
  { (reading Bool.not) with
    context := emptyContext
    cover :=
      { Index := Empty
        piece := fun i => nomatch i
        subset := fun i => nomatch i
        covers := fun h => h.elim } }

/-- Translation support for the compared observation cannot land in an empty target context. -/
theorem missing_target_sort_fails :
    ¬ Nonempty (ReadingContextChange (reading id) missingSort
      (Interpretation.identity presentation.theory)) := by
  rintro ⟨transition⟩
  have hs := transition.observed () List.mem_cons_self
  have ht : Declaration.sort () ∈ missingSort.context.declarations :=
    transition.support_subset hs (Set.mem_singleton _)
  exact ht.elim

/-- Fixing observed values along the same state map fails (1.12) at the point false. -/
theorem identityValue_fails :
    ¬ ∀ e : Assignment points.carrier [()],
      (reading Bool.not).observation.read
        ((Interpretation.identity presentation.theory).mapStates state e) =
      (reading id).observation.read e := by
  intro h
  have bad : true = false := h (Assignment.cons false Assignment.empty)
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

/-- A realization datum specifies the offset used when evaluating a state. -/
private def readRing (R : Type) [CommRing R] (offset : R) :
    CoefficientReading (statesOf R) [()] where
  Carrier := R
  ring := inferInstance
  Realization := R
  structureOf := fun _ => statesOf R
  realization := offset
  realizes := rfl
  evaluateOn data e := @Add.add R _ e.head data

/-- An identity coefficient map commutes with evaluation in the same realization. -/
def integerIdentity :
    CoefficientReading.Change (readRing Int 0) (readRing Int 0) id where
  coefficients := RingHom.id Int
  realizations := id
  realization_commutes := rfl
  evaluate_commutes := fun _ => rfl

/-- Send both coordinates of the realized state to the same integer. -/
private def diagonalStates (e : Assignment (statesOf Int).carrier [()]) :
    Assignment (statesOf (Int × Int)).carrier [()] :=
  Assignment.cons (e.head, e.head) Assignment.empty

/-- Extending integers diagonally to a product ring commutes with realized evaluation. -/
def integerDiagonal :
    CoefficientReading.Change (readRing Int 0) (readRing (Int × Int) (0, 0)) diagonalStates where
  coefficients := (RingHom.id Int).prod (RingHom.id Int)
  realizations := fun offset => (offset, offset)
  realization_commutes := rfl
  evaluate_commutes := fun _ => rfl

/-- The zero ring cannot be sent to the integers by a unital coefficient map. -/
theorem zero_ring_to_integer_fails :
    ¬ Nonempty (CoefficientReading.Change (readRing PUnit PUnit.unit) (readRing Int 0)
      (fun _ => Assignment.cons (0 : Int) Assignment.empty)) := by
  rintro ⟨data⟩
  let h : PUnit →+* Int := data.coefficients
  have hz : (0 : PUnit) = 1 := Subsingleton.elim _ _
  have bad : (0 : Int) = 1 := h.map_zero.symm.trans ((congrArg (fun x => h x) hz).trans h.map_one)
  exact (by decide : (0 : Int) ≠ 1) bad

/-- The selected offset cannot be changed while transporting the zero state by identity. -/
theorem offset_change_fails :
    ¬ Nonempty (CoefficientReading.Change (readRing Int 0) (readRing Int 1) id) := by
  rintro ⟨data⟩
  let h : Int →+* Int := data.coefficients
  have bad : (1 : Int) = h 0 :=
    data.evaluate_commutes (Assignment.cons (0 : Int) Assignment.empty)
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
  Or.inr (Or.inr (Or.inr (Set.mem_singleton _)))

/-- A selection excluding that required Law cannot support the constant's translation. -/
theorem selection_without_totality_fails :
    ¬ Declaration.translatedSupport translate (.total ()) ⊆
      {d | d ≠ Declaration.law ()} :=
  fun h => h totality_premise_is_retained rfl

end SHIGURE.Chapter1.TranslationSupport
