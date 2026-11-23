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
private def reading (observe : Bool → Bool) : Reading.{0, 0} where
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
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
  coefficientChange := PUnit.unit
  value := Bool.not
  commutes := fun _ => rfl

/-- No family with an empty index covers the declared Boolean sort. -/
theorem empty_cover_fails : ¬ ∃ cover : DeclarationCover whole, IsEmpty cover.Index := by
  rintro ⟨cover, hempty⟩
  obtain ⟨i, _⟩ := cover.covers (a := .sort ()) (Set.mem_univ _)
  exact hempty.false i

/-- The global state observation can be selected independently of the declarations. -/
private def missingSort : Reading.{0, 0} :=
  let emptyContext : DeclarationContext presentation := ⟨∅, fun ha => ha.elim⟩
  { (reading Bool.not) with
    context := emptyContext
    cover :=
      { Index := Empty
        piece := fun i => nomatch i
        subset := fun i => nomatch i
        covers := fun h => h.elim }
    coefficients := none }

/-- With fixed declarations the state observation still reads its actual structure. -/
def sameEmptyContext : ReadingComparison missingSort missingSort where
  interpretation := Interpretation.identity presentation.theory
  targetModel := model
  state := state
  contexts := .identity _
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
  coefficientChange := PUnit.unit
  value := id
  commutes := fun _ => rfl

/-- A retained declaration must translate into the selected target declarations. -/
theorem missing_target_sort_fails :
    ¬ ∃ transition : ReadingContextChange (reading id) missingSort
        (Interpretation.identity presentation.theory),
      Declaration.sort () ∈ transition.retained.declarations := by
  rintro ⟨transition, hs⟩
  have ht : Declaration.sort () ∈ missingSort.context.declarations :=
    transition.support_subset hs (Set.mem_singleton _)
  exact ht.elim

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
private def secondCover : Reading.{0, 0} :=
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
  supporting := Interpretation.identity presentation.theory
  sameSorts := rfl
  sameTranslation := HEq.rfl
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
  Native := base.Carrier
  nativeStructure _ := RestrictedStructure.restrict Observation.whole (statesOf base.Carrier)
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
  Native := Type
  nativeStructure X := RestrictedStructure.restrict Observation.whole (statesOf X)
  realizeNative _ := id
  nativePoints _ _ _ _ := id
  nativePoints_permitted _ _ _ _ := fun _ _ => Function.injective_id
  interpretLaw _ X := (RestrictedStructure.restrict Observation.whole (statesOf X)).satisfies
  change _ := id
  changePoints _ _ _ _ := id

/-- Select a Boolean realization from the large class while observing small Boolean states. -/
def all_small_realizations_reading : Reading.{0, 1} where
  presentation := Observation.presentation
  structureData := statesOf Bool
  observation := StateObservation.ofSort () Bool id
  context := Observation.whole
  cover := (Observation.reading id).cover
  Family := Unit
  realize _ := statesOf Bool
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := some ⟨[()],
    { base := ringOf Int
      algebra := ⟨ringOf Int, RingHom.id Int⟩
      scheme := allSmallRealizations
      realization := Bool
      context := [()]
      supported := fun _ _ => Set.mem_univ _
      inputs := fun i => i
      realizePoint _ _ := id
      point_permitted := fun _ _ => Function.injective_id
      evaluateOn R _ _ :=
        letI := R.scalars.ring
        0 }⟩

/-- The specified coefficient algebra and realization evaluate each state at its chosen offset. -/
private def readRing (R : Type) [CommRing R] (offset : R) :
    CoefficientReading Observation.whole (statesOf R) [()] where
  base := ringOf Int
  algebra := ⟨ringOf R, Int.castRingHom R⟩
  scheme := offsetScheme (ringOf Int)
  realization := offset
  context := [()]
  supported := fun _ _ => Set.mem_univ _
  inputs := fun i => i
  realizePoint _ _ x := x
  point_permitted := True.intro
  evaluateOn coefficients data e :=
    letI := coefficients.scalars.ring
    (show coefficients.scalars.Carrier from e.head) +
      (show coefficients.scalars.Carrier from data)

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
private def diagonalStates (e : Assignment (statesOf Int).carrier [()]) :
    Assignment (statesOf (Int × Int)).carrier [()] :=
  e.map (fun _ x => (x, x))

/-- This scheme's own scalar change sends the designated states to zero. -/
private def collapsedScheme : CoefficientScheme Observation.whole (ringOf Int) :=
  { offsetScheme (ringOf Int) with
    changePoints := fun {_} {target} _ _ _ _ _ =>
      letI := target.ring
      (0 : target.Carrier) }

/-- At the chosen integer algebra the underlying realization still reads its actual state. -/
private def collapsedReading : CoefficientReading Observation.whole (statesOf Int) [()] :=
  { readRing Int 4 with scheme := collapsedScheme }

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
    ¬ ∃ continuation : Assignment (collapsedReading.changedStructure directDiagonal.coefficients).carrier [()] →
      Assignment (statesOf (Int × Int)).carrier [()],
      ∀ e, continuation (collapsedReading.changedState directDiagonal.coefficients e) = diagonalStates e := by
  rintro ⟨continuation, agrees⟩
  let zero : Assignment (statesOf Int).carrier [()] := Assignment.cons (0 : Int) Assignment.empty
  let one : Assignment (statesOf Int).carrier [()] := Assignment.cons (1 : Int) Assignment.empty
  have same : collapsedReading.changedState directDiagonal.coefficients zero =
      collapsedReading.changedState directDiagonal.coefficients one := rfl
  have impossible : (0 : Int) = 1 :=
    congrArg (fun x => (show Int × Int from x.head).1)
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
private def readingOf (R : Type) [CommRing R] (offset : R) : Reading.{0, 0} where
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
  coefficients := some ⟨[()], readRing R offset⟩

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
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
  coefficientChange := .changed (ReadingInputMap.identity (readRing Int 4).selection.product)
    { integerDiagonal with
      evaluate_commutes := fun e => integerDiagonal.evaluate_commutes
        (InputSelection.Values.ofProduct (selection := (readRing Int 4).selection) e.1).tuple }
  value := fun x => (x, x)
  commutes := fun _ => rfl

/-- The comparison reads the transported value six at the state two with offset four. -/
theorem coefficient_comparison_at_two :
    (readRing (Int × Int) (4, 4)).evaluate
      (coefficientComparison.interpretation.mapStates coefficientComparison.state
        (Assignment.cons (2 : Int) Assignment.empty)) = ((6, 6) : Int × Int) := by
  exact integerDiagonal.evaluate_commutes (Assignment.cons (2 : Int) Assignment.empty)

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
  declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
  coefficientChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  value := fun x => (show Int from x) + (1 : Int)
  commutes := fun _ => rfl

/-- An unused extra copy of the integer sort does not change the selected state. -/
private def paddedIntegerInput : CoefficientReading Observation.whole (statesOf Int) [(), ()] :=
  { readRing Int 0 with
    inputs := fun {s} _ => match s with
      | () => .here }

/-- Both presentations describe the same single used position. -/
private theorem paddedInteger_aliases :
    HEq (readRing Int 0).selection.aliases paddedIntegerInput.selection.aliases := by
  apply heq_of_eq
  funext pos
  obtain ⟨s, x, y⟩ := pos
  cases s
  cases x with
  | here =>
    cases y with
    | here => exact propext ⟨fun _ => rfl, fun _ => rfl⟩
    | there y => exact nomatch y
  | there x => exact nomatch x

/-- The target lists an extra integer state that the evaluation never uses. -/
private def paddedIntegerReading : Reading.{0, 0} :=
  { readingOf Int 0 with coefficients := some ⟨[(), ()], paddedIntegerInput⟩ }

/-- Padding the outer product preserves the fixed comparison along the non-linear state map. -/
def fixed_comparison_with_unused_input : ReadingComparison (readingOf Int 0) paddedIntegerReading :=
  { fixedCoefficientComparison with
    declarationChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩ (Interpretation.Equivalent.refl _)
    coefficientChange := .fixed ⟨rfl, HEq.rfl, HEq.rfl⟩
      ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, paddedInteger_aliases, HEq.rfl, HEq.rfl⟩ }

/-- Sending zero to one in the fixed comparison would fail a coefficient-change square. -/
theorem fixed_comparison_has_no_scalar_change :
    ¬ Nonempty (CoefficientReading.Change (readRing Int 0) (readRing Int 0)
      (fun e => fixedCoefficientComparison.interpretation.mapStates fixedCoefficientComparison.state e)) := by
  rintro ⟨data⟩
  let h : Int →+* Int := data.coefficients
  have impossible : (1 : Int) = h 0 :=
    data.evaluate_commutes (Assignment.cons (0 : Int) Assignment.empty)
  exact (by decide : (1 : Int) ≠ 0) (impossible.trans h.map_zero)

/-- This selection changes only the point correspondence used to feed the evaluation rule. -/
private def shiftedPoint : CoefficientReading Observation.whole (statesOf Int) [()] :=
  { readRing Int 0 with
    realizePoint := fun _ _ x => (show Int from x) + (1 : Int)
    point_permitted := True.intro }

/-- A changed point correspondence cannot be hidden in the fixed comparison. -/
theorem point_change_is_not_fixed : ¬ (readRing Int 0).SameParameters shiftedPoint := by
  intro same
  have impossible : (0 : Int) = 1 :=
    congrFun (congrFun (congrFun (eq_of_heq same.points) ()) (List.mem_cons_self)) (0 : Int)
  exact (by decide : (0 : Int) ≠ 1) impossible

/-- Changing only the chosen offset still changes the realization. -/
theorem realization_change_is_not_fixed : ¬ (readRing Int 0).SameParameters (readRing Int 1) := by
  intro same
  exact (by decide : (0 : Int) ≠ 1) (eq_of_heq same.realization)

/-- The two projections give distinct algebras with the same underlying coefficient ring. -/
private def projectionReading (f : (Int × Int) →+* Int) :
    CoefficientReading Observation.whole (statesOf Int) [()] where
  base := ringOf (Int × Int)
  algebra := ⟨ringOf Int, f⟩
  scheme := offsetScheme (ringOf (Int × Int))
  realization := (0 : Int)
  context := [()]
  supported := fun _ _ => Set.mem_univ _
  inputs := fun i => i
  realizePoint _ _ x := x
  point_permitted := True.intro
  evaluateOn R _ e :=
    letI := R.scalars.ring
    (show R.scalars.Carrier from e.head) + R.fromBase ((0, 1) : Int × Int)

/-- Varying only the algebra structure map cannot bypass evaluation compatibility. -/
theorem projection_algebras_cannot_compare :
    ¬ Nonempty (CoefficientComparison (projectionReading (RingHom.fst Int Int))
      (projectionReading (RingHom.snd Int Int)) id (fun _ x => x) True) := by
  rintro ⟨comparison⟩
  cases comparison with
  | fixed _ same =>
    rcases same with ⟨sameBase, sameAlgebra, _, _, _, _, _, _⟩
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
    let j : (projectionReading (RingHom.snd Int Int)).selection.product.Index := ⟨(), .here, .here, rfl⟩
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
    CoefficientReading Observation.whole (statesOf Int) [()] :=
  { projectionReading f with
    evaluateOn R _ _ :=
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
    let repeated : CoefficientReading Observation.whole (statesOf Int) [()] :=
      { base with
        context := [(), ()]
        supported := fun _ _ => Set.mem_univ _
        inputs := fun {s} _ => match s with
          | () => .here
        realizePoint := fun _ _ x => x
        point_permitted := True.intro
        evaluateOn := fun _ _ e => e.head }
    ∀ e : Assignment (statesOf Int).carrier [()],
      repeated.inputTuple e .here = repeated.inputTuple e (.there .here) :=
  by
    dsimp only
    intro e
    apply CoefficientReading.inputTuple_eq_of_same_position
    rfl

/-- The ordinary reading has the same observation and no selected coefficient evaluation. -/
private def plainInteger : Reading.{0, 0} := { readingOf Int 0 with coefficients := none }

/-- The singleton observation and the coefficient input use the same integer state. -/
private def toOrdinaryInput :
    ReadingInputMap (readRing Int 0).selection.product (.ofSort ()) id where
  extra := .empty
  coordinate _ := ⟨.inl ⟨(), .here, .here, rfl⟩, rfl⟩
  extra_used i := nomatch i

/-- Read the same state when adding the singleton coefficient evaluation. -/
private def toCoefficientInput :
    ReadingInputMap (.ofSort ()) (readRing Int 0).selection.product id where
  extra := .empty
  coordinate j := ⟨.inl PUnit.unit, by cases j.1; rfl⟩
  extra_used i := nomatch i

/-- Forgetting coefficients gives an explicit map from the old evaluation to the ordinary value. -/
def forgetCoefficients : Reading.CoefficientCompatibility (readingOf Int 0) plainInteger id
    (fun _ x => x) True :=
  ⟨toOrdinaryInput, id, fun e => by
    let x : Int := e.1 ⟨(), .here, .here, rfl⟩
    change x = x + 0
    exact (Int.add_zero x).symm⟩

/-- Introducing coefficients supplies the corresponding map in the other direction. -/
def introduceCoefficients : Reading.CoefficientCompatibility plainInteger (readingOf Int 0) id
    (fun _ x => x) True :=
  ⟨toCoefficientInput, id, fun e => by
    let x : Int := e.1 PUnit.unit
    change x + 0 = x
    exact Int.add_zero x⟩

/-- This coefficient evaluation gives the same result at different observed states. -/
private def constantCoefficient : Reading.{0, 0} :=
  { readingOf Int 0 with
    coefficients := some ⟨[()], { readRing Int 0 with
      evaluateOn R _ _ :=
        letI := R.scalars.ring
        0 }⟩ }

/-- Two coefficient settings at the same algebra with different schemes and rules. -/
private def scalarRule (reading : CoefficientReading Observation.whole (statesOf Int) [()]) (value : Nat) :
    CoefficientReading Observation.whole (statesOf Int) [()] :=
  { reading with
    evaluateOn R _ _ :=
      letI := R.scalars.ring
      (value : R.scalars.Carrier) }

/-- Fixed coefficients cannot bypass a change from a constant zero rule to a constant one rule. -/
theorem incompatible_coefficient_rules :
    ¬ Nonempty (CoefficientComparison
      (scalarRule (readRing Int 0) 0) (scalarRule collapsedReading 1) id (fun _ x => x) True) := by
  rintro ⟨comparison⟩
  cases comparison with
  | fixed _ same =>
    have equal := eq_of_heq same.rule
    have impossible : (0 : Int) = 1 :=
      congrFun (congrFun (congrFun equal (readRing Int 0).algebra) (0 : Int))
        (Assignment.cons (0 : Int) Assignment.empty)
    exact (by decide : (0 : Int) ≠ 1) impossible
  | changed _ comparison =>
    let f : Int →+* Int := comparison.coefficients
    have impossible : (1 : Int) = f 0 :=
      comparison.evaluate_commutes ⟨fun _ => (0 : Int), fun _ => (0 : Int)⟩
    exact (by decide : (1 : Int) ≠ 0) (impossible.trans f.map_zero)

/-- The forgotten coefficient value cannot distinguish the two ordinary observations. -/
theorem forgetting_requires_a_value_map :
    ¬ Nonempty (Reading.CoefficientCompatibility constantCoefficient plainInteger id
      (fun _ x => x) True) := by
  rintro ⟨⟨inputs, value, commutes⟩⟩
  have atValue (x : Int) : x = value (0 : Int) := by
    let e : inputs.Values (statesOf Int).carrier := ⟨fun _ => x, fun _ => x⟩
    have square := commutes e
    change inputs.mapValues (fun _ x => x) e PUnit.unit = value (0 : Int) at square
    have mapped := inputs.mapValues_ofSort (fun _ (a : Int) => a) (fun _ => x) (fun _ => x)
      (fun _ => rfl) PUnit.unit
    exact mapped.symm.trans square
  exact (by decide : (0 : Int) ≠ 1) ((atValue 0).trans (atValue 1).symm)

/-- The zero ring cannot be sent to the integers by a unital coefficient map. -/
theorem zero_ring_to_integer_fails :
    ¬ Nonempty (CoefficientReading.Change (readRing PUnit PUnit.unit) (readRing Int 0)
      (fun _ => Assignment.cons (0 : Int) Assignment.empty)) := by
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
    (kept : Declaration.law (P := namedEquation) (.inl ()) ∈ U.declarations)
    (i : RingVocabulary.LawName) :
    Declaration.law (P := namedEquation) (.inr i) ∈ U.declarations :=
  U.closed kept (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl ⟨.inr i, ⟨i, rfl⟩, rfl⟩)))))

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
    (kept : Declaration.law (P := paddedPresentation) (.inl ()) ∈ U.declarations) :
    Declaration.total (P := paddedPresentation) Symbol.vectorZero ∈ U.declarations := by
  apply U.closed kept
  refine Or.inr (Or.inl (Or.inr (Or.inr ⟨RingVocabulary.LawName.zeroAdd, ?_⟩)))
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
  Or.inr (Or.inr (Or.inr (Set.mem_singleton _)))

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
  Native := Bool
  nativeStructure := points
  realizeNative _ := id
  nativePoints _ _ _ _ := id
  nativePoints_permitted _ _ _ _ := True.intro
  interpretLaw _ a := (points a).satisfies
  change _ := id
  changePoints _ _ _ _ := id

/-- Choose the original points of the scheme on the actual reading structure. -/
def selection : CoefficientReading sortOnly A [()] where
  base := CoefficientTransport.ringOf Int
  algebra := ⟨CoefficientTransport.ringOf Int, RingHom.id Int⟩
  scheme := scheme
  realization := true
  context := [()]
  supported := by
    rintro _ ⟨s, _, rfl⟩
    cases s
    exact Set.mem_singleton _
  inputs := fun i => i
  realizePoint _ _ x := x
  point_permitted := True.intro
  evaluateOn R _ _ :=
    letI := R.scalars.ring
    0

/-- The retained structure of the other realization is empty. -/
theorem empty_alternative : IsEmpty ((scheme.structureOf selection.algebra false).carrier ()) :=
  ⟨fun x => nomatch x⟩

/-- The same reading can select the local empty realization and read no coefficient inputs. -/
def emptySelection : CoefficientReading sortOnly A [()] where
  base := CoefficientTransport.ringOf Int
  algebra := selection.algebra
  scheme := scheme
  realization := false
  context := []
  supported := by
    rintro _ ⟨_, h, _⟩
    cases h
  inputs i := nomatch i
  realizePoint _ h := nomatch h
  point_permitted := True.intro
  evaluateOn R _ _ :=
    letI := R.scalars.ring
    0

/-- The global observation uses Bool, alongside the selected local empty realization. -/
def readingWithEmptyRealization : Reading.{0, 0} where
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
  coefficients := some ⟨[()], emptySelection⟩

/-- The selected local realization is empty even though the original reading has a constant. -/
theorem selected_empty_and_unread :
    IsEmpty ((emptySelection.scheme.structureOf emptySelection.algebra emptySelection.realization).carrier ()) ∧
      ∀ e e', emptySelection.evaluate e = emptySelection.evaluate e' :=
  ⟨empty_alternative, fun _ _ => emptySelection.evaluate_eq_of_inputs (fun i => nomatch i)⟩

/-- Keeping the old total constant would force an element of that same sort. -/
theorem no_empty_full_structure : ¬ ∃ B : Structure signature, IsEmpty (B.carrier ()) := by
  rintro ⟨B, noPoint⟩
  exact noPoint.false (B.total () Assignment.empty)

end SHIGURE.Chapter1.RestrictedCoefficients
