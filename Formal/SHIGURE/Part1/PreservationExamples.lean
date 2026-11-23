import Formal.SHIGURE.Part1.IdentityInterpretation
import Formal.SHIGURE.Part1.StructureMaps
import Formal.SHIGURE.Part1.Chapter1Examples
import Formal.SHIGURE.Part1.Reading

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
  value := Bool.not
  commutes := fun _ => rfl

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
