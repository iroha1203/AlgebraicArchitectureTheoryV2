import Formal.SHIGURE.Part1.IdentityInterpretation
import Formal.SHIGURE.Part1.StructureMaps
import Formal.SHIGURE.Part1.RestrictedEvaluation
import Formal.SHIGURE.Part1.CoefficientReading
import Formal.SHIGURE.Part1.SelectedPresentation

/-! # Observations and readings

Definition 1.11 separates observations of states from observations of a
family of realizations. The state component of (1.12) uses the structure
on the source signature obtained from the theory interpretation.

## Implementation notes

A state observation chooses a small indexed family of sorts. Singleton
and finite products are instances of this choice. The comparison applies
the structural map at each coordinate of the selected product.

The pulled-back structure uses the operation terms of the chosen
interpretation. Soundness of its totality and partial-domain derivations
provides the domain proofs needed to take individual term values.

The context comparison uses the actual support of a translation. An
operation can translate to a term involving several declarations, so the
support is set-valued and a source cover piece may use several target
pieces. Restriction to the retained source declarations controls which
facts can be transported.

The reading's structure is typed over its selected presentation. Retained
names can be traced to an ambient presentation through `ReadingOrigin`.
An empty carrier in the selected presentation can therefore be read even
when an omitted constant would force it to be inhabited.
An external observation reads states in the chosen signature. A reading
can also retain its input sorts for the context comparison. If an
observation is a primitive declaration, its operation and full arity
belong to a single cover piece.

A comparison with unchanged coefficient settings can use
the same evaluation rule in both realizations. Otherwise it compares the
chosen evaluations along the structural state map. The common input has
all used source positions and may include further positions that feed
the target evaluation. Sharing a position in a reading continues to
share its value in the comparison.
-/

universe u v w x

namespace SHIGURE

namespace Assignment

variable {S T : Type u} {X : T → Type u} {Γ : List S}

/-- Retype each coordinate to the named sort of the translated context. -/
def mapSorts (f : S → T) (xs : Assignment (fun s => X (f s)) Γ) :
    Assignment X (Γ.map f) :=
  ⟨Var.reindex f (fun i => xs i)⟩

/-- The retyped assignment reads the original value at its mapped position. -/
@[simp] theorem mapSorts_apply (f : S → T) (xs : Assignment (fun s => X (f s)) Γ)
    {s : S} (i : Var Γ s) : xs.mapSorts f (i.mapSorts f) = xs i :=
  Var.reindex_mapSorts f (fun j => xs j) i

/-- Equality on retyped variable positions determines the entire retyped assignment. -/
theorem ext_mapSorts (f : S → T) {xs ys : Assignment X (Γ.map f)}
    (h : ∀ {s} (i : Var Γ s), xs (i.mapSorts f) = ys (i.mapSorts f)) : xs = ys := by
  induction Γ with
  | nil => exact (eq_empty xs).trans (eq_empty ys).symm
  | cons s Γ ih =>
    have tail := ih (xs := xs.tail) (ys := ys.tail) (fun i => h (.there i))
    apply Assignment.ext
    intro t i
    cases i with
    | here => exact h .here
    | there j => exact congrArg (fun a : Assignment X (Γ.map f) => a j) tail

/-- Retyping an assignment commutes with selecting the variables of a subcontext. -/
theorem mapSorts_pull (f : S → T) {Δ : List S}
    (xs : Assignment (fun s => X (f s)) Δ) (ρ : Renaming Γ Δ) :
    (xs.mapSorts f).pull (ρ.mapSorts f) = (xs.pull ρ).mapSorts f := by
  apply ext_mapSorts f
  intro s i
  simp only [pull_apply, Renaming.mapSorts_apply, mapSorts_apply]

/-- Retyping an extended assignment leaves its bound value in the first coordinate. -/
theorem mapSorts_cons (f : S → T) {s : S} (x : X (f s))
    (xs : Assignment (fun s => X (f s)) Γ) :
    (Assignment.cons (X := fun t => X (f t)) (s := s) x xs).mapSorts f =
      Assignment.cons x (xs.mapSorts f) := by
  apply Assignment.ext
  intro _ i
  cases i <;> rfl

end Assignment

namespace Interpretation

variable {S T : Theory.{u}}

/-- Select the actual value of a term at an input known to satisfy its definedness formula. -/
private noncomputable def definedValue {sig : Signature.{u}} {Γ : List sig.SortType}
    {s : sig.SortType} (B : Structure sig) (t : Term sig Γ s) (xs : Assignment B.carrier Γ)
    (defined : t.defined.Holds B xs) : B.carrier s :=
  (t.eval B xs).get ((t.mem_domain_iff B xs).1 ((t.holds_defined B xs).1 defined))

/-- On the definedness locus, the selected value is an evaluation of the term. -/
private theorem evaluates_definedValue {sig : Signature.{u}} {Γ : List sig.SortType}
    {s : sig.SortType} (B : Structure sig) (t : Term sig Γ s) (xs : Assignment B.carrier Γ)
    (defined : t.defined.Holds B xs) : t.Evaluates B xs (definedValue B t xs defined) :=
  (t.mem_eval_iff B xs _).1 ⟨_, rfl⟩

/-- The structure data of the pullback used in (1.12).
The result satisfies the source theory by `pullback_isModel`. -/
noncomputable def pullbackStructure (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) : Structure S.signature where
  carrier s := B.carrier (u.onSort s)
  total f xs :=
    let e := xs.mapSorts u.onSort
    definedValue B (u.translation.operation (.total f)) e ((u.total f).sound B model e True.intro)
  relation r := {xs | (u.translation.relation r).Holds B (xs.mapSorts u.onSort)}
  partialDomain p := {xs | (u.translation.partialDomain p).Holds B (xs.mapSorts u.onSort)}
  partialValue p xs :=
    let e := xs.val.mapSorts u.onSort
    definedValue B (u.translation.operation (.partialOp p)) e
      ((u.partialDefined p).sound B model e xs.property)
  quantity q xs :=
    let e := xs.mapSorts u.onSort
    definedValue B (u.translation.operation (.quantity q)) e
      ((u.quantity q).sound B model e True.intro)

/-- A primitive graph in the pullback evaluates its replacement term. -/
theorem pullback_graph_iff (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) (op : Operation S.signature)
    (xs : Assignment (u.pullbackStructure B model).carrier op.arity.inputs)
    (y : (u.pullbackStructure B model).carrier op.arity.output) :
    (u.pullbackStructure B model).Graph op xs y ↔
      (u.translation.operation op).Evaluates B (xs.mapSorts u.onSort) y := by
  cases op with
  | total f =>
    rw [Structure.graph_total_iff]
    have h := evaluates_definedValue B (u.translation.operation (.total f)) (xs.mapSorts u.onSort)
      ((u.total f).sound B model (xs.mapSorts u.onSort) True.intro)
    exact ⟨fun eq => eq ▸ h, fun ev => Term.evaluates_unique B _ _ h ev⟩
  | quantity q =>
    rw [Structure.graph_quantity_iff]
    have h := evaluates_definedValue B (u.translation.operation (.quantity q))
      (xs.mapSorts u.onSort) ((u.quantity q).sound B model (xs.mapSorts u.onSort) True.intro)
    exact ⟨fun eq => eq ▸ h, fun ev => Term.evaluates_unique B _ _ h ev⟩
  | partialOp p =>
    rw [Structure.graph_partial_iff]
    let e := xs.mapSorts u.onSort
    let t := u.translation.operation (.partialOp p)
    have eval (h : (u.translation.partialDomain p).Holds B e) :
        t.Evaluates B e (definedValue B t e ((u.partialDefined p).sound B model e h)) :=
      evaluates_definedValue B t e ((u.partialDefined p).sound B model e h)
    constructor
    · rintro ⟨h, eq⟩
      exact eq ▸ eval h
    · intro ev
      have hd : t.defined.Holds B e := (t.holds_defined B e).2 ⟨_, ev⟩
      have h := (u.definedPartial p).sound B model e hd
      exact ⟨h, Term.evaluates_unique B _ _ (eval h) ev⟩

/-- The primitive facts of a pulled-back structure agree with their translated evaluation. -/
theorem pullback_atomic_iff (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) {Γ : List S.signature.SortType} (a : Atomic S.signature Γ)
    (e : Assignment (u.pullbackStructure B model).carrier Γ) :
    a.Holds (u.pullbackStructure B model) e ↔ (u.translation.atomic a).Holds B (e.mapSorts u.onSort) := by
  cases a with
  | eq x y =>
    change (e x = e y) ↔ (e.mapSorts u.onSort) (x.mapSorts u.onSort) =
      (e.mapSorts u.onSort) (y.mapSorts u.onSort)
    simp only [Assignment.mapSorts_apply]
  | rel r vars =>
    rw [Atomic.holds_rel, Translation.atomic_rel, Formula.holds_rename, Assignment.mapSorts_pull]
    rfl
  | domain p vars =>
    rw [Atomic.holds_domain, Translation.atomic_domain, Formula.holds_rename, Assignment.mapSorts_pull]
    rfl
  | graph op vars y =>
    rw [Atomic.holds_graph, pullback_graph_iff, Translation.atomic_graph, Formula.holds_rename]
    have same : (e.mapSorts u.onSort).pull
          (Renaming.cons (y.mapSorts u.onSort) (vars.mapSorts u.onSort)) =
        Assignment.cons (X := B.carrier) (s := u.onSort op.arity.output)
          (e y) ((e.pull vars).mapSorts u.onSort) := by
      apply Assignment.ext
      intro s i
      cases i with
      | here => exact Assignment.mapSorts_apply u.onSort e y
      | there i =>
        exact congrArg (fun a => a i) (Assignment.mapSorts_pull u.onSort e vars)
    rw [same, Term.holds_graph_iff, Term.mem_eval_iff]

/-- A positive formula in the pulled-back structure has its translated truth value. -/
theorem pullback_formula_iff (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) {Γ : List S.signature.SortType} (p : Formula S.signature Γ) :
    ∀ e : Assignment (u.pullbackStructure B model).carrier Γ,
      p.Holds (u.pullbackStructure B model) e ↔ (u.translation.formula p).Holds B (e.mapSorts u.onSort) := by
  induction p with
  | atom a => exact u.pullback_atomic_iff B model a
  | truth => intro; rfl
  | falsehood => intro; rfl
  | conj p q hp hq =>
    intro e
    exact (Formula.holds_conj _ _ _ _).trans
      ((and_congr (hp e) (hq e)).trans (Formula.holds_conj _ _ _ _).symm)
  | disj p q hp hq =>
    intro e
    exact (Formula.holds_disj _ _ _ _).trans
      ((or_congr (hp e) (hq e)).trans (Formula.holds_disj _ _ _ _).symm)
  | ex p ih =>
    intro e
    rw [Formula.holds_ex, Translation.formula_ex, Formula.holds_ex]
    exact exists_congr fun x => by simpa only [Assignment.mapSorts_cons] using ih (Assignment.cons x e)

/-- Interpreting a model yields a model of the source theory. -/
theorem pullback_isModel (u : Interpretation S T) (B : Structure T.signature)
    (model : T.Holds B) : S.Holds (u.pullbackStructure B model) := by
  intro name e held
  apply (u.pullback_formula_iff B model (S.law name).conclusion e).2
  apply (u.preserves name).sound B model _
  exact (u.pullback_formula_iff B model (S.law name).input e).1 held

/-- Pullback and retyping send a tuple of states through the given structural map. -/
def mapStates (u : Interpretation S T) {A : Structure S.signature}
    {B : Structure T.signature} {model : T.Holds B}
    (h : StructureMap A (u.pullbackStructure B model)) {Γ : List S.signature.SortType}
    (e : Assignment A.carrier Γ) : Assignment B.carrier (Γ.map u.onSort) :=
  (e.map h.onSort).mapSorts u.onSort

end Interpretation

/-- A state observation reads the dependent product of its selected sorts. -/
structure StateObservation {sig : Signature.{u}} (A : Structure sig) where
  /-- The indexed state sorts supplied to the observation. -/
  product : ObservationProduct sig.SortType
  /-- The values read by the observation. -/
  Output : Type u
  /-- The observation on the selected product. -/
  read : product.Values A.carrier → Output

namespace StateObservation

variable {sig : Signature.{u}} {A : Structure sig}

/-- Observe a single state's value with a function on its sort. -/
def ofSort (s : sig.SortType) (O : Type u) (f : A.carrier s → O) : StateObservation A :=
  ⟨.ofSort s, O, fun e => f (e PUnit.unit)⟩

/-- Observe an ordinary finite context, optionally naming its input positions for sharing. -/
def ofContext (Γ : List sig.SortType) (O : Type u) (f : Assignment A.carrier Γ → O)
    (nameScope : Option String := none) : StateObservation A :=
  ⟨{ ObservationProduct.ofList Γ with nameScope := nameScope }, O, fun e => f (ObservationProduct.toAssignment e)⟩

/-- Read a named total operation or quantity at its declared input tuple. -/
def ofTotalSymbol (symbol : TotalSymbol sig) : StateObservation A :=
  ofContext symbol.operation.arity.inputs (A.carrier symbol.operation.arity.output)
    ((⟨symbol, rfl⟩ : TypedTotal sig symbol.operation.arity).value A)

/-- A finite product reads the supplied typed assignment. -/
@[simp] theorem ofContext_assignment (Γ : List sig.SortType) (O : Type u)
    (f : Assignment A.carrier Γ → O) (e : Assignment A.carrier Γ) :
    (ofContext Γ O f).read (ObservationProduct.ofAssignment e) = f e := rfl

/-- Reading a singleton assignment applies the original single-sort observation. -/
@[simp] theorem ofSort_value (s : sig.SortType) (O : Type u) (f : A.carrier s → O)
    (x : A.carrier s) :
    (ofSort s O f).read (fun _ => x) = f x :=
  rfl

end StateObservation

/-- A family observation reads the family index, independently of any individual state. -/
structure FamilyObservation (Realization : Type v) where
  /-- The values used for distinguishing members of the family. -/
  Output : Type u
  /-- The function on the family of realizations. -/
  read : Realization → Output

/-- Partial identifications between independent coefficient and ordinary state positions. -/
structure SharedInputNames {S : Type u} (ordinary : ObservationProduct S) where
  /-- A coefficient position may identify one ordinary position. -/
  identify (Γ : CoefficientProduct S) : Γ.product.Index → Option ordinary.Index
  /-- Distinct coefficient positions cannot alias the same ordinary position. -/
  unique (Γ : CoefficientProduct S) {j k : Γ.product.Index} {i : ordinary.Index} :
    identify Γ j = some i → identify Γ k = some i → j = k

/-- Products with independent names need no additional identifications. -/
def SharedInputNames.empty {S : Type u} (ordinary : ObservationProduct S) : SharedInputNames ordinary :=
  ⟨fun _ _ => none, by
    intro _ _ _ _ absent _
    cases absent⟩

/-- Track whether the input sorts participate in declaration restriction. -/
inductive ObservationPlacement (Supported : Prop) where
  | external
  | retained (support : Supported)

/-- The input sorts of the observation participate in declaration restriction. -/
def ObservationPlacement.isRetained {Supported : Prop} : ObservationPlacement Supported → Prop
  | .external => False
  | .retained _ => True

/-- The theory, observations, contexts and value choices of Definition 1.11. -/
structure Reading where
  /-- The declared language, Law roles and derivations. -/
  presentation : PrimitivePresentation.{u}
  /-- The structure being read. -/
  structureData : Structure presentation.signature
  /-- The chosen state observation. -/
  observation : StateObservation structureData
  /-- The declarations selected from the presentation. -/
  context : DeclarationContext presentation
  /-- The selected cover of those declarations. -/
  cover : DeclarationCover context
  /-- A family of structures that may also be observed. -/
  Family : Type w
  /-- The structure associated to each family member. -/
  realize : Family → Structure presentation.signature
  /-- An observation on the family, when one is specified. -/
  familyObservation : Option (FamilyObservation.{x, w} Family)
  /-- The type of value-structure choices on the observation values. -/
  ValueStructure : Type u → Type u
  /-- The chosen value-structure data. -/
  valueStructure : ValueStructure observation.Output
  /-- The coefficient input context and its evaluation, when the reading uses coefficients. -/
  coefficients : Option (Σ Γ : CoefficientProduct presentation.signature.SortType,
    CoefficientReading.{u, v} context structureData Γ)
  /-- Identifications between independently named products, used at positions without a common name. -/
  sharedInputs : SharedInputNames observation.product := .empty _
  /-- An observation with retained inputs carries the supports of all its positions. -/
  observationPlacement : ObservationPlacement
    (∀ i, Declaration.sort (observation.product.sort i) ∈ context.declarations) := .external
  /-- A selected presentation can originate in an ambient context, without requiring an
  ambient expansion of its structures. -/
  origin : Option (Σ ambient : PrimitivePresentation.{u}, Σ retained : DeclarationContext ambient,
    ReadingOrigin presentation ambient retained) := none

/-- The ordinary observation is the interpretation of a retained primitive declaration. -/
structure Reading.DeclaredObservation (reading : Reading.{u, v, w, x}) where
  /-- The total operation or quantity that declares this observation. -/
  symbol : TotalSymbol reading.presentation.signature
  /-- The declaration belongs to the reading's selected context. -/
  kept : Declaration.ofOperation symbol.operation ∈ reading.context.declarations
  /-- The actual observation reads the declared interpretation. -/
  reads : reading.observation = StateObservation.ofTotalSymbol symbol

/-- A single cover piece contains the observation declaration and its full arity. -/
theorem Reading.DeclaredObservation.covered {reading : Reading.{u, v, w, x}}
    (declared : reading.DeclaredObservation) :
    ∃ i, Declaration.ofOperation declared.symbol.operation ∈ (reading.cover.piece i).declarations ∧
      Declaration.sorts (P := reading.presentation)
        (declared.symbol.operation.arity.output :: declared.symbol.operation.arity.inputs) ⊆
        (reading.cover.piece i).declarations := by
  obtain ⟨symbol, retained, reads⟩ := declared
  obtain ⟨i, kept⟩ := reading.cover.covers retained
  refine ⟨i, kept, ?_⟩
  rintro _ ⟨s, input, rfl⟩
  apply (reading.cover.piece i).closed kept
  cases symbol with
  | ordinary f => exact ⟨s, input, rfl⟩
  | quantity q => exact ⟨s, input, rfl⟩

/-- Restrict a reading to the typed presentation of its selected ambient declarations.
The new state observation is supplied on the restricted state product. The cover and
realization family are carried along the same declaration selection. -/
def Reading.restrict (reading : Reading.{u, v, w, x}) {P : PrimitivePresentation.{u}}
    (selection : ReadingOrigin P reading.presentation reading.context)
    (observation : StateObservation (selection.signature.restrict reading.structureData))
    (valueStructure : reading.ValueStructure observation.Output)
    (coefficients : Option (Σ Γ : CoefficientProduct P.signature.SortType,
      CoefficientReading.{u, v} (ReadingOrigin.whole P)
        (selection.signature.restrict reading.structureData) Γ) := none)
    (sharedInputs : SharedInputNames observation.product := .empty _) : Reading.{u, v, w, x} where
  presentation := P
  structureData := selection.signature.restrict reading.structureData
  observation := observation
  context := ReadingOrigin.whole P
  cover := selection.cover reading.cover
  Family := reading.Family
  realize a := selection.signature.restrict (reading.realize a)
  familyObservation := reading.familyObservation
  ValueStructure := reading.ValueStructure
  valueStructure := valueStructure
  coefficients := coefficients
  sharedInputs := sharedInputs
  observationPlacement := .retained (fun _ => Set.mem_univ _)
  origin := some ⟨reading.presentation, reading.context, selection⟩

/-- Finite lists have their typed coordinates, and indexed products use their original slots
even when only a proper subset of those slots occurs in the coefficient product. -/
def Reading.namedInput (reading : Reading.{u, v, w, x})
    (Γ : CoefficientProduct reading.presentation.signature.SortType) :
    Γ.product.Index → reading.observation.product.Index → Prop :=
  match Γ with
  | .ofList sorts scope => fun j i => j.1 = reading.observation.product.sort i ∧ scope ≠ none ∧
      { ObservationProduct.ofList sorts with nameScope := scope } = reading.observation.product ∧ HEq j i
  | .indexed _ _ sort scope => fun j i => sort j = reading.observation.product.sort i ∧ scope ≠ none ∧
      scope = reading.observation.product.nameScope ∧ HEq j.val i

/-- A shared coefficient coordinate uses its named ordinary position when it has one.
An explicit identification can supply a position for differently named products. -/
def Reading.SharesInput (reading : Reading.{u, v, w, x})
    (Γ : CoefficientProduct reading.presentation.signature.SortType)
    (j : Γ.product.Index) (i : reading.observation.product.Index) : Prop :=
  Γ.product.sort j = reading.observation.product.sort i ∧
    (reading.namedInput Γ j i ∨
      (reading.sharedInputs.identify Γ j = some i ∧
        (¬ ∃ k, reading.namedInput Γ j k) ∧ (¬ ∃ k, reading.namedInput Γ k i)))

/-- One coefficient position cannot alias two independently supplied ordinary positions. -/
theorem Reading.sharedInput_unique (reading : Reading.{u, v, w, x})
    (Γ : CoefficientProduct reading.presentation.signature.SortType) (j : Γ.product.Index)
    {i k : reading.observation.product.Index}
    (hi : reading.SharesInput Γ j i) (hk : reading.SharesInput Γ j k) : i = k := by
  rcases hi.2 with namedI | ⟨explicitI, noNameI, _⟩
  · rcases hk.2 with namedK | ⟨_, noNameK, _⟩
    · cases Γ with
      | ofList _ _ => exact eq_of_heq (namedI.2.2.2.symm.trans namedK.2.2.2)
      | indexed _ _ _ _ => exact eq_of_heq (namedI.2.2.2.symm.trans namedK.2.2.2)
    · exact (noNameK ⟨i, namedI⟩).elim
  · rcases hk.2 with namedK | ⟨explicitK, _, _⟩
    · exact (noNameI ⟨k, namedK⟩).elim
    · exact Option.some.inj (explicitI.symm.trans explicitK)

/-- Distinct coefficient positions remain independent when sharing ordinary inputs. -/
theorem Reading.sharedInput_injective (reading : Reading.{u, v, w, x})
    (Γ : CoefficientProduct reading.presentation.signature.SortType) {j k : Γ.product.Index}
    {i : reading.observation.product.Index}
    (hj : reading.SharesInput Γ j i) (hk : reading.SharesInput Γ k i) : j = k := by
  rcases hj.2 with namedJ | ⟨explicitJ, _, freshJ⟩
  · rcases hk.2 with namedK | ⟨_, _, freshK⟩
    · cases Γ with
      | ofList _ _ => exact eq_of_heq (namedJ.2.2.2.trans namedK.2.2.2.symm)
      | indexed _ _ _ _ => exact Subtype.ext (eq_of_heq (namedJ.2.2.2.trans namedK.2.2.2.symm))
    · exact (freshK ⟨j, namedJ⟩).elim
  · rcases hk.2 with namedK | ⟨explicitK, _, _⟩
    · exact (freshJ ⟨k, namedK⟩).elim
    · exact reading.sharedInputs.unique Γ explicitJ explicitK

/-- A state input for both evaluations assigns the same value at each shared position. -/
structure Reading.JointInput (reading : Reading.{u, v, w, x})
    (Γ : CoefficientProduct reading.presentation.signature.SortType) where
  /-- Values at the ordinary observation's positions. -/
  ordinary : reading.observation.product.Values reading.structureData.carrier
  /-- Values at the original coefficient positions. -/
  coefficient : Γ.product.Values reading.structureData.carrier
  /-- Shared positions use one state value. -/
  agrees (j : Γ.product.Index) (i : reading.observation.product.Index)
    (shared : reading.SharesInput Γ j i) :
    cast (congrArg reading.structureData.carrier shared.1) (coefficient j) = ordinary i

/-- Evaluate both observations on the same joint input. -/
def Reading.JointInput.evaluate {reading : Reading.{u, v, w, x}}
    {Γ : CoefficientProduct reading.presentation.signature.SortType}
    (input : reading.JointInput Γ)
    (coefficient : CoefficientReading.{u, v} reading.context reading.structureData Γ) :
    reading.observation.Output × coefficient.ring.Carrier :=
  (reading.observation.read input.ordinary, coefficient.evaluate input.coefficient)

namespace Declaration

variable {P Q : PrimitivePresentation.{u}}

/-- The target declarations that occur in a primitive translation, including its sorts. -/
def translatedSupport (u : Interpretation P.theory Q.theory) :
    Declaration P → Set (Declaration Q)
  | .sort s => {.sort (u.onSort s)}
  | .total f =>
    sorts ((P.signature.totalArity f).inputs.map u.onSort) ∪
      (formula (u.translation.operation (.total f)).graph ∪ derivation (u.total f))
  | .partialOp p =>
    sorts ((P.signature.partialArity p).inputs.map u.onSort) ∪
      (formula (u.translation.operation (.partialOp p)).graph ∪
        (formula (u.translation.partialDomain p) ∪
          (derivation (u.partialDefined p) ∪ derivation (u.definedPartial p))))
  | .quantity q =>
    sorts ((P.signature.quantityArity q).inputs.map u.onSort) ∪
      (formula (u.translation.operation (.quantity q)).graph ∪ derivation (u.quantity q))
  | .relation r =>
    sorts ((P.signature.relInputs r).map u.onSort) ∪ formula (u.translation.relation r)
  | .law i =>
    let law := P.laws.statement i
    sorts (law.context.map u.onSort) ∪ formula (u.translation.formula law.input) ∪
      formula (u.translation.formula law.conclusion) ∪
      match role : P.laws.role i with
      | .required => derivation (u.preserves ⟨i, role⟩)
      | .additional | .derived => ∅

/-- The translation of a total symbol retains every declaration in its totality proof. -/
theorem totality_derivation_support (u : Interpretation P.theory Q.theory) (f : P.signature.Total) :
    derivation (u.total f) ⊆ translatedSupport u (.total f) :=
  fun _ used => Or.inr (Or.inr used)

/-- A translated atom references only declarations in the image support of the source atom. -/
theorem translated_atomic_support (u : Interpretation P.theory Q.theory)
    {Γ : List P.signature.SortType} (a : Atomic P.signature Γ)
    (V : Set (Declaration Q))
    (supported : ∀ d ∈ atomic a, translatedSupport u d ⊆ V) :
    formula (u.translation.atomic a) ⊆ V := by
  cases a with
  | eq x y =>
    exact Set.empty_subset V
  | rel r vars =>
    rw [Translation.atomic_rel (S := P.signature) (T := Q.signature) u.translation r vars,
      formula_rename]
    intro d hd
    exact supported (.relation r) (Set.mem_singleton _) (Or.inr hd)
  | domain p vars =>
    rw [Translation.atomic_domain (S := P.signature) (T := Q.signature) u.translation p vars,
      formula_rename]
    intro d hd
    exact supported (.partialOp p) (Set.mem_singleton _) (Or.inr (Or.inr (Or.inl hd)))
  | graph op vars y =>
    rw [Translation.atomic_graph (S := P.signature) (T := Q.signature) u.translation op vars y,
      formula_rename]
    intro d hd
    cases op with
    | total f => exact supported (.total f) (Set.mem_singleton _) (Or.inr (Or.inl hd))
    | partialOp p => exact supported (.partialOp p) (Set.mem_singleton _) (Or.inr (Or.inl hd))
    | quantity q => exact supported (.quantity q) (Set.mem_singleton _) (Or.inr (Or.inl hd))

/-- A formula's translation uses the translated support of all its bound sorts and symbols. -/
theorem translated_formula_support (u : Interpretation P.theory Q.theory)
    {Γ : List P.signature.SortType} (p : Formula P.signature Γ) (V : Set (Declaration Q)) :
    (∀ d ∈ formula p, translatedSupport u d ⊆ V) → formula (u.translation.formula p) ⊆ V := by
  induction p with
  | atom a => exact translated_atomic_support u a V
  | truth => intro; exact Set.empty_subset V
  | falsehood => intro; exact Set.empty_subset V
  | conj p q hp hq =>
    intro keep d hd
    exact hd.elim (fun left => hp (fun x hx => keep x (Or.inl hx)) left)
      (fun right => hq (fun x hx => keep x (Or.inr hx)) right)
  | disj p q hp hq =>
    intro keep d hd
    exact hd.elim (fun left => hp (fun x hx => keep x (Or.inl hx)) left)
      (fun right => hq (fun x hx => keep x (Or.inr hx)) right)
  | @ex Γ s p ih =>
    intro keep d hd
    exact hd.elim (fun h => keep (.sort s) (Or.inl (Set.mem_singleton _)) h)
      (fun h => ih (fun x hx => keep x (Or.inr hx)) h)

/-- The support of a translated formula depends on the translation data. -/
theorem formula_support_of_same_translation
    {f g : P.signature.SortType → Q.signature.SortType}
    {left : Translation P.signature Q.signature f}
    {right : Translation P.signature Q.signature g} (sortsEqual : f = g)
    (translationEqual : HEq left right) {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    formulaSupport (P := Q) (left.formula p) = formulaSupport (P := Q) (right.formula p) := by
  subst g
  cases eq_of_heq translationEqual
  rfl

/-- The declared name underlying an evaluated state, relation, operation, or domain fact. -/
def ofFact {A : Structure P.signature} : EvaluationAtom A → Declaration P
  | .state s _ => .sort s
  | .total f _ _ _ => .total f
  | .relation r _ _ => .relation r
  | .partialDomain p _ _ | .partialGraph p _ _ _ => .partialOp p
  | .quantity q _ _ _ => .quantity q

/-- Transport of evaluation facts on one signature preserves the name used for restriction. -/
theorem ofFact_map {A B : Structure P.signature} (h : StructureMap A B)
    (a : EvaluationAtom A) :
    ofFact (P := P) (h.mapAtom a) = ofFact (P := P) a := by
  cases a <;> rfl

end Declaration

/-- The context comparison retains a source subcontext and assigns its translation support
to the selected target cover. Each source piece can use a family of target pieces. -/
structure ReadingContextChange (source target : Reading.{u, v, w, x})
    (u : Interpretation source.presentation.theory target.presentation.theory) where
  /-- The source declarations still being compared. -/
  retained : DeclarationContext source.presentation
  /-- Restriction to these declarations takes place inside the source selection. -/
  inside : retained.declarations ⊆ source.context.declarations
  /-- One can choose proofs whose supports are visible in the retained target declarations. -/
  supporting : Interpretation source.presentation.theory target.presentation.theory
  /-- These certificates interpret the same sorts as the chosen translation. -/
  sameSorts : supporting.onSort = u.onSort
  /-- These certificates justify the very same replacement terms and formulas. -/
  sameTranslation : HEq supporting.translation u.translation
  /-- A source cover piece can be compared over several target pieces. -/
  pieces : source.cover.Index → Set target.cover.Index
  /-- Each declaration's translated support is contained in the assigned target pieces. -/
  localSupport (i : source.cover.Index) {a : Declaration source.presentation} :
    a ∈ retained.declarations → a ∈ (source.cover.piece i).declarations →
    ∀ {d}, d ∈ Declaration.translatedSupport supporting a →
      ∃ j ∈ pieces i, d ∈ (target.cover.piece j).declarations

namespace ReadingContextChange

variable {source target : Reading.{u, v, w, x}}
  {u : Interpretation source.presentation.theory target.presentation.theory}

/-- The retained source declaration translates entirely inside the target context. -/
theorem support_subset (transition : ReadingContextChange source target u)
    {a : Declaration source.presentation} (ha : a ∈ transition.retained.declarations) :
    Declaration.translatedSupport transition.supporting a ⊆ target.context.declarations := by
  intro d hd
  obtain ⟨i, hi⟩ := source.cover.covers (transition.inside ha)
  obtain ⟨j, _, hj⟩ := transition.localSupport i ha hi hd
  exact target.cover.subset j hj

/-- A source sort in the restriction reaches an assigned target piece. -/
theorem sort_is_covered (transition : ReadingContextChange source target u)
    (s : source.presentation.signature.SortType)
    (retained : Declaration.sort s ∈ transition.retained.declarations) :
    ∃ i j, j ∈ transition.pieces i ∧
      Declaration.sort (u.onSort s) ∈ (target.cover.piece j).declarations := by
  obtain ⟨i, available⟩ := source.cover.covers (transition.inside retained)
  obtain ⟨j, chosen, covered⟩ := transition.localSupport i retained available (Set.mem_singleton _)
  exact ⟨i, j, chosen, congrFun transition.sameSorts s ▸ covered⟩

/-- Restrict a source piece to the declarations selected for this comparison. -/
def sourcePiece (transition : ReadingContextChange source target u) (i : source.cover.Index) :
    DeclarationContext source.presentation where
  declarations := transition.retained.declarations ∩ (source.cover.piece i).declarations
  closed h _ hd := ⟨transition.retained.closed h.1 hd, (source.cover.piece i).closed h.2 hd⟩

/-- The union of the target pieces actually assigned to a source piece. -/
def targetPiece (transition : ReadingContextChange source target u) (i : source.cover.Index) :
    DeclarationContext target.presentation where
  declarations := {d | ∃ j ∈ transition.pieces i, d ∈ (target.cover.piece j).declarations}
  closed := by
    rintro d ⟨j, assigned, mentioned⟩ e he
    exact ⟨j, assigned, (target.cover.piece j).closed mentioned he⟩

/-- Translate formula support using the specified target context for each declaration. -/
private theorem formula_support_in (transition : ReadingContextChange source target u)
    {Γ : List source.presentation.signature.SortType} (p : Formula source.presentation.signature Γ)
    (V : Set (Declaration target.presentation)) (keep : ∀ d ∈ Declaration.formulaSupport p,
      Declaration.translatedSupport transition.supporting d ⊆ V) :
    Declaration.formulaSupport (u.translation.formula p) ⊆ V := by
  rw [← Declaration.formula_support_of_same_translation transition.sameSorts transition.sameTranslation p]
  intro d hd
  rcases hd with hsort | hformula
  · obtain ⟨t, ht, rfl⟩ := hsort
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact keep (.sort s) (Or.inl ⟨s, hs, rfl⟩) (Set.mem_singleton _)
  · exact Declaration.translated_formula_support transition.supporting p V
      (fun d hd => keep d (Or.inr hd)) hformula

/-- A supported formula translates inside the declarations of the target reading. -/
theorem target_support (transition : ReadingContextChange source target u)
    {Γ : List source.presentation.signature.SortType} (p : Formula source.presentation.signature Γ)
    (retained : Declaration.formulaSupport p ⊆ transition.retained.declarations) :
    Declaration.formulaSupport (u.translation.formula p) ⊆ target.context.declarations :=
  transition.formula_support_in p _ (fun _ h => transition.support_subset (retained h))

/-- All translated support fits inside the assigned target pieces of the comparison. -/
theorem local_formula_support (transition : ReadingContextChange source target u)
    (i : source.cover.Index) {Γ : List source.presentation.signature.SortType}
    (p : Formula source.presentation.signature Γ)
    (retained : Declaration.formulaSupport p ⊆ (transition.sourcePiece i).declarations) :
    Declaration.formulaSupport (u.translation.formula p) ⊆ (transition.targetPiece i).declarations :=
  transition.formula_support_in p _ fun _ h _ hd =>
    transition.localSupport i (retained h).1 (retained h).2 hd

/-- Evaluated facts restricted to the declaration names retained by the comparison. -/
def Facts (transition : ReadingContextChange source target u)
    (A : Structure source.presentation.signature) : Type u :=
  {a : EvaluationAtom A // Declaration.ofFact a ∈ transition.retained.declarations}

/-- The state map transports evaluation facts on the retained context. -/
def mapFact (transition : ReadingContextChange source target u)
    {A B : Structure source.presentation.signature} (h : StructureMap A B)
    (a : transition.Facts A) : transition.Facts B :=
  ⟨h.mapAtom a.val, (Declaration.ofFact_map h a.val).symm ▸ a.property⟩

/-- Restriction of evaluation facts commutes with their structural transport. -/
theorem mapFact_forget (transition : ReadingContextChange source target u)
    {A B : Structure source.presentation.signature} (h : StructureMap A B) :
    Subtype.val ∘ transition.mapFact h = h.mapAtom ∘ Subtype.val :=
  rfl

end ReadingContextChange

/-- The readings select the same presentation, declarations, and cover. -/
structure Reading.SameContext (source target : Reading.{u, v, w, x}) : Prop where
  /-- The same symbols and written Laws are available. -/
  presentation : source.presentation = target.presentation
  /-- The same declarations are selected. -/
  context : HEq source.context target.context
  /-- The readings use the same cover of those declarations. -/
  cover : HEq source.cover target.cover

/-- The interpretation is equivalent to the identity across the identified theories. -/
def Interpretation.isIdentityAlong {S T : Theory.{u}} (same : S = T) (u : Interpretation S T) : Prop := by
  subst T
  exact u.Equivalent (Interpretation.identity S)

/-- A fixed selection admits any representative of the identity interpretation. -/
inductive Reading.ContextCompatibility (source target : Reading.{u, v, w, x})
    (u : Interpretation source.presentation.theory target.presentation.theory) where
  | fixed (same : source.SameContext target) :
      u.isIdentityAlong (congrArg PrimitivePresentation.theory same.presentation) →
      ContextCompatibility source target u
  | changed : ReadingContextChange source target u → ContextCompatibility source target u

/-- A restriction transports the chosen observation input supports of either reading. -/
def Reading.ContextCompatibility.retainsObservations {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    (positions : source.observation.product.Correspondence target.observation.product u.onSort) :
    source.ContextCompatibility target u → Prop
  | .fixed _ _ => True
  | .changed change =>
    (source.observationPlacement.isRetained →
      ∀ i, Declaration.sort (source.observation.product.sort i) ∈ change.retained.declarations) ∧
    (target.observationPlacement.isRetained →
      ∀ j, Declaration.sort (source.observation.product.sort (positions.position j)) ∈ change.retained.declarations)

/-- Source positions for an evaluation can be shared or supplied as further states. -/
structure ReadingInputMap {S T : Type u} (source : ObservationProduct S)
    (target : ObservationProduct T) (onSort : S → T) where
  /-- Further source positions used by the target evaluation. -/
  extra : ObservationProduct S
  /-- The source coordinate of each target input, with its corresponding sort. -/
  coordinate (j : target.Index) :
    {i : source.Index ⊕ extra.Index // onSort (Sum.elim source.sort extra.sort i) = target.sort j}
  /-- Each further source position supplies an actual target input. -/
  extra_used (i : extra.Index) : ∃ j, (coordinate j).val = .inr i

namespace ReadingInputMap

variable {S T : Type u} {source : ObservationProduct S} {target : ObservationProduct T}
  {onSort : S → T}

/-- A common input assigns values at all source and further positions. -/
abbrev Values (inputs : ReadingInputMap source target onSort) (X : S → Type u) :=
  source.Values X × inputs.extra.Values X

/-- The structural map acts at the source coordinate selected by each target input. -/
def mapValues (inputs : ReadingInputMap source target onSort)
    {X : S → Type u} {Y : T → Type u} (h : ∀ s, X s → Y (onSort s))
    (e : inputs.Values X) : target.Values Y :=
  fun j => match inputs.coordinate j with
    | ⟨.inl i, same⟩ => same ▸ h _ (e.1 i)
    | ⟨.inr i, same⟩ => same ▸ h _ (e.2 i)

/-- All positions used to supply the target evaluation come from the retained source sorts. -/
def RetainsSourceSorts (inputs : ReadingInputMap source target onSort) (retains : S → Prop) : Prop :=
  ∀ j, retains (Sum.elim source.sort inputs.extra.sort (inputs.coordinate j).val)

/-- On states constant within each sort, a target input gets the mapped sort value. -/
theorem mapValues_ofSort (inputs : ReadingInputMap source target onSort)
    {X : S → Type u} {Y : T → Type u} (h : ∀ s, X s → Y (onSort s))
    (x : ∀ s, X s) (y : ∀ t, Y t) (maps : ∀ s, h s (x s) = y (onSort s))
    (j : target.Index) :
    inputs.mapValues h (fun i => x (source.sort i), fun i => x (inputs.extra.sort i)) j = y (target.sort j) := by
  have transport {a b : T} (same : a = b) (x : Y a) (hx : x = y a) :
      (same ▸ x) = y b := by
    subst b
    exact hx
  dsimp only [mapValues]
  generalize inputs.coordinate j = coordinate
  obtain ⟨i, same⟩ := coordinate
  cases i with
  | inl i => exact transport same _ (maps (source.sort i))
  | inr i => exact transport same _ (maps (inputs.extra.sort i))

/-- Select the same positions under the identity sort map. -/
def identity (product : ObservationProduct S) : ReadingInputMap product product id where
  extra := .empty
  coordinate j := ⟨.inl j, rfl⟩
  extra_used i := nomatch i

/-- A target position that is shared with the ordinary observation gets the source position
specified by its ordinary correspondence. An extra input can supply that position if the
source coefficient evaluation does not already use it. -/
def RespectsOrdinary (inputs : ReadingInputMap source target onSort)
    {ordinarySource : ObservationProduct S} {ordinaryTarget : ObservationProduct T}
    (positions : ordinarySource.Correspondence ordinaryTarget onSort)
    (sourceShares : source.Index → ordinarySource.Index → Prop)
    (targetShares : target.Index → ordinaryTarget.Index → Prop) : Prop :=
  ∃ extraShares : inputs.extra.Index → Option ordinarySource.Index,
    (∀ k i, extraShares k = some i → inputs.extra.sort k = ordinarySource.sort i) ∧
    (∀ j k i, extraShares j = some i → extraShares k = some i → j = k) ∧
    ∀ j i, targetShares j i →
      match (inputs.coordinate j).val with
      | .inl k => sourceShares k (positions.position i)
      | .inr k => extraShares k = some (positions.position i) ∧
          ¬ ∃ q, sourceShares q (positions.position i)

/-- The identity map preserves the sharing relation of a common input layout. -/
theorem identity_respectsOrdinary (product : ObservationProduct S)
    {ordinary : ObservationProduct S} (shares : product.Index → ordinary.Index → Prop) :
    (identity product).RespectsOrdinary (.identity ordinary) shares shares := by
  exact ⟨(fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i), fun _ _ h => h⟩

end ReadingInputMap

/-- Every target evaluation position is covered where its retained source state is transported. -/
theorem ReadingContextChange.target_evaluation_input_is_covered {source target : Reading.{u, v, w, x}}
    {interpretation : Interpretation source.presentation.theory target.presentation.theory}
    (change : ReadingContextChange source target interpretation)
    {p : ObservationProduct source.presentation.signature.SortType}
    {q : ObservationProduct target.presentation.signature.SortType}
    (inputs : ReadingInputMap p q interpretation.onSort)
    (supports : inputs.RetainsSourceSorts (fun s => Declaration.sort s ∈ change.retained.declarations))
    (j : q.Index) :
    ∃ i k, k ∈ change.pieces i ∧ Declaration.sort (q.sort j) ∈ (target.cover.piece k).declarations := by
  obtain ⟨i, k, chosen, covered⟩ := change.sort_is_covered _ (supports j)
  exact ⟨i, k, chosen, (inputs.coordinate j).property ▸ covered⟩

/-- Compare two coefficient selections, keeping fixed settings or supplying an evaluation square. -/
inductive CoefficientComparison {P Q : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {V : DeclarationContext Q} {A : Structure P.signature} {B : Structure Q.signature}
    {Γ : CoefficientProduct P.signature.SortType} {Δ : CoefficientProduct Q.signature.SortType}
    (c : CoefficientReading.{u, v} U A Γ) (d : CoefficientReading.{u, v} V B Δ)
    (onSort : P.signature.SortType → Q.signature.SortType)
    (state : ∀ s, A.carrier s → B.carrier (onSort s)) where
  | fixed : c.SameParameters d → CoefficientComparison c d onSort state
  | changed (inputs : ReadingInputMap c.selection.used d.selection.used onSort) :
    CoefficientReading.EvaluationComparison c d
        (fun e : inputs.Values A.carrier => c.evaluateSelected e.1)
        (fun e => d.evaluateSelected (inputs.mapValues state e)) →
    CoefficientComparison c d onSort state

/-- With one coefficient evaluation, compare it directly or project to the ordinary output. -/
inductive OneSidedCoefficientComparison (CrossEvaluation : Type u) where
  | project
  | compare (square : CrossEvaluation)

/-- Transport the actual inputs of the ordinary or coefficient evaluations at both endpoints. -/
def Reading.CoefficientCompatibility (source target : Reading.{u, v, w, x})
    (onSort : source.presentation.signature.SortType → target.presentation.signature.SortType)
    (state : ∀ s, source.structureData.carrier s → target.structureData.carrier (onSort s)) : Type (u + 1) :=
  match source.coefficients, target.coefficients with
  | none, none => PUnit
  | some c, some d => CoefficientComparison c.2 d.2 onSort state
  | none, some d =>
    OneSidedCoefficientComparison (Σ inputs : ReadingInputMap source.observation.product d.2.selection.used onSort,
      {value : source.observation.Output → d.2.ring.Carrier //
        ∀ e : inputs.Values source.structureData.carrier,
          d.2.evaluateSelected (inputs.mapValues state e) = value (source.observation.read e.1)})
  | some c, none =>
    OneSidedCoefficientComparison (Σ inputs : ReadingInputMap c.2.selection.used target.observation.product onSort,
      {value : c.2.ring.Carrier → target.observation.Output //
        ∀ e : inputs.Values source.structureData.carrier,
          target.observation.read (inputs.mapValues state e) = value (c.2.evaluateSelected e.1)})

/-- The coefficient comparison uses the ordinary correspondence at shared state positions. -/
def Reading.CoefficientCompatibility.respectsOrdinary {source target : Reading.{u, v, w, x}}
    {onSort : source.presentation.signature.SortType → target.presentation.signature.SortType}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (onSort s)}
    (positions : source.observation.product.Correspondence target.observation.product onSort) :
    source.CoefficientCompatibility target onSort state → Prop := by
  unfold Reading.CoefficientCompatibility
  split
  · exact fun _ => True
  · rename_i c d _ _
    intro comparison
    cases comparison with
    | fixed =>
      exact ∀ (j : c.2.selection.used.Index) (k : d.2.selection.used.Index)
        (i : source.observation.product.Index) (l : target.observation.product.Index),
        HEq (c.1.slot j.val) (d.1.slot k.val) →
        source.SharesInput c.1 j.val i → target.SharesInput d.1 k.val l →
        i = positions.position l
    | changed inputs _ =>
      exact inputs.RespectsOrdinary positions
        (fun j i => source.SharesInput c.1 j.val i) (fun j i => target.SharesInput d.1 j.val i)
  · rename_i d _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare data => data.1.RespectsOrdinary positions (· = ·) (fun j i => target.SharesInput d.1 j.val i)
  · rename_i c _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare data => data.1.RespectsOrdinary positions (fun j i => source.SharesInput c.1 j.val i) (· = ·)

/-- The coefficient evaluations compared through a restriction use its retained state sorts. -/
def Reading.CoefficientCompatibility.retainsSourceSorts {source target : Reading.{u, v, w, x}}
    {onSort : source.presentation.signature.SortType → target.presentation.signature.SortType}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (onSort s)}
    (retains : source.presentation.signature.SortType → Prop) :
    source.CoefficientCompatibility target onSort state → Prop := by
  unfold Reading.CoefficientCompatibility
  split
  · exact fun _ => True
  · rename_i c _ _ _
    intro comparison
    cases comparison with
    | fixed => exact ∀ i, retains (c.2.selection.used.sort i)
    | changed inputs _ =>
      exact (∀ i, retains (c.2.selection.used.sort i)) ∧ inputs.RetainsSourceSorts retains
  · exact fun comparison => match comparison with
      | .project => True
      | .compare data => data.1.RetainsSourceSorts retains
  · rename_i c _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare data =>
        (∀ i, retains (c.2.selection.used.sort i)) ∧ data.1.RetainsSourceSorts retains

/-- Relate the coefficient square to the sorts selected by a declaration change. -/
def Reading.ContextCompatibility.retainsCoefficients {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s)}
    (contextChange : source.ContextCompatibility target u)
    (coefficientChange : source.CoefficientCompatibility target u.onSort state) : Prop :=
  match contextChange with
  | .fixed _ _ => True
  | .changed change =>
    coefficientChange.retainsSourceSorts (fun s => Declaration.sort s ∈ change.retained.declarations)

/-- In a projected comparison, evaluate the coefficient on the side where it exists and
apply the value projection to the pair of observations. The retained outputs commute. -/
def Reading.CoefficientCompatibility.projectionCommutes {source target : Reading.{u, v, w, x}}
    {onSort : source.presentation.signature.SortType → target.presentation.signature.SortType}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (onSort s)}
    (positions : source.observation.product.Correspondence target.observation.product onSort)
    (value : source.observation.Output → target.observation.Output) :
    source.CoefficientCompatibility target onSort state → Prop := by
  unfold Reading.CoefficientCompatibility
  split
  · exact fun _ => True
  · exact fun _ => True
  · rename_i d _ _
    exact fun comparison => match comparison with
      | .compare _ => True
      | .project => ∀ (e : source.observation.product.Values source.structureData.carrier)
          (t : target.JointInput d.1),
          t.ordinary = positions.mapValues state e →
          (t.evaluate d.2).1 =
            value (source.observation.read e)
  · rename_i c _ _
    exact fun comparison => match comparison with
      | .compare _ => True
      | .project => ∀ e : source.JointInput c.1,
          target.observation.read (positions.mapValues state e.ordinary) = (value ∘ Prod.fst) (e.evaluate c.2)

/-- A comparison gives the data of (1.12) between the selected state observations. -/
structure ReadingComparison (source target : Reading.{u, v, w, x}) where
  /-- A theory interpretation of the language used by the source. -/
  interpretation : Interpretation source.presentation.theory target.presentation.theory
  /-- The target observation's structure satisfies its required Laws. -/
  targetModel : target.presentation.theory.Holds target.structureData
  /-- The source state map ends in the structure pulled back from the target. -/
  state : StructureMap source.structureData
    (interpretation.pullbackStructure target.structureData targetModel)
  /-- The coordinates of the two observation products correspond along the sort map. -/
  contexts : source.observation.product.Correspondence target.observation.product interpretation.onSort
  /-- Fixed declarations and cover, or the selected restriction and cover maps. -/
  declarationChange : source.ContextCompatibility target interpretation
  /-- Retained observation positions are carried by the same restriction as the other selected data. -/
  observationSupport : declarationChange.retainsObservations contexts := by
    first | trivial | exact ⟨False.elim, False.elim⟩
  /-- Coefficient transport when both readings use coefficients, with an optional cross-evaluation
  map when just one uses them. -/
  coefficientChange : source.CoefficientCompatibility target interpretation.onSort state.onSort
  /-- When coefficient inputs and ordinary inputs share positions, both squares use the same states. -/
  coefficientInputs : coefficientChange.respectsOrdinary contexts := by trivial
  /-- A coefficient square over a changed context uses only the retained state sorts. -/
  coefficientSupport : declarationChange.retainsCoefficients coefficientChange := by trivial
  /-- The function between the two sets of observed values. -/
  value : source.observation.Output → target.observation.Output
  /-- When a coefficient output exists at only one endpoint, the specified projection commutes. -/
  coefficientProjection : coefficientChange.projectionCommutes contexts value := by trivial
  /-- Equation (1.12), imposed at every source state tuple. -/
  commutes (e : source.observation.product.Values source.structureData.carrier) :
    target.observation.read (contexts.mapValues state.onSort e) = value (source.observation.read e)

/-- A reading comparison between models, with the additional source condition of Construction 2.5. -/
structure ModelReadingComparison (source target : Reading.{u, v, w, x}) extends
    ReadingComparison source target where
  /-- The source structure is a model of its chosen theory. -/
  sourceModel : source.presentation.theory.Holds source.structureData

/-- A comparison of observations given as primitive declarations. -/
structure DeclaredReadingComparison (source target : Reading.{u, v, w, x}) extends
    ReadingComparison source target where
  /-- The observation used at the source. -/
  sourceObservation : source.DeclaredObservation
  /-- The observation used at the target. -/
  targetObservation : target.DeclaredObservation
  /-- A changed declaration context retains the source observation itself. -/
  retainsObservation : match toReadingComparison.declarationChange with
    | .fixed _ _ => True
    | .changed change =>
      Declaration.ofOperation sourceObservation.symbol.operation ∈ change.retained.declarations

/-- The target observation square is checked where the observation declaration and
all of its input sorts are covered by a single piece. -/
theorem DeclaredReadingComparison.covered_commutes {source target : Reading.{u, v, w, x}}
    (comparison : DeclaredReadingComparison source target) :
    ∃ i, Declaration.ofOperation comparison.targetObservation.symbol.operation ∈ (target.cover.piece i).declarations ∧
      Declaration.sorts (comparison.targetObservation.symbol.operation.arity.output ::
        comparison.targetObservation.symbol.operation.arity.inputs) ⊆ (target.cover.piece i).declarations ∧
      ∀ e, target.observation.read (comparison.contexts.mapValues comparison.state.onSort e) =
        comparison.value (source.observation.read e) := by
  obtain ⟨i, kept, inputs⟩ := comparison.targetObservation.covered
  exact ⟨i, kept, inputs, comparison.commutes⟩

/-- Equation (1.12) as an equality of composites on the entire selected product. -/
theorem ReadingComparison.commutes_eq {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) :
    target.observation.read ∘ comparison.contexts.mapValues comparison.state.onSort =
      comparison.value ∘ source.observation.read :=
  funext comparison.commutes

/-- The codomain of the comparison's state map satisfies the source theory. -/
theorem ReadingComparison.pullback_isModel {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) :
    source.presentation.theory.Holds
      (comparison.interpretation.pullbackStructure target.structureData comparison.targetModel) :=
  comparison.interpretation.pullback_isModel target.structureData comparison.targetModel

/-- The contextual data carried by this particular comparison. -/
abbrev ReadingComparison.ContextChange {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) :=
  {transition : ReadingContextChange source target comparison.interpretation //
    comparison.declarationChange = .changed transition}

/-- A retained target observation input is carried into an assigned target cover piece. -/
theorem ReadingComparison.target_input_is_covered {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) (change : comparison.ContextChange)
    (declared : target.observationPlacement.isRetained) (j : target.observation.product.Index) :
    ∃ i k, k ∈ change.val.pieces i ∧
      Declaration.sort (target.observation.product.sort j) ∈ (target.cover.piece k).declarations := by
  have supports := comparison.observationSupport
  rw [change.property] at supports
  obtain ⟨i, k, chosen, covered⟩ := change.val.sort_is_covered _ (supports.2 declared j)
  exact ⟨i, k, chosen, comparison.contexts.sort_eq j ▸ covered⟩

/-- The target path in the assigned cover pieces computes the translated formula's truth value. -/
theorem ReadingComparison.restricted_evaluation_commutes {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) {Γ : List source.presentation.signature.SortType}
    (change : comparison.ContextChange) (i : source.cover.Index)
    (p : Formula source.presentation.signature Γ)
    (retained : Declaration.formulaSupport p ⊆ (change.val.sourcePiece i).declarations)
    (e : Assignment source.structureData.carrier Γ) :
    (RestrictedEvaluation.restrict (change.val.targetPiece i) target.structureData).holds
      (comparison.interpretation.translation.formula p)
      (change.val.local_formula_support i p retained)
      (comparison.interpretation.mapStates comparison.state e) ↔
    p.Holds (comparison.interpretation.pullbackStructure target.structureData comparison.targetModel)
      (e.map comparison.state.onSort) :=
  (RestrictedEvaluation.restrict_holds_iff _ _ _ _ _).trans
    (comparison.interpretation.pullback_formula_iff _ _ _ _).symm

/-- Transport a formula evaluated in a retained source piece to its assigned target pieces. -/
theorem ReadingComparison.transport_restricted_formula {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) {Γ : List source.presentation.signature.SortType}
    (change : comparison.ContextChange) (i : source.cover.Index)
    (p : Formula source.presentation.signature Γ)
    (retained : Declaration.formulaSupport p ⊆ (change.val.sourcePiece i).declarations)
    (e : Assignment source.structureData.carrier Γ)
    (held : (RestrictedEvaluation.restrict (change.val.sourcePiece i)
      source.structureData).holds p retained e) :
    (RestrictedEvaluation.restrict (change.val.targetPiece i) target.structureData).holds
      (comparison.interpretation.translation.formula p)
      (change.val.local_formula_support i p retained)
      (comparison.interpretation.mapStates comparison.state e) :=
  (comparison.restricted_evaluation_commutes change i p retained e).2
    (comparison.state.holds_map p e ((RestrictedEvaluation.restrict_holds_iff _ _ _ _ _).1 held))

end SHIGURE
