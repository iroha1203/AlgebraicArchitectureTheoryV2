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
An external observation reads states in the chosen signature. Coordinates
that were external to the selection remain available independently of the
cover. A context restriction must still account for the evaluation at any
coordinates it forgets. A primitive observation keeps its actual operation
and full arity in a single cover piece.

A comparison with unchanged coefficient settings can use
the same evaluation rule in both realizations. A comparison of changed
coefficient settings or a changed context compares the chosen evaluations
along the structural state map. The common input has all used source
positions and may include further positions that feed the target evaluation.
Shared target positions must get their value from the same source state.
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

/-- A state observation is given by a function on an indexed product or by a named operation. -/
inductive StateObservation {sig : Signature.{u}} (A : Structure sig) where
  | ofFunction (product : ObservationProduct sig.SortType) (output : Type u)
      (read : product.Values A.carrier → output)
  | ofTotalSymbol (symbol : TotalSymbol sig)

namespace StateObservation

variable {sig : Signature.{u}} {A : Structure sig}

/-- The input product selected by the observer. -/
def product : StateObservation A → ObservationProduct sig.SortType
  | .ofFunction product _ _ => product
  | .ofTotalSymbol symbol => { ObservationProduct.ofList symbol.operation.arity.inputs with nameScope := none }

/-- The selected set of observation values. -/
def Output : StateObservation A → Type u
  | .ofFunction _ output _ => output
  | .ofTotalSymbol symbol => A.carrier symbol.operation.arity.output

/-- Evaluate the actual function or the actual declared operation. -/
def read (observation : StateObservation A) : observation.product.Values A.carrier → observation.Output :=
  match observation with
  | .ofFunction _ _ read => read
  | .ofTotalSymbol symbol =>
    fun e => (⟨symbol, rfl⟩ : TypedTotal sig symbol.operation.arity).value A
      (ObservationProduct.toAssignment e)

/-- The declaration used to evaluate a primitive observation. -/
def symbol : StateObservation A → Option (TotalSymbol sig)
  | .ofFunction .. => none
  | .ofTotalSymbol operation => some operation

/-- The observation as an explicit function on its input product. -/
private def asFunction (observation : StateObservation A) : StateObservation A :=
  .ofFunction observation.product observation.Output observation.read

/-- Selecting a primitive symbol determines the observation. -/
theorem eq_of_symbol {observation : StateObservation A} {f : TotalSymbol sig}
    (h : observation.symbol = some f) : observation = .ofTotalSymbol f := by
  cases observation with
  | ofFunction => cases h
  | ofTotalSymbol g => cases Option.some.inj h; rfl

/-- Observe a single state's value with a function on its sort. -/
def ofSort (s : sig.SortType) (O : Type u) (f : A.carrier s → O) : StateObservation A :=
  .ofFunction (.ofSort s) O (fun e => f (e PUnit.unit))

/-- Observe an ordinary finite context, optionally naming its input positions for sharing. -/
def ofContext (Γ : List sig.SortType) (O : Type u) (f : Assignment A.carrier Γ → O)
    (nameScope : Option String := none) : StateObservation A :=
  .ofFunction { ObservationProduct.ofList Γ with nameScope := nameScope } O
    (fun e => f (ObservationProduct.toAssignment e))

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
  /-- A primitive observation is selected together with its declaration. -/
  observationDeclared (f : TotalSymbol presentation.signature) (named : observation.symbol = some f) :
      Declaration.ofOperation f.operation ∈ context.declarations := by
    intro f named
    first | exact Set.mem_univ _ | cases named
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

namespace Reading.DeclaredObservation

variable {reading : Reading.{u, v, w, x}}

/-- Interpret the observation inside the piece containing its declaration. -/
def restrictedObservation (declaration : reading.DeclaredObservation)
    (piece : DeclarationContext reading.presentation)
    (kept : Declaration.ofOperation declaration.symbol.operation ∈ piece.declarations) :
    StateObservation reading.structureData := by
  obtain ⟨symbol, _, _⟩ := declaration
  let retained := RestrictedStructure.restrict piece reading.structureData
  cases symbol with
  | ordinary f =>
    exact StateObservation.ofContext _ _ (retained.total f kept)
  | quantity q =>
    exact StateObservation.ofContext _ _ (retained.quantity q kept)

/-- Restriction keeps the interpretation of the retained observation. -/
theorem restrictedObservation_eq (declaration : reading.DeclaredObservation)
    (piece : DeclarationContext reading.presentation)
    (kept : Declaration.ofOperation declaration.symbol.operation ∈ piece.declarations) :
    declaration.restrictedObservation piece kept = reading.observation.asFunction := by
  obtain ⟨symbol, available, literal⟩ := declaration
  cases symbol <;> exact congrArg StateObservation.asFunction literal.symm

/-- Equal observations evaluate equally after transporting their input and output types. -/
private theorem cast_read {sig : Signature.{u}} {A : Structure sig} {p q : StateObservation A}
    (same : p = q) (e : q.product.Values A.carrier) :
    cast (congrArg (fun obs : StateObservation A => obs.product.Values A.carrier → obs.Output) same)
      p.read e = q.read e := by
  cases same
  rfl

/-- Evaluate the local observation on the reading’s original typed input. -/
def readWithin (declaration : reading.DeclaredObservation)
    (piece : DeclarationContext reading.presentation)
    (kept : Declaration.ofOperation declaration.symbol.operation ∈ piece.declarations)
    (e : reading.observation.product.Values reading.structureData.carrier) : reading.observation.Output :=
  cast (congrArg (fun obs : StateObservation reading.structureData =>
    obs.product.Values reading.structureData.carrier → obs.Output) (declaration.restrictedObservation_eq piece kept))
    (declaration.restrictedObservation piece kept).read e

/-- The local value equals the value in the selected reading. -/
theorem readWithin_eq (declaration : reading.DeclaredObservation)
    (piece : DeclarationContext reading.presentation)
    (kept : Declaration.ofOperation declaration.symbol.operation ∈ piece.declarations)
    (e : reading.observation.product.Values reading.structureData.carrier) :
    declaration.readWithin piece kept e = reading.observation.read e :=
  cast_read (declaration.restrictedObservation_eq piece kept) e

end Reading.DeclaredObservation

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
  observationDeclared _ _ := Set.mem_univ _
  origin := some ⟨reading.presentation, reading.context, selection⟩

/-- Use original position names, including when the products keep different subsets of them. -/
def Reading.namedInput (reading : Reading.{u, v, w, x})
    (Γ : CoefficientProduct reading.presentation.signature.SortType)
    (j : Γ.product.Index) (i : reading.observation.product.Index) : Prop :=
  Γ.product.sort j = reading.observation.product.sort i ∧ Γ.product.nameScope ≠ none ∧
    Γ.product.nameScope = reading.observation.product.nameScope ∧
    HEq (Γ.slot j) (reading.observation.product.names.2 i)

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
    · exact reading.observation.product.names.2.injective
        (eq_of_heq (namedI.2.2.2.symm.trans namedK.2.2.2))
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
    · exact Γ.slot_injective (eq_of_heq (namedJ.2.2.2.trans namedK.2.2.2.symm))
    · exact (freshK ⟨j, namedJ⟩).elim
  · rcases hk.2 with namedK | ⟨explicitK, _, _⟩
    · exact (freshJ ⟨k, namedK⟩).elim
    · exact reading.sharedInputs.unique Γ explicitJ explicitK

/-- A state input for both evaluations assigns the same value at each shared position. -/
structure Reading.JointInput (reading : Reading.{u, v, w, x})
    {Γ : CoefficientProduct reading.presentation.signature.SortType} (selection : InputSelection Γ) where
  /-- Values at the ordinary observation's positions. -/
  ordinary : reading.observation.product.Values reading.structureData.carrier
  /-- Values at the original positions actually used by the coefficient evaluation. -/
  coefficient : selection.used.Values reading.structureData.carrier
  /-- Shared positions use one state value. -/
  agrees (j : selection.used.Index) (i : reading.observation.product.Index)
    (shared : reading.SharesInput Γ j.val i) :
    cast (congrArg reading.structureData.carrier shared.1) (coefficient j) = ordinary i

/-- Evaluate both observations on the same joint input. -/
def Reading.JointInput.evaluate {reading : Reading.{u, v, w, x}}
    {Γ : CoefficientProduct reading.presentation.signature.SortType}
    (coefficient : CoefficientReading.{u, v} reading.context reading.structureData Γ)
    (input : reading.JointInput coefficient.selection) :
    reading.observation.Output × coefficient.ring.Carrier :=
  (reading.observation.read input.ordinary, coefficient.evaluateSelected input.coefficient)

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
  /-- The local replacements are equivalent to the chosen interpretation. -/
  equivalent : supporting.Equivalent u
  /-- A source cover piece can be compared over several target pieces. -/
  pieces : source.cover.Index → Set target.cover.Index
  /-- Target pieces independently chosen for declarations added by the comparison. -/
  addedTargetPieces : Set target.cover.Index := ∅
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
  exact ⟨i, j, chosen, congrFun transition.equivalent.choose s ▸ covered⟩

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

/-- The target pieces selected either by an assignment or for added declarations. -/
def selectedTargetPieces (transition : ReadingContextChange source target u) :
    Set target.cover.Index :=
  {j | (∃ i, j ∈ transition.pieces i) ∨ j ∈ transition.addedTargetPieces}

/-- The target declarations available in the selected pieces. -/
def targetRetained (transition : ReadingContextChange source target u) :
    DeclarationContext target.presentation where
  declarations := {d | ∃ j ∈ transition.selectedTargetPieces, d ∈ (target.cover.piece j).declarations}
  closed := by
    rintro d ⟨j, chosen, mentioned⟩ e he
    exact ⟨j, chosen, (target.cover.piece j).closed mentioned he⟩

/-- All assigned pieces belong to the target reading's context. -/
theorem targetRetained_inside (transition : ReadingContextChange source target u) :
    transition.targetRetained.declarations ⊆ target.context.declarations := by
  rintro d ⟨j, _, kept⟩
  exact target.cover.subset j kept

/-- Translate formula support using the specified target context for each declaration. -/
private theorem formula_support_in (transition : ReadingContextChange source target u)
    {Γ : List source.presentation.signature.SortType} (p : Formula source.presentation.signature Γ)
    (V : Set (Declaration target.presentation)) (keep : ∀ d ∈ Declaration.formulaSupport p,
      Declaration.translatedSupport transition.supporting d ⊆ V) :
    Declaration.formulaSupport (transition.supporting.translation.formula p) ⊆ V := by
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
    Declaration.formulaSupport (transition.supporting.translation.formula p) ⊆ target.context.declarations :=
  transition.formula_support_in p _ (fun _ h => transition.support_subset (retained h))

/-- All translated support fits inside the assigned target pieces of the comparison. -/
theorem local_formula_support (transition : ReadingContextChange source target u)
    (i : source.cover.Index) {Γ : List source.presentation.signature.SortType}
    (p : Formula source.presentation.signature Γ)
    (retained : Declaration.formulaSupport p ⊆ (transition.sourcePiece i).declarations) :
    Declaration.formulaSupport (transition.supporting.translation.formula p) ⊆ (transition.targetPiece i).declarations :=
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

/-- Keeping the selection fixed is independent of the theory interpretation used in (1.12). -/
inductive Reading.ContextCompatibility (source target : Reading.{u, v, w, x})
    (u : Interpretation source.presentation.theory target.presentation.theory) where
  | fixed (same : source.SameContext target) : ContextCompatibility source target u
  | changed : ReadingContextChange source target u → ContextCompatibility source target u

/-- A changed context compares a source piece to an assigned or independently added target piece. -/
def Reading.ContextCompatibility.comparesPieces {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    (contextChange : source.ContextCompatibility target u)
    (i : source.cover.Index) (j : target.cover.Index) : Prop :=
  match contextChange with
  | .fixed _ => True
  | .changed change => j ∈ change.pieces i ∨ j ∈ change.addedTargetPieces

/-- The source piece after applying the context choice used by the comparison. -/
def Reading.ContextCompatibility.comparedSourcePiece {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    (contextChange : source.ContextCompatibility target u)
    (i : source.cover.Index) : DeclarationContext source.presentation :=
  match contextChange with
  | .fixed _ => source.cover.piece i
  | .changed change => change.sourcePiece i

namespace ReadingContextChange

variable {source target : Reading.{u, v, w, x}}
  {u : Interpretation source.presentation.theory target.presentation.theory}

/-- A source coordinate is either kept in the restriction or was already external to it. -/
def observationInputs (change : ReadingContextChange source target u) :
    Set source.observation.product.Index :=
  {i | let d := Declaration.sort (source.observation.product.sort i)
       d ∈ change.retained.declarations ∨
         (source.observation.symbol = none ∧ d ∉ source.context.declarations)}

/-- The local target uses exactly the observation coordinates with an available source. A
declared observation additionally requires its entire arity and its assigned declaration. -/
def targetObservationInputs (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort) :
    Set target.observation.product.Index :=
  {j | positions.position j ∈ change.observationInputs}

/-- Only a declared observation needs a piece containing its primitive. A target
declaration may use a state that was already available outside the source selection. -/
inductive ObservationLocations (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort) :
    Option (TotalSymbol source.presentation.signature) →
      Option (TotalSymbol target.presentation.signature) → Prop
  | external : ObservationLocations change positions none none
  | sourceOnly (f : TotalSymbol source.presentation.signature) (i : source.cover.Index) :
    Declaration.ofOperation f.operation ∈ (change.sourcePiece i).declarations →
    ObservationLocations change positions (some f) none
  | targetOnly (f : TotalSymbol target.presentation.signature) (j : target.cover.Index) :
    j ∈ change.selectedTargetPieces →
    Declaration.ofOperation f.operation ∈ (target.cover.piece j).declarations →
    (∀ k, k ∈ change.targetObservationInputs positions) →
    ObservationLocations change positions none (some f)
  | paired (f : TotalSymbol source.presentation.signature)
      (g : TotalSymbol target.presentation.signature) (i : source.cover.Index) (j : target.cover.Index) :
    (j ∈ change.pieces i ∨ j ∈ change.addedTargetPieces) →
    Declaration.ofOperation f.operation ∈ (change.sourcePiece i).declarations →
    Declaration.ofOperation g.operation ∈ (target.cover.piece j).declarations →
    (∀ k, k ∈ change.targetObservationInputs positions) →
    ObservationLocations change positions (some f) (some g)

/-- A declared target observation has an actual selected piece and an available input tuple. -/
theorem ObservationLocations.targetPiece {change : ReadingContextChange source target u}
    {positions : source.observation.product.Correspondence target.observation.product u.onSort}
    {left : Option (TotalSymbol source.presentation.signature)} {f : TotalSymbol target.presentation.signature}
    (support : change.ObservationLocations positions left (some f)) :
    ∃ j ∈ change.selectedTargetPieces,
      Declaration.ofOperation f.operation ∈ (target.cover.piece j).declarations ∧
      ∀ k, k ∈ change.targetObservationInputs positions := by
  cases support with
  | targetOnly _ j selected kept available => exact ⟨j, selected, kept, available⟩
  | paired _ _ i j pair keptSource kept available =>
    exact ⟨j, pair.imp (fun assigned => ⟨i, assigned⟩) id, kept, available⟩

/-- The structural map on the retained coordinates of the ordinary observation. -/
def mapObservationInputs (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort)
    (state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s))
    (e : (source.observation.product.restrict change.observationInputs).Values source.structureData.carrier) :
    (target.observation.product.restrict (change.targetObservationInputs positions)).Values
      target.structureData.carrier :=
  fun j => positions.sort_eq j.val ▸ state _ (e ⟨positions.position j.val, j.property⟩)

/-- The retained source tuple of a contextual comparison. -/
abbrev SourceObservationValues (change : ReadingContextChange source target u) :=
  (source.observation.product.restrict change.observationInputs).Values source.structureData.carrier

/-- The retained target tuple of a contextual comparison. -/
abbrev TargetObservationValues (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort) :=
  (target.observation.product.restrict (change.targetObservationInputs positions)).Values
    target.structureData.carrier

/-- The actual observations factor through the retained tuples. Their local square is
required on every retained tuple, including tuples with no ambient extension. -/
def ObservationSquare (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort)
    (state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s))
    (value : source.observation.Output → target.observation.Output)
    (also : (change.SourceObservationValues → source.observation.Output) →
      (change.TargetObservationValues positions → target.observation.Output) → Prop := fun _ _ => True) : Prop :=
  ∃ (readSource : change.SourceObservationValues → source.observation.Output)
    (readTarget : change.TargetObservationValues positions → target.observation.Output),
    (∀ e, readSource (fun i => e i.val) = source.observation.read e) ∧
    (∀ e, readTarget (fun j => e j.val) = target.observation.read e) ∧
    (∀ e, readTarget (change.mapObservationInputs positions state e) = value (readSource e)) ∧
    also readSource readTarget

/-- When all positions are available, the local square is the original square. -/
theorem observationSquare_of_available (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort)
    (state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s))
    (value : source.observation.Output → target.observation.Output)
    (left : ∀ i, i ∈ change.observationInputs)
    (right : ∀ j, j ∈ change.targetObservationInputs positions)
    (square : ∀ e, target.observation.read (positions.mapValues state e) = value (source.observation.read e)) :
    change.ObservationSquare positions state value :=
  ⟨fun e => source.observation.read (fun i => e ⟨i, left i⟩),
    fun e => target.observation.read (fun j => e ⟨j, right j⟩),
    fun _ => rfl, fun _ => rfl, (fun e => square (fun i => e ⟨i, left i⟩)), True.intro⟩

/-- Retaining every source sort makes all the observation inputs available for its square. -/
theorem observationSquare_of_all (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort)
    (state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s))
    (value : source.observation.Output → target.observation.Output)
    (kept : ∀ i, Declaration.sort (source.observation.product.sort i) ∈ change.retained.declarations)
    (square : ∀ e, target.observation.read (positions.mapValues state e) = value (source.observation.read e)) :
    change.ObservationSquare positions state value := by
  exact change.observationSquare_of_available positions state value
    (fun i => Or.inl (kept i)) (fun j => Or.inl (kept (positions.position j))) square

end ReadingContextChange

/-- A retained target observation can read an available state from either the source
restriction or its independently available observations. Its target declaration is selected. -/
def Reading.ContextCompatibility.retainsObservations {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    (positions : source.observation.product.Correspondence target.observation.product u.onSort) :
    source.ContextCompatibility target u → Prop
  | .fixed _ => True
  | .changed change =>
    (source.observationPlacement.isRetained →
      ∀ i, Declaration.sort (source.observation.product.sort i) ∈ change.retained.declarations) ∧
    (target.observationPlacement.isRetained →
      ∀ j, j ∈ change.targetObservationInputs positions ∧
        Declaration.sort (target.observation.product.sort j) ∈ change.targetRetained.declarations)

/-- A change of context keeps the primitive observations selected by either endpoint. -/
def Reading.ContextCompatibility.retainsChosenSymbols {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    (positions : source.observation.product.Correspondence target.observation.product u.onSort) :
    source.ContextCompatibility target u → Prop
  | .fixed .. => True
  | .changed change => change.ObservationLocations positions source.observation.symbol target.observation.symbol

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

/-- Every ordinary source position actually used by the target lies in the usable subset. -/
def UsesOnly (inputs : ReadingInputMap source target onSort) (available : Set source.Index) : Prop :=
  ∀ j i, (inputs.coordinate j).val = .inl i → i ∈ available

/-- The sort equality for a specific location of a target coordinate. -/
private theorem coordinateSort (inputs : ReadingInputMap source target onSort) {j : target.Index}
    {k : source.Index ⊕ inputs.extra.Index} (position : (inputs.coordinate j).val = k) :
    onSort (Sum.elim source.sort inputs.extra.sort k) = target.sort j :=
  Eq.mp (congrArg (fun k => onSort (Sum.elim source.sort inputs.extra.sort k) = target.sort j)
    position) (inputs.coordinate j).property

/-- Transport using only the usable source positions and the additional coefficient inputs. -/
def mapRestrictedValues (inputs : ReadingInputMap source target onSort)
    {X : S → Type u} {Y : T → Type u} (h : ∀ s, X s → Y (onSort s))
    {available : Set source.Index} (kept : inputs.UsesOnly available)
    (e : (source.restrict available).Values X × inputs.extra.Values X) : target.Values Y :=
  fun j =>
    match position : (inputs.coordinate j).val with
    | .inl i => inputs.coordinateSort position ▸ h _ (e.1 ⟨i, kept j i position⟩)
    | .inr i => inputs.coordinateSort position ▸ h _ (e.2 i)

/-- On restrictions of ambient tuples, the restricted state map is the original state map. -/
theorem mapRestrictedValues_restrict (inputs : ReadingInputMap source target onSort)
    {X : S → Type u} {Y : T → Type u} (h : ∀ s, X s → Y (onSort s))
    {available : Set source.Index} (kept : inputs.UsesOnly available) (e : inputs.Values X) :
    inputs.mapRestrictedValues h kept (fun i => e.1 i.val, e.2) = inputs.mapValues h e := by
  funext j
  cases position : inputs.coordinate j with
  | mk k equal =>
    have loc : (inputs.coordinate j).val = k := congrArg Subtype.val position
    cases k with
    | inl i =>
      simp only [mapRestrictedValues, mapValues, position]
      split
      · rename_i l hl
        cases Sum.inl.inj (hl.symm.trans loc)
        rfl
      · rename_i r hr
        cases hr.symm.trans loc
    | inr i =>
      simp only [mapRestrictedValues, mapValues, position]
      split
      · rename_i l hl
        cases hl.symm.trans loc
      · rename_i r hr
        cases Sum.inr.inj (hr.symm.trans loc)
        rfl

/-- Additional source positions used by the selected target coordinates. -/
def usedExtra (inputs : ReadingInputMap source target onSort) (kept : Set target.Index) :
    Set inputs.extra.Index :=
  {i | ∃ j ∈ kept, (inputs.coordinate j).val = .inr i}

/-- Map into the retained target tuple, using only the additional states that tuple reads. -/
def mapToRestrictedTarget (inputs : ReadingInputMap source target onSort)
    {X : S → Type u} {Y : T → Type u} (h : ∀ s, X s → Y (onSort s))
    {kept : Set target.Index}
    (e : source.Values X × (inputs.extra.restrict (inputs.usedExtra kept)).Values X) :
    (target.restrict kept).Values Y :=
  fun j =>
    match position : (inputs.coordinate j.val).val with
    | .inl i => inputs.coordinateSort position ▸ h _ (e.1 i)
    | .inr i => inputs.coordinateSort position ▸ h _ (e.2 ⟨i, j.val, j.property, position⟩)

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

/-- A name shared with a target position in the original source layout. -/
def CommonName (raw : ObservationProduct S) (i : raw.Index) (j : target.Index) : Prop :=
  raw.nameScope ≠ none ∧ raw.nameScope = target.nameScope ∧
    HEq (raw.names.2 i) (target.names.2 j) ∧ onSort (raw.sort i) = target.sort j

/-- A target position that is shared with the ordinary observation gets the source position
specified by its ordinary correspondence. An extra input that supplies an original named
position inherits its ordinary sharing before the source coefficient inputs were selected. -/
def RespectsOrdinary (inputs : ReadingInputMap source target onSort)
    {ordinarySource : ObservationProduct S} {ordinaryTarget : ObservationProduct T}
    (positions : ordinarySource.Correspondence ordinaryTarget onSort)
    (raw : ObservationProduct S) (origin : source.Index → raw.Index)
    (sourceShares : raw.Index → ordinarySource.Index → Prop)
    (targetShares : target.Index → ordinaryTarget.Index → Prop) : Prop :=
  ∃ extraShares : inputs.extra.Index → Option ordinarySource.Index,
    (∀ k i, extraShares k = some i → inputs.extra.sort k = ordinarySource.sort i) ∧
    (∀ j k i, extraShares j = some i → extraShares k = some i → j = k) ∧
    (∀ j i k, CommonName (target := target) (onSort := onSort) raw i j →
      (inputs.coordinate j).val = .inr k →
      ∀ l, extraShares k = some l ↔ sourceShares i l) ∧
    ∀ j i, targetShares j i →
      match (inputs.coordinate j).val with
      | .inl k => sourceShares (origin k) (positions.position i)
      | .inr k => extraShares k = some (positions.position i) ∧
          ¬ ∃ q : source.Index, sourceShares (origin q) (positions.position i)

/-- The identity map preserves the sharing relation of a common input layout. -/
theorem identity_respectsOrdinary (product : ObservationProduct S)
    {ordinary raw : ObservationProduct S} (origin : product.Index → raw.Index)
    (shares : raw.Index → ordinary.Index → Prop) :
    (identity product).RespectsOrdinary (.identity ordinary) raw origin shares
      (fun j i => shares (origin j) i) :=
  ⟨(fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i),
    (fun _ _ k => nomatch k), fun _ _ h => h⟩

/-- A shared name uses its original source coordinate, including when that coordinate
needs to be supplied in addition to the selected source inputs. -/
def PreservesNames (inputs : ReadingInputMap source target onSort)
    (raw : ObservationProduct S) (origin : source.Index → raw.Index) : Prop :=
  ∀ j (i : raw.Index),
    CommonName (target := target) (onSort := onSort) raw i j →
    match (inputs.coordinate j).val with
    | .inl input => origin input = i
    | .inr input => i ∉ Set.range origin ∧
        inputs.extra.sort input = raw.sort i ∧
        inputs.extra.nameScope = raw.nameScope ∧
        HEq (inputs.extra.names.2 input) (raw.names.2 i)

/-- Compare with the original names of a coefficient product before input selection. -/
abbrev UsesCoefficientNames {raw : CoefficientProduct S}
    (selection : InputSelection raw) (inputs : ReadingInputMap selection.used target onSort) : Prop :=
  inputs.PreservesNames raw.product Subtype.val

/-- The identity correspondence supplies every shared name from its original position. -/
theorem identity_usesCoefficientNames {raw : CoefficientProduct S} (selection : InputSelection raw) :
    UsesCoefficientNames selection (identity selection.used) := by
  intro j i same
  exact raw.slot_injective (eq_of_heq same.2.2.1.symm)

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

namespace CoefficientComparison

variable {P Q : PrimitivePresentation.{u}} {U : DeclarationContext P} {V : DeclarationContext Q}
  {A : Structure P.signature} {B : Structure Q.signature}
  {Γ : CoefficientProduct P.signature.SortType} {Δ : CoefficientProduct Q.signature.SortType}
  {c : CoefficientReading.{u, v} U A Γ} {d : CoefficientReading.{u, v} V B Δ}
  {onSort : P.signature.SortType → Q.signature.SortType}
  {state : ∀ s, A.carrier s → B.carrier (onSort s)}

/-- The correspondence of state inputs for the chosen coefficient transport. -/
def UsesInputs {ordinarySource : ObservationProduct P.signature.SortType}
    {ordinaryTarget : ObservationProduct Q.signature.SortType}
    (positions : ordinarySource.Correspondence ordinaryTarget onSort)
    (sourceShares : Γ.product.Index → ordinarySource.Index → Prop)
    (targetShares : Δ.product.Index → ordinaryTarget.Index → Prop) :
    CoefficientComparison c d onSort state → Prop
  | .fixed _ =>
    ∀ (k : d.selection.used.Index) (l : ordinaryTarget.Index),
      targetShares k.val l → ∃ j : c.selection.used.Index,
        HEq (Γ.slot j.val) (Δ.slot k.val) ∧ sourceShares j.val (positions.position l)
  | .changed inputs _ =>
    inputs.UsesCoefficientNames c.selection ∧
      inputs.RespectsOrdinary positions Γ.product Subtype.val sourceShares (fun j i => targetShares j.val i)

/-- A contextual change supplies an evaluation map, retains its inputs, and localizes each evaluation. -/
def SupportsEvaluation (retains extraAvailable : P.signature.SortType → Prop) (sourceLocal targetLocal : Prop) :
    CoefficientComparison c d onSort state → Prop
  | .fixed _ => False
  | .changed inputs _ =>
    ((∀ i, retains (c.selection.used.sort i)) ∧ (∀ i, extraAvailable (inputs.extra.sort i))) ∧
      sourceLocal ∧ targetLocal

/-- With a supplied evaluation map, support is exactly locality and retention of the actual inputs. -/
theorem supportsEvaluation_changed (retains extraAvailable : P.signature.SortType → Prop)
    (sourceLocal targetLocal : Prop)
    (inputs : ReadingInputMap c.selection.used d.selection.used onSort)
    (square : CoefficientReading.EvaluationComparison c d
      (fun e : inputs.Values A.carrier => c.evaluateSelected e.1)
      (fun e => d.evaluateSelected (inputs.mapValues state e))) :
    (CoefficientComparison.changed inputs square).SupportsEvaluation retains extraAvailable sourceLocal targetLocal ↔
      ((∀ i, retains (c.selection.used.sort i)) ∧ (∀ i, extraAvailable (inputs.extra.sort i))) ∧
        sourceLocal ∧ targetLocal :=
  Iff.rfl

/-- Evaluate the actual retained inputs at both ends of a coefficient square. -/
theorem restricted_evaluation_commutes
    (inputs : ReadingInputMap c.selection.used d.selection.used onSort)
    (square : CoefficientReading.EvaluationComparison c d
      (fun e : inputs.Values A.carrier => c.evaluateSelected e.1)
      (fun e => d.evaluateSelected (inputs.mapValues state e)))
    {W : DeclarationContext P} {Z : DeclarationContext Q}
    {left : W.declarations ⊆ U.declarations} {right : Z.declarations ⊆ V.declarations}
    (sourceLocal : c.RespectsRestriction W left) (targetLocal : d.RespectsRestriction Z right)
    (e : inputs.Values A.carrier) :
    d.evaluateRetained targetLocal d.algebra (d.restrictSelected targetLocal (inputs.mapValues state e)) =
      square.coefficients (c.evaluateRetained sourceLocal c.algebra (c.restrictSelected sourceLocal e.1)) := by
  simpa only [CoefficientReading.evaluateRetained_mk] using square.evaluate_commutes e

/-- Extract the actual comparison and its commuting evaluations on the chosen retained contexts. -/
theorem evaluation_from_support (comparison : CoefficientComparison c d onSort state)
    (retains extraAvailable : P.signature.SortType → Prop)
    {W : DeclarationContext P} {Z : DeclarationContext Q}
    {left : W.declarations ⊆ U.declarations} {right : Z.declarations ⊆ V.declarations}
    (support : comparison.SupportsEvaluation retains extraAvailable
      (c.RestrictionAllowed W left) (d.RestrictionAllowed Z right)) :
    ∃ (inputs : ReadingInputMap c.selection.used d.selection.used onSort)
      (square : CoefficientReading.EvaluationComparison c d
        (fun e : inputs.Values A.carrier => c.evaluateSelected e.1)
        (fun e => d.evaluateSelected (inputs.mapValues state e))),
      comparison = .changed inputs square ∧
      ∃ (sourceLocal : c.RestrictionAllowed W left) (targetLocal : d.RestrictionAllowed Z right),
        ∀ e, d.evaluateWithin targetLocal (inputs.mapValues state e) =
          square.coefficients (c.evaluateWithin sourceLocal e.1) := by
  cases comparison with
  | fixed _ => exact support.elim
  | changed inputs square =>
    have localSupport := (supportsEvaluation_changed retains extraAvailable _ _ inputs square).1 support
    refine ⟨inputs, square, rfl, localSupport.2.1, localSupport.2.2, ?_⟩
    intro e
    simpa only [CoefficientReading.evaluateWithin_eq] using square.evaluate_commutes e

end CoefficientComparison

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

/-- The coefficient comparison preserves coefficient names and the ordinary correspondence
at shared state positions. -/
def Reading.CoefficientCompatibility.respectsOrdinary {source target : Reading.{u, v, w, x}}
    {onSort : source.presentation.signature.SortType → target.presentation.signature.SortType}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (onSort s)}
    (positions : source.observation.product.Correspondence target.observation.product onSort) :
    source.CoefficientCompatibility target onSort state → Prop := by
  unfold Reading.CoefficientCompatibility
  split
  · exact fun _ => True
  · rename_i c d _ _
    exact CoefficientComparison.UsesInputs positions (source.SharesInput c.1) (target.SharesInput d.1)
  · rename_i d _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare data => data.1.PreservesNames source.observation.product id ∧
          data.1.RespectsOrdinary positions source.observation.product id (· = ·)
            (fun j i => target.SharesInput d.1 j.val i)
  · rename_i c _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare data => data.1.UsesCoefficientNames c.2.selection ∧
          data.1.RespectsOrdinary positions c.1.product Subtype.val (source.SharesInput c.1) (· = ·)

/-- The coefficient evaluations use only the retained states and respect the restriction at
each evaluated endpoint. A projection keeps only the ordinary component. -/
def Reading.CoefficientCompatibility.retainsEvaluation {source target : Reading.{u, v, w, x}}
    {onSort : source.presentation.signature.SortType → target.presentation.signature.SortType}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (onSort s)}
    (retains extraAvailable : source.presentation.signature.SortType → Prop) (sourceLocal targetLocal : Prop) :
    source.CoefficientCompatibility target onSort state → Prop := by
  unfold Reading.CoefficientCompatibility
  split
  · exact fun _ => True
  · exact CoefficientComparison.SupportsEvaluation retains extraAvailable sourceLocal targetLocal
  · exact fun comparison => match comparison with
      | .project => True
      | .compare data => (∀ i, extraAvailable (data.1.extra.sort i)) ∧ targetLocal
  · rename_i c _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare _ => (∀ i, retains (c.2.selection.used.sort i)) ∧ sourceLocal

/-- Keep the entire realization at an unchanged context. When declarations are forgotten,
the evaluation of its selected tuple descends to the retained primitive data. -/
def Reading.respectsCoefficientRestriction (reading : Reading.{u, v, w, x})
    (kept : DeclarationContext reading.presentation)
    (inside : kept.declarations ⊆ reading.context.declarations) : Prop :=
  match reading.coefficients with
  | none => True
  | some c => c.2.RestrictionAllowed kept inside

/-- Relate the coefficient square to the sorts selected by a declaration change. -/
def Reading.ContextCompatibility.retainsCoefficients {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s)}
    (contextChange : source.ContextCompatibility target u)
    (coefficientChange : source.CoefficientCompatibility target u.onSort state) : Prop :=
  match contextChange with
  | .fixed _ => True
  | .changed change =>
    coefficientChange.retainsEvaluation (fun s => Declaration.sort s ∈ change.retained.declarations)
      (fun s => Declaration.sort s ∈ change.retained.declarations ∨
        Declaration.sort s ∉ source.context.declarations)
      (source.respectsCoefficientRestriction change.retained change.inside)
      (target.respectsCoefficientRestriction change.targetRetained change.targetRetained_inside)

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
          (t : target.JointInput d.2.selection),
          t.ordinary = positions.mapValues state e →
          (Reading.JointInput.evaluate d.2 t).1 =
            value (source.observation.read e)
  · rename_i c _ _
    exact fun comparison => match comparison with
      | .compare _ => True
      | .project => ∀ e : source.JointInput c.2.selection,
          target.observation.read (positions.mapValues state e.ordinary) =
            (value ∘ Prod.fst) (Reading.JointInput.evaluate c.2 e)

/-- A one-sided coefficient comparison uses the same local ordinary evaluator as the
ordinary comparison, including on retained inputs that have no ambient extension. -/
def Reading.CoefficientCompatibility.respectsRestrictedOrdinary {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    {state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s)}
    (change : ReadingContextChange source target u)
    (positions : source.observation.product.Correspondence target.observation.product u.onSort)
    (readSource : change.SourceObservationValues → source.observation.Output)
    (readTarget : change.TargetObservationValues positions → target.observation.Output) :
    source.CoefficientCompatibility target u.onSort state → Prop := by
  unfold Reading.CoefficientCompatibility
  split
  · exact fun _ => True
  · exact fun _ => True
  · rename_i d _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare data =>
        ∃ kept : data.1.UsesOnly change.observationInputs,
          ∀ e : change.SourceObservationValues × data.1.extra.Values source.structureData.carrier,
            d.2.evaluateSelected (data.1.mapRestrictedValues state kept e) = data.2.val (readSource e.1)
  · rename_i c _ _
    exact fun comparison => match comparison with
      | .project => True
      | .compare data =>
        let kept := change.targetObservationInputs positions
        (∀ i : data.1.usedExtra kept,
          Declaration.sort (data.1.extra.sort i.val) ∈ change.retained.declarations ∨
            Declaration.sort (data.1.extra.sort i.val) ∉ source.context.declarations) ∧
        ∀ (e : c.2.selection.used.Values source.structureData.carrier)
          (extra : (data.1.extra.restrict (data.1.usedExtra kept)).Values source.structureData.carrier),
          readTarget (data.1.mapToRestrictedTarget state (e, extra)) = data.2.val (c.2.evaluateSelected e)

/-- Context changes localize the actual ordinary and one-sided coefficient comparisons together. -/
def Reading.ContextCompatibility.restrictedSquare {source target : Reading.{u, v, w, x}}
    {u : Interpretation source.presentation.theory target.presentation.theory}
    (positions : source.observation.product.Correspondence target.observation.product u.onSort)
    (state : ∀ s, source.structureData.carrier s → target.structureData.carrier (u.onSort s))
    (value : source.observation.Output → target.observation.Output)
    (coefficients : source.CoefficientCompatibility target u.onSort state) :
    source.ContextCompatibility target u → Prop
  | .fixed .. => True
  | .changed change => change.ObservationSquare positions state value
      (fun left right => coefficients.respectsRestrictedOrdinary change positions left right)

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
  /-- Named observations are evaluated in the paired pieces of this comparison. -/
  declaredObservations : declarationChange.retainsChosenSymbols contexts := by
    first | trivial | exact .external
  /-- Coefficient transport when both readings use coefficients, with an optional cross-evaluation
  map when just one uses them. -/
  coefficientChange : source.CoefficientCompatibility target interpretation.onSort state.onSort
  /-- Both squares use the same shared states, and coefficient names keep their original positions. -/
  coefficientInputs : coefficientChange.respectsOrdinary contexts := by trivial
  /-- A coefficient square over a changed context only uses the kept realizations and states. -/
  coefficientSupport : declarationChange.retainsCoefficients coefficientChange := by trivial
  /-- The function between the two sets of observed values. -/
  value : source.observation.Output → target.observation.Output
  /-- When a coefficient output exists at only one endpoint, the specified projection commutes. -/
  coefficientProjection : coefficientChange.projectionCommutes contexts value := by trivial
  /-- Equation (1.12), imposed at every source state tuple. -/
  commutes (e : source.observation.product.Values source.structureData.carrier) :
    target.observation.read (contexts.mapValues state.onSort e) = value (source.observation.read e)
  /-- The observations on the retained data commute over a changed context. -/
  restrictedObservations : declarationChange.restrictedSquare contexts state.onSort value coefficientChange := by trivial

/-- A reading comparison between models, with the additional source condition of Construction 2.5. -/
structure ModelReadingComparison (source target : Reading.{u, v, w, x}) extends
    ReadingComparison source target where
  /-- The source structure is a model of its chosen theory. -/
  sourceModel : source.presentation.theory.Holds source.structureData

/-- Read both declared observations in the actual paired pieces of the comparison. -/
theorem ReadingComparison.covered_commutes {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target)
    (left : source.DeclaredObservation) (right : target.DeclaredObservation) :
    ∃ (i : source.cover.Index) (j : target.cover.Index)
      (sourceKept : Declaration.ofOperation left.symbol.operation ∈
        (comparison.declarationChange.comparedSourcePiece i).declarations)
      (targetKept : Declaration.ofOperation right.symbol.operation ∈ (target.cover.piece j).declarations),
      comparison.declarationChange.comparesPieces i j ∧
      ∀ e, right.readWithin (target.cover.piece j) targetKept
          (comparison.contexts.mapValues comparison.state.onSort e) =
        comparison.value (left.readWithin (comparison.declarationChange.comparedSourcePiece i) sourceKept e) := by
  have locates : ∃ i j,
      Declaration.ofOperation left.symbol.operation ∈
        (comparison.declarationChange.comparedSourcePiece i).declarations ∧
      comparison.declarationChange.comparesPieces i j ∧
      Declaration.ofOperation right.symbol.operation ∈ (target.cover.piece j).declarations := by
    cases selected : comparison.declarationChange with
    | fixed _ =>
      obtain ⟨i, sourceKept⟩ := source.cover.covers left.kept
      obtain ⟨j, targetKept⟩ := target.cover.covers right.kept
      exact ⟨i, j, sourceKept, True.intro, targetKept⟩
    | changed change =>
      have support := comparison.declaredObservations
      have leftNamed : source.observation.symbol = some left.symbol := by rw [left.reads]; rfl
      have rightNamed : target.observation.symbol = some right.symbol := by rw [right.reads]; rfl
      rw [selected] at support
      change change.ObservationLocations comparison.contexts source.observation.symbol target.observation.symbol at support
      rw [leftNamed, rightNamed] at support
      cases support with
      | paired _ _ i j related leftKept rightKept _ => exact ⟨i, j, leftKept, related, rightKept⟩
  obtain ⟨i, j, sourceKept, assigned, targetKept⟩ := locates
  refine ⟨i, j, sourceKept, targetKept, assigned, ?_⟩
  intro e
  simpa only [Reading.DeclaredObservation.readWithin_eq] using comparison.commutes e

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

/-- Extract the coefficient evaluation conditions for this comparison's actual retained contexts. -/
theorem ReadingComparison.coefficient_support_on_retained {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) (change : comparison.ContextChange) :
    comparison.coefficientChange.retainsEvaluation
      (fun s => Declaration.sort s ∈ change.val.retained.declarations)
      (fun s => Declaration.sort s ∈ change.val.retained.declarations ∨
        Declaration.sort s ∉ source.context.declarations)
      (source.respectsCoefficientRestriction change.val.retained change.val.inside)
      (target.respectsCoefficientRestriction change.val.targetRetained change.val.targetRetained_inside) := by
  have support := comparison.coefficientSupport
  rw [change.property] at support
  exact support

/-- A declared target observation belongs to a piece actually selected by the comparison. -/
theorem ReadingComparison.target_observation_is_selected {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) (change : comparison.ContextChange)
    {f : TotalSymbol target.presentation.signature} (named : target.observation.symbol = some f) :
    ∃ j ∈ change.val.selectedTargetPieces,
      Declaration.ofOperation f.operation ∈ (target.cover.piece j).declarations ∧
      ∀ k, k ∈ change.val.targetObservationInputs comparison.contexts := by
  have holds := comparison.declaredObservations
  rw [change.property] at holds
  change change.val.ObservationLocations comparison.contexts source.observation.symbol target.observation.symbol at holds
  rw [named] at holds
  exact holds.targetPiece

/-- The actual retention and observation maps commute on the whole retained state product. -/
theorem ReadingComparison.observation_square_on_retained {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) (change : comparison.ContextChange) :
    change.val.ObservationSquare comparison.contexts comparison.state.onSort comparison.value := by
  have square := comparison.restrictedObservations
  rw [change.property] at square
  obtain ⟨left, right, leftFactor, rightFactor, agrees, _⟩ := square
  exact ⟨left, right, leftFactor, rightFactor, agrees, True.intro⟩

/-- All selected local value comparisons use the same restricted ordinary functions. -/
theorem ReadingComparison.observation_and_coefficients_on_retained {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) (change : comparison.ContextChange) :
    change.val.ObservationSquare comparison.contexts comparison.state.onSort comparison.value
      (fun left right => comparison.coefficientChange.respectsRestrictedOrdinary change.val
        comparison.contexts left right) := by
  have square := comparison.restrictedObservations
  rw [change.property] at square
  exact square

/-- Evaluate a declared target observation in its selected piece on every retained source tuple,
including when the source observation was external and had no source cover piece. -/
theorem ReadingComparison.target_local_observation_commutes {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) (change : comparison.ContextChange)
    (declared : target.DeclaredObservation) :
    ∃ (j : target.cover.Index) (_ : j ∈ change.val.selectedTargetPieces)
      (kept : Declaration.ofOperation declared.symbol.operation ∈ (target.cover.piece j).declarations)
      (available : ∀ k, k ∈ change.val.targetObservationInputs comparison.contexts)
      (readSource : change.val.SourceObservationValues → source.observation.Output),
      (∀ e, readSource (fun i => e i.val) = source.observation.read e) ∧
      ∀ e, declared.readWithin (target.cover.piece j) kept
          (fun k => change.val.mapObservationInputs comparison.contexts comparison.state.onSort e
            ⟨k, available k⟩) = comparison.value (readSource e) := by
  have named : target.observation.symbol = some declared.symbol := by rw [declared.reads]; rfl
  obtain ⟨j, selected, kept, available⟩ := comparison.target_observation_is_selected change named
  obtain ⟨readSource, readTarget, sourceFactor, targetFactor, square, _⟩ :=
    comparison.observation_square_on_retained change
  refine ⟨j, selected, kept, available, readSource, sourceFactor, ?_⟩
  intro e
  rw [Reading.DeclaredObservation.readWithin_eq, ← targetFactor]
  exact square e

/-- A retained target observation input is available in a selected target cover piece. -/
theorem ReadingComparison.target_input_is_covered {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) (change : comparison.ContextChange)
    (declared : target.observationPlacement.isRetained) (j : target.observation.product.Index) :
    ∃ k ∈ change.val.selectedTargetPieces,
      Declaration.sort (target.observation.product.sort j) ∈ (target.cover.piece k).declarations := by
  have supports := comparison.observationSupport
  rw [change.property] at supports
  exact (supports.2 declared j).2

/-- The target path in the assigned cover pieces computes the translated formula's truth value. -/
theorem ReadingComparison.restricted_evaluation_commutes {source target : Reading.{u, v, w, x}}
    (comparison : ReadingComparison source target) {Γ : List source.presentation.signature.SortType}
    (change : comparison.ContextChange) (i : source.cover.Index)
    (p : Formula source.presentation.signature Γ)
    (retained : Declaration.formulaSupport p ⊆ (change.val.sourcePiece i).declarations)
    (e : Assignment source.structureData.carrier Γ) :
    (RestrictedEvaluation.restrict (change.val.targetPiece i) target.structureData).holds
      (change.val.supporting.translation.formula p)
      (change.val.local_formula_support i p retained)
      (change.val.equivalent.retype (comparison.interpretation.mapStates comparison.state e)) ↔
    p.Holds (comparison.interpretation.pullbackStructure target.structureData comparison.targetModel)
      (e.map comparison.state.onSort) :=
  (RestrictedEvaluation.restrict_holds_iff _ _ _ _ _).trans
    ((change.val.equivalent.formula_holds_iff _ comparison.targetModel p _).trans
      (comparison.interpretation.pullback_formula_iff _ _ _ _).symm)

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
      (change.val.supporting.translation.formula p)
      (change.val.local_formula_support i p retained)
      (change.val.equivalent.retype (comparison.interpretation.mapStates comparison.state e)) :=
  (comparison.restricted_evaluation_commutes change i p retained e).2
    (comparison.state.holds_map p e ((RestrictedEvaluation.restrict_holds_iff _ _ _ _ _).1 held))

end SHIGURE
