import Formal.SHIGURE.Part1.Interpretation
import Formal.SHIGURE.Part1.StructureMaps
import Formal.SHIGURE.Part1.RestrictedEvaluation
import Formal.SHIGURE.Part1.CoefficientReading

/-! # Observations and readings

Definition 1.11 separates observations of states from observations of a
family of realizations. The state component of (1.12) uses the structure
on the source signature obtained from the theory interpretation.

## Implementation notes

A state observation chooses a finite typed context. A singleton context
gives a single-sort observation and a longer context gives a product.
An unrestricted input type would lose the state coordinates needed to
compare two observations across a theory interpretation.

The pulled-back structure uses the operation terms of the chosen
interpretation. Soundness of its totality and partial-domain derivations
provides the domain proofs needed to take individual term values.

The context comparison uses the actual support of a translation. An
operation can translate to a term involving several declarations, so the
support is set-valued and a source cover piece may use several target
pieces. Restriction to the retained source declarations controls which
facts can be transported.

A coefficient comparison between two chosen rings includes a ring
homomorphism and a map between the chosen realization data. The evaluator
uses that data's structure and the reading's state tuple, so the
coefficient square uses the same state map as (1.12). Introducing or
forgetting coefficients compares this evaluation with the ordinary
observation at the endpoint that has no coefficient ring.
-/

universe u

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
The model and functor laws for this construction are proved in Theorem 2.4. -/
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

/-- Pullback and retyping send a tuple of states through the given structural map. -/
def mapStates (u : Interpretation S T) {A : Structure S.signature}
    {B : Structure T.signature} {model : T.Holds B}
    (h : StructureMap A (u.pullbackStructure B model)) {Γ : List S.signature.SortType}
    (e : Assignment A.carrier Γ) : Assignment B.carrier (Γ.map u.onSort) :=
  (e.map h.onSort).mapSorts u.onSort

end Interpretation

/-- A state observation can read one sort or a finite product of sorts. -/
structure StateObservation {sig : Signature.{u}} (A : Structure sig) where
  /-- The sorts of the states supplied to the observation. -/
  context : List sig.SortType
  /-- The values read by the observation. -/
  Output : Type u
  /-- The observation on an assignment in the selected context. -/
  read : Assignment A.carrier context → Output

namespace StateObservation

variable {sig : Signature.{u}} {A : Structure sig}

/-- Observe a single state's value with a function on its sort. -/
def ofSort (s : sig.SortType) (O : Type u) (f : A.carrier s → O) : StateObservation A :=
  ⟨[s], O, fun e => f e.head⟩

/-- Reading a singleton assignment applies the original single-sort observation. -/
@[simp] theorem ofSort_cons (s : sig.SortType) (O : Type u) (f : A.carrier s → O)
    (x : A.carrier s) :
    (ofSort s O f).read (Assignment.cons x Assignment.empty) = f x :=
  rfl

end StateObservation

/-- A family observation reads the family index, independently of any individual state. -/
structure FamilyObservation (Realization : Type u) where
  /-- The values used for distinguishing members of the family. -/
  Output : Type u
  /-- The function on the family of realizations. -/
  read : Realization → Output

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
  Family : Type u
  /-- The structure associated to each family member. -/
  realize : Family → Structure presentation.signature
  /-- An observation on the family, when one is specified. -/
  familyObservation : Option (FamilyObservation Family)
  /-- The type of value-structure choices on the observation values. -/
  ValueStructure : Type u → Type u
  /-- The chosen value-structure data. -/
  valueStructure : ValueStructure observation.Output
  /-- The coefficient data, when the reading uses coefficients. -/
  coefficients : Option (CoefficientReading context structureData observation.context)

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

/-- The support of a translated formula depends on the translation data, not its proofs. -/
theorem atomic_support_of_same_translation
    {f g : P.signature.SortType → Q.signature.SortType}
    {left : Translation P.signature Q.signature f}
    {right : Translation P.signature Q.signature g} (sortsEqual : f = g)
    (translationEqual : HEq left right) {Γ : List P.signature.SortType} (a : Atomic P.signature Γ) :
    formulaSupport (P := Q) (left.atomic a) = formulaSupport (P := Q) (right.atomic a) := by
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
structure ReadingContextChange (source target : Reading.{u})
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

variable {source target : Reading.{u}}
  {u : Interpretation source.presentation.theory target.presentation.theory}

/-- The retained source declaration translates entirely inside the target context. -/
theorem support_subset (transition : ReadingContextChange source target u)
    {a : Declaration source.presentation} (ha : a ∈ transition.retained.declarations) :
    Declaration.translatedSupport transition.supporting a ⊆ target.context.declarations := by
  intro d hd
  obtain ⟨i, hi⟩ := source.cover.covers (transition.inside ha)
  obtain ⟨j, _, hj⟩ := transition.localSupport i ha hi hd
  exact target.cover.subset j hj

/-- A supported source atom translates into the actual selected target context. -/
theorem target_support (transition : ReadingContextChange source target u)
    {Γ : List source.presentation.signature.SortType} (a : Atomic source.presentation.signature Γ)
    (retained : Declaration.atomicSupport a ⊆ transition.retained.declarations) :
    Declaration.formulaSupport (u.translation.atomic a) ⊆ target.context.declarations := by
  rw [← Declaration.atomic_support_of_same_translation transition.sameSorts transition.sameTranslation a]
  intro d hd
  rcases hd with hsort | hformula
  · obtain ⟨t, ht, rfl⟩ := hsort
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact transition.support_subset (retained (Or.inl ⟨s, hs, rfl⟩)) (Set.mem_singleton _)
  · exact Declaration.translated_atomic_support transition.supporting a _
      (fun _ hd => transition.support_subset (retained (Or.inr hd))) hformula

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

/-- A comparison with fixed declarations and cover only needs the state observation square.
A change to the selected declarations or cover supplies the restriction and support maps. -/
inductive Reading.ContextCompatibility (source target : Reading.{u})
    (u : Interpretation source.presentation.theory target.presentation.theory) where
  | fixed : source.presentation = target.presentation →
      HEq source.context target.context → HEq source.cover target.cover →
      ContextCompatibility source target u
  | changed : ReadingContextChange source target u → ContextCompatibility source target u

/-- Retype a state tuple along equality of the contexts used by two observations. -/
def Assignment.castContext {sig : Signature.{u}} {A : Structure sig}
    {Γ Δ : List sig.SortType} (same : Γ = Δ) (e : Assignment A.carrier Γ) :
    Assignment A.carrier Δ :=
  same ▸ e

/-- The coefficient part of a comparison uses the same states as (1.12).
When one endpoint has no coefficients, the corresponding observation values are used. -/
def Reading.CoefficientCompatibility (source target : Reading.{u})
    (states : Assignment source.structureData.carrier source.observation.context →
      Assignment target.structureData.carrier target.observation.context) : Type u :=
  match source.coefficients, target.coefficients with
  | none, none => PUnit
  | some c, some d => CoefficientReading.Change c d states
  | none, some d =>
    {v : source.observation.Output → d.ring.Carrier //
      ∀ e, d.evaluate (states e) = v (source.observation.read e)}
  | some c, none =>
    {v : c.ring.Carrier → target.observation.Output //
      ∀ e, target.observation.read (states e) = v (c.evaluate e)}

/-- A comparison gives the data of (1.12) between the selected state observations. -/
structure ReadingComparison (source target : Reading.{u}) where
  /-- A theory interpretation of the language used by the source. -/
  interpretation : Interpretation source.presentation.theory target.presentation.theory
  /-- The target observation's structure satisfies its required Laws. -/
  targetModel : target.presentation.theory.Holds target.structureData
  /-- The source state map ends in the structure pulled back from the target. -/
  state : StructureMap source.structureData
    (interpretation.pullbackStructure target.structureData targetModel)
  /-- The two state observations take the corresponding typed products. -/
  contexts : source.observation.context.map interpretation.onSort = target.observation.context
  /-- Fixed declarations and cover, or the selected restriction and cover maps. -/
  declarationChange : source.ContextCompatibility target interpretation
  /-- Any change of the coefficients and their evaluation. -/
  coefficientChange : source.CoefficientCompatibility target
    (fun e => Assignment.castContext contexts (interpretation.mapStates state e))
  /-- The function between the two sets of observed values. -/
  value : source.observation.Output → target.observation.Output
  /-- Equation (1.12), imposed at every source state tuple. -/
  commutes (e : Assignment source.structureData.carrier source.observation.context) :
    target.observation.read (Assignment.castContext contexts (interpretation.mapStates state e)) =
      value (source.observation.read e)

/-- Equation (1.12) as an equality of composites on the entire selected product. -/
theorem ReadingComparison.commutes_eq {source target : Reading.{u}}
    (comparison : ReadingComparison source target) :
    target.observation.read ∘
      (fun e => Assignment.castContext comparison.contexts
        (comparison.interpretation.mapStates comparison.state e)) =
      comparison.value ∘ source.observation.read :=
  funext comparison.commutes

/-- The target path through restricted evaluation computes the translated formula of a
retained fact. This equality compares it to the global structural transport path. -/
theorem ReadingComparison.restricted_evaluation_commutes {source target : Reading.{u}}
    (comparison : ReadingComparison source target) {Γ : List source.presentation.signature.SortType}
    (transition : ReadingContextChange source target comparison.interpretation)
    (a : Atomic source.presentation.signature Γ)
    (retained : Declaration.atomicSupport a ⊆ transition.retained.declarations)
    (e : Assignment source.structureData.carrier Γ) :
    (RestrictedEvaluation.restrict target.context target.structureData).holds
      (comparison.interpretation.translation.atomic a)
      (transition.target_support a retained)
      (comparison.interpretation.mapStates comparison.state e) ↔
    a.Holds (comparison.interpretation.pullbackStructure target.structureData comparison.targetModel)
      (e.map comparison.state.onSort) :=
  (RestrictedEvaluation.restrict_holds_iff _ _ _ _ _).trans
    (comparison.interpretation.pullback_atomic_iff _ _ _ _).symm

/-- Start with a fact evaluated in the retained source context and evaluate its transport
in the selected target context. -/
theorem ReadingComparison.transport_restricted_atom {source target : Reading.{u}}
    (comparison : ReadingComparison source target) {Γ : List source.presentation.signature.SortType}
    (transition : ReadingContextChange source target comparison.interpretation)
    (a : Atomic source.presentation.signature Γ)
    (retained : Declaration.atomicSupport a ⊆ transition.retained.declarations)
    (e : Assignment source.structureData.carrier Γ)
    (held : (RestrictedEvaluation.restrict transition.retained
      source.structureData).atomic e a retained) :
    (RestrictedEvaluation.restrict target.context target.structureData).holds
      (comparison.interpretation.translation.atomic a)
      (transition.target_support a retained)
      (comparison.interpretation.mapStates comparison.state e) :=
  (comparison.restricted_evaluation_commutes transition a retained e).2
    (comparison.state.atomic_holds_map a e ((RestrictedEvaluation.restrict_atomic_iff _ _ _ _ _).1 held))

end SHIGURE
