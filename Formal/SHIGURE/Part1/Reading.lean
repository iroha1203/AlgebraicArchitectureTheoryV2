import Formal.SHIGURE.Part1.Interpretation
import Formal.SHIGURE.Part1.StructureMaps
import Formal.SHIGURE.Part1.DeclarationContexts

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

end Assignment

namespace Interpretation

variable {S T : Theory.{u}}

/-- Select the actual value of a term at an input known to satisfy its definedness formula. -/
private noncomputable def definedValue {sig : Signature.{u}} {Γ : List sig.SortType}
    {s : sig.SortType} (B : Structure sig) (t : Term sig Γ s) (xs : Assignment B.carrier Γ)
    (defined : t.defined.Holds B xs) : B.carrier s :=
  (t.eval B xs).get ((t.mem_domain_iff B xs).1 ((t.holds_defined B xs).1 defined))

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

/-- A coefficient choice records the actual coefficient ring and the chosen realization data. -/
structure CoefficientReading where
  /-- The carrier of the coefficient ring. -/
  Carrier : Type u
  /-- The commutative ring structure used for coefficients. -/
  ring : CommRing Carrier
  /-- The type of coefficient realization specifications. -/
  Realization : (R : Type u) → CommRing R → Type u
  /-- The coefficient realization specification used by this reading. -/
  realization : Realization Carrier ring

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
  coefficients : Option (CoefficientReading.{u})

/-- Retype a state tuple along equality of the contexts used by two observations. -/
def Assignment.castContext {sig : Signature.{u}} {A : Structure sig}
    {Γ Δ : List sig.SortType} (same : Γ = Δ) (e : Assignment A.carrier Γ) :
    Assignment A.carrier Δ :=
  same ▸ e

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

end SHIGURE
