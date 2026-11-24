import Formal.SHIGURE.Part1.FixedModels
import Mathlib.CategoryTheory.Types.Basic

/-! # State and observation operations for protocols

A quiver provides the names of the state and observation actions. For an
execution category these are all arrows. For a path presentation they are
only the generating edges. Both signatures also have one readout per vertex.

## Implementation notes

The same typed unary vocabulary serves the category and its presentation.
Identity, composition and path equalities will be imposed as Laws. Building
those equalities into the action data would hide which Laws are used to
recover the execution functor.
-/

universe u

namespace SHIGURE

open CategoryTheory

namespace Protocol

variable (V : Type u) [Quiver.{u} V]

/-- The named edges of the quiver, with both endpoint sorts. -/
abbrev Edge := Σ i j : V, i ⟶ j

/-- The three families of unary symbols in a protocol. -/
inductive Symbol where
  /-- Execute an edge on states. -/
  | step {i j : V} (f : i ⟶ j)
  /-- Execute the same edge on observations. -/
  | observation {i j : V} (f : i ⟶ j)
  /-- Read an observation at the given vertex. -/
  | readout (i : V)

variable {V}

/-- The sole input sort of a named operation. -/
def Symbol.input : Symbol V → V ⊕ V
  | .step (i := i) _ => .inl i
  | .observation (i := i) _ => .inr i
  | .readout i => .inl i

/-- The result sort of a named operation. -/
def Symbol.output : Symbol V → V ⊕ V
  | .step (j := j) _ => .inl j
  | .observation (j := j) _ => .inr j
  | .readout i => .inr i

/-- The signature of state actions, observation actions and readout maps. -/
def signature (V : Type u) [Quiver.{u} V] : Signature.{u} where
  SortType := V ⊕ V
  Total := Symbol V
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity f := ⟨[f.input], f.output⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- All operations in the vocabulary are total. -/
instance noPartial : IsEmpty (signature V).Partial := ⟨fun p => nomatch p⟩

/-- Apply a named unary operation before imposing any of the Laws. -/
def applySymbol (symbol : Symbol V) {Γ : List (V ⊕ V)} (arg : Term (signature V) Γ symbol.input) :
    Term (signature V) Γ symbol.output :=
  Term.app (sig := signature V) (.total symbol) (Term.argsCons arg Term.argsNil)

/-- Evaluate the interpretation of a symbol on its sole input. -/
def symbolValue (A : Structure (signature V)) (symbol : Symbol V) (x : A.carrier symbol.input) :
    A.carrier symbol.output := A.total symbol (Assignment.cons x Assignment.empty)

/-- At a unary input the symbol term evaluates by applying the named operation. -/
theorem totalValue_applySymbol (symbol : Symbol V) (A : Structure (signature V))
    {Γ : List (V ⊕ V)} (e : Assignment A.carrier Γ) (arg : Term (signature V) Γ symbol.input) :
    (applySymbol symbol arg).totalValue A e = symbolValue A symbol (arg.totalValue A e) := by
  apply congrArg (A.total symbol)
  apply Assignment.ext
  intro s i
  cases i with
  | here => rfl
  | there i => exact nomatch i

/-- The subsignature of observables contains the observation sorts and their edge operations. -/
def observationSignature (V : Type u) [Quiver.{u} V] : Signature.{u} where
  SortType := V
  Total := Edge V
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity f := ⟨[f.1], f.2.1⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- The observable reduct forgets all state sorts, state operations and readouts. -/
def observationInclusion (V : Type u) [Quiver.{u} V] : Subsignature (observationSignature V) (signature V) := by
  let names : SignatureNames (observationSignature V) (signature V) :=
    { onSort := Sum.inr
      onTotal := fun f => .observation f.2.2
      onRel := fun r => nomatch r
      onPartial := fun p => nomatch p
      onQuantity := fun q => nomatch q
      totalArity := fun _ => rfl
      relInputs := fun r => nomatch r
      partialArity := fun p => nomatch p
      quantityArity := fun q => nomatch q }
  refine ⟨names, Sum.inr_injective, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, j, f⟩ ⟨i', j', g⟩ same
    change Symbol.observation f = Symbol.observation g at same
    cases same
    rfl
  · intro r _ _
    exact nomatch r
  · intro p _ _
    exact nomatch p
  · intro q _ _
    exact nomatch q

/-- The observable structure is interpreted by the supplied observation action. -/
def observationData (O : V ⥤q Type u) : Structure (observationSignature V) where
  carrier := O.obj
  total f xs := O.map f.2.2 (xs .here)
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The state actions and readouts before imposing the protocol Laws. -/
structure Action (O : V ⥤q Type u) where
  /-- A state type at every vertex. -/
  state : V → Type u
  /-- The state functions of the named edges. -/
  step {i j : V} (f : i ⟶ j) : state i → state j
  /-- The map from states to observations at every vertex. -/
  observe (i : V) : state i → O.obj i

namespace Action

variable {O : V ⥤q Type u}

/-- The two kinds of sorts are interpreted by states and observations. -/
def carrier (X : Action O) : V ⊕ V → Type u
  | .inl i => X.state i
  | .inr i => O.obj i

/-- The three kinds of symbols have the interpretations of their names. -/
def value (X : Action O) : (f : Symbol V) → X.carrier f.input → X.carrier f.output
  | .step f => X.step f
  | .observation f => O.map f
  | .readout i => X.observe i

/-- Interpret the protocol vocabulary using the given states, operations and observations. -/
def toStructure (X : Action O) : Structure (signature V) where
  carrier := X.carrier
  total f xs := X.value f (xs .here)
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The interpreted unary symbol acts by its assigned function. -/
theorem symbolValue_toStructure (X : Action O) (f : Symbol V) (x : X.carrier f.input) :
    symbolValue X.toStructure f x = X.value f x := rfl

/-- A map of actions preserves all the named state functions and their readouts. -/
@[ext]
structure Hom (X Y : Action O) where
  /-- A map between the two state types at each vertex. -/
  state (i : V) : X.state i → Y.state i
  /-- The state maps commute with every edge action. -/
  step_comm {i j : V} (f : i ⟶ j) (x : X.state i) : state j (X.step f x) = Y.step f (state i x)
  /-- The maps preserve each readout. -/
  observe_comm (i : V) (x : X.state i) : Y.observe i (state i x) = X.observe i x

/-- Actions with a shared observation action compose componentwise. -/
instance category : Category.{u} (Action O) where
  Hom := Hom
  id _ := ⟨fun _ => id, fun _ _ => rfl, fun _ _ => rfl⟩
  comp f g :=
    { state := fun i => g.state i ∘ f.state i
      step_comm := fun e x => by simp only [Function.comp_apply, f.step_comm, g.step_comm]
      observe_comm := fun i x => by simp only [Function.comp_apply, g.observe_comm, f.observe_comm] }
  id_comp := by intros; apply Hom.ext; rfl
  comp_id := by intros; apply Hom.ext; rfl
  assoc := by intros; apply Hom.ext; rfl

variable {X Y Z : Action O}

/-- Two action arrows agree when their state maps agree at all inputs. -/
theorem hom_ext {f g : X ⟶ Y} (same : ∀ i x, f.state i x = g.state i x) : f = g :=
  Hom.ext (funext fun i => funext (same i))

/-- The identity acts as the identity on states. -/
@[simp] theorem id_state (X : Action O) (i : V) (x : X.state i) : (𝟙 X : Hom X X).state i x = x := rfl

/-- The state components of a composite compose in execution order. -/
theorem comp_state (f : X ⟶ Y) (g : Y ⟶ Z) (i : V) (x : X.state i) :
    (show Hom X Z from f ≫ g).state i x = g.state i (f.state i x) := rfl

/-- Transport of action arrows along an object equality acts by the carrier equality. -/
theorem eqToHom_state (same : X = Y) (i : V) (x : X.state i) :
    (show Hom X Y from eqToHom same).state i x = cast (congrArg (fun A => A.state i) same) x := by
  subst Y
  rw [eqToHom_refl, id_state]
  rfl

end Action
end Protocol
end SHIGURE
