import Formal.SHIGURE.Part1.ProtocolModels
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Protocols on an execution category

Definition 2.11 is the over category of the observation functor. Theorem 2.12
recovers that category from the state, observation and readout symbols and
the three families of Laws in (2.14).

## Implementation notes

The over category stores precisely a state functor with a natural readout.
Giving a separate category of pairs would repeat the mathlib composition.
The lawful-action category mediates the comparison with fixed-reduct models:
its objects satisfy the actual Laws and its maps preserve the named operations.
-/

universe u

namespace SHIGURE

open CategoryTheory

/-- Protocols and their arrows form the over category of the observation functor. -/
abbrev Protocol {E : Type u} [Category.{u} E] (O : E ⥤ Type u) := Over O

namespace Protocol

section Quiver

variable {V : Type u} [Quiver.{u} V]

/-- A readout commutes with a named edge on its state and observation sorts. -/
def observationLaw {i j : V} (e : i ⟶ j) : Law (signature V) :=
  let x : Term (signature V) [.inl i] (.inl i) := .var .here
  Law.equality (applySymbol (.readout j) (applySymbol (.step e) x))
    (applySymbol (.observation e) (applySymbol (.readout i) x))

/-- Satisfaction of the observation Law is the concrete commutative square. -/
theorem observationLaw_holds_iff {O : V ⥤q Type u} (X : Action O) {i j : V} (e : i ⟶ j) :
    (observationLaw e).Holds X.toStructure ↔
      ∀ x, X.observe j (X.step e x) = O.map e (X.observe i x) := by
  rw [observationLaw, Law.holds_equality_totalValue_iff]
  simp only [totalValue_applySymbol, Action.symbolValue_toStructure, Term.totalValue_var]
  exact ⟨fun h x => h (Assignment.cons x Assignment.empty), fun h xs => h (xs .here)⟩

end Quiver

variable {E : Type u} [Category.{u} E]

/-- The identity Law in (2.14). -/
def identityLaw (i : E) : Law (signature E) :=
  let x : Term (signature E) [.inl i] (.inl i) := .var .here
  Law.equality (applySymbol (.step (𝟙 i)) x) x

/-- The composition Law in (2.14). -/
def compositionLaw {i j k : E} (e : i ⟶ j) (f : j ⟶ k) : Law (signature E) :=
  let x : Term (signature E) [.inl i] (.inl i) := .var .here
  Law.equality (applySymbol (.step (e ≫ f)) x) (applySymbol (.step f) (applySymbol (.step e) x))

/-- The names of the three required Law families. -/
inductive LawName (E : Type u) [Category.{u} E]
  /-- The state action of an identity. -/
  | identity (i : E)
  /-- The state action of a composition. -/
  | composition {i j k : E} (e : i ⟶ j) (f : j ⟶ k)
  /-- Naturality of the readout along an execution arrow. -/
  | naturality {i j : E} (e : i ⟶ j)

/-- Each Law name denotes the corresponding equation in (2.14). -/
def law : LawName E → Law (signature E)
  | .identity i => identityLaw i
  | .composition e f => compositionLaw e f
  | .naturality e => observationLaw e

/-- The theory of executions whose observation structure will be fixed. -/
def theory (E : Type u) [Category.{u} E] : Theory.{u} := theoryWithLaws (law (E := E))

/-- The category of protocol models with the specified observation structure. -/
abbrev Models (O : E ⥤ Type u) := Semantic O.toPrefunctor (law (E := E))

/-- The identity Law of a concrete action is the identity function on its state. -/
theorem identityLaw_holds_iff {O : E ⥤q Type u} (X : Action O) (i : E) :
    (identityLaw i).Holds X.toStructure ↔ ∀ x, X.step (𝟙 i) x = x := by
  rw [identityLaw, Law.holds_equality_totalValue_iff]
  simp only [totalValue_applySymbol, Action.symbolValue_toStructure, Term.totalValue_var]
  exact ⟨fun h x => h (Assignment.cons x Assignment.empty), fun h xs => h (xs .here)⟩

/-- The composition Law identifies the state action of a composite with the two successive actions. -/
theorem compositionLaw_holds_iff {O : E ⥤q Type u} (X : Action O) {i j k : E}
    (e : i ⟶ j) (f : j ⟶ k) : (compositionLaw e f).Holds X.toStructure ↔
      ∀ x, X.step (e ≫ f) x = X.step f (X.step e x) := by
  rw [compositionLaw, Law.holds_equality_totalValue_iff]
  simp only [totalValue_applySymbol, Action.symbolValue_toStructure, Term.totalValue_var]
  exact ⟨fun h x => h (Assignment.cons x Assignment.empty), fun h xs => h (xs .here)⟩

variable {O : E ⥤ Type u}

/-- The named state operations and readouts of an actual protocol. -/
def action (P : Protocol O) : Action O.toPrefunctor where
  state := P.left.obj
  step e := P.left.map e
  observe := P.hom.app

/-- The protocol LawfulAction specialization keeps the three equation families. -/
abbrev ExecutionAction (O : E ⥤ Type u) := LawfulAction O.toPrefunctor (law (E := E))

/-- The state functor and natural readout supply the three families of Laws. -/
def toAction (P : Protocol O) : ExecutionAction O :=
  ⟨P.action, fun name => match name with
  | .identity i => (identityLaw_holds_iff P.action i).2 (congrFun (P.left.map_id i))
  | .composition e f => (compositionLaw_holds_iff P.action e f).2 (congrFun (P.left.map_comp e f))
  | .naturality e => (observationLaw_holds_iff P.action e).2 (congrFun (P.hom.naturality e))⟩

/-- The first two required Laws supply the functoriality of the recovered state action. -/
def stateFunctor (X : ExecutionAction O) : E ⥤ Type u where
  obj := X.obj.state
  map e := X.obj.step e
  map_id i := funext ((identityLaw_holds_iff X.obj i).1 (X.property (.identity i)))
  map_comp e f := funext ((compositionLaw_holds_iff X.obj e f).1 (X.property (.composition e f)))

/-- The third family of Laws supplies a natural readout on the recovered state functor. -/
def ofAction (X : ExecutionAction O) : Protocol O :=
  Over.mk (X := O) (Y := stateFunctor X) {
    app := X.obj.observe
    naturality := fun {_ _} e => funext ((observationLaw_holds_iff X.obj e).1 (X.property (.naturality e))) }

/-- Reading back the lawful action of a protocol gives that same protocol. -/
@[simp] theorem ofAction_toAction (P : Protocol O) : ofAction (toAction P) = P := by
  obtain ⟨F, η, rfl⟩ := Over.mk_surjective P
  cases F
  cases η
  rfl

/-- Naming the operations of a recovered protocol gives the original lawful action. -/
@[simp] theorem toAction_ofAction (X : ExecutionAction O) : toAction (ofAction X) = X := by
  apply ObjectProperty.FullSubcategory.ext
  cases X with
  | mk A h => cases A; rfl

/-- A protocol map gives the state maps and preservation of each operation and readout. -/
def toActionHom {P Q : Protocol O} (f : P ⟶ Q) : toAction P ⟶ toAction Q :=
  ObjectProperty.homMk {
    state := f.left.app
    step_comm e := congrFun (f.left.naturality e)
    observe_comm i := congrFun (NatTrans.congr_app (Over.w f) i) }

/-- Preservation of the two types of operation gives a natural map over the observation. -/
def ofActionHom {X Y : ExecutionAction O} (f : X ⟶ Y) : ofAction X ⟶ ofAction Y := by
  let map : stateFunctor X ⟶ stateFunctor Y :=
    { app i := f.hom.state i
      naturality := fun {_ _} e => funext (f.hom.step_comm e) }
  refine Over.homMk map ?_
  ext i x
  exact f.hom.observe_comm i x

/-- Encode the protocol with all arrows of the actual over category. -/
def toActions (O : E ⥤ Type u) : Protocol O ⥤ ExecutionAction O where
  obj := toAction
  map := toActionHom
  map_id _ := ObjectProperty.hom_ext _ (Action.hom_ext (fun _ _ => rfl))
  map_comp _ _ := ObjectProperty.hom_ext _ (Action.hom_ext (fun _ _ => rfl))

/-- Recover the protocol functor and every observation-preserving arrow. -/
def ofActions (O : E ⥤ Type u) : ExecutionAction O ⥤ Protocol O where
  obj := ofAction
  map := ofActionHom
  map_id _ := Over.OverMorphism.ext (by ext i x; rfl)
  map_comp _ _ := Over.OverMorphism.ext (by ext i x; rfl)

/-- The underlying state map of an object transport is a carrier transport at each vertex. -/
theorem eqToHom_app {P Q : Protocol O} (h : P = Q) (i : E) (x : P.left.obj i) :
    (show P ⟶ Q from eqToHom h).left.app i x = cast (congrArg (fun A : Protocol O => A.left.obj i) h) x := by
  subst Q
  rfl

/-- Naming then reading operations is strictly the identity on protocols. -/
theorem toActions_comp_ofActions (O : E ⥤ Type u) : toActions O ⋙ ofActions O = 𝟭 (Protocol O) := by
  have objects (P : Protocol O) : (toActions O ⋙ ofActions O).obj P = (𝟭 _).obj P := ofAction_toAction P
  refine Functor.ext objects ?_
  intro P Q f
  apply Over.OverMorphism.ext
  ext i x
  simp only [Over.comp_left, NatTrans.comp_app, types_comp_apply, eqToHom_app]
  rfl

/-- Reading then naming operations is strictly the identity on lawful actions. -/
theorem ofActions_comp_toActions (O : E ⥤ Type u) : ofActions O ⋙ toActions O = 𝟭 (ExecutionAction O) := by
  have objects (X : ExecutionAction O) : (ofActions O ⋙ toActions O).obj X = (𝟭 _).obj X := toAction_ofAction X
  refine Functor.ext objects ?_
  intro X Y f
  apply ObjectProperty.hom_ext (satisfies O.toPrefunctor law)
  let forget := (satisfies O.toPrefunctor law).ι
  change forget.map ((ofActions O ⋙ toActions O).map f) =
    forget.map (eqToHom (objects X) ≫ f ≫ eqToHom (objects Y).symm)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  apply Action.hom_ext
  intro i x
  rw [Action.comp_state, Action.comp_state, Action.eqToHom_state, Action.eqToHom_state]
  rfl

/-- The protocol category is strictly isomorphic to the category of its lawful actions. -/
def actionIso (O : E ⥤ Type u) : Cat.of (Protocol O) ≅ Cat.of (ExecutionAction O) where
  hom := (toActions O).toCatHom
  inv := (ofActions O).toCatHom
  hom_inv_id := congrArg Functor.toCatHom (toActions_comp_ofActions O)
  inv_hom_id := congrArg Functor.toCatHom (ofActions_comp_toActions O)

/-- Equation (2.15): the exact category of models with the fixed observation data. -/
def modelIso (O : E ⥤ Type u) : Cat.of (Protocol O) ≅ Cat.of (Models O) :=
  actionIso O ≪≫ LawfulAction.modelIso O.toPrefunctor law

end Protocol
end SHIGURE
