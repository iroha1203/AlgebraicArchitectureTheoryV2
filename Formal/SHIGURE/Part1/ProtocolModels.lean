import Formal.SHIGURE.Part1.ProtocolVocabulary
import Formal.SHIGURE.Part1.PullbackComparison
import Mathlib.CategoryTheory.Category.Cat

/-! # Protocol actions as fixed-reduct models

The view of an action as a model retains the whole observation structure.
The comparison uses a common signature for an execution category and a
quiver of generators, with the required Laws supplied in each case.

## Implementation notes

The action stores readouts with values in the prescribed observation types.
A fixed model can instead store propositionally equal observation types.
Reading back uses the actual reduct equality to move the readouts and the
observable operations. Requiring definitional equality of these types in the
model would discard objects of the fixed-reduct category.
-/

universe u

namespace SHIGURE.Protocol

open CategoryTheory

variable {V : Type u} [Quiver.{u} V] {O : V ⥤q Type u}

/-- A singleton assignment is determined by its sole coordinate. -/
private theorem singleton_eta {S : Type u} {X : S → Type u} {s : S} (xs : Assignment X [s]) :
    Assignment.cons (xs .here) Assignment.empty = xs := by
  apply Assignment.ext
  intro t i
  cases i with
  | here => rfl
  | there i => exact nomatch i

/-- Transporting a singleton assignment transports its sole value. -/
private theorem cast_singleton {S : Type u} {X Y : S → Type u} {s : S} (h : X = Y) (x : X s) :
    cast (congrArg (fun C => Assignment C [s]) h) (Assignment.cons x Assignment.empty) =
      Assignment.cons (cast (congrFun h s) x) Assignment.empty := by
  subst Y
  rfl

/-- Equality of carriers and the compatible total functions identify a purely total structure. -/
private theorem structure_eq_of_total {sig : Signature.{u}} [IsEmpty sig.Rel] [IsEmpty sig.Partial]
    [IsEmpty sig.Quantity] {A B : Structure sig} (carriers : A.carrier = B.carrier)
    (total : ∀ f (xs : Assignment A.carrier (sig.totalArity f).inputs),
      cast (congrFun carriers (sig.totalArity f).output) (A.total f xs) =
        B.total f (cast (congrArg (fun C => Assignment C (sig.totalArity f).inputs) carriers) xs)) : A = B := by
  cases A with
  | mk X f r d p q =>
    cases B with
    | mk Y g r' d' p' q' =>
      change X = Y at carriers
      subst Y
      have domains : d = d' := funext isEmptyElim
      refine Structure.ext rfl (heq_of_eq ?_) (heq_of_eq (funext isEmptyElim)) (heq_of_eq domains)
        (Structure.partialValue_heq domains p p' (fun name => isEmptyElim name)) (heq_of_eq (funext isEmptyElim))
      funext symbol xs
      exact total symbol xs

namespace Action

/-- The interpreted action has the prescribed observable reduct. -/
theorem restrict_toStructure (X : Action O) :
    (observationInclusion V).val.restrict X.toStructure = observationData O := by
  letI : IsEmpty (observationSignature V).Rel := ⟨fun r => nomatch r⟩
  letI : IsEmpty (observationSignature V).Partial := ⟨fun p => nomatch p⟩
  letI : IsEmpty (observationSignature V).Quantity := ⟨fun q => nomatch q⟩
  refine structure_eq_of_total (A := (observationInclusion V).val.restrict X.toStructure)
    (B := observationData O) rfl ?_
  rintro ⟨i, j, f⟩ xs
  rfl

/-- The fixed reduct identifies each original observation carrier with the supplied type. -/
theorem observation_carrier_eq (A : Structure (signature V))
    (fixed : (observationInclusion V).val.restrict A = observationData O) (i : V) :
    A.carrier (.inr i) = O.obj i :=
  congrArg (fun B : Structure (observationSignature V) => B.carrier i) fixed

/-- Reading back takes all state operations and transports each readout to its specified observation type. -/
def ofStructure (A : Structure (signature V))
    (fixed : (observationInclusion V).val.restrict A = observationData O) : Action O where
  state i := A.carrier (.inl i)
  step f x := symbolValue A (.step f) x
  observe i x := cast (observation_carrier_eq A fixed i) (symbolValue A (.readout i) x)

/-- Reading an encoded action recovers its state, step and observation functions. -/
@[simp] theorem ofStructure_toStructure (X : Action O) : ofStructure X.toStructure X.restrict_toStructure = X := by
  cases X
  rfl

/-- The carrier family of the encoded readback is equal to the original one. -/
private theorem readback_carriers (A : Structure (signature V))
    (fixed : (observationInclusion V).val.restrict A = observationData O) :
    (ofStructure A fixed).carrier = A.carrier := by
  funext s
  cases s with
  | inl i => rfl
  | inr i => exact (observation_carrier_eq A fixed i).symm

/-- Along a reduct equality the original observation operation acts by the prescribed one. -/
theorem observation_value_eq (A : Structure (signature V))
    (fixed : (observationInclusion V).val.restrict A = observationData O) {i j : V} (f : i ⟶ j)
    (x : A.carrier (.inr i)) :
    cast (observation_carrier_eq A fixed j) (symbolValue A (.observation f) x) =
      O.map f (cast (observation_carrier_eq A fixed i) x) := by
  let R := (observationInclusion V).val.restrict A
  have restriction : R.total ⟨i, j, f⟩ (Assignment.cons x Assignment.empty) =
      symbolValue A (.observation f) x := by
    change ((observationInclusion V).val.restrict A).total ⟨i, j, f⟩
      (Assignment.cons x Assignment.empty) = _
    rw [SignatureNames.restrict_total_apply]
    change A.total (.observation f)
      ((Assignment.cons (X := R.carrier) x Assignment.empty).mapSorts
        (X := A.carrier) Sum.inr) = _
    simp only [Assignment.mapSorts_cons, Assignment.eq_empty]
    rfl
  have action_eq (B : Structure (observationSignature V)) (h : R = B) :
      cast (congrArg (fun C : Structure (observationSignature V) => C.carrier j) h)
        (R.total ⟨i, j, f⟩ (Assignment.cons x Assignment.empty)) =
        B.total ⟨i, j, f⟩ (Assignment.cons
          (cast (congrArg (fun C : Structure (observationSignature V) => C.carrier i) h) x) Assignment.empty) := by
    subst B
    rfl
  simpa only [restriction] using action_eq (observationData O) fixed

/-- The re-encoded unary values agree with the originals on the transported carriers. -/
private theorem readback_value (A : Structure (signature V))
    (fixed : (observationInclusion V).val.restrict A = observationData O) (f : Symbol V)
    (x : (ofStructure A fixed).carrier f.input) :
    cast (congrFun (readback_carriers A fixed) f.output) ((ofStructure A fixed).value f x) =
      symbolValue A f (cast (congrFun (readback_carriers A fixed) f.input) x) := by
  cases f with
  | step f => rfl
  | readout i =>
    change cast (observation_carrier_eq A fixed i).symm
      (cast (observation_carrier_eq A fixed i) (symbolValue A (.readout i) x)) = _
    rw [cast_cast, cast_eq]
    rfl
  | observation f =>
    have same := observation_value_eq A fixed f
      (cast (congrFun (readback_carriers A fixed) (Symbol.observation f).input) x)
    rw [cast_cast, cast_eq] at same
    change cast (congrFun (readback_carriers A fixed) (Symbol.observation f).output) (O.map f x) = _
    rw [← same, cast_cast, cast_eq]

/-- Re-encoding a fixed-reduct structure recovers its actual carrier and operation data. -/
@[simp] theorem toStructure_ofStructure (A : Structure (signature V))
    (fixed : (observationInclusion V).val.restrict A = observationData O) : (ofStructure A fixed).toStructure = A := by
  letI : IsEmpty (signature V).Rel := ⟨fun r => nomatch r⟩
  letI : IsEmpty (signature V).Partial := ⟨fun p => nomatch p⟩
  letI : IsEmpty (signature V).Quantity := ⟨fun q => nomatch q⟩
  refine structure_eq_of_total (readback_carriers A fixed) ?_
  intro f xs
  rw [show xs = Assignment.cons (xs .here) Assignment.empty from (singleton_eta xs).symm]
  rw [cast_singleton (readback_carriers A fixed)]
  exact readback_value A fixed f _

variable {X Y : Action O}

/-- Action arrows give structural maps with identity observation components. -/
def toStructureMap (f : X ⟶ Y) : StructureMap X.toStructure Y.toStructure where
  onSort
    | .inl i => f.state i
    | .inr _ => id
  total_comm symbol xs := by
    cases symbol with
    | step e => exact f.step_comm e (xs .here)
    | observation e => rfl
    | readout i => exact (f.observe_comm i (xs .here)).symm
  relation_mem r := nomatch r
  partial_mem p := nomatch p
  partial_comm p := nomatch p
  quantity_comm q := nomatch q

/-- A structural state component is the original map of that state sort. -/
theorem toStructureMap_state (f : X ⟶ Y) (i : V) (x : X.state i) :
    (toStructureMap f).onSort (.inl i) x = f.state i x := rfl

/-- A structural observation component is the identity of the prescribed type. -/
theorem toStructureMap_observation (f : X ⟶ Y) (i : V) (x : O.obj i) :
    (toStructureMap f).onSort (.inr i) x = x := rfl

end Action

variable {Name : Type u}

/-- Supply a named family of Laws for the shared protocol vocabulary. -/
def theoryWithLaws (laws : Name → Law (signature V)) : Theory.{u} := ⟨signature V, Name, laws⟩

/-- Select the actions that satisfy exactly the supplied Laws. -/
def satisfies (O : V ⥤q Type u) (laws : Name → Law (signature V)) : ObjectProperty (Action O) :=
  fun X => (theoryWithLaws laws).Holds X.toStructure

/-- The category of actions satisfying those Laws retains all structure-preserving maps. -/
abbrev LawfulAction (O : V ⥤q Type u) (laws : Name → Law (signature V)) := (satisfies O laws).FullSubcategory

/-- The semantic category of the same Laws with the prescribed observation reduct. -/
abbrev Semantic (O : V ⥤q Type u) (laws : Name → Law (signature V)) :=
  FixedModel (theoryWithLaws laws) (observationInclusion V) (observationData O)

namespace LawfulAction

variable {laws : Name → Law (signature V)}

/-- Interpret the lawful action as a model with the exact observation structure. -/
def toModel (X : LawfulAction O laws) : Semantic O laws :=
  ⟨⟨X.obj.toStructure, X.property⟩, X.obj.restrict_toStructure⟩

/-- Recover the lawful action from a fixed-reduct model. -/
def ofModel (A : Semantic O laws) : LawfulAction O laws :=
  ⟨Action.ofStructure A.model.obj A.fixed, fun n =>
    (Action.toStructure_ofStructure A.model.obj A.fixed).symm ▸ A.model.property n⟩

/-- Encoding and reading the action recovers the whole object. -/
@[simp] theorem ofModel_toModel (X : LawfulAction O laws) : ofModel (toModel X) = X :=
  ObjectProperty.FullSubcategory.ext (Action.ofStructure_toStructure X.obj)

/-- Reading and encoding the model recovers both the model and its fixed reduct. -/
@[simp] theorem toModel_ofModel (A : Semantic O laws) : toModel (ofModel A) = A := by
  have same : (toModel (ofModel A)).model = A.model :=
    ObjectProperty.FullSubcategory.ext (Action.toStructure_ofStructure A.model.obj A.fixed)
  generalize toModel (ofModel A) = B at same ⊢
  cases A
  cases B
  cases same
  rfl

variable {X Y : LawfulAction O laws}

/-- Encode both kinds of carrier maps and the fixed observation condition. -/
def toModelHom (f : X ⟶ Y) : FixedModel.Hom (toModel X) (toModel Y) :=
  FixedModel.Hom.mk (ObjectProperty.homMk (Action.toStructureMap f.hom)) (fun i x => by
    change (Action.toStructureMap f.hom).onSort (.inr i) x = _
    rw [Action.toStructureMap_observation, cast_eq])

/-- A fixed model map gives the structure-preserving state maps of the readback. -/
def ofModelHom {A B : Semantic O laws} (f : FixedModel.Hom A B) : ofModel A ⟶ ofModel B :=
  ObjectProperty.homMk {
    state := fun i => f.modelHom.hom.onSort (.inl i)
    step_comm e x := by
      simpa only [Assignment.map_cons, Assignment.map_empty] using
        f.modelHom.hom.total_comm (.step e) (Assignment.cons x Assignment.empty)
    observe_comm i x := by
      have same := f.modelHom.hom.total_comm (.readout i) (Assignment.cons x Assignment.empty)
      have mapped : f.modelHom.hom.onSort (.inr i) (symbolValue A.model.obj (.readout i) x) =
          symbolValue B.model.obj (.readout i) (f.modelHom.hom.onSort (.inl i) x) := by
        simpa only [Assignment.map_cons, Assignment.map_empty] using same
      have fixed := f.fixes i (symbolValue A.model.obj (.readout i) x)
      change f.modelHom.hom.onSort (.inr i) (symbolValue A.model.obj (.readout i) x) = _ at fixed
      have transported := congrArg (cast (Action.observation_carrier_eq B.model.obj B.fixed i)) mapped
      change cast (B.carrier_eq i) (f.modelHom.hom.onSort (.inr i)
        (symbolValue A.model.obj (.readout i) x)) = _ at transported
      rw [fixed, cast_cast] at transported
      exact transported.symm }

/-- Encoding retains the map on each state carrier. -/
theorem toModelHom_state_apply (f : X ⟶ Y) (i : V) (x : X.obj.state i) :
    (toModelHom f).modelHom.hom.onSort (.inl i) x = f.hom.state i x := rfl

/-- Encoding uses the identity on each fixed observation carrier. -/
theorem toModelHom_observation_apply (f : X ⟶ Y) (i : V) (x : O.obj i) :
    (toModelHom f).modelHom.hom.onSort (.inr i) x = x := rfl

/-- Reading a model arrow retains every state component of the structural map. -/
theorem ofModelHom_state_apply {A B : Semantic O laws} (f : FixedModel.Hom A B) (i : V)
    (x : (ofModel A).obj.state i) :
    (ofModelHom f).hom.state i x = f.modelHom.hom.onSort (.inl i) x := rfl

/-- Encode lawful actions into the fixed-reduct model category. -/
def toModels (O : V ⥤q Type u) (laws : Name → Law (signature V)) : LawfulAction O laws ⥤ Semantic O laws where
  obj := toModel
  map := toModelHom
  map_id _ := FixedModel.Hom.ext (Model.hom_ext fun s _ => by cases s <;> rfl)
  map_comp _ _ := FixedModel.Hom.ext (Model.hom_ext fun s _ => by cases s <;> rfl)

/-- Read lawful actions from fixed-reduct models. -/
def ofModels (O : V ⥤q Type u) (laws : Name → Law (signature V)) : Semantic O laws ⥤ LawfulAction O laws where
  obj := ofModel
  map := ofModelHom
  map_id _ := ObjectProperty.hom_ext (satisfies O laws) (Action.hom_ext (fun _ _ => rfl))
  map_comp _ _ := ObjectProperty.hom_ext (satisfies O laws) (Action.hom_ext (fun _ _ => rfl))

/-- Encoding then reading back is strictly the identity on lawful actions. -/
theorem toModels_comp_ofModels (O : V ⥤q Type u) (laws : Name → Law (signature V)) :
    toModels O laws ⋙ ofModels O laws = 𝟭 (LawfulAction O laws) := by
  have objects (X : LawfulAction O laws) : (toModels O laws ⋙ ofModels O laws).obj X = (𝟭 _).obj X :=
    ofModel_toModel X
  refine Functor.ext objects ?_
  intro X Y f
  apply ObjectProperty.hom_ext (satisfies O laws)
  let forget := (satisfies O laws).ι
  change forget.map ((toModels O laws ⋙ ofModels O laws).map f) =
    forget.map (eqToHom (objects X) ≫ f ≫ eqToHom (objects Y).symm)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  apply Action.hom_ext
  intro i x
  rw [Action.comp_state, Action.comp_state, Action.eqToHom_state, Action.eqToHom_state]
  exact (ofModelHom_state_apply (toModelHom f) i x).trans (toModelHom_state_apply f i x)

/-- Reading then encoding is strictly the identity on fixed-reduct models. -/
theorem ofModels_comp_toModels (O : V ⥤q Type u) (laws : Name → Law (signature V)) :
    ofModels O laws ⋙ toModels O laws = 𝟭 (Semantic O laws) := by
  have objects (A : Semantic O laws) : (ofModels O laws ⋙ toModels O laws).obj A = (𝟭 _).obj A :=
    toModel_ofModel A
  refine Functor.ext objects ?_
  intro A B f
  apply FixedModel.Hom.ext
  let forget : Semantic O laws ⥤ Model (theoryWithLaws laws) := FixedModel.forget
  change forget.map ((ofModels O laws ⋙ toModels O laws).map f) =
    forget.map (eqToHom (objects A) ≫ f ≫ eqToHom (objects B).symm)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  apply Model.hom_ext
  intro s x
  rw [Model.comp_apply, Model.comp_apply, Model.eqToHom_apply, Model.eqToHom_apply]
  cases s with
  | inl i =>
    exact (toModelHom_state_apply (ofModelHom (show FixedModel.Hom A B from f)) i x).trans
      (ofModelHom_state_apply (show FixedModel.Hom A B from f) i x)
  | inr i =>
    have fixes (y : A.model.obj.carrier (.inr i)) :
        (forget.map f).hom.onSort (.inr i) y = cast ((A.carrier_eq i).trans (B.carrier_eq i).symm) y :=
      FixedModel.Hom.fixes (show FixedModel.Hom A B from f) i y
    rw [fixes, cast_cast, cast_cast, cast_eq]
    exact toModelHom_observation_apply (ofModelHom (show FixedModel.Hom A B from f)) i x

/-- Lawful actions and fixed observation models are strictly isomorphic categories. -/
def modelIso (O : V ⥤q Type u) (laws : Name → Law (signature V)) :
    Cat.of (LawfulAction O laws) ≅ Cat.of (Semantic O laws) where
  hom := (toModels O laws).toCatHom
  inv := (ofModels O laws).toCatHom
  hom_inv_id := congrArg Functor.toCatHom (toModels_comp_ofModels O laws)
  inv_hom_id := congrArg Functor.toCatHom (ofModels_comp_toModels O laws)

end LawfulAction
end SHIGURE.Protocol
