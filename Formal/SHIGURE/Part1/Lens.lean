import Formal.SHIGURE.Part1.Chapter1Examples
import Formal.SHIGURE.Part1.PullbackComparison
import Mathlib.CategoryTheory.Category.Cat

/-! # Total lenses and their models

Definition 2.8 builds the category from the get and put squares. Theorem 2.9
identifies it with the model category for the three Laws of Example 1.6.

## Implementation notes

The two carriers are stored in a family on the two sorts of the signature.
Separate carrier fields would give the same object data, but the family keeps
both carriers literally unchanged when a model is read back and encoded again.
The lens operations and laws are ordinary functions and equations on these
carriers. The model and its structure maps are constructed from those data.
-/

universe u

namespace SHIGURE

open CategoryTheory
open Chapter1.Lens (SortName)

/-- A total lens satisfies the three laws of (1.7). -/
structure Lens where
  /-- The carrier at each of the two sorts. -/
  carrier : SortName.{u} → Type u
  /-- Read the view of a state. -/
  get : carrier .source → carrier .view
  /-- Update a state with a new view. -/
  put : carrier .source → carrier .view → carrier .source
  /-- Updating with the current view leaves the state unchanged. -/
  put_get : ∀ a, put a (get a) = a
  /-- Reading an updated state returns the new view. -/
  get_put : ∀ a v, get (put a v) = v
  /-- Two updates retain only the last requested view. -/
  put_put : ∀ a v w, put (put a v) w = put a w

namespace Lens

/-- The state type of a lens. -/
abbrev State (L : Lens.{u}) := L.carrier .source

/-- The view type of a lens. -/
abbrev View (L : Lens.{u}) := L.carrier .view

/-- Construct a lens from its two types, operations and laws. -/
def ofTypes (S V : Type u) (get : S → V) (put : S → V → S)
    (put_get : ∀ a, put a (get a) = a) (get_put : ∀ a v, get (put a v) = v)
    (put_put : ∀ a v w, put (put a v) w = put a w) : Lens.{u} where
  carrier
    | .source => S
    | .view => V
  get := get
  put := put
  put_get := put_get
  get_put := get_put
  put_put := put_put

/-- Equation (2.10): the state and view maps commute with `get` and `put`. -/
@[ext]
structure Hom (L M : Lens.{u}) where
  /-- The map of states. -/
  state : L.State → M.State
  /-- The map of views. -/
  view : L.View → M.View
  /-- The pair commutes with reading the view. -/
  get_comm : ∀ a, M.get (state a) = view (L.get a)
  /-- The pair commutes with updating the view. -/
  put_comm : ∀ a v, state (L.put a v) = M.put (state a) (view v)

/-- The category of total lenses composes both component maps. -/
instance category : Category.{u} Lens.{u} where
  Hom := Hom
  id _ := ⟨id, id, fun _ => rfl, fun _ _ => rfl⟩
  comp f g :=
    { state := g.state ∘ f.state
      view := g.view ∘ f.view
      get_comm := fun a => by simp only [Function.comp_apply, g.get_comm, f.get_comm]
      put_comm := fun a v => by simp only [Function.comp_apply, f.put_comm, g.put_comm] }
  id_comp := by intros; apply Hom.ext <;> rfl
  comp_id := by intros; apply Hom.ext <;> rfl
  assoc := by intros; apply Hom.ext <;> rfl

variable {L M N : Lens.{u}}

/-- The identity lens arrow is the identity on states. -/
@[simp] theorem id_state (L : Lens.{u}) : (show Hom L L from 𝟙 L).state = id := rfl

/-- The identity lens arrow is the identity on views. -/
@[simp] theorem id_view (L : Lens.{u}) : (show Hom L L from 𝟙 L).view = id := rfl

/-- The state component of a composite composes the state maps. -/
@[simp] theorem comp_state (f : L ⟶ M) (g : M ⟶ N) :
    (show Hom L N from f ≫ g).state = g.state ∘ f.state := rfl

/-- The view component of a composite composes the view maps. -/
@[simp] theorem comp_view (f : L ⟶ M) (g : M ⟶ N) :
    (show Hom L N from f ≫ g).view = g.view ∘ f.view := rfl

/-- Equality of the two maps determines a lens arrow. -/
theorem hom_ext {f g : L ⟶ M} (state : ∀ a, f.state a = g.state a) (view : ∀ v, f.view v = g.view v) :
    f = g := Hom.ext (funext state) (funext view)

/-- Transport along equality of lens objects carries each state by type equality. -/
theorem eqToHom_state {L M : Lens.{u}} (same : L = M) (a : L.State) :
    (show Hom L M from eqToHom same).state a = cast (congrArg State same) a := by
  subst M
  simp only [eqToHom_refl, id_state, id_eq, cast_eq]

/-- Transport along equality of lens objects carries each view by type equality. -/
theorem eqToHom_view {L M : Lens.{u}} (same : L = M) (v : L.View) :
    (show Hom L M from eqToHom same).view v = cast (congrArg View same) v := by
  subst M
  simp only [eqToHom_refl, id_view, id_eq, cast_eq]

/-- A lens structure interprets precisely the two total symbols of Example 1.6. -/
def toStructure (L : Lens.{u}) : Structure Chapter1.Lens.signature.{u} where
  carrier := L.carrier
  total
    | .get => fun xs => L.get (xs .here)
    | .put => fun xs => L.put (xs .here) (xs (.there .here))
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- Read the interpretation of the `get` symbol at a unary input. -/
private def structureGet (A : Structure Chapter1.Lens.signature.{u}) : A.carrier .source → A.carrier .view :=
  fun a => A.total .get (Assignment.cons a Assignment.empty)

/-- Read the interpretation of the `put` symbol at a state and a view. -/
private def structurePut (A : Structure Chapter1.Lens.signature.{u}) :
    A.carrier .source → A.carrier .view → A.carrier .source :=
  fun a v => A.total .put (Assignment.cons a (Assignment.cons v Assignment.empty))

/-- A syntax-level read evaluates by the interpreted `get` operation. -/
private theorem getTerm_totalValue {Γ : List SortName.{u}}
    (A : Structure Chapter1.Lens.signature.{u}) (e : Assignment A.carrier Γ)
    (a : Term Chapter1.Lens.signature Γ .source) :
    (Chapter1.Lens.getTerm a).totalValue A e = structureGet A (a.totalValue A e) := by
  apply congrArg (A.total .get)
  apply Assignment.ext
  intro s i
  cases i with
  | here => rfl
  | there i => exact nomatch i

/-- A syntax-level update evaluates by the interpreted `put` operation. -/
private theorem putTerm_totalValue {Γ : List SortName.{u}}
    (A : Structure Chapter1.Lens.signature.{u}) (e : Assignment A.carrier Γ)
    (a : Term Chapter1.Lens.signature Γ .source) (v : Term Chapter1.Lens.signature Γ .view) :
    (Chapter1.Lens.putTerm a v).totalValue A e = structurePut A (a.totalValue A e) (v.totalValue A e) := by
  apply congrArg (A.total .put)
  apply Assignment.ext
  intro s i
  cases i with
  | here => rfl
  | there i =>
    cases i with
    | here => rfl
    | there i => exact nomatch i

/-- The first Law of Example 1.6 is exactly the update-by-current-view law. -/
private theorem getPut_law_iff (A : Structure Chapter1.Lens.signature.{u}) :
    (Chapter1.Lens.law .getPut).Holds A ↔ ∀ a, structurePut A a (structureGet A a) = a := by
  rw [Chapter1.Lens.law, Law.holds_equality_totalValue_iff]
  simp only [getTerm_totalValue, putTerm_totalValue, Term.totalValue]
  exact ⟨fun h a => h (Assignment.cons a Assignment.empty), fun h e => h (e .here)⟩

/-- The second Law of Example 1.6 is exactly the read-after-update law. -/
private theorem putGet_law_iff (A : Structure Chapter1.Lens.signature.{u}) :
    (Chapter1.Lens.law .putGet).Holds A ↔ ∀ a v, structureGet A (structurePut A a v) = v := by
  rw [Chapter1.Lens.law, Law.holds_equality_totalValue_iff]
  simp only [getTerm_totalValue, putTerm_totalValue, Term.totalValue]
  exact ⟨fun h a v => h (Assignment.cons a (Assignment.cons v Assignment.empty)),
    fun h e => h (e .here) (e (.there .here))⟩

/-- The third Law of Example 1.6 says that the last update suffices. -/
private theorem putPut_law_iff (A : Structure Chapter1.Lens.signature.{u}) :
    (Chapter1.Lens.law .putPut).Holds A ↔
      ∀ a v w, structurePut A (structurePut A a v) w = structurePut A a w := by
  rw [Chapter1.Lens.law, Law.holds_equality_totalValue_iff]
  simp only [putTerm_totalValue, Term.totalValue]
  exact ⟨fun h a v w => h (Assignment.cons a (Assignment.cons v (Assignment.cons w Assignment.empty))),
    fun h e => h (e .here) (e (.there .here)) (e (.there (.there .here)))⟩

/-- The three elementary lens laws make its structure a model. -/
def toModel (L : Lens.{u}) : Model Chapter1.Lens.theory.{u} :=
  ⟨L.toStructure, fun name => match name with
    | .getPut => (getPut_law_iff L.toStructure).2 L.put_get
    | .putGet => (putGet_law_iff L.toStructure).2 L.get_put
    | .putPut => (putPut_law_iff L.toStructure).2 L.put_put⟩

/-- Read the two operations and three laws from a model of the lens theory. -/
def ofModel (A : Model Chapter1.Lens.theory.{u}) : Lens.{u} where
  carrier := A.obj.carrier
  get := structureGet A.obj
  put := structurePut A.obj
  put_get := (getPut_law_iff A.obj).1 (A.property .getPut)
  get_put := (putGet_law_iff A.obj).1 (A.property .putGet)
  put_put := (putPut_law_iff A.obj).1 (A.property .putPut)

/-- Reading back a lens model recovers the same carriers and both functions. -/
@[simp] theorem ofModel_toModel (L : Lens.{u}) : ofModel L.toModel = L := by
  cases L
  rfl

/-- Every model of the lens theory is recovered strictly by re-encoding its lens. -/
@[simp] theorem toModel_ofModel (A : Model Chapter1.Lens.theory.{u}) : (ofModel A).toModel = A := by
  apply ObjectProperty.FullSubcategory.ext
  change (ofModel A).toStructure = A.obj
  have domains : (ofModel A).toStructure.partialDomain = A.obj.partialDomain := by
    funext p
    exact nomatch p
  refine Structure.ext rfl ?_ ?_ (heq_of_eq domains) ?_ ?_
  · apply heq_of_eq
    funext f xs
    cases f with
    | get =>
      change A.obj.total .get (Assignment.cons (xs .here) Assignment.empty) = A.obj.total .get xs
      apply congrArg (A.obj.total .get)
      apply Assignment.ext
      intro s i
      cases i with
      | here => rfl
      | there i => exact nomatch i
    | put =>
      change A.obj.total .put (Assignment.cons (xs .here) (Assignment.cons (xs (.there .here))
        Assignment.empty)) = A.obj.total .put xs
      apply congrArg (A.obj.total .put)
      apply Assignment.ext
      intro s i
      cases i with
      | here => rfl
      | there i =>
        cases i with
        | here => rfl
        | there i => exact nomatch i
  · apply heq_of_eq
    funext r
    exact nomatch r
  · exact Structure.partialValue_heq domains _ _ (fun p => nomatch p)
  · apply heq_of_eq
    funext q
    exact nomatch q

/-- The two squares of a lens arrow provide all structural preservation fields. -/
def toModelHom (f : L ⟶ M) : L.toModel ⟶ M.toModel :=
  ObjectProperty.homMk {
    onSort
      | .source => f.state
      | .view => f.view
    total_comm
      | .get => fun xs => (f.get_comm (xs .here)).symm
      | .put => fun xs => f.put_comm (xs .here) (xs (.there .here))
    relation_mem r := nomatch r
    partial_mem p := nomatch p
    partial_comm p := nomatch p
    quantity_comm q := nomatch q }

/-- A model arrow gives the two maps and both preservation squares of a lens arrow. -/
def ofModelHom {A B : Model Chapter1.Lens.theory.{u}} (f : A ⟶ B) : ofModel A ⟶ ofModel B where
  state := f.hom.onSort .source
  view := f.hom.onSort .view
  get_comm a := by
    simpa only [Assignment.map_cons, Assignment.map_empty] using
      (f.hom.total_comm .get (Assignment.cons a Assignment.empty)).symm
  put_comm a v := by
    simpa only [Assignment.map_cons, Assignment.map_empty] using
      f.hom.total_comm .put (Assignment.cons a (Assignment.cons v Assignment.empty))

/-- Encode total lenses and both components of every arrow as models. -/
def toModels : Lens.{u} ⥤ Model Chapter1.Lens.theory.{u} where
  obj := toModel
  map := toModelHom
  map_id _ := Model.hom_ext (fun s _ => by cases s <;> rfl)
  map_comp _ _ := Model.hom_ext (fun s _ => by cases s <;> rfl)

/-- Read total lenses and their arrows back from the full model category. -/
def ofModels : Model Chapter1.Lens.theory.{u} ⥤ Lens.{u} where
  obj := ofModel
  map := ofModelHom
  map_id _ := hom_ext (fun _ => rfl) (fun _ => rfl)
  map_comp _ _ := hom_ext (fun _ => rfl) (fun _ => rfl)

/-- Encoding then reading back is the identity functor on total lenses. -/
theorem toModels_comp_ofModels : toModels.{u} ⋙ ofModels.{u} = 𝟭 Lens.{u} := by
  refine Functor.ext ofModel_toModel ?_
  intro L M f
  apply hom_ext
  · intro a
    simp only [comp_state, eqToHom_state, Function.comp_apply, cast_eq]
    rfl
  · intro v
    simp only [comp_view, eqToHom_view, Function.comp_apply, cast_eq]
    rfl

/-- Reading and encoding is the identity functor on all models and all arrows. -/
theorem ofModels_comp_toModels : ofModels.{u} ⋙ toModels.{u} = 𝟭 (Model Chapter1.Lens.theory.{u}) := by
  refine Functor.ext toModel_ofModel ?_
  intro A B f
  apply Model.hom_ext
  intro s x
  rw [Model.comp_apply, Model.comp_apply, Model.eqToHom_apply, Model.eqToHom_apply]
  cases s <;> rfl

/-- Equation (2.11) as a strict isomorphism in mathlib's category of categories. -/
def modelIso : Cat.of Lens.{u} ≅ Cat.of (Model Chapter1.Lens.theory.{u}) where
  hom := toModels.toCatHom
  inv := ofModels.toCatHom
  hom_inv_id := congrArg Functor.toCatHom toModels_comp_ofModels
  inv_hom_id := congrArg Functor.toCatHom ofModels_comp_toModels

/-- The two object constructions give a bijection on all lenses and all models. -/
def modelObjectEquiv : Lens.{u} ≃ Model Chapter1.Lens.theory.{u} :=
  ⟨toModel, ofModel, ofModel_toModel, toModel_ofModel⟩

/-- The model isomorphism recovers every arrow between the encoded lenses. -/
def modelHomEquiv (L M : Lens.{u}) : (L ⟶ M) ≃ (L.toModel ⟶ M.toModel) :=
  (Cat.equivOfIso modelIso).fullyFaithfulFunctor.homEquiv

/-- The hom-set bijection sends a lens arrow to its two original maps. -/
theorem modelHomEquiv_apply (f : L ⟶ M) : modelHomEquiv L M f = toModelHom f := rfl

end Lens
end SHIGURE
