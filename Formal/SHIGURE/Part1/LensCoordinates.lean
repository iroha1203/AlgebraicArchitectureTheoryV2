import Formal.SHIGURE.Part1.Lens

/-! # Lens coordinates and all arrows in those coordinates

Proposition 2.10 uses the fiber over a selected view. The two objects of an
arrow may select their basepoints independently. The resulting product
coordinates make every arrow a pair of ordinary functions.
-/

universe u

namespace SHIGURE.Lens

open CategoryTheory

variable {L M N : Lens.{u}}

/-- The complement at a chosen view is the fiber of `get` over it. -/
abbrev Complement (L : Lens.{u}) (v₀ : L.View) := {a : L.State // L.get a = v₀}

/-- Equation (2.12): separate a state into its view and its update to the chosen view. -/
def coordinates (L : Lens.{u}) (v₀ : L.View) : L.State ≃ L.View × L.Complement v₀ where
  toFun a := (L.get a, ⟨L.put a v₀, L.get_put a v₀⟩)
  invFun pair := L.put pair.2.val pair.1
  left_inv a := (L.put_put a v₀ (L.get a)).trans (L.put_get a)
  right_inv := by
    rintro ⟨v, c⟩
    refine Prod.ext (L.get_put c.val v) (Subtype.ext ?_)
    exact (L.put_put c.val v v₀).trans ((congrArg (L.put c.val) c.property.symm).trans (L.put_get c.val))

/-- The first coordinate is `get`. -/
theorem coordinates_get (L : Lens.{u}) (v₀ : L.View) (a : L.State) :
    (L.coordinates v₀ a).1 = L.get a := rfl

/-- The second coordinate updates the state to the chosen view. -/
theorem coordinates_complement_value (L : Lens.{u}) (v₀ : L.View) (a : L.State) :
    (L.coordinates v₀ a).2.val = L.put a v₀ := rfl

/-- The inverse product coordinates update a complement state to the given view. -/
theorem coordinates_symm_apply (L : Lens.{u}) (v₀ : L.View) (pair : L.View × L.Complement v₀) :
    (L.coordinates v₀).symm pair = L.put pair.2.val pair.1 := rfl

/-- In the product coordinates `put` changes only the first coordinate. -/
theorem coordinates_put (L : Lens.{u}) (v₀ : L.View) (a : L.State) (v : L.View) :
    L.coordinates v₀ (L.put a v) = (v, (L.coordinates v₀ a).2) :=
  Prod.ext (L.get_put a v) (Subtype.ext (L.put_put a v v₀))

/-- A state already in the chosen fiber keeps its complement coordinate. -/
theorem coordinates_at_complement (L : Lens.{u}) (v₀ : L.View) (c : L.Complement v₀) :
    L.coordinates v₀ c.val = (v₀, c) :=
  Prod.ext c.property (Subtype.ext ((congrArg (L.put c.val) c.property.symm).trans (L.put_get c.val)))

/-- Equation (2.13): read the complement component by updating to the target basepoint. -/
def complementMap (f : L ⟶ M) (v₀ : L.View) (w₀ : M.View) : L.Complement v₀ → M.Complement w₀ :=
  fun c => ⟨M.put (f.state c.val) w₀, M.get_put _ _⟩

/-- The value of the complement map is the state map followed by a basepoint update. -/
theorem complementMap_apply (f : L ⟶ M) (v₀ : L.View) (w₀ : M.View) (c : L.Complement v₀) :
    (complementMap f v₀ w₀ c).val = M.put (f.state c.val) w₀ := rfl

/-- In product coordinates the state map is the view map paired with the complement map. -/
theorem normalForm (f : L ⟶ M) (v₀ : L.View) (w₀ : M.View)
    (pair : L.View × L.Complement v₀) :
    M.coordinates w₀ (f.state ((L.coordinates v₀).symm pair)) =
      (f.view pair.1, complementMap f v₀ w₀ pair.2) := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [M.coordinates_get, L.coordinates_symm_apply, f.get_comm, L.get_put]
  · rw [M.coordinates_complement_value, complementMap_apply, L.coordinates_symm_apply, f.put_comm, M.put_put]

/-- Transport an arbitrary pair of view and complement maps back to a lens arrow. -/
def homOfPair (v₀ : L.View) (w₀ : M.View)
    (view : L.View → M.View) (complement : L.Complement v₀ → M.Complement w₀) : L ⟶ M where
  state a := (M.coordinates w₀).symm (Prod.map view complement (L.coordinates v₀ a))
  view := view
  get_comm a := by
    rw [M.coordinates_symm_apply, M.get_put]
    exact congrArg view (L.coordinates_get v₀ a)
  put_comm a v := by
    apply (M.coordinates w₀).injective
    simp only [Equiv.apply_symm_apply, M.coordinates_put, L.coordinates_put, Prod.map_apply]
    rfl

/-- The constructed arrow acts by applying both maps in product coordinates. -/
theorem homOfPair_state (v₀ : L.View) (w₀ : M.View) (view : L.View → M.View)
    (complement : L.Complement v₀ → M.Complement w₀) (a : L.State) :
    (homOfPair v₀ w₀ view complement).state a =
      (M.coordinates w₀).symm (Prod.map view complement (L.coordinates v₀ a)) := rfl

/-- Equation (2.13) as a bijection on the entire set of arrows. -/
def homEquiv (v₀ : L.View) (w₀ : M.View) :
    (L ⟶ M) ≃ ((L.View → M.View) × (L.Complement v₀ → M.Complement w₀)) where
  toFun f := (f.view, complementMap f v₀ w₀)
  invFun pair := homOfPair v₀ w₀ pair.1 pair.2
  left_inv f := by
    apply hom_ext
    · intro a
      apply (M.coordinates w₀).injective
      rw [homOfPair_state, Equiv.apply_symm_apply]
      simpa only [Equiv.symm_apply_apply, Prod.map_apply] using (normalForm f v₀ w₀ (L.coordinates v₀ a)).symm
    · intro v
      rfl
  right_inv := by
    rintro ⟨view, complement⟩
    refine Prod.ext rfl (funext fun c => ?_)
    apply Subtype.ext
    rw [complementMap_apply, ← M.coordinates_complement_value,
      homOfPair_state, Equiv.apply_symm_apply, L.coordinates_at_complement]
    rfl

/-- The complement map of an identity is the identity for the same chosen view. -/
theorem complementMap_id (L : Lens.{u}) (v₀ : L.View) : complementMap (𝟙 L) v₀ v₀ = id := by
  funext c
  apply Subtype.ext
  rw [complementMap_apply, id_state, id_eq]
  exact (congrArg (L.put c.val) c.property.symm).trans (L.put_get c.val)

/-- The complement maps compose at any fixed choice of the three basepoints. -/
theorem complementMap_comp (f : L ⟶ M) (g : M ⟶ N) (v₀ : L.View) (w₀ : M.View) (z₀ : N.View) :
    complementMap (f ≫ g) v₀ z₀ = complementMap g w₀ z₀ ∘ complementMap f v₀ w₀ := by
  funext c
  apply Subtype.ext
  simp only [complementMap_apply, comp_state, Function.comp_apply]
  rw [g.put_comm, N.put_put]

/-- Under (2.13), the identity corresponds to the two identity functions. -/
theorem homEquiv_id (L : Lens.{u}) (v₀ : L.View) :
    homEquiv v₀ v₀ (𝟙 L) = (id, id) := Prod.ext rfl (complementMap_id L v₀)

/-- Under (2.13), composition is composition of the two functions separately. -/
theorem homEquiv_comp (f : L ⟶ M) (g : M ⟶ N) (v₀ : L.View) (w₀ : M.View) (z₀ : N.View) :
    homEquiv v₀ z₀ (f ≫ g) =
      ((homEquiv w₀ z₀ g).1 ∘ (homEquiv v₀ w₀ f).1, (homEquiv w₀ z₀ g).2 ∘ (homEquiv v₀ w₀ f).2) :=
  Prod.ext rfl (complementMap_comp f g v₀ w₀ z₀)

/-- The product lens has a view and an independent complement coordinate. -/
def product (V C : Type u) : Lens.{u} :=
  ofTypes (V × C) V Prod.fst (fun a v => (v, a.2)) (fun a => by cases a; rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

namespace BooleanExample

/-- The product lens in the reading-only counterexample. -/
abbrev lens : Lens.{0} := product Bool Bool

/-- Copy the current view into the complement while keeping the view fixed. -/
def readOnlyState (a : lens.State) : lens.State := (a.1, a.1)

/-- The counterexample preserves reading when the view map is the identity. -/
theorem readOnly_get (a : lens.State) : lens.get (readOnlyState a) = id (lens.get a) := rfl

/-- Updating the view after reading-only transport disagrees at `(false, false)` and `true`. -/
theorem readOnly_put_fails :
    readOnlyState (lens.put (false, false) true) ≠ lens.put (readOnlyState (false, false)) (id true) := by
  intro equal
  have second : true = false := congrArg Prod.snd equal
  cases second

/-- The reading-preserving pair cannot be a lens arrow. -/
theorem readOnly_no_hom : ¬ ∃ f : lens ⟶ lens, f.state = readOnlyState ∧ f.view = id := by
  rintro ⟨f, state, view⟩
  have square := f.put_comm (false, false) true
  rw [state, view] at square
  exact readOnly_put_fails square

/-- Flipping the complement and leaving the view fixed is a nonidentity lens arrow. -/
def flipComplement : lens ⟶ lens :=
  ⟨fun a => (a.1, !a.2), id, fun _ => rfl, fun _ _ => rfl⟩

/-- The normal form is valid for independent basepoints even when the view map misses the target basepoint. -/
theorem flip_independent_basepoints :
    flipComplement.view false ≠ true ∧
      (complementMap flipComplement false true ⟨(false, false), rfl⟩).val = (true, true) :=
  ⟨Bool.false_ne_true, rfl⟩

end BooleanExample
end SHIGURE.Lens
