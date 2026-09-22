import ResearchLean.AG.RealizationReconstruction.LensSemantics
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Formal.Util.AssertStandardAxioms

/-!
General total lenses and relative morphisms. The view and state types vary
independently between objects; no reference view or finiteness is assumed.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- A total, very-well-behaved lens on arbitrary state and view types. -/
structure GeneralLens where
  State : Type u
  View : Type u
  get : State → View
  put : State → View → State
  put_get : ∀ c, put c (get c) = c
  get_put : ∀ c v, get (put c v) = v
  put_put : ∀ c v w, put (put c v) w = put c w

namespace GeneralLens

/-- Relative morphisms use one state map and one view map in both squares. -/
@[ext]
structure Hom (L M : GeneralLens.{u}) where
  state : L.State → M.State
  view : L.View → M.View
  get_comm : ∀ c, M.get (state c) = view (L.get c)
  put_comm : ∀ c v, state (L.put c v) = M.put (state c) (view v)

/-- The update square alone forces the read square. -/
theorem get_comm_of_put_comm {L M : GeneralLens.{u}}
    (h : L.State → M.State) (v : L.View → M.View)
    (hp : ∀ c w, h (L.put c w) = M.put (h c) (v w)) (c : L.State) :
    M.get (h c) = v (L.get c) := by
  calc
    M.get (h c) = M.get (h (L.put c (L.get c))) := by rw [L.put_get]
    _ = M.get (M.put (h c) (v (L.get c))) := by rw [hp]
    _ = v (L.get c) := M.get_put _ _

/-- The two named operations assembled into a single typed map. -/
def operation (L : GeneralLens.{u}) :
    L.State ⊕ (L.State × L.View) → L.View ⊕ L.State
  | .inl c => .inl (L.get c)
  | .inr cv => .inr (L.put cv.1 cv.2)

/-- Equation (4.46) is equivalent to both relative lens squares (4.44). -/
theorem operation_square_iff (L M : GeneralLens.{u})
    (h : L.State → M.State) (v : L.View → M.View) :
    (∀ x, Sum.map v h (L.operation x) =
      M.operation (Sum.map h (Prod.map h v) x)) ↔
      (∀ c, M.get (h c) = v (L.get c)) ∧
      (∀ c w, h (L.put c w) = M.put (h c) (v w)) := by
  constructor
  · intro hs
    constructor
    · intro c
      have := hs (.inl c)
      exact Sum.inl.inj this.symm
    · intro c w
      have := hs (.inr (c, w))
      exact Sum.inr.inj this
  · rintro ⟨hg, hp⟩ x
    cases x with
    | inl c => exact congrArg Sum.inl (hg c).symm
    | inr cv => exact congrArg Sum.inr (hp cv.1 cv.2)

/-- Identity and composition preserve both named operations. -/
instance : Category GeneralLens.{u} where
  Hom := Hom
  id L := ⟨id, id, (fun _ => rfl), (fun _ _ => rfl)⟩
  comp f g :=
    { state := g.state ∘ f.state
      view := g.view ∘ f.view
      get_comm := fun c => by simp [Function.comp, g.get_comm, f.get_comm]
      put_comm := fun c v => by simp [Function.comp, f.put_comm, g.put_comm] }
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by intros; ext <;> rfl

/-- Every relative morphism gives the typed operation square. -/
theorem Hom.operation_square {L M : GeneralLens.{u}} (f : L ⟶ M) (x) :
    Sum.map f.view f.state (L.operation x) =
      M.operation (Sum.map f.state (Prod.map f.state f.view) x) :=
  (operation_square_iff L M f.state f.view).2 ⟨f.get_comm, f.put_comm⟩ x

/-- All pairs of bijections satisfying the put square form the reversible
relative changes of a lens; get preservation follows from the lens laws. -/
def invertibleOfPut {L M : GeneralLens.{u}}
    (h : L.State ≃ M.State) (v : L.View ≃ M.View)
    (hp : ∀ c w, h (L.put c w) = M.put (h c) (v w)) : L ≅ M where
  hom := ⟨h, v, get_comm_of_put_comm h v hp, hp⟩
  inv :=
    { state := h.symm
      view := v.symm
      get_comm := fun c => by
        apply v.injective
        have hg := get_comm_of_put_comm h v hp (h.symm c)
        simpa using hg.symm
      put_comm := fun c w => by
        apply h.injective
        have he := hp (h.symm c) (v.symm w)
        simpa using he.symm }
  hom_inv_id := by
    apply Hom.ext
    · funext x
      exact h.symm_apply_apply x
    · funext x
      exact v.symm_apply_apply x
  inv_hom_id := by
    apply Hom.ext
    · funext x
      exact h.apply_symm_apply x
    · funext x
      exact v.apply_symm_apply x

/-- The get-preserving pairs include every put-preserving pair of bijections. -/
theorem putPreserving_subset_getPreserving (L : GeneralLens.{u}) :
    {p : Equiv.Perm L.State × Equiv.Perm L.View |
      ∀ c w, p.1 (L.put c w) = L.put (p.1 c) (p.2 w)} ⊆
    {p : Equiv.Perm L.State × Equiv.Perm L.View |
      ∀ c, L.get (p.1 c) = p.2 (L.get c)} := by
  rintro ⟨h, v⟩ hp c
  exact get_comm_of_put_comm h v hp c

/-- The subgroup of bijective state/view pairs preserving get. -/
def getGroup (L : GeneralLens.{u}) :
    Subgroup (Equiv.Perm L.State × Equiv.Perm L.View) where
  carrier := {p | ∀ c, L.get (p.1 c) = p.2 (L.get c)}
  one_mem' := by intro c; rfl
  mul_mem' := by
    intro a b ha hb c
    change (∀ c, L.get (a.1 c) = a.2 (L.get c)) at ha
    change (∀ c, L.get (b.1 c) = b.2 (L.get c)) at hb
    change L.get ((a.1 * b.1) c) = (a.2 * b.2) (L.get c)
    simp only [Equiv.Perm.mul_apply]
    rw [ha (b.1 c), hb c]
  inv_mem' := by
    intro a ha c
    change L.get (a.1.symm c) = a.2.symm (L.get c)
    apply a.2.injective
    simpa using (ha (a.1.symm c)).symm

/-- The subgroup of bijective state/view pairs preserving put. -/
def putGroup (L : GeneralLens.{u}) :
    Subgroup (Equiv.Perm L.State × Equiv.Perm L.View) where
  carrier := {p | ∀ c v, p.1 (L.put c v) = L.put (p.1 c) (p.2 v)}
  one_mem' := by intro c v; rfl
  mul_mem' := by
    intro a b ha hb c v
    change (∀ c v, a.1 (L.put c v) = L.put (a.1 c) (a.2 v)) at ha
    change (∀ c v, b.1 (L.put c v) = L.put (b.1 c) (b.2 v)) at hb
    change (a.1 * b.1) (L.put c v) =
      L.put ((a.1 * b.1) c) ((a.2 * b.2) v)
    simp only [Equiv.Perm.mul_apply]
    rw [hb c v, ha (b.1 c) (b.2 v)]
  inv_mem' := by
    intro a ha c v
    change a.1.symm (L.put c v) =
      L.put (a.1.symm c) (a.2.symm v)
    apply a.1.injective
    simpa using (ha (a.1.symm c) (a.2.symm v)).symm

/-- Equation (4.47): the two-operation automorphism group is the put
stabilizer, and put preservation forces get preservation. -/
theorem putGroup_le_getGroup (L : GeneralLens.{u}) :
    L.putGroup ≤ L.getGroup := by
  intro p hp
  exact putPreserving_subset_getPreserving L hp

theorem getGroup_inf_putGroup (L : GeneralLens.{u}) :
    L.getGroup ⊓ L.putGroup = L.putGroup := by
  exact inf_eq_right.mpr L.putGroup_le_getGroup

/-- A nontrivial get-preserving state permutation on the Boolean product lens. -/
def boolFiberTwist : Equiv.Perm (Bool × Bool) where
  toFun := fun (v, k) => (v, xor k v)
  invFun := fun (v, k) => (v, xor k v)
  left_inv := by intro ⟨v, k⟩; cases v <;> cases k <;> rfl
  right_inv := by intro ⟨v, k⟩; cases v <;> cases k <;> rfl

/-- Canonical reference fiber at an arbitrary selected view. -/
abbrev Fiber (L : GeneralLens.{u}) (v₀ : L.View) :=
  {c : L.State // L.get c = v₀}

/-- A lens is canonically a product of its view with any reference fiber. -/
def productEquiv (L : GeneralLens.{u}) (v₀ : L.View) :
    L.State ≃ L.View × L.Fiber v₀ where
  toFun c := (L.get c, ⟨L.put c v₀, L.get_put c v₀⟩)
  invFun x := L.put x.2.1 x.1
  left_inv c := by
    change L.put (L.put c v₀) (L.get c) = c
    rw [L.put_put, L.put_get]
  right_inv x := by
    apply Prod.ext
    · exact L.get_put _ _
    · apply Subtype.ext
      change L.put (L.put x.2.1 x.1) v₀ = x.2.1
      rw [L.put_put]
      calc
        L.put x.2.1 v₀ = L.put x.2.1 (L.get x.2.1) :=
          congrArg (L.put x.2.1) x.2.2.symm
        _ = x.2.1 := L.put_get _

theorem productEquiv_get (L : GeneralLens.{u}) (v₀ : L.View)
    (c : L.State) : (L.productEquiv v₀ c).1 = L.get c := rfl

theorem productEquiv_put (L : GeneralLens.{u}) (v₀ : L.View)
    (c : L.State) (w : L.View) :
    L.productEquiv v₀ (L.put c w) =
      (w, (L.productEquiv v₀ c).2) := by
  apply Prod.ext
  · exact L.get_put c w
  · apply Subtype.ext
    exact L.put_put c w v₀

/-- A relative map sends the chosen source fiber to the chosen target fiber
after updating to the target reference view. -/
def fiberMap {L M : GeneralLens.{u}} (f : L ⟶ M)
    (v₀ : L.View) (w₀ : M.View) : L.Fiber v₀ → M.Fiber w₀ :=
  fun k => ⟨M.put (f.state k.1) w₀, M.get_put _ _⟩

theorem fiberMap_id (L : GeneralLens.{u}) (v₀ : L.View) :
    fiberMap (𝟙 L) v₀ v₀ = id := by
  funext k
  apply Subtype.ext
  change L.put k.1 v₀ = k.1
  calc
    L.put k.1 v₀ = L.put k.1 (L.get k.1) := congrArg (L.put k.1) k.2.symm
    _ = k.1 := L.put_get _

theorem fiberMap_comp {L M N : GeneralLens.{u}}
    (f : L ⟶ M) (g : M ⟶ N)
    (v₀ : L.View) (w₀ : M.View) (z₀ : N.View) :
    fiberMap (f ≫ g) v₀ z₀ =
      fiberMap g w₀ z₀ ∘ fiberMap f v₀ w₀ := by
  funext k
  apply Subtype.ext
  change N.put (g.state (f.state k.1)) z₀ =
    N.put (g.state (M.put (f.state k.1) w₀)) z₀
  rw [g.put_comm, N.put_put]

/-- A reversible relative change induces a bijection between independently
chosen source and target reference fibers. -/
def fiberEquiv {L M : GeneralLens.{u}} (e : L ≅ M)
    (v₀ : L.View) (w₀ : M.View) : L.Fiber v₀ ≃ M.Fiber w₀ where
  toFun := fiberMap e.hom v₀ w₀
  invFun := fiberMap e.inv w₀ v₀
  left_inv k := by
    have hc := congrArg (fun f => fiberMap f v₀ v₀) e.hom_inv_id
    change fiberMap (e.hom ≫ e.inv) v₀ v₀ = fiberMap (𝟙 L) v₀ v₀ at hc
    rw [fiberMap_comp e.hom e.inv v₀ w₀ v₀, fiberMap_id] at hc
    exact congrFun hc k
  right_inv k := by
    have hc := congrArg (fun f => fiberMap f w₀ w₀) e.inv_hom_id
    change fiberMap (e.inv ≫ e.hom) w₀ w₀ = fiberMap (𝟙 M) w₀ w₀ at hc
    rw [fiberMap_comp e.inv e.hom w₀ v₀ w₀, fiberMap_id] at hc
    exact congrFun hc k

/-- The view component of a relative lens isomorphism is an equivalence. -/
def viewEquiv {L M : GeneralLens.{u}} (e : L ≅ M) :
    L.View ≃ M.View where
  toFun := e.hom.view
  invFun := e.inv.view
  left_inv v := by
    have he := congrArg (fun f : L ⟶ L => f.view) e.hom_inv_id
    exact congrFun he v
  right_inv v := by
    have he := congrArg (fun f : M ⟶ M => f.view) e.inv_hom_id
    exact congrFun he v

/-- The state component of a relative lens isomorphism is an equivalence. -/
def stateEquiv {L M : GeneralLens.{u}} (e : L ≅ M) :
    L.State ≃ M.State where
  toFun := e.hom.state
  invFun := e.inv.state
  left_inv c := by
    have he := congrArg (fun f : L ⟶ L => f.state) e.hom_inv_id
    exact congrFun he c
  right_inv c := by
    have he := congrArg (fun f : M ⟶ M => f.state) e.inv_hom_id
    exact congrFun he c

/-- General two-lens normal form; the two reference views are independent. -/
theorem normalForm {L M : GeneralLens.{u}} (f : L ⟶ M)
    (v₀ : L.View) (w₀ : M.View) (c : L.State) :
    f.state c =
      (M.productEquiv w₀).symm
        (f.view (L.get c), fiberMap f v₀ w₀ (L.productEquiv v₀ c).2) := by
  change f.state c = M.put
    (M.put (f.state (L.put c v₀)) w₀) (f.view (L.get c))
  rw [f.put_comm, M.put_put]
  have hc : M.get (f.state c) = f.view (L.get c) := f.get_comm c
  rw [← hc, M.put_put, M.put_get]

/-- In the invertible case the hidden component in the general two-lens
normal form is the constructed fiber equivalence. -/
theorem invertibleNormalForm {L M : GeneralLens.{u}} (e : L ≅ M)
    (v₀ : L.View) (w₀ : M.View) (c : L.State) :
    stateEquiv e c =
      (M.productEquiv w₀).symm
        (viewEquiv e (L.get c),
          fiberEquiv e v₀ w₀ (L.productEquiv v₀ c).2) :=
  normalForm e.hom v₀ w₀ c

/-- The converse of the two-fiber normal form: independent view and reference
fiber equivalences assemble an invertible relative change of arbitrary lenses. -/
def isoOfViewFiberEquiv {L M : GeneralLens.{u}}
    (v₀ : L.View) (w₀ : M.View)
    (visible : L.View ≃ M.View)
    (hidden : L.Fiber v₀ ≃ M.Fiber w₀) : L ≅ M := by
  let h : L.State ≃ M.State :=
    (L.productEquiv v₀).trans
      ((Equiv.prodCongr visible hidden).trans (M.productEquiv w₀).symm)
  apply invertibleOfPut h visible
  intro c v
  apply (M.productEquiv w₀).injective
  change (M.productEquiv w₀) (h (L.put c v)) =
    (M.productEquiv w₀) (M.put (h c) (visible v))
  rw [M.productEquiv_put]
  have hc := L.productEquiv_put v₀ c v
  simp only [h, Equiv.trans_apply]
  rw [hc]
  simp

/-- The constructed change has exactly the stipulated product normal form. -/
theorem isoOfViewFiberEquiv_state {L M : GeneralLens.{u}}
    (v₀ : L.View) (w₀ : M.View)
    (visible : L.View ≃ M.View)
    (hidden : L.Fiber v₀ ≃ M.Fiber w₀) (c : L.State) :
    (isoOfViewFiberEquiv v₀ w₀ visible hidden).hom.state c =
      (M.productEquiv w₀).symm
        (visible (L.get c), hidden (L.productEquiv v₀ c).2) := rfl

/-- Extracting the visible and hidden equivalences from an arbitrary lens
isomorphism and reconstructing gives the original isomorphism. -/
theorem isoOfViewFiberEquiv_viewEquiv_fiberEquiv
    {L M : GeneralLens.{u}} (e : L ≅ M)
    (v₀ : L.View) (w₀ : M.View) :
    isoOfViewFiberEquiv v₀ w₀ (viewEquiv e) (fiberEquiv e v₀ w₀) = e := by
  apply Iso.ext
  apply Hom.ext
  · funext c
    exact (invertibleNormalForm e v₀ w₀ c).symm
  · rfl

theorem viewEquiv_isoOfViewFiberEquiv {L M : GeneralLens.{u}}
    (v₀ : L.View) (w₀ : M.View)
    (visible : L.View ≃ M.View)
    (hidden : L.Fiber v₀ ≃ M.Fiber w₀) :
    viewEquiv (isoOfViewFiberEquiv v₀ w₀ visible hidden) = visible := by
  ext v
  rfl

theorem fiberEquiv_isoOfViewFiberEquiv {L M : GeneralLens.{u}}
    (v₀ : L.View) (w₀ : M.View)
    (visible : L.View ≃ M.View)
    (hidden : L.Fiber v₀ ≃ M.Fiber w₀) :
    fiberEquiv (isoOfViewFiberEquiv v₀ w₀ visible hidden) v₀ w₀ = hidden := by
  ext k
  change M.put ((isoOfViewFiberEquiv v₀ w₀ visible hidden).hom.state k.1) w₀ =
    (hidden k).1
  rw [isoOfViewFiberEquiv_state]
  have hk : (L.productEquiv v₀ k.1).2 = k := by
    apply Subtype.ext
    change L.put k.1 v₀ = k.1
    calc
      L.put k.1 v₀ = L.put k.1 (L.get k.1) :=
        congrArg (L.put k.1) k.2.symm
      _ = k.1 := L.put_get _
  rw [k.2, hk]
  change M.put (M.put (hidden k).1 (visible v₀)) w₀ = (hidden k).1
  rw [M.put_put]
  calc
    M.put (hidden k).1 w₀ = M.put (hidden k).1 (M.get (hidden k).1) :=
      congrArg (M.put (hidden k).1) (hidden k).2.symm
    _ = (hidden k).1 := M.put_get _

/-- The complete classification of invertible relative lens changes by an
arbitrary visible equivalence and an equivalence of independent reference
fibers. -/
def isoEquivViewFiberEquiv {L M : GeneralLens.{u}}
    (v₀ : L.View) (w₀ : M.View) :
    (L ≅ M) ≃ ((L.View ≃ M.View) × (L.Fiber v₀ ≃ M.Fiber w₀)) where
  toFun e := (viewEquiv e, fiberEquiv e v₀ w₀)
  invFun pair := isoOfViewFiberEquiv v₀ w₀ pair.1 pair.2
  left_inv e := isoOfViewFiberEquiv_viewEquiv_fiberEquiv e v₀ w₀
  right_inv pair := by
    apply Prod.ext
    · exact viewEquiv_isoOfViewFiberEquiv v₀ w₀ pair.1 pair.2
    · exact fiberEquiv_isoOfViewFiberEquiv v₀ w₀ pair.1 pair.2

/-- The product construction has no restriction on the hidden type. -/
def productLens (V K : Type u) : GeneralLens.{u} where
  State := V × K
  View := V
  get := Prod.fst
  put := fun c v => (v, c.2)
  put_get := fun ⟨_, _⟩ => rfl
  get_put := fun _ _ => rfl
  put_put := fun ⟨_, _⟩ _ _ => rfl

/-- The inclusion of put-preserving changes in get-preserving changes can be
proper: the Boolean fiber twist reads correctly but does not update correctly. -/
theorem boolFiberTwist_get_not_put :
    (boolFiberTwist, Equiv.refl Bool) ∈
      (productLens Bool Bool).getGroup ∧
    (boolFiberTwist, Equiv.refl Bool) ∉
      (productLens Bool Bool).putGroup := by
  constructor
  · intro c
    rfl
  · intro hp
    have he := hp (false, false) true
    have hk := congrArg Prod.snd he
    cases hk

/-- Any visible map and any hidden map induce a relative product-lens map. -/
def productMap {V W K H : Type u} (v : V → W) (t : K → H) :
    productLens V K ⟶ productLens W H where
  state := Prod.map v t
  view := v
  get_comm := fun _ => rfl
  put_comm := fun _ _ => rfl

@[simp] theorem productMap_state {V W K H : Type u}
    (v : V → W) (t : K → H) (c : V × K) :
    (productMap v t).state c = (v c.1, t c.2) := rfl

/-- Example (4.39): merging the two Boolean hidden states is a lens morphism
whose state map is not injective. -/
theorem boolToPoint_not_injective :
    ¬ Function.Injective
      (productMap (id : PUnit → PUnit) (fun _ : Bool => PUnit.unit)).state := by
  intro hi
  have he := hi (show (productMap (id : PUnit → PUnit)
    (fun _ : Bool => PUnit.unit)).state (PUnit.unit, false) =
    (productMap (id : PUnit → PUnit)
      (fun _ : Bool => PUnit.unit)).state (PUnit.unit, true) from rfl)
  exact Bool.false_ne_true (congrArg Prod.snd he)

/-- The existing finite-reference semantic object is an instance of the
general three-law lens, retaining its actual carrier and operations. -/
def ofLensRealization {V : Type u} {v₀ : V}
    (L : LensRealization V v₀) : GeneralLens.{u} where
  State := L.Carrier
  View := V
  get := L.get
  put := L.put
  put_get := L.condition.put_get
  get_put := L.condition.get_put
  put_put := L.condition.put_put

/-- Existing fixed-view semantic morphisms embed with identity view map. -/
def ofFixedHom {V : Type u} {v₀ : V}
    {L M : LensRealization V v₀} (f : L ⟶ M) :
    ofLensRealization L ⟶ ofLensRealization M where
  state := f.toFun
  view := id
  get_comm := f.get_naturality
  put_comm := f.put_naturality

/-- The identity-view fiber recovers the existing semantic morphism exactly. -/
def toFixedHom {V : Type u} {v₀ : V}
    {L M : LensRealization V v₀}
    (f : ofLensRealization L ⟶ ofLensRealization M)
    (hv : f.view = id) : L ⟶ M where
  toFun := f.state
  get_naturality c := by
    have he := f.get_comm c
    simpa [hv] using he
  put_naturality c v := by
    have he := f.put_comm c v
    simpa [hv] using he

theorem toFixedHom_ofFixedHom {V : Type u} {v₀ : V}
    {L M : LensRealization V v₀} (f : L ⟶ M) :
    toFixedHom (ofFixedHom f) rfl = f := by
  apply LensRealization.Hom.ext
  rfl

end GeneralLens

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
