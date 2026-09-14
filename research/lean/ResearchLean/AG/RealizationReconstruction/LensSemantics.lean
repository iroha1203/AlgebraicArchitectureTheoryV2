import Mathlib.CategoryTheory.Idempotents.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Total-lens semantics and generator restriction

This module begins G-123(A,B,E) with the independently specified category of
total very-well-behaved lenses over a fixed view type and reference view.  Its
morphisms are all functions preserving both `get` and `put`; in particular,
they are not restricted to equivalences or to maps already represented by a
decoder.

## Implementation notes

Lens data and the semantic laws are separate declarations.  The finite
reference fiber is the only finiteness condition on an object.  Restriction is
evaluation on that fiber, while extension is constructed from `put`; neither
existence nor uniqueness of an extension is stored in the generator-map type.
The product model is introduced as a construction, not as the definition of a
semantic lens.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- Raw total-lens data over a view type `V`. -/
structure LensData (V : Type u) where
  /-- Concrete states. -/
  Carrier : Type u
  /-- The visible value of a state. -/
  get : Carrier → V
  /-- Updating a state to a requested visible value. -/
  put : Carrier → V → Carrier

/-- The three total-lens laws together with finiteness of the reference fiber. -/
structure IsTotalLens {V : Type u} (v₀ : V) (L : LensData V) : Prop where
  /-- Updating with the current view changes nothing. -/
  put_get : ∀ c, L.put c (L.get c) = c
  /-- Reading after an update returns the requested view. -/
  get_put : ∀ c v, L.get (L.put c v) = v
  /-- Only the last requested view matters. -/
  put_put : ∀ c v w, L.put (L.put c v) w = L.put c w
  /-- The complement over the selected view is finite. -/
  finite_fiber : Finite {c : L.Carrier // L.get c = v₀}

/-- A semantic lens is raw lens data satisfying the independent condition `IsTotalLens`. -/
structure LensRealization (V : Type u) (v₀ : V) where
  /-- The independently specified state, read, and update data. -/
  toLensData : LensData V
  /-- The semantic laws and finite-reference-fiber condition. -/
  condition : IsTotalLens v₀ toLensData

namespace LensRealization

variable {V : Type u} {v₀ : V}

/-- The carrier of a semantic lens. -/
abbrev Carrier (L : LensRealization V v₀) := L.toLensData.Carrier

/-- The get operation of a semantic lens. -/
abbrev get (L : LensRealization V v₀) := L.toLensData.get

/-- The put operation of a semantic lens. -/
abbrev put (L : LensRealization V v₀) := L.toLensData.put

/-- The finite generator carried by a lens: its fiber over `v₀`. -/
abbrev Fiber (L : LensRealization V v₀) := {c : L.Carrier // L.get c = v₀}

instance (L : LensRealization V v₀) : Finite L.Fiber := L.condition.finite_fiber

/-- A lens morphism preserves both `get` and `put`. -/
@[ext]
structure Hom (L M : LensRealization V v₀) where
  /-- The map on all states. -/
  toFun : L.Carrier → M.Carrier
  /-- Preservation of reads. -/
  get_naturality : ∀ c, M.get (toFun c) = L.get c
  /-- Preservation of updates. -/
  put_naturality : ∀ c v, toFun (L.put c v) = M.put (toFun c) v

instance : Category (LensRealization V v₀) where
  Hom := Hom
  id L :=
    { toFun := id
      get_naturality := fun _ => rfl
      put_naturality := fun _ _ => rfl }
  comp f g :=
    { toFun := g.toFun ∘ f.toFun
      get_naturality := fun c => by
        simpa only [Function.comp_apply] using
          (g.get_naturality (f.toFun c)).trans (f.get_naturality c)
      put_naturality := fun c v => by
        rw [Function.comp_apply, f.put_naturality, g.put_naturality]
        rfl }
  id_comp := by
    intro X Y f
    ext c
    rfl
  comp_id := by
    intro X Y f
    ext c
    rfl
  assoc := by
    intro W X Y Z f g h
    ext c
    rfl

instance {L M : LensRealization V v₀} : CoeFun (L ⟶ M) (fun _ => L.Carrier → M.Carrier) :=
  ⟨Hom.toFun⟩

/-- Restrict a complete lens morphism to the finite reference fiber. -/
def res {L M : LensRealization V v₀} (h : L ⟶ M) : L.Fiber → M.Fiber :=
  fun c => ⟨h c, (h.get_naturality c).trans c.property⟩

/-- Extend a map of reference fibers to a complete state map using `put`. -/
def ext {L M : LensRealization V v₀} (t : L.Fiber → M.Fiber) : L ⟶ M where
  toFun c := M.put (t ⟨L.put c v₀, L.condition.get_put c v₀⟩) (L.get c)
  get_naturality c := M.condition.get_put _ _
  put_naturality c v := by
    change M.put
        (t ⟨L.put (L.put c v) v₀, L.condition.get_put (L.put c v) v₀⟩)
        (L.get (L.put c v)) =
      M.put (M.put (t ⟨L.put c v₀, L.condition.get_put c v₀⟩) (L.get c)) v
    have hsource :
        (⟨L.put (L.put c v) v₀, L.condition.get_put (L.put c v) v₀⟩ : L.Fiber) =
          ⟨L.put c v₀, L.condition.get_put c v₀⟩ := by
      apply Subtype.ext
      exact L.condition.put_put c v v₀
    rw [hsource]
    calc
      M.put (t ⟨L.put c v₀, _⟩) (L.get (L.put c v)) =
          M.put (t ⟨L.put c v₀, _⟩) v := by
            exact congrArg (M.put (t ⟨L.put c v₀, _⟩))
              (L.condition.get_put c v)
      _ = M.put (M.put (t ⟨L.put c v₀, _⟩) (L.get c)) v :=
        (M.condition.put_put _ (L.get c) v).symm

/-- Restriction after extension is the original finite generator map. -/
@[simp]
theorem res_ext {L M : LensRealization V v₀} (t : L.Fiber → M.Fiber) :
    res (ext t) = t := by
  funext c
  apply Subtype.ext
  change M.put (t ⟨L.put c v₀, _⟩) (L.get c) = (t c).1
  have hsource : (⟨L.put c v₀, L.condition.get_put c v₀⟩ : L.Fiber) = c := by
    apply Subtype.ext
    calc
      L.put c v₀ = L.put c (L.get c) := congrArg (L.put c) c.property.symm
      _ = c := L.condition.put_get c
  rw [hsource]
  calc
    M.put (t c) (L.get c) = M.put (t c) v₀ :=
      congrArg (M.put (t c)) c.property
    _ = M.put (t c) (M.get (t c)) :=
      congrArg (M.put (t c)) (t c).property.symm
    _ = t c := M.condition.put_get (t c)

/-- Extension after restriction is the original complete lens morphism. -/
@[simp]
theorem ext_res {L M : LensRealization V v₀} (h : L ⟶ M) :
    ext (res h) = h := by
  apply Hom.ext
  funext c
  change M.put (h (L.put c v₀)) (L.get c) = h c
  rw [h.put_naturality]
  calc
    M.put (M.put (h c) v₀) (L.get c) = M.put (h c) (L.get c) :=
      M.condition.put_put (h c) v₀ (L.get c)
    _ = M.put (h c) (M.get (h c)) :=
      congrArg (M.put (h c)) (h.get_naturality c).symm
    _ = h c := M.condition.put_get (h c)

/-- Complete lens morphisms are in bijection with maps of finite reference fibers. -/
def homEquivFiberMap (L M : LensRealization V v₀) :
    (L ⟶ M) ≃ (L.Fiber → M.Fiber) where
  toFun := res
  invFun := ext
  left_inv := ext_res
  right_inv := res_ext

/-- Restriction sends the identity morphism to the identity fiber map. -/
@[simp]
theorem res_id (L : LensRealization V v₀) : res (𝟙 L) = id := by
  funext c
  apply Subtype.ext
  rfl

/-- Restriction sends composition to composition of finite fiber maps. -/
@[simp]
theorem res_comp {L M N : LensRealization V v₀} (f : L ⟶ M) (g : M ⟶ N) :
    res (f ≫ g) = res g ∘ res f := by
  funext c
  apply Subtype.ext
  rfl

/-- Extension is compatible with composition of generator maps. -/
theorem ext_comp {L M N : LensRealization V v₀}
    (f : L.Fiber → M.Fiber) (g : M.Fiber → N.Fiber) :
    ext f ≫ ext g = ext (g ∘ f) := by
  apply (homEquivFiberMap L N).injective
  change res (ext f ≫ ext g) = res (ext (g ∘ f))
  rw [res_comp, res_ext, res_ext, res_ext]

/-- Raw product-lens data with complement `K`. -/
def productData (V K : Type u) : LensData V where
  Carrier := V × K
  get := Prod.fst
  put := fun (_, k) v => (v, k)

/-- The reference fiber of a product lens is equivalent to its complement. -/
def productFiberEquiv (V K : Type u) (v₀ : V) :
    {c : (productData V K).Carrier // (productData V K).get c = v₀} ≃ K where
  toFun c := c.1.2
  invFun k := ⟨(v₀, k), rfl⟩
  left_inv c := by
    apply Subtype.ext
    cases c with
    | mk c hc =>
      cases c with
      | mk v k =>
        simp only [productData] at hc ⊢
        subst v
        rfl
  right_inv _ := rfl

/-- The product construction satisfies the total-lens condition for finite `K`. -/
def productCondition (V K : Type u) (v₀ : V) [Finite K] :
    IsTotalLens v₀ (productData V K) where
  put_get c := by cases c; rfl
  get_put _ _ := rfl
  put_put c _ _ := by cases c; rfl
  finite_fiber := Finite.of_equiv K (productFiberEquiv V K v₀).symm

/-- The product lens used by the finite decoder. -/
def product (V K : Type u) (v₀ : V) [Finite K] : LensRealization V v₀ where
  toLensData := productData V K
  condition := productCondition V K v₀

/-- The product lens is a positive instance of the semantic condition. -/
theorem product_isTotalLens (V K : Type u) (v₀ : V) [Finite K] :
    IsTotalLens v₀ (productData V K) :=
  productCondition V K v₀

/-- A raw Bool lens that ignores the requested view. -/
def ignoredUpdateData : LensData Bool where
  Carrier := Bool
  get := id
  put := fun c _ => c

/-- The ignored-update data is a negative instance of the semantic condition. -/
theorem ignoredUpdateData_not_isTotalLens :
    ¬ IsTotalLens false ignoredUpdateData := by
  intro h
  have hfalse := h.get_put false true
  exact Bool.noConfusion hfalse

end LensRealization

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
