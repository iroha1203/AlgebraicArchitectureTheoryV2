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

/-- Raw total-lens data over a view type `V`.

This is the independent semantic input of G-123(E), n1015 (L1); it contains no
presentation, decoder, or reconstruction certificate. -/
structure LensData (V : Type u) where
  /-- The concrete state carrier supplied by the n1015 (L1) semantic input. -/
  Carrier : Type u
  /-- The n1015 (L1) read operation supplied by the semantic input. -/
  get : Carrier → V
  /-- The n1015 (L1) update operation supplied by the semantic input. -/
  put : Carrier → V → Carrier

/-- The three total-lens laws together with finiteness of the reference fiber.

These are exactly the object-side premises of G-123(E), n1015 (L1).  The
finiteness premise concerns only the fiber over the fixed reference view. -/
structure IsTotalLens {V : Type u} (v₀ : V) (L : LensData V) : Prop where
  /-- The `put_get` object premise in n1015 (L1). -/
  put_get : ∀ c, L.put c (L.get c) = c
  /-- The `get_put` object premise in n1015 (L1). -/
  get_put : ∀ c v, L.get (L.put c v) = v
  /-- The `put_put` object premise in n1015 (L1). -/
  put_put : ∀ c v w, L.put (L.put c v) w = L.put c w
  /-- The finite-reference-fiber object premise in n1015 (L1). -/
  finite_fiber : Finite {c : L.Carrier // L.get c = v₀}

/-- A semantic lens is raw lens data satisfying the independent condition `IsTotalLens`.

This is the object type of the independently defined category in G-123(A,E),
not the image or essential image of a decoder. -/
structure LensRealization (V : Type u) (v₀ : V) where
  /-- The independently specified G-123(E) state, read, and update data. -/
  toLensData : LensData V
  /-- The n1015 (L1) semantic laws and finite-reference-fiber condition. -/
  condition : IsTotalLens v₀ toLensData

namespace LensRealization

variable {V : Type u} {v₀ : V}

/-- API projection for the G-123(A,E) independent semantic object; its source is
the `LensData` input of n1015 (L1). -/
abbrev Carrier (L : LensRealization V v₀) := L.toLensData.Carrier

/-- API projection for the n1015 (L1) `get` input of a semantic object. -/
abbrev get (L : LensRealization V v₀) := L.toLensData.get

/-- API projection for the n1015 (L1) `put` input of a semantic object. -/
abbrev put (L : LensRealization V v₀) := L.toLensData.put

/-- The finite generator carried by a lens: its fiber over `v₀`.

This is the complement `K_L` of n1015 (L3)--(L4). -/
abbrev Fiber (L : LensRealization V v₀) := {c : L.Carrier // L.get c = v₀}

/-- The reference fiber is finite by the object premise in n1015 (L1). -/
instance (L : LensRealization V v₀) : Finite L.Fiber := L.condition.finite_fiber

/-- A lens morphism preserves both `get` and `put`.

This is the complete, independently specified morphism class of G-123(E),
n1015 (L2); no invertibility or representability premise is imposed. -/
@[ext]
structure Hom (L M : LensRealization V v₀) where
  /-- The complete state map required by n1015 (L2). -/
  toFun : L.Carrier → M.Carrier
  /-- The `get`-preservation premise defining an n1015 (L2) morphism. -/
  get_naturality : ∀ c, M.get (toFun c) = L.get c
  /-- The `put`-preservation premise defining an n1015 (L2) morphism. -/
  put_naturality : ∀ c v, toFun (L.put c v) = M.put (toFun c) v

/-- The category required by G-123(A,E), with identities and composition on all
get/put-preserving maps from n1015 (L2). -/
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

/-- A semantic morphism acts on every state; this is the complete map used in
the G-123(B0) restriction and extension equations. -/
instance {L M : LensRealization V v₀} : CoeFun (L ⟶ M) (fun _ => L.Carrier → M.Carrier) :=
  ⟨Hom.toFun⟩

/-- Restrict a complete lens morphism to the finite reference fiber.

This is `res` in G-123(B0), n1015 (L3); its only premise is an arbitrary
get/put-preserving morphism from the independent semantic category. -/
def res {L M : LensRealization V v₀} (h : L ⟶ M) : L.Fiber → M.Fiber :=
  fun c => ⟨h c, (h.get_naturality c).trans c.property⟩

/-- Extend a map of reference fibers to a complete state map using `put`.

This is the constructed `ext` of G-123(B0), n1015 (L3).  Existence and the
preservation laws are derived from the lens laws rather than stored in `t`. -/
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

/-- API inverse law for G-123(B0): restriction after the constructed extension
is the original fiber map; it uses the n1015 (L1) laws. -/
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

/-- API inverse law for G-123(B0): extension after restriction is the original
complete morphism; it uses both n1015 (L1) laws and (L2) naturality. -/
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

/-- Complete lens morphisms are in bijection with maps of finite reference fibers.

This is the endpointwise G-123(B0) reconstruction theorem for the lens family,
assembled from the separately proved `res_ext` and `ext_res` equations. -/
def homEquivFiberMap (L M : LensRealization V v₀) :
    (L ⟶ M) ≃ (L.Fiber → M.Fiber) where
  toFun := res
  invFun := ext
  left_inv := ext_res
  right_inv := res_ext

/-- Functoriality API for G-123(B0): `res` sends the semantic identity to the
identity fiber map, with no premise beyond the category definition. -/
@[simp]
theorem res_id (L : LensRealization V v₀) : res (𝟙 L) = id := by
  funext c
  apply Subtype.ext
  rfl

/-- Functoriality API for G-123(B0): `res` sends semantic composition to
composition of fiber maps, using the n1015 (L2) morphism representation. -/
@[simp]
theorem res_comp {L M N : LensRealization V v₀} (f : L ⟶ M) (g : M ⟶ N) :
    res (f ≫ g) = res g ∘ res f := by
  funext c
  apply Subtype.ext
  rfl

/-- Functoriality API for G-123(B0): the constructed `ext` preserves composition;
the proof uses the previously discharged `res`/`ext` inverse laws. -/
theorem ext_comp {L M N : LensRealization V v₀}
    (f : L.Fiber → M.Fiber) (g : M.Fiber → N.Fiber) :
    ext f ≫ ext g = ext (g ∘ f) := by
  apply (homEquivFiberMap L N).injective
  change res (ext f ≫ ext g) = res (ext (g ∘ f))
  rw [res_comp, res_ext, res_ext, res_ext]

/-- Raw product-lens data with complement `K`.

This is the explicit construction used in n1015 (L4), not the definition of
the independent semantic category. -/
def productData (V K : Type u) : LensData V where
  Carrier := V × K
  get := Prod.fst
  put := fun (_, k) v => (v, k)

/-- The reference fiber of a product lens is equivalent to its complement.

This identifies the decoder generator with its finite complement in G-123(E). -/
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

/-- The product construction satisfies the total-lens condition for finite `K`.

This discharges the n1015 (L1) object premises for the decoder construction. -/
def productCondition (V K : Type u) (v₀ : V) [Finite K] :
    IsTotalLens v₀ (productData V K) where
  put_get c := by cases c; rfl
  get_put _ _ := rfl
  put_put c _ _ := by cases c; rfl
  finite_fiber := Finite.of_equiv K (productFiberEquiv V K v₀).symm

/-- The product lens used by the finite decoder.

This is the constructed object map for G-123(E); it does not define semantic
objects by decoder membership. -/
def product (V K : Type u) (v₀ : V) [Finite K] : LensRealization V v₀ where
  toLensData := productData V K
  condition := productCondition V K v₀

/-- An equivalence of complements induces an isomorphism of product lenses.

This is the finite-enumeration transport used to connect the exact n1015 (L4)
normal form with the finite decoder of G-123(E). -/
def productIsoOfEquiv (V : Type u) (v₀ : V) {K K' : Type u}
    [Finite K] [Finite K'] (e : K ≃ K') :
    product V K v₀ ≅ product V K' v₀ where
  hom :=
    { toFun := fun c => (c.1, e c.2)
      get_naturality := fun _ => rfl
      put_naturality := fun _ _ => rfl }
  inv :=
    { toFun := fun c => (c.1, e.symm c.2)
      get_naturality := fun _ => rfl
      put_naturality := fun _ _ => rfl }
  hom_inv_id := by
    apply Hom.ext
    funext c
    exact Prod.ext rfl (e.symm_apply_apply c.2)
  inv_hom_id := by
    apply Hom.ext
    funext c
    exact Prod.ext rfl (e.apply_symm_apply c.2)

/-- The canonical carrier equivalence `c ↦ (get c, put c v₀)` of n1015 (L4).

Its inverse is constructed as `(v,k) ↦ put k v`; neither direction is supplied
as input or chosen from a finite enumeration. -/
def canonicalNormalFormEquiv (L : LensRealization V v₀) :
    L.Carrier ≃ V × L.Fiber where
  toFun c := (L.get c, ⟨L.put c v₀, L.condition.get_put c v₀⟩)
  invFun vk := L.put vk.2 vk.1
  left_inv c := by
    change L.put (L.put c v₀) (L.get c) = c
    calc
      L.put (L.put c v₀) (L.get c) = L.put c (L.get c) :=
        L.condition.put_put c v₀ (L.get c)
      _ = c := L.condition.put_get c
  right_inv vk := by
    apply Prod.ext
    · exact L.condition.get_put vk.2 vk.1
    · apply Subtype.ext
      change L.put (L.put vk.2 vk.1) v₀ = vk.2
      calc
        L.put (L.put vk.2 vk.1) v₀ = L.put vk.2 v₀ :=
          L.condition.put_put vk.2 vk.1 v₀
        _ = L.put vk.2 (L.get vk.2) :=
          congrArg (L.put vk.2) vk.2.property.symm
        _ = vk.2 := L.condition.put_get vk.2

/-- The visible component of the canonical n1015 (L4) equivalence is `get`. -/
@[simp]
theorem canonicalNormalFormEquiv_fst (L : LensRealization V v₀) (c : L.Carrier) :
    (canonicalNormalFormEquiv L c).1 = L.get c := rfl

/-- The complement component of the canonical n1015 (L4) equivalence is
`put c v₀`, regarded as an element of the reference fiber. -/
@[simp]
theorem canonicalNormalFormEquiv_snd (L : LensRealization V v₀) (c : L.Carrier) :
    (canonicalNormalFormEquiv L c).2 =
      (⟨L.put c v₀, L.condition.get_put c v₀⟩ : L.Fiber) := rfl

/-- The inverse of the canonical n1015 (L4) equivalence is `(v,k) ↦ put k v`. -/
@[simp]
theorem canonicalNormalFormEquiv_symm_apply (L : LensRealization V v₀)
    (vk : V × L.Fiber) :
    (canonicalNormalFormEquiv L).symm vk = L.put vk.2 vk.1 := rfl

/-- The exact canonical lens isomorphism required by n1015 (L4).

It upgrades `canonicalNormalFormEquiv` to the independent semantic category;
the only premises used are the n1015 (L1) lens laws and finite reference fiber. -/
def canonicalNormalFormIso (L : LensRealization V v₀) :
    L ≅ product V L.Fiber v₀ where
  hom :=
    { toFun := canonicalNormalFormEquiv L
      get_naturality := fun _ => rfl
      put_naturality := fun c v => by
        apply Prod.ext
        · exact L.condition.get_put c v
        · apply Subtype.ext
          exact L.condition.put_put c v v₀ }
  inv :=
    { toFun := (canonicalNormalFormEquiv L).symm
      get_naturality := fun vk => L.condition.get_put vk.2 vk.1
      put_naturality := fun vk v => by
        change L.put vk.2 v = L.put (L.put vk.2 vk.1) v
        exact (L.condition.put_put vk.2 vk.1 v).symm }
  hom_inv_id := by
    apply Hom.ext
    funext c
    exact (canonicalNormalFormEquiv L).symm_apply_apply c
  inv_hom_id := by
    apply Hom.ext
    funext vk
    exact (canonicalNormalFormEquiv L).apply_symm_apply vk

/-- No-unfold API for the forward map of the main n1015 (L4) isomorphism; it
records both the visible and complement components required by G-123(E). -/
@[simp]
theorem canonicalNormalFormIso_hom_apply (L : LensRealization V v₀)
    (c : L.Carrier) :
    (canonicalNormalFormIso L).hom c =
      (L.get c, ⟨L.put c v₀, L.condition.get_put c v₀⟩) := rfl

/-- No-unfold API for the inverse map of the main n1015 (L4) isomorphism; the
state is reconstructed by the original lens update operation. -/
@[simp]
theorem canonicalNormalFormIso_inv_apply (L : LensRealization V v₀)
    (vk : V × L.Fiber) :
    (canonicalNormalFormIso L).inv vk = L.put vk.2 vk.1 := rfl

/-- Positive-instance theorem required by the predicate check for n1015 (L1);
the finite complement premise supplies precisely the required finite fiber. -/
theorem product_isTotalLens (V K : Type u) (v₀ : V) [Finite K] :
    IsTotalLens v₀ (productData V K) :=
  productCondition V K v₀

/-- Negative-test data for the n1015 (L1) predicate; its update ignores the
requested view and therefore is not used as a decoder object. -/
def ignoredUpdateData : LensData Bool where
  Carrier := Bool
  get := id
  put := fun c _ => c

/-- Negative-instance theorem for n1015 (L1): the independent predicate rejects
data violating `get_put`, preventing a vacuous semantic object condition. -/
theorem ignoredUpdateData_not_isTotalLens :
    ¬ IsTotalLens false ignoredUpdateData := by
  intro h
  have hfalse := h.get_put false true
  exact Bool.noConfusion hfalse

end LensRealization

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
