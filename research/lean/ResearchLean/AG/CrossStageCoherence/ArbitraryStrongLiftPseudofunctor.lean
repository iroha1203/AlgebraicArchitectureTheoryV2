import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Transport pseudofunctor from arbitrary selected strong lifts

For an arbitrary functor `r : E ⥤ B`, this module formalizes Constructions
4.13--4.14 and Theorem 4.15 of the fixed Rising Sea manuscript.  Given only a
choice of a target and a strongly cocartesian lift for every base arrow and
fiber object, it constructs the induced functor on fibers, the compositor in
the manuscript's direction, the unitor, and their associativity and unit laws.

## Implementation notes

`StrongLiftSelection` contains only the selected target and lift data.  The
strongly cocartesian property is kept as a separate hypothesis, so the data
structure does not store any conclusion or coherence law.  In particular,
the action on vertical morphisms, functor laws, naturality, compositor,
unitor, and all coherence equations are derived from universal-property
uniqueness.

The manuscript's compositor points from iterated transport to direct
transport.  Existing AAT core and geometry compositors use the inverse
orientation; the connection declarations at the end of this module record
that relationship explicitly rather than silently changing the fixed claim.
-/

namespace AAT.AG.CrossStageCoherence

universe u₁ u₂ v₁ v₂

open CategoryTheory
open AtomFoundation
open GeometryTransport

set_option maxHeartbeats 2000000

/-- Target objects and lift arrows selected over every base arrow. -/
structure StrongLiftSelection
    {E : Type u₁} {B : Type u₂}
    [Category.{v₁} E] [Category.{v₂} B] (r : E ⥤ B) where
  obj : ∀ {b b' : B}, (σ : b ⟶ b') → r.Fiber b → r.Fiber b'
  lift : ∀ {b b' : B} (σ : b ⟶ b') (X : r.Fiber b),
    X.1 ⟶ (obj σ X).1

namespace StrongLiftSelection

variable {E : Type u₁} {B : Type u₂}
variable [Category.{v₁} E] [Category.{v₂} B]
variable {r : E ⥤ B} (L : StrongLiftSelection r)
variable (hL : ∀ {b b' : B} (σ : b ⟶ b') (X : r.Fiber b),
  r.IsStronglyCocartesian σ (L.lift σ X))

/-- Transport a vertical arrow by the selected strong lift's universal property. -/
noncomputable def map {b b' : B} (σ : b ⟶ b')
    {X Y : r.Fiber b} (f : X ⟶ Y) : L.obj σ X ⟶ L.obj σ Y := by
  letI : r.IsStronglyCocartesian σ (L.lift σ X) := hL σ X
  letI : r.IsHomLift (𝟙 b) f.1 := f.2
  letI : r.IsHomLift σ (L.lift σ Y) := (hL σ Y).toIsHomLift
  letI : r.IsHomLift σ (f.1 ≫ L.lift σ Y) := by
    simpa using inferInstanceAs
      (r.IsHomLift ((𝟙 b) ≫ σ) (f.1 ≫ L.lift σ Y))
  exact ⟨CategoryTheory.Functor.IsStronglyCocartesian.map
      r σ (L.lift σ X) (g := 𝟙 b') (f' := σ)
      (Category.comp_id σ).symm (f.1 ≫ L.lift σ Y), inferInstance⟩

/-- Characterizing equation for the transported vertical arrow (Construction 4.13). -/
@[reassoc]
theorem lift_map {b b' : B} (σ : b ⟶ b')
    {X Y : r.Fiber b} (f : X ⟶ Y) :
    L.lift σ X ≫ (L.map hL σ f).1 = f.1 ≫ L.lift σ Y := by
  letI : r.IsStronglyCocartesian σ (L.lift σ X) := hL σ X
  letI : r.IsHomLift (𝟙 b) f.1 := f.2
  letI : r.IsHomLift σ (L.lift σ Y) := (hL σ Y).toIsHomLift
  letI : r.IsHomLift σ (f.1 ≫ L.lift σ Y) := by
    simpa using inferInstanceAs
      (r.IsHomLift ((𝟙 b) ≫ σ) (f.1 ≫ L.lift σ Y))
  exact CategoryTheory.Functor.IsStronglyCocartesian.fac
    r σ (L.lift σ X) (Category.comp_id σ).symm
      (f.1 ≫ L.lift σ Y)

/-- Transport by selected strong lifts preserves identity arrows. -/
theorem map_id {b b' : B} (σ : b ⟶ b') (X : r.Fiber b) :
    L.map hL σ (𝟙 X) = 𝟙 (L.obj σ X) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : r.IsStronglyCocartesian σ (L.lift σ X) := hL σ X
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r σ (L.lift σ X) (𝟙 b')
  change L.lift σ X ≫ (L.map hL σ (𝟙 X)).1 =
    L.lift σ X ≫ 𝟙 (L.obj σ X).1
  calc
    _ = ((𝟙 X : X ⟶ X)).1 ≫ L.lift σ X :=
      L.lift_map hL σ (𝟙 X)
    _ = L.lift σ X := Category.id_comp _
    _ = _ := (Category.comp_id _).symm

/-- Transport by selected strong lifts preserves composition. -/
theorem map_comp {b b' : B} (σ : b ⟶ b')
    {X Y Z : r.Fiber b} (f : X ⟶ Y) (g : Y ⟶ Z) :
    L.map hL σ (f ≫ g) = L.map hL σ f ≫ L.map hL σ g := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : r.IsStronglyCocartesian σ (L.lift σ X) := hL σ X
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r σ (L.lift σ X) (𝟙 b')
  change L.lift σ X ≫ (L.map hL σ (f ≫ g)).1 =
    L.lift σ X ≫ ((L.map hL σ f).1 ≫ (L.map hL σ g).1)
  calc
    _ = (f ≫ g).1 ≫ L.lift σ Z := L.lift_map hL σ (f ≫ g)
    _ = f.1 ≫ (g.1 ≫ L.lift σ Z) := Category.assoc _ _ _
    _ = f.1 ≫ (L.lift σ Y ≫ (L.map hL σ g).1) :=
      congrArg (fun k => f.1 ≫ k) (L.lift_map hL σ g).symm
    _ = (f.1 ≫ L.lift σ Y) ≫ (L.map hL σ g).1 :=
      (Category.assoc _ _ _).symm
    _ = (L.lift σ X ≫ (L.map hL σ f).1) ≫
        (L.map hL σ g).1 :=
      congrArg (fun k => k ≫ (L.map hL σ g).1)
        (L.lift_map hL σ f).symm
    _ = _ := Category.assoc _ _ _

/-- The fiber transport functor determined by the selected strong lifts. -/
noncomputable def transport {b b' : B} (σ : b ⟶ b') :
    r.Fiber b ⥤ r.Fiber b' where
  obj := L.obj σ
  map := L.map hL σ
  map_id := L.map_id hL σ
  map_comp := L.map_comp hL σ

/-- The selected two-step lift over a composite base arrow. -/
noncomputable def iteratedLift {b₀ b₁ b₂ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (X : r.Fiber b₀) :
    X.1 ⟶ ((L.transport hL τ).obj ((L.transport hL σ).obj X)).1 :=
  L.lift σ X ≫ L.lift τ ((L.transport hL σ).obj X)

/-- A composite of two selected strong lifts is strong over the composite arrow. -/
theorem iteratedLift_isStronglyCocartesian {b₀ b₁ b₂ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (X : r.Fiber b₀) :
    r.IsStronglyCocartesian (σ ≫ τ) (L.iteratedLift hL σ τ X) := by
  letI : r.IsStronglyCocartesian σ (L.lift σ X) := hL σ X
  letI : r.IsStronglyCocartesian τ
      (L.lift τ ((L.transport hL σ).obj X)) :=
    hL τ ((L.transport hL σ).obj X)
  exact CategoryTheory.Functor.IsStronglyCocartesian.comp r

/-- The selected two-step lift transports a vertical arrow to the iterated map. -/
theorem iteratedLift_map {b₀ b₁ b₂ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂)
    {X Y : r.Fiber b₀} (f : X ⟶ Y) :
    L.iteratedLift hL σ τ X ≫
        ((L.transport hL σ ⋙ L.transport hL τ).map f).1 =
      f.1 ≫ L.iteratedLift hL σ τ Y := by
  change (L.lift σ X ≫ L.lift τ ((L.transport hL σ).obj X)) ≫
      (L.map hL τ (L.map hL σ f)).1 =
    f.1 ≫ (L.lift σ Y ≫ L.lift τ ((L.transport hL σ).obj Y))
  calc
    _ = L.lift σ X ≫
        (L.lift τ ((L.transport hL σ).obj X) ≫
          (L.map hL τ (L.map hL σ f)).1) := Category.assoc _ _ _
    _ = L.lift σ X ≫
        ((L.map hL σ f).1 ≫
          L.lift τ ((L.transport hL σ).obj Y)) := by
      rw [show L.lift τ ((L.transport hL σ).obj X) ≫
          (L.map hL τ (L.map hL σ f)).1 =
        (L.map hL σ f).1 ≫
          L.lift τ ((L.transport hL σ).obj Y) by
        simpa only [transport] using L.lift_map hL τ (L.map hL σ f)]
    _ = (L.lift σ X ≫ (L.map hL σ f).1) ≫
        L.lift τ ((L.transport hL σ).obj Y) :=
      (Category.assoc _ _ _).symm
    _ = (f.1 ≫ L.lift σ Y) ≫
        L.lift τ ((L.transport hL σ).obj Y) := by
      rw [L.lift_map]
    _ = _ := Category.assoc _ _ _

/-- The manuscript-oriented compositor component, from iterated to direct transport. -/
noncomputable def compositorApp {b₀ b₁ b₂ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (X : r.Fiber b₀) :
    (L.transport hL τ).obj ((L.transport hL σ).obj X) ≅
      (L.transport hL (σ ≫ τ)).obj X := by
  letI : r.IsStronglyCocartesian (σ ≫ τ)
      (L.iteratedLift hL σ τ X) :=
    L.iteratedLift_isStronglyCocartesian hL σ τ X
  letI : r.IsStronglyCocartesian (σ ≫ τ) (L.lift (σ ≫ τ) X) :=
    hL (σ ≫ τ) X
  exact strongLiftComparisonIso r (σ ≫ τ)
    (L.iteratedLift hL σ τ X) (L.lift (σ ≫ τ) X)

/-- The compositor factors the iterated lift as the selected direct lift (4.14). -/
@[reassoc]
theorem iteratedLift_compositorApp {b₀ b₁ b₂ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (X : r.Fiber b₀) :
    L.iteratedLift hL σ τ X ≫ (L.compositorApp hL σ τ X).hom.1 =
      L.lift (σ ≫ τ) X := by
  letI : r.IsStronglyCocartesian (σ ≫ τ)
      (L.iteratedLift hL σ τ X) :=
    L.iteratedLift_isStronglyCocartesian hL σ τ X
  letI : r.IsStronglyCocartesian (σ ≫ τ) (L.lift (σ ≫ τ) X) :=
    hL (σ ≫ τ) X
  exact strongLiftComparisonHom_fac r (σ ≫ τ)
    (L.iteratedLift hL σ τ X) (L.lift (σ ≫ τ) X)

/-- The manuscript-oriented compositor is natural on vertical arrows. -/
theorem compositor_naturality {b₀ b₁ b₂ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂)
    {X Y : r.Fiber b₀} (f : X ⟶ Y) :
    (L.transport hL σ ⋙ L.transport hL τ).map f ≫
        (L.compositorApp hL σ τ Y).hom =
      (L.compositorApp hL σ τ X).hom ≫
        (L.transport hL (σ ≫ τ)).map f := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : r.IsStronglyCocartesian (σ ≫ τ)
      (L.iteratedLift hL σ τ X) :=
    L.iteratedLift_isStronglyCocartesian hL σ τ X
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r (σ ≫ τ) (L.iteratedLift hL σ τ X) (𝟙 b₂)
  change L.iteratedLift hL σ τ X ≫
      ((L.map hL τ (L.map hL σ f)).1 ≫
        (L.compositorApp hL σ τ Y).hom.1) =
    L.iteratedLift hL σ τ X ≫
      ((L.compositorApp hL σ τ X).hom.1 ≫
        (L.map hL (σ ≫ τ) f).1)
  calc
    _ = (L.iteratedLift hL σ τ X ≫
        (L.map hL τ (L.map hL σ f)).1) ≫
          (L.compositorApp hL σ τ Y).hom.1 :=
      (Category.assoc _ _ _).symm
    _ = (f.1 ≫ L.iteratedLift hL σ τ Y) ≫
          (L.compositorApp hL σ τ Y).hom.1 := by
      rw [show L.iteratedLift hL σ τ X ≫
          (L.map hL τ (L.map hL σ f)).1 =
        f.1 ≫ L.iteratedLift hL σ τ Y by
        simpa only [transport] using L.iteratedLift_map hL σ τ f]
    _ = f.1 ≫ (L.iteratedLift hL σ τ Y ≫
          (L.compositorApp hL σ τ Y).hom.1) := Category.assoc _ _ _
    _ = f.1 ≫ L.lift (σ ≫ τ) Y := by
      rw [L.iteratedLift_compositorApp]
    _ = L.lift (σ ≫ τ) X ≫ (L.map hL (σ ≫ τ) f).1 :=
      (L.lift_map hL (σ ≫ τ) f).symm
    _ = (L.iteratedLift hL σ τ X ≫
          (L.compositorApp hL σ τ X).hom.1) ≫
        (L.map hL (σ ≫ τ) f).1 := by
      rw [L.iteratedLift_compositorApp]
    _ = _ := Category.assoc _ _ _

/-- The natural compositor of transport, oriented as in Construction 4.14. -/
noncomputable def compositor {b₀ b₁ b₂ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) :
    L.transport hL σ ⋙ L.transport hL τ ≅
      L.transport hL (σ ≫ τ) :=
  NatIso.ofComponents (L.compositorApp hL σ τ)
    (fun f => L.compositor_naturality hL σ τ f)

/-- The identity arrow on a fiber object, viewed as the comparison identity lift. -/
noncomputable def identityLift (b : B) (X : r.Fiber b) : X.1 ⟶ X.1 :=
  𝟙 X.1

/-- The identity comparison lift is strongly cocartesian over the identity. -/
theorem identityLift_isStronglyCocartesian (b : B) (X : r.Fiber b) :
    r.IsStronglyCocartesian (𝟙 b) (identityLift (r := r) b X) := by
  letI : r.IsHomLift (𝟙 b) (identityLift (r := r) b X) :=
    CategoryTheory.IsHomLift.id X.2
  letI : IsIso (identityLift (r := r) b X) := by
    change IsIso (𝟙 X.1)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    r (𝟙 b) (identityLift (r := r) b X)

/-- The unitor component generated by uniqueness of the selected identity lift. -/
noncomputable def unitorApp (b : B) (X : r.Fiber b) :
    (L.transport hL (𝟙 b)).obj X ≅ X := by
  letI : r.IsStronglyCocartesian (𝟙 b) (L.lift (𝟙 b) X) := hL (𝟙 b) X
  letI : r.IsStronglyCocartesian (𝟙 b)
      (identityLift (r := r) b X) :=
    identityLift_isStronglyCocartesian (r := r) b X
  exact strongLiftComparisonIso r (𝟙 b)
    (L.lift (𝟙 b) X) (identityLift (r := r) b X)

/-- The unitor factors the selected identity lift as the identity arrow (4.15). -/
@[reassoc]
theorem lift_unitorApp (b : B) (X : r.Fiber b) :
    L.lift (𝟙 b) X ≫ (L.unitorApp hL b X).hom.1 = 𝟙 X.1 := by
  letI : r.IsStronglyCocartesian (𝟙 b) (L.lift (𝟙 b) X) := hL (𝟙 b) X
  letI : r.IsStronglyCocartesian (𝟙 b)
      (identityLift (r := r) b X) :=
    identityLift_isStronglyCocartesian (r := r) b X
  exact strongLiftComparisonHom_fac r (𝟙 b)
    (L.lift (𝟙 b) X) (identityLift (r := r) b X)

/-- The unitor is natural on vertical arrows. -/
theorem unitor_naturality (b : B) {X Y : r.Fiber b} (f : X ⟶ Y) :
    (L.transport hL (𝟙 b)).map f ≫ (L.unitorApp hL b Y).hom =
      (L.unitorApp hL b X).hom ≫ f := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : r.IsStronglyCocartesian (𝟙 b) (L.lift (𝟙 b) X) := hL (𝟙 b) X
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r (𝟙 b) (L.lift (𝟙 b) X) (𝟙 b)
  change L.lift (𝟙 b) X ≫
      ((L.map hL (𝟙 b) f).1 ≫ (L.unitorApp hL b Y).hom.1) =
    L.lift (𝟙 b) X ≫ ((L.unitorApp hL b X).hom.1 ≫ f.1)
  calc
    _ = (L.lift (𝟙 b) X ≫ (L.map hL (𝟙 b) f).1) ≫
          (L.unitorApp hL b Y).hom.1 := (Category.assoc _ _ _).symm
    _ = (f.1 ≫ L.lift (𝟙 b) Y) ≫
          (L.unitorApp hL b Y).hom.1 := by rw [L.lift_map]
    _ = f.1 ≫ (L.lift (𝟙 b) Y ≫
          (L.unitorApp hL b Y).hom.1) := Category.assoc _ _ _
    _ = f.1 := by rw [L.lift_unitorApp, Category.comp_id]
    _ = (L.lift (𝟙 b) X ≫
          (L.unitorApp hL b X).hom.1) ≫ f.1 := by
      rw [L.lift_unitorApp, Category.id_comp]
    _ = _ := Category.assoc _ _ _

/-- The natural unitor of transport. -/
noncomputable def unitor (b : B) :
    L.transport hL (𝟙 b) ≅ 𝟭 (r.Fiber b) :=
  NatIso.ofComponents (L.unitorApp hL b)
    (fun f => L.unitor_naturality hL b f)

/-- Object transport induced by equality of two base arrows. -/
noncomputable def transportEqCast {b b' : B} {σ τ : b ⟶ b'}
    (e : σ = τ) (X : r.Fiber b) :
    (L.transport hL σ).obj X ⟶ (L.transport hL τ).obj X :=
  eqToHom (congrArg (fun k => (L.transport hL k).obj X) e)

/-- Equality transport of a base arrow carries one selected lift to the other. -/
@[reassoc]
theorem lift_transportEqCast {b b' : B} {σ τ : b ⟶ b'}
    (e : σ = τ) (X : r.Fiber b) :
    L.lift σ X ≫ (L.transportEqCast hL e X).1 = L.lift τ X := by
  cases e
  change L.lift σ X ≫ 𝟙 _ = L.lift σ X
  exact Category.comp_id _

/-- The right-associated selected lift along three composable base arrows. -/
noncomputable def tripleIteratedLift {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    X.1 ⟶ ((L.transport hL υ).obj
      ((L.transport hL τ).obj ((L.transport hL σ).obj X))).1 :=
  L.lift σ X ≫
    L.iteratedLift hL τ υ ((L.transport hL σ).obj X)

/-- The three-step selected lift is strong over right-associated composition. -/
theorem tripleIteratedLift_isStronglyCocartesian {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    r.IsStronglyCocartesian (σ ≫ (τ ≫ υ))
      (L.tripleIteratedLift hL σ τ υ X) := by
  letI : r.IsStronglyCocartesian σ (L.lift σ X) := hL σ X
  letI : r.IsStronglyCocartesian (τ ≫ υ)
      (L.iteratedLift hL τ υ ((L.transport hL σ).obj X)) :=
    L.iteratedLift_isStronglyCocartesian hL τ υ
      ((L.transport hL σ).obj X)
  exact CategoryTheory.Functor.IsStronglyCocartesian.comp r

/-- Cast direct transport from right- to left-associated base composition. -/
noncomputable def associatorCast {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    (L.transport hL (σ ≫ (τ ≫ υ))).obj X ⟶
      (L.transport hL ((σ ≫ τ) ≫ υ)).obj X :=
  L.transportEqCast hL (Category.assoc σ τ υ).symm X

/-- First route in (4.16): transport the inner compositor, then compose once more. -/
noncomputable def associativityLeftRoute {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    (L.transport hL υ).obj
        ((L.transport hL τ).obj ((L.transport hL σ).obj X)) ⟶
      (L.transport hL ((σ ≫ τ) ≫ υ)).obj X :=
  (L.transport hL υ).map (L.compositorApp hL σ τ X).hom ≫
    (L.compositorApp hL (σ ≫ τ) υ X).hom

/-- Second route in (4.16), including the base associativity cast. -/
noncomputable def associativityRightRoute {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    (L.transport hL υ).obj
        ((L.transport hL τ).obj ((L.transport hL σ).obj X)) ⟶
      (L.transport hL ((σ ≫ τ) ≫ υ)).obj X :=
  (L.compositorApp hL τ υ ((L.transport hL σ).obj X)).hom ≫
    (L.compositorApp hL σ (τ ≫ υ) X).hom ≫
      L.associatorCast hL σ τ υ X

/-- The first associativity route carries the three-step lift to the direct lift. -/
theorem tripleIteratedLift_associativityLeftRoute {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    L.tripleIteratedLift hL σ τ υ X ≫
        (L.associativityLeftRoute hL σ τ υ X).1 =
      L.lift ((σ ≫ τ) ≫ υ) X := by
  change (L.lift σ X ≫
      (L.lift τ ((L.transport hL σ).obj X) ≫
        L.lift υ
          ((L.transport hL τ).obj ((L.transport hL σ).obj X)))) ≫
      ((L.map hL υ (L.compositorApp hL σ τ X).hom).1 ≫
        (L.compositorApp hL (σ ≫ τ) υ X).hom.1) =
    L.lift ((σ ≫ τ) ≫ υ) X
  calc
    _ = (L.lift σ X ≫ L.lift τ ((L.transport hL σ).obj X)) ≫
        (L.lift υ
            ((L.transport hL τ).obj ((L.transport hL σ).obj X)) ≫
          ((L.map hL υ (L.compositorApp hL σ τ X).hom).1 ≫
            (L.compositorApp hL (σ ≫ τ) υ X).hom.1)) := by
      simp only [Category.assoc]
    _ = (L.lift σ X ≫ L.lift τ ((L.transport hL σ).obj X)) ≫
        ((L.lift υ
            ((L.transport hL τ).obj ((L.transport hL σ).obj X)) ≫
          (L.map hL υ (L.compositorApp hL σ τ X).hom).1) ≫
            (L.compositorApp hL (σ ≫ τ) υ X).hom.1) := by
      exact congrArg
        (fun k => (L.lift σ X ≫
            L.lift τ ((L.transport hL σ).obj X)) ≫ k)
        (Category.assoc _ _ _).symm
    _ = (L.lift σ X ≫ L.lift τ ((L.transport hL σ).obj X)) ≫
        (((L.compositorApp hL σ τ X).hom.1 ≫
            L.lift υ ((L.transport hL (σ ≫ τ)).obj X)) ≫
          (L.compositorApp hL (σ ≫ τ) υ X).hom.1) := by
      exact congrArg
        (fun k => (L.lift σ X ≫
            L.lift τ ((L.transport hL σ).obj X)) ≫ k)
        (by
          simpa only [transport, Category.assoc] using
            L.lift_map_assoc hL υ (L.compositorApp hL σ τ X).hom
              (L.compositorApp hL (σ ≫ τ) υ X).hom.1)
    _ = ((L.lift σ X ≫ L.lift τ ((L.transport hL σ).obj X)) ≫
          (L.compositorApp hL σ τ X).hom.1) ≫
        (L.lift υ ((L.transport hL (σ ≫ τ)).obj X) ≫
          (L.compositorApp hL (σ ≫ τ) υ X).hom.1) := by
      simp only [Category.assoc]
    _ = L.lift (σ ≫ τ) X ≫
        (L.lift υ ((L.transport hL (σ ≫ τ)).obj X) ≫
          (L.compositorApp hL (σ ≫ τ) υ X).hom.1) := by
      rw [show (L.lift σ X ≫
            L.lift τ ((L.transport hL σ).obj X)) ≫
          (L.compositorApp hL σ τ X).hom.1 = L.lift (σ ≫ τ) X by
        simpa only [iteratedLift] using
          L.iteratedLift_compositorApp hL σ τ X]
    _ = (L.lift (σ ≫ τ) X ≫
          L.lift υ ((L.transport hL (σ ≫ τ)).obj X)) ≫
        (L.compositorApp hL (σ ≫ τ) υ X).hom.1 :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      simpa only [iteratedLift] using
        L.iteratedLift_compositorApp hL (σ ≫ τ) υ X

/-- The second associativity route carries the three-step lift to the same direct lift. -/
theorem tripleIteratedLift_associativityRightRoute {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    L.tripleIteratedLift hL σ τ υ X ≫
        (L.associativityRightRoute hL σ τ υ X).1 =
      L.lift ((σ ≫ τ) ≫ υ) X := by
  change (L.lift σ X ≫
      (L.lift τ ((L.transport hL σ).obj X) ≫
        L.lift υ
          ((L.transport hL τ).obj ((L.transport hL σ).obj X)))) ≫
      ((L.compositorApp hL τ υ ((L.transport hL σ).obj X)).hom.1 ≫
        ((L.compositorApp hL σ (τ ≫ υ) X).hom.1 ≫
          (L.associatorCast hL σ τ υ X).1)) =
    L.lift ((σ ≫ τ) ≫ υ) X
  calc
    _ = L.lift σ X ≫
        ((L.lift τ ((L.transport hL σ).obj X) ≫
            L.lift υ
              ((L.transport hL τ).obj ((L.transport hL σ).obj X))) ≫
          ((L.compositorApp hL τ υ
              ((L.transport hL σ).obj X)).hom.1 ≫
            ((L.compositorApp hL σ (τ ≫ υ) X).hom.1 ≫
              (L.associatorCast hL σ τ υ X).1))) :=
      Category.assoc _ _ _
    _ = L.lift σ X ≫
        (L.lift (τ ≫ υ) ((L.transport hL σ).obj X) ≫
          ((L.compositorApp hL σ (τ ≫ υ) X).hom.1 ≫
            (L.associatorCast hL σ τ υ X).1)) := by
      exact congrArg (fun k => L.lift σ X ≫ k) (by
        simpa only [iteratedLift] using
          L.iteratedLift_compositorApp_assoc hL τ υ
            ((L.transport hL σ).obj X)
            ((L.compositorApp hL σ (τ ≫ υ) X).hom.1 ≫
              (L.associatorCast hL σ τ υ X).1))
    _ = L.lift (σ ≫ (τ ≫ υ)) X ≫
        (L.associatorCast hL σ τ υ X).1 := by
      simpa only [iteratedLift, Category.assoc] using
        L.iteratedLift_compositorApp_assoc hL σ (τ ≫ υ) X
          (L.associatorCast hL σ τ υ X).1
    _ = _ := by
      simpa only [associatorCast] using
        L.lift_transportEqCast hL (Category.assoc σ τ υ).symm X

/-- Associativity coherence of the manuscript-oriented compositor (4.16). -/
theorem compositor_assoc {b₀ b₁ b₂ b₃ : B}
    (σ : b₀ ⟶ b₁) (τ : b₁ ⟶ b₂) (υ : b₂ ⟶ b₃)
    (X : r.Fiber b₀) :
    L.associativityLeftRoute hL σ τ υ X =
      L.associativityRightRoute hL σ τ υ X := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : r.IsStronglyCocartesian (σ ≫ (τ ≫ υ))
      (L.tripleIteratedLift hL σ τ υ X) :=
    L.tripleIteratedLift_isStronglyCocartesian hL σ τ υ X
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r (σ ≫ (τ ≫ υ)) (L.tripleIteratedLift hL σ τ υ X) (𝟙 b₃)
  change L.tripleIteratedLift hL σ τ υ X ≫
      (L.associativityLeftRoute hL σ τ υ X).1 =
    L.tripleIteratedLift hL σ τ υ X ≫
      (L.associativityRightRoute hL σ τ υ X).1
  rw [L.tripleIteratedLift_associativityLeftRoute,
    L.tripleIteratedLift_associativityRightRoute]

/-- Cast direct transport along the right unit equality `σ ≫ 𝟙 = σ`. -/
noncomputable def rightUnitCast {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    (L.transport hL (σ ≫ 𝟙 b₁)).obj X ⟶ (L.transport hL σ).obj X :=
  L.transportEqCast hL (Category.comp_id σ) X

/-- The right-unit compositor route, with its required base equality cast. -/
noncomputable def rightUnitRoute {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    (L.transport hL (𝟙 b₁)).obj ((L.transport hL σ).obj X) ⟶
      (L.transport hL σ).obj X :=
  (L.compositorApp hL σ (𝟙 b₁) X).hom ≫ L.rightUnitCast hL σ X

/-- The right-unit compositor route carries the iterated lift to the original lift. -/
theorem iteratedLift_rightUnitRoute {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    L.iteratedLift hL σ (𝟙 b₁) X ≫ (L.rightUnitRoute hL σ X).1 =
      L.lift σ X := by
  change L.iteratedLift hL σ (𝟙 b₁) X ≫
      ((L.compositorApp hL σ (𝟙 b₁) X).hom.1 ≫
        (L.rightUnitCast hL σ X).1) = L.lift σ X
  calc
    _ = L.lift (σ ≫ 𝟙 b₁) X ≫ (L.rightUnitCast hL σ X).1 := by
      simpa only [Category.assoc] using
        L.iteratedLift_compositorApp_assoc hL σ (𝟙 b₁) X
          (L.rightUnitCast hL σ X).1
    _ = _ := by
      simpa only [rightUnitCast] using
        L.lift_transportEqCast hL (Category.comp_id σ) X

/-- The target unitor carries the same iterated lift to the original lift. -/
theorem iteratedLift_unitorApp {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    L.iteratedLift hL σ (𝟙 b₁) X ≫
        (L.unitorApp hL b₁ ((L.transport hL σ).obj X)).hom.1 =
      L.lift σ X := by
  change (L.lift σ X ≫
      L.lift (𝟙 b₁) ((L.transport hL σ).obj X)) ≫
        (L.unitorApp hL b₁ ((L.transport hL σ).obj X)).hom.1 =
    L.lift σ X
  calc
    _ = L.lift σ X ≫
        (L.lift (𝟙 b₁) ((L.transport hL σ).obj X) ≫
          (L.unitorApp hL b₁ ((L.transport hL σ).obj X)).hom.1) :=
      Category.assoc _ _ _
    _ = _ := by
      rw [L.lift_unitorApp]
      simpa only [transport] using Category.comp_id (L.lift σ X)

/-- Right unit coherence `c_{id,σ} = ε_{T_σ}` from (4.16), with base cast. -/
theorem compositor_right_unit {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    L.rightUnitRoute hL σ X =
      (L.unitorApp hL b₁ ((L.transport hL σ).obj X)).hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : r.IsStronglyCocartesian (σ ≫ 𝟙 b₁)
      (L.iteratedLift hL σ (𝟙 b₁) X) :=
    L.iteratedLift_isStronglyCocartesian hL σ (𝟙 b₁) X
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r (σ ≫ 𝟙 b₁) (L.iteratedLift hL σ (𝟙 b₁) X) (𝟙 b₁)
  change L.iteratedLift hL σ (𝟙 b₁) X ≫
      (L.rightUnitRoute hL σ X).1 =
    L.iteratedLift hL σ (𝟙 b₁) X ≫
      (L.unitorApp hL b₁ ((L.transport hL σ).obj X)).hom.1
  rw [L.iteratedLift_rightUnitRoute, L.iteratedLift_unitorApp]

/-- Cast direct transport along the left unit equality `𝟙 ≫ σ = σ`. -/
noncomputable def leftUnitCast {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    (L.transport hL (𝟙 b₀ ≫ σ)).obj X ⟶ (L.transport hL σ).obj X :=
  L.transportEqCast hL (Category.id_comp σ) X

/-- The left-unit compositor route, with its required base equality cast. -/
noncomputable def leftUnitRoute {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    (L.transport hL σ).obj ((L.transport hL (𝟙 b₀)).obj X) ⟶
      (L.transport hL σ).obj X :=
  (L.compositorApp hL (𝟙 b₀) σ X).hom ≫ L.leftUnitCast hL σ X

/-- The left-unit compositor route carries the iterated lift to the original lift. -/
theorem iteratedLift_leftUnitRoute {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    L.iteratedLift hL (𝟙 b₀) σ X ≫ (L.leftUnitRoute hL σ X).1 =
      L.lift σ X := by
  change L.iteratedLift hL (𝟙 b₀) σ X ≫
      ((L.compositorApp hL (𝟙 b₀) σ X).hom.1 ≫
        (L.leftUnitCast hL σ X).1) = L.lift σ X
  calc
    _ = L.lift (𝟙 b₀ ≫ σ) X ≫ (L.leftUnitCast hL σ X).1 := by
      simpa only [Category.assoc] using
        L.iteratedLift_compositorApp_assoc hL (𝟙 b₀) σ X
          (L.leftUnitCast hL σ X).1
    _ = _ := by
      simpa only [leftUnitCast] using
        L.lift_transportEqCast hL (Category.id_comp σ) X

/-- Transporting the source unitor carries the same iterated lift to the original lift. -/
theorem iteratedLift_map_unitorApp {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    L.iteratedLift hL (𝟙 b₀) σ X ≫
        ((L.transport hL σ).map (L.unitorApp hL b₀ X).hom).1 =
      L.lift σ X := by
  change (L.lift (𝟙 b₀) X ≫
      L.lift σ ((L.transport hL (𝟙 b₀)).obj X)) ≫
        (L.map hL σ (L.unitorApp hL b₀ X).hom).1 =
    L.lift σ X
  calc
    _ = L.lift (𝟙 b₀) X ≫
        (L.lift σ ((L.transport hL (𝟙 b₀)).obj X) ≫
          (L.map hL σ (L.unitorApp hL b₀ X).hom).1) :=
      Category.assoc _ _ _
    _ = L.lift (𝟙 b₀) X ≫
        ((L.unitorApp hL b₀ X).hom.1 ≫ L.lift σ X) := by
      rw [show L.lift σ ((L.transport hL (𝟙 b₀)).obj X) ≫
          (L.map hL σ (L.unitorApp hL b₀ X).hom).1 =
        (L.unitorApp hL b₀ X).hom.1 ≫ L.lift σ X by
        simpa only [transport] using
          L.lift_map hL σ (L.unitorApp hL b₀ X).hom]
    _ = (L.lift (𝟙 b₀) X ≫
          (L.unitorApp hL b₀ X).hom.1) ≫ L.lift σ X :=
      (Category.assoc _ _ _).symm
    _ = 𝟙 X.1 ≫ L.lift σ X := by rw [L.lift_unitorApp]
    _ = _ := Category.id_comp _

/-- Left unit coherence `c_{σ,id} = T_σ(ε)` from (4.16), with base cast. -/
theorem compositor_left_unit {b₀ b₁ : B} (σ : b₀ ⟶ b₁)
    (X : r.Fiber b₀) :
    L.leftUnitRoute hL σ X =
      (L.transport hL σ).map (L.unitorApp hL b₀ X).hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : r.IsStronglyCocartesian (𝟙 b₀ ≫ σ)
      (L.iteratedLift hL (𝟙 b₀) σ X) :=
    L.iteratedLift_isStronglyCocartesian hL (𝟙 b₀) σ X
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r (𝟙 b₀ ≫ σ) (L.iteratedLift hL (𝟙 b₀) σ X) (𝟙 b₁)
  change L.iteratedLift hL (𝟙 b₀) σ X ≫
      (L.leftUnitRoute hL σ X).1 =
    L.iteratedLift hL (𝟙 b₀) σ X ≫
      (L.map hL σ (L.unitorApp hL b₀ X).hom).1
  rw [L.iteratedLift_leftUnitRoute]
  simpa only [transport] using
    (L.iteratedLift_map_unitorApp hL σ X).symm

end StrongLiftSelection

universe u v

/-- The existing canonical core lifts as input data for the arbitrary construction. -/
noncomputable def coreStrongLiftSelection {U : AtomCarrier.{u}} :
    StrongLiftSelection (packageProjection U) where
  obj := fun σ P => coreFiberTransportObj σ P
  lift := fun σ P => coreFiberLift σ P

/-- The core selection satisfies exactly the strong-lift hypothesis of Construction 4.13. -/
theorem coreStrongLiftSelection_isStronglyCocartesian {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y) (P : CoreFiber X) :
    (packageProjection U).IsStronglyCocartesian σ
      ((coreStrongLiftSelection (U := U)).lift σ P) :=
  coreFiberLift_isStronglyCocartesian σ P

/-- Generic vertical transport specializes to the existing core transport map. -/
theorem coreStrongLiftSelection_map {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    {P Q : CoreFiber X} (f : P ⟶ Q) :
    (coreStrongLiftSelection (U := U)).map
        coreStrongLiftSelection_isStronglyCocartesian σ f =
      coreFiberTransportMap σ f := by
  rfl

/-- Generic fiber transport specializes to the existing core transport functor. -/
theorem coreStrongLiftSelection_transport {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y) :
    (coreStrongLiftSelection (U := U)).transport
        coreStrongLiftSelection_isStronglyCocartesian σ =
      coreFiberTransportFunctor σ := by
  rfl

/-- The manuscript-oriented generic compositor is the inverse of the existing core compositor. -/
theorem coreStrongLiftSelection_compositorApp {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (P : CoreFiber X) :
    (coreStrongLiftSelection (U := U)).compositorApp
        coreStrongLiftSelection_isStronglyCocartesian σ τ P =
      (coreFiberCompositorApp σ τ P).symm := by
  rfl

/-- The generic natural compositor is the inverse of the existing core natural compositor. -/
theorem coreStrongLiftSelection_compositor {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z) :
    (coreStrongLiftSelection (U := U)).compositor
        coreStrongLiftSelection_isStronglyCocartesian σ τ =
      (coreFiberCompositor σ τ).symm := by
  rfl

/-- The generic unitor specializes to the existing core unitor component. -/
theorem coreStrongLiftSelection_unitorApp {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (P : CoreFiber X) :
    (coreStrongLiftSelection (U := U)).unitorApp
        coreStrongLiftSelection_isStronglyCocartesian X P =
      coreFiberUnitorApp X P := by
  rfl

/-- The generic natural unitor specializes to the existing core natural unitor. -/
theorem coreStrongLiftSelection_unitor {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) :
    (coreStrongLiftSelection (U := U)).unitor
        coreStrongLiftSelection_isStronglyCocartesian X =
      coreFiberUnitor X := by
  rfl

/-- The existing canonical geometry lifts as input data for the arbitrary construction. -/
noncomputable def geomStrongLiftSelection {U : AtomCarrier.{u}} :
    StrongLiftSelection (crossStageProjection.{u, v} U) where
  obj := fun σ G => geomFiberTransportObj σ G
  lift := fun σ G => geomFiberLift σ G

/-- The geometry selection satisfies exactly the strong-lift hypothesis of Construction 4.13. -/
theorem geomStrongLiftSelection_isStronglyCocartesian {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y) (G : GeomFiber.{u, v} X) :
    (crossStageProjection.{u, v} U).IsStronglyCocartesian σ
      ((geomStrongLiftSelection (U := U)).lift σ G) :=
  geomFiberLift_isStronglyCocartesian σ G

/-- Generic vertical transport specializes to the existing geometry transport map. -/
theorem geomStrongLiftSelection_map {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    {G H : GeomFiber.{u, v} X} (f : G ⟶ H) :
    (geomStrongLiftSelection (U := U)).map
        geomStrongLiftSelection_isStronglyCocartesian σ f =
      geomFiberTransportMap σ f := by
  rfl

/-- Generic fiber transport specializes to the existing geometry transport functor. -/
theorem geomStrongLiftSelection_transport {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y) :
    (geomStrongLiftSelection (U := U)).transport
        geomStrongLiftSelection_isStronglyCocartesian σ =
      geomFiberTransportFunctor.{u, v} σ := by
  rfl

/--
The manuscript-oriented generic compositor is the inverse of the existing
geometry compositor.
-/
theorem geomStrongLiftSelection_compositorApp {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    (geomStrongLiftSelection (U := U)).compositorApp
        geomStrongLiftSelection_isStronglyCocartesian σ τ G =
      (geomFiberCompositorApp σ τ G).symm := by
  rfl

/-- The generic natural compositor is the inverse of the existing geometry natural compositor. -/
theorem geomStrongLiftSelection_compositor {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z) :
    (geomStrongLiftSelection (U := U)).compositor
        geomStrongLiftSelection_isStronglyCocartesian σ τ =
      (geomFiberCompositor σ τ).symm := by
  rfl

/-- The generic unitor specializes to the existing geometry unitor component. -/
theorem geomStrongLiftSelection_unitorApp {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (G : GeomFiber.{u, v} X) :
    (geomStrongLiftSelection (U := U)).unitorApp
        geomStrongLiftSelection_isStronglyCocartesian X G =
      geomFiberUnitorApp X G := by
  rfl

/-- The generic natural unitor specializes to the existing geometry natural unitor. -/
theorem geomStrongLiftSelection_unitor {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) :
    (geomStrongLiftSelection (U := U)).unitor
        geomStrongLiftSelection_isStronglyCocartesian X =
      geomFiberUnitor X := by
  rfl

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
