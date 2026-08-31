import ResearchLean.AG.GeometryTransport.Categories

/-!
# Realization-exact upper equivalences

This module begins G-115 K2b2b-r.  It separates the exact upper map needed by
geometry realization from the lower component of a `PackageTotalHom`.  The
realization supply is indexed directly by that upper map, while the comparison
below proves that no new notion is introduced when an exact total hom is
available.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

universe u₁ u₂ u₃ u₄

open CategoryTheory AtomFoundation GeometryTransport

/-- An exact equivalence at the upper (signed-reading) level only.

No lower morphism is stored: the two cancellation laws are precisely the data
needed by the realization-exact part of G-115. -/
structure ExactUpperEquivalence {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) where
  forward : SignedExactCoreReadingHom P Q
  backward : SignedExactCoreReadingHom Q P
  forward_backward :
    forward.comp backward = SignedExactCoreReadingHom.refl P
  backward_forward :
    backward.comp forward = SignedExactCoreReadingHom.refl Q

/-- Forward context transport attached directly to an exact upper map. -/
abbrev upperCoreContextFunctor {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :=
  f.equationTransport.contextEquivalence.functor

private theorem signed_comp_assoc {U : AtomCarrier.{u}}
    {P Q R S : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R)
    (h : SignedExactCoreReadingHom R S) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply SignedExactCoreReadingHom.ext <;> rfl

private theorem signed_refl_comp {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :
    (SignedExactCoreReadingHom.refl P).comp f = f := by
  apply SignedExactCoreReadingHom.ext <;> rfl

private theorem signed_comp_refl {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :
    f.comp (SignedExactCoreReadingHom.refl Q) = f := by
  apply SignedExactCoreReadingHom.ext <;> rfl

/-- A dependent cast equality gives the corresponding heterogeneous equality. -/
private theorem heq_of_cast_eq {A : Type u₁} {X : A → Type u₂}
    {a b : A} (h : a = b) {x : X a} {y : X b}
    (hxy : cast (congrArg X h) x = y) : HEq x y := by
  cases h
  cases hxy
  rfl

/-- A heterogeneous equality can be transported along a specified index path. -/
private theorem cast_eq_of_heq {A : Type u₁} {X : A → Type u₂}
    {a b : A} (h : a = b) {x : X a} {y : X b}
    (hxy : HEq x y) : cast (congrArg X h) x = y := by
  cases h
  exact eq_of_heq hxy

/-- Componentwise cancellations compose across two dependent carrier maps.

Implementation notes: the four component maps are lifted to maps of dependent
Sigma types.  Their two cancellation equalities then compose without casts;
the second component is finally transported along the authored composite index
equality. -/
private theorem dependent_cancel_comp
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    {XA : A → Type u₄} {XB : B → Type u₄} {XC : C → Type u₄}
    (f : A → B) (g : B → C) (gi : C → B) (fi : B → A)
    (hf : ∀ a, XA a → XB (f a)) (hg : ∀ b, XB b → XC (g b))
    (hgi : ∀ c, XC c → XB (gi c)) (hfi : ∀ b, XB b → XA (fi b))
    (pf : ∀ a, fi (f a) = a) (pg : ∀ b, gi (g b) = b)
    (hf_cancel : ∀ a x, cast (congrArg XA (pf a)) (hfi _ (hf a x)) = x)
    (hg_cancel : ∀ b x, cast (congrArg XB (pg b)) (hgi _ (hg b x)) = x)
    (pcomp : ∀ a, fi (gi (g (f a))) = a) :
    ∀ a x, cast (congrArg XA (pcomp a))
      (hfi _ (hgi _ (hg _ (hf a x)))) = x := by
  let F : Sigma XA → Sigma XB := fun x => ⟨f x.1, hf x.1 x.2⟩
  let G : Sigma XB → Sigma XC := fun x => ⟨g x.1, hg x.1 x.2⟩
  let Gi : Sigma XC → Sigma XB := fun x => ⟨gi x.1, hgi x.1 x.2⟩
  let Fi : Sigma XB → Sigma XA := fun x => ⟨fi x.1, hfi x.1 x.2⟩
  have hF : ∀ x, Fi (F x) = x := fun x =>
    Sigma.ext (pf x.1) (heq_of_cast_eq (pf x.1) (hf_cancel x.1 x.2))
  have hG : ∀ x, Gi (G x) = x := fun x =>
    Sigma.ext (pg x.1) (heq_of_cast_eq (pg x.1) (hg_cancel x.1 x.2))
  intro a x
  have htotal : Fi (Gi (G (F ⟨a, x⟩))) = ⟨a, x⟩ := by
    rw [hG (F ⟨a, x⟩), hF ⟨a, x⟩]
  exact cast_eq_of_heq (pcomp a) (Sigma.ext_iff.mp htotal).2

/-- Inverse preservation plus component cancellation reflects a dependent
predicate.

Implementation notes: the forward and inverse carrier maps are lifted to
dependent Sigma types, where component cancellation rewrites the inverse image
of the preserved predicate back to its original indexed value. -/
private theorem dependent_reflect
    {A : Type u₁} {B : Type u₂} {XA : A → Type u₃} {XB : B → Type u₃}
    (f : A → B) (fi : B → A)
    (hf : ∀ a, XA a → XB (f a)) (hfi : ∀ b, XB b → XA (fi b))
    (pf : ∀ a, fi (f a) = a)
    (hf_cancel : ∀ a x, cast (congrArg XA (pf a)) (hfi _ (hf a x)) = x)
    (PA : ∀ a, XA a → Prop) (PB : ∀ b, XB b → Prop)
    (hfi_preserves : ∀ b x, PB b x → PA (fi b) (hfi b x)) :
    ∀ a x, PB (f a) (hf a x) → PA a x := by
  let F : Sigma XA → Sigma XB := fun x => ⟨f x.1, hf x.1 x.2⟩
  let Fi : Sigma XB → Sigma XA := fun x => ⟨fi x.1, hfi x.1 x.2⟩
  have hF : ∀ x, Fi (F x) = x := fun x =>
    Sigma.ext (pf x.1) (heq_of_cast_eq (pf x.1) (hf_cancel x.1 x.2))
  intro a x hread
  have hinv : PA (fi (f a)) (hfi (f a) (hf a x)) :=
    hfi_preserves (f a) (hf a x) hread
  have htotal := hF (⟨a, x⟩ : Sigma XA)
  change Fi (F ⟨a, x⟩) = ⟨a, x⟩ at htotal
  have : PA (Fi (F ⟨a, x⟩)).1 (Fi (F ⟨a, x⟩)).2 := hinv
  rw [htotal] at this
  exact this

namespace ExactUpperEquivalence

/-- Identity exact upper equivalence. -/
def refl {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    ExactUpperEquivalence P P where
  forward := SignedExactCoreReadingHom.refl P
  backward := SignedExactCoreReadingHom.refl P
  forward_backward := signed_refl_comp _
  backward_forward := signed_refl_comp _

/-- Symmetry of exact upper equivalence. -/
def symm {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (e : ExactUpperEquivalence P Q) : ExactUpperEquivalence Q P where
  forward := e.backward
  backward := e.forward
  forward_backward := e.backward_forward
  backward_forward := e.forward_backward

/-- Composition of exact upper equivalences. -/
def comp {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    (e : ExactUpperEquivalence P Q) (d : ExactUpperEquivalence Q R) :
    ExactUpperEquivalence P R where
  forward := e.forward.comp d.forward
  backward := d.backward.comp e.backward
  forward_backward := by
    rw [signed_comp_assoc, ← signed_comp_assoc d.forward d.backward e.backward,
      d.forward_backward, signed_refl_comp, e.forward_backward]
  backward_forward := by
    rw [signed_comp_assoc, ← signed_comp_assoc e.backward e.forward d.forward,
      e.backward_forward, signed_refl_comp, d.backward_forward]

end ExactUpperEquivalence

namespace ExactUpperEquivalence

/-- The forward-then-backward context object is the original object. -/
theorem forwardBackwardContext {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (e : ExactUpperEquivalence P Q)
    (W : Site.ContextCategoryObject P.contextPreorder) :
    (upperCoreContextFunctor e.backward).obj
        ((upperCoreContextFunctor e.forward).obj W) = W := by
  have h := congrArg
    (fun f : SignedExactCoreReadingHom P P =>
      (upperCoreContextFunctor f).obj W) e.forward_backward
  exact h

/-- The backward-then-forward context object is the original object. -/
theorem backwardForwardContext {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (e : ExactUpperEquivalence P Q)
    (W : Site.ContextCategoryObject Q.contextPreorder) :
    (upperCoreContextFunctor e.forward).obj
        ((upperCoreContextFunctor e.backward).obj W) = W := by
  have h := congrArg
    (fun f : SignedExactCoreReadingHom Q Q =>
      (upperCoreContextFunctor f).obj W) e.backward_forward
  exact h

/-- The forward atom map followed by the backward atom map is the identity. -/
theorem forwardBackwardAtom {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (e : ExactUpperEquivalence P Q) (atom : U.Atom) :
    e.backward.atomEquiv (e.forward.atomEquiv atom) = atom := by
  have h := congrArg
    (fun f : SignedExactCoreReadingHom P P => f.atomEquiv atom)
    e.forward_backward
  exact h

/-- The backward atom map followed by the forward atom map is the identity. -/
theorem backwardForwardAtom {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (e : ExactUpperEquivalence P Q) (atom : U.Atom) :
    e.forward.atomEquiv (e.backward.atomEquiv atom) = atom := by
  have h := congrArg
    (fun f : SignedExactCoreReadingHom Q Q => f.atomEquiv atom)
    e.backward_forward
  exact h

end ExactUpperEquivalence

/-- Realization transport indexed by an exact upper map rather than by a
completed total core hom. -/
structure UpperRealizationTransportSupply {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) (f : SignedExactCoreReadingHom P Q) where
  supportComp : ∀ W : Site.ContextCategoryObject P.contextPreorder,
    W.ctx.Support → ((upperCoreContextFunctor f).obj W).ctx.Support
  axisComp : ∀ W : Site.ContextCategoryObject P.contextPreorder,
    W.ctx.Axis → ((upperCoreContextFunctor f).obj W).ctx.Axis
  observableComp : ∀ W : Site.ContextCategoryObject P.contextPreorder,
    W.ctx.Observable → ((upperCoreContextFunctor f).obj W).ctx.Observable
  supportReads : ∀ (W : Site.ContextCategoryObject P.contextPreorder) support atom,
    W.ctx.minimal.supportReads support atom →
      ((upperCoreContextFunctor f).obj W).ctx.minimal.supportReads
        (supportComp W support) (f.atomEquiv atom)
  axisReads : ∀ (W : Site.ContextCategoryObject P.contextPreorder) axis,
    W.ctx.minimal.axisReads axis →
      ((upperCoreContextFunctor f).obj W).ctx.minimal.axisReads (axisComp W axis)
  observableReads : ∀ (W : Site.ContextCategoryObject P.contextPreorder) observable,
    W.ctx.minimal.observableReads observable →
      ((upperCoreContextFunctor f).obj W).ctx.minimal.observableReads
        (observableComp W observable)
  support_naturality : ∀ {W V : Site.ContextCategoryObject P.contextPreorder}
      (w : W ⟶ V) support,
    (Q.contextPreorder.morphism
      (leOfHom ((upperCoreContextFunctor f).map w))).supportMap
        (supportComp W support) =
      supportComp V
        ((P.contextPreorder.morphism (leOfHom w)).supportMap support)
  axis_naturality : ∀ {W V : Site.ContextCategoryObject P.contextPreorder}
      (w : W ⟶ V) axis,
    (Q.contextPreorder.morphism
      (leOfHom ((upperCoreContextFunctor f).map w))).axisMap
        (axisComp W axis) =
      axisComp V ((P.contextPreorder.morphism (leOfHom w)).axisMap axis)
  observable_naturality : ∀ {W V : Site.ContextCategoryObject P.contextPreorder}
      (w : W ⟶ V) observable,
    (Q.contextPreorder.morphism
      (leOfHom ((upperCoreContextFunctor f).map w))).observableRestrict
        (observableComp V observable) =
      observableComp W
        ((P.contextPreorder.morphism (leOfHom w)).observableRestrict observable)

namespace UpperRealizationTransportSupply

/-- Identity realization supply. -/
def refl {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    UpperRealizationTransportSupply P P (SignedExactCoreReadingHom.refl P) where
  supportComp := fun _ support => support
  axisComp := fun _ axis => axis
  observableComp := fun _ observable => observable
  supportReads := fun _ _ _ h => h
  axisReads := fun _ _ h => h
  observableReads := fun _ _ h => h
  support_naturality := by intros; rfl
  axis_naturality := by intros; rfl
  observable_naturality := by intros; rfl

/-- Composition of upper-indexed realization supplies. -/
def comp {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    {f : SignedExactCoreReadingHom P Q}
    {g : SignedExactCoreReadingHom Q R}
    (Hf : UpperRealizationTransportSupply P Q f)
    (Hg : UpperRealizationTransportSupply Q R g) :
    UpperRealizationTransportSupply P R (f.comp g) where
  supportComp W support := Hg.supportComp _ (Hf.supportComp W support)
  axisComp W axis := Hg.axisComp _ (Hf.axisComp W axis)
  observableComp W observable :=
    Hg.observableComp _ (Hf.observableComp W observable)
  supportReads W support atom h :=
    Hg.supportReads _ _ _ (Hf.supportReads W support atom h)
  axisReads W axis h := Hg.axisReads _ _ (Hf.axisReads W axis h)
  observableReads W observable h :=
    Hg.observableReads _ _ (Hf.observableReads W observable h)
  support_naturality w support := by
    rw [Hg.support_naturality ((upperCoreContextFunctor f).map w)
      (Hf.supportComp _ support), Hf.support_naturality w support]
  axis_naturality w axis := by
    rw [Hg.axis_naturality ((upperCoreContextFunctor f).map w)
      (Hf.axisComp _ axis), Hf.axis_naturality w axis]
  observable_naturality w observable := by
    rw [Hg.observable_naturality ((upperCoreContextFunctor f).map w)
      (Hf.observableComp _ observable), Hf.observable_naturality w observable]

end UpperRealizationTransportSupply

/-- The upper-indexed supply is definitionally the existing G-108 supply when
the upper map comes from a total core hom. -/
def upperRealizationTransportSupplyEquiv {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : PackageTotalHom P Q) :
    UpperRealizationTransportSupply P Q f.upper ≃
      RealizationTransportSupply P Q f where
  toFun H :=
    { supportComp := H.supportComp
      axisComp := H.axisComp
      observableComp := H.observableComp
      supportReads := H.supportReads
      axisReads := H.axisReads
      observableReads := H.observableReads
      support_naturality := H.support_naturality
      axis_naturality := H.axis_naturality
      observable_naturality := H.observable_naturality }
  invFun H :=
    { supportComp := H.supportComp
      axisComp := H.axisComp
      observableComp := H.observableComp
      supportReads := H.supportReads
      axisReads := H.axisReads
      observableReads := H.observableReads
      support_naturality := H.support_naturality
      axis_naturality := H.axis_naturality
      observable_naturality := H.observable_naturality }
  left_inv H := by cases H; rfl
  right_inv H := by cases H; rfl

/-- Realization-exactness of an exact upper equivalence.

The six laws are stated after transport along the two upper cancellation
equalities.  Thus the carrier types are identified by the authored upper
equivalence itself, rather than by an unchecked cast or by a lower morphism. -/
structure RealizationExactUpperEquivalence {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (e : ExactUpperEquivalence P Q) where
  homSupply : UpperRealizationTransportSupply P Q e.forward
  invSupply : UpperRealizationTransportSupply Q P e.backward
  support_hom_inv : ∀ (W : Site.ContextCategoryObject P.contextPreorder)
      (support : W.ctx.Support),
    cast (congrArg (fun X => X.ctx.Support) (e.forwardBackwardContext W))
        (invSupply.supportComp _ (homSupply.supportComp W support)) = support
  support_inv_hom : ∀ (W : Site.ContextCategoryObject Q.contextPreorder)
      (support : W.ctx.Support),
    cast (congrArg (fun X => X.ctx.Support) (e.backwardForwardContext W))
        (homSupply.supportComp _ (invSupply.supportComp W support)) = support
  axis_hom_inv : ∀ (W : Site.ContextCategoryObject P.contextPreorder)
      (axis : W.ctx.Axis),
    cast (congrArg (fun X => X.ctx.Axis) (e.forwardBackwardContext W))
        (invSupply.axisComp _ (homSupply.axisComp W axis)) = axis
  axis_inv_hom : ∀ (W : Site.ContextCategoryObject Q.contextPreorder)
      (axis : W.ctx.Axis),
    cast (congrArg (fun X => X.ctx.Axis) (e.backwardForwardContext W))
        (homSupply.axisComp _ (invSupply.axisComp W axis)) = axis
  observable_hom_inv : ∀ (W : Site.ContextCategoryObject P.contextPreorder)
      (observable : W.ctx.Observable),
    cast (congrArg (fun X => X.ctx.Observable) (e.forwardBackwardContext W))
        (invSupply.observableComp _
          (homSupply.observableComp W observable)) = observable
  observable_inv_hom : ∀ (W : Site.ContextCategoryObject Q.contextPreorder)
      (observable : W.ctx.Observable),
    cast (congrArg (fun X => X.ctx.Observable) (e.backwardForwardContext W))
        (homSupply.observableComp _
          (invSupply.observableComp W observable)) = observable

namespace RealizationExactUpperEquivalence

/-- Identity realization-exact upper equivalence. -/
def refl {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    RealizationExactUpperEquivalence (ExactUpperEquivalence.refl P) where
  homSupply := UpperRealizationTransportSupply.refl P
  invSupply := UpperRealizationTransportSupply.refl P
  support_hom_inv := by intros; rfl
  support_inv_hom := by intros; rfl
  axis_hom_inv := by intros; rfl
  axis_inv_hom := by intros; rfl
  observable_hom_inv := by intros; rfl
  observable_inv_hom := by intros; rfl

/-- Symmetry preserves realization-exactness. -/
def symm {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e) :
    RealizationExactUpperEquivalence e.symm where
  homSupply := H.invSupply
  invSupply := H.homSupply
  support_hom_inv := H.support_inv_hom
  support_inv_hom := H.support_hom_inv
  axis_hom_inv := H.axis_inv_hom
  axis_inv_hom := H.axis_hom_inv
  observable_hom_inv := H.observable_inv_hom
  observable_inv_hom := H.observable_hom_inv

/-- Composition preserves realization-exactness.

Implementation notes: the forward supplies compose in route order, while the
inverse supplies compose in the reverse order.  Each cancellation field is
obtained by applying the inner component cancellation and then the outer one;
the casts are exactly those generated by the composed upper cancellation. -/
def comp {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    {e : ExactUpperEquivalence P Q} {d : ExactUpperEquivalence Q R}
    (H : RealizationExactUpperEquivalence e)
    (K : RealizationExactUpperEquivalence d) :
    RealizationExactUpperEquivalence (e.comp d) where
  homSupply := H.homSupply.comp K.homSupply
  invSupply := K.invSupply.comp H.invSupply
  support_hom_inv W support := by
    exact dependent_cancel_comp
      (XA := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Support)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Support)
      (XC := fun X : Site.ContextCategoryObject R.contextPreorder => X.ctx.Support)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor d.forward).obj X)
      (fun X => (upperCoreContextFunctor d.backward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      H.homSupply.supportComp K.homSupply.supportComp
      K.invSupply.supportComp H.invSupply.supportComp
      e.forwardBackwardContext d.forwardBackwardContext
      H.support_hom_inv K.support_hom_inv
      (e.comp d).forwardBackwardContext W support
  support_inv_hom W support := by
    exact dependent_cancel_comp
      (XA := fun X : Site.ContextCategoryObject R.contextPreorder => X.ctx.Support)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Support)
      (XC := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Support)
      (fun X => (upperCoreContextFunctor d.backward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor d.forward).obj X)
      K.invSupply.supportComp H.invSupply.supportComp
      H.homSupply.supportComp K.homSupply.supportComp
      d.backwardForwardContext e.backwardForwardContext
      K.support_inv_hom H.support_inv_hom
      (e.comp d).backwardForwardContext W support
  axis_hom_inv W axis := by
    exact dependent_cancel_comp
      (XA := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Axis)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Axis)
      (XC := fun X : Site.ContextCategoryObject R.contextPreorder => X.ctx.Axis)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor d.forward).obj X)
      (fun X => (upperCoreContextFunctor d.backward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      H.homSupply.axisComp K.homSupply.axisComp
      K.invSupply.axisComp H.invSupply.axisComp
      e.forwardBackwardContext d.forwardBackwardContext
      H.axis_hom_inv K.axis_hom_inv
      (e.comp d).forwardBackwardContext W axis
  axis_inv_hom W axis := by
    exact dependent_cancel_comp
      (XA := fun X : Site.ContextCategoryObject R.contextPreorder => X.ctx.Axis)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Axis)
      (XC := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Axis)
      (fun X => (upperCoreContextFunctor d.backward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor d.forward).obj X)
      K.invSupply.axisComp H.invSupply.axisComp
      H.homSupply.axisComp K.homSupply.axisComp
      d.backwardForwardContext e.backwardForwardContext
      K.axis_inv_hom H.axis_inv_hom
      (e.comp d).backwardForwardContext W axis
  observable_hom_inv W observable := by
    exact dependent_cancel_comp
      (XA := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Observable)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Observable)
      (XC := fun X : Site.ContextCategoryObject R.contextPreorder => X.ctx.Observable)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor d.forward).obj X)
      (fun X => (upperCoreContextFunctor d.backward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      H.homSupply.observableComp K.homSupply.observableComp
      K.invSupply.observableComp H.invSupply.observableComp
      e.forwardBackwardContext d.forwardBackwardContext
      H.observable_hom_inv K.observable_hom_inv
      (e.comp d).forwardBackwardContext W observable
  observable_inv_hom W observable := by
    exact dependent_cancel_comp
      (XA := fun X : Site.ContextCategoryObject R.contextPreorder => X.ctx.Observable)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Observable)
      (XC := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Observable)
      (fun X => (upperCoreContextFunctor d.backward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor d.forward).obj X)
      K.invSupply.observableComp H.invSupply.observableComp
      H.homSupply.observableComp K.homSupply.observableComp
      d.backwardForwardContext e.backwardForwardContext
      K.observable_inv_hom H.observable_inv_hom
      (e.comp d).backwardForwardContext W observable

/-- Support reading is reflected as well as preserved by the forward supply.

Implementation notes: the reverse implication applies the backward supply's
reading-preservation law and then cancels both the transported support and the
forward-backward atom action. -/
theorem supportReads_iff {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (support : W.ctx.Support) (atom : U.Atom) :
    W.ctx.minimal.supportReads support atom ↔
      ((upperCoreContextFunctor e.forward).obj W).ctx.minimal.supportReads
        (H.homSupply.supportComp W support) (e.forward.atomEquiv atom) := by
  constructor
  · exact H.homSupply.supportReads W support atom
  · intro hread
    have hreflect := dependent_reflect
      (XA := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Support)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Support)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      H.homSupply.supportComp H.invSupply.supportComp
      e.forwardBackwardContext H.support_hom_inv
      (fun X value => X.ctx.minimal.supportReads value
        (e.backward.atomEquiv (e.forward.atomEquiv atom)))
      (fun X value => X.ctx.minimal.supportReads value
        (e.forward.atomEquiv atom))
      (fun X value h => H.invSupply.supportReads X value _ h)
      W support hread
    simpa only [e.forwardBackwardAtom atom] using hreflect

/-- Axis reading is reflected as well as preserved by the forward supply. -/
theorem axisReads_iff {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder) (axis : W.ctx.Axis) :
    W.ctx.minimal.axisReads axis ↔
      ((upperCoreContextFunctor e.forward).obj W).ctx.minimal.axisReads
        (H.homSupply.axisComp W axis) := by
  constructor
  · exact H.homSupply.axisReads W axis
  · exact dependent_reflect
      (XA := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Axis)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Axis)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      H.homSupply.axisComp H.invSupply.axisComp
      e.forwardBackwardContext H.axis_hom_inv
      (fun X value => X.ctx.minimal.axisReads value)
      (fun X value => X.ctx.minimal.axisReads value)
      (fun X value h => H.invSupply.axisReads X value h)
      W axis

/-- Observable reading is reflected as well as preserved by the forward
supply. -/
theorem observableReads_iff {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (observable : W.ctx.Observable) :
    W.ctx.minimal.observableReads observable ↔
      ((upperCoreContextFunctor e.forward).obj W).ctx.minimal.observableReads
        (H.homSupply.observableComp W observable) := by
  constructor
  · exact H.homSupply.observableReads W observable
  · exact dependent_reflect
      (XA := fun X : Site.ContextCategoryObject P.contextPreorder => X.ctx.Observable)
      (XB := fun X : Site.ContextCategoryObject Q.contextPreorder => X.ctx.Observable)
      (fun X => (upperCoreContextFunctor e.forward).obj X)
      (fun X => (upperCoreContextFunctor e.backward).obj X)
      H.homSupply.observableComp H.invSupply.observableComp
      e.forwardBackwardContext H.observable_hom_inv
      (fun X value => X.ctx.minimal.observableReads value)
      (fun X value => X.ctx.minimal.observableReads value)
      (fun X value h => H.invSupply.observableReads X value h)
      W observable

/-- Forward supply viewed as the existing G-108 realization supply whenever
an exact total hom with the same upper map is supplied. -/
def homTotalSupply {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e) (h : PackageTotalHom P Q)
    (upper_eq : h.upper = e.forward) : RealizationTransportSupply P Q h := by
  exact (upperRealizationTransportSupplyEquiv h).toFun
    (upper_eq.symm ▸ H.homSupply)

/-- Backward supply viewed as the existing G-108 realization supply whenever
an exact total hom with the same backward upper map is supplied. -/
def invTotalSupply {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e) (h : PackageTotalHom Q P)
    (upper_eq : h.upper = e.backward) : RealizationTransportSupply Q P h := by
  exact (upperRealizationTransportSupplyEquiv h).toFun
    (upper_eq.symm ▸ H.invSupply)

/-- Conditional forward `HGeom` adapter.  The total hom and its upper-map
identification are explicit arguments. -/
def homHGeom {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    {G : GeometryPackage.{u, v} U}
    {e : ExactUpperEquivalence G.core Q}
    (H : RealizationExactUpperEquivalence e)
    (h : PackageTotalHom G.core Q) (upper_eq : h.upper = e.forward) :
    HGeom G h :=
  H.homTotalSupply h upper_eq

/-- Conditional backward `HGeom` adapter. -/
def invHGeom {U : AtomCarrier.{u}} {P : AATCorePackage U}
    {G : GeometryPackage.{u, v} U}
    {e : ExactUpperEquivalence P G.core}
    (H : RealizationExactUpperEquivalence e)
    (h : PackageTotalHom G.core P) (upper_eq : h.upper = e.backward) :
    HGeom G h :=
  H.invTotalSupply h upper_eq

end RealizationExactUpperEquivalence

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
