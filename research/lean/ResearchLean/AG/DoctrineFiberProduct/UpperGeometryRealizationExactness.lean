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
