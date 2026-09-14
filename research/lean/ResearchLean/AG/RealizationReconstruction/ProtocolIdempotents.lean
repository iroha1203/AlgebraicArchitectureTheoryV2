import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.Data.Finite.Card
import ResearchLean.AG.RealizationReconstruction.ProtocolSemantics

/-!
# Idempotent splitting for independent protocol semantics

This module discharges the idempotent-completeness requirement of G-123(B) for
the protocol realization category independently of its finite decoder.  Given
an actual idempotent natural transformation over the observation functor, it
constructs the objectwise fixed-point functor, its restricted executions and
observations, and both splitting maps.

## Implementation notes

No split object or retract certificate is an input.  Closure under every
execution follows from naturality of the given endomorphism.  Vertexwise
finiteness follows by embedding each fixed-point subtype in the original finite
state carrier.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace ProtocolRealization

variable {S : ProtocolSchema.{u}} {O : S.ExecutionCategory ⥤ Type u}

/-- The objectwise fixed-point functor of a semantic protocol endomorphism.

This is the constructed splitting object for G-123(B); its execution maps are
restrictions of the original functor, with closure proved by naturality. -/
def fixedPointFunctor (X : ProtocolRealization S O) (e : X ⟶ X) :
    S.ExecutionCategory ⥤ Type u where
  obj q := {x : X.toFunctor.obj q // e.toNatTrans.app q x = x}
  map {q q'} f x :=
    ⟨X.toFunctor.map f x, by
      have h := congrFun (e.toNatTrans.naturality f) x
      exact h.trans (congrArg (X.toFunctor.map f) x.property)⟩
  map_id q := by
    funext x
    apply Subtype.ext
    exact congrFun (X.toFunctor.map_id q) x
  map_comp f g := by
    funext x
    apply Subtype.ext
    exact congrFun (X.toFunctor.map_comp f g) x

/-- Observation restricted to the fixed-point functor.

This construction uses the original observation and proves naturality for all
quotient executions from the original natural transformation. -/
def fixedPointObservation (X : ProtocolRealization S O) (e : X ⟶ X) :
    fixedPointFunctor X e ⟶ O where
  app q x := X.observation.app q x.1
  naturality := by
    intro q q' f
    funext x
    exact congrFun (X.observation.naturality f) x.1

/-- The semantic protocol object carried by the fixed points of an endomorphism.

This packages the constructed functor and observation; finite named carriers
are inherited from the original G-123(E) object premise. -/
def fixedPoint (X : ProtocolRealization S O) (e : X ⟶ X) : ProtocolRealization S O where
  toFunctor := fixedPointFunctor X e
  state_finite := fun v => by
    let inclusion : (fixedPointFunctor X e).obj (S.vertexObject v) → X.State v :=
      Subtype.val
    exact Finite.of_injective inclusion (fun _ _ h => Subtype.ext h)
  observation := fixedPointObservation X e

/-- Inclusion of the constructed fixed-point protocol into the original one.

This is the first splitting map for G-123(B) and is natural for every execution. -/
def fixedPointInclusion (X : ProtocolRealization S O) (e : X ⟶ X) :
    fixedPoint X e ⟶ X where
  toNatTrans :=
    { app := fun _ => Subtype.val
      naturality := by
        intro q q' f
        rfl }
  observation_naturality := by
    ext q x
    rfl

/-- Retraction onto the fixed-point protocol for an idempotent endomorphism.

The idempotence equation is the sole direction hypothesis and is used to prove
that every value of `e` lies in the fixed-point subtype. -/
def fixedPointRetraction (X : ProtocolRealization S O) (e : X ⟶ X)
    (he : e ≫ e = e) : X ⟶ fixedPoint X e where
  toNatTrans :=
    { app := fun q x =>
        ⟨e.toNatTrans.app q x, by
          have h := congrArg (fun a : X ⟶ X => a.toNatTrans.app q) he
          exact congrFun h x⟩
      naturality := by
        intro q q' f
        funext x
        apply Subtype.ext
        exact congrFun (e.toNatTrans.naturality f) x }
  observation_naturality := by
    ext q x
    have h := NatTrans.congr_app e.observation_naturality q
    exact congrFun h x

/-- Inclusion followed by retraction is identity on the fixed-point protocol.

This is the first splitting equation required for G-123(B). -/
theorem fixedPoint_split_id (X : ProtocolRealization S O) (e : X ⟶ X)
    (he : e ≫ e = e) :
    fixedPointInclusion X e ≫ fixedPointRetraction X e he = 𝟙 _ := by
  apply Hom.ext
  ext q x
  apply Subtype.ext
  exact x.property

/-- Retraction followed by inclusion recovers the original idempotent.

This is the second, separately proved splitting equation for G-123(B). -/
theorem fixedPoint_split_e (X : ProtocolRealization S O) (e : X ⟶ X)
    (he : e ≫ e = e) :
    fixedPointRetraction X e he ≫ fixedPointInclusion X e = e := by
  apply Hom.ext
  ext q x
  rfl

/-- Main G-123(B) idempotent-completeness instance for protocol semantics.

Every idempotent splits through the explicitly constructed fixed-point functor;
the result is independent of the finite presentation equivalence. -/
instance protocolRealization_isIdempotentComplete :
    IsIdempotentComplete (ProtocolRealization S O) where
  idempotents_split X e he :=
    ⟨fixedPoint X e, fixedPointInclusion X e, fixedPointRetraction X e he,
      fixedPoint_split_id X e he, fixedPoint_split_e X e he⟩

end ProtocolRealization

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
