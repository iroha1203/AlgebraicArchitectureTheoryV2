import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryPostFiberInvariance

/-!
Cycle 29 evidence for `G-aat-quality-surface-04`.

Cycle 28 characterizes observation-level current-shadow extensionality of
finite query-generated observations by post-map invariance on current-shadow
query-reading fibers.  This file makes the induced factor explicit: choose the
canonical representative tower for a current shadow and read the post-map on
that representative query vector.

This is still a support node.  It constructs the finite-query factor once the
fiber-invariance premise is supplied; it does not derive that premise from
semantic soundness.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryFiberFactor

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryPostFiberInvariance

universe u v w x y z

/-! ## Canonical factor on current-shadow query fibers -/

/--
The canonical factor induced by a finite query post-map on current-shadow
fibers.

At a current shadow, it reads the query vector of the canonical representative
tower of that shadow.
-/
def canonicalQueryPostFiberFactor
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out)
    (shadow : FiniteTowerLayerShadow) : Out :=
  post shadow
    (supportTraceVector query
      (representativeTowerOfShadow.{u, v, w, x, y}
        (Atom := Atom) shadow).sourceTraceToken)

/--
The canonical representative tower realizes the readings used by
`canonicalQueryPostFiberFactor`.
-/
theorem queryReadingsRealizableAtCurrentShadow_representative
    {Atom : Type u}
    (query : List Atom)
    (shadow : FiniteTowerLayerShadow) :
    QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
      (Atom := Atom) query shadow
      (supportTraceVector query
        (representativeTowerOfShadow.{u, v, w, x, y}
          (Atom := Atom) shadow).sourceTraceToken) := by
  exact
    ⟨representativeTowerOfShadow.{u, v, w, x, y}
        (Atom := Atom) shadow,
      canonicalShadow_representativeTowerOfShadow.{u, v, w, x, y}
        (Atom := Atom) shadow,
      rfl⟩

/--
Fiber invariance identifies every realized query-reading value with the
canonical representative factor.
-/
theorem post_eq_canonicalQueryPostFiberFactor_of_postInvariant
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) query post)
    {shadow : FiniteTowerLayerShadow}
    {readings : List Bool}
    (hrealized :
      QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
        (Atom := Atom) query shadow readings) :
    post shadow readings =
      canonicalQueryPostFiberFactor
        (Atom := Atom) query post shadow := by
  exact
    hinvariant shadow readings
      (supportTraceVector query
        (representativeTowerOfShadow.{u, v, w, x, y}
          (Atom := Atom) shadow).sourceTraceToken)
      hrealized
      (queryReadingsRealizableAtCurrentShadow_representative
        (Atom := Atom) query shadow)

/--
Under post-fiber invariance, the generated observation factors through the
explicit canonical query-post factor.
-/
theorem queryTraceGeneratedObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) query post)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    post (canonicalTowerLayerShadow T)
        (supportTraceVector query T.sourceTraceToken) =
      canonicalQueryPostFiberFactor
        (Atom := Atom) query post (canonicalTowerLayerShadow T) := by
  exact
    post_eq_canonicalQueryPostFiberFactor_of_postInvariant
      (Atom := Atom)
      hinvariant
      (queryReadingsRealizableAtCurrentShadow_self query T)

/--
Finite query package version of explicit current-shadow factorization.
-/
theorem finiteTraceQueryObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) obs.query obs.post)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    obs.observe T =
      canonicalQueryPostFiberFactor
        (Atom := Atom) obs.query obs.post (canonicalTowerLayerShadow T) := by
  exact
    queryTraceGeneratedObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
      (Atom := Atom) hinvariant T

/--
The canonical factor is pointwise unique among factors defined on current
shadows that agree with the post-map on every realized query-reading fiber.
-/
theorem canonicalQueryPostFiberFactor_pointwise_unique
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    {factor : FiniteTowerLayerShadow -> Out}
    (hfactor :
      ∀ shadow readings,
        QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
          (Atom := Atom) query shadow readings ->
          post shadow readings = factor shadow) :
    ∀ shadow,
      factor shadow =
        canonicalQueryPostFiberFactor
          (Atom := Atom) query post shadow := by
  intro shadow
  exact
    (hfactor shadow
      (supportTraceVector query
        (representativeTowerOfShadow.{u, v, w, x, y}
          (Atom := Atom) shadow).sourceTraceToken)
      (queryReadingsRealizableAtCurrentShadow_representative
        (Atom := Atom) query shadow)).symm

/--
Explicit universal factorization package for finite query-generated
observations under post-fiber invariance.
-/
theorem queryTraceGeneratedObservation_explicitFiberFactorization
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) query post) :
    (∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken) =
        canonicalQueryPostFiberFactor
          (Atom := Atom) query post (canonicalTowerLayerShadow T)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ shadow readings,
          QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
            (Atom := Atom) query shadow readings ->
            post shadow readings = factor shadow) ->
          ∀ shadow,
            factor shadow =
              canonicalQueryPostFiberFactor
                (Atom := Atom) query post shadow) := by
  exact
    ⟨queryTraceGeneratedObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
      (Atom := Atom) hinvariant,
      fun factor hfactor =>
        canonicalQueryPostFiberFactor_pointwise_unique
          (Atom := Atom) hfactor⟩

end SemanticRepairFiniteQueryFiberFactor
end QualitySurface
end Formal.AG.Research
