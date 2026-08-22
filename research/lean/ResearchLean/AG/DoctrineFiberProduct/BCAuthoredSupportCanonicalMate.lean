import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchema
import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness

/-!
# The canonical Beck--Chevalley mate on authored support

This module restricts the two exact Beck--Chevalley routes and their canonical
mate to the finite discrete support fixed by `AuthoredSupportContext`.  The
context's `RealizableSquare.realization_eq` is consumed directly: neither a
route, endpoint isomorphism, comparison, mate, nor exactness certificate is
accepted from a caller.

The canonical restriction depends only on the comparator-free context.  The
raw authored table is deliberately not inspected here; generating its induced
comparison and defining `MateCoherentRel` are later obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Exact authored-support routes -/

/-- The `(pi1)^*` then `(pi2)_!` route restricted to authored support. -/
noncomputable def authoredSupportDirectRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    AuthoredSupportRoute context := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact
    (AuthoredSupportContext.supportFunctor
      ⟨⟨toSemanticBC presentation, presentation, rfl⟩,
        lift, endpoint_eq⟩) ⋙
      selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcLeftPresentation presentation)) ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic (bcTopPresentation presentation))

/-- The `(sigma1)_!` then `(sigma2)^*` route restricted to authored support. -/
noncomputable def authoredSupportViaBaseRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    AuthoredSupportRoute context := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact
    (AuthoredSupportContext.supportFunctor
      ⟨⟨toSemanticBC presentation, presentation, rfl⟩,
        lift, endpoint_eq⟩) ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic (bcBottomPresentation presentation)) ⋙
      selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation presentation))

/-- The direct route as the fixed family required by the F0b2b signature. -/
noncomputable def authoredSupportDirectRouteFamily
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    AuthoredSupportRouteFamily U :=
  authoredSupportDirectRoute

/-- The via-base route as the fixed family required by the F0b2b signature. -/
noncomputable def authoredSupportViaBaseRouteFamily
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    AuthoredSupportRouteFamily U :=
  authoredSupportViaBaseRoute

/-! ## Canonical mate restriction -/

/--
Restrict the exact producer mate to the discrete authored support.  Only the
comparator-free context is an input.
-/
noncomputable def authoredSupportCanonicalMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    authoredSupportDirectRoute context ⟶
      authoredSupportViaBaseRoute context := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact Functor.whiskerLeft
    (AuthoredSupportContext.supportFunctor
      ⟨⟨toSemanticBC presentation, presentation, rfl⟩,
        lift, endpoint_eq⟩)
    (coreBeckChevalleyMate presentation)

/-- The canonical restriction inhabits the exact F0b2b producer signature. -/
noncomputable def authoredSupportCanonicalMateFamily
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    CanonicalMateRestrictionSignature
      (authoredSupportDirectRouteFamily U)
      (authoredSupportViaBaseRouteFamily U) :=
  authoredSupportCanonicalMate

/--
The authored support object retagged at the exact decoded southwest endpoint.
The only transport consumed is `RealizableSquare.realization_eq`.
-/
noncomputable def authoredSupportDecodedObject
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) (cell : context.Category) :
    CoreFiber context.square.presentation.1.cospan.firstSource.toSemantic := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact
    (AuthoredSupportContext.supportFunctor
      ⟨⟨toSemanticBC presentation, presentation, rfl⟩,
        lift, endpoint_eq⟩).obj cell

/-- Each restricted component is definitionally the exact canonical component. -/
theorem authoredSupportCanonicalMate_app_heq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) (cell : context.Category) :
    HEq ((authoredSupportCanonicalMate context).app cell)
      ((coreBeckChevalleyMate context.square.presentation).app
        (authoredSupportDecodedObject context cell)) := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  rfl

/-- Cycle 39 exactness survives restriction to every authored support. -/
noncomputable instance authoredSupportCanonicalMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    IsIso (authoredSupportCanonicalMate context) := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  rw [NatTrans.isIso_iff_isIso_app]
  intro cell
  change IsIso
    ((coreBeckChevalleyMate presentation).app
      ((AuthoredSupportContext.supportFunctor
        ⟨⟨toSemanticBC presentation, presentation, rfl⟩,
          lift, endpoint_eq⟩).obj cell))
  exact coreBeckChevalleyMate_app_isIso presentation _

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
