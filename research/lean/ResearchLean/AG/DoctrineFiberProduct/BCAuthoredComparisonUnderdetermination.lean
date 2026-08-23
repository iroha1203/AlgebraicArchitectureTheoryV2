import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredSupportCanonicalMate

/-!
# Underdetermination of the authored comparison signature

This module records the Cycle 41 blocker without weakening the fixed G-110
target.  The raw authored comparator table is an endomorphism of the southwest
support functor.  Functoriality therefore transports it to endomorphisms of the
two Beck--Chevalley routes, but does not itself provide a morphism from the
direct route to the via-base route.

The existing canonical mate supplies such a cross-route morphism.  Naturality
shows that twisting it by the authored endomorphism on either side gives the
same result.  The bare producer signature can also be inhabited while ignoring
the authored table altogether.  Consequently that signature does not express
the missing authored-incidence/factorization law required by G-110; none of the
definitions below is presented as the requested authored comparison.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Route endomorphisms induced by southwest-support endomorphisms -/

/-- Transport a southwest-support endomorphism along the direct route tail. -/
noncomputable def authoredSupportDirectEndomorphism
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (alpha : context.supportFunctor ⟶ context.supportFunctor) :
    authoredSupportDirectRoute context ⟶
      authoredSupportDirectRoute context := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact Functor.whiskerRight alpha
    (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcLeftPresentation presentation)) ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic (bcTopPresentation presentation)))

/-- Transport a southwest-support endomorphism along the via-base route tail. -/
noncomputable def authoredSupportViaBaseEndomorphism
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (alpha : context.supportFunctor ⟶ context.supportFunctor) :
    authoredSupportViaBaseRoute context ⟶
      authoredSupportViaBaseRoute context := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact Functor.whiskerRight alpha
    (coreFiberTransportFunctor
        (typedPresentationToSemantic (bcBottomPresentation presentation)) ⋙
      selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation presentation)))

/--
Naturality of the canonical mate identifies the left and right route twists.
This records the equality of these two evident constructions; it is not a
classification of every term definable from `AuthoredBCDatumSquare`.
-/
theorem authoredSupportCanonicalMate_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (alpha : context.supportFunctor ⟶ context.supportFunctor) :
    authoredSupportDirectEndomorphism context alpha ≫
        authoredSupportCanonicalMate context =
      authoredSupportCanonicalMate context ≫
        authoredSupportViaBaseEndomorphism context alpha := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  ext cell
  simpa [authoredSupportDirectEndomorphism,
    authoredSupportCanonicalMate, authoredSupportViaBaseEndomorphism] using
      congrArg Subtype.val
        ((coreBeckChevalleyMate presentation).naturality (alpha.app cell))

/-! ## Consequences for the raw authored table -/

/-- The raw authored table induces an endomorphism of the direct route. -/
noncomputable def authoredDirectRouteEndomorphism
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportDirectRoute input.context :=
  authoredSupportDirectEndomorphism input.context input.endpointAutomorphism

/-- The same raw table induces an endomorphism of the via-base route. -/
noncomputable def authoredViaBaseRouteEndomorphism
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredSupportViaBaseRoute input.context ⟶
      authoredSupportViaBaseRoute input.context :=
  authoredSupportViaBaseEndomorphism input.context input.endpointAutomorphism

/-- Left twist of the canonical mate by the authored route endomorphism. -/
noncomputable def authoredCanonicalMateLeftTwist
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportViaBaseRoute input.context :=
  authoredDirectRouteEndomorphism input ≫
    authoredSupportCanonicalMate input.context

/-- Right twist of the canonical mate by the authored route endomorphism. -/
noncomputable def authoredCanonicalMateRightTwist
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportViaBaseRoute input.context :=
  authoredSupportCanonicalMate input.context ≫
    authoredViaBaseRouteEndomorphism input

/-- The two evident authored twists coincide solely by mate naturality. -/
theorem authoredCanonicalMate_twists_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredCanonicalMateLeftTwist input =
      authoredCanonicalMateRightTwist input :=
  authoredSupportCanonicalMate_naturality
    input.context input.endpointAutomorphism

/-!
The exact producer type alone permits an implementation that never inspects
`input.authored`.  This definition is a negative interface witness, not an
accepted implementation of the G-110 authored comparison obligation.
-/
noncomputable def authoredComparisonIgnoringAuthored
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    AuthoredComparisonProducerSignature
      (authoredSupportDirectRouteFamily U)
      (authoredSupportViaBaseRouteFamily U) :=
  fun input => authoredSupportCanonicalMate input.context

@[simp]
theorem authoredComparisonIgnoringAuthored_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredComparisonIgnoringAuthored U input =
      authoredSupportCanonicalMate input.context := rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
