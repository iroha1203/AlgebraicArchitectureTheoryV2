import ResearchLean.AG.FullGeometryNormalization.ExactDerivedCleavageComparison

/-!
# Lower-route coherence for the exact-derived cleavage comparison

This layer compares the literal exact two-edge routes with the lower maps of
the canonical-authored G-114 route legs.  The only endpoint identifications
used below are generated from the realized pullback comparison and the fiber
incidence equations; no point comparison or factorization certificate is
accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-! ## Direct-to-canonical source points -/

/-- The direct exact base-route source point identified with the independently
constructed canonical-authored base-route source point.  Both endpoint casts
are the stored fiber incidences, and the middle comparison is the inverse of
the realization-proven pullback-source isomorphism. -/
noncomputable def authoredExactDirectToCanonicalBaseSourcePointIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    packagePoint (authoredExactGeneratedMateSourceGeometryAt A z k g).1.core ≅
      packagePoint (authoredExactCanonicalBaseRouteFiberAt A z k g).1.core :=
  eqToIso (authoredExactGeneratedMateSourceGeometryAt A z k g).2 ≪≫
    (authoredExactPullbackSourceIso A).symm ≪≫
    eqToIso (authoredExactCanonicalBaseRouteFiberAt A z k g).2.symm

/-- The direct exact pulled-route source point identified with the
independently constructed canonical-authored pulled-route source point. -/
noncomputable def authoredExactDirectToCanonicalPulledSourcePointIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    packagePoint (authoredExactGeneratedMateTargetGeometryAt A z k g).1.core ≅
      packagePoint (authoredExactCanonicalPulledRouteFiberAt A z k g).1.core :=
  eqToIso (authoredExactGeneratedMateTargetGeometryAt A z k g).2 ≪≫
    (authoredExactPullbackSourceIso A).symm ≪≫
    eqToIso (authoredExactCanonicalPulledRouteFiberAt A z k g).2.symm

/-! ## Lower-route factorization -/

/-- The canonical-authored base source cast exposes the same exact lower
two-edge route as the direct construction.  The right-hand side is deliberately
kept with the direct geometry's stored incidence cast, so no heterogeneous
endpoint equality is hidden in the statement. -/
theorem authoredExactDirectBaseRoute_lower_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactDirectToCanonicalBaseSourcePointIsoAt A z k g).hom ≫
          eqToHom (authoredExactCanonicalBaseRouteFiberAt A z k g).2 ≫
          authoredExactMixedFst A ≫
          A.context.square.semantic.square.bottom =
      eqToHom (authoredExactGeneratedMateSourceGeometryAt A z k g).2 ≫
          A.context.square.semantic.square.left ≫
          A.context.square.semantic.square.bottom := by
  have hleft : (authoredExactPullbackSourceIso A).inv ≫
      authoredExactMixedFst A = A.context.square.semantic.square.left := by
    rw [← authoredExactPullbackSourceIso_hom_left A]
    simp
  simp [authoredExactDirectToCanonicalBaseSourcePointIsoAt, eqToIso]
  simpa only [Category.assoc] using congrArg
    (fun hom => hom ≫ A.context.square.semantic.square.bottom) hleft

/-- The canonical-authored pulled source cast exposes the same exact lower
two-edge route as the direct pulled-first construction.  The middle equality is
the realized pullback comparison square, not a caller-provided route witness. -/
theorem authoredExactDirectPulledRoute_lower_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactDirectToCanonicalPulledSourcePointIsoAt A z k g).hom ≫
          eqToHom (authoredExactCanonicalPulledRouteFiberAt A z k g).2 ≫
          authoredExactPulledComparison A ≫
          (authoredExactPullbackTargetIso A).hom ≫
          A.context.square.semantic.square.right =
      eqToHom (authoredExactGeneratedMateTargetGeometryAt A z k g).2 ≫
          A.context.square.semantic.square.top ≫
          A.context.square.semantic.square.right := by
  have hpulled : (authoredExactPullbackSourceIso A).inv ≫
        authoredExactPulledComparison A ≫
        (authoredExactPullbackTargetIso A).hom =
      A.context.square.semantic.square.top := by
    rw [← authoredExactPulledComparison_comparisonSquare A]
    simp
  simp [authoredExactDirectToCanonicalPulledSourcePointIsoAt, eqToIso]
  simpa only [Category.assoc] using congrArg
    (fun hom => hom ≫ A.context.square.semantic.square.right) hpulled

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
