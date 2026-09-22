import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedEndpointBridge

/-! # The factor equation of the literal semantic Cartesian mate -/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

noncomputable local instance semanticLiteralMateAtomDecidableEq
    (U : AtomCarrier.{u}) : DecidableEq U.Atom := Classical.decEq _

/-- The semantic mate is the unique comparison factoring the base-first
two-edge exact route through the pulled-first route. -/
theorem semanticDerivedLiteralMateNorthwestIsoAt_hom_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq).hom.1 ≫
        semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq =
      semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq := by
  let baseLeg := semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq
  let pulledLeg := semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq
  let pointIso := semanticDerivedLiteralSourcePointIsoAt input Q k g endpoint_eq
  letI hpulled : (crossStageProjection U).IsStronglyCartesian
      ((crossStageProjection U).map pulledLeg) pulledLeg := by
    let first := semanticGeometryPullLift input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    let second := semanticGeometryPullLift input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    letI hfirst : (crossStageProjection U).IsStronglyCartesian
        first.base.base first := by
      simpa [first] using semanticGeometryPullLift_crossStageStronglyCartesian_map
        input.square.top
        (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    letI hsecond : (crossStageProjection U).IsStronglyCartesian
        second.base.base second := by
      simpa [second] using semanticGeometryPullLift_crossStageStronglyCartesian_map
        input.square.right
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    simpa [pulledLeg, semanticDerivedDirectPulledRouteLegAt,
      first, second, Functor.map_comp] using
      CategoryTheory.Functor.IsStronglyCartesian.comp
        (crossStageProjection U)
  have baseFac : (crossStageProjection U).map baseLeg =
      pointIso.hom ≫ (crossStageProjection U).map pulledLeg := by
    simp only [baseLeg, pulledLeg, pointIso,
      semanticDerivedDirectBaseRouteLegAt,
      semanticDerivedDirectPulledRouteLegAt,
      Functor.map_comp, semanticGeometryPullLift_crossStageProjection,
      semanticGeometryPullBaseHom, semanticDerivedLiteralSourcePointIsoAt,
      Iso.trans_hom, eqToIso.hom, Category.assoc]
    simp
    simpa only [Category.assoc] using congrArg
      (fun f => f ≫ eqToHom
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm)
      input.square.commutes
  have h := CategoryTheory.Functor.IsStronglyCartesian.fac
    (crossStageProjection U) ((crossStageProjection U).map pulledLeg)
    pulledLeg baseFac baseLeg
  simpa [semanticDerivedLiteralMateNorthwestIsoAt, baseLeg,
    pulledLeg, pointIso] using h

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
