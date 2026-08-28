import ResearchLean.AG.DiagnosticConservativity.PentagonDownstreamCompatibility
import ResearchLean.AG.DiagnosticConservativity.CompositionPropositionCompatibility
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoTransport

/-!
# G-113 revision 2 whole-pentagon proposition compatibility

The whole-pentagon mate comparisons carry direct three-arrow endpoint and
reselection transport to successive transport.  Their generated inverse
reselection routes then identify coherence for every direct-target
reselection, and transport coherentizability witnesses in both directions to
identify obstruction vanishing.

The proposition proofs retain the actual left and right whole-pentagon
comparators.  They do not obtain the result merely from the all-hom coherence
or vanishing equivalences, and they do not restrict arbitrary target
reselections to the image of a selected source witness.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-- Cycle 23 API lemma for G-113(h), at endpoint layer (b): the generated left
whole-pentagon comparison carries direct three-arrow transport of every source
automorphism to successive transport.  No compatibility equation is supplied. -/
theorem indexedDiagnosticPentagonMateLeftEndpointEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    indexedDiagnosticPentagonMateLeftEndpointEquivalence
        first second third source vertex
        (indexedDiagnosticEndpointEquivalence
          ((first.comp second).comp third) source vertex automorphism) =
      indexedDiagnosticEndpointEquivalence third
        (second.transportedInterpretation
          (first.transportedInterpretation source)) vertex
        (indexedDiagnosticEndpointEquivalence second
          (first.transportedInterpretation source) vertex
          (indexedDiagnosticEndpointEquivalence first source vertex
            automorphism)) := by
  rw [indexedDiagnosticPentagonMateLeftEndpointEquivalence_eq_g111]
  rw [indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply]
  rw [indexedDiagnosticPentagonG111LeftEndpointEquivalence_apply]
  rw [coreFiberPentagonLeftRouteIso_app_trans]
  rw [packageFiberAutMulEquivOfCoreFiberIso_trans]
  have firstStage :=
    indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
      (first.comp second) third source vertex automorphism
  rw [indexedDiagnosticCompositionMateEndpointCompositorEquivalence_eq_g111]
    at firstStage
  rw [indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply] at firstStage
  rw [indexedDiagnosticCompositionEndpointCompositorEquivalence_apply] at firstStage
  simp only [IndexedBaseDiagramHom.comp_app] at firstStage
  have mappedFirstStage := congrArg
    (packageFiberAutMulEquivOfCoreFiberIso
      ((CategoryTheory.Functor.isoWhiskerRight
        (coreFiberCompositor (first.app vertex) (second.app vertex))
        (coreFiberTransportFunctor (third.app vertex))).app
          (source.fiberPackage vertex))) firstStage
  refine mappedFirstStage.trans ?_
  have whiskerNaturality := coreFiberFunctorPackageAutHom_iso_naturality
    (CategoryTheory.Functor.isoWhiskerRight
      (coreFiberCompositor (first.app vertex) (second.app vertex))
      (coreFiberTransportFunctor (third.app vertex)))
    (source.fiberPackage vertex) automorphism
  have directComp := congrArg (fun action => action automorphism)
    (coreFiberFunctorPackageAutHom_comp
      (coreFiberTransportFunctor (first.app vertex ≫ second.app vertex))
      (coreFiberTransportFunctor (third.app vertex))
      (source.fiberPackage vertex))
  have successiveComp := congrArg (fun action => action automorphism)
    (coreFiberFunctorPackageAutHom_comp
      (coreFiberTransportFunctor (first.app vertex) ⋙
        coreFiberTransportFunctor (second.app vertex))
      (coreFiberTransportFunctor (third.app vertex))
      (source.fiberPackage vertex))
  have pairComp := congrArg (fun action => action automorphism)
    (coreFiberFunctorPackageAutHom_comp
      (coreFiberTransportFunctor (first.app vertex))
      (coreFiberTransportFunctor (second.app vertex))
      (source.fiberPackage vertex))
  change packageFiberAutMulEquivOfCoreFiberIso
      ((CategoryTheory.Functor.isoWhiskerRight
        (coreFiberCompositor (first.app vertex) (second.app vertex))
        (coreFiberTransportFunctor (third.app vertex))).app
          (source.fiberPackage vertex))
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (third.app vertex))
        ((coreFiberTransportFunctor
          (first.app vertex ≫ second.app vertex)).obj
            (source.fiberPackage vertex))
        (coreFiberFunctorPackageAutHom
          (coreFiberTransportFunctor (first.app vertex ≫ second.app vertex))
          (source.fiberPackage vertex) automorphism)) =
    coreFiberFunctorPackageAutHom
      (coreFiberTransportFunctor (third.app vertex))
      ((coreFiberTransportFunctor (first.app vertex) ⋙
        coreFiberTransportFunctor (second.app vertex)).obj
          (source.fiberPackage vertex))
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (second.app vertex))
        ((coreFiberTransportFunctor (first.app vertex)).obj
          (source.fiberPackage vertex))
        (coreFiberFunctorPackageAutHom
          (coreFiberTransportFunctor (first.app vertex))
          (source.fiberPackage vertex) automorphism))
  calc
    _ = packageFiberAutMulEquivOfCoreFiberIso
        ((CategoryTheory.Functor.isoWhiskerRight
          (coreFiberCompositor (first.app vertex) (second.app vertex))
          (coreFiberTransportFunctor (third.app vertex))).app
            (source.fiberPackage vertex))
        (coreFiberFunctorPackageAutHom
          (coreFiberTransportFunctor
              (first.app vertex ≫ second.app vertex) ⋙
            coreFiberTransportFunctor (third.app vertex))
          (source.fiberPackage vertex) automorphism) :=
      congrArg
        (packageFiberAutMulEquivOfCoreFiberIso
          ((CategoryTheory.Functor.isoWhiskerRight
            (coreFiberCompositor (first.app vertex) (second.app vertex))
            (coreFiberTransportFunctor (third.app vertex))).app
              (source.fiberPackage vertex))) directComp.symm
    _ = coreFiberFunctorPackageAutHom
        ((coreFiberTransportFunctor (first.app vertex) ⋙
          coreFiberTransportFunctor (second.app vertex)) ⋙
            coreFiberTransportFunctor (third.app vertex))
        (source.fiberPackage vertex) automorphism := whiskerNaturality
    _ = coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (third.app vertex))
        ((coreFiberTransportFunctor (first.app vertex) ⋙
          coreFiberTransportFunctor (second.app vertex)).obj
            (source.fiberPackage vertex))
        (coreFiberFunctorPackageAutHom
          (coreFiberTransportFunctor (first.app vertex) ⋙
            coreFiberTransportFunctor (second.app vertex))
          (source.fiberPackage vertex) automorphism) := successiveComp
    _ = _ := congrArg
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (third.app vertex))
        ((coreFiberTransportFunctor (first.app vertex) ⋙
          coreFiberTransportFunctor (second.app vertex)).obj
            (source.fiberPackage vertex))) pairComp

/-- Cycle 23 API lemma for G-113(h), at endpoint layer (b): the cast-bearing
right whole-pentagon comparison has the same generated application equation. -/
theorem indexedDiagnosticPentagonMateRightEndpointEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    indexedDiagnosticPentagonMateRightEndpointEquivalence
        first second third source vertex
        (indexedDiagnosticEndpointEquivalence
          ((first.comp second).comp third) source vertex automorphism) =
      indexedDiagnosticEndpointEquivalence third
        (second.transportedInterpretation
          (first.transportedInterpretation source)) vertex
        (indexedDiagnosticEndpointEquivalence second
          (first.transportedInterpretation source) vertex
          (indexedDiagnosticEndpointEquivalence first source vertex
            automorphism)) := by
  rw [← indexedDiagnosticPentagonMateEndpointEquivalence_eq
    first second third source vertex]
  exact indexedDiagnosticPentagonMateLeftEndpointEquivalence_transport_apply
    first second third source vertex automorphism

/-- Cycle 23 G-113(h)/(c) left application equation on every source
reselection; all edge coordinates are transported by the generated comparator. -/
theorem indexedDiagnosticPentagonMateLeftReselectionEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    indexedDiagnosticPentagonMateLeftReselectionEquivalence
        first second third source
        (indexedDiagnosticReselectionEquivalence
          ((first.comp second).comp third) source reselection) =
      indexedDiagnosticReselectionEquivalence third
        (second.transportedInterpretation
          (first.transportedInterpretation source))
        (indexedDiagnosticReselectionEquivalence second
          (first.transportedInterpretation source)
          (indexedDiagnosticReselectionEquivalence first source
            reselection)) := by
  funext i j edge
  change indexedDiagnosticPentagonMateLeftEndpointEquivalence
      first second third source j
      (indexedDiagnosticEndpointEquivalence
        ((first.comp second).comp third) source j (reselection i j edge)) =
    indexedDiagnosticEndpointEquivalence third
      (second.transportedInterpretation
        (first.transportedInterpretation source)) j
      (indexedDiagnosticEndpointEquivalence second
        (first.transportedInterpretation source) j
        (indexedDiagnosticEndpointEquivalence first source j
          (reselection i j edge)))
  exact indexedDiagnosticPentagonMateLeftEndpointEquivalence_transport_apply
    first second third source j (reselection i j edge)

/-- Cycle 23 G-113(h)/(c) right application equation on every source
reselection, retaining the cast-bearing right whole route. -/
theorem indexedDiagnosticPentagonMateRightReselectionEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    indexedDiagnosticPentagonMateRightReselectionEquivalence
        first second third source
        (indexedDiagnosticReselectionEquivalence
          ((first.comp second).comp third) source reselection) =
      indexedDiagnosticReselectionEquivalence third
        (second.transportedInterpretation
          (first.transportedInterpretation source))
        (indexedDiagnosticReselectionEquivalence second
          (first.transportedInterpretation source)
          (indexedDiagnosticReselectionEquivalence first source
            reselection)) := by
  rw [← indexedDiagnosticPentagonMateReselectionEquivalence_eq
    first second third source]
  exact indexedDiagnosticPentagonMateLeftReselectionEquivalence_transport_apply
    first second third source reselection

/-- Cycle 23 G-113(h)/(c) inverse law for the left comparator on every
direct-target reselection.  The inverse witness is generated, not supplied. -/
theorem indexedDiagnosticPentagonMateLeftReselectionEquivalence_inverse
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      (((first.comp second).comp third).transportedInterpretation source)) :
    first.inverseTransportedReselection source
        (second.inverseTransportedReselection
          (first.transportedInterpretation source)
          (third.inverseTransportedReselection
            (second.transportedInterpretation
              (first.transportedInterpretation source))
            (indexedDiagnosticPentagonMateLeftReselectionEquivalence
              first second third source directReselection))) =
      ((first.comp second).comp third).inverseTransportedReselection source
        directReselection := by
  let sourceReselection :=
    (indexedDiagnosticReselectionEquivalence
      ((first.comp second).comp third) source).symm directReselection
  have directRoundTrip :
      indexedDiagnosticReselectionEquivalence
          ((first.comp second).comp third) source sourceReselection =
        directReselection := by
    exact (indexedDiagnosticReselectionEquivalence
      ((first.comp second).comp third) source).apply_symm_apply directReselection
  have pentagonEquation :=
    indexedDiagnosticPentagonMateLeftReselectionEquivalence_transport_apply
      first second third source sourceReselection
  rw [directRoundTrip] at pentagonEquation
  change (indexedDiagnosticReselectionEquivalence first source).symm
      ((indexedDiagnosticReselectionEquivalence second
        (first.transportedInterpretation source)).symm
        ((indexedDiagnosticReselectionEquivalence third
          (second.transportedInterpretation
            (first.transportedInterpretation source))).symm
          (indexedDiagnosticPentagonMateLeftReselectionEquivalence
            first second third source directReselection))) = sourceReselection
  rw [pentagonEquation]
  simp only [MulEquiv.symm_apply_apply]

/-- Cycle 23 G-113(h)/(c) inverse law for the cast-bearing right comparator on
every direct-target reselection. -/
theorem indexedDiagnosticPentagonMateRightReselectionEquivalence_inverse
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      (((first.comp second).comp third).transportedInterpretation source)) :
    first.inverseTransportedReselection source
        (second.inverseTransportedReselection
          (first.transportedInterpretation source)
          (third.inverseTransportedReselection
            (second.transportedInterpretation
              (first.transportedInterpretation source))
            (indexedDiagnosticPentagonMateRightReselectionEquivalence
              first second third source directReselection))) =
      ((first.comp second).comp third).inverseTransportedReselection source
        directReselection := by
  rw [← indexedDiagnosticPentagonMateReselectionEquivalence_eq
    first second third source]
  exact indexedDiagnosticPentagonMateLeftReselectionEquivalence_inverse
    first second third source directReselection

/-- Cycle 23 main theorem for G-113(h), at coherence layer (d): every direct
target reselection is coherent iff its generated left whole-pentagon image is. -/
theorem indexedDiagnosticPentagonCoherentAt_mate_left_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      (((first.comp second).comp third).transportedInterpretation source)) :
    (((first.comp second).comp third).transportedInterpretation source).IndexedCoherentAt
        directReselection ↔
      (third.transportedInterpretation
        (second.transportedInterpretation
          (first.transportedInterpretation source))).IndexedCoherentAt
        (indexedDiagnosticPentagonMateLeftReselectionEquivalence
          first second third source directReselection) := by
  calc
    _ ↔ source.IndexedCoherentAt
        (((first.comp second).comp third).inverseTransportedReselection source
          directReselection) :=
      indexedCoherentAt_inverseTransport_iff
        ((first.comp second).comp third) source directReselection
    _ ↔ source.IndexedCoherentAt
        (first.inverseTransportedReselection source
          (second.inverseTransportedReselection
            (first.transportedInterpretation source)
            (third.inverseTransportedReselection
              (second.transportedInterpretation
                (first.transportedInterpretation source))
              (indexedDiagnosticPentagonMateLeftReselectionEquivalence
                first second third source directReselection)))) := by
      rw [indexedDiagnosticPentagonMateLeftReselectionEquivalence_inverse]
    _ ↔ (first.transportedInterpretation source).IndexedCoherentAt
        (second.inverseTransportedReselection
          (first.transportedInterpretation source)
          (third.inverseTransportedReselection
            (second.transportedInterpretation
              (first.transportedInterpretation source))
            (indexedDiagnosticPentagonMateLeftReselectionEquivalence
              first second third source directReselection))) :=
      (indexedCoherentAt_inverseTransport_iff first source _).symm
    _ ↔ (second.transportedInterpretation
        (first.transportedInterpretation source)).IndexedCoherentAt
        (third.inverseTransportedReselection
          (second.transportedInterpretation
            (first.transportedInterpretation source))
          (indexedDiagnosticPentagonMateLeftReselectionEquivalence
            first second third source directReselection)) :=
      (indexedCoherentAt_inverseTransport_iff second
        (first.transportedInterpretation source) _).symm
    _ ↔ _ :=
      (indexedCoherentAt_inverseTransport_iff third
        (second.transportedInterpretation
          (first.transportedInterpretation source)) _).symm

/-- Cycle 23 main theorem for G-113(h), at coherence layer (d): every direct
target reselection is coherent iff its cast-bearing right whole-pentagon image is. -/
theorem indexedDiagnosticPentagonCoherentAt_mate_right_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      (((first.comp second).comp third).transportedInterpretation source)) :
    (((first.comp second).comp third).transportedInterpretation source).IndexedCoherentAt
        directReselection ↔
      (third.transportedInterpretation
        (second.transportedInterpretation
          (first.transportedInterpretation source))).IndexedCoherentAt
        (indexedDiagnosticPentagonMateRightReselectionEquivalence
          first second third source directReselection) := by
  rw [← indexedDiagnosticPentagonMateReselectionEquivalence_eq
    first second third source]
  exact indexedDiagnosticPentagonCoherentAt_mate_left_iff
    first second third source directReselection

/-- Cycle 23 main theorem for G-113(h), at obstruction layer (e): direct and
successive three-arrow transport have equivalent obstruction vanishing.  The
forward coherentizability witness uses the left comparator and the reverse
witness uses the right comparator, with neither witness caller-supplied. -/
theorem indexedDiagnosticPentagonTransportObstructionVanishes_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    TransportObstructionVanishes
        (((first.comp second).comp third).transportedInterpretation source).toAdmissibleTransportData ↔
      TransportObstructionVanishes
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨directReselection, directCoherent⟩
    have directIndexed :
        (((first.comp second).comp third).transportedInterpretation source).IndexedCoherentAt
          directReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (((first.comp second).comp third).transportedInterpretation source)
        directReselection).2 directCoherent
    let successiveReselection :=
      indexedDiagnosticPentagonMateLeftReselectionEquivalence
        first second third source directReselection
    have successiveIndexed :
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))).IndexedCoherentAt
              successiveReselection := by
      exact (indexedDiagnosticPentagonCoherentAt_mate_left_iff
        first second third source directReselection).1 directIndexed
    exact ⟨successiveReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))) successiveReselection).1
        successiveIndexed⟩
  · rintro ⟨successiveReselection, successiveCoherent⟩
    have successiveIndexed :
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))).IndexedCoherentAt
              successiveReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))) successiveReselection).2
        successiveCoherent
    let directReselection :=
      (indexedDiagnosticPentagonMateRightReselectionEquivalence
        first second third source).symm successiveReselection
    have directIndexed :
        (((first.comp second).comp third).transportedInterpretation source).IndexedCoherentAt
          directReselection := by
      apply (indexedDiagnosticPentagonCoherentAt_mate_right_iff
        first second third source directReselection).2
      simpa only [directReselection,
        (indexedDiagnosticPentagonMateRightReselectionEquivalence
          first second third source).apply_symm_apply] using successiveIndexed
    exact ⟨directReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (((first.comp second).comp third).transportedInterpretation source)
        directReselection).1 directIndexed⟩

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
