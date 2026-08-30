import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCoefficientNormalization

/-!
# Finite cochains and the global mate equation on compatible routes

The two route transports constructed from the certificate-free compatible
input are now consumed as actual G-109 transport data.  Path factorization is
derived from the generator factor graphs, including its empty-path and
concatenation specializations.  The initial raw cochain on each route is then
defined by the G-109 upper obstruction API rather than accepted as input.

Canonical-comparator pullback, the resulting cochain image laws, and the
global upper-mate equation are successor obligations.  No route equation,
solution, cochain, or comparator compatibility is accepted from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The generated base route, forgotten to the G-109 transport vocabulary. -/
noncomputable def generatedBaseRouteData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerTransportData.{u, v} P U :=
  input.generatedBaseRouteTransport.toTwoLayerTransportData

/-- The independently generated pulled route in the G-109 vocabulary. -/
noncomputable def generatedPulledRouteData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerTransportData.{u, v} P U :=
  input.generatedPulledRouteTransport.toTwoLayerTransportData

/-- The authored source transport, forgotten to the G-109 vocabulary. -/
noncomputable def compatibleSourceRouteData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerTransportData.{u, v} P U :=
  input.sourceTransport.toTwoLayerTransportData

/-- Every generated base-route path factors its target leg through the same
authored source path.  This is derived by induction from the generator factor
law rather than stored as route naturality. -/
theorem generatedBaseRoutePath_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteData.lift.pathLift path))
        (input.generatedBaseRouteLegAt j) =
      RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift path)) := by
  induction path with
  | nil vertex =>
      change (𝟙 (⟨input.generatedBaseRouteGeometryAt vertex⟩ :
          RefinementGeometryCategory U)) ≫ input.generatedBaseRouteLegAt vertex =
        input.generatedBaseRouteLegAt vertex ≫
          𝟙 (⟨(input.sourceGeometry vertex).package⟩ :
            RefinementGeometryCategory U)
      rw [Category.id_comp, Category.comp_id]
  | cons edge tail inductionHypothesis =>
      change (((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteFixedGeometryEdge edge)) ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.generatedBaseRouteData.lift.pathLift tail))) ≫
          input.generatedBaseRouteLegAt _ =
        input.generatedBaseRouteLegAt _ ≫
          (((exactGeometryToRefinementGeometry U).map
            (input.sourceTransport.edgeLift edge)) ≫
            ((exactGeometryToRefinementGeometry U).map
              (input.compatibleSourceRouteData.lift.pathLift tail)))
      calc
        _ = ((exactGeometryToRefinementGeometry U).map
              (input.generatedBaseRouteFixedGeometryEdge edge)) ≫
            (((exactGeometryToRefinementGeometry U).map
              (input.generatedBaseRouteData.lift.pathLift tail)) ≫
              input.generatedBaseRouteLegAt _) := Category.assoc _ _ _
        _ = ((exactGeometryToRefinementGeometry U).map
              (input.generatedBaseRouteFixedGeometryEdge edge)) ≫
            (input.generatedBaseRouteLegAt _ ≫
              ((exactGeometryToRefinementGeometry U).map
                (input.compatibleSourceRouteData.lift.pathLift tail))) :=
          congrArg _ inductionHypothesis
        _ = (((exactGeometryToRefinementGeometry U).map
              (input.generatedBaseRouteFixedGeometryEdge edge)) ≫
              input.generatedBaseRouteLegAt _) ≫
            ((exactGeometryToRefinementGeometry U).map
              (input.compatibleSourceRouteData.lift.pathLift tail)) :=
          (Category.assoc _ _ _).symm
        _ = (input.generatedBaseRouteLegAt _ ≫
              ((exactGeometryToRefinementGeometry U).map
                (input.sourceTransport.edgeLift edge))) ≫
            ((exactGeometryToRefinementGeometry U).map
              (input.compatibleSourceRouteData.lift.pathLift tail)) := by
          exact congrArg
            (fun hom => hom ≫
              (exactGeometryToRefinementGeometry U).map
                (input.compatibleSourceRouteData.lift.pathLift tail))
            (input.generatedBaseRouteGeometryEdge_fac edge)
        _ = _ := Category.assoc _ _ _

/-- Every generated pulled-route path has the analogous independently derived
factorization through its own route leg. -/
theorem generatedPulledRoutePath_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteData.lift.pathLift path))
        (input.generatedPulledRouteLegAt j) =
      RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift path)) := by
  induction path with
  | nil vertex =>
      change (𝟙 (⟨input.generatedPulledRouteGeometryAt vertex⟩ :
          RefinementGeometryCategory U)) ≫ input.generatedPulledRouteLegAt vertex =
        input.generatedPulledRouteLegAt vertex ≫
          𝟙 (⟨(input.sourceGeometry vertex).package⟩ :
            RefinementGeometryCategory U)
      rw [Category.id_comp, Category.comp_id]
  | cons edge tail inductionHypothesis =>
      change (((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteFixedGeometryEdge edge)) ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.generatedPulledRouteData.lift.pathLift tail))) ≫
          input.generatedPulledRouteLegAt _ =
        input.generatedPulledRouteLegAt _ ≫
          (((exactGeometryToRefinementGeometry U).map
            (input.sourceTransport.edgeLift edge)) ≫
            ((exactGeometryToRefinementGeometry U).map
              (input.compatibleSourceRouteData.lift.pathLift tail)))
      calc
        _ = ((exactGeometryToRefinementGeometry U).map
              (input.generatedPulledRouteFixedGeometryEdge edge)) ≫
            (((exactGeometryToRefinementGeometry U).map
              (input.generatedPulledRouteData.lift.pathLift tail)) ≫
              input.generatedPulledRouteLegAt _) := Category.assoc _ _ _
        _ = ((exactGeometryToRefinementGeometry U).map
              (input.generatedPulledRouteFixedGeometryEdge edge)) ≫
            (input.generatedPulledRouteLegAt _ ≫
              ((exactGeometryToRefinementGeometry U).map
                (input.compatibleSourceRouteData.lift.pathLift tail))) :=
          congrArg _ inductionHypothesis
        _ = (((exactGeometryToRefinementGeometry U).map
              (input.generatedPulledRouteFixedGeometryEdge edge)) ≫
              input.generatedPulledRouteLegAt _) ≫
            ((exactGeometryToRefinementGeometry U).map
              (input.compatibleSourceRouteData.lift.pathLift tail)) :=
          (Category.assoc _ _ _).symm
        _ = (input.generatedPulledRouteLegAt _ ≫
              ((exactGeometryToRefinementGeometry U).map
                (input.sourceTransport.edgeLift edge))) ≫
            ((exactGeometryToRefinementGeometry U).map
              (input.compatibleSourceRouteData.lift.pathLift tail)) := by
          exact congrArg
            (fun hom => hom ≫
              (exactGeometryToRefinementGeometry U).map
                (input.compatibleSourceRouteData.lift.pathLift tail))
            (input.generatedPulledRouteGeometryEdge_fac edge)
        _ = _ := Category.assoc _ _ _

/-- Empty-path compatibility on the base route is the literal two-sided unit
factorization of its generated leg. -/
theorem generatedBaseRoutePath_nil_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteData.lift.pathLift (.nil i)))
        (input.generatedBaseRouteLegAt i) =
      RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift (.nil i))) := by
  change (𝟙 (⟨input.generatedBaseRouteGeometryAt i⟩ :
      RefinementGeometryCategory U)) ≫ input.generatedBaseRouteLegAt i =
    input.generatedBaseRouteLegAt i ≫
      𝟙 (⟨(input.sourceGeometry i).package⟩ :
        RefinementGeometryCategory U)
  rw [Category.id_comp, Category.comp_id]

/-- Empty-path compatibility is proved separately for the pulled route. -/
theorem generatedPulledRoutePath_nil_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteData.lift.pathLift (.nil i)))
        (input.generatedPulledRouteLegAt i) =
      RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift (.nil i))) := by
  change (𝟙 (⟨input.generatedPulledRouteGeometryAt i⟩ :
      RefinementGeometryCategory U)) ≫ input.generatedPulledRouteLegAt i =
    input.generatedPulledRouteLegAt i ≫
      𝟙 (⟨(input.sourceGeometry i).package⟩ :
        RefinementGeometryCategory U)
  rw [Category.id_comp, Category.comp_id]

/-- Concatenated base paths satisfy the two-stage factor graph, exposing both
path pieces instead of merely aliasing `pathLift_append`. -/
theorem generatedBaseRoutePath_append_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j l : P.Vertex} (first : P.Path i j) (second : P.Path j l) :
    (((exactGeometryToRefinementGeometry U).map
        (input.generatedBaseRouteData.lift.pathLift first)) ≫
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedBaseRouteData.lift.pathLift second))) ≫
        input.generatedBaseRouteLegAt l =
      input.generatedBaseRouteLegAt i ≫
        (((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift first)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second))) := by
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteData.lift.pathLift first)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteData.lift.pathLift second)) ≫
          input.generatedBaseRouteLegAt l) := Category.assoc _ _ _
    _ = ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteData.lift.pathLift first)) ≫
        (input.generatedBaseRouteLegAt j ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.compatibleSourceRouteData.lift.pathLift second))) :=
      congrArg _ (input.generatedBaseRoutePath_fac second)
    _ = (((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteData.lift.pathLift first)) ≫
          input.generatedBaseRouteLegAt j) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second)) :=
      (Category.assoc _ _ _).symm
    _ = (input.generatedBaseRouteLegAt i ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.compatibleSourceRouteData.lift.pathLift first))) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second)) :=
      congrArg (fun hom => hom ≫
        (exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second))
        (input.generatedBaseRoutePath_fac first)
    _ = _ := Category.assoc _ _ _

/-- The pulled route has its own concatenated two-stage factor graph. -/
theorem generatedPulledRoutePath_append_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j l : P.Vertex} (first : P.Path i j) (second : P.Path j l) :
    (((exactGeometryToRefinementGeometry U).map
        (input.generatedPulledRouteData.lift.pathLift first)) ≫
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedPulledRouteData.lift.pathLift second))) ≫
        input.generatedPulledRouteLegAt l =
      input.generatedPulledRouteLegAt i ≫
        (((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift first)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second))) := by
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteData.lift.pathLift first)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteData.lift.pathLift second)) ≫
          input.generatedPulledRouteLegAt l) := Category.assoc _ _ _
    _ = ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteData.lift.pathLift first)) ≫
        (input.generatedPulledRouteLegAt j ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.compatibleSourceRouteData.lift.pathLift second))) :=
      congrArg _ (input.generatedPulledRoutePath_fac second)
    _ = (((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteData.lift.pathLift first)) ≫
          input.generatedPulledRouteLegAt j) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second)) :=
      (Category.assoc _ _ _).symm
    _ = (input.generatedPulledRouteLegAt i ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.compatibleSourceRouteData.lift.pathLift first))) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second)) :=
      congrArg (fun hom => hom ≫
        (exactGeometryToRefinementGeometry U).map
          (input.compatibleSourceRouteData.lift.pathLift second))
        (input.generatedPulledRoutePath_fac first)
    _ = _ := Category.assoc _ _ _

/-- Initial G-109 raw cochain of the compatible source transport. -/
noncomputable def compatibleSourceRawDefectCochain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    UpperDefectCochain input.compatibleSourceRouteData :=
  upperRawDefectCochain input.compatibleSourceRouteData 1

/-- Initial G-109 raw cochain derived from the generated base transport. -/
noncomputable def generatedBaseRouteRawDefectCochain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    UpperDefectCochain input.generatedBaseRouteData :=
  upperRawDefectCochain input.generatedBaseRouteData 1

/-- Initial G-109 raw cochain derived independently from the pulled transport. -/
noncomputable def generatedPulledRouteRawDefectCochain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    UpperDefectCochain input.generatedPulledRouteData :=
  upperRawDefectCochain input.generatedPulledRouteData 1

/-- Evaluation of the generated base cochain is the actual G-109 raw defect. -/
@[simp] theorem generatedBaseRouteRawDefectCochain_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.generatedBaseRouteRawDefectCochain cell =
      upperRawTwoCellDefect input.generatedBaseRouteData 1 cell := rfl

/-- Evaluation of the pulled cochain is its independently generated raw defect. -/
@[simp] theorem generatedPulledRouteRawDefectCochain_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.generatedPulledRouteRawDefectCochain cell =
      upperRawTwoCellDefect input.generatedPulledRouteData 1 cell := rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
