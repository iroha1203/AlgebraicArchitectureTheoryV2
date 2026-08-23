import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredComparisonUnderdetermination
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCleavageWitnesses

/-!
# A nonidentity authored-table witness for the comparison interface

The original finite authored-support fixture deliberately uses the identity
comparator.  This companion fixture keeps its identity Beck--Chevalley square
and nonempty diagnostic support but replaces the support package by the
reviewed four-axis package and the raw comparator by the visible axis swap.
It shows that the authored endpoint endomorphism surface is not restricted to
the identity case.  It does not select an authored cross-route comparison.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

local instance finiteAuthoredAxisSwapAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The visible four-axis swap as a package-fiber automorphism. -/
noncomputable def finiteAuthoredAxisSwap :
    PackageFiberAut finiteReindexFourAxisCore :=
  ⟨finiteCleavageAxisPermutationIso finiteReindexAxisSwap, rfl⟩

/-- Identity diagnostic edge lifts on the four-axis support package. -/
noncomputable def finiteAuthoredAxisSwapLiftData :
    AdmissibleLiftData finiteBCDiagnosticGeometry FiniteModel.carrier where
  package := fun _ => finiteReindexFourAxisCore
  edgeLift := fun _ => PackageTotalHom.id finiteReindexFourAxisCore
  edgeStrong := by
    intro source target edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 (packagePoint finiteReindexFourAxisCore))
        (Iso.refl finiteReindexFourAxisCore).hom :=
      CategoryTheory.IsHomLift.id rfl
    simpa using
      (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
        (packageProjection FiniteModel.carrier)
        (𝟙 (packagePoint finiteReindexFourAxisCore))
        (Iso.refl finiteReindexFourAxisCore))

/-- G-106 transport data whose unique authored comparator is the axis swap. -/
noncomputable def finiteAuthoredAxisSwapTransportData :
    AdmissibleTransportData finiteBCDiagnosticGeometry FiniteModel.carrier where
  lift := finiteAuthoredAxisSwapLiftData
  twoCellBase := by
    intro face
    cases face
    change (PackageTotalHom.id finiteReindexFourAxisCore).base =
      ((PackageTotalHom.id finiteReindexFourAxisCore).comp
        (PackageTotalHom.id finiteReindexFourAxisCore)).base
    rw [show (PackageTotalHom.id finiteReindexFourAxisCore).comp
        (PackageTotalHom.id finiteReindexFourAxisCore) =
      PackageTotalHom.id finiteReindexFourAxisCore by
        exact @Category.comp_id
          (AATCorePackage FiniteModel.carrier)
          (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
          finiteReindexFourAxisCore finiteReindexFourAxisCore
          (PackageTotalHom.id finiteReindexFourAxisCore)]
  comparator := fun _ => finiteAuthoredAxisSwap

/-- The axis-swap transport data interpreted on the same identity BC square. -/
noncomputable def finiteAuthoredAxisSwapInterpretation :
    BCDiagnosticInterpretation FiniteModel.carrier
      finiteAuthoredSupportSquare.semantic where
  data := by
    simpa [finiteAuthoredSupportSquare, realizableSquareOf,
      finiteAuthoredSupportBCPresentation, bcPresentationOfCospan,
      toSemanticBC, finiteBCDiagnosticPresentation] using
        finiteAuthoredAxisSwapTransportData

/-- Every axis-swap authored endpoint is the square's southwest vertex. -/
theorem finiteAuthoredAxisSwap_endpoint_eq
    (face : finiteAuthoredSupportSquare.semantic.diagnostic.TwoCell) :
    (packageProjection FiniteModel.carrier).obj
        (finiteAuthoredAxisSwapInterpretation.data.lift.package
          (finiteAuthoredSupportSquare.semantic.diagnostic.twoTarget face)) =
      finiteAuthoredSupportSquare.semantic.square.southwest := by
  cases face
  rfl

/-- A nonempty authored-datum square carrying the nonidentity axis swap. -/
noncomputable def finiteAuthoredAxisSwapDatumSquare :
    AuthoredBCDatumSquare FiniteModel.carrier where
  context :=
    { square := finiteAuthoredSupportSquare
      lift := finiteAuthoredAxisSwapLiftData
      endpoint_eq := finiteAuthoredAxisSwap_endpoint_eq }
  twoCellBase := finiteAuthoredAxisSwapTransportData.twoCellBase
  authored :=
    { comparator := fun _ => finiteAuthoredAxisSwap }

/-- Its unique endpoint component is the visible axis-swap total morphism. -/
theorem finiteAuthoredAxisSwap_component :
    (finiteAuthoredAxisSwapDatumSquare.endpointAutomorphism.app
        (Discrete.mk FiniteBCDiagnosticCell.cell)).1 =
      finiteCleavageAxisPermutationTotal finiteReindexAxisSwap := by
  rfl

/-- The unique raw authored component is genuinely nonidentity. -/
theorem finiteAuthoredAxisSwap_component_ne_identity :
    finiteAuthoredAxisSwapDatumSquare.endpointAutomorphism.app
        (Discrete.mk FiniteBCDiagnosticCell.cell) ≠
      𝟙 (finiteAuthoredAxisSwapDatumSquare.context.supportFunctor.obj
        (Discrete.mk FiniteBCDiagnosticCell.cell)) := by
  intro equality
  have totalEquality := congrArg Subtype.val equality
  have axisEquality := congrArg
    (fun hom : PackageTotalHom finiteReindexFourAxisCore
        finiteReindexFourAxisCore =>
      hom.upper.axisMap finiteReindexAxisZero) totalEquality
  have swapped : finiteReindexAxisOne = finiteReindexAxisZero := by
    simpa [finiteAuthoredAxisSwap_component,
      finiteCleavageAxisPermutationTotal, finiteReindexAxisSwap,
      finiteReindexAxisZero, finiteReindexAxisOne] using axisEquality
  exact finiteReindexAxisZero_ne_one swapped.symm

/-- The raw authored endpoint endotransformation is genuinely nonidentity. -/
theorem finiteAuthoredAxisSwap_endpointAutomorphism_ne_identity :
    finiteAuthoredAxisSwapDatumSquare.endpointAutomorphism ≠
      𝟙 finiteAuthoredAxisSwapDatumSquare.context.supportFunctor := by
  intro equality
  exact finiteAuthoredAxisSwap_component_ne_identity
    (NatTrans.congr_app equality (Discrete.mk FiniteBCDiagnosticCell.cell))

/-!
Transport over an identity base map reflects nonidentity vertical morphisms.
This local API lemma lets the witness distinguish the raw route twist from the
unmodified canonical comparison without assuming functor faithfulness.
-/
private theorem coreFiberTransport_map_ne_id_of_ne_id
    {U : AtomCarrier} {X Y : ExtractionInstance U} (base : X ⟶ Y)
    [IsIso base] {P : CoreFiber X}
    (hom : P ⟶ P) (hom_ne : hom ≠ 𝟙 P) :
    (coreFiberTransportFunctor base).map hom ≠
      𝟙 ((coreFiberTransportFunctor base).obj P) := by
  intro map_eq
  let lift := coreFiberLift base P
  letI : (packageProjection U).IsStronglyCocartesian
      base lift := coreFiberLift_isStronglyCocartesian base P
  letI : IsIso lift :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (packageProjection U) base lift
  have factor := coreFiberTransportMap_fac base hom
  apply hom_ne
  apply CategoryTheory.Functor.Fiber.hom_ext
  rw [← cancel_mono lift]
  calc
    hom.1 ≫ lift = lift ≫ (coreFiberTransportMap base hom).1 :=
      factor.symm
    _ = lift ≫ CategoryTheory.Functor.Fiber.fiberInclusion.map
        (𝟙 ((coreFiberTransportFunctor base).obj P)) := by
      exact congrArg (fun mapped => lift ≫
        CategoryTheory.Functor.Fiber.fiberInclusion.map mapped) map_eq
    _ = CategoryTheory.Functor.Fiber.fiberInclusion.map (𝟙 P) ≫
        lift := by
      exact (Category.comp_id lift).trans (Category.id_comp lift).symm

/-- Selected reindexing over an invertible base reflects nonidentity maps. -/
private theorem selectedCoreFiberReindex_map_ne_id_of_ne_id
    {U : AtomCarrier} [DecidableEq U.Atom]
    (input : RealizableHom U) [IsIso input.semantic.hom]
    {P : CoreFiber input.semantic.target}
    (hom : P ⟶ P) (hom_ne : hom ≠ 𝟙 P) :
    (selectedCoreFiberReindexFunctor input).map hom ≠
      𝟙 ((selectedCoreFiberReindexFunctor input).obj P) := by
  intro map_eq
  let lift := selectedCoreFiberCartesianLift input P
  letI := lift.isStronglyCartesian
  letI : IsIso lift.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (packageProjection U) input.semantic.hom lift.hom
  have factor := selectedCoreFiberReindexFunctor_map_fac input hom
  apply hom_ne
  apply CategoryTheory.Functor.Fiber.hom_ext
  rw [← cancel_epi lift.hom]
  calc
    lift.hom ≫ hom.1 =
        ((selectedCoreFiberReindexFunctor input).map hom).1 ≫ lift.hom :=
      factor.symm
    _ = CategoryTheory.Functor.Fiber.fiberInclusion.map
        (𝟙 ((selectedCoreFiberReindexFunctor input).obj P)) ≫
          lift.hom := by
      exact congrArg (fun mapped =>
        CategoryTheory.Functor.Fiber.fiberInclusion.map mapped ≫ lift.hom)
          map_eq
    _ = lift.hom ≫
        CategoryTheory.Functor.Fiber.fiberInclusion.map (𝟙 P) := by
      exact (Category.id_comp lift.hom).trans (Category.comp_id lift.hom).symm

/-- The authored axis swap remains nonidentity after the exact direct route. -/
theorem finiteAuthoredAxisSwap_directEndomorphism_ne_identity :
    authoredDirectRouteEndomorphism finiteAuthoredAxisSwapDatumSquare ≠
      𝟙 (authoredSupportDirectRoute
        finiteAuthoredAxisSwapDatumSquare.context) := by
  intro equality
  let presentation :=
    finiteAuthoredAxisSwapDatumSquare.context.square.presentation
  have pullback := finiteCodePointedPullback_isPullback_from_producer
    presentation.1.cospan.first presentation.1.cospan.second
  letI : IsIso (typedPresentationToSemantic
      presentation.1.cospan.first) := by
    change IsIso (typedPresentationToSemantic
      (idTypedPresentation finiteAuthoredSupportInstance))
    change IsIso (𝟙 finiteAuthoredSupportInstance.toSemantic)
    infer_instance
  letI : IsIso (typedPresentationToSemantic
      presentation.1.cospan.second) := by
    change IsIso (typedPresentationToSemantic
      (idTypedPresentation finiteAuthoredSupportInstance))
    change IsIso (𝟙 finiteAuthoredSupportInstance.toSemantic)
    infer_instance
  letI : IsIso (typedPresentationToSemantic
      (pullbackFstPresentation presentation.1.cospan.first
        presentation.1.cospan.second)) :=
    pullback.isIso_fst_of_isIso
  letI : IsIso (typedPresentationToSemantic
      (pullbackSndPresentation presentation.1.cospan.first
        presentation.1.cospan.second)) :=
    pullback.isIso_snd_of_isIso
  letI : IsIso
      (typedRealizableHom (bcLeftPresentation presentation)).semantic.hom := by
    change IsIso (typedPresentationToSemantic
      (pullbackFstPresentation presentation.1.cospan.first
        presentation.1.cospan.second))
    infer_instance
  letI : IsIso (typedPresentationToSemantic
      (bcTopPresentation presentation)) := by
    change IsIso (typedPresentationToSemantic
      (pullbackSndPresentation presentation.1.cospan.first
        presentation.1.cospan.second))
    infer_instance
  have reindex_ne := selectedCoreFiberReindex_map_ne_id_of_ne_id
    (typedRealizableHom (bcLeftPresentation presentation))
    (finiteAuthoredAxisSwapDatumSquare.endpointAutomorphism.app
      (Discrete.mk FiniteBCDiagnosticCell.cell))
    finiteAuthoredAxisSwap_component_ne_identity
  have transport_ne := coreFiberTransport_map_ne_id_of_ne_id
    (typedPresentationToSemantic (bcTopPresentation presentation))
    ((selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation))).map
        (finiteAuthoredAxisSwapDatumSquare.endpointAutomorphism.app
          (Discrete.mk FiniteBCDiagnosticCell.cell))) reindex_ne
  have componentEquality := NatTrans.congr_app equality
    (Discrete.mk FiniteBCDiagnosticCell.cell)
  apply transport_ne
  simpa [presentation, authoredDirectRouteEndomorphism,
    authoredSupportDirectEndomorphism, authoredSupportDirectRoute,
    finiteAuthoredAxisSwapDatumSquare, finiteAuthoredAxisSwapInterpretation,
    finiteAuthoredAxisSwapTransportData, finiteAuthoredAxisSwapLiftData,
    finiteAuthoredSupportSquare, finiteAuthoredSupportBCPresentation,
    finiteAuthoredSupportCospan, bcPresentationOfCospan,
    AuthoredBCDatumSquare.endpointAutomorphism,
    AuthoredBCDatumSquare.endpointComponent,
    AuthoredBCDatumSquare.endpointComponentTotal,
    finiteAuthoredAxisSwap] using componentEquality

/-- On the nonidentity raw table, the canonical left twist is not the canonical mate. -/
theorem finiteAuthoredAxisSwap_leftTwist_ne_ignoring :
    authoredCanonicalMateLeftTwist finiteAuthoredAxisSwapDatumSquare ≠
      authoredComparisonIgnoringAuthored FiniteModel.carrier
        finiteAuthoredAxisSwapDatumSquare := by
  intro equality
  apply finiteAuthoredAxisSwap_directEndomorphism_ne_identity
  rw [← cancel_mono
    (authoredSupportCanonicalMate finiteAuthoredAxisSwapDatumSquare.context)]
  simpa [authoredCanonicalMateLeftTwist,
    authoredComparisonIgnoringAuthored] using equality

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
