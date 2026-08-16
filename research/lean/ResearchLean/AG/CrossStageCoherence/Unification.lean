import ResearchLean.AG.CrossStageCoherence.PastingObstruction

/-!
# Pseudofunctor and obstruction-vocabulary unification

The compositor component itself is an isomorphism between the direct and
iterated transport targets, not an automorphism of either endpoint.  Its
categorical role is therefore recorded by its normalization factorization.
Endpoint automorphisms enter `C_G` only after path whiskering.  The theorems
below connect that whiskering to core pushforward, and reconstruct the
specialized raw cochain directly from the general composite-fiber comparator.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

/-- The pseudofunctor compositor normalizes the direct lift to the iterated
lift; it is deliberately not assigned a `C_G` type across distinct targets. -/
theorem pseudofunctorCompositor_normalization {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    geomFiberLift (σ ≫ τ) G ≫ (geomFiberCompositorApp σ τ G).hom.1 =
      geomFiberIteratedLift σ τ G :=
  geomFiberCompositorApp_hom_fac σ τ G

/-- After normalization to one endpoint, path whiskering produces an actual
`C_G` element with its universal-property factorization. -/
theorem pseudofunctorWhiskering_compositeFiber_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    (upperReselectedPathLift data reselection path).comp
      (CompositeFiberAut.hom
        (upperWhiskerCompositeFiberAut data reselection automorphism path)) =
      upperFiberAutThenPath data reselection automorphism path :=
  upperWhiskerCompositeFiberAut_fac data reselection automorphism path

/-- The `p` image of normalized upper whiskering is exactly the inherited core
whiskering, rather than a separately supplied compatibility. -/
theorem pseudofunctorWhiskering_pushforward
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    compositeFiberPushforward (data.geometry j)
        (upperWhiskerCompositeFiberAut data reselection automorphism path) =
      whiskerFiberAut data.coreLiftData
        (pushforwardEdgeReselection data reselection)
        (compositeFiberPushforward (data.geometry i) automorphism) path :=
  pushforward_upperWhiskerCompositeFiberAut
    data reselection automorphism path

/-- Specialized comparator rebuilt directly from the general `C_G`
comparison after normalization of both paths to their declared endpoint. -/
noncomputable def pseudofunctorCanonicalComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    CompositeFiberAut (data.lift.geometry (P.twoTarget cell)) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoLeft cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoRight cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoLeft cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoRight cell)
  exact canonicalCompositeFiberComparator
    (upperReselectedPathLift data.lift reselection (P.twoLeft cell))
    (upperReselectedPathLift data.lift reselection (P.twoRight cell))
    (upperReselectedTwoCellBase data reselection cell)

/-- The reconstructed specialization is the obstruction vocabulary's canonical
comparator, by strong-cocartesian uniqueness. -/
theorem pseudofunctorCanonicalComparator_eq_upper
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    pseudofunctorCanonicalComparator data reselection cell =
      upperCanonicalTwoCellComparator data reselection cell := by
  let left := upperReselectedPathLift data.lift reselection (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoLeft cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoRight cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoLeft cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoRight cell)
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left :=
    (upperReselectLiftData data.lift reselection).pathLift_compositeStrong
      (P.twoLeft cell)
  apply CompositeFiberAut.ext_of_strong_fac left
  exact (canonicalCompositeFiberComparator_fac
    (upperReselectedPathLift data.lift reselection (P.twoLeft cell))
    (upperReselectedPathLift data.lift reselection (P.twoRight cell))
    (upperReselectedTwoCellBase data reselection cell)).trans
      (upperCanonicalTwoCellComparator_fac data reselection cell).symm

/-- Pseudofunctor-specialized raw defect, with authored and generated
provenance kept separate. -/
noncomputable def pseudofunctorRawTwoCellDefect
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    CompositeFiberAut (data.lift.geometry (P.twoTarget cell)) :=
  data.comparator cell *
    (pseudofunctorCanonicalComparator data reselection cell)⁻¹

theorem pseudofunctorRawTwoCellDefect_eq_upper
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    pseudofunctorRawTwoCellDefect data reselection cell =
      upperRawTwoCellDefect data reselection cell := by
  rw [pseudofunctorRawTwoCellDefect, upperRawTwoCellDefect,
    pseudofunctorCanonicalComparator_eq_upper]

noncomputable def pseudofunctorRawDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    UpperDefectCochain data :=
  fun cell => pseudofunctorRawTwoCellDefect data reselection cell

theorem pseudofunctorRawDefectCochain_eq_upper
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    pseudofunctorRawDefectCochain data reselection =
      upperRawDefectCochain data reselection := by
  funext cell
  exact pseudofunctorRawTwoCellDefect_eq_upper data reselection cell

/-- Orbit vanishing stated using the independently reconstructed specialized
cochain. -/
def PseudofunctorObstructionVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∃ reselection : UpperEdgeReselection data.lift,
    pseudofunctorRawDefectCochain data reselection =
      upperIdentityDefectCochain data

theorem pseudofunctorObstructionVanishes_iff_joint
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    PseudofunctorObstructionVanishes data ↔ JointVanishes data := by
  constructor
  · rintro ⟨reselection, identity⟩
    exact ⟨reselection,
      (pseudofunctorRawDefectCochain_eq_upper data reselection).symm.trans
        identity⟩
  · rintro ⟨reselection, identity⟩
    exact ⟨reselection,
      (pseudofunctorRawDefectCochain_eq_upper data reselection).trans
        identity⟩

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
