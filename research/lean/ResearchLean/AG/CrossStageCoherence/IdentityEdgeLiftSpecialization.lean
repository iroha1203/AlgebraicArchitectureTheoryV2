import ResearchLean.AG.CrossStageCoherence.EdgeEffectivityInstances

/-!
# Identity-edge-lift affine specialization

This module fixes the identity-edge-lift reading required by G-109: every
presented edge has the identity two-layer lift, so the baseline canonical cell
comparator is forced to be `1` by strong cancellation.  The general twisted
affine step therefore specializes to left translation by the raw defect.

The final finite firing reuses the reviewed noncentral comparator on this
identity-lift datum.  Its raw defect is nonidentity, so the specialization is
not merely a normalization statement at the unit element.

## Implementation notes

The identity geometry/core strong certificates are derived from the existing
`IsStronglyCocartesian.of_iso` API; they are not accepted as fields.  Arbitrary
authored comparators are then added only after the constant lift datum is
constructed.  The proof that the canonical factor is `1` uses its actual
factorization through the identity path lift and `ext_of_strong_fac`, rather
than simplifying the comparator by definition.  The noncentral firing changes
only the authored comparator; it does not claim that this identity-lift fixture
detects the general nontrivial canonical right twist.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

namespace IdentityEdgeLiftSpecialization

/-- Identity is a strongly cocartesian geometry lift for every geometry package. -/
theorem geometryIdentityStrong
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    (geometryProjection U).IsStronglyCocartesian
      (GeometryTotalHom.id G).base (GeometryTotalHom.id G) := by
  letI : (geometryProjection U).IsHomLift
      (𝟙 G.core) (Iso.refl G).hom :=
    CategoryTheory.IsHomLift.id rfl
  simpa using
    (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (geometryProjection U) (𝟙 G.core) (Iso.refl G))

/-- The projected identity is independently strongly cocartesian. -/
theorem coreIdentityStrong
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    (packageProjection U).IsStronglyCocartesian
      (PackageTotalHom.id G.core).base (PackageTotalHom.id G.core) := by
  letI : (packageProjection U).IsHomLift
      (𝟙 (packagePoint G.core)) (Iso.refl G.core).hom :=
    CategoryTheory.IsHomLift.id rfl
  simpa using
    (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (packageProjection U) (𝟙 (packagePoint G.core)) (Iso.refl G.core))

/-- Constant two-layer data in which every presented edge is lifted by the identity. -/
noncomputable def liftData
    (P : FiniteTransportPresentation.{u})
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    TwoLayerLiftData.{u, v} P U where
  geometry _ := G
  edgeLift _ := GeometryTotalHom.id G
  edgeGeometryStrong _ := geometryIdentityStrong G
  edgeCoreStrong _ := coreIdentityStrong G

/-- Every path in the constant identity-edge lift evaluates to the identity. -/
theorem pathLift_eq_id
    (P : FiniteTransportPresentation.{u})
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    {source target : P.Vertex} (path : P.Path source target) :
    (liftData P G).pathLift path = GeometryTotalHom.id G := by
  induction path with
  | nil => rfl
  | cons edge tail inductionHypothesis =>
      change (GeometryTotalHom.id G).comp ((liftData P G).pathLift tail) =
        GeometryTotalHom.id G
      rw [inductionHypothesis]
      exact Category.comp_id
        (self := geometryTotalCategory U) (GeometryTotalHom.id G)

/-- Add arbitrary authored cell comparators to the constant identity-edge lift. -/
noncomputable def data
    (P : FiniteTransportPresentation.{u})
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (comparator : P.TwoCell → CompositeFiberAut G) :
    TwoLayerTransportData.{u, v} P U where
  lift := liftData P G
  twoCellBase := by
    intro cell
    rw [pathLift_eq_id, pathLift_eq_id]
  comparator := comparator

/-- Identity edge lifts generate the identity baseline canonical comparator. -/
theorem upperCanonical_eq_one
    (P : FiniteTransportPresentation.{u})
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (comparator : P.TwoCell → CompositeFiberAut G)
    (cell : P.TwoCell) :
    upperCanonicalTwoCellComparator (data P G comparator) 1 cell = 1 := by
  let transport := data P G comparator
  let leftLift := upperReselectedPathLift transport.lift 1 (P.twoLeft cell)
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      leftLift.base.base leftLift :=
    (upperReselectLiftData transport.lift 1).pathLift_compositeStrong
      (P.twoLeft cell)
  apply CompositeFiberAut.ext_of_strong_fac leftLift
  calc
    leftLift.comp (CompositeFiberAut.hom
        (upperCanonicalTwoCellComparator transport 1 cell)) =
        upperReselectedPathLift transport.lift 1 (P.twoRight cell) :=
      upperCanonicalTwoCellComparator_fac transport 1 cell
    _ = GeometryTotalHom.id G := by
      rw [upperReselectedPathLift_one]
      change (liftData P G).pathLift (P.twoRight cell) = GeometryTotalHom.id G
      exact pathLift_eq_id P G _
    _ = leftLift.comp (CompositeFiberAut.hom (1 : CompositeFiberAut G)) := by
      dsimp only [leftLift, transport]
      rw [upperReselectedPathLift_one]
      change GeometryTotalHom.id G =
        ((liftData P G).pathLift (P.twoLeft cell)).comp
          (CompositeFiberAut.hom (1 : CompositeFiberAut G))
      rw [pathLift_eq_id]
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        G G (GeometryTotalHom.id G)).symm

/-- Fixed identity-edge-lift specialization: the twisted affine step becomes
left translation by the raw defect. -/
theorem cellAffineStep_forward_apply
    (P : FiniteTransportPresentation.{u})
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (comparator : P.TwoCell → CompositeFiberAut G)
    (cell : P.TwoCell)
    (coordinate : CompositeFiberAut
      ((data P G comparator).lift.geometry (P.twoTarget cell))) :
    CellAffineStep (data P G comparator) (CellChainStep.forward cell) coordinate =
      upperRawTwoCellDefect (data P G comparator) 1 cell * coordinate := by
  rw [cellAffineStep_apply]
  simp only [cellAuthoredFactor, cellCanonicalFactor, CellChainStep.forward,
    castCompositeFiberAut, upperRawTwoCellDefect]
  rw [upperCanonical_eq_one]
  simp

/-! ## Nontrivial finite firing -/

/-- Reuse the reviewed noncentral authored comparator on an identity-edge lift. -/
noncomputable abbrev noncentralData :
    TwoLayerTransportData NoncentralTwistWitness.presentation
      FiniteModel.carrier :=
  data NoncentralTwistWitness.presentation NoncentralTwistWitness.package
    (fun _ => NoncentralTwistWitness.compositeSwap01)

/-- The identity-edge canonical factor is trivial while the authored raw defect
remains the reviewed nonidentity, noncentral transposition. -/
theorem noncentralRawDefect_eq :
    upperRawTwoCellDefect noncentralData 1
      NoncentralTwistWitness.TwistCell.comparison =
        NoncentralTwistWitness.compositeSwap01 := by
  rw [upperRawTwoCellDefect, upperCanonical_eq_one]
  simp [data]

/-- The specialization fires on a genuinely nonidentity raw defect. -/
theorem noncentralRawDefect_ne_one :
    upperRawTwoCellDefect noncentralData 1
      NoncentralTwistWitness.TwistCell.comparison ≠ 1 := by
  rw [noncentralRawDefect_eq]
  exact NoncentralTwistWitness.compositeSwap01_ne_one

/-- The noncentral finite cell acts by actual nontrivial left translation. -/
theorem noncentral_cellAffineStep_forward_apply
    (coordinate : CompositeFiberAut
      (noncentralData.lift.geometry
        (NoncentralTwistWitness.presentation.twoTarget
          NoncentralTwistWitness.TwistCell.comparison))) :
    CellAffineStep noncentralData
        (CellChainStep.forward NoncentralTwistWitness.TwistCell.comparison)
        coordinate =
      upperRawTwoCellDefect noncentralData 1
          NoncentralTwistWitness.TwistCell.comparison * coordinate :=
  cellAffineStep_forward_apply NoncentralTwistWitness.presentation
    NoncentralTwistWitness.package
    (fun _ => NoncentralTwistWitness.compositeSwap01)
    NoncentralTwistWitness.TwistCell.comparison coordinate

end IdentityEdgeLiftSpecialization

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
