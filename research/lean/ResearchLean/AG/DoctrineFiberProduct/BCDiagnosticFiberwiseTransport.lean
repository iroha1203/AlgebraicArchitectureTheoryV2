import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticBaseChangeAutomorphism

/-!
# Fiberwise transport of a fixed diagnostic presentation

This module keeps the vertex, edge, and two-cell types of a finite diagnostic
presentation fixed while applying one generated core-fiber functor to its
semantic interpretation.  Source edges are represented as fiber isomorphisms;
their target strong-cocartesianness and every target two-cell base equation are
therefore derived.  The target comparator is the image of the source comparator
under the endpoint group homomorphism from Cycle 68.

The construction is the fiberwise d1/d3 engine.  It does not supply a target
edge qualification, base equation, or comparator, and it makes no raw-defect,
orbit, or vanishing claim.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- A G-106 diagnostic interpretation internal to one categorical core fiber.
Edges are stored as isomorphisms, the intrinsic form of a strongly
cocartesian lift over an identity base arrow. -/
structure FiberwiseAdmissibleTransportData
    (G : FiniteTransportPresentation.{u}) (U : AtomCarrier.{u})
    (X : ExtractionInstance U) where
  /-- One object of the fixed core fiber at every diagnostic vertex. -/
  package : G.Vertex → CoreFiber X
  /-- One invertible vertical lift at every diagnostic edge. -/
  edgeIso : {i j : G.Vertex} → G.Edge i j → (package i ≅ package j)
  /-- The authored source comparator; target comparators are generated from it. -/
  comparator : (cell : G.TwoCell) →
    PackageFiberAut (package (G.twoTarget cell)).1

namespace FiberwiseAdmissibleTransportData

/-- Forget the fiber tags and retain the underlying package at each vertex. -/
def packageTotal
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (vertex : G.Vertex) : AATCorePackage U :=
  (data.package vertex).1

/-- The underlying total morphism of one fiberwise edge isomorphism. -/
def edgeLift
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {i j : G.Vertex} (edge : G.Edge i j) :
    PackageTotalHom (data.packageTotal i) (data.packageTotal j) :=
  (data.edgeIso edge).hom.1

/-- Every generated total edge is strongly cocartesian; this is derived from
the fact that it is the underlying morphism of a fiber isomorphism. -/
theorem edgeLift_isStronglyCocartesian
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {i j : G.Vertex} (edge : G.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (data.edgeLift edge).base (data.edgeLift edge) := by
  letI : IsIso (data.edgeIso edge).hom.1 := by
    change IsIso (CategoryTheory.Functor.Fiber.fiberInclusion.map
      (data.edgeIso edge).hom)
    infer_instance
  change (packageProjection U).IsStronglyCocartesian
    ((packageProjection U).map (data.edgeIso edge).hom.1)
    (data.edgeIso edge).hom.1
  infer_instance

/-- The generated G-106 edge-lift layer.  Its qualification is a theorem, not
a post-transport input field. -/
noncomputable def toLiftData
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X) :
    AdmissibleLiftData G U where
  package := data.packageTotal
  edgeLift := data.edgeLift
  edgeStrong := data.edgeLift_isStronglyCocartesian

/-- Compose the fiberwise edge isomorphisms along a presented path. -/
def pathIso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {i j : G.Vertex} : G.Path i j → (data.package i ≅ data.package j)
  | .nil _ => Iso.refl _
  | .cons edge tail => data.edgeIso edge ≪≫ data.pathIso tail

/-- Forgetting the fiber tags identifies generated path evaluation with the
underlying morphism of the composed fiber isomorphism. -/
theorem pathLift_eq_pathIso_hom
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {i j : G.Vertex} (path : G.Path i j) :
    data.toLiftData.pathLift path = (data.pathIso path).hom.1 := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [AdmissibleLiftData.pathLift, pathIso, Iso.trans_hom]
      rw [inductionHypothesis]
      rfl

/-- Parallel paths in the unchanged combinatorial presentation acquire their
target base equality from the common fixed core fiber. -/
theorem twoCellBase
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (cell : G.TwoCell) :
    (data.toLiftData.pathLift (G.twoLeft cell)).base =
      (data.toLiftData.pathLift (G.twoRight cell)).base := by
  rw [data.pathLift_eq_pathIso_hom, data.pathLift_eq_pathIso_hom]
  let left := (data.pathIso (G.twoLeft cell)).hom
  let right := (data.pathIso (G.twoRight cell)).hom
  letI : (packageProjection U).IsHomLift (𝟙 X) left.1 := left.2
  letI : (packageProjection U).IsHomLift (𝟙 X) right.1 := right.2
  have leftFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (𝟙 X) left.1
  have rightFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (𝟙 X) right.1
  simpa only using leftFac.trans rightFac.symm

/-- Reassemble reviewed G-106 transport data.  Both admissibility fields are
derived by the preceding theorems. -/
noncomputable def toTransportData
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X) :
    AdmissibleTransportData G U where
  lift := data.toLiftData
  twoCellBase := data.twoCellBase
  comparator := data.comparator

/-- Apply one generated core-fiber functor without changing the diagnostic
vertex, edge, or two-cell types. -/
noncomputable def map
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y) :
    FiberwiseAdmissibleTransportData G U Y where
  package vertex := F.obj (data.package vertex)
  edgeIso edge := F.mapIso (data.edgeIso edge)
  comparator cell := coreFiberFunctorPackageAutHom F
    (data.package (G.twoTarget cell)) (data.comparator cell)

/-- The transported G-106 datum is generated from `map`; no target
qualification, base equation, or comparator is accepted. -/
noncomputable def transported
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y) :
    AdmissibleTransportData G U :=
  (data.map F).toTransportData

/-- The target comparator satisfies the mandated d3 generation equation. -/
@[simp]
theorem transported_comparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y) (cell : G.TwoCell) :
    (data.transported F).comparator cell =
      coreFiberFunctorPackageAutHom F
        (data.package (G.twoTarget cell)) (data.comparator cell) := rfl

/-- The target edge qualification is definitionally the theorem generated
from the mapped edge isomorphism. -/
theorem transported_edgeStrong
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y)
    {i j : G.Vertex} (edge : G.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      ((data.transported F).lift.edgeLift edge).base
      ((data.transported F).lift.edgeLift edge) :=
  (data.map F).edgeLift_isStronglyCocartesian edge

/-- The target two-cell base equation is the generated fixed-fiber equation. -/
theorem transported_twoCellBase
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y) (cell : G.TwoCell) :
    ((data.transported F).lift.pathLift (G.twoLeft cell)).base =
      ((data.transported F).lift.pathLift (G.twoRight cell)).base :=
  (data.map F).twoCellBase cell

end FiberwiseAdmissibleTransportData

/-! ## Specialization to the two exact diagnostic base-change routes -/

/-- Transport a fiberwise diagnostic interpretation along the generated direct
route of one finite Beck--Chevalley presentation. -/
noncomputable def bcDiagnosticDirectTransportedData
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      presentation.1.cospan.firstSource.toSemantic) :
    AdmissibleTransportData G U :=
  data.transported (bcDiagnosticDirectFunctor presentation)

/-- Transport the same interpretation along the generated via-base route. -/
noncomputable def bcDiagnosticViaBaseTransportedData
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      presentation.1.cospan.firstSource.toSemantic) :
    AdmissibleTransportData G U :=
  data.transported (bcDiagnosticViaBaseFunctor presentation)

/-- The direct target comparator is generated by the direct endpoint group
homomorphism. -/
@[simp]
theorem bcDiagnosticDirectTransportedData_comparator
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      presentation.1.cospan.firstSource.toSemantic)
    (cell : G.TwoCell) :
    (bcDiagnosticDirectTransportedData presentation data).comparator cell =
      coreFiberFunctorPackageAutHom
        (bcDiagnosticDirectFunctor presentation)
        (data.package (G.twoTarget cell)) (data.comparator cell) := rfl

/-- The via-base target comparator is generated by the via-base endpoint group
homomorphism. -/
@[simp]
theorem bcDiagnosticViaBaseTransportedData_comparator
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      presentation.1.cospan.firstSource.toSemantic)
    (cell : G.TwoCell) :
    (bcDiagnosticViaBaseTransportedData presentation data).comparator cell =
      coreFiberFunctorPackageAutHom
        (bcDiagnosticViaBaseFunctor presentation)
        (data.package (G.twoTarget cell)) (data.comparator cell) := rfl

/-- The canonical mate-generated endpoint comparison identifies the two
generated target comparator tables pointwise. -/
theorem bcDiagnosticTransportedComparator_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      presentation.1.cospan.firstSource.toSemantic)
    (cell : G.TwoCell) :
    bcDiagnosticEndpointComparison presentation
        (data.package (G.twoTarget cell))
        ((bcDiagnosticDirectTransportedData presentation data).comparator cell) =
      (bcDiagnosticViaBaseTransportedData presentation data).comparator cell := by
  simpa only [bcDiagnosticDirectTransportedData_comparator,
    bcDiagnosticViaBaseTransportedData_comparator] using
      (bcDiagnosticEndpointComparison_naturality presentation
        (data.package (G.twoTarget cell)) (data.comparator cell))

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
