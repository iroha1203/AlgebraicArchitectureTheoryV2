import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticFiberwiseTransport

/-!
# Source-fiber incidence bridge for diagnostic base change

This module connects ordinary G-106 `AdmissibleTransportData` to the actual
two Beck--Chevalley core-fiber routes.  The source qualification says only that
the already supplied packages and edge lifts lie in the selected southwest
core fiber.  Strong cocartesianness over its identity then makes every source
edge invertible, so the fiberwise representation and both target diagnostic
data sets are generated without supplying a target field.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Incidence of ordinary G-106 data with one fixed source core fiber.
It records source geometry only: vertex bases and the fact that each existing
source edge lies over the identity of that base. -/
structure DiagnosticSourceFiberIncidence
    {G : FiniteTransportPresentation.{u}} (U : AtomCarrier.{u})
    (data : AdmissibleTransportData G U) (X : ExtractionInstance U) where
  /-- Every already selected source package lies over `X`. -/
  vertexBase : ∀ vertex : G.Vertex,
    packagePoint (data.lift.package vertex) = X
  /-- Every already selected source edge is vertical over `X`. -/
  edgeVertical : ∀ {i j : G.Vertex} (edge : G.Edge i j),
    (packageProjection U).IsHomLift (𝟙 X) (data.lift.edgeLift edge)

namespace DiagnosticSourceFiberIncidence

/-- The existing package at a vertex, tagged as an object of the fixed source
fiber. -/
def fiberPackage
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : AdmissibleTransportData G U} {X : ExtractionInstance U}
    (incidence : DiagnosticSourceFiberIncidence U data X)
    (vertex : G.Vertex) : CoreFiber X :=
  ⟨data.lift.package vertex, incidence.vertexBase vertex⟩

/-- A source edge is an isomorphism in the fixed core fiber.  Invertibility is
derived from the existing strongly cocartesian qualification and its identity
base; it is not an additional incidence field. -/
noncomputable def fiberEdgeIso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : AdmissibleTransportData G U} {X : ExtractionInstance U}
    (incidence : DiagnosticSourceFiberIncidence U data X)
    {i j : G.Vertex} (edge : G.Edge i j) :
    incidence.fiberPackage i ≅ incidence.fiberPackage j := by
  let edgeLift := data.lift.edgeLift edge
  letI : (packageProjection U).IsHomLift (𝟙 X) edgeLift :=
    incidence.edgeVertical edge
  have baseFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (𝟙 X) edgeLift
  letI : @IsIso (ExtractionInstance U)
      (ExtInstHom.extractionInstanceCategory U)
      (packagePoint (data.lift.package i))
      (packagePoint (data.lift.package j)) edgeLift.base := by
    change IsIso ((packageProjection U).map edgeLift)
    rw [baseFac]
    infer_instance
  letI : (packageProjection U).IsStronglyCocartesian
      edgeLift.base edgeLift := data.lift.edgeStrong edge
  letI : @IsIso (AATCorePackage U)
      (PackageTotalHom.packageTotalCategory U)
      (data.lift.package i) (data.lift.package j) edgeLift :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (p := packageProjection U) (f := edgeLift.base) edgeLift
  exact
    { hom := ⟨edgeLift, inferInstance⟩
      inv := ⟨inv edgeLift, inferInstance⟩
      hom_inv_id := by
        apply CategoryTheory.Functor.Fiber.hom_ext
        change edgeLift ≫ inv edgeLift = 𝟙 (data.lift.package i)
        exact @IsIso.hom_inv_id (AATCorePackage U)
          (PackageTotalHom.packageTotalCategory U)
          (data.lift.package i) (data.lift.package j) edgeLift _
      inv_hom_id := by
        apply CategoryTheory.Functor.Fiber.hom_ext
        change inv edgeLift ≫ edgeLift = 𝟙 (data.lift.package j)
        exact @IsIso.inv_hom_id (AATCorePackage U)
          (PackageTotalHom.packageTotalCategory U)
          (data.lift.package i) (data.lift.package j) edgeLift _ }

/-- Re-express ordinary source G-106 data in the actual selected source core
fiber.  Comparator values are the original source values; no target value is
accepted. -/
noncomputable def toFiberwise
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : AdmissibleTransportData G U} {X : ExtractionInstance U}
    (incidence : DiagnosticSourceFiberIncidence U data X) :
    FiberwiseAdmissibleTransportData G U X where
  package := incidence.fiberPackage
  edgeIso := incidence.fiberEdgeIso
  comparator := data.comparator

/-- Forgetting the generated fiberwise representation recovers the original
source packages pointwise. -/
@[simp]
theorem toFiberwise_package
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : AdmissibleTransportData G U} {X : ExtractionInstance U}
    (incidence : DiagnosticSourceFiberIncidence U data X)
    (vertex : G.Vertex) :
    incidence.toFiberwise.toTransportData.lift.package vertex =
      data.lift.package vertex := rfl

/-- Forgetting the generated fiberwise representation recovers the original
source edge lifts pointwise. -/
@[simp]
theorem toFiberwise_edgeLift
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : AdmissibleTransportData G U} {X : ExtractionInstance U}
    (incidence : DiagnosticSourceFiberIncidence U data X)
    {i j : G.Vertex} (edge : G.Edge i j) :
    incidence.toFiberwise.toTransportData.lift.edgeLift edge =
      data.lift.edgeLift edge := by
  change (incidence.fiberEdgeIso edge).hom.1 = data.lift.edgeLift edge
  simp [fiberEdgeIso]

/-- Forgetting the generated fiberwise representation recovers every original
source comparator. -/
@[simp]
theorem toFiberwise_comparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : AdmissibleTransportData G U} {X : ExtractionInstance U}
    (incidence : DiagnosticSourceFiberIncidence U data X)
    (cell : G.TwoCell) :
    incidence.toFiberwise.toTransportData.comparator cell =
      data.comparator cell := rfl

end DiagnosticSourceFiberIncidence

/-! ## Actual Beck--Chevalley specialization -/

/-- Source-fiber incidence for the ordinary interpretation decoded from one
finite Beck--Chevalley presentation. -/
abbrev BCDiagnosticSourceFiberIncidence
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation)) :=
  DiagnosticSourceFiberIncidence U interpretation.data
    presentation.1.cospan.firstSource.toSemantic

/-- The ordinary source interpretation transported along the actual direct BC
route.  The target datum is generated from source data and source incidence. -/
noncomputable def bcDiagnosticDirectTransportedInterpretationData
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation) :
    AdmissibleTransportData (toSemanticBC presentation).diagnostic U :=
  bcDiagnosticDirectTransportedData presentation incidence.toFiberwise

/-- The same ordinary source interpretation transported along the actual
via-base BC route. -/
noncomputable def bcDiagnosticViaBaseTransportedInterpretationData
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation) :
    AdmissibleTransportData (toSemanticBC presentation).diagnostic U :=
  bcDiagnosticViaBaseTransportedData presentation incidence.toFiberwise

/-- The direct-route target comparator is generated from the ordinary source
comparator by the actual direct endpoint group homomorphism. -/
@[simp]
theorem bcDiagnosticDirectTransportedInterpretationData_comparator
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (cell : (toSemanticBC presentation).diagnostic.TwoCell) :
    (bcDiagnosticDirectTransportedInterpretationData presentation
      interpretation incidence).comparator cell =
      coreFiberFunctorPackageAutHom
        (bcDiagnosticDirectFunctor presentation)
        (incidence.toFiberwise.package
          ((toSemanticBC presentation).diagnostic.twoTarget cell))
        (interpretation.data.comparator cell) := rfl

/-- The via-base target comparator is generated from the same ordinary source
comparator by the actual via-base endpoint group homomorphism. -/
@[simp]
theorem bcDiagnosticViaBaseTransportedInterpretationData_comparator
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (cell : (toSemanticBC presentation).diagnostic.TwoCell) :
    (bcDiagnosticViaBaseTransportedInterpretationData presentation
      interpretation incidence).comparator cell =
      coreFiberFunctorPackageAutHom
        (bcDiagnosticViaBaseFunctor presentation)
        (incidence.toFiberwise.package
          ((toSemanticBC presentation).diagnostic.twoTarget cell))
        (interpretation.data.comparator cell) := rfl

/-- The direct target edge qualification is generated from source incidence
and the mapped fiber isomorphism. -/
theorem bcDiagnosticDirectTransportedInterpretationData_edgeStrong
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    {i j : (toSemanticBC presentation).diagnostic.Vertex}
    (edge : (toSemanticBC presentation).diagnostic.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      ((bcDiagnosticDirectTransportedInterpretationData presentation
        interpretation incidence).lift.edgeLift edge).base
      ((bcDiagnosticDirectTransportedInterpretationData presentation
        interpretation incidence).lift.edgeLift edge) :=
  incidence.toFiberwise.transported_edgeStrong
    (bcDiagnosticDirectFunctor presentation) edge

/-- The via-base target edge qualification is generated from source incidence
and the mapped fiber isomorphism. -/
theorem bcDiagnosticViaBaseTransportedInterpretationData_edgeStrong
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    {i j : (toSemanticBC presentation).diagnostic.Vertex}
    (edge : (toSemanticBC presentation).diagnostic.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      ((bcDiagnosticViaBaseTransportedInterpretationData presentation
        interpretation incidence).lift.edgeLift edge).base
      ((bcDiagnosticViaBaseTransportedInterpretationData presentation
        interpretation incidence).lift.edgeLift edge) :=
  incidence.toFiberwise.transported_edgeStrong
    (bcDiagnosticViaBaseFunctor presentation) edge

/-- Every direct target two-cell base equation is derived in the generated
fixed target fiber. -/
theorem bcDiagnosticDirectTransportedInterpretationData_twoCellBase
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (cell : (toSemanticBC presentation).diagnostic.TwoCell) :
    ((bcDiagnosticDirectTransportedInterpretationData presentation
      interpretation incidence).lift.pathLift
        ((toSemanticBC presentation).diagnostic.twoLeft cell)).base =
      ((bcDiagnosticDirectTransportedInterpretationData presentation
        interpretation incidence).lift.pathLift
          ((toSemanticBC presentation).diagnostic.twoRight cell)).base :=
  incidence.toFiberwise.transported_twoCellBase
    (bcDiagnosticDirectFunctor presentation) cell

/-- Every via-base target two-cell base equation is derived in the generated
fixed target fiber. -/
theorem bcDiagnosticViaBaseTransportedInterpretationData_twoCellBase
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (cell : (toSemanticBC presentation).diagnostic.TwoCell) :
    ((bcDiagnosticViaBaseTransportedInterpretationData presentation
      interpretation incidence).lift.pathLift
        ((toSemanticBC presentation).diagnostic.twoLeft cell)).base =
      ((bcDiagnosticViaBaseTransportedInterpretationData presentation
        interpretation incidence).lift.pathLift
          ((toSemanticBC presentation).diagnostic.twoRight cell)).base :=
  incidence.toFiberwise.transported_twoCellBase
    (bcDiagnosticViaBaseFunctor presentation) cell

/-- The canonical mate-generated endpoint comparison identifies the generated
direct and via-base comparator tables for an ordinary G-106 interpretation. -/
theorem bcDiagnosticTransportedInterpretationComparator_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (cell : (toSemanticBC presentation).diagnostic.TwoCell) :
    bcDiagnosticEndpointComparison presentation
        (incidence.toFiberwise.package
          ((toSemanticBC presentation).diagnostic.twoTarget cell))
        ((bcDiagnosticDirectTransportedInterpretationData presentation
          interpretation incidence).comparator cell) =
      (bcDiagnosticViaBaseTransportedInterpretationData presentation
        interpretation incidence).comparator cell := by
  exact bcDiagnosticTransportedComparator_naturality presentation
    incidence.toFiberwise cell

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
