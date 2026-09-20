import ResearchLean.AG.LocalSemanticReconstruction.IndependentCoreTableAssembly
import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomEquationAssembly
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomDetectorLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationNaturality
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomSignatureLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantComposition
import Formal.Util.AssertStandardAxioms

/-!
# Complete core-package Hom assembly from primitive preservation rules

Implementation notes: the inputs are the independent dependent object tables
and the common Hom table. Every compatibility field below is a primitive
point rule. The native source, Atom, operation, equation, observable, and
signature maps are constructed from those rows; invariant witnesses are
erased by the previously constructed quotient. The staged object presentation
keeps dependent carrier references aligned without assuming native transports.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageAssembly

noncomputable section

universe u v

open Site AtomFoundation IndependentCoreTableAssembly IndependentCorePrimitive

variable {U : AtomCarrier.{u}} {mode : Mode}
variable (s t : PackageData U) (h : Table.{u, v} U mode)


/-- Independent primitive preservation rules used to construct all native core Hom fields. -/
structure PointLaws : Prop where
  /-- Pointed and upper Atom graphs satisfy inverse and agreement laws. -/
  atom : Atom.IsCoherent h
  /-- Source normalization and extraction are compared at primitive point pairs. -/
  extraction : CoreLaws.ExtractionLaws (s.val.1.1.val.val) (t.val.1.1.val.val) h
  /-- Derived family/configuration matching is characterized by its primitive points. -/
  matching : TransportMatch.IsLawful h
  /-- Formation and composition preserve primitive responses. -/
  generation : CoreLaws.GenerationLaws (s.val.1.2.1.val) (t.val.1.2.1.val) (s.val.1.2.2.1) (t.val.1.2.2.1) h
  /-- Equation rows have total inverse graphs at the declared index carriers. -/
  equationRows : IndependentInverseGraph.IsLawful (IndependentEquationPrimitive.index (s.val.2.2.1.val))
    (IndependentEquationPrimitive.index (t.val.2.2.1.val))
    (InverseRows.equation h (generatedObject s.val.1) (generatedObject t.val.1))
  /-- Context rows preserve both orders and satisfy the original unit/counit comparisons. -/
  contextRows : Context.IsLawful (context s.val.2.1).le (context t.val.2.1).le
    (Context.points h (generatedObject s.val.1) (generatedObject t.val.1))
  /-- Every active observable row is an inverse ring graph. -/
  observableRows : letI := ObservableNatural.rings (s.val.2.2.1.val) (s.val.2.2.1.property.choose) (s.val.2.2.1.property.choose_spec)
    letI := ObservableNatural.rings (t.val.2.2.1.val) (t.val.2.2.1.property.choose) (t.val.2.2.1.property.choose_spec)
    Observable.IsLawful h (IndependentEquationPrimitive.observableType (s.val.2.2.1.val))
      (IndependentEquationPrimitive.observableType (t.val.2.2.1.val))
  /-- Role, restriction, violation, and residual clauses are primitive point rules. -/
  equationPoints : EquationAssembly.PointLaws (s.val.2.2.1.val) (t.val.2.2.1.val) h
  /-- Detector codes compare finite syntax through true Atom points. -/
  detector : Detector.PointLaws (s.val.2.2.2.val) (t.val.2.2.2.val) h (generatedObject s.val.1) (generatedObject t.val.1)
  /-- Operation rows are directed maps on the carriers at their object endpoints. -/
  operationRows : Operation.IsLawful h (Operations.carrier (s.val.1.2.2.2.2.2.val)) (Operations.carrier (t.val.1.2.2.2.2.2.val))
  /-- Operation action squares compare primitive responses. -/
  operationPoints : OperationNatural.PointLaws (s.val.1.2.2.2.2.2.val) (t.val.1.2.2.2.2.2.val) h
  /-- Signature axes retain their directed map. -/
  axisRows : IndependentCarrierGraph.IsLawful
    (IndependentInvariantSignaturePrimitive.Signature.axis (s.val.1.2.2.2.2.1.val))
    (IndependentInvariantSignaturePrimitive.Signature.axis (t.val.1.2.2.2.2.1.val)) (signatureAxis h)
  /-- Each selected axis pair has inverse coordinate rows. -/
  coordinateRows : Signature.IsLawful h
    (IndependentInvariantSignaturePrimitive.Signature.axis (s.val.1.2.2.2.2.1.val))
    (IndependentInvariantSignaturePrimitive.Signature.axis (t.val.1.2.2.2.2.1.val))
    (IndependentInvariantSignaturePrimitive.Signature.coordinateType (s.val.1.2.2.2.2.1.val) (s.val.1.2.2.2.2.1.property))
    (IndependentInvariantSignaturePrimitive.Signature.coordinateType (t.val.1.2.2.2.2.1.val) (t.val.1.2.2.2.2.1.property))
  /-- Selection is preserved and reflected by the axis points. -/
  selected : SignatureLaws.SelectedPoints (s.val.1.2.2.2.2.1.val) (t.val.1.2.2.2.2.1.val) h
  /-- Coordinates compare their primitive values over object and axis points. -/
  coordinates : SignatureLaws.CoordinatePoints (s.val.1.2.2.2.2.1.val) (t.val.1.2.2.2.2.1.val) h

variable (ho : CoreLaws.ObjectRows h) (hl : PointLaws s t h)

/-- Assemble configuration maps from the Atom action and the primitive configuration comparison. -/
def configurationMap (A : ArchitectureObject U) :
    ConfigurationHom A.configuration (CoreLaws.objectMap h ho A).configuration :=
  (CoreLaws.configuration_eq (s.val.1.2.1.val) (t.val.1.2.1.val) (s.val.1.2.2.1) (t.val.1.2.2.1) h hl.atom.upper hl.matching ho hl.generation A).symm ▸
    AtomConfiguration.transportHom (Atom.assemble (Atom.upper h) hl.atom.upper) A.configuration

/-- Configuration-map assembly retains exactly the common Atom graph. -/
theorem configurationMap_atomMap (A : ArchitectureObject U) :
    (configurationMap s t h ho hl A).atomMap = Atom.assemble (Atom.upper h) hl.atom.upper := by
  exact (CompleteGeometryGraphAssembly.PackageGraphData.configurationHom_cast_atomMap
    (CoreLaws.configuration_eq (s.val.1.2.1.val) (t.val.1.2.1.val) (s.val.1.2.2.1) (t.val.1.2.2.1) h hl.atom.upper hl.matching ho hl.generation A) _).trans
      (AtomConfiguration.transportHom_atomMap _ _)

/-- Construct the lower pointed doctrine map from normalization and admission point clauses. -/
def lower : ExtInstHom (packagePoint (assemblePackage s)) (packagePoint (assemblePackage t)) where
  doctrineHom := {
    sourceMap := CoreLaws.sourceMap (s.val.1.1.val.val) (t.val.1.1.val.val) h hl.extraction
    atomEquiv := Atom.assemble (Atom.pointed h) hl.atom.pointed
    normalize_eq := CoreLaws.normalize_eq (s.val.1.1.val.val) (t.val.1.1.val.val) (s.val.1.1.val.property) (t.val.1.1.val.property) h hl.extraction
    extraction_iff := CoreLaws.extraction_iff (s.val.1.1.val.val) (t.val.1.1.val.val) (s.val.1.1.val.property) (t.val.1.1.val.property) h hl.extraction hl.atom }
  source_eq := CoreLaws.source_eq (s.val.1.1.val.val) (t.val.1.1.val.val) h hl.extraction

variable (p : InvariantWitness.Local.{u, v}
  (assemblePackage s).reading.invariantReading (assemblePackage t).reading.invariantReading mode)

/-- The primitive invariant quotient determines the common Hom table used by every other role. -/
abbrev retained := InvariantWitness.retained _ _ p

/-- Assemble the complete upper native core transport, using the invariant quotient only for its original proof field. -/
def upper (hl : PointLaws s t (retained s t p).table) :
    SignedExactCoreReadingHom (assemblePackage s) (assemblePackage t) := by
  let r := retained s t p
  let h := r.table
  let ho := r.objectRows
  exact {
    atomEquiv := Atom.assemble (Atom.upper h) hl.atom.upper
    extraction_eq := CoreLaws.extracted_family_eq (s.val.1.1.val.val) (t.val.1.1.val.val) (s.val.1.1.val.property) (t.val.1.1.val.property) h hl.extraction hl.atom
    composition_eq := CoreLaws.composition_eq (s.val.1.2.1.val) (t.val.1.2.1.val) (s.val.1.2.1.property) (t.val.1.2.1.property) (s.val.1.2.2.1) (t.val.1.2.2.1) h hl.atom.upper hl.matching hl.generation
    objectMap := CoreLaws.objectMap h ho
    object_formation_eq := CoreLaws.object_formation_eq (s.val.1.2.1.val) (t.val.1.2.1.val) (s.val.1.2.2.1) (t.val.1.2.2.1) h hl.atom.upper hl.matching ho hl.generation
    configurationMap := configurationMap s t h ho hl
    configurationMap_atomMap := configurationMap_atomMap s t h ho hl
    configuration_eq := CoreLaws.configuration_eq (s.val.1.2.1.val) (t.val.1.2.1.val) (s.val.1.2.2.1) (t.val.1.2.2.1) h hl.atom.upper hl.matching ho hl.generation
    equationTransport := EquationAssembly.assemble (s.val.2.2.1.val) (t.val.2.2.1.val) (s.val.2.2.1.property.choose) (t.val.2.2.1.property.choose) (s.val.2.2.1.property.choose_spec) (t.val.2.2.1.property.choose_spec) h hl.equationRows
      hl.contextRows hl.atom.upper ho hl.observableRows hl.equationPoints
    detectorCode_eq := Detector.native_of_points h hl.atom.upper (s.val.2.2.1.val) (t.val.2.2.1.val) (s.val.2.2.2.val) (t.val.2.2.2.val) (s.val.2.2.2.property.choose) (t.val.2.2.2.property.choose) hl.equationRows hl.detector
    operationMap := fun {A B} op => Operation.assemble h ho (Operations.carrier (s.val.1.2.2.2.2.2.val)) (Operations.carrier (t.val.1.2.2.2.2.2.val))
      hl.operationRows A B op
    operation_naturality := fun {A B} op => ((OperationNatural.native_configuration_square_iff (s.val.1.2.2.2.2.2.val) (t.val.1.2.2.2.2.2.val) (s.val.1.2.2.2.2.2.property.choose) (t.val.1.2.2.2.2.2.property.choose) h ho hl.atom.upper
      hl.operationRows (s.val.1.2.2.2.2.2.property.choose_spec) (t.val.1.2.2.2.2.2.property.choose_spec) (configurationMap s t h ho hl) (configurationMap_atomMap s t h ho hl)).2
        (OperationNatural.nativeSquare_of_points (s.val.1.2.2.2.2.2.val) (t.val.1.2.2.2.2.2.val) (s.val.1.2.2.2.2.2.property.choose) (t.val.1.2.2.2.2.2.property.choose) h ho hl.atom.upper hl.operationRows hl.operationPoints)) A B op
    invariantMap := r.indexMap
    invariant_transport := InvariantWitness.package_transport _ _ p
    axisMap := Signature.axisMap h _ _ hl.axisRows
    coordinateEquiv := Signature.assemble h _ _ hl.axisRows _ _ hl.coordinateRows
    axis_selected_iff := SignatureLaws.selected_of_points (s.val.1.2.2.2.2.1.val) (t.val.1.2.2.2.2.1.val) h hl.axisRows hl.selected
    coordinate_eq := SignatureLaws.nativeCoordinates_of_points (s.val.1.2.2.2.2.1.val) (t.val.1.2.2.2.2.1.val) (s.val.1.2.2.2.2.1.property) (t.val.1.2.2.2.2.1.property) h hl.axisRows ho hl.coordinateRows hl.coordinates }

/-- All computational core Hom components are assembled from common rows; the two Atom roles agree by their local point law. -/
def assemble (hl : PointLaws s t (retained s t p).table) :
    PackageTotalHom (assemblePackage s) (assemblePackage t) where
  base := lower s t (retained s t p).table hl
  upper := upper s t p hl
  atomEquiv_eq := (Atom.pointed_eq_upper (retained s t p).table hl.atom).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageAssembly

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageAssembly
