import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRows
import Formal.Util.AssertStandardAxioms

/-!
# Native preservation laws on independent object stages

The source and target are assembled from the original independent primitive
tables. Native map recovery identifies the maps used in the existing converse
point-law APIs, so normalization, extraction, generation, operation, and signature
preservation follow from the original Hom fields. Dependent indices and their
families are compared as Sigma pairs before transporting preservation equations.
The primitive point predicates remain unchanged; no native preservation field
is added to their local data.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U) (mode : Mode)
variable (f : PackageTotalHom (assemble s).core (assemble t).core)
variable (a : (assemble s).Coefficient →+* (assemble t).Coefficient)
variable (raw : RawQuery (assemble s).core.object (assemble t).core.object mode → Bool)
variable (realization : RealizationQuery (assemble s).core.object (assemble t).core.object mode → Bool)

/-- Native normalization and extraction imply every guarded primitive extraction instance on the original stages. -/
theorem readWith_extraction : CoreLaws.ExtractionLaws s.1.val.1.1.val.val t.1.val.1.1.val.val
    (readWith mode f a raw realization) := by
  apply CoreLaws.extractionLaws_of_native s.1.val.1.1.val.val t.1.val.1.1.val.val
    s.1.val.1.1.val.property t.1.val.1.1.val.property (readWith mode f a raw realization)
    (readWith_source_rows mode f a raw realization) (readWith_atom_rows mode f a raw realization).pointed
  · exact (congrFun (readWith_source_assemble mode f a raw realization) _).trans f.base.source_eq
  · intro x
    exact (congrArg (assemble t).core.reading.doctrine.normalize
      (congrFun (readWith_source_assemble mode f a raw realization) x)).trans
        ((f.base.doctrineHom.normalize_eq x).trans
          (congrFun (readWith_source_assemble mode f a raw realization)
            ((assemble s).core.reading.doctrine.normalize x)).symm)
  · intro x z
    exact (f.base.doctrineHom.extraction_iff x z).trans (Iff.of_eq
      (congrArg₂ (assemble t).core.reading.doctrine.extracts
        (congrFun (readWith_source_assemble mode f a raw realization) x).symm
        (congrArg (fun e : U.Atom ≃ U.Atom => e z)
          (readWith_pointed_assemble mode f a raw realization)).symm))

/-- Native composition, formation, and configuration preservation imply all primitive generation rules. -/
theorem readWith_generation : CoreLaws.GenerationLaws s.1.val.1.2.1.val t.1.val.1.2.1.val
    s.1.val.1.2.2.1 t.1.val.1.2.2.1 (readWith mode f a raw realization) := by
  have ha : TransportMatch.atomEquiv (readWith mode f a raw realization)
      (readWith_atom_rows mode f a raw realization).upper = f.upper.atomEquiv :=
    readWith_atom_assemble mode f a raw realization
  apply CoreLaws.generationLaws_of_native s.1.val.1.2.1.val t.1.val.1.2.1.val
    s.1.val.1.2.1.property t.1.val.1.2.1.property s.1.val.1.2.2.1 t.1.val.1.2.2.1
    (readWith mode f a raw realization) (readWith_atom_rows mode f a raw realization).upper
    (readWith_matching mode f a raw realization) (readWith_object_rows mode f a raw realization)
  · rw [ha]
    exact f.upper.composition_eq
  · rw [readWith_object_assemble, ha]
    exact f.upper.object_formation_eq
  · rw [readWith_object_assemble, ha]
    exact f.upper.configuration_eq

/-- Native selected-axis preservation supplies all candidate-axis point comparisons on the independent stages. -/
theorem readWith_selected : SignatureLaws.SelectedPoints s.1.val.1.2.2.2.2.1.val t.1.val.1.2.2.2.2.1.val
    (readWith mode f a raw realization) := by
  apply SignatureLaws.selected_points_of_native s.1.val.1.2.2.2.2.1.val t.1.val.1.2.2.2.2.1.val
    (readWith mode f a raw realization) (readWith_axis_rows mode f a raw realization)
  intro i
  exact (f.upper.axis_selected_iff i).trans (Iff.of_eq
    (congrArg (assemble t).core.algebra.signatureReading.selected
      (congrFun (readWith_axis_assemble mode f a raw realization) i).symm))

/-- Native operation naturality gives every guarded primitive operation-action square. -/
theorem readWith_operation_preservation : OperationNatural.PointLaws s.1.val.1.2.2.2.2.2.val
    t.1.val.1.2.2.2.2.2.val (readWith mode f a raw realization) := by
  let D := Σ F : ArchitectureObject U → ArchitectureObject U,
    ∀ A B, (assemble s).core.reading.operationReading.Op A B →
      (assemble t).core.reading.operationReading.Op (F A) (F B)
  have he : (⟨CoreLaws.objectMap (readWith mode f a raw realization) (readWith_object_rows mode f a raw realization),
      Operation.assemble (readWith mode f a raw realization) (readWith_object_rows mode f a raw realization)
        (assemble s).core.reading.operationReading.Op (assemble t).core.reading.operationReading.Op
        (readWith_operation_rows mode f a raw realization)⟩ : D) =
    ⟨f.upper.objectMap, fun A B => f.upper.operationMap (A := A) (B := B)⟩ :=
    Sigma.ext (readWith_object_assemble mode f a raw realization)
      (readWith_operation_assemble_heq mode f a raw realization)
  have hs := congrArg (fun d : D => ∀ (A B : ArchitectureObject U)
    (op : (assemble s).core.reading.operationReading.Op A B) (x : U.Atom),
    ((assemble t).core.reading.operationReading.configurationMap (d.2 A B op)).atomMap (f.upper.atomEquiv x) =
      f.upper.atomEquiv (((assemble s).core.reading.operationReading.configurationMap op).atomMap x)) he
  have hn : ∀ (A B : ArchitectureObject U) (op : (assemble s).core.reading.operationReading.Op A B) (x : U.Atom),
      ((assemble t).core.reading.operationReading.configurationMap (f.upper.operationMap op)).atomMap
        (f.upper.atomEquiv x) =
      f.upper.atomEquiv (((assemble s).core.reading.operationReading.configurationMap op).atomMap x) := by
    intro A B op x
    have hh := congrArg (fun c => c.atomMap x) (f.upper.operation_naturality op)
    change ((assemble t).core.reading.operationReading.configurationMap (f.upper.operationMap op)).atomMap
      ((f.upper.configurationMap A).atomMap x) = (f.upper.configurationMap B).atomMap
        (((assemble s).core.reading.operationReading.configurationMap op).atomMap x) at hh
    rw [f.upper.configurationMap_atomMap A, f.upper.configurationMap_atomMap B] at hh
    exact hh
  have hp := Eq.mpr hs hn
  apply OperationNatural.points_of_nativeSquare s.1.val.1.2.2.2.2.2.val t.1.val.1.2.2.2.2.2.val
    s.1.val.1.2.2.2.2.2.property.choose t.1.val.1.2.2.2.2.2.property.choose
    (readWith mode f a raw realization) (readWith_object_rows mode f a raw realization)
    (readWith_atom_rows mode f a raw realization).upper (readWith_operation_rows mode f a raw realization)
  intro A B op x
  rw [readWith_atom_assemble mode f a raw realization]
  exact hp A B op x

/-- Native signature coordinates supply every primitive coordinate comparison over object and axis points. -/
theorem readWith_coordinate_preservation : SignatureLaws.CoordinatePoints s.1.val.1.2.2.2.2.1.val
    t.1.val.1.2.2.2.2.1.val (readWith mode f a raw realization) := by
  let D := Σ F : (assemble s).core.algebra.signatureReading.Axis → (assemble t).core.algebra.signatureReading.Axis,
    ∀ i, (assemble s).core.algebra.signatureReading.Coordinate i ≃
      (assemble t).core.algebra.signatureReading.Coordinate (F i)
  have he : (⟨Signature.axisMap (readWith mode f a raw realization) _ _
      (readWith_axis_rows mode f a raw realization),
      Signature.assemble (readWith mode f a raw realization) _ _ (readWith_axis_rows mode f a raw realization)
        (assemble s).core.algebra.signatureReading.Coordinate (assemble t).core.algebra.signatureReading.Coordinate
        (readWith_signature_rows mode f a raw realization)⟩ : D) =
    ⟨f.upper.axisMap, f.upper.coordinateEquiv⟩ :=
    Sigma.ext (readWith_axis_assemble mode f a raw realization)
      (readWith_signature_assemble_heq mode f a raw realization)
  have hs := congrArg (fun d : D => ∀ (M : ArchitectureObject U) (i : (assemble s).core.algebra.signatureReading.Axis),
    d.2 i ((assemble s).core.algebra.signatureReading.coordinate M i) =
      (assemble t).core.algebra.signatureReading.coordinate (f.upper.objectMap M) (d.1 i)) he
  have hp := Eq.mpr hs f.upper.coordinate_eq
  apply SignatureLaws.coordinate_points_of_native s.1.val.1.2.2.2.2.1.val t.1.val.1.2.2.2.2.1.val
    s.1.val.1.2.2.2.2.1.property t.1.val.1.2.2.2.2.1.property (readWith mode f a raw realization)
    (readWith_axis_rows mode f a raw realization) (readWith_object_rows mode f a raw realization)
    (readWith_signature_rows mode f a raw realization)
  intro M i
  rw [readWith_object_assemble mode f a raw realization]
  exact hp M i

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
