import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeIndices
import Formal.Util.AssertStandardAxioms

/-!
# Dependent native families for the common Hom reader

Implementation notes: native index recovery identifies each target fiber
before its point family is read. The casts below transport native data along
those proved index equalities; their heterogeneous recovery APIs record that
the data itself is unchanged. Existing indexed reading equivalences then
provide all candidate rows and their laws, without a second custom encoding.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)

/-- Identify the native operation targets with the object indices read from the same Hom. -/
def operationFamily : ∀ A B, G.core.reading.operationReading.Op A B →
    H.core.reading.operationReading.Op
      (CoreLaws.objectMap (indices mode f a) (object_rows mode f a) A)
      (CoreLaws.objectMap (indices mode f a) (object_rows mode f a) B) :=
  cast (congrArg (fun F => ∀ A B, G.core.reading.operationReading.Op A B →
    H.core.reading.operationReading.Op (F A) (F B)) (objectMap_indices mode f a)).symm
      (fun A B => f.upper.operationMap (A := A) (B := B))

/-- Object-index identification changes no native operation data. -/
theorem operationFamily_heq : HEq (operationFamily mode f a)
    (fun A B => f.upper.operationMap (A := A) (B := B)) := cast_heq _ _

/-- Read the operation family on all candidate endpoint and carrier pairs. -/
def operationRows : IndependentIndexedCarrierGraph.Table.{u + 1, u + 1, u, u}
    (ArchitectureObject U × ArchitectureObject U) (ArchitectureObject U × ArchitectureObject U) :=
  (Operation.readingEquiv (indices mode f a) (object_rows mode f a)
    G.core.reading.operationReading.Op H.core.reading.operationReading.Op (operationFamily mode f a)).val

/-- The native operation reader supplies candidate inactivity and active directed totality. -/
theorem operationRows_lawful : IndependentIndexedCarrierGraph.IsLawful
    (Operation.endpoints (indices mode f a)) (Operation.Fiber G.core.reading.operationReading.Op)
    (Operation.Fiber H.core.reading.operationReading.Op) (operationRows mode f a) :=
  (Operation.readingEquiv (indices mode f a) (object_rows mode f a)
    G.core.reading.operationReading.Op H.core.reading.operationReading.Op (operationFamily mode f a)).property

/-- Identify native signature-coordinate targets with the axis graph's reconstructed indices. -/
def signatureFamily : ∀ i, G.core.algebra.signatureReading.Coordinate i ≃
    H.core.algebra.signatureReading.Coordinate
      (Signature.axisMap (indices mode f a) _ _ (axis_rows mode f a) i) :=
  cast (congrArg (fun F => ∀ i, G.core.algebra.signatureReading.Coordinate i ≃
    H.core.algebra.signatureReading.Coordinate (F i)) (axisMap_indices mode f a)).symm f.upper.coordinateEquiv

/-- The axis identification preserves the whole original coordinate-equivalence family. -/
theorem signatureFamily_heq : HEq (signatureFamily mode f a) f.upper.coordinateEquiv := cast_heq _ _

/-- Read both coordinate directions at every candidate axis and coordinate carrier. -/
def signatureRows : IndependentCandidateIndexedInverseGraph.Table.{u, u, u, u} :=
  (Signature.readingEquiv (indices mode f a) _ _ (axis_rows mode f a)
    G.core.algebra.signatureReading.Coordinate H.core.algebra.signatureReading.Coordinate
    (signatureFamily mode f a)).val

/-- Signature readings supply all outer/inner candidate normalization and inverse-row laws. -/
theorem signatureRows_lawful : IndependentCandidateIndexedInverseGraph.IsLawful
    G.core.algebra.signatureReading.Axis H.core.algebra.signatureReading.Axis
    (Signature.axisPoints (indices mode f a) _ _) G.core.algebra.signatureReading.Coordinate
    H.core.algebra.signatureReading.Coordinate (signatureRows mode f a) :=
  (Signature.readingEquiv (indices mode f a) _ _ (axis_rows mode f a)
    G.core.algebra.signatureReading.Coordinate H.core.algebra.signatureReading.Coordinate
    (signatureFamily mode f a)).property

/-- Identify the original observable-ring family along recovery of the full context equivalence. -/
def observableFamily : ∀ W : ContextCategoryObject G.core.contextPreorder,
    G.core.equationSystem.Observable W ≃+* H.core.equationSystem.Observable
      ((Context.assemble G.core.contextPreorder H.core.contextPreorder
        (Context.points (indices mode f a) G.core.object H.core.object) (context_rows mode f a)).functor.obj W) :=
  cast (congrArg (fun E : ContextCategoryObject G.core.contextPreorder ≌ ContextCategoryObject H.core.contextPreorder =>
    ∀ W, G.core.equationSystem.Observable W ≃+* H.core.equationSystem.Observable (E.functor.obj W))
      (context_assemble_indices mode f a)).symm f.upper.equationTransport.observableEquiv

/-- Context-index recovery preserves every original observable-ring equivalence. -/
theorem observableFamily_heq : HEq (observableFamily mode f a) f.upper.equationTransport.observableEquiv := cast_heq _ _

/-- Read every observable inverse graph at its candidate context and value-carrier pair. -/
def observableRows : IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u}
    (ArchCtx G.core.object) (ArchCtx H.core.object) :=
  (Observable.readingEquiv G.core.contextPreorder H.core.contextPreorder (indices mode f a) (context_rows mode f a)
    (fun W => G.core.equationSystem.Observable ⟨W⟩) (fun V => H.core.equationSystem.Observable ⟨V⟩)
    (observableFamily mode f a)).val

/-- The observable reader supplies inverse graph and ring-operation laws on all candidate rows. -/
theorem observableRows_lawful : IndependentIndexedRingGraph.IsLawful
    (Observable.contextPoints (indices mode f a)) (fun W => G.core.equationSystem.Observable ⟨W⟩)
    (fun V => H.core.equationSystem.Observable ⟨V⟩) (observableRows mode f a) :=
  (Observable.readingEquiv G.core.contextPreorder H.core.contextPreorder (indices mode f a) (context_rows mode f a)
    (fun W => G.core.equationSystem.Observable ⟨W⟩) (fun V => H.core.equationSystem.Observable ⟨V⟩)
    (observableFamily mode f a)).property

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
