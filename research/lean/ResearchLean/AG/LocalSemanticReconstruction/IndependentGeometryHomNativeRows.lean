import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeInvariant
import Formal.Util.AssertStandardAxioms

/-!
# Native row laws on the single common Hom table

The component graph laws apply to the same complete reader, including its
inactive candidates. The recovery APIs identify the maps reconstructed from
these rows with the original maps. Preservation of primitive object responses
is a separate obligation; graph totality alone does not assert those laws.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (raw : RawQuery G.core.object H.core.object mode → Bool)
variable (realization : RealizationQuery G.core.object H.core.object mode → Bool)

/-- The original pointed/upper equality supplies both inverse Atom rows and their pointwise agreement. -/
theorem readWith_atom_rows : Atom.IsCoherent (readWith mode f a raw realization) := by
  refine ⟨Atom.read_isLawful _, Atom.read_isLawful _, ?_⟩
  intro x y
  exact congrArg (fun e => Atom.read e .forward x y) f.atomEquiv_eq.symm

/-- Upper Atom row assembly restores the actual native equivalence. -/
theorem readWith_atom_assemble : Atom.assemble (Atom.upper (readWith mode f a raw realization))
    (readWith_atom_rows mode f a raw realization).upper = f.upper.atomEquiv :=
  Atom.assemble_read _

/-- Pointed Atom row assembly restores the original lower equivalence independently. -/
theorem readWith_pointed_assemble : Atom.assemble (Atom.pointed (readWith mode f a raw realization))
    (readWith_atom_rows mode f a raw realization).pointed = f.base.doctrineHom.atomEquiv :=
  Atom.assemble_read _

/-- Completing derived family/configuration flags leaves the native common reader unchanged. -/
theorem readWith_completeMatching : TransportMatch.completeMatching (readWith mode f a raw realization)
    (readWith_atom_rows mode f a raw realization).upper = readWith mode f a raw realization := by
  classical
  funext q
  cases q <;> try rfl
  case familyTransport F F' =>
    change decide (F' = F.transport (Atom.assemble _ _)) = decide (F' = F.transport f.upper.atomEquiv)
    rw [readWith_atom_assemble]
  case configurationTransport C C' =>
    change decide (C' = C.transport (Atom.assemble _ _)) = decide (C' = C.transport f.upper.atomEquiv)
    rw [readWith_atom_assemble]

/-- Native matching flags obey positive point comparisons and finite negative witnesses. -/
theorem readWith_matching : TransportMatch.IsLawful (readWith mode f a raw realization) := by
  have hm := TransportMatch.completeMatching_isLawful (readWith mode f a raw realization)
    (readWith_atom_rows mode f a raw realization).upper
  rw [readWith_completeMatching] at hm
  exact hm

/-- Source rows retain the original directed carrier graph laws. -/
theorem readWith_source_rows : IndependentCarrierGraph.IsLawful
    G.core.reading.doctrine.Source H.core.reading.doctrine.Source
    (source (readWith mode f a raw realization)) :=
  IndependentCarrierGraph.read_isLawful _ _ f.base.doctrineHom.sourceMap

/-- Source row assembly restores the original normalization-preserving source function. -/
theorem readWith_source_assemble : IndependentCarrierGraph.assemble _ _
    (source (readWith mode f a raw realization)) (readWith_source_rows mode f a raw realization) =
      f.base.doctrineHom.sourceMap :=
  IndependentCarrierGraph.assemble_read _ _ _

/-- The complete table has exactly the native equation-index inverse rows. -/
theorem readWith_equation_rows : IndependentInverseGraph.IsLawful
    G.core.equationSystem.Index H.core.equationSystem.Index
    (InverseRows.equation (readWith mode f a raw realization) G.core.object H.core.object) := by
  rw [readWith_equation]
  exact IndependentInverseGraph.read_isLawful _ _ _

/-- Both context directions obey their original order and equivalence comparison laws. -/
theorem readWith_context_rows : Context.IsLawful G.core.contextPreorder.le H.core.contextPreorder.le
    (Context.points (readWith mode f a raw realization) G.core.object H.core.object) := by
  rw [readWith_context]
  exact Context.read_isLawful _ _ _

/-- Operation rows retain all candidate endpoint laws and native directed totality on the common table. -/
theorem readWith_operation_rows : Operation.IsLawful (readWith mode f a raw realization)
    G.core.reading.operationReading.Op H.core.reading.operationReading.Op := by
  change IndependentIndexedCarrierGraph.IsLawful (Operation.endpoints (indices mode f a))
    _ _ (Operation.points (readWith mode f a raw realization))
  rw [readWith_operation]
  exact operationRows_lawful mode f a

/-- The complete table has the original directed axis rows, without requiring an axis inverse. -/
theorem readWith_axis_rows : IndependentCarrierGraph.IsLawful
    G.core.algebra.signatureReading.Axis H.core.algebra.signatureReading.Axis
    (signatureAxis (readWith mode f a raw realization)) :=
  IndependentCarrierGraph.read_isLawful _ _ f.upper.axisMap

/-- Both coordinate directions retain every outer and inner candidate-row law. -/
theorem readWith_signature_rows : Signature.IsLawful (readWith mode f a raw realization)
    G.core.algebra.signatureReading.Axis H.core.algebra.signatureReading.Axis
    G.core.algebra.signatureReading.Coordinate H.core.algebra.signatureReading.Coordinate := by
  change IndependentCandidateIndexedInverseGraph.IsLawful _ _
    (Signature.axisPoints (indices mode f a) _ _) _ _ (Signature.points (readWith mode f a raw realization))
  rw [readWith_signature]
  exact signatureRows_lawful mode f a

/-- Observable rows retain inactive-context normalization, inverse graphs, and all ring-operation laws. -/
theorem readWith_observable_rows : Observable.IsLawful (readWith mode f a raw realization)
    (fun W => G.core.equationSystem.Observable ⟨W⟩) (fun V => H.core.equationSystem.Observable ⟨V⟩) := by
  have he : Observable.contextPoints (readWith mode f a raw realization) =
      Observable.contextPoints (indices mode f a) (A := G.core.object) (B := H.core.object) := by
    funext W V
    exact (congrFun (congrFun (congrFun (readWith_context mode f a raw realization) .forward) W) V).trans
      (congrFun (congrFun (congrFun (context_indices mode f a) .forward) W) V).symm
  change IndependentIndexedRingGraph.IsLawful _ _ _
    (Observable.points (readWith mode f a raw realization) G.core.object H.core.object)
  rw [he, readWith_observable]
  exact observableRows_lawful mode f a

/-- The native object function is restored from the complete table's unique object rows. -/
theorem readWith_object_assemble : CoreLaws.objectMap (readWith mode f a raw realization)
    (readWith_object_rows mode f a raw realization) = f.upper.objectMap :=
  retainedWith_objectMap mode f a raw realization

/-- The actual native context equivalence is restored from the complete table's context rows. -/
theorem readWith_context_assemble : Context.assemble G.core.contextPreorder H.core.contextPreorder
    (Context.points (readWith mode f a raw realization) G.core.object H.core.object)
    (readWith_context_rows mode f a raw realization) = f.upper.equationTransport.contextEquivalence := by
  have he : (⟨Context.points (readWith mode f a raw realization) G.core.object H.core.object,
      readWith_context_rows mode f a raw realization⟩ :
      {p // Context.IsLawful G.core.contextPreorder.le H.core.contextPreorder.le p}) =
    ⟨Context.read G.core.contextPreorder H.core.contextPreorder f.upper.equationTransport.contextEquivalence,
      Context.read_isLawful _ _ f.upper.equationTransport.contextEquivalence⟩ :=
    Subtype.ext (readWith_context mode f a raw realization)
  exact (congrArg (Context.readingEquiv G.core.contextPreorder H.core.contextPreorder).symm he).trans
    (Context.assemble_read _ _ f.upper.equationTransport.contextEquivalence)

/-- The directed axis function assembled from the common reader is the original native function. -/
theorem readWith_axis_assemble : Signature.axisMap (readWith mode f a raw realization) _ _
    (readWith_axis_rows mode f a raw realization) = f.upper.axisMap :=
  IndependentCarrierGraph.assemble_read _ _ _

/-- Operation assembly on the complete reader recovers the whole native dependent function family. -/
theorem readWith_operation_assemble_heq : HEq
    (Operation.assemble (readWith mode f a raw realization) (readWith_object_rows mode f a raw realization)
      G.core.reading.operationReading.Op H.core.reading.operationReading.Op
      (readWith_operation_rows mode f a raw realization))
    (fun A B => f.upper.operationMap (A := A) (B := B)) := by
  have he : (⟨Operation.points (readWith mode f a raw realization),
      readWith_operation_rows mode f a raw realization⟩ :
      {p // IndependentIndexedCarrierGraph.IsLawful (Operation.endpoints (indices mode f a))
        (Operation.Fiber G.core.reading.operationReading.Op) (Operation.Fiber H.core.reading.operationReading.Op) p}) =
    Operation.readingEquiv (indices mode f a) (object_rows mode f a)
      G.core.reading.operationReading.Op H.core.reading.operationReading.Op (operationFamily mode f a) :=
    Subtype.ext (readWith_operation mode f a raw realization)
  have hm := (congrArg (Operation.readingEquiv (indices mode f a) (object_rows mode f a)
    G.core.reading.operationReading.Op H.core.reading.operationReading.Op).symm he).trans
      (Operation.assemble_read (indices mode f a) (object_rows mode f a)
        G.core.reading.operationReading.Op H.core.reading.operationReading.Op (operationFamily mode f a))
  exact (heq_of_eq hm).trans (operationFamily_heq mode f a)

/-- Signature assembly recovers the whole native coordinate-equivalence family over the directed axis map. -/
theorem readWith_signature_assemble_heq : HEq
    (Signature.assemble (readWith mode f a raw realization) _ _ (readWith_axis_rows mode f a raw realization)
      G.core.algebra.signatureReading.Coordinate H.core.algebra.signatureReading.Coordinate
      (readWith_signature_rows mode f a raw realization)) f.upper.coordinateEquiv := by
  have he : (⟨Signature.points (readWith mode f a raw realization),
      readWith_signature_rows mode f a raw realization⟩ :
      {p // IndependentCandidateIndexedInverseGraph.IsLawful
        G.core.algebra.signatureReading.Axis H.core.algebra.signatureReading.Axis
        (Signature.axisPoints (indices mode f a) _ _) G.core.algebra.signatureReading.Coordinate
        H.core.algebra.signatureReading.Coordinate p}) =
    Signature.readingEquiv (indices mode f a) _ _ (axis_rows mode f a)
      G.core.algebra.signatureReading.Coordinate H.core.algebra.signatureReading.Coordinate (signatureFamily mode f a) :=
    Subtype.ext (readWith_signature mode f a raw realization)
  have hm := (congrArg (Signature.readingEquiv (indices mode f a) _ _ (axis_rows mode f a)
    G.core.algebra.signatureReading.Coordinate H.core.algebra.signatureReading.Coordinate).symm he).trans
      (Signature.assemble_read (indices mode f a) _ _ (axis_rows mode f a)
        G.core.algebra.signatureReading.Coordinate H.core.algebra.signatureReading.Coordinate (signatureFamily mode f a))
  exact (heq_of_eq hm).trans (signatureFamily_heq mode f a)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
