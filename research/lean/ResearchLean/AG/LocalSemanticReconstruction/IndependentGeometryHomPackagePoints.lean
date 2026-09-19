import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPackageAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Primitive point recovery for the assembled complete core Hom

These are the component computation laws of the actual package assembler.
Each statement reads the constructed native map, including inactive candidate
carriers where applicable. They connect the independent preservation rules to
the subsequent complete geometry Hom assembly and separation proof.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageAssembly

noncomputable section

universe u v

open Site AtomFoundation IndependentCoreTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode}
variable (s t : PackageData U)
variable (p : InvariantWitness.Local.{u, v}
  (assemblePackage s).reading.invariantReading (assemblePackage t).reading.invariantReading mode)
variable (hl : PointLaws s t (retained s t p).table)

/-- The assembled lower source map restores all active and inactive carrier point queries. -/
theorem read_source : IndependentCarrierGraph.read _ _
    (assemble s t p hl).base.doctrineHom.sourceMap = source (retained s t p).table :=
  IndependentCarrierGraph.read_assemble _ _ _ hl.extraction.source

/-- Both pointed Atom directions are recovered from the actual lower Hom component. -/
theorem read_pointedAtom : Atom.read (assemble s t p hl).base.doctrineHom.atomEquiv =
    Atom.pointed (retained s t p).table := Atom.read_assemble _ hl.atom.pointed

/-- Both upper Atom directions are recovered separately from the lower component. -/
theorem read_atom : Atom.read (assemble s t p hl).upper.atomEquiv =
    Atom.upper (retained s t p).table := Atom.read_assemble _ hl.atom.upper

/-- A true object point is exactly the object image of the assembled package Hom. -/
theorem object_point_iff (A B : ArchitectureObject U) :
    (retained s t p).table (.object A B) = true ↔ (assemble s t p hl).upper.objectMap A = B :=
  (retained s t p).object_point_iff A B

/-- The native equation equivalence restores both point directions and inactive carriers. -/
theorem read_equation : IndependentInverseGraph.read _ _ (assemble s t p hl).upper.equationEquiv =
    InverseRows.equation (retained s t p).table (generatedObject s.val.1) (generatedObject t.val.1) :=
  IndependentInverseGraph.read_assemble _ _ _ hl.equationRows

/-- The native context equivalence restores the forward and backward context tables. -/
theorem read_context : Context.read (context s.val.2.1) (context t.val.2.1)
    (assemble s t p hl).upper.equationTransport.contextEquivalence =
      Context.points (retained s t p).table (generatedObject s.val.1) (generatedObject t.val.1) :=
  Context.read_assemble _ _ _ hl.contextRows

/-- A true forward Atom cell identifies the assembled upper image. -/
theorem atom_point_iff (a b : U.Atom) :
    (retained s t p).table (.atom .forward a b) = true ↔
      (assemble s t p hl).upper.atomEquiv a = b :=
  (Atom.graph _ hl.atom.upper .forward).edge_eq_true_iff_target_eq a b

/-- A true active equation cell identifies the assembled equation image. -/
theorem equation_point_iff (i : (assemblePackage s).equationSystem.Index)
    (j : (assemblePackage t).equationSystem.Index) :
    (retained s t p).table (.atObjects (assemblePackage s).object (assemblePackage t).object
      (.equation .forward (.edge (assemblePackage s).equationSystem.Index
        (assemblePackage t).equationSystem.Index i j))) = true ↔
      (assemble s t p hl).upper.equationEquiv i = j :=
  EquationLaws.equation_forward_iff s.val.2.2.1.val t.val.2.2.1.val _ hl.equationRows i j

/-- The forward context function retains precisely its original true point pairs. -/
theorem context_point_iff (W : ArchCtx (assemblePackage s).object)
    (V : ArchCtx (assemblePackage t).object) :
    (retained s t p).table (.atObjects (assemblePackage s).object (assemblePackage t).object
      (.context .forward W V)) = true ↔ ((assemble s t p hl).upper.equationTransport.contextEquivalence.functor.obj ⟨W⟩).ctx = V := by
  let c := Context.code (context s.val.2.1) (context t.val.2.1)
    (Context.points (retained s t p).table _ _) hl.contextRows
  change c.forwardCode.edge ⟨W⟩ ⟨V⟩ = true ↔ (c.forwardCode.assemble ⟨W⟩).ctx = V
  rw [c.forwardCode.edge_eq_true_iff_target_eq]
  constructor
  · exact congrArg ContextCategoryObject.ctx
  · intro he
    cases c.forwardCode.assemble ⟨W⟩
    cases he
    rfl

/-- The backward context function also retains every true pair, without imposing object bijectivity. -/
theorem context_backward_point_iff (W : ArchCtx (assemblePackage s).object)
    (V : ArchCtx (assemblePackage t).object) :
    (retained s t p).table (.atObjects (assemblePackage s).object (assemblePackage t).object
      (.context .backward W V)) = true ↔ ((assemble s t p hl).upper.equationTransport.contextEquivalence.inverse.obj ⟨V⟩).ctx = W := by
  let c := Context.code (context s.val.2.1) (context t.val.2.1)
    (Context.points (retained s t p).table _ _) hl.contextRows
  change c.backwardCode.edge ⟨V⟩ ⟨W⟩ = true ↔ (c.backwardCode.assemble ⟨V⟩).ctx = W
  rw [c.backwardCode.edge_eq_true_iff_target_eq]
  constructor
  · exact congrArg ContextCategoryObject.ctx
  · intro he
    cases c.backwardCode.assemble ⟨V⟩
    cases he
    rfl

/-- The operation map's full candidate endpoint/carrier table survives native assembly. -/
theorem read_operation : (Operation.readingEquiv (retained s t p).table (retained s t p).objectRows
    (fun A B => (assemblePackage s).reading.operationReading.Op A B)
    (fun A B => (assemblePackage t).reading.operationReading.Op A B)
    (fun A B op => (assemble s t p hl).upper.operationMap (A := A) (B := B) op)).val =
      Operation.points (retained s t p).table :=
  Operation.read_assemble _ _ _ _ hl.operationRows

/-- The original directed invariant-index graph is restored after auxiliary witness erasure. -/
theorem read_invariant : IndependentCarrierGraph.read _ _ (assemble s t p hl).upper.invariantMap =
    invariant (retained s t p).table :=
  IndependentCarrierGraph.read_assemble _ _ _ (retained s t p).indexRows

/-- The directed signature-axis graph is preserved, including inactive candidate carriers. -/
theorem read_axis : IndependentCarrierGraph.read _ _ (assemble s t p hl).upper.axisMap =
    signatureAxis (retained s t p).table :=
  IndependentCarrierGraph.read_assemble _ _ _ hl.axisRows

/-- A true axis point is exactly the reconstructed native axis image. -/
theorem axis_point_iff (i : (assemblePackage s).algebra.signatureReading.Axis)
    (j : (assemblePackage t).algebra.signatureReading.Axis) :
    (retained s t p).table (.signatureAxis (.edge (assemblePackage s).algebra.signatureReading.Axis
      (assemblePackage t).algebra.signatureReading.Axis i j)) = true ↔
        (assemble s t p hl).upper.axisMap i = j :=
  Signature.axis_forward_iff _ _ _ hl.axisRows i j

/-- Full coordinate-family reading recovers the active and inactive axis/carrier candidates. -/
theorem read_signatureCoordinates : (Signature.readingEquiv (retained s t p).table _ _ hl.axisRows
    (assemblePackage s).algebra.signatureReading.Coordinate
    (assemblePackage t).algebra.signatureReading.Coordinate (assemble s t p hl).upper.coordinateEquiv).val =
      Signature.points (retained s t p).table :=
  Signature.read_assemble _ _ _ _ _ _ hl.coordinateRows

/-- Complete observable-family reading recovers all context and value-carrier point rows. -/
theorem read_observables :
    letI := ObservableNatural.rings s.val.2.2.1.val s.val.2.2.1.property.choose s.val.2.2.1.property.choose_spec
    letI := ObservableNatural.rings t.val.2.2.1.val t.val.2.2.1.property.choose t.val.2.2.1.property.choose_spec
    (Observable.readingEquiv (context s.val.2.1) (context t.val.2.1)
    (retained s t p).table hl.contextRows
    (IndependentEquationPrimitive.observableType s.val.2.2.1.val)
    (IndependentEquationPrimitive.observableType t.val.2.2.1.val)
    (assemble s t p hl).upper.equationTransport.observableEquiv).val =
      Observable.points (retained s t p).table (generatedObject s.val.1) (generatedObject t.val.1) := by
  letI := ObservableNatural.rings s.val.2.2.1.val s.val.2.2.1.property.choose s.val.2.2.1.property.choose_spec
  letI := ObservableNatural.rings t.val.2.2.1.val t.val.2.2.1.property.choose t.val.2.2.1.property.choose_spec
  exact Observable.read_assemble _ _ _ _ _ _ hl.observableRows

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageAssembly

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageAssembly
