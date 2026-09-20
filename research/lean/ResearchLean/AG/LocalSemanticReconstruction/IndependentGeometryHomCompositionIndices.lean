import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeIndices
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomAtomComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphComposition
import Formal.Util.AssertStandardAxioms

/-!
# Direct scalar and index composition on the common Hom declaration

Implementation notes: each role follows its original primitive point graphs.
The first row selects an intermediate index or value and the second row supplies
the output flag. Equation and context backward rows reverse this order. Native
package composition is used only to verify the construction. Dependent value
rows are supplied after these index rows, as in the common native reader.
-/

namespace AAT.AG.LocalSemanticReconstruction

noncomputable section

universe u v w

namespace IndependentCarrierGraph

/-- The direct point composition API reads the ordinary composite of the two assembled functions. -/
theorem compose_eq_read (A : Type u) (B : Type v) (C : Type w)
    (h : Table.{u, v}) (hh : IsLawful A B h) (k : Table.{v, w}) (hk : IsLawful B C k) :
    compose A B C h hh k = read A C (assemble B C k hk ∘ assemble A B h hh) :=
  (read_assemble A C (compose A B C h hh k) (compose_isLawful A B C h hh k hk)).symm.trans
    (congrArg (read A C) (assemble_compose A B C h hh k hk))

end IndependentCarrierGraph

namespace IndependentGeometryHomPrimitive.Composition

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)

/-- Compose the primitive equation and context index rows at the independently generated endpoints. -/
def dependentIndices : DependentQuery mode (assemble s).core.object (assemble r).core.object → Bool
  | .equation d z => InverseRows.fromInverse
      (IndependentInverseGraph.compose (assemble s).core.equationSystem.Index
        (assemble t).core.equationSystem.Index (assemble r).core.equationSystem.Index
        (InverseRows.equation (PackageAssembly.retained s.1 t.1 p).table
          (assemble s).core.object (assemble t).core.object) hp.equationRows
        (InverseRows.equation (PackageAssembly.retained t.1 r.1 q).table
          (assemble t).core.object (assemble r).core.object) hq.equationRows) d z
  | .context d W Z => Context.compose (assemble s).core.contextPreorder
      (assemble t).core.contextPreorder (assemble r).core.contextPreorder
      (Context.points (PackageAssembly.retained s.1 t.1 p).table
        (assemble s).core.object (assemble t).core.object) hp.contextRows
      (Context.points (PackageAssembly.retained t.1 r.1 q).table
        (assemble t).core.object (assemble r).core.object) hq.contextRows d W Z
  | _ => false

/-- The primitive dependent index composition agrees with the original native core composition. -/
theorem dependentIndices_eq_native : dependentIndices s t r p hp q hq =
    NativeReader.dependentIndices mode
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq)) := by
  funext z
  cases z with
  | equation d z =>
    exact congrArg (fun h => InverseRows.fromInverse h d z)
      (IndependentInverseGraph.compose_eq_read _ _ _ _ hp.equationRows _ hq.equationRows)
  | context d W Z =>
    exact congrArg (fun h => h d W Z)
      (Context.compose_eq_read _ _ _ _ hp.contextRows _ hq.contextRows)
  | observable => rfl
  | raw => rfl
  | realization => rfl

variable (cp : GeometryComponents.CoefficientPoints s t p)

/-- Compose every scalar/index role directly on the common query type, normalizing other rows to false. -/
def indices : Table.{u, v} U mode := by
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let k := (PackageAssembly.retained t.1 r.1 q).table
  intro z
  exact match z with
  | .source z => IndependentCarrierGraph.compose (assemble s).core.reading.doctrine.Source
      (assemble t).core.reading.doctrine.Source (assemble r).core.reading.doctrine.Source
      (source h) hp.extraction.source (source k) z
  | .pointedAtom d a c => Atom.compose (Atom.pointed h) hp.atom.pointed (Atom.pointed k) hq.atom.pointed d a c
  | .atom d a c => Atom.compose (Atom.upper h) hp.atom.upper (Atom.upper k) hq.atom.upper d a c
  | .object A C => k (.object (CoreLaws.objectMap h (PackageAssembly.retained s.1 t.1 p).objectRows A) C)
  | .invariant z => IndependentCarrierGraph.compose (assemble s).core.reading.invariantReading.Index
      (assemble t).core.reading.invariantReading.Index (assemble r).core.reading.invariantReading.Index
      (invariant h) (PackageAssembly.retained s.1 t.1 p).indexRows (invariant k) z
  | .signatureAxis z => IndependentCarrierGraph.compose (assemble s).core.algebra.signatureReading.Axis
      (assemble t).core.algebra.signatureReading.Axis (assemble r).core.algebra.signatureReading.Axis
      (signatureAxis h) hp.axisRows (signatureAxis k) z
  | .coefficient z => IndependentCarrierGraph.compose (assemble s).Coefficient
      (assemble t).Coefficient (assemble r).Coefficient (coefficient h) cp.1 (coefficient k) z
  | .familyTransport F F' => k (.familyTransport (F.transport (Atom.assemble (Atom.upper h) hp.atom.upper)) F')
  | .configurationTransport C C' => k (.configurationTransport (C.transport (Atom.assemble (Atom.upper h) hp.atom.upper)) C')
  | .atObjects A C z => NativeReader.liftDependent mode (assemble s).core.object (assemble r).core.object
      (dependentIndices s t r p hp q hq) A C z
  | _ => false

/-- Every directly composed index cell equals the common reader of native core and coefficient composition. -/
theorem indices_eq_native (cq : GeometryComponents.CoefficientPoints t r q) : indices s t r p hp q hq cp =
    NativeReader.indices mode
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) := by
  classical
  funext z
  cases z with
  | source z => exact congrFun (IndependentCarrierGraph.compose_eq_read _ _ _ _ hp.extraction.source _ hq.extraction.source) z
  | pointedAtom d a c => exact congrArg (fun h => h d a c) (Atom.compose_eq_read _ hp.atom.pointed _ hq.atom.pointed)
  | atom d a c => exact congrArg (fun h => h d a c) (Atom.compose_eq_read _ hp.atom.upper _ hq.atom.upper)
  | object A C =>
    apply Bool.eq_iff_iff.mpr
    exact (PackageAssembly.object_point_iff t.1 r.1 q hq _ C).trans decide_eq_true_iff.symm
  | invariant z => exact congrFun (IndependentCarrierGraph.compose_eq_read _ _ _ _
      (PackageAssembly.retained s.1 t.1 p).indexRows _ (PackageAssembly.retained t.1 r.1 q).indexRows) z
  | signatureAxis z => exact congrFun (IndependentCarrierGraph.compose_eq_read _ _ _ _ hp.axisRows _ hq.axisRows) z
  | coefficient z => exact congrFun (IndependentCarrierGraph.compose_eq_read _ _ _ _ cp.1 _ cq.1) z
  | familyTransport F F' =>
    apply Bool.eq_iff_iff.mpr
    exact (TransportMatch.family_iff _ hq.atom.upper hq.matching _ F').trans
      ((congrArg (fun H => F' = H) (AtomFoundation.atomFamily_transport_comp F
        (Atom.assemble _ hp.atom.upper) (Atom.assemble _ hq.atom.upper))).to_iff.trans decide_eq_true_iff.symm)
  | configurationTransport C C' =>
    apply Bool.eq_iff_iff.mpr
    exact (TransportMatch.configuration_iff _ hq.atom.upper hq.matching _ C').trans
      ((congrArg (fun H => C' = H) (AtomFoundation.atomConfiguration_transport_comp C
        (Atom.assemble _ hp.atom.upper) (Atom.assemble _ hq.atom.upper))).to_iff.trans decide_eq_true_iff.symm)
  | atObjects A C z =>
    exact congrArg
      (fun h => NativeReader.liftDependent mode (assemble s).core.object (assemble r).core.object h A C z)
      (dependentIndices_eq_native s t r p hp q hq)
  | operation => rfl
  | signatureCoordinate => rfl

end IndependentGeometryHomPrimitive.Composition

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCarrierGraph
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
