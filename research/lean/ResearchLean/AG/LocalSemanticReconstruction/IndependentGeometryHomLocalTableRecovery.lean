import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalFamilyRecovery
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeReader
import Formal.Util.AssertStandardAxioms

/-!
# Recovery of every common Hom query after assembly

Core and coefficient inverse laws recover all their candidate rows. This
comparison theorem takes raw and realization readback as its remaining
premises; the complete Hom specializations discharge them with their actual
assemblers. Inactive object rows are used explicitly in the full table proof.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} (s t : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (hc : GeometryComponents.CoefficientPoints s t p)
variable (raw : RawQuery (assemble s).core.object (assemble t).core.object mode → Bool)
variable (realization : RealizationQuery (assemble s).core.object (assemble t).core.object mode → Bool)

/-- Every common query is restored when the actual raw and realization readings restore their original projections. -/
theorem readWith_assemble
    (hi : ∀ A B (q : DependentQuery mode A B),
      (A ≠ (assemble s).core.object ∨ B ≠ (assemble t).core.object) →
        (PackageAssembly.retained s.1 t.1 p).table (.atObjects A B q) = false)
    (hr : ∀ q, raw q = (PackageAssembly.retained s.1 t.1 p).table (.atObjects _ _ (.raw q)))
    (hz : ∀ q, realization q = (PackageAssembly.retained s.1 t.1 p).table (.atObjects _ _ (.realization q))) :
    readWith mode (GeometryComponents.base s t p hp) (GeometryComponents.coefficientMap s t p hc) raw realization =
      (PackageAssembly.retained s.1 t.1 p).table := by
  classical
  let f := GeometryComponents.base s t p hp
  let a := GeometryComponents.coefficientMap s t p hc
  let h := (PackageAssembly.retained s.1 t.1 p).table
  funext q
  cases q with
  | source q => exact congrFun (indices_assemble_source s t p hp a) q
  | pointedAtom d x y => exact congrArg (fun r => r d x y) (indices_assemble_pointed s t p hp a)
  | atom d x y => exact congrArg (fun r => r d x y) (indices_assemble_atom s t p hp a)
  | object A B => exact indices_assemble_object s t p hp a A B
  | invariant q => exact congrFun (indices_assemble_invariant s t p hp a) q
  | operation A B A' B' q => exact congrFun (operationRows_assemble s t p hp a) (.edge (A, B) (A', B') q)
  | signatureAxis q => exact congrFun (indices_assemble_axis s t p hp a) q
  | signatureCoordinate d I J i j q =>
    have he := congrArg (fun r => fun q => r (.edge I J i j q)) (signatureRows_assemble s t p hp a)
    exact (congrArg (fun r => InverseRows.fromInverse r d q) he).trans
      (congrArg (fun r => r d q) (InverseRows.fromInverse_asInverse
        (fun d q => h (.signatureCoordinate d I J i j q))))
  | coefficient q => exact congrFun (GeometryComponents.read_coefficient s t p hc) q
  | familyTransport F F' => exact indices_assemble_family s t p hp a F F'
  | configurationTransport C C' => exact indices_assemble_configuration s t p hp a C C'
  | atObjects A B q =>
    by_cases hA : A = (assemble s).core.object
    · subst A
      by_cases hB : B = (assemble t).core.object
      · subst B
        apply (readWith_dependent mode f a raw realization q).trans
        cases q with
        | equation d q =>
          exact (congrArg (fun r => InverseRows.fromInverse r d q) (PackageAssembly.read_equation s.1 t.1 p hp)).trans
            (congrArg (fun r => r d q) (InverseRows.fromInverse_asInverse
              (fun d q => h (.atObjects _ _ (.equation d q)))))
        | context d W V => exact congrArg (fun r => r d W V) (PackageAssembly.read_context s.1 t.1 p hp)
        | observable d W V q =>
          have he := congrArg (fun r => fun q => r (.edge W V q)) (observableRows_assemble s t p hp a)
          exact (congrArg (fun r => InverseRows.fromInverse r d q) he).trans
            (congrArg (fun r => r d q) (InverseRows.fromInverse_asInverse
              (fun d q => h (.atObjects _ _ (.observable d W V q)))))
        | raw q => exact hr q
        | realization q => exact hz q
      · exact (readWith_inactive mode f a raw realization _ B q (Or.inr hB)).trans
          (hi _ B q (Or.inr hB)).symm
    · exact (readWith_inactive mode f a raw realization A B q (Or.inl hA)).trans
        (hi A B q (Or.inl hA)).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
