import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomSignatureComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomObservableComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeReader
import Formal.Util.AssertStandardAxioms

/-!
# Common core-Hom point composition with mode-specific extension rows

The scalar/index, operation, signature, and observable compositions fill the
same closed common query declaration. Raw and realization rows are explicit
point callbacks for the later mode-specific constructions. This module proves
the complete table comparison for any such callbacks; it does not infer their
geometric laws. Native core composition appears only in the comparison proof.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)
variable (raw : RawQuery (assemble s).core.object (assemble r).core.object mode → Bool)
variable (realization : RealizationQuery (assemble s).core.object (assemble r).core.object mode → Bool)

/-- Fill active dependent roles with primitive observable composition and the specified mode-specific point rows. -/
def dependentWith : DependentQuery mode (assemble s).core.object (assemble r).core.object → Bool
  | .observable d W Z a => InverseRows.fromInverse (fun a => observableRows s t r p hp q hq (.edge W Z a)) d a
  | .raw a => raw a
  | .realization a => realization a
  | a => dependentIndices s t r p hp q hq a

/-- Directly composed dependent core rows equal the common native reader of core composition with the same extension points. -/
theorem dependentWith_eq_native (cp : GeometryComponents.CoefficientPoints s t p)
    (cq : GeometryComponents.CoefficientPoints t r q) : dependentWith s t r p hp q hq raw realization =
    NativeReader.dependentRead mode
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) raw realization := by
  funext a
  cases a with
  | equation d a => exact congrFun (dependentIndices_eq_native s t r p hp q hq) (.equation d a)
  | context d W Z => exact congrFun (dependentIndices_eq_native s t r p hp q hq) (.context d W Z)
  | observable d W Z a =>
    exact congrArg (fun h => InverseRows.fromInverse (fun a => h (.edge W Z a)) d a)
      (observableRows_eq_native s t r p hp q hq cp cq)
  | raw => rfl
  | realization => rfl

variable (cp : GeometryComponents.CoefficientPoints s t p)

/-- Fill the complete common declaration from the primitive core compositions and the mode-specific extension rows. -/
def composeWith : Table.{u, v} U mode
  | .operation A B A' B' a => operationRows s t r p hp q (.edge (A, B) (A', B') a)
  | .signatureCoordinate d I J i j a => InverseRows.fromInverse (fun a => signatureRows s t r p hp q hq (.edge I J i j a)) d a
  | .atObjects A B a => NativeReader.liftDependent mode (assemble s).core.object (assemble r).core.object
      (dependentWith s t r p hp q hq raw realization) A B a
  | a => indices s t r p hp q hq cp a

/-- Every common point in direct core composition agrees with the original native core and coefficient composite reader. -/
theorem composeWith_eq_native (cq : GeometryComponents.CoefficientPoints t r q) : composeWith s t r p hp q hq raw realization cp =
    NativeReader.readWith mode
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) raw realization := by
  have hi := indices_eq_native s t r p hp q hq cp cq
  funext a
  cases a with
  | source a => exact congrFun hi (.source a)
  | pointedAtom d x y => exact congrFun hi (.pointedAtom d x y)
  | atom d x y => exact congrFun hi (.atom d x y)
  | object A B => exact congrFun hi (.object A B)
  | invariant a => exact congrFun hi (.invariant a)
  | signatureAxis a => exact congrFun hi (.signatureAxis a)
  | coefficient a => exact congrFun hi (.coefficient a)
  | familyTransport F F' => exact congrFun hi (.familyTransport F F')
  | configurationTransport C C' => exact congrFun hi (.configurationTransport C C')
  | operation A B A' B' a => exact congrFun (operationRows_eq_native s t r p hp q hq cp cq) (.edge (A, B) (A', B') a)
  | signatureCoordinate d I J i j a =>
    exact congrArg (fun h => InverseRows.fromInverse (fun a => h (.edge I J i j a)) d a)
      (signatureRows_eq_native s t r p hp q hq cp cq)
  | atObjects A B a =>
    exact congrArg (fun h => NativeReader.liftDependent mode (assemble s).core.object (assemble r).core.object h A B a)
      (dependentWith_eq_native s t r p hp q hq raw realization cp cq)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
