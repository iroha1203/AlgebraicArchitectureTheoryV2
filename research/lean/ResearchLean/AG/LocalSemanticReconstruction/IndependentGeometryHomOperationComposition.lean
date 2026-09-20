import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCompositionIndices
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeFamilies
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomReadingCongruence
import Formal.Util.AssertStandardAxioms

/-!
# Direct operation composition over the common object rows

Implementation notes: the first primitive object points choose the middle
endpoint pair, and the first operation row chooses its middle value. The
second operation row is queried there. The heterogeneous equalities below
remove only the proved endpoint casts; native composition is the comparison
target, not the definition of the output table.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

namespace Operation

variable {U : AtomCarrier.{u}} {mode : Mode}
variable (h : Table.{u, v} U mode) (ho : CoreLaws.ObjectRows h)
variable (S M T : ArchitectureObject U → ArchitectureObject U → Type u)

/-- Operation assembly's endpoint cast preserves the value assembled from the primitive indexed row. -/
theorem assemble_value_heq (hh : IsLawful h S M) (A B : ArchitectureObject U) (x : S A B) :
    HEq (assemble h ho S M hh A B x)
      (IndependentIndexedCarrierGraph.assemble (endpoints h) (endpoints_total h ho)
        (Fiber S) (Fiber M) (points h) hh (A, B) x) := cast_heq _ _

/-- Reindexing a native operation family retains its values at the same ordered source pair. -/
theorem toIndexed_heq (f : ∀ A B, S A B → M (CoreLaws.objectMap h ho A) (CoreLaws.objectMap h ho B)) :
    HEq ((nativeFamilyEquiv h ho S M).symm f) (fun i : ArchitectureObject U × ArchitectureObject U => f i.1 i.2) := by
  apply Function.hfunext rfl
  intro i j hij
  cases hij
  apply Function.hfunext rfl
  intro x y hxy
  cases hxy
  exact cast_heq _ _

variable (hh : IsLawful h S M) (k : Table.{u, v} U mode) (ko : CoreLaws.ObjectRows k) (hk : IsLawful k M T)

/-- The two primitive indexed operation functions compose to the original native operation functions. -/
theorem indexed_comp_heq : HEq
    (fun i x => IndependentIndexedCarrierGraph.assemble (endpoints k) (endpoints_total k ko)
      (Fiber M) (Fiber T) (points k) hk
      (IndependentIndexedCarrierGraph.index (endpoints h) (endpoints_total h ho) i)
      (IndependentIndexedCarrierGraph.assemble (endpoints h) (endpoints_total h ho)
        (Fiber S) (Fiber M) (points h) hh i x))
    (fun i : ArchitectureObject U × ArchitectureObject U => fun x : S i.1 i.2 =>
      assemble k ko M T hk (CoreLaws.objectMap h ho i.1) (CoreLaws.objectMap h ho i.2)
        (assemble h ho S M hh i.1 i.2 x)) := by
  apply Function.hfunext rfl
  intro i j hij
  cases hij
  apply Function.hfunext rfl
  intro x y hxy
  cases hxy
  have he : (⟨IndependentIndexedCarrierGraph.index (endpoints h) (endpoints_total h ho) i,
      IndependentIndexedCarrierGraph.assemble (endpoints h) (endpoints_total h ho)
        (Fiber S) (Fiber M) (points h) hh i x⟩ :
        Σ j : ArchitectureObject U × ArchitectureObject U, Fiber M j) =
      ⟨(CoreLaws.objectMap h ho i.1, CoreLaws.objectMap h ho i.2), assemble h ho S M hh i.1 i.2 x⟩ :=
    Sigma.ext (index_eq h ho i) (assemble_value_heq h ho S M hh i.1 i.2 x).symm
  have hv := congrArg (fun d : Σ j : ArchitectureObject U × ArchitectureObject U, Fiber M j =>
      (⟨(CoreLaws.objectMap k ko d.1.1, CoreLaws.objectMap k ko d.1.2),
        assemble k ko M T hk d.1.1 d.1.2 d.2⟩ : Σ j : ArchitectureObject U × ArchitectureObject U, Fiber T j)) he
  exact (assemble_value_heq k ko M T hk _ _ _).symm.trans (Sigma.mk.inj hv).2

end Operation

namespace NativeReader

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)

/-- The indexed family used by the common native reader preserves every original operation value. -/
theorem operationIndexedFamily_heq : HEq
    ((Operation.nativeFamilyEquiv (indices mode f a) (object_rows mode f a)
      G.core.reading.operationReading.Op H.core.reading.operationReading.Op).symm (operationFamily mode f a))
    (fun i : ArchitectureObject U × ArchitectureObject U => f.upper.operationMap (A := i.1) (B := i.2)) := by
  refine (Operation.toIndexed_heq (indices mode f a) (object_rows mode f a)
    G.core.reading.operationReading.Op H.core.reading.operationReading.Op (operationFamily mode f a)).trans ?_
  apply Function.hfunext rfl
  intro i j hij
  cases hij
  apply Function.hfunext rfl
  intro x y hxy
  cases hxy
  have hs : (⟨CoreLaws.objectMap (indices mode f a) (object_rows mode f a), operationFamily mode f a⟩ :
      Σ F : ArchitectureObject U → ArchitectureObject U,
        ∀ A B, G.core.reading.operationReading.Op A B → H.core.reading.operationReading.Op (F A) (F B)) =
      ⟨f.upper.objectMap, fun A B => f.upper.operationMap (A := A) (B := B)⟩ :=
    Sigma.ext (objectMap_indices mode f a) (operationFamily_heq mode f a)
  have hv := congrArg (fun d : Σ F : ArchitectureObject U → ArchitectureObject U,
      ∀ A B, G.core.reading.operationReading.Op A B → H.core.reading.operationReading.Op (F A) (F B) =>
    (⟨d.1, d.2 i.1 i.2 x⟩ : Σ F : ArchitectureObject U → ArchitectureObject U,
      H.core.reading.operationReading.Op (F i.1) (F i.2))) hs
  exact (Sigma.mk.inj hv).2

end NativeReader

namespace Composition

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)

/-- Compose common operation points using only the first primitive endpoint/value and the second point table. -/
def operationRows : IndependentIndexedCarrierGraph.Table.{u + 1, u + 1, u, u}
    (ArchitectureObject U × ArchitectureObject U) (ArchitectureObject U × ArchitectureObject U) :=
  IndependentIndexedCarrierGraph.composeRows (Operation.endpoints (PackageAssembly.retained s.1 t.1 p).table)
    (Operation.endpoints_total _ (PackageAssembly.retained s.1 t.1 p).objectRows)
    (Operation.Fiber (assemble s).core.reading.operationReading.Op)
    (Operation.Fiber (assemble t).core.reading.operationReading.Op)
    (Operation.Fiber (assemble r).core.reading.operationReading.Op)
    (Operation.points (PackageAssembly.retained s.1 t.1 p).table) hp.operationRows
    (Operation.points (PackageAssembly.retained t.1 r.1 q).table)

/-- Composition of operation endpoint graphs is the endpoint graph of the directly composed common indices. -/
theorem operation_endpoints (cp : GeometryComponents.CoefficientPoints s t p) :
    IndependentIndexedCarrierGraph.composeIndex (Operation.endpoints (PackageAssembly.retained s.1 t.1 p).table)
      (Operation.endpoints_total _ (PackageAssembly.retained s.1 t.1 p).objectRows)
      (Operation.endpoints (PackageAssembly.retained t.1 r.1 q).table) =
      Operation.endpoints (indices s t r p hp q hq cp) := by
  funext i j
  change Operation.endpoints (PackageAssembly.retained t.1 r.1 q).table
    (IndependentIndexedCarrierGraph.index (Operation.endpoints (PackageAssembly.retained s.1 t.1 p).table)
      (Operation.endpoints_total _ (PackageAssembly.retained s.1 t.1 p).objectRows) i) j = _
  rw [Operation.index_eq]
  rfl

/-- Direct operation point composition recovers the complete common reading of native operation composition. -/
theorem operationRows_eq_native (cp : GeometryComponents.CoefficientPoints s t p)
    (cq : GeometryComponents.CoefficientPoints t r q) : operationRows s t r p hp q =
    NativeReader.operationRows mode
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) := by
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let k := (PackageAssembly.retained t.1 r.1 q).table
  let ho := (PackageAssembly.retained s.1 t.1 p).objectRows
  let ko := (PackageAssembly.retained t.1 r.1 q).objectRows
  let f := PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq)
  let a := (GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)
  let S := Operation.Fiber (assemble s).core.reading.operationReading.Op
  let M := Operation.Fiber (assemble t).core.reading.operationReading.Op
  let T := Operation.Fiber (assemble r).core.reading.operationReading.Op
  let ci := IndependentIndexedCarrierGraph.composeIndex (Operation.endpoints h) (Operation.endpoints_total h ho) (Operation.endpoints k)
  let hi := IndependentIndexedCarrierGraph.composeIndex_total (Operation.endpoints h) (Operation.endpoints_total h ho)
    (Operation.endpoints k) (Operation.endpoints_total k ko)
  let hc := IndependentIndexedCarrierGraph.composeRows_isLawful (Operation.endpoints h) (Operation.endpoints_total h ho)
    S M T (Operation.points h) hp.operationRows (Operation.points k) (Operation.endpoints k) hq.operationRows
  have he : ci = Operation.endpoints (NativeReader.indices mode f a) :=
    (operation_endpoints s t r p hp q hq cp).trans (congrArg Operation.endpoints (indices_eq_native s t r p hp q hq cp cq))
  refine (IndependentIndexedCarrierGraph.read_assemble ci hi S T (operationRows s t r p hp q) hc).symm.trans ?_
  apply ReadingCongruence.indexed_function ci (Operation.endpoints (NativeReader.indices mode f a)) hi
    (Operation.endpoints_total _ (NativeReader.object_rows mode f a)) he S T
  exact (IndependentIndexedCarrierGraph.assemble_composeRows_heq (Operation.endpoints h) (Operation.endpoints_total h ho)
    S M T (Operation.points h) hp.operationRows (Operation.points k) (Operation.endpoints k)
    (Operation.endpoints_total k ko) hq.operationRows).trans
      ((Operation.indexed_comp_heq h ho (assemble s).core.reading.operationReading.Op
        (assemble t).core.reading.operationReading.Op (assemble r).core.reading.operationReading.Op hp.operationRows k ko hq.operationRows).trans
        (NativeReader.operationIndexedFamily_heq mode f a).symm)

end Composition

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Operation
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
