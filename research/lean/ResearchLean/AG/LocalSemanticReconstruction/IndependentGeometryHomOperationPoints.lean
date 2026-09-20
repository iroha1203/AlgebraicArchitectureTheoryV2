import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationReadings
import Formal.Util.AssertStandardAxioms

/-!
# Native operation-family evaluation at true common endpoint pairs

These point APIs connect the earlier directed operation-family equivalence to
the primitive action squares used for operation naturality. A true pair of
object graph points activates the row. Transport along equality of endpoint
pairs only changes the dependent target type and does not select a new map.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Operation.Point

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}
variable (h : Table.{u, v} U mode)
variable (S T : ArchitectureObject U → ArchitectureObject U → Type u)
variable (hl : Operation.IsLawful h S T)

/-- Construct the operation map directly at any true ordered endpoint pair. -/
def atPair (p q : ArchitectureObject U × ArchitectureObject U)
    (hp : Operation.endpoints h p q = true) : Operation.Fiber S p → Operation.Fiber T q :=
  IndependentCarrierGraph.assemble _ _
    (IndependentIndexedCarrierGraph.row (Operation.points h) p q) (hl.active p q hp)

/-- A common operation point is true exactly when the active row maps its input to its output. -/
theorem forward_iff (p q : ArchitectureObject U × ArchitectureObject U)
    (hp : Operation.endpoints h p q = true) (x : Operation.Fiber S p) (y : Operation.Fiber T q) :
    h (.operation p.1 p.2 q.1 q.2 (.edge (Operation.Fiber S p) (Operation.Fiber T q) x y)) = true ↔
      atPair h S T hl p q hp x = y :=
  (IndependentCarrierGraph.graph _ _ _ (hl.active p q hp).2).edge_eq_true_iff_target_eq x y

/-- Equal target endpoint pairs transport only the dependent operation value type. -/
theorem atPair_cast (p q q' : ArchitectureObject U × ArchitectureObject U) (he : q = q')
    (hp : Operation.endpoints h p q = true) (hp' : Operation.endpoints h p q' = true)
    (x : Operation.Fiber S p) :
    cast (congrArg (Operation.Fiber T) he) (atPair h S T hl p q hp x) =
      atPair h S T hl p q' hp' x := by
  cases he
  rfl

variable (ho : CoreLaws.ObjectRows h)

/-- The two actual object images give a true common operation-endpoint row. -/
theorem endpoints_point (A B : ArchitectureObject U) :
    Operation.endpoints h (A, B) (CoreLaws.objectMap h ho A, CoreLaws.objectMap h ho B) = true := by
  have hp := (IndependentIndexedCarrierGraph.active_iff (Operation.endpoints h)
    (Operation.endpoints_total h ho) (A, B) _).2 (Operation.index_eq h ho (A, B)).symm
  exact hp

/-- Every assembled native operation value is the value at its true common endpoint row. -/
theorem assemble_eq_atPair (A B : ArchitectureObject U) (x : S A B) :
    Operation.assemble h ho S T hl A B x =
      atPair h S T hl (A, B) (CoreLaws.objectMap h ho A, CoreLaws.objectMap h ho B)
        (endpoints_point h ho A B) x := by
  change cast (congrArg (Operation.Fiber T) (Operation.index_eq h ho (A, B)))
      (atPair h S T hl (A, B)
        (IndependentIndexedCarrierGraph.index (Operation.endpoints h) (Operation.endpoints_total h ho) (A, B))
        ((IndependentIndexedCarrierGraph.active_iff (Operation.endpoints h)
          (Operation.endpoints_total h ho) (A, B) _).2 rfl) x) = _
  exact atPair_cast h S T hl (A, B) _ _ (Operation.index_eq h ho (A, B)) _ _ x

/-- The native operation family's value has its original common forward point. -/
theorem assemble_point (A B : ArchitectureObject U) (x : S A B) :
    h (.operation A B (CoreLaws.objectMap h ho A) (CoreLaws.objectMap h ho B)
      (.edge (S A B) (T (CoreLaws.objectMap h ho A) (CoreLaws.objectMap h ho B))
        x (Operation.assemble h ho S T hl A B x))) = true := by
  apply (forward_iff h S T hl (A, B) _ (endpoints_point h ho A B) x _).2
  exact (assemble_eq_atPair h S T hl ho A B x).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Operation.Point

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Operation.Point
