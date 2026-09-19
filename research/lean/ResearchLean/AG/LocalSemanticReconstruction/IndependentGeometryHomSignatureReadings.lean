import ResearchLean.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInverseRows
import Formal.Util.AssertStandardAxioms

/-!
# Signature coordinate equivalences from common Hom point rows

The axis action is directed. Its true graph pair activates a coordinate
equivalence whose outer axis and inner coordinate carriers are both explicit
candidate references. All native coordinate families are recovered, and both
inverse readings include the inactive outer and inner candidate rows.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Signature

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- One common signature-axis graph pair, at explicitly supplied candidate axis carriers. -/
def axisPoints (h : Table.{u, v} U mode) (I J : Type u) (i : I) (j : J) : Bool :=
  h (.signatureAxis (.edge I J i j))

/-- Project the common signature-coordinate role without selecting either axis carrier. -/
def points (h : Table.{u, v} U mode) : IndependentCandidateIndexedInverseGraph.Table.{u, u, u, u}
  | .edge I J i j q => InverseRows.signatureCoordinate h I J i j q

variable (h : Table.{u, v} U mode) (I J : Type u)
variable (ha : IndependentCarrierGraph.IsLawful I J (signatureAxis h))
variable (S : I → Type u) (T : J → Type u)

/-- The native axis function is constructed from the directed common graph, without invertibility. -/
def axisMap : I → J := IndependentCarrierGraph.assemble I J (signatureAxis h) ha

/-- Native axis evaluation is exactly the true common graph point. -/
theorem axis_forward_iff (i : I) (j : J) :
    axisPoints h I J i j = true ↔ axisMap h I J ha i = j :=
  (IndependentCarrierGraph.graph I J (signatureAxis h) ha.2).edge_eq_true_iff_target_eq i j

/-- The coordinate laws normalize every candidate outer/inner row and construct inverse fiber maps. -/
abbrev IsLawful := IndependentCandidateIndexedInverseGraph.IsLawful I J (axisPoints h I J) S T (points h)

/-- Construct the coordinate equivalence at an arbitrary true axis pair from its point rows. -/
def atPair (hc : IsLawful h I J S T) (i : I) (j : J) (hp : axisPoints h I J i j = true) : S i ≃ T j :=
  IndependentInverseGraph.assemble (S i) (T j) (InverseRows.signatureCoordinate h I J i j)
    (hc.selected.active i j hp)

/-- The active forward coordinate point gives exactly its independently reconstructed fiber image. -/
theorem atPair_forward_iff (hc : IsLawful h I J S T) (i : I) (j : J)
    (hp : axisPoints h I J i j = true) (x : S i) (y : T j) :
    h (.signatureCoordinate .forward I J i j (.edge (S i) (T j) x y)) = true ↔
      atPair h I J S T hc i j hp x = y :=
  (IndependentCarrierGraph.graph (S i) (T j) _ (hc.selected.active i j hp).forward.2).edge_eq_true_iff_target_eq x y

/-- The backward coordinate point keeps common source/target order while recovering the inverse fiber image. -/
theorem atPair_backward_iff (hc : IsLawful h I J S T) (i : I) (j : J)
    (hp : axisPoints h I J i j = true) (x : S i) (y : T j) :
    h (.signatureCoordinate .backward I J i j (.edge (S i) (T j) x y)) = true ↔
      (atPair h I J S T hc i j hp).symm y = x :=
  (IndependentCarrierGraph.graph (T j) (S i) _ (hc.selected.active i j hp).backward.2).edge_eq_true_iff_target_eq y x

/-- Every native coordinate-equivalence family over the directed axis map has an exact candidate point presentation. -/
def readingEquiv : (∀ i, S i ≃ T (axisMap h I J ha i)) ≃
    {t : IndependentCandidateIndexedInverseGraph.Table.{u, u, u, u} //
      IndependentCandidateIndexedInverseGraph.IsLawful I J (axisPoints h I J) S T t} :=
  IndependentCandidateIndexedInverseGraph.readingEquiv I J (axisPoints h I J) S T ha.2

/-- Construct all native coordinate equivalences from the common signature rows. -/
def assemble (hc : IsLawful h I J S T) : ∀ i, S i ≃ T (axisMap h I J ha i) :=
  (readingEquiv h I J ha S T).symm ⟨points h, hc⟩

/-- Each native component is exactly the fiber equivalence at the axis graph's selected point. -/
theorem assemble_eq_atPair (hc : IsLawful h I J S T) (i : I) :
    assemble h I J ha S T hc i =
      atPair h I J S T hc i (axisMap h I J ha i) ((axis_forward_iff h I J ha i _).2 rfl) := rfl

/-- Reading after assembly restores every candidate axis and coordinate carrier row. -/
theorem read_assemble (hc : IsLawful h I J S T) :
    (readingEquiv h I J ha S T (assemble h I J ha S T hc)).val = points h :=
  congrArg Subtype.val ((readingEquiv h I J ha S T).apply_symm_apply ⟨points h, hc⟩)

/-- Every native coordinate family survives reading and assembly, including each inverse component. -/
theorem assemble_read (f : ∀ i, S i ≃ T (axisMap h I J ha i)) :
    (readingEquiv h I J ha S T).symm (readingEquiv h I J ha S T f) = f :=
  (readingEquiv h I J ha S T).symm_apply_apply f

/-- Complete signature-coordinate point rows separate all native coordinate families. -/
theorem read_injective : Function.Injective (fun f => (readingEquiv h I J ha S T f).val) := by
  intro f g he
  exact (readingEquiv h I J ha S T).injective (Subtype.ext he)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Signature

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Signature
