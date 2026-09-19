import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRingCarrierGraphs
import Formal.Util.AssertStandardAxioms

/-!
# Directed coefficient maps from the common Hom table

The coefficient carriers and operations come from primitive object responses.
Only zero, one, addition, and multiplication point rules are imposed on the
directed common graph. No inverse coefficient map or completed ring hom is a
local field. The resulting ring hom reads back to every candidate graph point.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Coefficient

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

open IndependentRingPrimitive

variable (s t : Carrier.Table.{v}) (hs : Carrier.IsTyped s) (ht : Carrier.IsTyped t)

/-- Coefficient laws use the original primitive operation responses at the selected carriers. -/
def PointLaws (h : Table.{u, v} U mode) : Prop :=
  IndependentCarrierGraph.IsLawful (Carrier.carrier s) (Carrier.carrier t) (coefficient h) ∧
    IndependentRingCarrierGraph.Preserves (Carrier.active s hs) (Carrier.active t ht) (coefficient h)

variable (hls : Carrier.IsLawful s hs) (hlt : Carrier.IsLawful t ht)

/-- Assemble the original directed ring hom from common coefficient points. -/
def assemble (h : Table.{u, v} U mode) (hh : PointLaws s t hs ht h) :
    letI : CommRing (Carrier.carrier s) := IndependentRingPrimitive.assemble (Carrier.active s hs) hls
    letI : CommRing (Carrier.carrier t) := IndependentRingPrimitive.assemble (Carrier.active t ht) hlt
    Carrier.carrier s →+* Carrier.carrier t := by
  letI : CommRing (Carrier.carrier s) := IndependentRingPrimitive.assemble (Carrier.active s hs) hls
  letI : CommRing (Carrier.carrier t) := IndependentRingPrimitive.assemble (Carrier.active t ht) hlt
  exact Hom.assemble _ (IndependentRingCarrierGraph.function_laws _ _ hls hlt _ hh.1 hh.2)

/-- The assembled coefficient map has exactly the original primitive graph in every candidate carrier. -/
theorem read_assemble (h : Table.{u, v} U mode) (hh : PointLaws s t hs ht h) :
    IndependentCarrierGraph.read _ _ (assemble s t hs ht hls hlt h hh) = coefficient h :=
  IndependentCarrierGraph.read_assemble _ _ _ hh.1

/-- A true coefficient point is exactly the image under the reconstructed directed map. -/
theorem point_iff (h : Table.{u, v} U mode) (hh : PointLaws s t hs ht h)
    (x : Carrier.carrier s) (y : Carrier.carrier t) :
    h (.coefficient (.edge _ _ x y)) = true ↔ assemble s t hs ht hls hlt h hh x = y :=
  (IndependentCarrierGraph.graph _ _ _ hh.1.2).edge_eq_true_iff_target_eq x y

/-- Any native map between the assembled rings satisfies the original primitive operation point rules. -/
theorem preserves_of_native
    (f : letI : CommRing (Carrier.carrier s) := IndependentRingPrimitive.assemble (Carrier.active s hs) hls
      letI : CommRing (Carrier.carrier t) := IndependentRingPrimitive.assemble (Carrier.active t ht) hlt
      Carrier.carrier s →+* Carrier.carrier t) :
    IndependentRingCarrierGraph.Preserves (Carrier.active s hs) (Carrier.active t ht)
      (IndependentCarrierGraph.read _ _ f) := by
  letI : CommRing (Carrier.carrier s) := IndependentRingPrimitive.assemble (Carrier.active s hs) hls
  letI : CommRing (Carrier.carrier t) := IndependentRingPrimitive.assemble (Carrier.active t ht) hlt
  have hp := (IndependentRingCarrierGraph.read_isLawful f).2
  simpa only [Carrier.assemble, IndependentRingPrimitive.read_assemble] using hp

/-- Whole-table coefficient equality with a native directed reading supplies all coefficient laws. -/
theorem pointLaws_of_native (h : Table.{u, v} U mode)
    (f : letI : CommRing (Carrier.carrier s) := IndependentRingPrimitive.assemble (Carrier.active s hs) hls
      letI : CommRing (Carrier.carrier t) := IndependentRingPrimitive.assemble (Carrier.active t ht) hlt
      Carrier.carrier s →+* Carrier.carrier t)
    (hf : coefficient h = IndependentCarrierGraph.read _ _ f) : PointLaws s t hs ht h := by
  rw [PointLaws, hf]
  exact ⟨IndependentCarrierGraph.read_isLawful _ _ f, preserves_of_native s t hs ht hls hlt f⟩

/-- Assembly restores every native coefficient map, with no injectivity or surjectivity assumption. -/
theorem assemble_eq_native (h : Table.{u, v} U mode)
    (f : letI : CommRing (Carrier.carrier s) := IndependentRingPrimitive.assemble (Carrier.active s hs) hls
      letI : CommRing (Carrier.carrier t) := IndependentRingPrimitive.assemble (Carrier.active t ht) hlt
      Carrier.carrier s →+* Carrier.carrier t)
    (hf : coefficient h = IndependentCarrierGraph.read _ _ f) :
    assemble s t hs ht hls hlt h (pointLaws_of_native s t hs ht hls hlt h f hf) = f := by
  letI : CommRing (Carrier.carrier s) := IndependentRingPrimitive.assemble (Carrier.active s hs) hls
  letI : CommRing (Carrier.carrier t) := IndependentRingPrimitive.assemble (Carrier.active t ht) hlt
  apply RingHom.ext
  intro x
  apply (point_iff s t hs ht hls hlt h _ x (f x)).1
  change coefficient h (.edge _ _ x (f x)) = true
  rw [hf]
  exact (IndependentCarrierGraph.read_edge _ _ f x (f x)).2 rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Coefficient

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Coefficient
