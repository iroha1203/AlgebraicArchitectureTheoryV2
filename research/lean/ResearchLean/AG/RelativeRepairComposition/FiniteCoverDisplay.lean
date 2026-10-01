import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverRanges

/-!
# Input data of a full finite cover display

## Implementation notes

Only the original closed cover, complete finite enumerations and full input
bases are stored. Coordinates, reconstruction, gauges and their laws are
constructed by the accepted generator and strict gluing. No repair or
comparison certificate is a field of this input structure.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]

/-- Complete finite input data for one display of the same original geometry and kernels. -/
structure FiniteCoverDisplay where
  Index : Type uI
  indexFintype : Fintype Index
  indexDecidable : DecidableEq Index
  region : Index → ClosedRegion K
  vertexDecidable : ∀ i, DecidablePred (· ∈ (region i).vertices)
  edgeDecidable : ∀ i, DecidablePred (· ∈ (region i).edges)
  faceDecidable : ∀ i, DecidablePred (· ∈ (region i).faces)
  cover : ClosedRegion.IndexedCover region
  bases : FiniteFamily.Bases (k := k) M.A
  enumField : FiniteElimination.Enumeration k
  enumEdges : FiniteElimination.Enumeration (EdgeName (K := K))
  enumFaces : FiniteElimination.Enumeration K.TwoCell
  enumIndex : FiniteElimination.Enumeration Index

namespace FiniteCoverDisplay
variable (d : FiniteCoverDisplay (k := k) M)

/-- The display uses the finite original cover-index input. -/
instance indexFinite : Fintype d.Index := d.indexFintype
/-- Equality of display indices uses its explicit input decision. -/
instance indexEquality : DecidableEq d.Index := d.indexDecidable
/-- Original vertex membership in each closed region uses the input decision. -/
instance regionVertexDecision : ∀ i, DecidablePred (· ∈ (d.region i).vertices) := d.vertexDecidable
/-- Original named-edge membership uses the input decision. -/
instance regionEdgeDecision : ∀ i, DecidablePred (· ∈ (d.region i).edges) := d.edgeDecidable
/-- Original face membership uses the input decision. -/
instance regionFaceDecision : ∀ i, DecidablePred (· ∈ (d.region i).faces) := d.faceDecidable

variable [Fintype k] [DecidableEq k]
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P) (allowed : Set (EdgeName (K := K)))

/-- Full generated coordinates use the same one-time local elimination at each original region. -/
abbrev Objects := GeneratedStrictCover.Objects M d.bases P d.region candidates hlinear δ
  d.enumField d.enumEdges d.enumFaces allowed
/-- Full labels retain every original permitted vertex value and strict overlap equality. -/
abbrev Labels := StrictSupportedCover.Labels M P d.region candidates allowed
/-- The display groupoid has all generated objects and all full original compatible labels. -/
abbrev Groupoid := GeneratedCoverAction.Groupoid M d.bases P d.region candidates hlinear δ
  d.enumField d.enumEdges d.enumFaces allowed

end FiniteCoverDisplay
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
