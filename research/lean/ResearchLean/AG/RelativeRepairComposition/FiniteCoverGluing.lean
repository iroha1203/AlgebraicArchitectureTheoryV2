import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteIndexedGluing

/-!
# Finite assembly of every original relative cell degree

## Implementation notes

All four maps use the same complete finite region list and the original-cell
cover conditions. The degreewise maps retain every original value. Their
comparison with general gluing lets the accepted differential laws apply to
the computed assembly without assuming that an extension is a chain map.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uG uA uI
namespace FiniteCoverGlue
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)

section Degree0
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]

/-- Compute the full original degree-0 family from all compatible local values. -/
def glue0 : IndexedCover.Compatible0 M P U →+ RelativeCover.C0 M ClosedRegion.all P :=
  FiniteFamilyGlue.glue (fun i => (U i).vertices) enumI hc.vertices M.A P.vertices

/-- Every restored degree-0 value equals the same original local value. -/
theorem glue0_value (b : IndexedCover.Compatible0 M P U) (i : I) (x : (U i).vertices) :
    (glue0 M P U enumI hc b).1 ⟨x.1,Set.mem_univ x.1⟩ = (b.1 i).1 x :=
  FiniteFamilyGlue.glue_value (fun i => (U i).vertices) enumI hc.vertices M.A P.vertices
    b i x.1 x.2

/-- Finite restoration returns the whole original degree-0 family after restriction. -/
theorem glue_restriction0 (b : RelativeCover.C0 M ClosedRegion.all P) :
    glue0 M P U enumI hc (IndexedCover.restriction0 M P U b) = b :=
  FiniteFamilyGlue.glue_restriction (fun i => (U i).vertices) enumI hc.vertices M.A P.vertices b

/-- Restriction after finite restoration returns every local degree-0 value. -/
theorem restrict_glue0 (b : IndexedCover.Compatible0 M P U) :
    IndexedCover.restriction0 M P U (glue0 M P U enumI hc b) = b :=
  FiniteFamilyGlue.restriction_glue (fun i => (U i).vertices) enumI hc.vertices M.A P.vertices b

/-- Computed degree-0 assembly is the same full original map as general gluing. -/
theorem glue0_eq_general (b : IndexedCover.Compatible0 M P U) :
    glue0 M P U enumI hc b = IndexedCover.glue0 M P U hc b :=
  FiniteFamilyGlue.glue_eq_general (fun i => (U i).vertices) enumI hc.vertices M.A P.vertices b

end Degree0

section Degree1
variable [∀ i, DecidablePred (· ∈ (U i).edges)]

/-- Compute the full original degree-1 family from all compatible local values. -/
def glue1 : IndexedCover.Compatible1 M P U →+ RelativeCover.C1 M ClosedRegion.all P :=
  FiniteFamilyGlue.glue (fun i => (U i).edges) enumI hc.edges (fun e : EdgeName (K := K) => M.A e.2.1) P.edges

/-- Every restored degree-1 value equals the same original local value. -/
theorem glue1_value (b : IndexedCover.Compatible1 M P U) (i : I) (x : (U i).edges) :
    (glue1 M P U enumI hc b).1 ⟨x.1,Set.mem_univ x.1⟩ = (b.1 i).1 x :=
  FiniteFamilyGlue.glue_value (fun i => (U i).edges) enumI hc.edges (fun e : EdgeName (K := K) => M.A e.2.1) P.edges
    b i x.1 x.2

/-- Finite restoration returns the whole original degree-1 family after restriction. -/
theorem glue_restriction1 (b : RelativeCover.C1 M ClosedRegion.all P) :
    glue1 M P U enumI hc (IndexedCover.restriction1 M P U b) = b :=
  FiniteFamilyGlue.glue_restriction (fun i => (U i).edges) enumI hc.edges (fun e : EdgeName (K := K) => M.A e.2.1) P.edges b

/-- Restriction after finite restoration returns every local degree-1 value. -/
theorem restrict_glue1 (b : IndexedCover.Compatible1 M P U) :
    IndexedCover.restriction1 M P U (glue1 M P U enumI hc b) = b :=
  FiniteFamilyGlue.restriction_glue (fun i => (U i).edges) enumI hc.edges (fun e : EdgeName (K := K) => M.A e.2.1) P.edges b

/-- Computed degree-1 assembly is the same full original map as general gluing. -/
theorem glue1_eq_general (b : IndexedCover.Compatible1 M P U) :
    glue1 M P U enumI hc b = IndexedCover.glue1 M P U hc b :=
  FiniteFamilyGlue.glue_eq_general (fun i => (U i).edges) enumI hc.edges (fun e : EdgeName (K := K) => M.A e.2.1) P.edges b

end Degree1

section Degree2
variable [∀ i, DecidablePred (· ∈ (U i).faces)]

/-- Compute the full original degree-2 family from all compatible local values. -/
def glue2 : IndexedCover.Compatible2 M P U →+ RelativeCover.C2 M ClosedRegion.all P :=
  FiniteFamilyGlue.glue (fun i => (U i).faces) enumI hc.faces (fun f => M.A (K.twoTarget f)) P.faces

/-- Every restored degree-2 value equals the same original local value. -/
theorem glue2_value (b : IndexedCover.Compatible2 M P U) (i : I) (x : (U i).faces) :
    (glue2 M P U enumI hc b).1 ⟨x.1,Set.mem_univ x.1⟩ = (b.1 i).1 x :=
  FiniteFamilyGlue.glue_value (fun i => (U i).faces) enumI hc.faces (fun f => M.A (K.twoTarget f)) P.faces
    b i x.1 x.2

/-- Finite restoration returns the whole original degree-2 family after restriction. -/
theorem glue_restriction2 (b : RelativeCover.C2 M ClosedRegion.all P) :
    glue2 M P U enumI hc (IndexedCover.restriction2 M P U b) = b :=
  FiniteFamilyGlue.glue_restriction (fun i => (U i).faces) enumI hc.faces (fun f => M.A (K.twoTarget f)) P.faces b

/-- Restriction after finite restoration returns every local degree-2 value. -/
theorem restrict_glue2 (b : IndexedCover.Compatible2 M P U) :
    IndexedCover.restriction2 M P U (glue2 M P U enumI hc b) = b :=
  FiniteFamilyGlue.restriction_glue (fun i => (U i).faces) enumI hc.faces (fun f => M.A (K.twoTarget f)) P.faces b

/-- Computed degree-2 assembly is the same full original map as general gluing. -/
theorem glue2_eq_general (b : IndexedCover.Compatible2 M P U) :
    glue2 M P U enumI hc b = IndexedCover.glue2 M P U hc b :=
  FiniteFamilyGlue.glue_eq_general (fun i => (U i).faces) enumI hc.faces (fun f => M.A (K.twoTarget f)) P.faces b

end Degree2

section Degree3
variable [∀ i, DecidablePred (· ∈ (U i).triples)]

/-- Compute the full original degree-3 family from all compatible local values. -/
def glue3 : IndexedCover.Compatible3 M P U →+ RelativeCover.C3 M ClosedRegion.all P :=
  FiniteFamilyGlue.glue (fun i => (U i).triples) enumI hc.triples (fun t => M.A (K.threeTarget t)) P.triples

/-- Every restored degree-3 value equals the same original local value. -/
theorem glue3_value (b : IndexedCover.Compatible3 M P U) (i : I) (x : (U i).triples) :
    (glue3 M P U enumI hc b).1 ⟨x.1,Set.mem_univ x.1⟩ = (b.1 i).1 x :=
  FiniteFamilyGlue.glue_value (fun i => (U i).triples) enumI hc.triples (fun t => M.A (K.threeTarget t)) P.triples
    b i x.1 x.2

/-- Finite restoration returns the whole original degree-3 family after restriction. -/
theorem glue_restriction3 (b : RelativeCover.C3 M ClosedRegion.all P) :
    glue3 M P U enumI hc (IndexedCover.restriction3 M P U b) = b :=
  FiniteFamilyGlue.glue_restriction (fun i => (U i).triples) enumI hc.triples (fun t => M.A (K.threeTarget t)) P.triples b

/-- Restriction after finite restoration returns every local degree-3 value. -/
theorem restrict_glue3 (b : IndexedCover.Compatible3 M P U) :
    IndexedCover.restriction3 M P U (glue3 M P U enumI hc b) = b :=
  FiniteFamilyGlue.restriction_glue (fun i => (U i).triples) enumI hc.triples (fun t => M.A (K.threeTarget t)) P.triples b

/-- Computed degree-3 assembly is the same full original map as general gluing. -/
theorem glue3_eq_general (b : IndexedCover.Compatible3 M P U) :
    glue3 M P U enumI hc b = IndexedCover.glue3 M P U hc b :=
  FiniteFamilyGlue.glue_eq_general (fun i => (U i).triples) enumI hc.triples (fun t => M.A (K.threeTarget t)) P.triples b

end Degree3

end FiniteCoverGlue
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
