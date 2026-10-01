import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.GeneratedPublicRelations

/-!
# Constructed feasible strict public families for zero defect

## Implementation notes

Zero original corrections construct positive supported and strict objects for
every range. These are then mapped through the actual generated coordinates.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
namespace StrictCoverZeroCases
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)

variable (allowed : Set (EdgeName (K := K)))

/-- Zero defect has a strict family of supported original zero corrections for every allowed range. -/
def originalZero : StrictSupportedCover.Objects M P U candidates allowed 0 :=
  ⟨fun i => SupportedEquation.zeroObject M P (U i) candidates allowed,by intro i j e hi hj; rfl⟩

/-- Zero defect admits complete strict generated coordinates for every allowed range. -/
def generatedZero : GeneratedStrictCover.Objects M bases P U candidates hlinear 0 enumK enumEdges enumFaces allowed :=
  GeneratedStrictCover.coordinate M bases P U candidates hlinear 0 enumK enumEdges enumFaces allowed
    (originalZero M P U candidates allowed)

/-- The generated zero-defect case supplies a feasible public relation family, with no existential premise. -/
def publicZero : GeneratedPublicRelations.Objects M bases P U candidates hlinear 0 enumK enumEdges enumFaces allowed :=
  GeneratedPublicRelations.publicCoordinates M bases P U candidates hlinear 0 enumK enumEdges enumFaces allowed
    (generatedZero M bases P U candidates hlinear enumK enumEdges enumFaces allowed)

/-- Every original public coordinate of the constructed feasible zero-defect family is zero. -/
theorem public_zero_values (i : I) :
    ((publicZero M bases P U candidates hlinear enumK enumEdges enumFaces allowed).1 i).1 = 0 := by
  change ((GeneratedStrictCover.coordinate M bases P U candidates hlinear 0 enumK enumEdges enumFaces allowed
    (originalZero M P U candidates allowed)).1 i).1.1 = 0
  rw [GeneratedStrictCover.coordinate_public]
  change (FiniteNative.edgeSplit M bases (U i) P (ClosedRegion.privateAlwaysEdges U P candidates i) 0).2 = 0
  rw [map_zero]
  rfl

end StrictCoverZeroCases
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
