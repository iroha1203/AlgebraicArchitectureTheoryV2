import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.GeneratedStrictCover

/-!
# Public feasibility and all retained private freedoms

## Implementation notes

The public relation uses the same precomputed private differential and section.
A public family determines all strict objects by freely choosing every kernel
vector; no allowed range changes the local generator.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
namespace GeneratedPublicRelations
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
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)

local notation "private" i => ClosedRegion.privateAlwaysEdges U P candidates i
local notation "N" i => LinearMap.ker (FiniteNative.D M bases (U i) P (private i) hlinear)

/-- Each public value belongs to the same generated cokernel relation. -/
abbrev LocalRelation (i : I) := ↥(LinearInterface.Relation
  (FiniteNative.D M bases (U i) P (private i) hlinear)
  (FiniteNative.F M bases (U i) P (private i) hlinear)
  (FiniteNative.generatedSection M bases (U i) P (private i) hlinear enumK enumEdges enumFaces)
  (FiniteNative.rhs M bases (U i) P δ))

variable (allowed : Set (EdgeName (K := K)))

/-- A feasible public family has only the original relation, support and shared-edge conditions. -/
def Objects := {z : ∀ i,LocalRelation M bases P U candidates hlinear δ enumK enumEdges enumFaces i //
  (∀ i (e : (U i).edges), e.1 ∈ candidates \ allowed →
    GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 e = 0) ∧
  (∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges), j ≠ i →
    GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 ⟨e,hi⟩ =
      GeneratedStrictCover.publicValue M bases P U candidates j (z j).1 ⟨e,hj⟩)}

local notation "Public" => Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
local notation "Whole" => GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed

/-- Retain precisely the public relation values of every complete generated object. -/
def publicCoordinates (y : Whole) : Public := ⟨fun i => (y.1 i).1,y.2⟩

/-- Any private kernel vector at every region gives a complete object over the same public family. -/
def assemble (z : Public) (n : ∀ i,N i) : Whole := ⟨fun i => (z.1 i,n i),z.2⟩

/-- The full strict object space is all feasible public families times all private kernels. -/
def publicKernelEquiv : Whole ≃ (Public × (∀ i,N i)) where
  toFun y := (publicCoordinates M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y,
    fun i => (y.1 i).2)
  invFun zn := assemble M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed zn.1 zn.2
  left_inv y := Subtype.ext (by funext i; exact Prod.eta (y.1 i))
  right_inv zn := by apply Prod.ext <;> rfl

/-- Existence requires only public conditions; every private kernel admits zero. -/
theorem nonempty_iff_public : Nonempty Whole ↔ Nonempty Public := by
  constructor
  · rintro ⟨y⟩
    exact ⟨publicCoordinates M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y⟩
  · rintro ⟨z⟩
    exact ⟨assemble M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed z (fun _ => 0)⟩

omit [∀ i, DecidablePred (· ∈ (U i).vertices)] in
/-- A nonzero forbidden original candidate value excludes a feasible public family. -/
theorem not_supported_of_ne (z : ∀ i,LocalRelation M bases P U candidates hlinear δ enumK enumEdges enumFaces i)
    (i : I) (e : (U i).edges) (he : e.1 ∈ candidates \ allowed)
    (hne : GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 e ≠ 0) :
    ¬ ((∀ i (e : (U i).edges), e.1 ∈ candidates \ allowed →
      GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 e = 0) ∧
      (∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges), j ≠ i →
        GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 ⟨e,hi⟩ =
          GeneratedStrictCover.publicValue M bases P U candidates j (z j).1 ⟨e,hj⟩)) :=
  fun hz => hne (hz.1 i e he)

omit [∀ i, DecidablePred (· ∈ (U i).vertices)] in
/-- Unequal full original shared values exclude a feasible public family. -/
theorem not_shared_of_ne (z : ∀ i,LocalRelation M bases P U candidates hlinear δ enumK enumEdges enumFaces i)
    (i j : I) (e : EdgeName (K := K)) (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges) (hij : j ≠ i)
    (hne : GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 ⟨e,hi⟩ ≠
      GeneratedStrictCover.publicValue M bases P U candidates j (z j).1 ⟨e,hj⟩) :
    ¬ ((∀ i (e : (U i).edges), e.1 ∈ candidates \ allowed →
      GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 e = 0) ∧
      (∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges), j ≠ i →
        GeneratedStrictCover.publicValue M bases P U candidates i (z i).1 ⟨e,hi⟩ =
          GeneratedStrictCover.publicValue M bases P U candidates j (z j).1 ⟨e,hj⟩)) :=
  fun hz => hne (hz.2 i j e hi hj hij)

end GeneratedPublicRelations
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
