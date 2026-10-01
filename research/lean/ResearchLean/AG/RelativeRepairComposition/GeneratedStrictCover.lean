import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.StrictCoverRestoration
import ResearchLean.AG.RelativeRepairComposition.FiniteCoverInterfaces

/-!
# Strict public conditions on the same generated local interfaces

## Implementation notes

Each local object is the generated relation times the full private kernel.
Support and shared-edge conditions read only the public coordinate; they do
not depend on a section or on a private kernel value.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
namespace GeneratedStrictCover
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
local notation "E" i => FiniteNative.generatedSolutionEquiv M bases (U i) P (private i)
  hlinear δ enumK enumEdges enumFaces

/-- The full generated local relation and private kernel, before imposing any range. -/
abbrev LocalObject (i : I) :=
  FiniteNative.GeneratedObjects M bases (U i) P (private i) hlinear δ enumK enumEdges enumFaces

/-- Read full original edge values from the public coordinates alone. -/
def publicValue (i : I)
    (z : FiniteNative.ZIndex M bases (U i) P (private i) → k) (e : (U i).edges) : M.A e.1.2.1 :=
  ((FiniteNative.edgeSplit M bases (U i) P (private i)).symm (0,z)).1 e

/-- The inverse retains exactly the public component of the generated relation. -/
theorem restored_public (i : I) (y : LocalObject M bases P U candidates hlinear δ enumK enumEdges enumFaces i) :
    (FiniteNative.edgeSplit M bases (U i) P (private i) ((E i).symm y).1).2 = y.1.1 := by
  exact FiniteNative.generated_solution_inverse_public M bases (U i) P (private i)
    hlinear δ enumK enumEdges enumFaces y

/-- Every retained original edge value is independent of the entire private kernel. -/
theorem restored_value_public (i : I)
    (y : LocalObject M bases P U candidates hlinear δ enumK enumEdges enumFaces i)
    (e : (U i).edges) (he : e.1 ∉ private i) :
    ((E i).symm y).1.1 e = publicValue M bases P U candidates i y.1.1 e := by
  let h := ((E i).symm y).1
  have hz := restored_public M bases P U candidates hlinear δ enumK enumEdges enumFaces i y
  have hh : h = (FiniteNative.edgeSplit M bases (U i) P (private i)).symm
      ((FiniteNative.edgeSplit M bases (U i) P (private i) h).1,y.1.1) := by
    rw [← hz]
    exact (LinearEquiv.symm_apply_apply _ h).symm
  change h.1 e = _
  rw [hh]
  by_cases hp : e.1 ∈ P.edges
  · exact (((FiniteNative.edgeSplit M bases (U i) P (private i)).symm _).2 e hp).trans
      (((FiniteNative.edgeSplit M bases (U i) P (private i)).symm (0,y.1.1)).2 e hp).symm
  · exact FiniteNative.public_edge_private_independent M bases (U i) P (private i)
      _ 0 y.1.1 e hp he

variable (allowed : Set (EdgeName (K := K)))

/-- Support and every shared original value are imposed only on public coordinates. -/
def PublicCompatible (y : ∀ i,LocalObject M bases P U candidates hlinear δ enumK enumEdges enumFaces i) : Prop :=
  (∀ i (e : (U i).edges), e.1 ∈ candidates \ allowed →
    publicValue M bases P U candidates i (y i).1.1 e = 0) ∧
  (∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges), j ≠ i →
    publicValue M bases P U candidates i (y i).1.1 ⟨e,hi⟩ =
      publicValue M bases P U candidates j (y j).1.1 ⟨e,hj⟩)

/-- The strict generated object space retains every local private kernel freedom. -/
def Objects := {y : ∀ i,LocalObject M bases P U candidates hlinear δ enumK enumEdges enumFaces i //
  PublicCompatible M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y}

/-- Coordinates of independently defined strict original supported objects. -/
def coordinate (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed :=
  ⟨fun i => (E i) (h.1 i).1,by
    constructor
    · intro i e he
      have hv := restored_value_public M bases P U candidates hlinear δ enumK enumEdges enumFaces i
        ((E i) (h.1 i).1) e (ClosedRegion.candidate_not_private U P candidates i e.1 he.1)
      rw [Equiv.symm_apply_apply] at hv
      exact hv.symm.trans ((h.1 i).2 e he)
    · intro i j e hi hj hij
      have hvi := restored_value_public M bases P U candidates hlinear δ enumK enumEdges enumFaces i
        ((E i) (h.1 i).1) ⟨e,hi⟩
        (ClosedRegion.overlap_not_private U P candidates i j hij e ⟨hi,hj⟩)
      have hvj := restored_value_public M bases P U candidates hlinear δ enumK enumEdges enumFaces j
        ((E j) (h.1 j).1) ⟨e,hj⟩
        (ClosedRegion.overlap_not_private U P candidates j i (Ne.symm hij) e ⟨hj,hi⟩)
      rw [Equiv.symm_apply_apply] at hvi hvj
      exact hvi.symm.trans ((h.2 i j e hi hj).trans hvj)⟩

/-- The public coordinate is the same full public component of the original edge cochain. -/
theorem coordinate_public (h : StrictSupportedCover.Objects M P U candidates allowed δ) (i : I) :
    ((coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed h).1 i).1.1 =
      (FiniteNative.edgeSplit M bases (U i) P (private i) (h.1 i).1.1).2 := by
  have hv := restored_public M bases P U candidates hlinear δ enumK enumEdges enumFaces i
    ((E i) (h.1 i).1)
  rw [Equiv.symm_apply_apply] at hv
  exact hv.symm

/-- Restore whole original local equations from all public and private coordinates. -/
def restore (y : Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed) :
    StrictSupportedCover.Objects M P U candidates allowed δ :=
  ⟨fun i => ⟨(E i).symm (y.1 i),by
      intro e he
      exact (restored_value_public M bases P U candidates hlinear δ enumK enumEdges enumFaces i
        (y.1 i) e (ClosedRegion.candidate_not_private U P candidates i e.1 he.1)).trans
          (y.2.1 i e he)⟩,by
    intro i j e hi hj
    by_cases hij : j = i
    · subst j; rfl
    · have hvi := restored_value_public M bases P U candidates hlinear δ enumK enumEdges enumFaces i
        (y.1 i) ⟨e,hi⟩ (ClosedRegion.overlap_not_private U P candidates i j hij e ⟨hi,hj⟩)
      have hvj := restored_value_public M bases P U candidates hlinear δ enumK enumEdges enumFaces j
        (y.1 j) ⟨e,hj⟩ (ClosedRegion.overlap_not_private U P candidates j i (Ne.symm hij) e ⟨hj,hi⟩)
      exact hvi.trans ((y.2.2 i j e hi hj hij).trans hvj.symm)⟩

/-- Restoration after coordinates keeps every original local affine solution. -/
theorem restore_coordinate (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
      (coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed h) = h := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact (E i).symm_apply_apply (h.1 i).1

/-- Coordinates after restoration keep all public and all private kernel values. -/
theorem coordinate_restore (y : Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed) :
    coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
      (restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y) = y := by
  apply Subtype.ext
  funext i
  exact (E i).apply_symm_apply (y.1 i)

/-- Independent strict original objects and full generated coordinates are exactly equivalent. -/
def objectEquiv : StrictSupportedCover.Objects M P U candidates allowed δ ≃
    Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed where
  toFun := coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
  invFun := restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
  left_inv := restore_coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
  right_inv := coordinate_restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed

end GeneratedStrictCover
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
