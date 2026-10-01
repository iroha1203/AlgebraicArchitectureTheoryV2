import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.StrictFiniteAssembly
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction
import ResearchLean.AG.RelativeRepairComposition.GeneratedRangeInclusion

/-!
# One-time generated interfaces for every finite assembly order and bracket

## Implementation notes

The original whole leaf cover determines the private edge sets before assembly.
Nested tuples are flattened without eliminating any intermediate shared edge.
The same one-time original generators then read all leaf coordinates. Whole
native inverse laws retain all original labels and every local kernel freedom.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
namespace GeneratedFiniteAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v,Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i,DecidablePred (· ∈ (U i).vertices)] [∀ i,DecidablePred (· ∈ (U i).edges)]
variable [∀ i,DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
variable (allowed : Set (EdgeName (K := K)))
variable (t : FiniteBinary.Tree) (σ : FiniteBinary.Leaves t ≃ I)

/-- Generate all leaf public and private coordinates from independently nested original equations. -/
def objectEquiv : StrictFiniteAssembly.Objects M P U candidates allowed δ t σ ≃
    GeneratedStrictCover.Objects M bases P U candidates hlinear δ ek ee ef allowed :=
  (StrictFiniteAssembly.objectEquiv M P U candidates allowed δ t σ).trans
    (GeneratedStrictCover.objectEquiv M bases P U candidates hlinear δ ek ee ef allowed)

/-- Generated reconstruction returns the entire flattened original leaf family. -/
theorem restore_objects (h : StrictFiniteAssembly.Objects M P U candidates allowed δ t σ) :
    GeneratedStrictCover.restore M bases P U candidates hlinear δ ek ee ef allowed
      (objectEquiv M bases P U candidates hlinear δ ek ee ef allowed t σ h) =
      StrictFiniteAssembly.flatten M P U candidates allowed δ t σ h :=
  GeneratedStrictCover.restore_coordinate M bases P U candidates hlinear δ ek ee ef allowed _

/-- Every original leaf edge value is retained, including candidates and all still-shared edges. -/
theorem restore_leaf_value (h : StrictFiniteAssembly.Objects M P U candidates allowed δ t σ)
    (l : FiniteBinary.Leaves t) (e : (U (σ l)).edges) :
    ((GeneratedStrictCover.restore M bases P U candidates hlinear δ ek ee ef allowed
      (objectEquiv M bases P U candidates hlinear δ ek ee ef allowed t σ h)).1 (σ l)).1.1.1 e =
      (StrictFiniteAssembly.leafEquiv M P U candidates allowed δ t σ h.1 l).1.1.1 e := by
  rw [restore_objects]
  change (StrictFiniteAssembly.tupleEquiv M P U candidates allowed δ t σ h.1 (σ l)).1.1.1 e = _
  rw [StrictFiniteAssembly.tuple_leaf]

/-- All nested original objects and their full labels have computed native interface coordinates. -/
noncomputable def equivalence : StrictFiniteAssembly.Groupoid M P U candidates allowed δ t σ ≌
    GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ ek ee ef allowed :=
  (StrictFiniteAssembly.equivalence M P U candidates allowed δ t σ).trans
    (GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed)

/-- The entire generated forward-inverse composite preserves every original child and arrow. -/
theorem functor_inverse : (equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).functor ⋙
    (equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).inverse =
      𝟭 (StrictFiniteAssembly.Groupoid M P U candidates allowed δ t σ) :=
  strict_trans_functor_inverse _ _ (StrictFiniteAssembly.functor_inverse M P U candidates allowed δ t σ)
    (GeneratedCoverAction.functor_inverse M bases P U candidates hlinear δ ek ee ef allowed)

/-- The entire generated inverse-forward composite retains every public coordinate, full kernel and label. -/
theorem inverse_functor : (equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).inverse ⋙
    (equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).functor =
      𝟭 (GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ ek ee ef allowed) :=
  strict_trans_inverse_functor _ _ (StrictFiniteAssembly.inverse_functor M P U candidates allowed δ t σ)
    (GeneratedCoverAction.inverse_functor M bases P U candidates hlinear δ ek ee ef allowed)

/-- Computed reconstruction is the identical original flattening on the complete native functor. -/
theorem reconstruction_functor :
    (equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).functor ⋙
      (GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed).inverse =
        (StrictFiniteAssembly.equivalence M P U candidates allowed δ t σ).functor := by
  change (StrictFiniteAssembly.equivalence M P U candidates allowed δ t σ).functor ⋙
    ((GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed).functor ⋙
      (GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed).inverse) = _
  rw [GeneratedCoverAction.functor_inverse,Functor.comp_id]

/-- Every generated assembly arrow retains the full original compatible vertex-label tuple. -/
theorem functor_label {x y : StrictFiniteAssembly.Groupoid M P U candidates allowed δ t σ} (b : x ⟶ y) :
    ((equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).functor.map b).1 = b.1 := rfl

variable (t' : FiniteBinary.Tree) (σ' : FiniteBinary.Leaves t' ≃ I)
/-- Every order and bracket change commutes with the same computed full native generation. -/
theorem comparison_generation :
    (StrictFiniteAssembly.comparison M P U candidates allowed δ t σ t' σ').functor ⋙
      (equivalence M bases P U candidates hlinear δ ek ee ef allowed t' σ').functor =
        (equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).functor := by
  change ((StrictFiniteAssembly.comparison M P U candidates allowed δ t σ t' σ').functor ⋙
    (StrictFiniteAssembly.equivalence M P U candidates allowed δ t' σ').functor) ⋙
      (GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed).functor = _
  rw [StrictFiniteAssembly.comparison_rec]
  rfl

variable {S V : Set (EdgeName (K := K))}
/-- Every allowed range relaxation acts on all nested objects and original arrows through the same one-time coordinates. -/
noncomputable def rangeFunctor (h : S ⊆ V) :
    StrictFiniteAssembly.Groupoid M P U candidates S δ t σ ⥤
      StrictFiniteAssembly.Groupoid M P U candidates V δ t σ :=
  (equivalence M bases P U candidates hlinear δ ek ee ef S t σ).functor ⋙
    GeneratedRangeInclusion.functor M bases P U candidates hlinear δ ek ee ef h ⋙
      (equivalence M bases P U candidates hlinear δ ek ee ef V t σ).inverse

/-- Range relaxation commutes with the complete original one-time generation on every object and arrow. -/
theorem range_generation (h : S ⊆ V) :
    rangeFunctor M bases P U candidates hlinear δ ek ee ef t σ h ⋙
      (equivalence M bases P U candidates hlinear δ ek ee ef V t σ).functor =
    (equivalence M bases P U candidates hlinear δ ek ee ef S t σ).functor ⋙
      GeneratedRangeInclusion.functor M bases P U candidates hlinear δ ek ee ef h := by
  change (equivalence M bases P U candidates hlinear δ ek ee ef S t σ).functor ⋙
    (GeneratedRangeInclusion.functor M bases P U candidates hlinear δ ek ee ef h ⋙
      ((equivalence M bases P U candidates hlinear δ ek ee ef V t σ).inverse ⋙
        (equivalence M bases P U candidates hlinear δ ek ee ef V t σ).functor)) = _
  rw [inverse_functor,Functor.comp_id]

/-- Every range relaxation preserves every complete original leaf edge value. -/
theorem range_leaf_value (h : S ⊆ V)
    (x : StrictFiniteAssembly.Groupoid M P U candidates S δ t σ) (i : I) (e : (U i).edges) :
    ((StrictFiniteAssembly.flatten M P U candidates V δ t σ
      ((rangeFunctor M bases P U candidates hlinear δ ek ee ef t σ h).obj x).back).1 i).1.1.1 e =
      ((StrictFiniteAssembly.flatten M P U candidates S δ t σ x.back).1 i).1.1.1 e := by
  let z := objectEquiv M bases P U candidates hlinear δ ek ee ef S t σ x.back
  have hd : StrictFiniteAssembly.flatten M P U candidates V δ t σ
      ((rangeFunctor M bases P U candidates hlinear δ ek ee ef t σ h).obj x).back =
      GeneratedStrictCover.restore M bases P U candidates hlinear δ ek ee ef V
        (GeneratedRangeInclusion.objectsInclusion M bases P U candidates hlinear δ ek ee ef h z) := by
    change (StrictFiniteAssembly.objectEquiv M P U candidates V δ t σ)
      ((StrictFiniteAssembly.objectEquiv M P U candidates V δ t σ).symm _) = _
    exact (StrictFiniteAssembly.objectEquiv M P U candidates V δ t σ).apply_symm_apply _
  rw [hd]
  have hv : ((GeneratedStrictCover.restore M bases P U candidates hlinear δ ek ee ef V
      (GeneratedRangeInclusion.objectsInclusion M bases P U candidates hlinear δ ek ee ef h z)).1 i).1.1.1 e =
      ((GeneratedStrictCover.restore M bases P U candidates hlinear δ ek ee ef S z).1 i).1.1.1 e := rfl
  rw [hv]
  change ((GeneratedStrictCover.restore M bases P U candidates hlinear δ ek ee ef S
    (objectEquiv M bases P U candidates hlinear δ ek ee ef S t σ x.back)).1 i).1.1.1 e = _
  rw [restore_objects]

/-- Full range arrows keep every original compatible vertex label, including stabilizers. -/
theorem range_label_value (h : S ⊆ V)
    {x y : StrictFiniteAssembly.Groupoid M P U candidates S δ t σ} (b : x ⟶ y)
    (i : I) (v : (U i).vertices) :
    ((((rangeFunctor M bases P U candidates hlinear δ ek ee ef t σ h).map b).1.toAdd).1 i).1.1 v =
      (b.1.toAdd.1 i).1.1 v := rfl

/-- The concrete finite order/bracket comparison equals the comparison through complete generated coordinates. -/
theorem comparison_generated :
    (StrictFiniteAssembly.comparison M P U candidates allowed δ t σ t' σ').functor =
      (equivalence M bases P U candidates hlinear δ ek ee ef allowed t σ).functor ⋙
        (equivalence M bases P U candidates hlinear δ ek ee ef allowed t' σ').inverse := by
  change (StrictFiniteAssembly.equivalence M P U candidates allowed δ t σ).functor ⋙
    (StrictFiniteAssembly.equivalence M P U candidates allowed δ t' σ').inverse =
    (StrictFiniteAssembly.equivalence M P U candidates allowed δ t σ).functor ⋙
      ((GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed).functor ⋙
        (GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed).inverse) ⋙
          (StrictFiniteAssembly.equivalence M P U candidates allowed δ t' σ').inverse
  rw [GeneratedCoverAction.functor_inverse,Functor.id_comp]

/-- Every finite order/bracket comparison commutes with all allowed-range relaxation functors. -/
theorem comparison_range (h : S ⊆ V) :
    rangeFunctor M bases P U candidates hlinear δ ek ee ef t σ h ⋙
      (StrictFiniteAssembly.comparison M P U candidates V δ t σ t' σ').functor =
    (StrictFiniteAssembly.comparison M P U candidates S δ t σ t' σ').functor ⋙
      rangeFunctor M bases P U candidates hlinear δ ek ee ef t' σ' h := by
  rw [comparison_generated M bases P U candidates hlinear δ ek ee ef V t σ t' σ',
    comparison_generated M bases P U candidates hlinear δ ek ee ef S t σ t' σ']
  change (equivalence M bases P U candidates hlinear δ ek ee ef S t σ).functor ⋙
    (GeneratedRangeInclusion.functor M bases P U candidates hlinear δ ek ee ef h ⋙
      ((equivalence M bases P U candidates hlinear δ ek ee ef V t σ).inverse ⋙
        (equivalence M bases P U candidates hlinear δ ek ee ef V t σ).functor)) ⋙
          (equivalence M bases P U candidates hlinear δ ek ee ef V t' σ').inverse =
    (equivalence M bases P U candidates hlinear δ ek ee ef S t σ).functor ⋙
      (((equivalence M bases P U candidates hlinear δ ek ee ef S t' σ').inverse ⋙
        (equivalence M bases P U candidates hlinear δ ek ee ef S t' σ').functor) ⋙
          GeneratedRangeInclusion.functor M bases P U candidates hlinear δ ek ee ef h) ⋙
            (equivalence M bases P U candidates hlinear δ ek ee ef V t' σ').inverse
  rw [inverse_functor,inverse_functor,Functor.comp_id,Functor.id_comp]

end GeneratedFiniteAssembly
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
