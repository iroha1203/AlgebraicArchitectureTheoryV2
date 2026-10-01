import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteFamilyCoordinates
import ResearchLean.AG.RelativeRepairComposition.IndexedClosedCovers

/-!
# Public and private original-cell coordinate partition

## Implementation notes

Only nonshared always-allowed original edges are internal. The complement
retains all shared and candidate edges, including parallel named edges. The
linear split and its inverse read and restore the same original index.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uk uj uG uCover
namespace FinitePartition
variable {k : Type uk} [Field k]
variable {J : Type uj} (internal : Set J) [DecidablePred (· ∈ internal)]

/-- Read both parts while keeping the same original coordinate index. -/
def split (v : J → k) : (internal → k) × (↥(internalᶜ) → k) :=
  (fun i => v i.1,fun i => v i.1)

/-- Join both parts by the supplied original-index membership decision. -/
def join (v : (internal → k) × (↥(internalᶜ) → k)) : J → k :=
  fun i => if hi : i ∈ internal then v.1 ⟨i,hi⟩ else v.2 ⟨i,hi⟩

omit [Field k] in
/-- Joining after splitting retains every original value. -/
theorem join_split (v : J → k) : join internal (split internal v) = v := by
  funext i
  unfold join split
  split <;> rfl

omit [Field k] in
/-- Splitting after joining retains both complete coordinate families. -/
theorem split_join (v : (internal → k) × (↥(internalᶜ) → k)) : split internal (join internal v) = v := by
  apply Prod.ext
  · funext i
    change (if hi : i.1 ∈ internal then v.1 ⟨i.1,hi⟩ else v.2 ⟨i.1,hi⟩) = v.1 i
    simp only [dif_pos i.2]
  · funext i
    change (if hi : i.1 ∈ internal then v.1 ⟨i.1,hi⟩ else v.2 ⟨i.1,hi⟩) = v.2 i
    simp only [dif_neg i.2]

/-- Full linear coordinate partition with both exact inverse compositions. -/
def equivalence : (J → k) ≃ₗ[k] ((internal → k) × (↥(internalᶜ) → k)) where
  toFun := split internal
  invFun := join internal
  left_inv := join_split internal
  right_inv := split_join internal
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Field k] in
/-- Public reconstruction reads the same original value independently of the private component. -/
theorem join_public (v : (internal → k) × (↥(internalᶜ) → k)) (i : ↥(internalᶜ)) :
    join internal v i.1 = v.2 i := by
  change (if hi : i.1 ∈ internal then _ else _) = _
  simp only [dif_neg i.2]

end FinitePartition
namespace ClosedRegion
variable {K : FiniteTransportPresentation.{uG}}
variable {I : Type uCover} (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K)))

/-- Shared original edges occur in another region of the same indexed cover. -/
def sharedEdges (i : I) : Set (EdgeName (K := K)) := {e | ∃ j, j ≠ i ∧ e ∈ (U j).edges}

/-- Only nonfixed, noncandidate and nonshared edges of this region are private variables. -/
def privateAlwaysEdges (i : I) : Set (EdgeName (K := K)) :=
  {e | e ∈ (U i).edges ∧ e ∉ P.edges ∧ e ∉ candidates ∧ e ∉ sharedEdges U i}

/-- Finite cover membership computes whether another region contains an original edge. -/
instance sharedEdgesDecidable [Fintype I] [DecidableEq I]
    [∀ j, DecidablePred (· ∈ (U j).edges)] (i : I) : DecidablePred (· ∈ sharedEdges U i) :=
  fun e => show Decidable (∃ j, j ≠ i ∧ e ∈ (U j).edges) from inferInstance

/-- The finite original input computes exactly the nonshared always-allowed private set. -/
instance privateAlwaysEdgesDecidable [Fintype I] [DecidableEq I]
    [∀ j, DecidablePred (· ∈ (U j).edges)] [DecidablePred (· ∈ P.edges)]
    [DecidablePred (· ∈ candidates)] (i : I) : DecidablePred (· ∈ privateAlwaysEdges U P candidates i) :=
  fun e => show Decidable (e ∈ (U i).edges ∧ e ∉ P.edges ∧ e ∉ candidates ∧ e ∉ sharedEdges U i) from inferInstance

/-- Sharedness exposes occurrence in another region, with its same original edge name. -/
theorem mem_sharedEdges (i : I) (e : EdgeName (K := K)) :
    e ∈ sharedEdges U i ↔ ∃ j, j ≠ i ∧ e ∈ (U j).edges := Iff.rfl

/-- A second region containing an edge makes that same edge shared. -/
theorem shared_of_other (i j : I) (hij : j ≠ i) (e : EdgeName (K := K)) (he : e ∈ (U j).edges) :
    e ∈ sharedEdges U i := ⟨j,hij,he⟩

/-- A single-index family has no shared edges. -/
theorem not_shared_subsingleton [Subsingleton I] (i : I) (e : EdgeName (K := K)) :
    e ∉ sharedEdges U i := by
  rintro ⟨j,hj,_⟩
  exact hj (Subsingleton.elim j i)

/-- Private membership retains all four specified conditions. -/
theorem mem_privateAlwaysEdges (i : I) (e : EdgeName (K := K)) :
    e ∈ privateAlwaysEdges U P candidates i ↔
      e ∈ (U i).edges ∧ e ∉ P.edges ∧ e ∉ candidates ∧ e ∉ sharedEdges U i := Iff.rfl

/-- Every candidate edge stays outside the internal variables. -/
theorem candidate_not_private (i : I) (e : EdgeName (K := K)) (he : e ∈ candidates) :
    e ∉ privateAlwaysEdges U P candidates i := by
  intro h
  exact h.2.2.1 he

/-- Every edge shared with another region stays outside the internal variables. -/
theorem shared_not_private (i : I) (e : EdgeName (K := K)) (he : e ∈ sharedEdges U i) :
    e ∉ privateAlwaysEdges U P candidates i := by
  intro h
  exact h.2.2.2 he

/-- A region's nonfixed noncandidate edge with no other occurrence is a private variable. -/
theorem private_of_nonshared (i : I) (e : EdgeName (K := K))
    (hu : e ∈ (U i).edges) (hp : e ∉ P.edges) (hc : e ∉ candidates) (hs : e ∉ sharedEdges U i) :
    e ∈ privateAlwaysEdges U P candidates i := ⟨hu,hp,hc,hs⟩

/-- Every original edge in an overlap with another region is public in this region. -/
theorem overlap_not_private (i j : I) (hij : j ≠ i) (e : EdgeName (K := K))
    (he : e ∈ (inter (U i) (U j)).edges) : e ∉ privateAlwaysEdges U P candidates i :=
  shared_not_private U P candidates i e (shared_of_other U i j hij e he.2)

end ClosedRegion
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
