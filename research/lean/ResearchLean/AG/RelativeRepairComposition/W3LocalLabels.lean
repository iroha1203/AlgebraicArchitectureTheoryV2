import ResearchLean.AG.RelativeRepairComposition.W3LocalRepairs

/-! # W3's full original patch labels

At empty permission the original e imposes b_t=b_s, the original f imposes
b_s=T b_t, and the edge-free overlap keeps two independent full vectors.
-/
namespace AAT.AG.RelativeRepairComposition.W3LocalLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3LocalRepairs

/-- Original s selected in U. -/
def leftS : (ClosedRegion.presentation leftRegion).Vertex := ⟨vertexS, Set.mem_univ _⟩
/-- Original t selected in U. -/
def leftT : (ClosedRegion.presentation leftRegion).Vertex := ⟨vertexT, Set.mem_univ _⟩
/-- Original s selected in V. -/
def rightS : (ClosedRegion.presentation rightRegion).Vertex := ⟨vertexS, Set.mem_univ _⟩
/-- Original t selected in V. -/
def rightT : (ClosedRegion.presentation rightRegion).Vertex := ⟨vertexT, Set.mem_univ _⟩
/-- Original s retained in the actual overlap. -/
def overlapS : (ClosedRegion.presentation overlap).Vertex :=
  ⟨vertexS, by change vertexS ∈ overlap.vertices; rw [overlap_vertices]; exact Set.mem_univ _⟩
/-- Original t retained in the actual overlap. -/
def overlapT : (ClosedRegion.presentation overlap).Vertex :=
  ⟨vertexT, by change vertexT ∈ overlap.vertices; rw [overlap_vertices]; exact Set.mem_univ _⟩

/-- U's selected edge is precisely the original e. -/
def leftEdge : EdgeName (K := ClosedRegion.presentation leftRegion) :=
  (ClosedRegion.edgeNameEquiv leftRegion).symm ⟨name edgeE, rfl⟩
/-- V's selected edge is precisely the original f. -/
def rightEdge : EdgeName (K := ClosedRegion.presentation rightRegion) :=
  (ClosedRegion.edgeNameEquiv rightRegion).symm ⟨name edgeF, rfl⟩

/-- The original overlap contains no actual typed edge. -/
theorem overlap_no_edge (e : EdgeName (K := ClosedRegion.presentation overlap)) : False := by
  have h : (ClosedRegion.edgeNameEquiv overlap e).1 ∈
      (∅ : Set (EdgeName (K := geometry))) := by
    simpa only [overlap_edges] using (ClosedRegion.edgeNameEquiv overlap e).2
  exact h

/-- Forbidden original e equates both complete U vectors. -/
theorem left_relation (sheared : Bool) (b : LocalLabels sheared leftRegion ∅) :
    b.1 leftT = b.1 leftS :=
  b.2.2 leftEdge (local_fixed_all leftRegion leftEdge)

/-- Forbidden original f keeps its full T relation between both complete V vectors. -/
theorem right_relation (sheared : Bool) (b : LocalLabels sheared rightRegion ∅) :
    b.1 rightS = linearAction sheared (b.1 rightT) :=
  b.2.2 rightEdge (local_fixed_all rightRegion rightEdge)

/-- Every entire A vector gives the original constant full U label. -/
def leftLabel (sheared : Bool) (a : A) : LocalLabels sheared leftRegion ∅ :=
  ⟨fun _ => a, by
    constructor
    · intro v hv; exact hv.elim
    · intro e he
      have hn : (ClosedRegion.edgeNameEquiv leftRegion e).1 = name edgeE :=
        (ClosedRegion.edgeNameEquiv leftRegion e).2
      change a = (reference sheared e.2.2.1).linear a
      have h := congrArg (fun e : EdgeName (K := geometry) =>
        (reference sheared e.2.2).linear a) hn
      exact h.symm⟩

/-- Every entire A vector gives V's original (T a,a) label. -/
def rightLabel (sheared : Bool) (a : A) : LocalLabels sheared rightRegion ∅ :=
  ⟨fun v => if (v.1 : Fin 2).val = 0 then linearAction sheared a else a, by
    constructor
    · intro v hv; exact hv.elim
    · intro e he
      have hn : (ClosedRegion.edgeNameEquiv rightRegion e).1 = name edgeF :=
        (ClosedRegion.edgeNameEquiv rightRegion e).2
      change (fun e : EdgeName (K := geometry) =>
        (if (e.2.1 : Fin 2).val = 0 then linearAction sheared a else a) =
          (reference sheared e.2.2).linear
            (if (e.1 : Fin 2).val = 0 then linearAction sheared a else a))
          (ClosedRegion.edgeNameEquiv rightRegion e).1
      rw [hn]
      rfl⟩

/-- Every original U label and all A have both additive inverse coordinates. -/
def leftLabelEquiv (sheared : Bool) : LocalLabels sheared leftRegion ∅ ≃+ A where
  toFun b := b.1 leftS
  invFun := leftLabel sheared
  left_inv b := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v
    · rfl
    · exact (left_relation sheared b).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Every original V label and all A have both additive inverse coordinates, using the original t. -/
def rightLabelEquiv (sheared : Bool) : LocalLabels sheared rightRegion ∅ ≃+ A where
  toFun b := b.1 rightT
  invFun := rightLabel sheared
  left_inv b := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v
    · exact (right_relation sheared b).symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Both original overlap vertex vectors are free for every permission. -/
def overlapLabel (sheared : Bool) (S : Set (EdgeName (K := geometry))) (bs bt : A) :
    LocalLabels sheared overlap S :=
  ⟨fun v => if (v.1 : Fin 2).val = 0 then bs else bt, by
    constructor
    · intro v hv; exact hv.elim
    · intro e he; exact (overlap_no_edge e).elim⟩

/-- All original overlap labels have both inverse coordinates in the entire A². -/
def overlapLabelEquiv (sheared : Bool) (S : Set (EdgeName (K := geometry))) :
    LocalLabels sheared overlap S ≃+ (A × A) where
  toFun b := ⟨b.1 overlapS,b.1 overlapT⟩
  invFun b := overlapLabel sheared S b.1 b.2
  left_inv b := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end AAT.AG.RelativeRepairComposition.W3LocalLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3LocalLabels
