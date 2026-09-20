import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierComposition
import Formal.Util.AssertStandardAxioms

/-!
# Primitive composition of context-indexed point graphs

Implementation notes: an index point chooses the middle context and a value
point chooses the middle value. The second table is read at those two points.
Its own inactivity law handles false second-index candidates. Native maps
occur only in the comparison API, which covers every candidate index pair.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

noncomputable section

universe u v w x y z

variable {I : Type u} {J : Type v} {K : Type w}
variable {S : I → Type x} {M : J → Type y} {T : K → Type z}
variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (h : Table S M) (hh : IsLawful S M p h) (k : Table M T)

/-- Follow one primitive index point and one primitive value point before reading the second row. -/
def compose : Table S T := fun i l x y =>
  let j := IndependentIndexedCarrierGraph.index p hp i
  k j l ((graph h hh i j ((IndependentIndexedCarrierGraph.active_iff p hp i j).2 rfl)).assemble x) y

/-- Any true first index pair exposes the same direct value composition. -/
theorem compose_at_pair (i : I) (j : J) (l : K) (hij : p i j = true) (x : S i) (y : T l) :
    compose p hp h hh k i l x y = k j l ((graph h hh i j hij).assemble x) y := by
  have he := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
  subst j
  rfl

variable (q : J → K → Bool) (hk : IsLawful M T q k)

include hk in
/-- The primitive composite preserves inactivity and exactly one output on each active row. -/
theorem compose_isLawful : IsLawful S T (IndependentIndexedCarrierGraph.composeIndex p hp q)
    (compose p hp h hh k) := by
  constructor
  · intro i l hil x y
    exact hk.inactive _ l hil _ y
  · intro i l hil x
    exact hk.active _ l hil _

variable (F : I → J) (hpF : ∀ i j, p i j = true ↔ F i = j)
variable (G : J → K) (hqG : ∀ j l, q j l = true ↔ G j = l)

/-- Direct point composition reads the successive native dependent functions at every candidate pair. -/
theorem compose_eq_read : compose p hp h hh k =
    read (G ∘ F) (fun i x => assemble G hqG k hk (F i) (assemble F hpF h hh i x)) := by
  classical
  funext i l x y
  have hij : p i (F i) = true := (hpF i _).2 rfl
  rw [compose_at_pair p hp h hh k i (F i) l hij x y]
  by_cases hil : G (F i) = l
  · subst l
    apply Bool.eq_iff_iff.mpr
    exact (point_iff G hqG k hk (F i) _ y).trans
      (read_point_iff (G ∘ F) (fun i x => assemble G hqG k hk (F i) (assemble F hpF h hh i x)) i x y).symm
  · have h0 : q (F i) l = false := Bool.eq_false_iff.mpr (fun ht => hil ((hqG _ _).1 ht))
    rw [hk.inactive _ _ h0]
    simp only [read, Function.comp_apply, hil, ↓reduceDIte]

include hpF hqG in
/-- The composed primitive index flag is precisely the successive native index image. -/
theorem compose_index_iff (i : I) (l : K) :
    IndependentIndexedCarrierGraph.composeIndex p hp q i l = true ↔ G (F i) = l := by
  have he : IndependentIndexedCarrierGraph.index p hp i = F i :=
    ((IndependentIndexedCarrierGraph.active_iff p hp i (F i)).1 ((hpF i (F i)).2 rfl)).symm
  change q (IndependentIndexedCarrierGraph.index p hp i) l = true ↔ _
  rw [he]
  exact hqG (F i) l

/-- The composed point family assembles to the ordinary composition of the original native families. -/
theorem assemble_compose :
    assemble (G ∘ F) (compose_index_iff p hp q F hpF G hqG)
      (compose p hp h hh k) (compose_isLawful p hp h hh k q hk) =
      fun i x => assemble G hqG k hk (F i) (assemble F hpF h hh i x) := by
  funext i x
  apply (point_iff (G ∘ F) _ _ (compose_isLawful p hp h hh k q hk) i x _).1
  rw [compose_eq_read p hp h hh k q hk F hpF G hqG]
  exact (read_point_iff (G ∘ F) _ i x _).2 rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph
