import ResearchLean.AG.LocalSemanticReconstruction.PrimitiveFunctionGraphCategory
import Formal.Util.AssertStandardAxioms

/-!
# Dependent point graphs on carriers supplied by primitive references

Implementation notes: context Support, Axis, and Observable queries already
determine their value carriers from the context references. They therefore
need no second candidate-carrier layer. This API keeps all candidate index
pairs, gives false values to inactive pairs, and reuses the existing
total-functional graph assembler. The map F occurs only in the comparison API;
the local row conditions use the independent Boolean index points p.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

noncomputable section

universe u v w z

variable {I : Type u} {J : Type v} (S : I → Type w) (T : J → Type z)

/-- A point response on the value carriers selected by its two primitive index references. -/
abbrev Table := ∀ i j, S i → T j → Bool

/-- Inactive pairs are false; every active pair has one output for each input. -/
structure IsLawful (p : I → J → Bool) (q : Table S T) : Prop where
  /-- No extra data are retained at inactive index pairs. -/
  inactive : ∀ i j, p i j = false → ∀ x y, q i j x y = false
  /-- Active dependent rows are directed total-function graphs. -/
  active : ∀ i j, p i j = true → ∀ x, ∃! y, q i j x y = true

variable {S T} {p : I → J → Bool}

/-- The existing primitive graph code at a true index pair uses exactly that row's Boolean responses. -/
def graph (q : Table S T) (hq : IsLawful S T p q) (i : I) (j : J) (hij : p i j = true) :
    PrimitiveFunctionGraph.GraphCode (S i) (T j) := ⟨⟨q i j⟩, ⟨hq.active i j hij⟩⟩

variable (F : I → J) (hp : ∀ i j, p i j = true ↔ F i = j)

/-- Construct the directed native dependent family from its active primitive rows. -/
def assemble (q : Table S T) (hq : IsLawful S T p q) : ∀ i, S i → T (F i) :=
  fun i => (graph q hq i (F i) ((hp i (F i)).2 rfl)).assemble

/-- Each true point on an active native row is exactly its assembled image. -/
theorem point_iff (q : Table S T) (hq : IsLawful S T p q) (i : I) (x : S i) (y : T (F i)) :
    q i (F i) x y = true ↔ assemble F hp q hq i x = y :=
  (graph q hq i (F i) ((hp i (F i)).2 rfl)).edge_eq_true_iff_target_eq x y

/-- Read each native point at its original candidate index pair and set every inactive pair to false. -/
def read (f : ∀ i, S i → T (F i)) : Table S T := by
  classical
  exact fun i j x y => if he : F i = j then decide (cast (congrArg T he) (f i x) = y) else false

/-- At the actual native image index, a reading is exactly equality with the function value. -/
theorem read_point_iff (f : ∀ i, S i → T (F i)) (i : I) (x : S i) (y : T (F i)) :
    read F f i (F i) x y = true ↔ f i x = y := by
  classical
  simp [read]

include hp in
/-- Every native dependent map satisfies precisely the inactive and unique-output row conditions. -/
theorem read_isLawful (f : ∀ i, S i → T (F i)) : IsLawful S T p (read F f) := by
  classical
  constructor
  · intro i j hij x y
    have hn : F i ≠ j := fun he => Bool.noConfusion (hij.symm.trans ((hp i j).2 he))
    simp [read, hn]
  · intro i j hij x
    obtain rfl := (hp i j).1 hij
    refine ⟨f i x, (read_point_iff F f i x _).2 rfl, ?_⟩
    intro y hy
    exact ((read_point_iff F f i x y).1 hy).symm

/-- Reading and assembling restores every native directed dependent function. -/
theorem assemble_read (f : ∀ i, S i → T (F i)) :
    assemble F hp (read F f) (read_isLawful F hp f) = f := by
  funext i x
  exact (point_iff F hp _ _ i x (f i x)).1 ((read_point_iff F f i x _).2 rfl)

/-- Re-reading restores the entire primitive table, including all inactive candidate pairs. -/
theorem read_assemble (q : Table S T) (hq : IsLawful S T p q) :
    read F (assemble F hp q hq) = q := by
  classical
  funext i j x y
  by_cases he : F i = j
  · subst j
    apply Bool.eq_iff_iff.mpr
    exact (read_point_iff F _ i x y).trans (point_iff F hp q hq i x y).symm
  · have hn : p i j = false := Bool.eq_false_iff.mpr (fun hh => he ((hp i j).1 hh))
    simp [read, he, hq.inactive i j hn x y]

/-- All native dependent directed maps have exact presentations by these typed primitive point rows. -/
def readingEquiv : (∀ i, S i → T (F i)) ≃ {q : Table S T // IsLawful S T p q} where
  toFun f := ⟨read F f, read_isLawful F hp f⟩
  invFun q := assemble F hp q.val q.property
  left_inv := assemble_read F hp
  right_inv q := Subtype.ext (read_assemble F hp q.val q.property)

/-- Inverse-dependent rows retain both original point directions without adding an inverse index map. -/
structure InverseLaws (p : I → J → Bool) (q r : Table S T) : Prop where
  /-- Forward rows are directed total functions at each active pair. -/
  forward : IsLawful S T p q
  /-- Reverse rows have a unique source for each target value. -/
  backward : ∀ i j, p i j = true → ∀ y, ∃! x, r i j x y = true
  /-- The same ordered source/target pair describes inverse edges in both directions. -/
  inverse : ∀ i j x y, q i j x y = r i j x y

/-- The reverse graph at one active pair has target-to-source function direction. -/
def backwardGraph (q r : Table S T) (hl : InverseLaws p q r) (i : I) (j : J) (hij : p i j = true) :
    PrimitiveFunctionGraph.GraphCode (T j) (S i) := ⟨⟨fun y x => r i j x y⟩, ⟨hl.backward i j hij⟩⟩

/-- Assemble all fiber equivalences using the two primitive graph directions. -/
def assembleEquiv (q r : Table S T) (hl : InverseLaws p q r) : ∀ i, S i ≃ T (F i) := fun i => {
  toFun := assemble F hp q hl.forward i
  invFun := (backwardGraph q r hl i (F i) ((hp i (F i)).2 rfl)).assemble
  left_inv := by
    intro x
    apply (backwardGraph q r hl i (F i) ((hp i (F i)).2 rfl)).target_eq_of_edge
    exact (hl.inverse i (F i) x _).symm.trans ((point_iff F hp q hl.forward i x _).2 rfl)
  right_inv := by
    intro y
    apply (point_iff F hp q hl.forward i _ y).1
    exact (hl.inverse i (F i) _ y).trans
      ((backwardGraph q r hl i (F i) ((hp i (F i)).2 rfl)).edge_target y) }

/-- The forward point table recovers all native images of the assembled equivalence family. -/
theorem read_assembleEquiv (q r : Table S T) (hl : InverseLaws p q r) :
    read F (fun i => assembleEquiv F hp q r hl i) = q := read_assemble F hp q hl.forward

/-- The reverse point table agrees with the same ordered inverse-edge reading. -/
theorem read_assembleEquiv_backward (q r : Table S T) (hl : InverseLaws p q r) :
    read F (fun i => assembleEquiv F hp q r hl i) = r :=
  (read_assembleEquiv F hp q r hl).trans (funext fun i => funext fun j => funext fun x => funext fun y => hl.inverse i j x y)

include hp in
/-- Native equivalence readings satisfy the original inverse row laws at every index pair. -/
theorem read_inverseLaws (f : ∀ i, S i ≃ T (F i)) :
    InverseLaws p (read F (fun i => f i)) (read F (fun i => f i)) := by
  refine ⟨read_isLawful F hp (fun i => f i), ?_, fun _ _ _ _ => rfl⟩
  intro i j hij y
  obtain rfl := (hp i j).1 hij
  refine ⟨(f i).symm y, (read_point_iff F _ i _ y).2 ((f i).apply_symm_apply y), ?_⟩
  intro x hx
  exact (f i).injective (((read_point_iff F _ i x y).1 hx).trans ((f i).apply_symm_apply y).symm)

/-- The inverse-row assembler restores every original fiber equivalence. -/
theorem assembleEquiv_read (f : ∀ i, S i ≃ T (F i)) :
    assembleEquiv F hp (read F (fun i => f i)) (read F (fun i => f i)) (read_inverseLaws F hp f) = f := by
  funext i
  apply Equiv.ext
  intro x
  exact congrFun (congrFun (assemble_read F hp (fun i => f i)) i) x

end

end AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph
