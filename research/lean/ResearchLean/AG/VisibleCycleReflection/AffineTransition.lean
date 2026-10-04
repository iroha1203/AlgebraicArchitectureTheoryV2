import ResearchLean.AG.VisibleCycleReflection.ActualReflection
import Formal.Util.AssertStandardAxioms

/-!
# Primitive affine transitions on the actual open cover

## Implementation notes

Transition values retain the original presentation group. Ordered nonempty
intersections read the actual Cech transition; reversing the order negates it.
At any geometric point, T0 allows at most two distinct charts. Thus the atlas
cocycle follows from inverse and identity laws, without a supplied coherence
certificate. Generic atlas laws below are direction hypotheses; the actual
constructor proves them from the primitive transition and T0.
-/

noncomputable section
open TopologicalSpace Set Classical
namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge
universe u

/-- An affine atlas before constructing its fibers and locally constant states. -/
structure AffineAtlas (X I M : Type u) [TopologicalSpace X] [AddCommGroup M] where
  patch : I → Opens X
  covers : ∀ x : X, ∃ i, x ∈ patch i
  transition : I → I → M
  self : ∀ i, transition i i = 0
  reverse : ∀ i j, transition j i = -transition i j
  cocycle : ∀ i j k x, x ∈ patch i → x ∈ patch j → x ∈ patch k →
    transition i j + transition j k = transition i k

namespace GeometricCover
variable {X I M : Type u} [TopologicalSpace X] [LinearOrder I] [AddCommGroup M]
variable (K : GeometricCover X I)

/-- Identity, signed ordered transition, and the unique value on an empty overlap. -/
def transitionValue (c : K.Edge → M) (i j : I) : M :=
  if hij : i < j then
    if ho : ((K.patch i ⊓ K.patch j : Opens X) : Set X).Nonempty then
      c ⟨(i,j),hij,ho⟩ else 0
  else if hji : j < i then
    if ho : ((K.patch j ⊓ K.patch i : Opens X) : Set X).Nonempty then
      -c ⟨(j,i),hji,ho⟩ else 0
  else 0

/-- Public value on every ordered, nonempty actual overlap. -/
theorem transitionValue_forward (c : K.Edge → M) (e : K.Edge) :
    K.transitionValue c e.1.1 e.1.2 = c e := by
  rw [transitionValue, dif_pos e.2.1, dif_pos e.2.2]

/-- Self transitions are zero for every primitive cochain. -/
@[simp] theorem transitionValue_self (c : K.Edge → M) (i : I) :
    K.transitionValue c i i = 0 := by
  simp [transitionValue]

/-- Reversing a transition negates its original primitive value. -/
theorem transitionValue_reverse (c : K.Edge → M) (i j : I) :
    K.transitionValue c j i = -K.transitionValue c i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [transitionValue,dif_pos h,dif_neg (not_lt_of_ge (le_of_lt h))]
    split_ifs <;> simp
  · simp
  · simp only [transitionValue,dif_pos h,dif_neg (not_lt_of_ge (le_of_lt h))]
    split_ifs <;> simp

/-- Empty actual intersections carry the zero transition. -/
theorem transitionValue_empty (c : K.Edge → M) (i j : I)
    (h : ¬((K.patch i ⊓ K.patch j : Opens X) : Set X).Nonempty) :
    K.transitionValue c i j = 0 := by
  have h' : ¬((K.patch j ⊓ K.patch i : Opens X) : Set X).Nonempty := by
    simpa only [inf_comm] using h
  simp only [transitionValue,dif_neg h,dif_neg h']
  simp

/-- T0 forbids one point from lying in three strictly ordered distinct charts. -/
theorem not_mem_three (i j k : I) (hij : i < j) (hjk : j < k) (x : X)
    (hi : x ∈ K.patch i) (hj : x ∈ K.patch j) : x ∉ K.patch k := by
  intro hk
  exact K.tripleEmpty i j k hij hjk ⟨x,⟨⟨hi,hj⟩,hk⟩⟩

/-- At any actual point, a triple of chart indices repeats an index. -/
theorem index_eq_of_mem_three (i j k : I) (x : X)
    (hi : x ∈ K.patch i) (hj : x ∈ K.patch j) (hk : x ∈ K.patch k) :
    i = j ∨ j = k ∨ i = k := by
  by_contra h
  simp only [not_or] at h
  rcases lt_or_gt_of_ne h.1 with hij | hji
  · rcases lt_or_gt_of_ne h.2.1 with hjk | hkj
    · exact K.not_mem_three i j k hij hjk x hi hj hk
    · rcases lt_or_gt_of_ne h.2.2 with hik | hki
      · exact K.not_mem_three i k j hik hkj x hi hk hj
      · exact K.not_mem_three k i j hki hij x hk hi hj
  · rcases lt_or_gt_of_ne h.2.2 with hik | hki
    · exact K.not_mem_three j i k hji hik x hj hi hk
    · rcases lt_or_gt_of_ne h.2.1 with hjk | hkj
      · exact K.not_mem_three j k i hjk hki x hj hk hi
      · exact K.not_mem_three k j i hkj hji x hk hj hi

/-- Every original primitive transition obeys the pointwise atlas cocycle. -/
theorem transitionValue_cocycle (c : K.Edge → M) (i j k : I) (x : X)
    (hi : x ∈ K.patch i) (hj : x ∈ K.patch j) (hk : x ∈ K.patch k) :
    K.transitionValue c i j + K.transitionValue c j k = K.transitionValue c i k := by
  rcases K.index_eq_of_mem_three i j k x hi hj hk with h | h | h
  · subst j; simp
  · subst k; simp
  · subst k
    rw [transitionValue_reverse,transitionValue_self,neg_add_cancel]

/-- All atlas laws are generated from T0 and the independently given edge values. -/
def atlasFromCochain (c : K.Edge → M) : AffineAtlas X I M where
  patch := K.patch
  covers := K.covers
  transition := K.transitionValue c
  self := K.transitionValue_self c
  reverse := K.transitionValue_reverse c
  cocycle := K.transitionValue_cocycle c

variable {Source : Type u} {laws : FiniteLawFamily Source} {q : Reading Source}
variable [Fintype I] (P : GeneratorPresentation laws) (target : I → Set q.Target)
    (hne : ∀ i, (target i).Nonempty)

/-- The atlas generated by arbitrary actual integer transition sections on this cover. -/
def actualAffineAtlas
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1) :
    AffineAtlas X I P.PresentationGroup :=
  K.atlasFromCochain (P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne) ξ)

/-- The actual atlas retains every chart of the original geometric cover. -/
@[simp] theorem actualAffineAtlas_patch
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1) (i : I) :
    (K.actualAffineAtlas P target hne ξ).patch i = K.patch i := rfl

/-- Original actual transition values are the atlas's forward overlap translations. -/
theorem actualAffineAtlas_transition
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1) (e : K.Edge) :
    (K.actualAffineAtlas P target hne ξ).transition e.1.1 e.1.2 =
      P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne) ξ e :=
  K.transitionValue_forward _ e

end GeometricCover
end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
