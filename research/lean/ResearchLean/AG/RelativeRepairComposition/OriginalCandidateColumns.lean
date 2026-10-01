import ResearchLean.AG.RelativeRepairComposition.FiniteCoefficientDifferentials
import Mathlib.LinearAlgebra.Pi

/-!
# The original global differential split into always and named candidate columns

The always source is the entire relative degree-one family with zero candidate
values. Each candidate input is its whole original target kernel. Masks read the
same original values; no image basis, repair or separation certificate is input.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace OriginalColumns
set_option autoImplicit false
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable [DecidablePred (· ∈ candidates)]
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
local notation "C1P" => RelativeCover.C1 M ClosedRegion.all P
local notation "C2P" => RelativeCover.C2 M ClosedRegion.all P

/-- All named candidates retain their full original target coefficient space. -/
abbrev CandidateValues := ∀ e : candidates, M.A e.1.2.1

/-- Always-allowed corrections are precisely the full relative family zero on all candidates. -/
def alwaysSpace : Submodule k C1P where
  carrier := {h | ∀ e : candidates, h.1 ⟨e.1,Set.mem_univ e.1⟩ = 0}
  zero_mem' _ := rfl
  add_mem' {a} {b} ha hb e := by
    change a.1 ⟨e.1,Set.mem_univ e.1⟩ + b.1 ⟨e.1,Set.mem_univ e.1⟩ = 0
    rw [ha e,hb e,add_zero]
  smul_mem' t h hh e := by
    change t • h.1 ⟨e.1,Set.mem_univ e.1⟩ = 0
    rw [hh e,smul_zero]

/-- Read every candidate from its same original relative edge value. -/
def candidateRead : C1P →ₗ[k] CandidateValues M candidates where
  toFun h e := h.1 ⟨e.1,Set.mem_univ e.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)

/-- Restore all original candidate values and zero all other original edges. -/
def candidateCochain : CandidateValues M candidates →ₗ[k] C1P where
  toFun y := ⟨fun e => if he : e.1 ∈ candidates then y ⟨e.1,he⟩ else 0,by
    intro e hp
    exact dif_neg (fun hc => houtside e.1 hc hp)⟩
  map_add' y z := by
    apply Subtype.ext
    funext e
    change (if he : e.1 ∈ candidates then y ⟨e.1,he⟩ + z ⟨e.1,he⟩ else (0 : M.A e.1.2.1)) =
      (if he : e.1 ∈ candidates then y ⟨e.1,he⟩ else (0 : M.A e.1.2.1)) +
      (if he : e.1 ∈ candidates then z ⟨e.1,he⟩ else (0 : M.A e.1.2.1))
    by_cases he : e.1 ∈ candidates <;> simp [he]
  map_smul' t y := by
    apply Subtype.ext
    funext e
    change (if he : e.1 ∈ candidates then t • y ⟨e.1,he⟩ else (0 : M.A e.1.2.1)) =
      t • (if he : e.1 ∈ candidates then y ⟨e.1,he⟩ else (0 : M.A e.1.2.1))
    by_cases he : e.1 ∈ candidates <;> simp [he]

/-- Candidate restoration reads the same whole kernel at its same original edge name. -/
theorem candidate_value (y : CandidateValues M candidates) (e : candidates) :
    (candidateCochain (k := k) M P candidates houtside y).1 ⟨e.1,Set.mem_univ e.1⟩ = y e :=
  dif_pos e.2

/-- Candidate restoration vanishes on every noncandidate original edge. -/
theorem noncandidate_value (y : CandidateValues M candidates) (e : EdgeName (K := K))
    (he : e ∉ candidates) :
    (candidateCochain (k := k) M P candidates houtside y).1 ⟨e,Set.mem_univ e⟩ = 0 := dif_neg he

/-- Reading restored full candidate values is the identity on every original candidate. -/
theorem read_candidate (y : CandidateValues M candidates) :
    candidateRead (k := k) M P candidates (candidateCochain (k := k) M P candidates houtside y) = y := by
  funext e
  exact candidate_value (k := k) M P candidates houtside y e

/-- Mask only candidate values, retaining every original always-allowed correction. -/
def alwaysRead : C1P →ₗ[k] alwaysSpace (k := k) M P candidates where
  toFun h := ⟨⟨fun e => if e.1 ∈ candidates then 0 else h.1 e,by
    intro e hp
    change (if e.1 ∈ candidates then 0 else h.1 e) = 0
    by_cases he : e.1 ∈ candidates
    · exact if_pos he
    · rw [if_neg he]
      exact h.2 e hp⟩,by intro e; exact if_pos e.2⟩
  map_add' h j := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    change (if e.1 ∈ candidates then 0 else h.1 e + j.1 e) =
      (if e.1 ∈ candidates then 0 else h.1 e) + (if e.1 ∈ candidates then 0 else j.1 e)
    by_cases he : e.1 ∈ candidates <;> simp [he]
  map_smul' t h := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    change (if e.1 ∈ candidates then 0 else t • h.1 e) =
      t • (if e.1 ∈ candidates then 0 else h.1 e)
    by_cases he : e.1 ∈ candidates <;> simp [he]

/-- The two independently specified sources reconstruct every full original relative cochain. -/
theorem decompose (h : C1P) :
    (alwaysRead (k := k) M P candidates h).1 +
      candidateCochain (k := k) M P candidates houtside (candidateRead (k := k) M P candidates h) = h := by
  apply Subtype.ext
  funext e
  change (if e.1 ∈ candidates then 0 else h.1 e) +
    (if he : e.1 ∈ candidates then h.1 ⟨e.1,Set.mem_univ e.1⟩ else (0 : M.A e.1.2.1)) = h.1 e
  by_cases he : e.1 ∈ candidates <;> simp [he]

variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)

/-- The same original global differential on the complete always source. -/
def D : alwaysSpace (k := k) M P candidates →ₗ[k] C2P :=
  (differential1 M hlinear ClosedRegion.all P).comp (alwaysSpace (k := k) M P candidates).subtype

/-- The complete candidate differential uses the same original face paths. -/
def candidateMap : CandidateValues M candidates →ₗ[k] C2P :=
  (differential1 M hlinear ClosedRegion.all P).comp
    (candidateCochain (k := k) M P candidates houtside)

/-- The original differential is the sum of the always and complete candidate columns. -/
theorem differential_decompose (h : C1P) :
    D (k := k) M P candidates hlinear (alwaysRead (k := k) M P candidates h) +
      candidateMap (k := k) M P candidates houtside hlinear (candidateRead (k := k) M P candidates h) =
        differential1 M hlinear ClosedRegion.all P h := by
  change differential1 M hlinear ClosedRegion.all P _ +
    differential1 M hlinear ClosedRegion.all P _ = _
  rw [← map_add]
  exact congrArg (differential1 M hlinear ClosedRegion.all P)
    (decompose (k := k) M P candidates houtside h)

variable [DecidableEq (EdgeName (K := K))]

/-- The full original kernel column at one original candidate name. -/
def column (e : candidates) : M.A e.1.2.1 →ₗ[k] C2P :=
  (candidateMap (k := k) M P candidates houtside hlinear).comp
    (LinearMap.single k (fun e : candidates => M.A e.1.2.1) e)

variable [Fintype (EdgeName (K := K))]

/-- The literal finite sum of named full columns equals the complete candidate map. -/
theorem sum_columns :
    LinearMap.lsum k (fun e : candidates => M.A e.1.2.1) k
      (column (k := k) M P candidates houtside hlinear) =
        candidateMap (k := k) M P candidates houtside hlinear := by
  exact (LinearMap.lsum k (fun e : candidates => M.A e.1.2.1) k).apply_symm_apply
    (candidateMap (k := k) M P candidates houtside hlinear)

/-- The same global face differential is Dx plus every original named full column. -/
theorem differential_named_sum (h : C1P) :
    D (k := k) M P candidates hlinear (alwaysRead (k := k) M P candidates h) +
      ∑ e : candidates, column (k := k) M P candidates houtside hlinear e
        (candidateRead (k := k) M P candidates h e) = differential1 M hlinear ClosedRegion.all P h := by
  have hs := LinearMap.congr_fun (sum_columns (k := k) M P candidates houtside hlinear)
    (candidateRead (k := k) M P candidates h)
  simp only [LinearMap.lsum_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.proj_apply] at hs
  rw [hs]
  exact differential_decompose (k := k) M P candidates houtside hlinear h

end OriginalColumns
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
