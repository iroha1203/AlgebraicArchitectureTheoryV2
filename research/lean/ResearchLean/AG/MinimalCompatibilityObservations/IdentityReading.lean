import ResearchLean.AG.MinimalCompatibilityObservations.ProtocolFiniteSearch
import ResearchLean.AG.ProtocolHolonomy.IdentityG124Determining
import Formal.Util.AssertStandardAxioms

/-!
# G-128: G-124's component representatives as state observations

The selected vertices are literally G-124's representatives.  At each such
vertex we observe every point of the original finite fiber.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction
open AAT.AG.LocalSemanticReconstruction

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]

/-- The empty equation family used in the fixed identity-operation case. -/
def identityEmptyEquations (Q : FixedFDirectedMultigraph.{u, u}) :
    PathEquations Q where
  Index := PEmpty
  finiteIndex := inferInstance
  source := fun r => r.elim
  target := fun r => r.elim
  left := fun r => r.elim
  right := fun r => r.elim

/-- The original finite protocol input, with identity operations, no path
equations, and only the identity visible change. -/
def identityG128Input (Q : FixedFDirectedMultigraph.{u, u}) (K : Type u)
    [Finite Q.Vertex] [Finite Q.Edge] [Finite K] : FiniteProtocolInput Q :=
  identityFiniteProtocolInput Q K (identityEmptyEquations Q) ⊥ (by
    intro g hg r
    cases r)

/-- G-124's chosen representatives, paired with all original fiber points. -/
noncomputable def identityRepresentativeStates
    (Q : FixedFDirectedMultigraph.{u, u}) (K : Type u)
    [Finite Q.Vertex] [Finite K] :
    Finset (ProtocolStates (identityReversibleData Q K)) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  exact (CSFixedFDetermining.protocolRepresentativeSet Q).biUnion fun r =>
    Finset.univ.image fun x : K => (⟨r, x⟩ : ProtocolStates (identityReversibleData Q K))

omit [Finite Q.Edge] in
/-- Membership retains precisely the original G-124 representative and a
fiber point; no replacement root choice is introduced. -/
theorem mem_identityRepresentativeStates
    (r : Q.Vertex) (x : K) :
    (⟨r, x⟩ : ProtocolStates (identityReversibleData Q K)) ∈
      identityRepresentativeStates Q K ↔
      r ∈ CSFixedFDetermining.protocolRepresentativeSet Q := by
  classical
  simp [identityRepresentativeStates]

/-- A G-124 lift over the identity visible change becomes the same actual
fiberwise change in G-128's ambient group. -/
def identityAmbientOfLift
    (a : (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q)) :
    ambientChange (identityReversibleData Q K) ⊥ :=
  fiberPairToAmbient (identityReversibleData Q K) ⊥
    ⟨(1 : (⊥ : Subgroup (FixedFGraphAutomorphism Q))), a.fiber⟩

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
theorem identityAmbientOfLift_compatible
    (a : (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q)) :
    identityAmbientOfLift a ∈ compatibleChange (identityReversibleData Q K) ⊥ := by
  apply (fiberPair_compatible_iff (identityReversibleData Q K) ⊥
    ⟨(1 : (⊥ : Subgroup (FixedFGraphAutomorphism Q))), a.fiber⟩).2
  exact a.edge_naturality

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
/-- Every point evaluation of G-128's state action is the corresponding
G-124 permutation reading of the same original lift. -/
theorem identityAmbientOfLift_readAt
    (a : (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q))
    (r : Q.Vertex) (x : K) :
    (ambientStateAction (identityReversibleData Q K) ⊥).smul
        (identityAmbientOfLift a) ⟨r, x⟩ =
      ⟨r, (FinitePermutationReadingCriteria.readAt Q K 1
        (identityLiftEquivG124Preserving a) r) x⟩ := by
  rw [identityG124_readAt]
  rfl

/-- Convert an original table of permutations at G-124's representatives
into the pointwise state table required by C's actual extension search. -/
noncomputable def identityPointTable
    (tR : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} → Equiv.Perm K) :
    {p : ProtocolStates (identityReversibleData Q K) //
      p ∈ identityRepresentativeStates Q K} →
      ProtocolStates (identityReversibleData Q K) :=
  fun p => ⟨p.1.1,
    tR ⟨p.1.1, (mem_identityRepresentativeStates (K := K) p.1.1 p.1.2).mp p.2⟩ p.1.2⟩

omit [Finite Q.Edge] in
/-- Equality of the G-124 representative permutation table yields equality
with the exact state table submitted to C. -/
theorem identity_observe_eq_pointTable
    (a : (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q))
    (tR : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} → Equiv.Perm K)
    (h : ∀ r, FinitePermutationReadingCriteria.readAt Q K 1
      (identityLiftEquivG124Preserving a) r.1 = tR r) :
    letI := ambientStateAction (identityReversibleData Q K) ⊥
    observe (identityRepresentativeStates Q K) (identityAmbientOfLift a) =
      identityPointTable tR := by
  funext p
  rcases p with ⟨⟨r, x⟩, hr⟩
  let rr : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} :=
    ⟨r, (mem_identityRepresentativeStates (K := K) r x).mp hr⟩
  change (ambientStateAction (identityReversibleData Q K) ⊥).smul
      (identityAmbientOfLift a) ⟨r, x⟩ = ⟨r, tR rr x⟩
  rw [identityAmbientOfLift_readAt, h rr]

/-- Every G-124 edge-coherent representative table has a successful run
of C's actual compatible-extension search on the original identity protocol. -/
theorem identityCompatibleSearch_exists [Nontrivial K]
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge] [DecidableEq K]
    (tR : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} → Equiv.Perm K)
    (hcoh : FinitePermutationReadingCriteria.EdgeCoherent Q K
      (CSFixedFDetermining.protocolRepresentativeSet Q) tR)
    (visible : ExplicitEnumeration (identityG128Input Q K).H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration ((identityG128Input Q K).data.Fiber v)) :
    ∃ b : ambientChange (identityReversibleData Q K) ⊥,
      protocolStateCompatibleExtension (identityG128Input Q K)
        visible vertices edges fibers
        (identityRepresentativeStates Q K) (identityPointTable tR) = some b := by
  classical
  obtain ⟨a, ha⟩ :=
    (identityLift_representatives_determining (Q := Q) (K := K) 1).2 tR hcoh
  have hobs := identity_observe_eq_pointTable a tR (by
    intro r
    exact congrFun ha r)
  have hne : protocolStateCompatibleExtension (identityG128Input Q K)
        visible vertices edges fibers
        (identityRepresentativeStates Q K) (identityPointTable tR) ≠ none := by
    intro hn
    have hall := (protocolStateCompatibleExtension_none_iff
      (identityG128Input Q K) visible vertices edges fibers
      (identityRepresentativeStates Q K) (identityPointTable tR)).mp hn
    exact hall ⟨identityAmbientOfLift a,
      identityAmbientOfLift_compatible a, hobs⟩
  cases hsearch : protocolStateCompatibleExtension (identityG128Input Q K)
      visible vertices edges fibers
      (identityRepresentativeStates Q K) (identityPointTable tR) with
  | none => exact (hne hsearch).elim
  | some b => exact ⟨b, rfl⟩

/-- Reinterpret a compatible fiberwise pair over the sole visible identity
as the original G-127 lift. -/
noncomputable def identityLiftOfCompatiblePair
    (p : AmbientFiberPair (identityReversibleData Q K) ⊥)
    (hp : fiberPairToAmbient (identityReversibleData Q K) ⊥ p ∈
      compatibleChange (identityReversibleData Q K) ⊥) :
    (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q) := by
  rcases p with ⟨u, f⟩
  have hu : u = 1 := Subsingleton.elim _ _
  subst u
  exact ⟨f, (fiberPair_compatible_iff
    (identityReversibleData Q K) ⊥ ⟨1, f⟩).mp hp⟩

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
theorem identityLiftOfCompatiblePair_state
    (p : AmbientFiberPair (identityReversibleData Q K) ⊥)
    (hp : fiberPairToAmbient (identityReversibleData Q K) ⊥ p ∈
      compatibleChange (identityReversibleData Q K) ⊥)
    (v : Q.Vertex) (x : K) :
    (ambientStateAction (identityReversibleData Q K) ⊥).smul
        (fiberPairToAmbient (identityReversibleData Q K) ⊥ p) ⟨v, x⟩ =
      ⟨v, (identityLiftOfCompatiblePair p hp).fiber v x⟩ := by
  rcases p with ⟨u, f⟩
  have hu : u = 1 := Subsingleton.elim _ _
  subst u
  rfl

/-- An E1-compatible ambient change over the sole visible identity is an
original G-127 identity lift, using its actual vertexwise fiber maps. -/
noncomputable def identityLiftOfCompatible
    (b : ambientChange (identityReversibleData Q K) ⊥)
    (hb : b ∈ compatibleChange (identityReversibleData Q K) ⊥) :
    (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q) := by
  let p := ambientEquivFiberPair (identityReversibleData Q K) ⊥ b
  have hp : fiberPairToAmbient (identityReversibleData Q K) ⊥ p = b :=
    (ambientEquivFiberPair (identityReversibleData Q K) ⊥).left_inv b
  exact identityLiftOfCompatiblePair p (by rw [hp]; exact hb)

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
/-- The recovered lift acts at every original state exactly as the ambient
change returned by C. -/
theorem identityLiftOfCompatible_state
    (b : ambientChange (identityReversibleData Q K) ⊥)
    (hb : b ∈ compatibleChange (identityReversibleData Q K) ⊥)
    (v : Q.Vertex) (x : K) :
    (ambientStateAction (identityReversibleData Q K) ⊥).smul b ⟨v, x⟩ =
      ⟨v, (identityLiftOfCompatible b hb).fiber v x⟩ := by
  let D := identityReversibleData Q K
  let p := ambientEquivFiberPair D ⊥ b
  have hp : fiberPairToAmbient D ⊥ p = b :=
    (ambientEquivFiberPair D ⊥).left_inv b
  let hc : fiberPairToAmbient D ⊥ p ∈ compatibleChange D ⊥ := by
    rw [hp]
    exact hb
  have hs := identityLiftOfCompatiblePair_state p hc v x
  calc
    (ambientStateAction D ⊥).smul b ⟨v, x⟩ =
        (ambientStateAction D ⊥).smul (fiberPairToAmbient D ⊥ p) ⟨v, x⟩ := by
          rw [hp]
    _ = ⟨v, (identityLiftOfCompatible b hb).fiber v x⟩ := hs

/-- The actual C result reads as exactly the submitted G-124 permutation
table at every original component representative. -/
theorem identityCompatibleSearch_readAt
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge] [DecidableEq K]
    (tR : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} → Equiv.Perm K)
    (visible : ExplicitEnumeration (identityG128Input Q K).H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration ((identityG128Input Q K).data.Fiber v))
    (b : ambientChange (identityReversibleData Q K) ⊥)
    (hsearch : protocolStateCompatibleExtension (identityG128Input Q K)
      visible vertices edges fibers
      (identityRepresentativeStates Q K) (identityPointTable tR) = some b) :
    ∃ hb : b ∈ compatibleChange (identityReversibleData Q K) ⊥,
      ∀ r, FinitePermutationReadingCriteria.readAt Q K 1
        (identityLiftEquivG124Preserving
          (identityLiftOfCompatible b hb)) r.1 = tR r := by
  obtain ⟨ht, hb⟩ := protocolStateCompatibleExtension_some
    (identityG128Input Q K) visible vertices edges fibers
    (identityRepresentativeStates Q K) (identityPointTable tR) b hsearch
  refine ⟨hb, ?_⟩
  intro r
  apply Equiv.ext
  intro x
  rw [identityG124_readAt]
  have hmem : (⟨r.1, x⟩ : ProtocolStates (identityReversibleData Q K)) ∈
      identityRepresentativeStates Q K :=
    (mem_identityRepresentativeStates (K := K) r.1 x).2 r.2
  have hx := congrFun ht ⟨⟨r.1, x⟩, hmem⟩
  change (ambientStateAction (identityReversibleData Q K) ⊥).smul
      b ⟨r.1, x⟩ = ⟨r.1, tR r x⟩ at hx
  rw [identityLiftOfCompatible_state b hb] at hx
  exact eq_of_heq (Sigma.mk.inj_iff.mp hx).2

/-- G-124's existing separation theorem makes C's returned lift the unique
extension of the submitted representative table. -/
theorem identityCompatibleSearch_unique [Nontrivial K]
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge] [DecidableEq K]
    (tR : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} → Equiv.Perm K)
    (visible : ExplicitEnumeration (identityG128Input Q K).H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration ((identityG128Input Q K).data.Fiber v))
    (a : (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q))
    (ha : ∀ r, FinitePermutationReadingCriteria.readAt Q K 1
      (identityLiftEquivG124Preserving a) r.1 = tR r)
    (b : ambientChange (identityReversibleData Q K) ⊥)
    (hsearch : protocolStateCompatibleExtension (identityG128Input Q K)
      visible vertices edges fibers
      (identityRepresentativeStates Q K) (identityPointTable tR) = some b) :
    ∃ hb : b ∈ compatibleChange (identityReversibleData Q K) ⊥,
      identityLiftOfCompatible b hb = a := by
  obtain ⟨hb, hread⟩ := identityCompatibleSearch_readAt
    tR visible vertices edges fibers b hsearch
  refine ⟨hb, ?_⟩
  apply (identityLift_representatives_determining (Q := Q) (K := K) 1).1
  funext r
  apply Equiv.ext
  intro x
  have hleft := congrArg (fun p : Equiv.Perm K => p x) (hread r)
  have hright := congrArg (fun p : Equiv.Perm K => p x) (ha r)
  simpa only [FiniteReading.restrict, identityG124_readAt] using
    hleft.trans hright.symm

/-- At every vertex, C's returned state map is the original G-124
extension and the original G-127 (C2) root reconstruction. -/
theorem identityCompatibleSearch_C2 [Nontrivial K]
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge] [DecidableEq K]
    (tR : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} → Equiv.Perm K)
    (visible : ExplicitEnumeration (identityG128Input Q K).H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration ((identityG128Input Q K).data.Fiber v))
    (a : (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q))
    (ha : ∀ r, FinitePermutationReadingCriteria.readAt Q K 1
      (identityLiftEquivG124Preserving a) r.1 = tR r)
    (b : ambientChange (identityReversibleData Q K) ⊥)
    (hsearch : protocolStateCompatibleExtension (identityG128Input Q K)
      visible vertices edges fibers
      (identityRepresentativeStates Q K) (identityPointTable tR) = some b) :
    let α := FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
      (identityLiftEquivG124Preserving a)
    ∀ v : Q.Vertex, ∀ x : K,
      (ambientStateAction (identityReversibleData Q K) ⊥).smul b ⟨v, x⟩ =
        ⟨v, ((identityComponentRootSolutions
          (g := (1 : FixedFGraphAutomorphism Q)) α).reconstructedFiber
            (identityReversibleData Q K) (g124RepresentativeRootedPaths Q) v) x⟩ := by
  obtain ⟨hb, hba⟩ := identityCompatibleSearch_unique
    tR visible vertices edges fibers a ha b hsearch
  intro α v x
  have hα :
      ((FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies).symm
        α) =
        identityLiftEquivG124Preserving a :=
    Equiv.symm_apply_apply
      FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
      (identityLiftEquivG124Preserving a)
  have hc2 := identity_G124_C2_extension_agree
    (g := (1 : FixedFGraphAutomorphism Q)) α v
  rw [hα, identityG124_readAt] at hc2
  rw [identityLiftOfCompatible_state b hb, hba]
  exact congrArg (fun p : Equiv.Perm K => (⟨v, p x⟩ :
    ProtocolStates (identityReversibleData Q K))) hc2

/-- The original G-124 edge-coherence predicate is exactly the success
condition of C's compatible-extension search on the same representative
state table. -/
theorem identityCompatibleSearch_iff_edgeCoherent [Nontrivial K]
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge] [DecidableEq K]
    (tR : {r : Q.Vertex // r ∈
      CSFixedFDetermining.protocolRepresentativeSet Q} → Equiv.Perm K)
    (visible : ExplicitEnumeration (identityG128Input Q K).H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration ((identityG128Input Q K).data.Fiber v)) :
    (∃ b : ambientChange (identityReversibleData Q K) ⊥,
      protocolStateCompatibleExtension (identityG128Input Q K)
        visible vertices edges fibers
        (identityRepresentativeStates Q K) (identityPointTable tR) = some b) ↔
      FinitePermutationReadingCriteria.EdgeCoherent Q K
        (CSFixedFDetermining.protocolRepresentativeSet Q) tR := by
  constructor
  · rintro ⟨b, hsearch⟩
    obtain ⟨hb, hread⟩ := identityCompatibleSearch_readAt
      tR visible vertices edges fibers b hsearch
    intro e
    let l := identityLiftOfCompatible b hb
    have hs := hread ⟨Q.source e.1, e.2.1⟩
    have ht := hread ⟨Q.target e.1, e.2.2⟩
    change l.fiber (Q.source e.1) = tR ⟨Q.source e.1, e.2.1⟩ at hs
    change l.fiber (Q.target e.1) = tR ⟨Q.target e.1, e.2.2⟩ at ht
    change tR ⟨Q.source e.1, e.2.1⟩ =
      tR ⟨Q.target e.1, e.2.2⟩
    rw [← hs, ← ht]
    exact (identityLiftToG124Family l).edge_constant e.1
  · intro hcoh
    exact identityCompatibleSearch_exists tR hcoh visible vertices edges fibers

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations

end AAT.AG.MinimalCompatibilityObservations
