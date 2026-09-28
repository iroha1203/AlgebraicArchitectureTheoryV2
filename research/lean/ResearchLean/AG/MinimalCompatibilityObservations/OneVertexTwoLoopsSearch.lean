import ResearchLean.AG.MinimalCompatibilityObservations.OneVertexTwoLoopsGroup
import ResearchLean.AG.MinimalCompatibilityObservations.ProtocolFiniteSearch
import Formal.Util.AssertStandardAxioms

/-!
# G-128: observation and finite search on the original two-loop protocol

The original primitive input and its execution enumerations are used throughout.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction

instance : (v : oneLoopGraph.Vertex) →
    DecidableEq (oneLoopInput.data.Fiber v) := by
  intro v
  change DecidableEq Bool
  infer_instance

/-- Both members of the actual visible group, in identity/name-swap order. -/
def oneLoopVisible : ExplicitEnumeration oneLoopInput.H where
  values := [1, ⟨oneLoopSwap, oneLoopSwap_mem_H⟩]
  complete := by
    intro g
    rcases oneLoop_H_exact g with h | h
    · have : g = 1 := Subtype.ext h
      simp [this]
    · have : g = (⟨oneLoopSwap, oneLoopSwap_mem_H⟩ : oneLoopInput.H) :=
        Subtype.ext h
      simp [this]

/-- An actual ambient change swapping the names and fixing each state. -/
def oneLoopEdgeSwapAmbient : ambientChange oneLoopData oneLoopInput.H :=
  fiberPairToAmbient oneLoopData oneLoopInput.H
    ⟨⟨oneLoopSwap, oneLoopSwap_mem_H⟩,
      fun v => by cases v; exact Equiv.refl Bool⟩

theorem oneLoopEdgeSwap_incompatible :
    oneLoopEdgeSwapAmbient ∉ compatibleChange oneLoopData oneLoopInput.H := by
  intro h
  have hv := (oneLoop_compatible_iff_first_one oneLoopEdgeSwapAmbient).mp h
  have hs : (⟨oneLoopSwap, oneLoopSwap_mem_H⟩ : oneLoopInput.H) = 1 :=
    oneLoopHEquivPermBool.injective (by
      change oneLoopHEquivPermBool
        (⟨oneLoopSwap, oneLoopSwap_mem_H⟩ : oneLoopInput.H) = 1
      simpa only [oneLoopAmbientEquiv_first] using hv)
  exact oneLoopSwap_ne_one (congrArg Subtype.val hs)

theorem oneLoopEdgeSwap_fixes_state (p : ProtocolStates oneLoopData) :
    (ambientStateAction oneLoopData oneLoopInput.H).smul
      oneLoopEdgeSwapAmbient p = p := by
  rcases p with ⟨v, x⟩
  cases v
  rfl

/-- The original C minimum search fails on states, and its scan yields a
specific incompatible all-state fixer, with both A and B costs infinite. -/
theorem oneLoop_state_search_infinite :
    letI := ambientStateAction oneLoopData oneLoopInput.H
    protocolStateMinimum oneLoopInput oneLoopVisible oneLoopVertices
      oneLoopEdges oneLoopFibers = none ∧
    ∃ k : ambientChange oneLoopData oneLoopInput.H,
      protocolStateIncompatibleFixer oneLoopInput oneLoopVisible oneLoopVertices
        oneLoopEdges oneLoopFibers = some k ∧
      k ∉ compatibleChange oneLoopData oneLoopInput.H ∧
      (∀ p : ProtocolStates oneLoopData,
        (ambientStateAction oneLoopData oneLoopInput.H).smul k p = p) ∧
      minObservations (X := ProtocolStates oneLoopData)
        (compatibleChange oneLoopData oneLoopInput.H) = ⊤ ∧
      optimalQueries (X := ProtocolStates oneLoopData)
        (compatibleChange oneLoopData oneLoopInput.H) = ⊤ := by
  letI := ambientStateAction oneLoopData oneLoopInput.H
  have hno : ¬ ∃ B : Finset (ProtocolStates oneLoopData),
      Sufficient (compatibleChange oneLoopData oneLoopInput.H) B := by
    rintro ⟨B, hB⟩
    exact oneLoopEdgeSwap_incompatible
      (hB (by
        intro x hx
        exact oneLoopEdgeSwap_fixes_state x))
  have hm := (protocolStateMinimum_none_iff oneLoopInput oneLoopVisible
    oneLoopVertices oneLoopEdges oneLoopFibers).2 hno
  exact ⟨hm, protocolStateMinimum_none_witness oneLoopInput oneLoopVisible
    oneLoopVertices oneLoopEdges oneLoopFibers hm⟩

/-- An edge-name permutation fixing the first named loop is the identity. -/
private theorem oneLoop_visible_one_of_fixed_false (u : oneLoopInput.H)
    (h : u.1.edge false = false) : u = 1 := by
  rcases oneLoop_H_exact u with hone | hswap
  · exact Subtype.ext hone
  · have hh := congrArg (fun g : FixedFGraphAutomorphism oneLoopGraph =>
        g.edge false) hswap
    change u.1.edge false = true at hh
    rw [h] at hh
    cases hh

private theorem oneLoop_bool_perm_one_of_fixed_false (p : Equiv.Perm Bool)
    (h : p false = false) : p = 1 := by
  apply Equiv.ext
  intro x
  cases x with
  | false => simpa using h
  | true =>
      have hne : p true ≠ false := by
        intro hp
        have he := p.injective (hp.trans h.symm)
        cases he
      cases hp : p true <;> simp_all

/-- The second independent ambient generator: it fixes names and swaps states. -/
def oneLoopFiberSwapAmbient : ambientChange oneLoopData oneLoopInput.H :=
  fiberPairToAmbient oneLoopData oneLoopInput.H
    ⟨1, fun v => by cases v; exact Equiv.swap false true⟩

private theorem oneLoopEdgeSwap_ne_one : oneLoopEdgeSwapAmbient ≠ 1 := by
  intro h
  exact oneLoopEdgeSwap_incompatible (h ▸ (compatibleChange oneLoopData oneLoopInput.H).one_mem)

private theorem oneLoopFiberSwap_ne_one : oneLoopFiberSwapAmbient ≠ 1 := by
  intro h
  have hp := congrArg (fun a : ambientChange oneLoopData oneLoopInput.H =>
    (ambientStateAction oneLoopData oneLoopInput.H).smul a
      (⟨PUnit.unit, false⟩ : ProtocolStates oneLoopData)) h
  change (⟨PUnit.unit, true⟩ : ProtocolStates oneLoopData) =
    ⟨PUnit.unit, false⟩ at hp
  cases hp

private theorem oneLoopEdgeSwap_fixes_full_state (p : ProtocolStates oneLoopData) :
    (ambientFullAction oneLoopData oneLoopInput.H).smul
      oneLoopEdgeSwapAmbient (Sum.inr (Sum.inr p)) =
        Sum.inr (Sum.inr p) := by
  simpa only [ambientFullAction] using congrArg (fun q => Sum.inr (Sum.inr q))
    (oneLoopEdgeSwap_fixes_state p)

/-- A name observation and a state observation identify every ambient change. -/
theorem oneLoop_edge_state_sufficient_bot :
    letI := ambientFullAction oneLoopData oneLoopInput.H
    Sufficient (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H))
      ({Sum.inr (Sum.inl false), Sum.inr (Sum.inr ⟨PUnit.unit, false⟩)} :
        Finset (ProtocolFullPoints oneLoopData)) := by
  letI := ambientFullAction oneLoopData oneLoopInput.H
  intro a ha
  have he := ha (Sum.inr (Sum.inl false)) (by simp)
  have hs := ha (Sum.inr (Sum.inr (⟨PUnit.unit, false⟩ :
    ProtocolStates oneLoopData))) (by simp)
  have hfalse : a.1.1.1.edge false = false := by
    change (Sum.inr (Sum.inl (a.1.1.1.edge false)) :
      ProtocolFullPoints oneLoopData) = Sum.inr (Sum.inl false) at he
    exact Sum.inl.inj (Sum.inr.inj he)
  have hv : a.1.1 = 1 := oneLoop_visible_one_of_fixed_false a.1.1 hfalse
  have hstate : a.1.2 ⟨PUnit.unit, false⟩ =
      (⟨PUnit.unit, false⟩ : ProtocolStates oneLoopData) := by
    change (Sum.inr (Sum.inr (a.1.2 ⟨PUnit.unit, false⟩)) :
      ProtocolFullPoints oneLoopData) = _ at hs
    exact Sum.inr.inj (Sum.inr.inj hs)
  have hsecond : (oneLoopAmbientEquiv a).2 false = false := by
    rw [ambientState_eq_mk oneLoopData oneLoopInput.H] at hstate
    have hf : ambientFiberTo oneLoopData oneLoopInput.H a PUnit.unit false =
        false := by
      have hvtx : a.1.1.1.vertex PUnit.unit = PUnit.unit := by
        cases a.1.1.1.vertex PUnit.unit
        rfl
      rw [hvtx] at hstate
      exact eq_of_heq (Sigma.mk.inj_iff.mp hstate).2
    simpa only [oneLoopAmbientEquiv_second, ambientEquivFiberPair,
      ambientFiberEquiv] using hf
  have hsecondOne : (oneLoopAmbientEquiv a).2 = 1 :=
    oneLoop_bool_perm_one_of_fixed_false _ hsecond
  have hfirst : (oneLoopAmbientEquiv a).1 = 1 := by
    simp [oneLoopAmbientEquiv_first, hv]
  have hone : a = 1 := oneLoopAmbientEquiv.injective (by
    apply Prod.ext
    · simpa using hfirst
    · simpa using hsecondOne)
  exact Subgroup.mem_bot.mpr hone

private theorem oneLoop_second_one_of_all_state_fixed
    (a : ambientChange oneLoopData oneLoopInput.H)
    (hfix : ∀ p : ProtocolStates oneLoopData,
      (ambientStateAction oneLoopData oneLoopInput.H).smul a p = p) :
    (oneLoopAmbientEquiv a).2 = 1 := by
  have hstate := hfix ⟨PUnit.unit, false⟩
  have hf : ambientFiberTo oneLoopData oneLoopInput.H a PUnit.unit false =
      false := by
    change a.1.2 ⟨PUnit.unit, false⟩ =
      (⟨PUnit.unit, false⟩ : ProtocolStates oneLoopData) at hstate
    rw [ambientState_eq_mk oneLoopData oneLoopInput.H] at hstate
    have hvtx : a.1.1.1.vertex PUnit.unit = PUnit.unit := by
      cases a.1.1.1.vertex PUnit.unit
      rfl
    rw [hvtx] at hstate
    exact eq_of_heq (Sigma.mk.inj_iff.mp hstate).2
  have hsecond : (oneLoopAmbientEquiv a).2 false = false := by
    simpa only [oneLoopAmbientEquiv_second, ambientEquivFiberPair,
      ambientFiberEquiv] using hf
  exact oneLoop_bool_perm_one_of_fixed_false _ hsecond

/-- An incompatible change invisible at every state is uniquely the
original edge-name swap with identity state action. -/
theorem oneLoop_state_invisible_unique
    (a : ambientChange oneLoopData oneLoopInput.H)
    (ha : a ∉ compatibleChange oneLoopData oneLoopInput.H)
    (hfix : ∀ p : ProtocolStates oneLoopData,
      (ambientStateAction oneLoopData oneLoopInput.H).smul a p = p) :
    a = oneLoopEdgeSwapAmbient := by
  have hvisible : a.1.1.1 = oneLoopSwap := by
    rcases oneLoop_H_exact a.1.1 with h | h
    · have hv : (oneLoopAmbientEquiv a).1 = 1 := by
        have hu : a.1.1 = 1 := Subtype.ext h
        simp [oneLoopAmbientEquiv_first, hu]
      exact (ha ((oneLoop_compatible_iff_first_one a).2 hv)).elim
    · exact h
  have hfirst : (oneLoopAmbientEquiv a).1 =
      (oneLoopAmbientEquiv oneLoopEdgeSwapAmbient).1 := by
    simp only [oneLoopAmbientEquiv_first]
    apply congrArg oneLoopHEquivPermBool
    exact Subtype.ext hvisible
  have hsecond := oneLoop_second_one_of_all_state_fixed a hfix
  have hedgeSecond := oneLoop_second_one_of_all_state_fixed
    oneLoopEdgeSwapAmbient oneLoopEdgeSwap_fixes_state
  apply oneLoopAmbientEquiv.injective
  apply Prod.ext
  · exact hfirst
  · rw [hsecond, hedgeSecond]

set_option maxHeartbeats 1000000 in
/-- The exact C state-only outcome is the original incompatible name swap,
both through exhaustive minimum/witness search and through greedy cover. -/
theorem oneLoop_state_C_outputs :
    protocolStateIncompatibleFixer oneLoopInput oneLoopVisible oneLoopVertices
      oneLoopEdges oneLoopFibers = some oneLoopEdgeSwapAmbient ∧
    protocolStateMinimumOrWitness oneLoopInput oneLoopVisible oneLoopVertices
      oneLoopEdges oneLoopFibers = Sum.inr oneLoopEdgeSwapAmbient ∧
    protocolStateGreedy oneLoopInput oneLoopVisible oneLoopVertices
      oneLoopEdges oneLoopFibers = Sum.inr oneLoopEdgeSwapAmbient := by
  obtain ⟨hm, k, hk, hbad, hfix, _, _⟩ := oneLoop_state_search_infinite
  have hunique : k = oneLoopEdgeSwapAmbient :=
    oneLoop_state_invisible_unique k hbad hfix
  have hscan : protocolStateIncompatibleFixer oneLoopInput oneLoopVisible
      oneLoopVertices oneLoopEdges oneLoopFibers = some oneLoopEdgeSwapAmbient := by
    simpa [hunique] using hk
  have hwitness : protocolStateMinimumOrWitness oneLoopInput oneLoopVisible
      oneLoopVertices oneLoopEdges oneLoopFibers =
      Sum.inr oneLoopEdgeSwapAmbient := by
    simp only [protocolStateMinimumOrWitness, hm, hscan,
      Option.getD_some]
  have hgreedy : protocolStateGreedy oneLoopInput oneLoopVisible oneLoopVertices
      oneLoopEdges oneLoopFibers = Sum.inr oneLoopEdgeSwapAmbient := by
    have hs := protocolStateGreedy_correct oneLoopInput oneLoopVisible
      oneLoopVertices oneLoopEdges oneLoopFibers
    cases hg : protocolStateGreedy oneLoopInput oneLoopVisible oneLoopVertices
        oneLoopEdges oneLoopFibers with
    | inl B =>
        rw [hg] at hs
        have hno := (protocolStateMinimum_none_iff oneLoopInput oneLoopVisible
          oneLoopVertices oneLoopEdges oneLoopFibers).1 hm
        exact (hno ⟨B, hs⟩).elim
    | inr j =>
        rw [hg] at hs
        have hj : j ∉ compatibleChange oneLoopData oneLoopInput.H ∧
            ∀ p : ProtocolStates oneLoopData,
              (ambientStateAction oneLoopData oneLoopInput.H).smul j p = p := by
          exact hs
        rw [oneLoop_state_invisible_unique j hj.1 hj.2]
  exact ⟨hscan, hwitness, hgreedy⟩

/-- The first named edge alone decides compatibility in the actual full
action, since compatibility is exactly identity in the visible factor. -/
theorem oneLoop_edge_sufficient :
    letI := ambientFullAction oneLoopData oneLoopInput.H
    Sufficient (compatibleChange oneLoopData oneLoopInput.H)
      ({Sum.inr (Sum.inl false)} : Finset (ProtocolFullPoints oneLoopData)) := by
  letI := ambientFullAction oneLoopData oneLoopInput.H
  intro a ha
  have he := ha (Sum.inr (Sum.inl false)) (by simp)
  have hfalse : a.1.1.1.edge false = false := by
    change (Sum.inr (Sum.inl (a.1.1.1.edge false)) :
      ProtocolFullPoints oneLoopData) = Sum.inr (Sum.inl false) at he
    exact Sum.inl.inj (Sum.inr.inj he)
  have hv : a.1.1 = 1 := oneLoop_visible_one_of_fixed_false a.1.1 hfalse
  exact (oneLoop_compatible_iff_first_one a).2 (by
    simp [oneLoopAmbientEquiv_first, hv])

/-- A single named-edge point is necessary and sufficient for compatibility;
the actual full minimum search returns a singleton and B has value one. -/
theorem oneLoop_full_compatible_search_one :
    letI := ambientFullAction oneLoopData oneLoopInput.H
    minObservations (X := ProtocolFullPoints oneLoopData)
      (compatibleChange oneLoopData oneLoopInput.H) = 1 ∧
    optimalQueries (X := ProtocolFullPoints oneLoopData)
      (compatibleChange oneLoopData oneLoopInput.H) = 1 ∧
    ∃ B : Finset (ProtocolFullPoints oneLoopData),
      protocolFullMinimum oneLoopInput oneLoopVisible oneLoopVertices
        oneLoopEdges oneLoopFibers = some B ∧ B.card = 1 := by
  letI := ambientFullAction oneLoopData oneLoopInput.H
  have hle := minObservations_le
    (compatibleChange oneLoopData oneLoopInput.H)
    ({Sum.inr (Sum.inl false)} : Finset (ProtocolFullPoints oneLoopData))
    oneLoop_edge_sufficient
  have hne : compatibleChange oneLoopData oneLoopInput.H ≠ ⊤ := by
    intro htop
    exact oneLoopEdgeSwap_incompatible (by rw [htop]; trivial)
  have hzero : minObservations (X := ProtocolFullPoints oneLoopData)
      (compatibleChange oneLoopData oneLoopInput.H) ≠ 0 := by
    intro h
    exact hne ((minObservations_eq_zero_iff _).mp h)
  have hmin : minObservations (X := ProtocolFullPoints oneLoopData)
      (compatibleChange oneLoopData oneLoopInput.H) = 1 := by
    have hle1 : minObservations (X := ProtocolFullPoints oneLoopData)
        (compatibleChange oneLoopData oneLoopInput.H) ≤ 1 := by
      simpa using hle
    apply le_antisymm hle1
    by_contra h
    have hz : minObservations (X := ProtocolFullPoints oneLoopData)
        (compatibleChange oneLoopData oneLoopInput.H) = 0 := by
      have hlt : minObservations (X := ProtocolFullPoints oneLoopData)
          (compatibleChange oneLoopData oneLoopInput.H) < 1 := lt_of_not_ge h
      exact ENat.lt_one_iff_eq_zero.mp hlt
    exact hzero hz
  obtain ⟨B, hB⟩ := protocolFullMinimum_success oneLoopInput oneLoopVisible
    oneLoopVertices oneLoopEdges oneLoopFibers
  have hc := protocolFullMinimum_card oneLoopInput oneLoopVisible
    oneLoopVertices oneLoopEdges oneLoopFibers B hB
  have hcard : B.card = 1 := by exact_mod_cast hc.trans hmin
  exact ⟨hmin, by rw [optimalQueries_eq_minObservations, hmin],
    B, hB, hcard⟩

/-- A sufficient full observation for all ambient changes must include at
least one edge and one state point. -/
theorem oneLoop_full_bot_two_le_card
    (B : Finset (ProtocolFullPoints oneLoopData))
    (hB : letI := ambientFullAction oneLoopData oneLoopInput.H
      Sufficient (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) B) :
    2 ≤ B.card := by
  letI := ambientFullAction oneLoopData oneLoopInput.H
  have hEdge : ∃ x ∈ B,
      (ambientFullAction oneLoopData oneLoopInput.H).smul
        oneLoopEdgeSwapAmbient x ≠ x := by
    by_contra hn
    push_neg at hn
    have hone : oneLoopEdgeSwapAmbient = 1 :=
      Subgroup.mem_bot.mp (hB (by intro x hx; exact hn x hx))
    exact oneLoopEdgeSwap_ne_one hone
  have hFiber : ∃ y ∈ B,
      (ambientFullAction oneLoopData oneLoopInput.H).smul
        oneLoopFiberSwapAmbient y ≠ y := by
    by_contra hn
    push_neg at hn
    have hone : oneLoopFiberSwapAmbient = 1 :=
      Subgroup.mem_bot.mp (hB (by intro y hy; exact hn y hy))
    exact oneLoopFiberSwap_ne_one hone
  obtain ⟨x, hx, hxm⟩ := hEdge
  obtain ⟨y, hy, hym⟩ := hFiber
  have hxEdge : ∃ e : Bool, x = Sum.inr (Sum.inl e) := by
    rcases x with v | e | p
    · exact False.elim (hxm (by cases v; rfl))
    · exact ⟨e, rfl⟩
    · exact False.elim (hxm (oneLoopEdgeSwap_fixes_full_state p))
  have hyState : ∃ p : ProtocolStates oneLoopData,
      y = Sum.inr (Sum.inr p) := by
    rcases y with v | e | p
    · exact False.elim (hym (by cases v; rfl))
    · exact False.elim (hym (by cases e <;> rfl))
    · exact ⟨p, rfl⟩
  by_contra hcard
  have hle : B.card ≤ 1 := by omega
  have hxy := (Finset.card_le_one.mp hle) x hx y hy
  obtain ⟨e, he⟩ := hxEdge
  obtain ⟨p, hp⟩ := hyState
  rw [he, hp] at hxy
  cases hxy

/-- C's exhaustive all-change search uses the identical primitive ambient
table and full-point order, but tests against the trivial subgroup. -/
def oneLoopFullBotMinimum : Option (Finset (ProtocolFullPoints oneLoopData)) := by
  letI : DecidableEq (ambientChange oneLoopData oneLoopInput.H) :=
    ambientDecidableEq oneLoopData oneLoopInput.H oneLoopVertices
      oneLoopEdges oneLoopFibers
  letI : DecidablePred (· ∈ (⊥ : Subgroup
      (ambientChange oneLoopData oneLoopInput.H))) := by
    intro a
    exact decidable_of_iff (a = 1) (by simp)
  letI : MulAction (ambientChange oneLoopData oneLoopInput.H)
      (ProtocolFullPoints oneLoopData) :=
    ambientFullAction oneLoopData oneLoopInput.H
  exact minimumObservation (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H))
    (FiniteProtocolInput.ambientTable oneLoopInput oneLoopVisible
      oneLoopVertices oneLoopFibers)
    (allProtocolFullPoints oneLoopData oneLoopVertices
      oneLoopEdges oneLoopFibers)

/-- The same all-change table passed to C's greedy cover algorithm. -/
def oneLoopFullBotGreedy : Finset (ProtocolFullPoints oneLoopData) ⊕
    ambientChange oneLoopData oneLoopInput.H := by
  letI : DecidableEq (ambientChange oneLoopData oneLoopInput.H) :=
    ambientDecidableEq oneLoopData oneLoopInput.H oneLoopVertices
      oneLoopEdges oneLoopFibers
  letI : DecidablePred (· ∈ (⊥ : Subgroup
      (ambientChange oneLoopData oneLoopInput.H))) := by
    intro a
    exact decidable_of_iff (a = 1) (by simp)
  letI : MulAction (ambientChange oneLoopData oneLoopInput.H)
      (ProtocolFullPoints oneLoopData) :=
    ambientFullAction oneLoopData oneLoopInput.H
  exact greedyObservationSet
    (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H))
    (FiniteProtocolInput.ambientTable oneLoopInput oneLoopVisible
      oneLoopVertices oneLoopFibers)
    (allProtocolFullPoints oneLoopData oneLoopVertices
      oneLoopEdges oneLoopFibers)

/-- The same input has all-change minimum two; C returns a two-point set,
and B's optimal stopping query count is two. -/
theorem oneLoop_full_bot_search_two :
    letI := ambientFullAction oneLoopData oneLoopInput.H
    minObservations (X := ProtocolFullPoints oneLoopData)
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) = 2 ∧
    optimalQueries (X := ProtocolFullPoints oneLoopData)
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) = 2 ∧
    ∃ B : Finset (ProtocolFullPoints oneLoopData),
      oneLoopFullBotMinimum = some B ∧ B.card = 2 := by
  letI := ambientFullAction oneLoopData oneLoopInput.H
  let B₀ : Finset (ProtocolFullPoints oneLoopData) :=
    {Sum.inr (Sum.inl false), Sum.inr (Sum.inr ⟨PUnit.unit, false⟩)}
  have hB₀ : Sufficient
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) B₀ :=
    oneLoop_edge_state_sufficient_bot
  have hle : minObservations (X := ProtocolFullPoints oneLoopData)
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) ≤ 2 := by
    have h := minObservations_le
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) B₀ hB₀
    simpa [B₀] using h
  have hne : minObservations (X := ProtocolFullPoints oneLoopData)
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by norm_num) hle
  obtain ⟨B, hB, hcard⟩ := minObservations_attained
    (X := ProtocolFullPoints oneLoopData)
    (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) hne
  have htwo : 2 ≤ B.card := oneLoop_full_bot_two_le_card B hB
  have hmin : minObservations (X := ProtocolFullPoints oneLoopData)
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) = 2 := by
    apply le_antisymm hle
    rw [← hcard]
    exact_mod_cast htwo
  letI : DecidableEq (ambientChange oneLoopData oneLoopInput.H) :=
    ambientDecidableEq oneLoopData oneLoopInput.H oneLoopVertices
      oneLoopEdges oneLoopFibers
  letI : DecidablePred (· ∈ (⊥ : Subgroup
      (ambientChange oneLoopData oneLoopInput.H))) := by
    intro a
    exact decidable_of_iff (a = 1) (by simp)
  have hsome : ∃ C : Finset (ProtocolFullPoints oneLoopData),
      oneLoopFullBotMinimum = some C := by
    cases hm : oneLoopFullBotMinimum with
    | some C => exact ⟨C, rfl⟩
    | none =>
        have hn := (minimumObservation_none_iff
          (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H))
          (FiniteProtocolInput.ambientTable oneLoopInput oneLoopVisible
            oneLoopVertices oneLoopFibers)
          (allProtocolFullPoints oneLoopData oneLoopVertices
            oneLoopEdges oneLoopFibers)).1 (by simpa only [oneLoopFullBotMinimum] using hm)
        exact (hn ⟨B₀, hB₀⟩).elim
  obtain ⟨C, hC⟩ := hsome
  have hc : (C.card : ℕ∞) =
      minObservations (X := ProtocolFullPoints oneLoopData)
        (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H)) := by
    exact minimumObservation_card
      (⊥ : Subgroup (ambientChange oneLoopData oneLoopInput.H))
      (FiniteProtocolInput.ambientTable oneLoopInput oneLoopVisible
        oneLoopVertices oneLoopFibers)
      (allProtocolFullPoints oneLoopData oneLoopVertices
        oneLoopEdges oneLoopFibers) C
      (by simpa only [oneLoopFullBotMinimum] using hC)
  have hCcard : C.card = 2 := by exact_mod_cast hc.trans hmin
  exact ⟨hmin, by rw [optimalQueries_eq_minObservations, hmin],
    C, hC, hCcard⟩

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- In the specified Xall order, the original compatible minimum search
returns the first edge point. The returned point is the sufficient point above. -/
theorem oneLoop_full_compatible_C_exact :
    protocolFullMinimum oneLoopInput oneLoopVisible oneLoopVertices
      oneLoopEdges oneLoopFibers =
      some ({Sum.inr (Sum.inl false)} :
        Finset (ProtocolFullPoints oneLoopData)) := by
  decide

/-- The original full-point greedy search uses the same first edge point. -/
theorem oneLoop_full_compatible_greedy_exact :
    protocolFullGreedy oneLoopInput oneLoopVisible oneLoopVertices
      oneLoopEdges oneLoopFibers =
      Sum.inl ({Sum.inr (Sum.inl false)} :
        Finset (ProtocolFullPoints oneLoopData)) := by
  letI : DecidableEq (ambientChange oneLoopData oneLoopInput.H) :=
    ambientDecidableEq oneLoopData oneLoopInput.H oneLoopVertices
      oneLoopEdges oneLoopFibers
  decide

/-- In the same Xall order, all-change identification chooses the named edge
and state 0; the prior proof shows this returned pair is globally minimal. -/
theorem oneLoop_full_bot_C_exact :
    oneLoopFullBotMinimum =
      some ({Sum.inr (Sum.inl false),
        Sum.inr (Sum.inr ⟨PUnit.unit, false⟩)} :
        Finset (ProtocolFullPoints oneLoopData)) := by
  decide

/-- Greedy's input-order tie break selects the same two minimal points. -/
theorem oneLoop_full_bot_greedy_exact :
    oneLoopFullBotGreedy =
      Sum.inl ({Sum.inr (Sum.inl false),
        Sum.inr (Sum.inr ⟨PUnit.unit, false⟩)} :
        Finset (ProtocolFullPoints oneLoopData)) := by
  letI : DecidableEq (ambientChange oneLoopData oneLoopInput.H) :=
    ambientDecidableEq oneLoopData oneLoopInput.H oneLoopVertices
      oneLoopEdges oneLoopFibers
  decide

end AAT.AG.MinimalCompatibilityObservations

#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopVisible
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopEdgeSwapAmbient
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopEdgeSwap_incompatible
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopEdgeSwap_fixes_state
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_state_search_infinite
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopFiberSwapAmbient
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_edge_state_sufficient_bot
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_state_invisible_unique
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_state_C_outputs
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_edge_sufficient
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_full_compatible_search_one
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_full_bot_two_le_card
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopFullBotMinimum
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopFullBotGreedy
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_full_bot_search_two
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_full_compatible_C_exact
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_full_compatible_greedy_exact
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_full_bot_C_exact
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_full_bot_greedy_exact
#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
