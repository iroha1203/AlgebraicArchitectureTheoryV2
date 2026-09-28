import ResearchLean.AG.MinimalCompatibilityObservations.IndependentComposition
import ResearchLean.AG.ProtocolHolonomy.ChangeGroup
import ResearchLean.AG.ProtocolHolonomy.LiftBridge
import Formal.Util.AssertStandardAxioms

/-!
# G-128: ambient changes of a named reversible protocol

The ambient group retains the selected visible change and an arbitrary
fiber-preserving permutation of all states. Named-operation compatibility is
imposed only on a separate subgroup.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction

universe u v w

variable {Q : FixedFDirectedMultigraph.{u, v}}
variable (D : ReversibleData.{u, v, w} Q)
variable (H : Subgroup (FixedFGraphAutomorphism Q))

abbrev ProtocolStates := Σ x, D.Fiber x

/-- Visible changes in `H`, paired with all state permutations following the
visible vertex map. This group includes operation-incompatible changes. -/
def ambientChange : Subgroup (H × Equiv.Perm (ProtocolStates D)) where
  carrier := {a | ∀ p : ProtocolStates D, (a.2 p).1 = a.1.1.vertex p.1}
  one_mem' := by
    intro p
    rfl
  mul_mem' := by
    intro a b ha hb p
    change ((a.2 * b.2) p).1 =
      (a.1.1 * b.1.1).vertex p.1
    calc
      ((a.2 * b.2) p).1 = a.1.1.vertex (b.2 p).1 := ha (b.2 p)
      _ = a.1.1.vertex (b.1.1.vertex p.1) := congrArg a.1.1.vertex (hb p)
      _ = (a.1.1 * b.1.1).vertex p.1 := rfl
  inv_mem' := by
    intro a ha p
    change ((a.2⁻¹) p).1 = (a.1.1⁻¹).vertex p.1
    apply a.1.1.vertex.injective
    calc
      a.1.1.vertex ((a.2⁻¹ p).1) = (a.2 (a.2⁻¹ p)).1 := (ha (a.2⁻¹ p)).symm
      _ = p.1 := by simp
      _ = a.1.1.vertex ((a.1.1⁻¹).vertex p.1) := by simp

/-- A member of the ambient group preserves the original named-operation
relation precisely when its visible and state components commute with each
named edge in both directions. -/
def compatibleChange : Subgroup (ambientChange D H) where
  carrier := {a | ∀ e p q,
    D.NamedExecution e p q ↔
      D.NamedExecution (a.1.1.1.edge e) (a.1.2 p) (a.1.2 q)}
  one_mem' := by
    intro e p q
    exact Iff.rfl
  mul_mem' := by
    intro a b ha hb e p q
    change D.NamedExecution e p q ↔
      D.NamedExecution (a.1.1.1.edge (b.1.1.1.edge e))
        (a.1.2 (b.1.2 p)) (a.1.2 (b.1.2 q))
    exact (hb e p q).trans
      (ha (b.1.1.1.edge e) (b.1.2 p) (b.1.2 q))
  inv_mem' := by
    intro a ha e p q
    have h := ha (a.1.1.1.edge.symm e)
      (a.1.2.symm p) (a.1.2.symm q)
    simpa using h.symm

/-- The operation-compatible part of the independently constructed ambient
group is the original G-127 change group, preserving both components. -/
def compatibleMulEquivChangeGroup :
    compatibleChange D H ≃* D.ChangeGroup H where
  toFun a :=
    ⟨{ visible := a.1.1.1.1
       state := a.1.1.2
       observation := a.1.2
       preserves := a.2 }, a.1.1.1.2⟩
  invFun c :=
    ⟨⟨(⟨c.1.visible, c.2⟩, c.1.state), c.1.observation⟩,
      c.1.preserves⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv c := by
    apply Subtype.ext
    apply ReversibleData.StateChange.ext <;> rfl
  map_mul' a b := by
    apply Subtype.ext
    apply ReversibleData.StateChange.ext <;> rfl

@[simp] theorem compatibleMulEquiv_visible
    (a : compatibleChange D H) :
    (compatibleMulEquivChangeGroup D H a).1.visible = a.1.1.1.1 := rfl

@[simp] theorem compatibleMulEquiv_state
    (a : compatibleChange D H) :
    (compatibleMulEquivChangeGroup D H a).1.state = a.1.1.2 := rfl

/-- The same compatible changes, now displayed as visible changes paired with
their original G-127 fiberwise lifts. -/
noncomputable def compatibleMulEquivLiftPair :
    compatibleChange D H ≃* D.LiftPair H :=
  (compatibleMulEquivChangeGroup D H).trans
    (D.liftPairMulEquivChangeGroup H).symm

/-- The visible projection of the independently built compatible group. -/
def compatibleVisible : compatibleChange D H →* H where
  toFun a := a.1.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem compatibleMulEquiv_projection
    (a : compatibleChange D H) :
    ReversibleData.ChangeGroup.projection (compatibleMulEquivChangeGroup D H a) =
      compatibleVisible D H a := rfl

@[simp] theorem compatibleLiftPair_visible
    (a : compatibleChange D H) :
    (compatibleMulEquivLiftPair D H a).1 = compatibleVisible D H a := by
  rfl

/-- Every visible fiber of the compatible group is the original G-127 lift
fiber, including the possibility that both sides are empty. -/
noncomputable def compatibleFiberEquiv (u₀ : H) :
    {a : compatibleChange D H // compatibleVisible D H a = u₀} ≃
      D.Lift u₀.1 where
  toFun a := by
    let p := compatibleMulEquivLiftPair D H a.1
    have hp : p.1 = u₀ :=
      (compatibleLiftPair_visible D H a.1).trans a.2
    exact hp ▸ p.2
  invFun l := ⟨(compatibleMulEquivLiftPair D H).symm ⟨u₀, l⟩, by
    have h := compatibleLiftPair_visible D H
      ((compatibleMulEquivLiftPair D H).symm ⟨u₀, l⟩)
    simpa using h.symm⟩
  left_inv a := by
    rcases a with ⟨a, ha⟩
    cases ha
    apply Subtype.ext
    exact (compatibleMulEquivLiftPair D H).symm_apply_apply a
  right_inv l := by
    have hp := (compatibleMulEquivLiftPair D H).apply_symm_apply
      (⟨u₀, l⟩ : D.LiftPair H)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hp).2

/-- Observation targets containing only protocol states. -/
def ambientStateAction : MulAction (ambientChange D H) (ProtocolStates D) where
  smul a p := a.1.2 p
  one_smul := by intro p; rfl
  mul_smul := by intro a b p; rfl

/-- Vertices, named edges, and states are kept as separate observable points. -/
abbrev ProtocolFullPoints := Q.Vertex ⊕ (Q.Edge ⊕ ProtocolStates D)

def ambientFullAction : MulAction (ambientChange D H) (ProtocolFullPoints D) where
  smul a x :=
    match x with
    | Sum.inl v => Sum.inl (a.1.1.1.vertex v)
    | Sum.inr (Sum.inl e) => Sum.inr (Sum.inl (a.1.1.1.edge e))
    | Sum.inr (Sum.inr p) => Sum.inr (Sum.inr (a.1.2 p))
  one_smul := by
    intro (x : ProtocolFullPoints D)
    rcases x with v | e | p <;> rfl
  mul_smul := by
    intro a b x
    rcases x with v | e | p <;> rfl

theorem ambientFullAction_faithful :
    letI := ambientFullAction D H
    FaithfulSMul (ambientChange D H) (ProtocolFullPoints D) := by
  letI := ambientFullAction D H
  refine ⟨?_⟩
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply FixedFGraphAutomorphism.ext
    · apply Equiv.ext
      intro v
      have hv := h (Sum.inl v)
      change Sum.inl (a.1.1.1.vertex v) = Sum.inl (b.1.1.1.vertex v) at hv
      exact Sum.inl.inj hv
    · apply Equiv.ext
      intro e
      have he := h (Sum.inr (Sum.inl e))
      change Sum.inr (Sum.inl (a.1.1.1.edge e)) =
        Sum.inr (Sum.inl (b.1.1.1.edge e)) at he
      exact Sum.inl.inj (Sum.inr.inj he)
  · apply Equiv.ext
    intro p
    have hp := h (Sum.inr (Sum.inr p))
    change Sum.inr (Sum.inr (a.1.2 p)) =
      Sum.inr (Sum.inr (b.1.2 p)) at hp
    exact Sum.inr.inj (Sum.inr.inj hp)

theorem ambientFull_sufficient [Fintype Q.Vertex] [Fintype Q.Edge]
    [∀ v, Fintype (D.Fiber v)]
    (Gamma : Subgroup (ambientChange D H)) :
    letI := ambientFullAction D H
    Sufficient Gamma (Finset.univ : Finset (ProtocolFullPoints D)) := by
  letI := ambientFullAction D H
  letI : FaithfulSMul (ambientChange D H) (ProtocolFullPoints D) :=
    ambientFullAction_faithful D H
  intro g hg
  have hone : g = 1 := FaithfulSMul.eq_of_smul_eq_smul (by
    intro (x : ProtocolFullPoints D)
    have hOne : (1 : ambientChange D H) • x = x := by
      rcases x with v | e | p <;> rfl
    exact (hg x (Finset.mem_univ x)).trans hOne.symm)
  simp [hone]

theorem ambientFull_minObservations_ne_top [Fintype Q.Vertex] [Fintype Q.Edge]
    [∀ v, Fintype (D.Fiber v)] :
    letI := ambientFullAction D H
    minObservations (X := ProtocolFullPoints D) (compatibleChange D H) ≠ ⊤ := by
  letI := ambientFullAction D H
  have hS := ambientFull_sufficient D H (compatibleChange D H)
  have hle := minObservations_le (compatibleChange D H)
    (Finset.univ : Finset (ProtocolFullPoints D)) hS
  intro htop
  rw [htop] at hle
  have hfinite : ((Finset.univ : Finset (ProtocolFullPoints D)).card : ℕ∞) ≠ ⊤ := by
    exact ENat.coe_ne_top _
  exact hfinite (top_le_iff.mp hle)

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
