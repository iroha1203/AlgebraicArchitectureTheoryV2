import ResearchLean.AG.ProtocolHolonomy.LiftableVisible
import Formal.Util.AssertStandardAxioms

/-!
# Right vertical action on every lift fiber

The literal kernel acts by right multiplication on a fiber of the actual
visible projection. The action is transported to the original `Lift` type.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- The fiber of the actual change group over a liftable visible change. -/
def LiftableFiber (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) :=
  {a : D.ChangeGroup H // D.projectionToLiftable H a = g}

/-- A fixed-visible actual state change is the same object as an element of
the selected visible projection fiber. -/
def stateChangeOverEquivLiftableFiber
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) :
    D.StateChangeOver g.1.1 ≃ D.LiftableFiber H g where
  toFun c := ⟨⟨c.1, by
    change c.1.visible ∈ H
    rw [c.2]
    exact g.1.2⟩, by
      apply Subtype.ext
      apply Subtype.ext
      exact c.2⟩
  invFun a := ⟨a.1.1, by
    have h := congrArg (fun z : D.LiftableVisible H => z.1.1) a.2
    exact h⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Actual A1 lifts over `g` are exactly the projection fiber of actual
operation-preserving state changes. -/
noncomputable def liftEquivLiftableFiber
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) :
    D.Lift g.1.1 ≃ D.LiftableFiber H g :=
  (D.liftEquivStateChangeOver g.1.1).trans
    (D.stateChangeOverEquivLiftableFiber H g)

/-- Right multiplication by a literal kernel element, represented as a
left action of the opposite kernel group. -/
instance liftableFiberSMul
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) :
    SMul (D.projectionToLiftable H).kerᵐᵒᵖ (D.LiftableFiber H g) where
  smul k a := ⟨a.1 * (MulOpposite.unop k).1, by
    rw [map_mul, a.2,
      MonoidHom.mem_ker.mp (MulOpposite.unop k).2, mul_one]⟩

instance liftableFiberMulAction
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) :
    MulAction (D.projectionToLiftable H).kerᵐᵒᵖ (D.LiftableFiber H g) where
  one_smul a := by
    apply Subtype.ext
    change a.1 * (1 : D.ChangeGroup H) = a.1
    simp
  mul_smul k l a := by
    apply Subtype.ext
    change a.1 * ((MulOpposite.unop l).1 * (MulOpposite.unop k).1) =
      (a.1 * (MulOpposite.unop l).1) * (MulOpposite.unop k).1
    simp [mul_assoc]

theorem liftableFiber_action_free
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a : D.LiftableFiber H g) :
    Function.Injective
      (fun k : (D.projectionToLiftable H).kerᵐᵒᵖ => k • a) := by
  intro k l h
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have hv := congrArg (fun z : D.LiftableFiber H g => z.1) h
  exact mul_left_cancel hv

theorem liftableFiber_action_transitive
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H)
    (a b : D.LiftableFiber H g) :
    ∃ k : (D.projectionToLiftable H).kerᵐᵒᵖ, k • a = b := by
  let d : D.ChangeGroup H := a.1⁻¹ * b.1
  have hd : d ∈ (D.projectionToLiftable H).ker := by
    rw [MonoidHom.mem_ker]
    change D.projectionToLiftable H (a.1⁻¹ * b.1) = 1
    rw [map_mul, map_inv, a.2, b.2, inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨d, hd⟩, ?_⟩
  apply Subtype.ext
  change a.1 * d = b.1
  simp [d]

/-- The C3 right action on the original A1 lift fiber, obtained from
literal right multiplication in the actual change group. -/
noncomputable def liftRightAction
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H)
    (k : (D.projectionToLiftable H).kerᵐᵒᵖ)
    (a : D.Lift g.1.1) : D.Lift g.1.1 :=
  (D.liftEquivLiftableFiber H g).symm
    (k • D.liftEquivLiftableFiber H g a)

theorem liftRightAction_one
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a : D.Lift g.1.1) :
    D.liftRightAction H g 1 a = a := by
  simp [liftRightAction]

theorem liftRightAction_mul
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H)
    (k l : (D.projectionToLiftable H).kerᵐᵒᵖ)
    (a : D.Lift g.1.1) :
    D.liftRightAction H g (k * l) a =
      D.liftRightAction H g k (D.liftRightAction H g l a) := by
  simp [liftRightAction, mul_smul]

@[simp] theorem liftRightAction_toFiber
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H)
    (k : (D.projectionToLiftable H).kerᵐᵒᵖ)
    (a : D.Lift g.1.1) :
    D.liftEquivLiftableFiber H g (D.liftRightAction H g k a) =
      k • D.liftEquivLiftableFiber H g a :=
  (D.liftEquivLiftableFiber H g).apply_symm_apply _

/-- The action on each original A1 lift fiber is free. -/
theorem lift_action_free
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a : D.Lift g.1.1) :
    Function.Injective
      (fun k : (D.projectionToLiftable H).kerᵐᵒᵖ =>
        D.liftRightAction H g k a) := by
  intro k l h
  have he := congrArg (D.liftEquivLiftableFiber H g) h
  rw [D.liftRightAction_toFiber H g, D.liftRightAction_toFiber H g] at he
  exact D.liftableFiber_action_free H g _ he

/-- Every two A1 lifts over the same visible change differ by a unique
vertical kernel element on the right. -/
theorem lift_action_transitive
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a b : D.Lift g.1.1) :
    ∃ k : (D.projectionToLiftable H).kerᵐᵒᵖ,
      D.liftRightAction H g k a = b := by
  let E := D.liftEquivLiftableFiber H g
  obtain ⟨k, hk⟩ := D.liftableFiber_action_transitive H g (E a) (E b)
  refine ⟨k, E.injective ?_⟩
  rw [D.liftRightAction_toFiber H g]
  exact hk

theorem lift_action_existsUnique
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a b : D.Lift g.1.1) :
    ∃! k : (D.projectionToLiftable H).kerᵐᵒᵖ,
      D.liftRightAction H g k a = b := by
  obtain ⟨k, hk⟩ := D.lift_action_transitive H g a b
  exact ⟨k, hk, fun l hl => D.lift_action_free H g a (hl.trans hk.symm)⟩

/-- The transported action remains literal right multiplication of the
actual state changes. -/
theorem liftRightAction_stateChange
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H)
    (k : (D.projectionToLiftable H).kerᵐᵒᵖ)
    (a : D.Lift g.1.1) :
    (D.liftRightAction H g k a).toStateChange =
      a.toStateChange * (MulOpposite.unop k).1.1 := by
  have h := congrArg (fun z : D.LiftableFiber H g => z.1.1)
    (D.liftRightAction_toFiber H g k a)
  exact h

/-- The requested right action of the original vertical group Aut_Q(F). -/
noncomputable def verticalRightAction
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H)
    (a : D.Lift g.1.1)
    (α : D.Lift (1 : FixedFGraphAutomorphism Q)) : D.Lift g.1.1 :=
  D.liftRightAction H g
    (MulOpposite.op (D.verticalLiftEquivLiftableKernel H α)) a

theorem verticalRightAction_one
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a : D.Lift g.1.1) :
    D.verticalRightAction H g a 1 = a := by
  simp [verticalRightAction, D.liftRightAction_one H g a]

theorem verticalRightAction_mul
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a : D.Lift g.1.1)
    (α β : D.Lift (1 : FixedFGraphAutomorphism Q)) :
    D.verticalRightAction H g (D.verticalRightAction H g a α) β =
      D.verticalRightAction H g a (α * β) := by
  unfold verticalRightAction
  rw [← D.liftRightAction_mul H g]
  congr 1
  simp [map_mul]

theorem verticalRightAction_free
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a : D.Lift g.1.1) :
    Function.Injective
      (fun α : D.Lift (1 : FixedFGraphAutomorphism Q) =>
        D.verticalRightAction H g a α) := by
  intro α β h
  have hk := D.lift_action_free H g a h
  apply (D.verticalLiftEquivLiftableKernel H).injective
  exact congrArg MulOpposite.unop hk

theorem verticalRightAction_transitive
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a b : D.Lift g.1.1) :
    ∃ α : D.Lift (1 : FixedFGraphAutomorphism Q),
      D.verticalRightAction H g a α = b := by
  obtain ⟨k, hk⟩ := D.lift_action_transitive H g a b
  refine ⟨(D.verticalLiftEquivLiftableKernel H).symm
      (MulOpposite.unop k), ?_⟩
  simpa [verticalRightAction] using hk

theorem verticalRightAction_existsUnique
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (a b : D.Lift g.1.1) :
    ∃! α : D.Lift (1 : FixedFGraphAutomorphism Q),
      D.verticalRightAction H g a α = b := by
  obtain ⟨α, hα⟩ := D.verticalRightAction_transitive H g a b
  exact ⟨α, hα, fun β hβ =>
    D.verticalRightAction_free H g a (hβ.trans hα.symm)⟩

/-- C3's action is literally `(φ·α)_v = φ_v ∘ α_v`. -/
theorem verticalRightAction_fiber_apply
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H)
    (a : D.Lift g.1.1)
    (α : D.Lift (1 : FixedFGraphAutomorphism Q))
    (v : Q.Vertex) (x : D.Fiber v) :
    (D.verticalRightAction H g a α).fiber v x =
      a.fiber v (α.fiber v x) := by
  have h := congrArg (fun c : D.StateChange => c.state ⟨v, x⟩)
    (D.liftRightAction_stateChange H g
      (MulOpposite.op (D.verticalLiftEquivLiftableKernel H α)) a)
  change (⟨g.1.1.vertex v,
      (D.verticalRightAction H g a α).fiber v x⟩ : Σ z, D.Fiber z) =
    a.stateEquiv (α.stateEquiv ⟨v, x⟩) at h
  simpa only [Lift.stateEquiv_apply,
    FixedFGraphAutomorphism.one_vertex] using
    eq_of_heq (Sigma.mk.inj_iff.mp h).2

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftEquivLiftableFiber
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftableFiber_action_free
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftableFiber_action_transitive
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.lift_action_existsUnique
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalRightAction_existsUnique
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalRightAction_fiber_apply
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
