import ResearchLean.AG.ProtocolHolonomy.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker
import Formal.Util.AssertStandardAxioms

/-!
# Actual operation-preserving changes of a reversible protocol

The graph and total-state equivalences act on named execution graphs.  The
preservation law is stated as an iff for the named edge relation, so it is
stable under composition and inversion.  Its equivalence to the fiberwise
`Lift` equation is a separate proof obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}} (D : ReversibleData.{u, v, w} Q)

/-- A pair of total states related by one actual named operation. -/
def NamedExecution (e : Q.Edge)
    (p q : Σ x, D.Fiber x) : Prop :=
  ∃ x : D.Fiber (Q.source e),
    p = ⟨Q.source e, x⟩ ∧
      q = ⟨Q.target e, D.edgeEquiv e x⟩

/-- A graph renaming with an actual equivalence of all states that follows
the visible vertex and preserves each renamed named operation. -/
structure StateChange where
  visible : FixedFGraphAutomorphism Q
  state : (Σ x, D.Fiber x) ≃ (Σ x, D.Fiber x)
  observation : ∀ p, (state p).1 = visible.vertex p.1
  preserves : ∀ e p q,
    D.NamedExecution e p q ↔
      D.NamedExecution (visible.edge e) (state p) (state q)

namespace StateChange

variable {D}

@[ext] theorem ext {a b : D.StateChange}
    (hv : a.visible = b.visible) (hs : a.state = b.state) : a = b := by
  cases a
  cases b
  cases hv
  cases hs
  rfl

instance : One D.StateChange where
  one :=
    { visible := 1
      state := 1
      observation := fun _ => rfl
      preserves := fun _ _ _ => Iff.rfl }

instance : Mul D.StateChange where
  mul a b :=
    { visible := a.visible * b.visible
      state := a.state * b.state
      observation := by
        intro p
        calc
          ((a.state * b.state) p).1 = a.visible.vertex (b.state p).1 :=
            a.observation (b.state p)
          _ = a.visible.vertex (b.visible.vertex p.1) :=
            congrArg a.visible.vertex (b.observation p)
          _ = (a.visible * b.visible).vertex p.1 := rfl
      preserves := by
        intro e p q
        change D.NamedExecution e p q ↔
          D.NamedExecution (a.visible.edge (b.visible.edge e))
            (a.state (b.state p)) (a.state (b.state q))
        exact (b.preserves e p q).trans
          (a.preserves (b.visible.edge e) (b.state p) (b.state q)) }

instance : Inv D.StateChange where
  inv a :=
    { visible := a.visible⁻¹
      state := a.state⁻¹
      observation := by
        intro p
        apply a.visible.vertex.injective
        calc
          a.visible.vertex ((a.state⁻¹ p).1) =
              (a.state (a.state⁻¹ p)).1 :=
            (a.observation (a.state⁻¹ p)).symm
          _ = p.1 := by simp
          _ = a.visible.vertex ((a.visible⁻¹).vertex p.1) := by simp
      preserves := by
        intro e p q
        have h := a.preserves (a.visible.edge.symm e)
          (a.state.symm p) (a.state.symm q)
        simpa using h.symm }

@[simp] theorem one_visible : (1 : D.StateChange).visible = 1 := rfl
@[simp] theorem one_state : (1 : D.StateChange).state = 1 := rfl
@[simp] theorem mul_visible (a b : D.StateChange) :
    (a * b).visible = a.visible * b.visible := rfl
@[simp] theorem mul_state (a b : D.StateChange) :
    (a * b).state = a.state * b.state := rfl
@[simp] theorem inv_visible (a : D.StateChange) :
    (a⁻¹).visible = a.visible⁻¹ := rfl
@[simp] theorem inv_state (a : D.StateChange) :
    (a⁻¹).state = a.state⁻¹ := rfl

instance : Group D.StateChange where
  mul_assoc a b c := by apply ext <;> simp [mul_assoc]
  one_mul a := by apply ext <;> simp
  mul_one a := by apply ext <;> simp
  inv_mul_cancel a := by apply ext <;> simp

/-- The visible component is a group homomorphism, defined from the actual
state-change group rather than a supplied abstract extension. -/
def projection : D.StateChange →* FixedFGraphAutomorphism Q where
  toFun a := a.visible
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The total-state component is a group homomorphism. -/
def totalState : D.StateChange →* Equiv.Perm (Σ x, D.Fiber x) where
  toFun a := a.state
  map_one' := rfl
  map_mul' _ _ := rfl

theorem pair_injective :
    Function.Injective
      (fun a : D.StateChange => (a.visible, a.state)) := by
  intro a b h
  exact ext (congrArg Prod.fst h) (congrArg Prod.snd h)

end StateChange

/-- The actual change group whose visible component lies in the supplied
subgroup of graph automorphisms. -/
def ChangeGroup (H : Subgroup (FixedFGraphAutomorphism Q)) :
    Subgroup D.StateChange :=
  H.comap (StateChange.projection (D := D))

namespace ChangeGroup

variable {D} {H : Subgroup (FixedFGraphAutomorphism Q)}

/-- Projection into the selected visible group. Its image may be proper. -/
def projection : D.ChangeGroup H →* H where
  toFun a := ⟨a.1.visible, a.2⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

/-- The actual kernel of the visible projection. -/
def verticalGroup : Subgroup (D.ChangeGroup H) :=
  (projection (D := D) (H := H)).ker

@[simp] theorem projection_apply (a : D.ChangeGroup H) :
    (projection (D := D) (H := H) a).1 = a.1.visible := rfl

end ChangeGroup
end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.StateChange.projection
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.StateChange.pair_injective
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.ChangeGroup.projection
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
