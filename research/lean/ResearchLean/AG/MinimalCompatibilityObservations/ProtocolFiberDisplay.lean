import ResearchLean.AG.MinimalCompatibilityObservations.ProtocolAmbient
import ResearchLean.AG.ProtocolHolonomy.LiftRootReconstruction
import ResearchLean.AG.ProtocolHolonomy.VerticalCentralizer
import Formal.Util.AssertStandardAxioms

/-!
# G-128: fiberwise display of every ambient protocol change
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction

universe u v w

variable {Q : FixedFDirectedMultigraph.{u, v}}
variable (D : ReversibleData.{u, v, w} Q)
variable (H : Subgroup (FixedFGraphAutomorphism Q))

/-- The fixed visible change and a family of bijections on every fiber,
without imposing the named-operation equation. -/
def AmbientFiberPair :=
  Σ u : H, ∀ v : Q.Vertex, D.Fiber v ≃ D.Fiber (u.1.vertex v)

/-- Assemble an arbitrary fiberwise family into a total-state permutation. -/
def fiberPairToAmbient (a : AmbientFiberPair D H) : ambientChange D H :=
  ⟨(a.1, Equiv.sigmaCongr a.1.1.vertex a.2), by
    rintro ⟨v, x⟩
    rfl⟩

/-- Restrict the ambient total-state permutation to one source fiber. -/
def ambientFiberTo (a : ambientChange D H) (v : Q.Vertex)
    (x : D.Fiber v) : D.Fiber (a.1.1.1.vertex v) :=
  Eq.mp (congrArg D.Fiber (a.2 ⟨v, x⟩)) (a.1.2 ⟨v, x⟩).2

theorem ambientState_eq_mk (a : ambientChange D H)
    (v : Q.Vertex) (x : D.Fiber v) :
    a.1.2 ⟨v, x⟩ = ⟨a.1.1.1.vertex v, ambientFiberTo D H a v x⟩ := by
  apply Sigma.ext (a.2 ⟨v, x⟩)
  exact (cast_heq (congrArg D.Fiber (a.2 ⟨v, x⟩))
    (a.1.2 ⟨v, x⟩).2).symm

theorem ambientFiberTo_injective (a : ambientChange D H) (v : Q.Vertex) :
    Function.Injective (ambientFiberTo D H a v) := by
  intro x y h
  apply (Sigma.mk.inj_iff.mp (a.1.2.injective (by
    rw [ambientState_eq_mk D H, ambientState_eq_mk D H, h]))).2 |> eq_of_heq

theorem ambientFiberTo_surjective (a : ambientChange D H) (v : Q.Vertex) :
    Function.Surjective (ambientFiberTo D H a v) := by
  intro y
  obtain ⟨⟨w, x⟩, h⟩ := a.1.2.surjective
    (⟨a.1.1.1.vertex v, y⟩ : ProtocolStates D)
  have hw : w = v := a.1.1.1.vertex.injective (by
    calc
      a.1.1.1.vertex w = (a.1.2 ⟨w, x⟩).1 := (a.2 ⟨w, x⟩).symm
      _ = a.1.1.1.vertex v := congrArg Sigma.fst h)
  subst w
  refine ⟨x, ?_⟩
  have hh := h
  rw [ambientState_eq_mk D H] at hh
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

/-- The mathematical fiberwise display of an ambient state permutation. -/
noncomputable def ambientFiberEquiv (a : ambientChange D H) (v : Q.Vertex) :
    D.Fiber v ≃ D.Fiber (a.1.1.1.vertex v) :=
  Equiv.ofBijective (ambientFiberTo D H a v)
    ⟨ambientFiberTo_injective D H a v, ambientFiberTo_surjective D H a v⟩

/-- The ambient total-state presentation and the fixed GOAL's fiberwise
presentation are equivalent for every visible change. -/
noncomputable def ambientEquivFiberPair :
    ambientChange D H ≃ AmbientFiberPair D H where
  toFun a := ⟨a.1.1, ambientFiberEquiv D H a⟩
  invFun := fiberPairToAmbient D H
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Equiv.ext
      rintro ⟨v, x⟩
      change (⟨a.1.1.1.vertex v, ambientFiberEquiv D H a v x⟩ : ProtocolStates D) =
        a.1.2 ⟨v, x⟩
      exact (ambientState_eq_mk D H a v x).symm
  right_inv p := by
    rcases p with ⟨u, f⟩
    change (⟨u, ambientFiberEquiv D H (fiberPairToAmbient D H ⟨u, f⟩)⟩ :
      AmbientFiberPair D H) = ⟨u, f⟩
    congr 1
    funext v
    apply Equiv.ext
    intro x
    rfl

/-- The group law is the original product in the independently constructed
ambient group, transported through the explicit fiberwise display. -/
noncomputable instance : Group (AmbientFiberPair D H) :=
  (ambientEquivFiberPair D H).symm.group

noncomputable def ambientMulEquivFiberPair :
    ambientChange D H ≃* AmbientFiberPair D H where
  toEquiv := ambientEquivFiberPair D H
  map_mul' a b := by
    change ambientEquivFiberPair D H (a * b) =
      ambientEquivFiberPair D H
        ((ambientEquivFiberPair D H).symm (ambientEquivFiberPair D H a) *
          (ambientEquivFiberPair D H).symm (ambientEquivFiberPair D H b))
    simp

theorem fiberPair_mul_fiber_apply (a b : AmbientFiberPair D H)
    (v : Q.Vertex) (x : D.Fiber v) :
    ((a * b).2 v) x = a.2 (b.1.1.vertex v) (b.2 v x) := by
  rfl

/-- In the fiberwise display, named-operation compatibility is exactly the
original edge square from the fixed GOAL. -/
theorem fiberPair_compatible_iff (a : AmbientFiberPair D H) :
    fiberPairToAmbient D H a ∈ compatibleChange D H ↔
      ∀ (e : Q.Edge) (x : D.Fiber (Q.source e)),
        a.2 (Q.target e) (D.edgeEquiv e x) =
          D.renamedEdgeEquiv a.1.1 e (a.2 (Q.source e) x) := by
  constructor
  · intro h e x
    let c : D.StateChange :=
      { visible := a.1.1
        state := (fiberPairToAmbient D H a).1.2
        observation := (fiberPairToAmbient D H a).2
        preserves := h }
    have hfiber (v : Q.Vertex) : c.toLift.fiber v = a.2 v := by
      apply Equiv.ext
      intro y
      rfl
    simpa only [hfiber] using c.toLift.edge_naturality e x
  · intro h
    let l : D.Lift a.1.1 := ⟨a.2, h⟩
    intro e p q
    exact l.preserves_namedExecution e p q

/-- The fixed GOAL's compatible group as a subgroup of all fiberwise pairs. -/
noncomputable def fiberCompatible : Subgroup (AmbientFiberPair D H) :=
  (compatibleChange D H).map (ambientMulEquivFiberPair D H).toMonoidHom

@[simp] theorem mem_fiberCompatible_iff (a : AmbientFiberPair D H) :
    a ∈ fiberCompatible D H ↔
      ∀ (e : Q.Edge) (x : D.Fiber (Q.source e)),
        a.2 (Q.target e) (D.edgeEquiv e x) =
          D.renamedEdgeEquiv a.1.1 e (a.2 (Q.source e) x) := by
  rw [fiberCompatible, Subgroup.mem_map_equiv]
  exact fiberPair_compatible_iff D H a

/-- The actual E1 fiberwise compatible group and G-127's original change
group are isomorphic, preserving the same visible and state changes. -/
noncomputable def fiberCompatibleMulEquivChangeGroup :
    fiberCompatible D H ≃* D.ChangeGroup H :=
  ((ambientMulEquivFiberPair D H).subgroupMap (compatibleChange D H)).symm.trans
    (compatibleMulEquivChangeGroup D H)

@[simp] theorem fiberCompatibleMulEquiv_visible
    (a : fiberCompatible D H) :
    (fiberCompatibleMulEquivChangeGroup D H a).1.visible = a.1.1.1 := rfl

@[simp] theorem fiberCompatibleMulEquiv_state
    (a : fiberCompatible D H) :
    (fiberCompatibleMulEquivChangeGroup D H a).1.state =
      Equiv.sigmaCongr a.1.1.1.vertex a.1.2 := rfl

/-- Each compatible visible fiber inherits G-127's original root-solution
classification, with no assumption that the fiber is inhabited. -/
noncomputable def compatibleFiberRootEquiv (R : RootedPaths Q) (u₀ : H) :
    {a : compatibleChange D H // compatibleVisible D H a = u₀} ≃
      D.RootSolutions R u₀.1 :=
  (compatibleFiberEquiv D H u₀).trans
    (D.liftEquivRootSolutions R u₀.1)

/-- The literal kernel of the compatible visible projection. -/
def compatibleVertical : Subgroup (compatibleChange D H) :=
  (compatibleVisible D H).ker

theorem compatibleVertical_map :
    (compatibleVertical D H).map (compatibleMulEquivChangeGroup D H).toMonoidHom =
      ReversibleData.ChangeGroup.verticalGroup (D := D) (H := H) := by
  ext c
  rw [Subgroup.mem_map_equiv]
  change compatibleVisible D H ((compatibleMulEquivChangeGroup D H).symm c) = 1 ↔
    ReversibleData.ChangeGroup.projection c = 1
  have h := compatibleMulEquiv_projection D H
    ((compatibleMulEquivChangeGroup D H).symm c)
  simp only [(compatibleMulEquivChangeGroup D H).apply_symm_apply] at h
  rw [h]

/-- The compatible vertical kernel is the original G-127 projection kernel. -/
noncomputable def compatibleVerticalEquivChangeVertical :
    compatibleVertical D H ≃*
      ReversibleData.ChangeGroup.verticalGroup (D := D) (H := H) :=
  ((compatibleMulEquivChangeGroup D H).subgroupMap (compatibleVertical D H)).trans
    (MulEquiv.subgroupCongr (compatibleVertical_map D H))

/-- The same kernel as actual identity-visible state changes. -/
def changeVerticalEquivStateVertical :
    ReversibleData.ChangeGroup.verticalGroup (D := D) (H := H) ≃*
      D.VerticalStateGroup where
  toFun c := ⟨c.1.1, by
    change c.1.1.visible = 1
    exact congrArg Subtype.val c.2⟩
  invFun a := ⟨⟨a.1, by
    change a.1.visible ∈ H
    have hv : a.1.visible = 1 := a.2
    rw [hv]
    exact H.one_mem⟩, by
      apply Subtype.ext
      exact a.2⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; rfl
  map_mul' a b := by apply Subtype.ext; rfl

/-- The full chain from the new compatible projection kernel to the original
G-127 B2 product of root holonomy centralizers. -/
noncomputable def compatibleVerticalRootMulEquiv (R : RootedPaths Q) :
    compatibleVertical D H ≃* D.RootCentralizers R :=
  ((compatibleVerticalEquivChangeVertical D H).trans
    (changeVerticalEquivStateVertical D H)).trans
      ((D.liftMulEquivVerticalStateGroup).symm.trans (D.verticalRootMulEquiv R))

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
