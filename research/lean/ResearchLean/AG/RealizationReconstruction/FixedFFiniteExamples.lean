import ResearchLean.AG.RealizationReconstruction.FixedFFiberCardinality
import Mathlib.Tactic
import Formal.Util.AssertStandardAxioms

/-!
# The three fixed finite examples for the common following-change classification

This file instantiates the fixed-graph classification on the three examples
specified by G-123(F): the Bool product lens, its selected-value-preserving
`Fin 3` variant, and the two-session `Fin 4` protocol.  The concrete state
maps and failed update squares are retained, and all counts are obtained from
the same source/fiber classification used in the general theorem.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFFiniteExamples

open FixedFRestrictedAutomorphism
open FixedFSplitExactSequenceAndTorsor
open FixedFPointedSplitExactSequenceAndTorsor
open FixedFFiberCardinality

/-! ## General finite APIs used by the examples -/

/-- Before imposing operation preservation, a following change is exactly one
hidden permutation at every visible vertex. -/
def followingEquivVertexPermutationFamilies
    {F : FixedFDirectedMultigraph} {K : Type w}
    (automorphism : FixedFGraphAutomorphism F) :
    FixedFFollowingStateChange F K automorphism ≃
      (F.Vertex → Equiv.Perm K) where
  toFun change := change.fiberPerm
  invFun family := FixedFFollowingStateChange.ofFamily family
  left_inv change := by
    apply FixedFFollowingStateChange.ext
    apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    exact (change.factorization vertex hidden).symm
  right_inv family := FixedFFollowingStateChange.fiberPerm_ofFamily family

/-- The raw observation-preserving fiber has one arbitrary hidden permutation
per visible vertex. -/
theorem natCard_followingStateChange
    {F : FixedFDirectedMultigraph} {K : Type w}
    [Finite F.Vertex] [Finite K]
    (automorphism : FixedFGraphAutomorphism F) :
    Nat.card (FixedFFollowingStateChange F K automorphism) =
      Nat.factorial (Nat.card K) ^ Nat.card F.Vertex := by
  calc
    Nat.card (FixedFFollowingStateChange F K automorphism) =
        Nat.card (F.Vertex → Equiv.Perm K) :=
      Nat.card_congr (followingEquivVertexPermutationFamilies automorphism)
    _ = Nat.factorial (Nat.card K) ^ Nat.card F.Vertex := by
      rw [Nat.card_fun, Nat.card_perm]

/-- Raw observation-preserving changes whose constructed hidden family fixes a
selected value at every visible vertex. -/
abbrev PointedFollowingStateChange
    (F : FixedFDirectedMultigraph) (K : Type w) (basepoint : K)
    (automorphism : FixedFGraphAutomorphism F) :=
  { change : FixedFFollowingStateChange F K automorphism //
    ∀ vertex, change.fiberPerm vertex basepoint = basepoint }

/-- Pointed raw changes are exactly vertex-indexed point stabilizers. -/
def pointedFollowingEquivVertexFamilies
    {F : FixedFDirectedMultigraph} {K : Type w}
    (basepoint : K) (automorphism : FixedFGraphAutomorphism F) :
    PointedFollowingStateChange F K basepoint automorphism ≃
      (F.Vertex → PointedPermutation basepoint) where
  toFun change := fun vertex =>
    ⟨change.1.fiberPerm vertex, change.2 vertex⟩
  invFun family :=
    ⟨FixedFFollowingStateChange.ofFamily
        (fun vertex => (family vertex).1), by
      intro vertex
      rw [FixedFFollowingStateChange.fiberPerm_ofFamily]
      exact (family vertex).2⟩
  left_inv change := by
    apply Subtype.ext
    apply FixedFFollowingStateChange.ext
    apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    exact (change.1.factorization vertex hidden).symm
  right_inv family := by
    funext vertex
    apply Subtype.ext
    change
      (FixedFFollowingStateChange.ofFamily
        (fun vertex => (family vertex).1)).fiberPerm vertex =
        (family vertex).1
    exact congrFun
      (FixedFFollowingStateChange.fiberPerm_ofFamily
        (fun vertex => (family vertex).1)) vertex

/-- The raw pointed fiber has one point stabilizer per visible vertex. -/
theorem natCard_pointedFollowingStateChange
    {F : FixedFDirectedMultigraph} {K : Type w}
    [Finite F.Vertex] [Finite K]
    (basepoint : K) (automorphism : FixedFGraphAutomorphism F) :
    Nat.card (PointedFollowingStateChange F K basepoint automorphism) =
      Nat.factorial (Nat.card K - 1) ^ Nat.card F.Vertex := by
  calc
    Nat.card (PointedFollowingStateChange F K basepoint automorphism) =
        Nat.card (F.Vertex → PointedPermutation basepoint) :=
      Nat.card_congr
        (pointedFollowingEquivVertexFamilies basepoint automorphism)
    _ = Nat.factorial (Nat.card K - 1) ^ Nat.card F.Vertex := by
      rw [Nat.card_fun, natCard_pointedPermutation]

/-! ## The two product-lens graphs -/

/-- The operation graph of a product lens has one named update from every
visible value to every visible value. -/
def completeUpdateGraph (V : Type u) : FixedFDirectedMultigraph where
  Vertex := V
  Edge := V × V
  source := Prod.fst
  target := Prod.snd

/-- Every visible permutation renames all product-lens update operations. -/
def completeUpdateAutomorphism {V : Type u} (permutation : Equiv.Perm V) :
    FixedFGraphAutomorphism (completeUpdateGraph V) where
  vertex := permutation
  edge := Equiv.prodCongr permutation permutation
  source_rename _ := rfl
  target_rename _ := rfl

/-- A complete update graph on an inhabited carrier has one generated
undirected component. -/
def completeUpdateComponentEquivPUnit {V : Type u} (basepoint : V) :
    FixedFComponent (completeUpdateGraph V) ≃ PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := fixedFComponentMk (completeUpdateGraph V) basepoint
  left_inv component := by
    refine Quotient.inductionOn component ?_
    intro vertex
    change fixedFComponentMk (completeUpdateGraph V) basepoint =
      fixedFComponentMk (completeUpdateGraph V) vertex
    exact (fixedFComponent_source_eq_target
      (completeUpdateGraph V) (vertex, basepoint)).symm
  right_inv point := by cases point; rfl

theorem natCard_completeUpdateComponent {V : Type u} (basepoint : V) :
    Nat.card (FixedFComponent (completeUpdateGraph V)) = 1 := by
  calc
    Nat.card (FixedFComponent (completeUpdateGraph V)) =
        Nat.card PUnit.{u + 1} :=
      Nat.card_congr (completeUpdateComponentEquivPUnit basepoint)
    _ = 1 := by norm_num

/-! ### Fixed Bool product-lens example -/

def productGet {V : Type u} {K : Type w} (state : V × K) : V := state.1

def productPut {V : Type u} {K : Type w}
    (state : V × K) (newVisible : V) : V × K :=
  (newVisible, state.2)

abbrev BoolLensGraph := completeUpdateGraph Bool

instance : Finite BoolLensGraph.Vertex := by
  change Finite Bool
  infer_instance

theorem natCard_boolLensVertex : Nat.card BoolLensGraph.Vertex = 2 := by
  change Nat.card Bool = 2
  norm_num

def boolLensIdentityAutomorphism : FixedFGraphAutomorphism BoolLensGraph :=
  completeUpdateAutomorphism 1

def boolLensFlipAutomorphism : FixedFGraphAutomorphism BoolLensGraph :=
  completeUpdateAutomorphism (Equiv.swap false true)

abbrev BoolLensVisibleGroup :
    Subgroup (FixedFGraphAutomorphism BoolLensGraph) := ⊤

def boolLensVisibleIdentity : BoolLensVisibleGroup :=
  ⟨boolLensIdentityAutomorphism, trivial⟩

def boolLensVisibleFlip : BoolLensVisibleGroup :=
  ⟨boolLensFlipAutomorphism, trivial⟩

/-- The fixed map `h(v,k)=(v,k xor v)`. -/
def boolLensTwistChange :
    FixedFFollowingStateChange BoolLensGraph Bool
      boolLensIdentityAutomorphism :=
  FixedFFollowingStateChange.ofFamily (fun visible =>
    { toFun := fun hidden => Bool.xor hidden visible
      invFun := fun hidden => Bool.xor hidden visible
      left_inv := by intro hidden; cases visible <;> cases hidden <;> rfl
      right_inv := by intro hidden; cases visible <;> cases hidden <;> rfl })

theorem boolLensTwistChange_apply (visible hidden : Bool) :
    boolLensTwistChange.h (visible, hidden) =
      (visible, Bool.xor hidden visible) := by
  rfl

theorem boolLensTwist_preserves_get (state : Bool × Bool) :
    productGet (boolLensTwistChange.h state) = productGet state := by
  rcases state with ⟨visible, hidden⟩
  rfl

/-- Updating `(false,false)` to `true` and then applying `h` gives the first
order required by the fixed example. -/
theorem boolLensTwist_after_put :
    boolLensTwistChange.h (productPut (false, false) true) =
      (true, true) := by
  rfl

/-- Applying `h` first and then updating to `true` gives the second order. -/
theorem boolLensPut_after_twist :
    productPut (boolLensTwistChange.h (false, false)) true =
      (true, false) := by
  rfl

theorem boolLensTwist_does_not_preserve_put :
    ¬ boolLensTwistChange.PreservesNamedOperations := by
  intro preserves
  have equality := preserves (false, true) false
  have hiddenEquality := congrArg Prod.snd equality
  exact Bool.noConfusion hiddenEquality

theorem boolLens_get_count_identity :
    Nat.card
        (FixedFFollowingStateChange BoolLensGraph Bool
          boolLensIdentityAutomorphism) = 4 := by
  rw [natCard_followingStateChange
    (F := BoolLensGraph) (K := Bool), natCard_boolLensVertex]
  norm_num

theorem boolLens_get_count_flip :
    Nat.card
        (FixedFFollowingStateChange BoolLensGraph Bool
          boolLensFlipAutomorphism) = 4 := by
  rw [natCard_followingStateChange
    (F := BoolLensGraph) (K := Bool), natCard_boolLensVertex]
  norm_num

theorem boolLens_get_put_count_identity :
    Nat.card
        (ProjectionFiber (K := Bool) BoolLensVisibleGroup
          boolLensVisibleIdentity) = 2 := by
  rw [natCard_projectionFiber (F := BoolLensGraph) (K := Bool),
    natCard_completeUpdateComponent false]
  norm_num

theorem boolLens_get_put_count_flip :
    Nat.card
        (ProjectionFiber (K := Bool) BoolLensVisibleGroup
          boolLensVisibleFlip) = 2 := by
  rw [natCard_projectionFiber (F := BoolLensGraph) (K := Bool),
    natCard_completeUpdateComponent false]
  norm_num

/-! ### Fixed selected-value-preserving product-lens example -/

def pointedLensFiberFamily (visible : Bool) : Equiv.Perm (Fin 3) :=
  if visible then Equiv.swap 1 2 else 1

def pointedLensTwistChange :
    FixedFFollowingStateChange BoolLensGraph (Fin 3)
      boolLensIdentityAutomorphism :=
  FixedFFollowingStateChange.ofFamily pointedLensFiberFamily

theorem pointedLensTwist_apply_false (hidden : Fin 3) :
    pointedLensTwistChange.h (false, hidden) = (false, hidden) := by
  rfl

theorem pointedLensTwist_apply_true (hidden : Fin 3) :
    pointedLensTwistChange.h (true, hidden) =
      (true, Equiv.swap (1 : Fin 3) 2 hidden) := by
  rfl

theorem pointedLensTwist_preserves_get (state : Bool × Fin 3) :
    productGet (pointedLensTwistChange.h state) = productGet state := by
  rcases state with ⟨visible, hidden⟩
  rfl

theorem pointedLensTwist_preserves_section (visible : Bool) :
    pointedLensTwistChange.h (visible, (0 : Fin 3)) = (visible, 0) := by
  cases visible with
  | false => rfl
  | true =>
      apply Prod.ext
      · rfl
      · change (Equiv.swap (1 : Fin 3) 2) 0 = 0
        decide

theorem pointedLensTwist_after_put :
    pointedLensTwistChange.h
        (productPut (false, (1 : Fin 3)) true) = (true, 2) := by
  simp [pointedLensTwistChange, pointedLensFiberFamily,
    FixedFFollowingStateChange.ofFamily, boolLensIdentityAutomorphism,
    completeUpdateAutomorphism, productPut]

theorem pointedLensPut_after_twist :
    productPut
        (pointedLensTwistChange.h (false, (1 : Fin 3))) true =
      (true, 1) := by
  rfl

theorem pointedLensTwist_does_not_preserve_put :
    ¬ pointedLensTwistChange.PreservesNamedOperations := by
  intro preserves
  have equality := preserves (false, true) (1 : Fin 3)
  have hiddenEquality := congrArg Prod.snd equality
  exact (by decide : (2 : Fin 3) ≠ 1) hiddenEquality

/-- A constant nonidentity hidden swap preserves all update operations and the
selected section. -/
def pointedLensConstantSwapChange :
    FixedFFollowingStateChange BoolLensGraph (Fin 3)
      boolLensIdentityAutomorphism :=
  FixedFFollowingStateChange.ofFamily (fun _ => Equiv.swap 1 2)

theorem pointedLensConstantSwap_preserves_operations :
    pointedLensConstantSwapChange.PreservesNamedOperations := by
  rw [FixedFFollowingStateChange.preservesNamedOperations_iff]
  intro namedEdge
  rfl

theorem pointedLensConstantSwap_preserves_section (visible : Bool) :
    pointedLensConstantSwapChange.h (visible, (0 : Fin 3)) =
      (visible, 0) := by
  simp [pointedLensConstantSwapChange,
    FixedFFollowingStateChange.ofFamily, boolLensIdentityAutomorphism,
    completeUpdateAutomorphism]
  decide

theorem pointedLensTwist_nonidentity :
    pointedLensTwistChange.h ≠ Equiv.refl (Bool × Fin 3) := by
  intro equality
  have moved := congrArg (fun e : (Bool × Fin 3) ≃ (Bool × Fin 3) =>
    e (true, (1 : Fin 3))) equality
  exact (by decide : (true, (2 : Fin 3)) ≠ (true, 1)) moved

theorem pointedLensConstantSwap_nonidentity :
    pointedLensConstantSwapChange.h ≠ Equiv.refl (Bool × Fin 3) := by
  intro equality
  have moved := congrArg (fun e : (Bool × Fin 3) ≃ (Bool × Fin 3) =>
    e (false, (1 : Fin 3))) equality
  exact (by decide : (false, (2 : Fin 3)) ≠ (false, 1)) moved

theorem pointedLens_get_section_count :
    Nat.card
        (PointedFollowingStateChange BoolLensGraph (Fin 3) 0
          boolLensIdentityAutomorphism) = 4 := by
  rw [natCard_pointedFollowingStateChange
    (F := BoolLensGraph) (K := Fin 3), natCard_boolLensVertex]
  norm_num

theorem pointedLens_get_put_section_count :
    Nat.card
        (PointedProjectionFiber BoolLensVisibleGroup (0 : Fin 3)
          boolLensVisibleIdentity) = 2 := by
  rw [natCard_pointedProjectionFiber (F := BoolLensGraph) (K := Fin 3),
    natCard_completeUpdateComponent false]
  norm_num

/-! ## Fixed two-session protocol example -/

def protocolGraph : FixedFDirectedMultigraph where
  Vertex := Fin 4
  Edge := Bool
  source
    | false => 0
    | true => 2
  target
    | false => 1
    | true => 3

instance : Finite protocolGraph.Vertex := by
  change Finite (Fin 4)
  infer_instance

instance : Fintype protocolGraph.Vertex := by
  change Fintype (Fin 4)
  infer_instance

theorem natCard_protocolVertex : Nat.card protocolGraph.Vertex = 4 := by
  change Nat.card (Fin 4) = 4
  norm_num

def protocolIdentityAutomorphism : FixedFGraphAutomorphism protocolGraph := 1

def protocolVertexSwap : Equiv.Perm (Fin 4) where
  toFun value := ![(2 : Fin 4), 3, 0, 1] value
  invFun value := ![(2 : Fin 4), 3, 0, 1] value
  left_inv value := by fin_cases value <;> rfl
  right_inv value := by fin_cases value <;> rfl

def protocolEdgeSwap : Equiv.Perm Bool := Equiv.swap false true

def protocolSessionSwapAutomorphism :
    FixedFGraphAutomorphism protocolGraph where
  vertex := protocolVertexSwap
  edge := protocolEdgeSwap
  source_rename namedEdge := by
    cases namedEdge <;>
      simp [protocolGraph, protocolEdgeSwap, protocolVertexSwap]
  target_rename namedEdge := by
    cases namedEdge <;>
      simp [protocolGraph, protocolEdgeSwap, protocolVertexSwap]

abbrev ProtocolVisibleGroup :
    Subgroup (FixedFGraphAutomorphism protocolGraph) := ⊤

def protocolVisibleIdentity : ProtocolVisibleGroup :=
  ⟨protocolIdentityAutomorphism, trivial⟩

def protocolVisibleSessionSwap : ProtocolVisibleGroup :=
  ⟨protocolSessionSwapAutomorphism, trivial⟩

/-- The canonical lift of the visible session exchange; its hidden action is
the identity and its actual operation adapter still renames the two edges. -/
def protocolSessionSwapLift :
    FixedFRestrictedAutomorphism.FollowingGroup
      (K := Bool) ProtocolVisibleGroup :=
  FixedFRestrictedAutomorphism.canonicalSection
    (K := Bool) ProtocolVisibleGroup
    protocolVisibleSessionSwap

theorem protocolSessionSwapLift_fiberPerm (vertex : Fin 4) :
    protocolSessionSwapLift.1.fiberPerm vertex = 1 := by
  change
    (FixedFPreservingFollowingPair.visibleRename
      (K := Bool) protocolSessionSwapAutomorphism).fiberPerm vertex = 1
  exact FixedFPreservingFollowingPair.visibleRename_fiberPerm
    protocolSessionSwapAutomorphism vertex

theorem protocolSessionSwap_operationMap_false (hidden : Bool) :
    protocolSessionSwapLift.1.change.operationMap (false, hidden) =
      (true, hidden) := by
  apply Prod.ext
  · simp [protocolSessionSwapLift,
      FixedFRestrictedAutomorphism.canonicalSection,
      FixedFPreservingFollowingPair.visibleRenameSection,
      FixedFPreservingFollowingPair.visibleRename,
      FixedFFollowingStateChange.operationMap, protocolVisibleSessionSwap,
      protocolSessionSwapAutomorphism, protocolEdgeSwap]
  · change protocolSessionSwapLift.1.fiberPerm
        (protocolGraph.source false) hidden = hidden
    rw [protocolSessionSwapLift_fiberPerm]
    rfl

theorem protocolSessionSwap_operationMap_true (hidden : Bool) :
    protocolSessionSwapLift.1.change.operationMap (true, hidden) =
      (false, hidden) := by
  apply Prod.ext
  · simp [protocolSessionSwapLift,
      FixedFRestrictedAutomorphism.canonicalSection,
      FixedFPreservingFollowingPair.visibleRenameSection,
      FixedFPreservingFollowingPair.visibleRename,
      FixedFFollowingStateChange.operationMap, protocolVisibleSessionSwap,
      protocolSessionSwapAutomorphism, protocolEdgeSwap]
  · change protocolSessionSwapLift.1.fiberPerm
        (protocolGraph.source true) hidden = hidden
    rw [protocolSessionSwapLift_fiberPerm]
    rfl

def protocolComponentLabel : Fin 4 → Bool
  | 0 | 1 => false
  | 2 | 3 => true

theorem protocolComponentLabel_edge (namedEdge : protocolGraph.Edge) :
    protocolComponentLabel (protocolGraph.source namedEdge) =
      protocolComponentLabel (protocolGraph.target namedEdge) := by
  cases namedEdge <;> rfl

theorem protocolComponentLabel_reachable {first second : Fin 4}
    (reachable : FixedFUndirectedReachable protocolGraph first second) :
    protocolComponentLabel first = protocolComponentLabel second := by
  induction reachable with
  | rel first second step =>
      obtain ⟨namedEdge, sourceEquality, targetEquality⟩ := step
      subst first
      subst second
      exact protocolComponentLabel_edge namedEdge
  | refl vertex => rfl
  | symm first second relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans first second third firstRelation secondRelation firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

def protocolComponentEquivBool : FixedFComponent protocolGraph ≃ Bool where
  toFun := Quotient.lift protocolComponentLabel
    (fun _ _ reachable => protocolComponentLabel_reachable reachable)
  invFun label :=
    if label then fixedFComponentMk protocolGraph (2 : Fin 4)
    else fixedFComponentMk protocolGraph (0 : Fin 4)
  left_inv component := by
    refine Quotient.inductionOn component ?_
    intro vertex
    change Fin 4 at vertex
    fin_cases vertex
    · rfl
    · change fixedFComponentMk protocolGraph (0 : Fin 4) =
        fixedFComponentMk protocolGraph (1 : Fin 4)
      exact fixedFComponent_source_eq_target protocolGraph false
    · rfl
    · change fixedFComponentMk protocolGraph (2 : Fin 4) =
        fixedFComponentMk protocolGraph (3 : Fin 4)
      exact fixedFComponent_source_eq_target protocolGraph true
  right_inv label := by cases label <;> rfl

theorem natCard_protocolComponent :
    Nat.card (FixedFComponent protocolGraph) = 2 := by
  rw [Nat.card_congr protocolComponentEquivBool]
  norm_num

theorem protocol_observation_count_identity :
    Nat.card
        (FixedFFollowingStateChange protocolGraph Bool
          protocolIdentityAutomorphism) = 16 := by
  rw [natCard_followingStateChange
    (F := protocolGraph) (K := Bool), natCard_protocolVertex]
  norm_num

theorem protocol_operation_count_identity :
    Nat.card
        (ProjectionFiber (K := Bool) ProtocolVisibleGroup
          protocolVisibleIdentity) = 4 := by
  rw [natCard_projectionFiber (F := protocolGraph) (K := Bool),
    natCard_protocolComponent]
  norm_num

theorem protocol_operation_count_sessionSwap :
    Nat.card
        (ProjectionFiber (K := Bool) ProtocolVisibleGroup
          protocolVisibleSessionSwap) = 4 := by
  rw [natCard_projectionFiber (F := protocolGraph) (K := Bool),
    natCard_protocolComponent]
  norm_num

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFFiniteExamples

end AAT.AG.RealizationReconstruction
