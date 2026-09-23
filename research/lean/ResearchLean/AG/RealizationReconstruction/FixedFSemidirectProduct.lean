import ResearchLean.AG.RealizationReconstruction.FixedFFiniteExamples
import Mathlib.GroupTheory.SemidirectProduct
import Formal.Util.AssertStandardAxioms

/-!
# Component reindexing and the fixed-graph semidirect product

The visible subgroup is supplied independently. Its proved action on the
generated component quotient acts on component-indexed hidden permutations
by inverse reindexing.  The isomorphism below sends a destination-indexed
family and a visible automorphism to the actual state change which first
renames the visible state and then applies the chosen hidden permutation.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFSemidirectProduct

open FixedFRestrictedAutomorphism
open FixedFRestrictedKernelIdentification

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- The hidden permutation group indexed by components of the graph in Theorem 7.25. -/
abbrev ComponentGroup (F : FixedFDirectedMultigraph) (K : Type w) :=
  FixedFComponent F → Equiv.Perm K

/-- The action in (7.43), indexed at the destination component. -/
def reindex (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    ComponentGroup F K ≃* ComponentGroup F K where
  toFun family component :=
    family ((FixedFGraphAutomorphism.restrictedComponentAction H visible)⁻¹ component)
  invFun family component :=
    family (FixedFGraphAutomorphism.restrictedComponentAction H visible component)
  left_inv family := by
    funext component
    simp
  right_inv family := by
    funext component
    simp
  map_mul' first second := by
    funext component
    rfl

/-- The reindexing maps compose in the visible group order. -/
def componentAction (H : Subgroup (FixedFGraphAutomorphism F)) :
    H →* MulAut (ComponentGroup F K) where
  toFun := reindex H
  map_one' := by
    apply MulEquiv.ext
    intro family
    funext component
    simp [reindex]
  map_mul' first second := by
    apply MulEquiv.ext
    intro family
    funext component
    simp [reindex, mul_inv_rev]

/-- Theorem 7.25 uses this semidirect product with the proved component action. -/
abbrev Semidirect (H : Subgroup (FixedFGraphAutomorphism F)) :=
  ComponentGroup F K ⋊[componentAction (K := K) H] H

/-- Concrete interpretation of a semidirect pair as an actual preserving change. -/
def realize (H : Subgroup (FixedFGraphAutomorphism F))
    (entry : Semidirect (K := K) H) : FollowingGroup (K := K) H :=
  componentKernelHom (K := K) H entry.left *
    canonicalSection (K := K) H entry.right

/-- The hidden permutation is evaluated at the destination component. -/
theorem realize_fiberPerm
    (H : Subgroup (FixedFGraphAutomorphism F))
    (entry : Semidirect (K := K) H) (vertex : F.Vertex) :
    (realize H entry).1.fiberPerm vertex =
      entry.left
        (entry.right.1.componentPerm (fixedFComponentMk F vertex)) := by
  change
    ((componentKernelHom (K := K) H entry.left).1 *
      (canonicalSection (K := K) H entry.right).1).fiberPerm vertex = _
  rw [FixedFPreservingFollowingPair.mul_fiberPerm,
    componentKernelHom_fiberPerm]
  change entry.left (fixedFComponentMk F (entry.right.1.vertex vertex)) *
      (FixedFPreservingFollowingPair.visibleRename entry.right.1).fiberPerm vertex = _
  rw [FixedFPreservingFollowingPair.visibleRename_fiberPerm]
  simp [FixedFGraphAutomorphism.componentPerm_mk]

/-- Equality of actual changes follows from their visible projections and
their constructed fiber permutations. -/
theorem actual_ext
    (H : Subgroup (FixedFGraphAutomorphism F))
    {first second : FollowingGroup (K := K) H}
    (visible : projection (K := K) H first = projection (K := K) H second)
    (fibers : ∀ vertex, first.1.fiberPerm vertex = second.1.fiberPerm vertex) :
    first = second := by
  apply Subtype.ext
  apply FixedFPreservingFollowingPair.ext
  · exact congrArg Subtype.val visible
  · apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    change first.1.change.h (vertex, hidden) =
      second.1.change.h (vertex, hidden)
    rw [first.1.change.factorization, second.1.change.factorization]
    have visibleEquality : first.1.automorphism =
        second.1.automorphism := congrArg Subtype.val visible
    have fiberEquality : first.1.change.fiberPerm vertex =
        second.1.change.fiberPerm vertex := fibers vertex
    exact Prod.ext
      (congrArg (fun automorphism => automorphism.vertex vertex) visibleEquality)
      (congrArg (fun permutation : Equiv.Perm K => permutation hidden)
        fiberEquality)

/-- The realization preserves the semidirect multiplication. -/
def realizeHom (H : Subgroup (FixedFGraphAutomorphism F)) :
    Semidirect (K := K) H →* FollowingGroup (K := K) H where
  toFun := realize H
  map_one' := by
    apply actual_ext (K := K) H
    · apply Subtype.ext
      rfl
    · intro vertex
      rw [realize_fiberPerm]
      rfl
  map_mul' first second := by
    apply actual_ext (K := K) H
    · apply Subtype.ext
      rfl
    · intro vertex
      change (realize H (first * second)).1.fiberPerm vertex =
        ((realize H first).1 * (realize H second).1).fiberPerm vertex
      rw [realize_fiberPerm, FixedFPreservingFollowingPair.mul_fiberPerm,
        realize_fiberPerm, realize_fiberPerm]
      change
        (first.left * componentAction (K := K) H first.right second.left)
            ((first.right * second.right).1.componentPerm
              (fixedFComponentMk F vertex)) =
          first.left (first.right.1.componentPerm
              (second.right.1.componentPerm (fixedFComponentMk F vertex))) *
            second.left (second.right.1.componentPerm
              (fixedFComponentMk F vertex))
      have componentMul :
          (first.right.1 * second.right.1).componentPerm =
            first.right.1.componentPerm * second.right.1.componentPerm := by
        exact (FixedFGraphAutomorphism.componentAction (F := F)).map_mul
          first.right.1 second.right.1
      change
        (first.left * componentAction (K := K) H first.right second.left)
            ((first.right.1 * second.right.1).componentPerm
              (fixedFComponentMk F vertex)) = _
      rw [componentMul]
      simp [componentAction, reindex,
        FixedFGraphAutomorphism.restrictedComponentAction,
        FixedFGraphAutomorphism.componentAction]

/-- The canonical component-family decomposition is onto every actual change. -/
theorem realize_surjective
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    Function.Surjective (realizeHom (K := K) H) := by
  intro actual
  let visible := projection (K := K) H actual
  let family : ComponentGroup F K := fun component =>
    componentFamilyOfPair actual.1
      ((FixedFGraphAutomorphism.restrictedComponentAction H visible)⁻¹ component)
  refine ⟨⟨family, visible⟩, ?_⟩
  apply actual_ext (K := K) H
  · apply Subtype.ext
    rfl
  · intro vertex
    change (realize H
      (⟨family, visible⟩ : Semidirect (K := K) H)).1.fiberPerm vertex =
        actual.1.fiberPerm vertex
    rw [realize_fiberPerm]
    change family (visible.1.componentPerm (fixedFComponentMk F vertex)) =
      actual.1.fiberPerm vertex
    simp only [family, FixedFGraphAutomorphism.restrictedComponentAction,
      MonoidHom.comp_apply, Subgroup.subtype_apply,
      FixedFGraphAutomorphism.componentAction]
    change componentFamilyOfPair actual.1
        (visible.1.componentPerm.symm
          (visible.1.componentPerm (fixedFComponentMk F vertex))) = _
    rw [Equiv.symm_apply_apply]
    exact componentFamilyOfPair_mk actual.1 vertex

/-- Destination-indexed families are read faithfully from actual state maps. -/
theorem realize_injective
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    Function.Injective (realizeHom (K := K) H) := by
  intro first second equal
  apply SemidirectProduct.ext
  · funext component
    refine Quotient.inductionOn component ?_
    intro vertex
    have rightEqual : first.right = second.right := by
      have eqProj := congrArg (projection (K := K) H) equal
      exact eqProj
    have fiberEqual := congrArg
      (fun actual : FollowingGroup (K := K) H =>
        actual.1.fiberPerm
          (first.right.1.vertex.symm vertex)) equal
    change (realize H first).1.fiberPerm _ =
      (realize H second).1.fiberPerm _ at fiberEqual
    rw [realize_fiberPerm, realize_fiberPerm] at fiberEqual
    simpa [rightEqual, FixedFGraphAutomorphism.componentPerm_mk] using fiberEqual
  · exact congrArg (projection (K := K) H) equal

/-- Fixed-source theorem 7.25, equation (7.43), for every supplied visible
subgroup and the actual operation-preserving following-change group. -/
noncomputable def actualEquivSemidirect
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    FollowingGroup (K := K) H ≃* Semidirect (K := K) H :=
  (MulEquiv.ofBijective (realizeHom (K := K) H)
    ⟨realize_injective (K := K) H, realize_surjective (K := K) H⟩).symm

/-! ## The selected-state version of corollary 7.26 -/

open FixedFPointedSplitExactSequenceAndTorsor

/-- The same component action restricts to point stabilizers because
reindexing changes the component, not the hidden permutation. -/
def pointedReindex (H : Subgroup (FixedFGraphAutomorphism F))
    (basepoint : K) (visible : H) :
    PointedComponentGroup F K basepoint ≃*
      PointedComponentGroup F K basepoint where
  toFun family component :=
    family ((FixedFGraphAutomorphism.restrictedComponentAction H visible)⁻¹ component)
  invFun family component :=
    family (FixedFGraphAutomorphism.restrictedComponentAction H visible component)
  left_inv family := by funext component; simp
  right_inv family := by funext component; simp
  map_mul' first second := by funext component; rfl

/-- Corollary 7.26 restricts the component action to permutations fixing the chosen state. -/
def pointedComponentAction
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    H →* MulAut (PointedComponentGroup F K basepoint) where
  toFun := pointedReindex H basepoint
  map_one' := by
    apply MulEquiv.ext
    intro family
    funext component
    simp [pointedReindex]
  map_mul' first second := by
    apply MulEquiv.ext
    intro family
    funext component
    simp [pointedReindex, mul_inv_rev]

/-- The semidirect product in Corollary 7.26 for the given hidden-state basepoint. -/
abbrev PointedSemidirect
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :=
  PointedComponentGroup F K basepoint ⋊[pointedComponentAction H basepoint] H

/-- Forgetting point-stabilizer proofs commutes with component reindexing. -/
def forgetPointedSemidirect
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    PointedSemidirect H basepoint →* Semidirect (K := K) H where
  toFun entry :=
    ⟨forgetPointedComponentGroup basepoint entry.left, entry.right⟩
  map_one' := by
    apply SemidirectProduct.ext <;> rfl
  map_mul' first second := by
    apply SemidirectProduct.ext
    · funext component
      rfl
    · rfl

/-- This API lemma preserves the pointed subgroup when comparing concrete changes. -/
theorem forgetPointedSemidirect_injective
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    Function.Injective (forgetPointedSemidirect H basepoint) := by
  intro first second equality
  apply SemidirectProduct.ext
  · funext component
    apply Subtype.ext
    exact congrFun (congrArg SemidirectProduct.left equality) component
  · exact congrArg
      (fun entry : Semidirect (K := K) H => entry.right) equality

/-- Pointed pairs are realized by the same concrete state equivalence. -/
def pointedRealizeHom
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    PointedSemidirect H basepoint →*
      PointedFollowingGroup H basepoint where
  toFun entry :=
    ⟨realizeHom (K := K) H (forgetPointedSemidirect H basepoint entry), by
      intro vertex
      change (realize H
        (forgetPointedSemidirect H basepoint entry)).1.fiberPerm vertex
          basepoint = basepoint
      rw [realize_fiberPerm]
      exact (entry.left
        (entry.right.1.componentPerm (fixedFComponentMk F vertex))).2⟩
  map_one' := by
    apply Subtype.ext
    change realizeHom (K := K) H
      (forgetPointedSemidirect H basepoint 1) = 1
    rw [map_one, map_one]
  map_mul' first second := by
    apply Subtype.ext
    change realizeHom (K := K) H
      (forgetPointedSemidirect H basepoint (first * second)) =
      realizeHom (K := K) H (forgetPointedSemidirect H basepoint first) *
        realizeHom (K := K) H (forgetPointedSemidirect H basepoint second)
    rw [map_mul, map_mul]

/-- Injectivity of the concrete pointed realization used in Corollary 7.26. -/
theorem pointedRealize_injective
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    Function.Injective (pointedRealizeHom H basepoint) := by
  intro first second equality
  apply forgetPointedSemidirect_injective H basepoint
  apply realize_injective (K := K) H
  exact congrArg Subtype.val equality

/-- Every pointed operation-preserving change yields the component family required by Corollary 7.26. -/
theorem pointedRealize_surjective
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    Function.Surjective (pointedRealizeHom H basepoint) := by
  intro actual
  let visible := pointedProjection H basepoint actual
  let family : PointedComponentGroup F K basepoint := fun component =>
    ⟨componentFamilyOfPair actual.1.1
        ((FixedFGraphAutomorphism.restrictedComponentAction H visible)⁻¹ component),
      by
        refine Quotient.inductionOn component ?_
        intro vertex
        change actual.1.1.fiberPerm
          (visible.1.vertex.symm vertex) basepoint = basepoint
        exact actual.2 _⟩
  refine ⟨⟨family, visible⟩, ?_⟩
  apply Subtype.ext
  apply actual_ext (K := K) H
  · apply Subtype.ext
    rfl
  · intro vertex
    change
      (realize H
        (forgetPointedSemidirect H basepoint
          (⟨family, visible⟩ : PointedSemidirect H basepoint))).1.fiberPerm vertex =
        actual.1.1.fiberPerm vertex
    rw [realize_fiberPerm]
    change (family (visible.1.componentPerm (fixedFComponentMk F vertex))).1 =
      actual.1.1.fiberPerm vertex
    simp only [family, FixedFGraphAutomorphism.restrictedComponentAction,
      MonoidHom.comp_apply, Subgroup.subtype_apply,
      FixedFGraphAutomorphism.componentAction]
    change componentFamilyOfPair actual.1.1
        (visible.1.componentPerm.symm
          (visible.1.componentPerm (fixedFComponentMk F vertex))) = _
    rw [Equiv.symm_apply_apply]
    exact componentFamilyOfPair_mk actual.1.1 vertex

/-- Fixed-source corollary 7.26: each component factor is the actual point
stabilizer in `Sym(K)`, with the same inverse-reindexing action. -/
noncomputable def pointedActualEquivSemidirect
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    PointedFollowingGroup H basepoint ≃*
      PointedSemidirect H basepoint :=
  (MulEquiv.ofBijective (pointedRealizeHom H basepoint)
    ⟨pointedRealize_injective H basepoint,
      pointedRealize_surjective H basepoint⟩).symm

/-! ## The two-worker finite protocol of example 7.30 -/

namespace TwoWorkers

open FixedFFiniteExamples

/-- The two-worker visible exchange of Example 7.30 has order two. -/
private theorem sessionSwap_mul_self :
    protocolSessionSwapAutomorphism * protocolSessionSwapAutomorphism = 1 := by
  apply FixedFGraphAutomorphism.ext
  · apply Equiv.ext
    intro vertex
    fin_cases vertex <;>
      rfl
  · apply Equiv.ext
    intro edge
    cases edge <;> rfl

/-- The inverse of the two-worker exchange is itself, for the visible subgroup construction. -/
private theorem sessionSwap_inv :
    protocolSessionSwapAutomorphism⁻¹ = protocolSessionSwapAutomorphism := by
  calc
    protocolSessionSwapAutomorphism⁻¹ =
        protocolSessionSwapAutomorphism⁻¹ * 1 := (mul_one _).symm
    _ = protocolSessionSwapAutomorphism⁻¹ *
          (protocolSessionSwapAutomorphism * protocolSessionSwapAutomorphism) := by
      rw [sessionSwap_mul_self]
    _ = protocolSessionSwapAutomorphism := by group

/-- Exactly the two allowed visible changes: identity and worker exchange. -/
def visibleGroup : Subgroup (FixedFGraphAutomorphism protocolGraph) where
  carrier := { change | change = 1 ∨ change = protocolSessionSwapAutomorphism }
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro first second firstMem secondMem
    rcases firstMem with rfl | rfl <;>
      rcases secondMem with rfl | rfl
    · left; simp
    · right; simp
    · right; simp
    · left; exact sessionSwap_mul_self
  inv_mem' := by
    intro change changeMem
    rcases changeMem with rfl | rfl
    · left; simp
    · right; exact sessionSwap_inv

/-- The identity visible change in the two-worker model of Example 7.30. -/
def visibleIdentity : visibleGroup := ⟨1, Or.inl rfl⟩

/-- The concrete worker-exchange visible change of Example 7.30. -/
def visibleSwap : visibleGroup :=
  ⟨protocolSessionSwapAutomorphism, Or.inr rfl⟩

/-- Worker exchange differs from the identity on the first control vertex. -/
private theorem swap_ne_one : visibleSwap ≠ visibleIdentity := by
  intro equality
  have vertexEquality := congrArg
    (fun change : visibleGroup => change.1.vertex (0 : Fin 4)) equality
  change (2 : Fin 4) = 0 at vertexEquality
  exact (by decide : (2 : Fin 4) ≠ 0) vertexEquality

/-- The worker exchange swaps the two generated components. -/
theorem swap_component (component : FixedFComponent protocolGraph) :
    (FixedFGraphAutomorphism.restrictedComponentAction visibleGroup visibleSwap
      component) =
      protocolComponentEquivBool.symm
        (!(protocolComponentEquivBool component)) := by
  apply protocolComponentEquivBool.injective
  refine Quotient.inductionOn component ?_
  intro vertex
  fin_cases vertex <;>
    rfl

/-- There are exactly two visible changes. -/
noncomputable def visibleEquivBool : visibleGroup ≃ Bool := by
  classical
  refine {
    toFun := fun change => if change = visibleIdentity then false else true
    invFun := fun value => if value then visibleSwap else visibleIdentity
    left_inv := ?_
    right_inv := ?_ }
  · intro change
    rcases change.2 with equalIdentity | equalSwap
    · have : change = visibleIdentity := Subtype.ext equalIdentity
      subst change
      simp
    · have : change = visibleSwap := Subtype.ext equalSwap
      subst change
      simp [swap_ne_one]
  · intro value
    cases value <;> simp [swap_ne_one]

/-- The visible subgroup in Example 7.30 has the two required elements. -/
theorem natCard_visibleGroup : Nat.card visibleGroup = 2 := by
  rw [Nat.card_congr visibleEquivBool]
  norm_num

/-- The two-worker visible group is the genuine permutation group on its
two component labels, not merely a two-element set. -/
def visiblePermutationHom : visibleGroup →* Equiv.Perm Bool :=
  (protocolComponentEquivBool.permCongrHom).toMonoidHom.comp
    (FixedFGraphAutomorphism.restrictedComponentAction visibleGroup)

/-- Worker exchange acts as the nontrivial permutation of the two components. -/
theorem visiblePermutationHom_swap :
    visiblePermutationHom visibleSwap = Equiv.swap false true := by
  apply Equiv.ext
  intro label
  cases label <;>
    rfl

/-- The two allowed visible changes are distinguished by their action on components. -/
theorem visiblePermutationHom_injective :
    Function.Injective visiblePermutationHom := by
  intro first second equality
  rcases first.2 with firstIdentity | firstSwap <;>
    rcases second.2 with secondIdentity | secondSwap
  · exact Subtype.ext (firstIdentity.trans secondIdentity.symm)
  · have firstEq : first = visibleIdentity := Subtype.ext firstIdentity
    have secondEq : second = visibleSwap := Subtype.ext secondSwap
    rw [firstEq, secondEq] at equality
    change visiblePermutationHom (1 : visibleGroup) =
      visiblePermutationHom visibleSwap at equality
    rw [map_one, visiblePermutationHom_swap] at equality
    have impossible := congrArg (fun p : Equiv.Perm Bool => p false) equality
    cases impossible
  · have firstEq : first = visibleSwap := Subtype.ext firstSwap
    have secondEq : second = visibleIdentity := Subtype.ext secondIdentity
    rw [firstEq, secondEq] at equality
    change visiblePermutationHom visibleSwap =
      visiblePermutationHom (1 : visibleGroup) at equality
    rw [map_one, visiblePermutationHom_swap] at equality
    have impossible := congrArg (fun p : Equiv.Perm Bool => p false) equality
    cases impossible
  · exact Subtype.ext (firstSwap.trans secondSwap.symm)

/-- Example 7.30 identifies its visible group with the genuine group S2. -/
noncomputable def visibleEquivPermBool :
    visibleGroup ≃* Equiv.Perm Bool := by
  classical
  letI : Finite visibleGroup :=
    Finite.of_injective visibleEquivBool visibleEquivBool.injective
  letI : Fintype visibleGroup := Fintype.ofFinite visibleGroup
  refine MulEquiv.ofBijective visiblePermutationHom ?_
  apply (Fintype.bijective_iff_injective_and_card
    visiblePermutationHom).2
  constructor
  · exact visiblePermutationHom_injective
  · calc
      Fintype.card visibleGroup = 2 := by
        rw [Fintype.card_congr visibleEquivBool]
        decide
      _ = Fintype.card (Equiv.Perm Bool) := by
        rw [Fintype.card_perm]
        decide

/-- The two component-indexed hidden factors are evaluated at the actual
component classes represented by vertices 0 and 2. -/
def componentPairEquiv :
    ComponentGroup protocolGraph Bool ≃*
      (Equiv.Perm Bool × Equiv.Perm Bool) where
  toFun family :=
    (family (protocolComponentEquivBool.symm false),
      family (protocolComponentEquivBool.symm true))
  invFun pair component :=
    if protocolComponentEquivBool component then pair.2 else pair.1
  left_inv family := by
    funext component
    have recovered := protocolComponentEquivBool.symm_apply_apply component
    cases label : protocolComponentEquivBool component <;>
      simpa [label] using congrArg family recovered
  right_inv pair := by
    apply Prod.ext <;>
      simp
  map_mul' first second := by
    apply Prod.ext <;>
      rfl

/-- Worker exchange interchanges exactly the two hidden `S₂` factors. -/
theorem componentPair_swap (family : ComponentGroup protocolGraph Bool) :
    componentPairEquiv (componentAction (K := Bool) visibleGroup visibleSwap family) =
      (componentPairEquiv family).swap := by
  apply Prod.ext
  · change family
        ((FixedFGraphAutomorphism.restrictedComponentAction visibleGroup
          visibleSwap)⁻¹ (protocolComponentEquivBool.symm false)) =
        family (protocolComponentEquivBool.symm true)
    rw [show
      (FixedFGraphAutomorphism.restrictedComponentAction visibleGroup
        visibleSwap)⁻¹ =
          FixedFGraphAutomorphism.restrictedComponentAction visibleGroup
            visibleSwap from by
      apply Equiv.ext
      intro component
      rw [← map_inv, show visibleSwap⁻¹ = visibleSwap from by
        apply Subtype.ext
        exact sessionSwap_inv]
      ]
    rw [swap_component]
    rfl
  · change family
        ((FixedFGraphAutomorphism.restrictedComponentAction visibleGroup
          visibleSwap)⁻¹ (protocolComponentEquivBool.symm true)) =
        family (protocolComponentEquivBool.symm false)
    rw [show
      (FixedFGraphAutomorphism.restrictedComponentAction visibleGroup
        visibleSwap)⁻¹ =
          FixedFGraphAutomorphism.restrictedComponentAction visibleGroup
            visibleSwap from by
      apply Equiv.ext
      intro component
      rw [← map_inv, show visibleSwap⁻¹ = visibleSwap from by
        apply Subtype.ext
        exact sessionSwap_inv]
      ]
    rw [swap_component]
    rfl

/-- The two componentwise S2 factors in the kernel of Example 7.30. -/
abbrev HiddenPair := Equiv.Perm Bool × Equiv.Perm Bool

/-- The visible action on the explicit pair of hidden permutation factors. -/
def hiddenPairAction : visibleGroup →* MulAut HiddenPair where
  toFun visible :=
    (componentPairEquiv.symm.trans
      (componentAction (K := Bool) visibleGroup visible)).trans
        componentPairEquiv
  map_one' := by
    apply MulEquiv.ext
    intro pair
    simp
  map_mul' first second := by
    apply MulEquiv.ext
    intro pair
    simp [MulEquiv.trans_apply, map_mul]

/-- The worker exchange interchanges the two hidden-permutation factors. -/
theorem hiddenPairAction_swap (pair : HiddenPair) :
    hiddenPairAction visibleSwap pair = pair.swap := by
  change componentPairEquiv
      (componentAction (K := Bool) visibleGroup visibleSwap
        (componentPairEquiv.symm pair)) = pair.swap
  rw [componentPair_swap, componentPairEquiv.apply_symm_apply]

/-- An explicit `S₂ × S₂` kernel and the visible two-element group. -/
noncomputable def actualEquivHiddenPair :
    FollowingGroup (K := Bool) visibleGroup ≃*
      HiddenPair ⋊[hiddenPairAction] visibleGroup := by
  let convert : Semidirect (K := Bool) visibleGroup ≃*
      HiddenPair ⋊[hiddenPairAction] visibleGroup :=
    { toFun := fun entry => ⟨componentPairEquiv entry.left, entry.right⟩
      invFun := fun entry => ⟨componentPairEquiv.symm entry.left, entry.right⟩
      left_inv := by intro entry; ext <;> simp
      right_inv := by intro entry; ext <;> simp
      map_mul' := by
        intro first second
        apply SemidirectProduct.ext
        · change componentPairEquiv
            (first.left * componentAction (K := Bool) visibleGroup
              first.right second.left) =
              componentPairEquiv first.left *
                hiddenPairAction first.right (componentPairEquiv second.left)
          rw [map_mul]
          simp [hiddenPairAction]
        · rfl }
  exact (actualEquivSemidirect (K := Bool) visibleGroup).trans convert

/-- Identify the visible two-element group with `S₂` and transport its
proved pair-swapping action to that standard group. -/
noncomputable def permutationPairAction :
    Equiv.Perm Bool →* MulAut HiddenPair :=
  hiddenPairAction.comp visibleEquivPermBool.symm.toMonoidHom

/-- The exact worker group is `(S₂ × S₂) ⋊ S₂`, with the final `S₂`
acting by exchange of the two hidden factors. -/
noncomputable def actualEquivExplicitWorker :
    FollowingGroup (K := Bool) visibleGroup ≃*
      HiddenPair ⋊[permutationPairAction] Equiv.Perm Bool := by
  let convert : HiddenPair ⋊[hiddenPairAction] visibleGroup ≃*
      HiddenPair ⋊[permutationPairAction] Equiv.Perm Bool :=
    { toFun := fun entry => ⟨entry.left, visibleEquivPermBool entry.right⟩
      invFun := fun entry => ⟨entry.left, visibleEquivPermBool.symm entry.right⟩
      left_inv := by intro entry; ext <;> simp
      right_inv := by intro entry; ext <;> simp
      map_mul' := by
        intro first second
        apply SemidirectProduct.ext
        · change first.left * hiddenPairAction first.right second.left =
            first.left * permutationPairAction
              (visibleEquivPermBool first.right) second.left
          simp [permutationPairAction]
        · exact map_mul visibleEquivPermBool first.right second.right }
  exact actualEquivHiddenPair.trans convert

/-- The nontrivial visible S2 element swaps the hidden S2 factors in Example 7.30. -/
theorem permutationPairAction_swap (pair : HiddenPair) :
    permutationPairAction (Equiv.swap false true) pair = pair.swap := by
  have : visibleEquivPermBool visibleSwap = Equiv.swap false true :=
    visiblePermutationHom_swap
  rw [← this]
  change hiddenPairAction
    (visibleEquivPermBool.symm (visibleEquivPermBool visibleSwap)) pair = _
  rw [visibleEquivPermBool.symm_apply_apply]
  exact hiddenPairAction_swap pair

/-- The full operation-preserving worker change group is the concrete
`(S₂ × S₂) ⋊ S₂` with component exchange as its action. -/
noncomputable def actualEquivWorkerSemidirect :
    FollowingGroup (K := Bool) visibleGroup ≃*
      Semidirect (K := Bool) visibleGroup :=
  actualEquivSemidirect (K := Bool) visibleGroup

/-- The component permutation factors have four elements and the visible
worker-exchange group has two. -/
theorem natCard_workerChangeGroup :
    Nat.card (FollowingGroup (K := Bool) visibleGroup) = 8 := by
  rw [Nat.card_congr actualEquivWorkerSemidirect.toEquiv]
  rw [Nat.card_congr (SemidirectProduct.equivProd)]
  rw [Nat.card_prod,
    FixedFFiberCardinality.natCard_componentGroup,
    natCard_protocolComponent, natCard_visibleGroup]
  norm_num

end TwoWorkers

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFSemidirectProduct

end AAT.AG.RealizationReconstruction
