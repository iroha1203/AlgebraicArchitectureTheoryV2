import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualContextAction
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness
import Formal.Util.AssertStandardAxioms

/-!
# Independent finite permutation actions on source Extension values

For an independently supplied carrier `E`, every permutation of `E` acts on
the `Extension` value of every fixed finite-axis-fold source context whose
Extension carrier is equal to `E` under the classical type-equality test.
Contexts with any other Extension carrier are fixed.  The carrier test uses
classical type equality;
no semantic residual element, completed context map, or range is accepted as
syntax.

The action preserves the complete minimal context and the Extension carrier.
Because readable context morphisms ignore Extension values, the action reads
in both directions in the original source context preorder.  Canonical probe
contexts, one for every `e : E`, prove that the resulting homomorphism from the
independent finite permutation group is injective on the full source
context-object carrier.

This is a source-context action only.  It does not claim that these
permutations lift to actual normalized automorphisms, lie in the actual local
kernel, or cover any semantic residual group.
-/

namespace AAT.AG.RealizationReconstruction

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

private noncomputable abbrev FiniteAxisFoldPermutationSource :=
  finiteAxisFoldSourceGeometryPackage

private noncomputable abbrev FiniteAxisFoldPermutationSourceCore :=
  FiniteAxisFoldPermutationSource.core

/-! ## A universe-polymorphic Extension-value action -/

/-- Apply `permutation` precisely when the ambient Extension carrier is the
independently supplied type `E`; fix values on every other carrier. -/
noncomputable def finiteAxisFoldExtensionValuePermutation
    {E alpha : Type u} (permutation : Equiv.Perm E) (value : alpha) : alpha := by
  classical
  by_cases carrier_eq : alpha = E
  · exact Equiv.cast carrier_eq.symm
      (permutation (Equiv.cast carrier_eq value))
  · exact value

/-- The identity permutation fixes every value on every Extension carrier. -/
@[simp] theorem finiteAxisFoldExtensionValuePermutation_one
    {E alpha : Type u} (value : alpha) :
    finiteAxisFoldExtensionValuePermutation (1 : Equiv.Perm E) value = value := by
  classical
  by_cases carrier_eq : alpha = E
  · subst alpha
    simp [finiteAxisFoldExtensionValuePermutation]
  · simp [finiteAxisFoldExtensionValuePermutation, carrier_eq]

/-- Successive value actions compose in the ordinary permutation-group
orientation: `(first * second) e = first (second e)`. -/
theorem finiteAxisFoldExtensionValuePermutation_mul
    {E alpha : Type u} (first second : Equiv.Perm E) (value : alpha) :
    finiteAxisFoldExtensionValuePermutation first
        (finiteAxisFoldExtensionValuePermutation second value) =
      finiteAxisFoldExtensionValuePermutation (first * second) value := by
  classical
  by_cases carrier_eq : alpha = E
  · subst alpha
    simp [finiteAxisFoldExtensionValuePermutation]
  · simp [finiteAxisFoldExtensionValuePermutation, carrier_eq]

/-- Acting by a permutation and then its inverse recovers every Extension
value, including values carried by types other than `E`. -/
theorem finiteAxisFoldExtensionValuePermutation_inv
    {E alpha : Type u} (permutation : Equiv.Perm E) (value : alpha) :
    finiteAxisFoldExtensionValuePermutation permutation⁻¹
        (finiteAxisFoldExtensionValuePermutation permutation value) = value := by
  rw [finiteAxisFoldExtensionValuePermutation_mul]
  simp

/-- On the independently supplied carrier itself, the recipe is exactly the
given permutation rather than merely an extensionally related action. -/
@[simp] theorem finiteAxisFoldExtensionValuePermutation_self
    {E : Type u} (permutation : Equiv.Perm E) (value : E) :
    finiteAxisFoldExtensionValuePermutation permutation value =
      permutation value := by
  classical
  simp [finiteAxisFoldExtensionValuePermutation]

/-! ## Action on every fixed source context -/

/-- Change only the Extension value of a fixed source context.  The complete
minimal reading and the Extension carrier are retained definitionally. -/
noncomputable def finiteAxisFoldSourceContextPermutation
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object where
  minimal := W.minimal
  Extension := W.Extension
  extension :=
    finiteAxisFoldExtensionValuePermutation permutation W.extension

@[simp] theorem finiteAxisFoldSourceContextPermutation_minimal
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    (finiteAxisFoldSourceContextPermutation permutation W).minimal = W.minimal :=
  rfl

@[simp] theorem finiteAxisFoldSourceContextPermutation_extensionType
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    (finiteAxisFoldSourceContextPermutation permutation W).Extension =
      W.Extension :=
  rfl

@[simp] theorem finiteAxisFoldSourceContextPermutation_extension
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    (finiteAxisFoldSourceContextPermutation permutation W).extension =
      finiteAxisFoldExtensionValuePermutation permutation W.extension :=
  rfl

/-- The identity permutation fixes every complete source context. -/
@[simp] theorem finiteAxisFoldSourceContextPermutation_one
    {E : Type}
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    finiteAxisFoldSourceContextPermutation (1 : Equiv.Perm E) W = W := by
  rcases W with ⟨minimal, Extension, extension⟩
  simp [finiteAxisFoldSourceContextPermutation]

/-- Context actions compose with the same ordinary permutation orientation as
the value action. -/
theorem finiteAxisFoldSourceContextPermutation_mul
    {E : Type} (first second : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    finiteAxisFoldSourceContextPermutation first
        (finiteAxisFoldSourceContextPermutation second W) =
      finiteAxisFoldSourceContextPermutation (first * second) W := by
  rcases W with ⟨minimal, Extension, extension⟩
  simp [finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldExtensionValuePermutation_mul]

/-- The inverse permutation recovers every complete source context. -/
theorem finiteAxisFoldSourceContextPermutation_inv
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    finiteAxisFoldSourceContextPermutation permutation⁻¹
        (finiteAxisFoldSourceContextPermutation permutation W) = W := by
  rw [finiteAxisFoldSourceContextPermutation_mul]
  simp

/-- Readable map from every source context into its permuted context. -/
def finiteAxisFoldSourceContextPermutationForwardMorphism
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    Site.ContextMorphism W
      (finiteAxisFoldSourceContextPermutation permutation W) where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- The forward readable map is a restriction in the original source
context preorder. -/
theorem finiteAxisFoldSourceContextPermutationForwardMorphism_isRestriction
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    (finiteAxisFoldSourceContextPermutationForwardMorphism permutation W).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun h => W.supportReads_objectFamily h

/-- Readable map from every permuted source context back to its source. -/
def finiteAxisFoldSourceContextPermutationBackwardMorphism
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    Site.ContextMorphism
      (finiteAxisFoldSourceContextPermutation permutation W) W where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- The reverse readable map is also a restriction in the original source
context preorder. -/
theorem finiteAxisFoldSourceContextPermutationBackwardMorphism_isRestriction
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    (finiteAxisFoldSourceContextPermutationBackwardMorphism permutation W).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun h => W.supportReads_objectFamily h

/-- Every source context reads into its permuted context. -/
theorem finiteAxisFoldSourceContext_le_permutation
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    FiniteAxisFoldPermutationSourceCore.contextPreorder.le W
      (finiteAxisFoldSourceContextPermutation permutation W) := by
  exact ⟨finiteAxisFoldSourceContextPermutationForwardMorphism permutation W,
    finiteAxisFoldSourceContextPermutationForwardMorphism_isRestriction
      permutation W⟩

/-- Every permuted context reads back into its original source context. -/
theorem finiteAxisFoldSourceContextPermutation_le_context
    {E : Type} (permutation : Equiv.Perm E)
    (W : Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object) :
    FiniteAxisFoldPermutationSourceCore.contextPreorder.le
      (finiteAxisFoldSourceContextPermutation permutation W) W := by
  exact ⟨finiteAxisFoldSourceContextPermutationBackwardMorphism permutation W,
    finiteAxisFoldSourceContextPermutationBackwardMorphism_isRestriction
      permutation W⟩

/-! ## A faithful action on the full source context-object carrier -/

/-- The complete object carrier of the original fixed source context
category. -/
abbrev FiniteAxisFoldSourceContextObject :=
  Site.ContextCategoryObject
    FiniteAxisFoldPermutationSourceCore.contextPreorder

/-- Apply an independent Extension permutation to a source context-category
object. -/
noncomputable def finiteAxisFoldSourceContextObjectPermutation
    {E : Type} (permutation : Equiv.Perm E)
    (W : FiniteAxisFoldSourceContextObject) :
    FiniteAxisFoldSourceContextObject :=
  ⟨finiteAxisFoldSourceContextPermutation permutation W.ctx⟩

@[simp] theorem finiteAxisFoldSourceContextObjectPermutation_one
    {E : Type} (W : FiniteAxisFoldSourceContextObject) :
    finiteAxisFoldSourceContextObjectPermutation (1 : Equiv.Perm E) W = W := by
  rcases W with ⟨W⟩
  simp [finiteAxisFoldSourceContextObjectPermutation]

theorem finiteAxisFoldSourceContextObjectPermutation_mul
    {E : Type} (first second : Equiv.Perm E)
    (W : FiniteAxisFoldSourceContextObject) :
    finiteAxisFoldSourceContextObjectPermutation first
        (finiteAxisFoldSourceContextObjectPermutation second W) =
      finiteAxisFoldSourceContextObjectPermutation (first * second) W := by
  rcases W with ⟨W⟩
  simp [finiteAxisFoldSourceContextObjectPermutation,
    finiteAxisFoldSourceContextPermutation_mul]

/-- Every independent Extension permutation gives an actual permutation of
the complete source context-object carrier. -/
noncomputable def finiteAxisFoldSourceContextObjectPerm
    {E : Type} (permutation : Equiv.Perm E) :
    Equiv.Perm FiniteAxisFoldSourceContextObject where
  toFun := finiteAxisFoldSourceContextObjectPermutation permutation
  invFun := finiteAxisFoldSourceContextObjectPermutation permutation⁻¹
  left_inv W := by
    simpa using
      finiteAxisFoldSourceContextObjectPermutation_mul permutation⁻¹
        permutation W
  right_inv W := by
    simpa using
      finiteAxisFoldSourceContextObjectPermutation_mul permutation
        permutation⁻¹ W

/-- The independently supplied permutation group acts faithfully on the full
source context-object carrier.  The hom uses ordinary, not opposite,
permutation orientation. -/
noncomputable def finiteAxisFoldSourceContextObjectPermHom (E : Type) :
    Equiv.Perm E →* Equiv.Perm FiniteAxisFoldSourceContextObject where
  toFun := finiteAxisFoldSourceContextObjectPerm
  map_one' := by
    apply Equiv.ext
    intro W
    exact finiteAxisFoldSourceContextObjectPermutation_one W
  map_mul' first second := by
    apply Equiv.ext
    intro W
    exact (finiteAxisFoldSourceContextObjectPermutation_mul first second W).symm

/-- Canonical source context exposing a chosen `e : E` and no additional
minimal-context variation.  These probes are defined before and independently
of the semantic residual group. -/
def finiteAxisFoldSourceExtensionProbe {E : Type} (value : E) :
    Site.ArchCtx FiniteAxisFoldPermutationSourceCore.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := by intros; contradiction
    axisReads := fun _ => False
    observableReads := fun _ => False
  }
  Extension := E
  extension := value

/-- The action on every canonical probe is exactly the supplied permutation
on its chosen element. -/
@[simp] theorem finiteAxisFoldSourceExtensionProbe_permutation_extension
    {E : Type} (permutation : Equiv.Perm E) (value : E) :
    (finiteAxisFoldSourceContextPermutation permutation
      (finiteAxisFoldSourceExtensionProbe value)).extension =
        permutation value := by
  simp [finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldSourceExtensionProbe]

/-- With a finite independent carrier, distinct input permutations induce
distinct permutations of the full source context-object carrier.  The proof
evaluates at the canonical probe for every `e : E`; no representable subfamily
or completed semantic context action is supplied as input. -/
theorem finiteAxisFoldSourceContextObjectPermHom_injective
    (E : Type) [Fintype E] :
    Function.Injective (finiteAxisFoldSourceContextObjectPermHom E) := by
  intro first second equality
  apply Equiv.ext
  intro value
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
      permutation
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject))
    equality
  have extensionSigmaEquality := congrArg
    (fun W : FiniteAxisFoldSourceContextObject =>
      (⟨W.ctx.Extension, W.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier))
    evaluated
  have probeEquality :
      (⟨E, first value⟩ : Sigma fun carrier : Type => carrier) =
        ⟨E, second value⟩ := by
    simpa [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] using extensionSigmaEquality
  exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
