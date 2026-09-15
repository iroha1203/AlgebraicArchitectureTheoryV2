import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualObjectOperationRigidity
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization
import Formal.Util.AssertStandardAxioms

/-!
# A source Extension-value action for the finite-axis-fold residual analysis

The context category of the fixed finite-axis-fold input contains every
architecture context over the selected object.  Context morphisms read only
the minimal support, axis, and observable data; the additional `Extension`
value is not part of a readable morphism.  This file uses that original input
to construct a uniform involution which negates a Boolean Extension value and
fixes every other Extension type.

The construction keeps the full context quantifier.  It does not select a
post-hoc family of representable contexts, accept a context equivalence as an
input, or store source coverage.  Its purpose is to expose a genuine residual
candidate direction at the independently fixed source exact core, independent
of the Atom, object, operation, invariant, axis, and signature-coordinate
directions handled by the preceding cycles.  This module does not yet lift the
action through complete geometry, the actual pull--push endpoint, or
normalization, so it does not claim an actual residual-kernel element.
-/

namespace AAT.AG.RealizationReconstruction

universe v

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

private noncomputable abbrev FiniteAxisFoldContextSource :=
  finiteAxisFoldSourceGeometryPackage

private noncomputable abbrev FiniteAxisFoldContextSourceCore :=
  FiniteAxisFoldContextSource.core

/-! ## A uniform involution of Extension values -/

/-- Negate an Extension value when its carrier is `Bool`, and otherwise leave
it unchanged.  The recipe has no semantic map or completed comparison as an
input. -/
noncomputable def finiteAxisFoldExtensionValueToggle {alpha : Type}
    (value : alpha) : alpha := by
  classical
  by_cases h : alpha = Bool
  · exact Equiv.cast h.symm (!(Equiv.cast h value))
  · exact value

/-- The fixed Extension-value recipe is an involution on every carrier. -/
theorem finiteAxisFoldExtensionValueToggle_involutive {alpha : Type}
    (value : alpha) :
    finiteAxisFoldExtensionValueToggle
        (finiteAxisFoldExtensionValueToggle value) = value := by
  classical
  by_cases h : alpha = Bool
  · subst alpha
    cases value <;> simp [finiteAxisFoldExtensionValueToggle]
  · simp [finiteAxisFoldExtensionValueToggle, h]

/-- Negation is the concrete action on the selected Boolean Extension. -/
@[simp] theorem finiteAxisFoldExtensionValueToggle_false :
    finiteAxisFoldExtensionValueToggle false = true := by
  simp [finiteAxisFoldExtensionValueToggle]

/-- Apply the Extension-value involution to an arbitrary context while
retaining its complete minimal reading and its Extension carrier. -/
noncomputable def finiteAxisFoldExtensionToggleContext
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    Site.ArchCtx FiniteAxisFoldContextSourceCore.object where
  minimal := W.minimal
  Extension := W.Extension
  extension := finiteAxisFoldExtensionValueToggle W.extension

/-- The toggle's canonical simplification preserves the complete minimal
reading definitionally. -/
@[simp] theorem finiteAxisFoldExtensionToggleContext_minimal
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    (finiteAxisFoldExtensionToggleContext W).minimal = W.minimal :=
  rfl

/-- The toggle's canonical simplification preserves the Extension carrier
definitionally; only its selected value changes. -/
@[simp] theorem finiteAxisFoldExtensionToggleContext_extensionType
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    (finiteAxisFoldExtensionToggleContext W).Extension = W.Extension :=
  rfl

/-- Applying the context recipe twice recovers every original context. -/
theorem finiteAxisFoldExtensionToggleContext_involutive
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    finiteAxisFoldExtensionToggleContext
        (finiteAxisFoldExtensionToggleContext W) = W := by
  rcases W with ⟨minimal, Extension, extension⟩
  simp [finiteAxisFoldExtensionToggleContext,
    finiteAxisFoldExtensionValueToggle_involutive]

/-- An explicit context whose Extension value is moved by the recipe. -/
def finiteAxisFoldBooleanFalseContext :
    Site.ArchCtx FiniteAxisFoldContextSourceCore.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := by intros; contradiction
    axisReads := fun _ => False
    observableReads := fun _ => False
  }
  Extension := Bool
  extension := false

/-- The concrete moved context has Boolean value `true` after toggling. -/
theorem finiteAxisFoldBooleanFalseContext_toggle_extension :
    (finiteAxisFoldExtensionToggleContext
      finiteAxisFoldBooleanFalseContext).extension = true := by
  change finiteAxisFoldExtensionValueToggle false = true
  exact finiteAxisFoldExtensionValueToggle_false

/-- The Boolean-false context is genuinely moved. -/
theorem finiteAxisFoldBooleanFalseContext_toggle_ne :
    finiteAxisFoldExtensionToggleContext
        finiteAxisFoldBooleanFalseContext ≠
      finiteAxisFoldBooleanFalseContext := by
  intro equality
  simpa [finiteAxisFoldExtensionToggleContext,
    finiteAxisFoldBooleanFalseContext] using equality

/-! ## Readable maps and the context autoequivalence -/

/-- Extension data are invisible to the forward readable map. -/
def finiteAxisFoldExtensionToggleForwardMorphism
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    Site.ContextMorphism W (finiteAxisFoldExtensionToggleContext W) where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- The forward Extension-toggle map is a restriction for every context. -/
theorem finiteAxisFoldExtensionToggleForwardMorphism_isRestriction
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    (finiteAxisFoldExtensionToggleForwardMorphism W).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun h => W.supportReads_objectFamily h

/-- Extension data are likewise invisible in the reverse direction. -/
def finiteAxisFoldExtensionToggleBackwardMorphism
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    Site.ContextMorphism (finiteAxisFoldExtensionToggleContext W) W where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- The reverse Extension-toggle map is a restriction for every context. -/
theorem finiteAxisFoldExtensionToggleBackwardMorphism_isRestriction
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    (finiteAxisFoldExtensionToggleBackwardMorphism W).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun h => W.supportReads_objectFamily h

/-- Every context reads into its Extension toggle in the fixed canonical
context preorder. -/
theorem finiteAxisFoldContext_le_extensionToggle
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    FiniteAxisFoldContextSourceCore.contextPreorder.le W
      (finiteAxisFoldExtensionToggleContext W) := by
  change ∃ f : Site.ContextMorphism W
      (finiteAxisFoldExtensionToggleContext W), f.IsRestriction
  exact ⟨finiteAxisFoldExtensionToggleForwardMorphism W,
    finiteAxisFoldExtensionToggleForwardMorphism_isRestriction W⟩

/-- The Extension toggle also reads back into the original context. -/
theorem finiteAxisFoldExtensionToggle_le_context
    (W : Site.ArchCtx FiniteAxisFoldContextSourceCore.object) :
    FiniteAxisFoldContextSourceCore.contextPreorder.le
      (finiteAxisFoldExtensionToggleContext W) W := by
  change ∃ f : Site.ContextMorphism
      (finiteAxisFoldExtensionToggleContext W) W, f.IsRestriction
  exact ⟨finiteAxisFoldExtensionToggleBackwardMorphism W,
    finiteAxisFoldExtensionToggleBackwardMorphism_isRestriction W⟩

/-- Functor induced by the Extension-value involution on the complete thin
context category. -/
noncomputable def finiteAxisFoldExtensionToggleContextFunctor :
    Site.ContextCategoryObject FiniteAxisFoldContextSourceCore.contextPreorder ⥤
      Site.ContextCategoryObject FiniteAxisFoldContextSourceCore.contextPreorder where
  obj W := ⟨finiteAxisFoldExtensionToggleContext W.ctx⟩
  map {W V} f := by
    apply homOfLE
    exact FiniteAxisFoldContextSourceCore.contextPreorder.trans
      (finiteAxisFoldExtensionToggle_le_context W.ctx)
      (FiniteAxisFoldContextSourceCore.contextPreorder.trans f.le
        (finiteAxisFoldContext_le_extensionToggle V.ctx))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The context functor squares to the identity on every object. -/
theorem finiteAxisFoldExtensionToggleContextFunctor_obj_obj
    (W : Site.ContextCategoryObject
      FiniteAxisFoldContextSourceCore.contextPreorder) :
    finiteAxisFoldExtensionToggleContextFunctor.obj
        (finiteAxisFoldExtensionToggleContextFunctor.obj W) = W := by
  cases W with
  | mk ctx =>
      exact congrArg
        (Site.ContextCategoryObject.of
          FiniteAxisFoldContextSourceCore.contextPreorder)
        (finiteAxisFoldExtensionToggleContext_involutive ctx)

/-- The full context autoequivalence generated by Extension-value negation. -/
noncomputable def finiteAxisFoldExtensionToggleContextEquivalence :
    Site.ContextCategoryObject FiniteAxisFoldContextSourceCore.contextPreorder ≌
      Site.ContextCategoryObject FiniteAxisFoldContextSourceCore.contextPreorder :=
  CategoryTheory.Equivalence.mk
    finiteAxisFoldExtensionToggleContextFunctor
    finiteAxisFoldExtensionToggleContextFunctor
    (NatIso.ofComponents
      (fun W => eqToIso
        (finiteAxisFoldExtensionToggleContextFunctor_obj_obj W).symm)
      (by intros; apply Subsingleton.elim))
    (NatIso.ofComponents
      (fun W => eqToIso
        (finiteAxisFoldExtensionToggleContextFunctor_obj_obj W))
      (by intros; apply Subsingleton.elim))

/-- The context autoequivalence moves the explicit Boolean-false context. -/
theorem finiteAxisFoldExtensionToggleContextEquivalence_moves_false :
    (finiteAxisFoldExtensionToggleContextEquivalence.functor.obj
      ⟨finiteAxisFoldBooleanFalseContext⟩).ctx ≠
        finiteAxisFoldBooleanFalseContext :=
  finiteAxisFoldBooleanFalseContext_toggle_ne

private theorem finiteAxisFoldContextSubsingleton_heq_of_type_eq
    {alpha beta : Sort v} [Subsingleton alpha] [Subsingleton beta]
    (type_eq : alpha = beta) (first : alpha) (second : beta) :
    HEq first second := by
  cases type_eq
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Squaring the constructed context equivalence gives the strict identity
equivalence, not merely an unspecified equivalence of categories. -/
theorem finiteAxisFoldExtensionToggleContextEquivalence_trans_self :
    finiteAxisFoldExtensionToggleContextEquivalence.trans
        finiteAxisFoldExtensionToggleContextEquivalence =
      CategoryTheory.Equivalence.refl := by
  have hfunctor :
      (finiteAxisFoldExtensionToggleContextEquivalence.trans
        finiteAxisFoldExtensionToggleContextEquivalence).functor =
      𝟭 (Site.ContextCategoryObject
        FiniteAxisFoldContextSourceCore.contextPreorder) := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · exact finiteAxisFoldExtensionToggleContextFunctor_obj_obj W
    · intros
      exact Subsingleton.elim _ _
  have hinverse :
      (finiteAxisFoldExtensionToggleContextEquivalence.trans
        finiteAxisFoldExtensionToggleContextEquivalence).inverse =
      𝟭 (Site.ContextCategoryObject
        FiniteAxisFoldContextSourceCore.contextPreorder) := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · exact finiteAxisFoldExtensionToggleContextFunctor_obj_obj W
    · intros
      exact Subsingleton.elim _ _
  apply CategoryTheory.Equivalence.ext hfunctor hinverse
  · apply finiteAxisFoldContextSubsingleton_heq_of_type_eq
    apply congrArg
      (fun F => (𝟭 (Site.ContextCategoryObject
        FiniteAxisFoldContextSourceCore.contextPreorder)) ≅ F)
    rw [hfunctor, hinverse]
    rfl
  · apply finiteAxisFoldContextSubsingleton_heq_of_type_eq
    apply congrArg
      (fun F => F ≅ (𝟭 (Site.ContextCategoryObject
        FiniteAxisFoldContextSourceCore.contextPreorder)))
    rw [hfunctor, hinverse]
    rfl

/-! ## Primitive exact-core action and raw invariance -/

/-- Exact equation transport whose only nonidentity datum is the constructed
context autoequivalence.  The fixed equation observables and residuals are
independent of Extension values. -/
noncomputable def finiteAxisFoldExtensionToggleEquationTransport :
    EquationSystemExactTransport
      FiniteAxisFoldContextSourceCore.algebra.equationSystem
      FiniteAxisFoldContextSourceCore.algebra.equationSystem
      (Equiv.refl FiniteModel.carrier.Atom) id where
  contextEquivalence := finiteAxisFoldExtensionToggleContextEquivalence
  equationEquiv := Equiv.refl _
  role_eq := by intros; rfl
  observableEquiv := fun _ => RingEquiv.refl Int
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; rfl
  equationResidual_eq := by intros; rfl

/-- Exact source-core endomorphism generated solely by the Extension-value
recipe. -/
noncomputable def finiteAxisFoldExtensionToggleUpper :
    SignedExactCoreReadingHom FiniteAxisFoldContextSourceCore
      FiniteAxisFoldContextSourceCore :=
  { SignedExactCoreReadingHom.refl FiniteAxisFoldContextSourceCore with
    equationTransport := finiteAxisFoldExtensionToggleEquationTransport }

/-- Package-total form of the primitive Extension-value action. -/
noncomputable def finiteAxisFoldExtensionToggleTotal :
    PackageTotalHom FiniteAxisFoldContextSourceCore
      FiniteAxisFoldContextSourceCore where
  base := ExtInstHom.id (packagePoint FiniteAxisFoldContextSourceCore)
  upper := finiteAxisFoldExtensionToggleUpper
  atomEquiv_eq := rfl

/-- The exact source upper is an involution on all of its computational
fields. -/
theorem finiteAxisFoldExtensionToggleUpper_comp_self :
    finiteAxisFoldExtensionToggleUpper.comp
        finiteAxisFoldExtensionToggleUpper =
      SignedExactCoreReadingHom.refl FiniteAxisFoldContextSourceCore := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · rfl
  · apply equationSystemExactTransport_hext
    · rfl
    · rfl
    · exact finiteAxisFoldExtensionToggleContextEquivalence_trans_self
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The total-package Extension action is an involution. -/
theorem finiteAxisFoldExtensionToggleTotal_comp_self :
    finiteAxisFoldExtensionToggleTotal.comp
        finiteAxisFoldExtensionToggleTotal =
      PackageTotalHom.id FiniteAxisFoldContextSourceCore := by
  apply PackageTotalHom.ext
  · rfl
  · exact finiteAxisFoldExtensionToggleUpper_comp_self

/-- Reindexing the fixed constant raw system by the source Extension action
changes no coordinate, relation, or restriction data.  This is the raw-data
premise for the still-unconstructed complete-geometry lift. -/
theorem finiteAxisFoldExtensionToggle_rawReindex :
    rawReindex (G := FiniteAxisFoldContextSource)
        (H := FiniteAxisFoldContextSource)
        finiteAxisFoldExtensionToggleTotal FiniteAxisFoldContextSource.raw =
      FiniteAxisFoldContextSource.raw := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

/-- The package-total action is nonidentity because its context equivalence
moves the explicit Boolean-false context. -/
theorem finiteAxisFoldExtensionToggleTotal_ne_id :
    finiteAxisFoldExtensionToggleTotal ≠
      PackageTotalHom.id FiniteAxisFoldContextSourceCore := by
  intro equality
  have contextEquality := congrArg
    (fun hom : PackageTotalHom FiniteAxisFoldContextSourceCore
        FiniteAxisFoldContextSourceCore =>
      hom.upper.equationTransport.contextEquivalence)
    equality
  have movedEquality := congrArg
    (fun equivalence =>
      (equivalence.functor.obj
        (⟨finiteAxisFoldBooleanFalseContext⟩ :
          Site.ContextCategoryObject
            FiniteAxisFoldContextSourceCore.contextPreorder)).ctx)
    contextEquality
  exact finiteAxisFoldBooleanFalseContext_toggle_ne movedEquality

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
