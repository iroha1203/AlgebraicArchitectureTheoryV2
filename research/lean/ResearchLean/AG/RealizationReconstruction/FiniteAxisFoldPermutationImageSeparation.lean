import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationLocalFiberKernelInjective
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBackwardToggleSyntax
import Mathlib.Logic.Equiv.Bool
import Formal.Util.AssertStandardAxioms

/-!
# The Boolean toggle inside the finite-permutation image

The independently constructed two-symbol Boolean toggle is the Boolean
specialization of the arbitrary finite Extension-permutation action.  The
comparison is proved first at the primitive source-value recipe, then through
the complete source geometry and the fixed actual normalization route.  Thus
the old two-element evaluator is not a second semantic input.

The same finite-permutation section also contains a non-involutive permutation
of `Fin 3`.  Since every value of the two-symbol evaluator is involutive and
the arbitrary section is injective, that element is outside the old evaluator
range.  This separates the independently generated permutation family from
the displayed C2 fragment without defining syntax to be a semantic range.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

local instance finiteAxisFoldPermutationComparisonAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private theorem finiteAxisFoldPermutationComparison_subsingleton_heq_of_type_eq
    {alpha beta : Sort _} [Subsingleton alpha] [Subsingleton beta]
    (type_eq : alpha = beta) (first : alpha) (second : beta) :
    HEq first second := by
  cases type_eq
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Boolean negation is exactly the generic Extension-value permutation
recipe specialized to `Equiv.boolNot`. -/
theorem finiteAxisFoldExtensionValuePermutation_boolNot
    {alpha : Type} (value : alpha) :
    finiteAxisFoldExtensionValuePermutation Equiv.boolNot value =
      finiteAxisFoldExtensionValueToggle value := by
  classical
  by_cases carrier_eq : alpha = Bool
  · subst alpha
    cases value <;>
      simp [finiteAxisFoldExtensionValuePermutation,
        finiteAxisFoldExtensionValueToggle, Equiv.boolNot]
  · simp [finiteAxisFoldExtensionValuePermutation,
      finiteAxisFoldExtensionValueToggle, carrier_eq]

/-- The generic Boolean context action is the original source-owned toggle on
every complete source context, not merely on the distinguished probe. -/
theorem finiteAxisFoldSourceContextPermutation_boolNot
    (W : Site.ArchCtx finiteAxisFoldSourceGeometryPackage.core.object) :
    finiteAxisFoldSourceContextPermutation Equiv.boolNot W =
      finiteAxisFoldExtensionToggleContext W := by
  rcases W with ⟨minimal, Extension, extension⟩
  simp only [finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldExtensionToggleContext]
  rw [finiteAxisFoldExtensionValuePermutation_boolNot]

/-- Equality of the full context functors, including every source object and
every readable arrow. -/
theorem finiteAxisFoldSourceContextPermutationFunctor_boolNot :
    finiteAxisFoldSourceContextPermutationFunctor Equiv.boolNot =
      finiteAxisFoldExtensionToggleContextFunctor := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (Site.ContextCategoryObject.of
        finiteAxisFoldSourceGeometryPackage.core.contextPreorder)
      (finiteAxisFoldSourceContextPermutation_boolNot W.ctx)
  · intros
    exact Subsingleton.elim _ _

/-- Equality of the asymmetric context equivalences used by the two complete
source-geometry constructions. -/
theorem finiteAxisFoldSourceBackwardPermutationContextEquivalence_boolNot :
    finiteAxisFoldSourceBackwardPermutationContextEquivalence Equiv.boolNot =
      finiteAxisFoldExtensionBackwardContextEquivalence := by
  have hfunctor :
      (finiteAxisFoldSourceBackwardPermutationContextEquivalence
        Equiv.boolNot).functor =
        finiteAxisFoldExtensionBackwardContextEquivalence.functor := rfl
  have hinverse :
      (finiteAxisFoldSourceBackwardPermutationContextEquivalence
        Equiv.boolNot).inverse =
        finiteAxisFoldExtensionBackwardContextEquivalence.inverse :=
    finiteAxisFoldSourceContextPermutationFunctor_boolNot
  apply CategoryTheory.Equivalence.ext hfunctor hinverse
  · apply finiteAxisFoldPermutationComparison_subsingleton_heq_of_type_eq
    apply congrArg
      (fun F =>
        (CategoryTheory.Functor.id
          (Site.ContextCategoryObject
            finiteAxisFoldSourceGeometryPackage.core.contextPreorder)) ≅ F)
    rw [hfunctor, hinverse]
  · apply finiteAxisFoldPermutationComparison_subsingleton_heq_of_type_eq
    apply congrArg
      (fun F => F ≅
        (CategoryTheory.Functor.id
          (Site.ContextCategoryObject
            finiteAxisFoldSourceGeometryPackage.core.contextPreorder)))
    rw [hfunctor, hinverse]

private theorem finiteAxisFoldPermutationComparison_geomReadHom_heq_of_base_eq
    {firstBase secondBase : PackageTotalHom
      finiteAxisFoldSourceGeometryPackage.core
      finiteAxisFoldSourceGeometryPackage.core}
    (first : GeomReadHom finiteAxisFoldSourceGeometryPackage
      finiteAxisFoldSourceGeometryPackage firstBase)
    (second : GeomReadHom finiteAxisFoldSourceGeometryPackage
      finiteAxisFoldSourceGeometryPackage secondBase)
    (hbase : firstBase = secondBase)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hsupport : HEq first.supportComp second.supportComp)
    (haxis : HEq first.axisComp second.axisComp)
    (hobservable : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

/-- The generic backward complete-geometry morphism at Boolean negation is
the previously constructed backward-toggle morphism. -/
theorem finiteAxisFoldSourceBackwardPermutationGeometry_boolNot :
    finiteAxisFoldSourceBackwardPermutationGeometry Equiv.boolNot =
      finiteAxisFoldExtensionBackwardGeometry := by
  have hbase :
      finiteAxisFoldSourceBackwardPermutationTotal Equiv.boolNot =
        finiteAxisFoldExtensionBackwardTotal := by
    apply PackageTotalHom.ext
    · rfl
    · apply SignedExactCoreReadingHom.ext
      · rfl
      · rfl
      · apply equationSystemExactTransport_hext
        · rfl
        · rfl
        · exact
            finiteAxisFoldSourceBackwardPermutationContextEquivalence_boolNot
        · rfl
        · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  apply GeometryTotalHom.ext hbase
  apply finiteAxisFoldPermutationComparison_geomReadHom_heq_of_base_eq _ _
    hbase rfl
  · rfl
  · rfl
  · rfl

/-- The Boolean value of the generic source section is exactly the original
source-owned geometry automorphism. -/
theorem finiteAxisFoldSourcePermutationGeometrySectionHom_boolNot :
    finiteAxisFoldSourcePermutationGeometrySectionHom Bool Equiv.boolNot =
      finiteAxisFoldExtensionBackwardGeometryAut := by
  apply Iso.ext
  simpa using finiteAxisFoldSourceBackwardPermutationGeometry_boolNot

/-- The equality survives the vertical source-fiber packaging. -/
theorem finiteAxisFoldSourcePermutationGeometryFiberSectionHom_boolNot :
    finiteAxisFoldSourcePermutationGeometryFiberSectionHom Bool Equiv.boolNot =
      finiteAxisFoldExtensionBackwardGeometryFiberAut := by
  apply Iso.ext
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact congrArg Iso.hom
    finiteAxisFoldSourcePermutationGeometrySectionHom_boolNot

/-- The equality survives the canonical source-to-southwest transport and
endpoint retagging. -/
theorem finiteAxisFoldSouthwestPermutationGeometrySectionHom_boolNot :
    finiteAxisFoldSouthwestPermutationGeometrySectionHom Bool Equiv.boolNot =
      finiteAxisFoldSouthwestExtensionBackwardAut := by
  simp only [finiteAxisFoldSouthwestPermutationGeometrySectionHom,
    MonoidHom.comp_apply,
    finiteAxisFoldSouthwestExtensionBackwardAut,
    finiteAxisFoldTransportedExtensionBackwardAut]
  rw [finiteAxisFoldSourcePermutationGeometryFiberSectionHom_boolNot]
  apply Iso.ext
  rfl

/-- The equality survives the fixed exact-left pull and top transport. -/
theorem finiteAxisFoldActualDirectPermutationGeometrySectionHom_boolNot :
    finiteAxisFoldActualDirectPermutationGeometrySectionHom Bool Equiv.boolNot =
      finiteAxisFoldActualDirectExtensionBackwardAut := by
  change
    (geomFiberTransportFunctor
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).mapIso
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
            (finiteAxisFoldSouthwestPermutationGeometrySectionHom Bool
              Equiv.boolNot)) =
      finiteAxisFoldActualDirectExtensionBackwardAut
  rw [finiteAxisFoldSouthwestPermutationGeometrySectionHom_boolNot]
  rfl

/-- The generic Boolean permutation gives the original normalized
backward-toggle automorphism on the fixed actual endpoint. -/
theorem finiteAxisFoldNormalizedPermutationGeometrySectionHom_boolNot :
    finiteAxisFoldNormalizedPermutationGeometrySectionHom Bool Equiv.boolNot =
      finiteAxisFoldNormalizedExtensionBackwardAut := by
  have admissibleEquality :
      finiteAxisFoldActualDirectAdmissibleAutomorphismHom
          (finiteAxisFoldActualDirectPermutationGeometrySectionHom Bool
            Equiv.boolNot) =
        finiteAxisFoldActualDirectExtensionBackwardAdmissibleAut := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact congrArg (fun automorphism => automorphism.hom.1)
      finiteAxisFoldActualDirectPermutationGeometrySectionHom_boolNot
  change
    (geometryNormalizationFunctor FiniteModel.carrier).mapIso
        (finiteAxisFoldActualDirectAdmissibleAutomorphismHom
          (finiteAxisFoldActualDirectPermutationGeometrySectionHom Bool
            Equiv.boolNot)) =
      finiteAxisFoldNormalizedExtensionBackwardAut
  rw [admissibleEquality]
  rfl

/-- After all four kernel subtype layers are retained, the Boolean member of
the arbitrary finite-permutation section is exactly the Cycle 91 toggle. -/
theorem finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_boolNot :
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Bool
        Equiv.boolNot =
      finiteAxisFoldNormalizedExtensionBackwardLocalFiberKernel := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact finiteAxisFoldNormalizedPermutationGeometrySectionHom_boolNot

/-! ## Exact comparison with the independent C2 evaluator -/

/-- The independent two-symbol syntax maps to the complete Boolean
permutation group without referring to the semantic residual kernel. -/
noncomputable def FiniteAxisFoldBackwardToggleSyntax.boolPerm :
    FiniteAxisFoldBackwardToggleSyntax →* Equiv.Perm Bool where
  toFun
    | .identity => 1
    | .toggle => Equiv.boolNot
  map_one' := rfl
  map_mul' first second := by
    cases first <;> cases second
    · rfl
    · rfl
    · rfl
    · apply Equiv.ext
      intro value
      cases value <;> rfl

/-- The Cycle 91 evaluator is literally the generic Boolean section after
the independently defined syntax-to-permutation map. -/
theorem finiteAxisFoldBackwardToggleSyntax_evaluate_eq_boolPermutationSection :
    (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Bool).comp
        FiniteAxisFoldBackwardToggleSyntax.boolPerm =
      FiniteAxisFoldBackwardToggleSyntax.evaluate := by
  apply MonoidHom.ext
  intro code
  cases code
  · exact map_one
      (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Bool)
  · exact
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_boolNot

/-- Every Boolean permutation is represented by one of the two independent
source codes. -/
theorem finiteAxisFoldBackwardToggleSyntax_boolPerm_surjective :
    Function.Surjective FiniteAxisFoldBackwardToggleSyntax.boolPerm := by
  intro permutation
  cases falseValue : permutation false
  · have trueValue : permutation true = true := by
      cases value_eq : permutation true
      · exfalso
        have contradiction : true = false :=
          permutation.injective (value_eq.trans falseValue.symm)
        cases contradiction
      · rfl
    refine ⟨.identity, ?_⟩
    apply Equiv.ext
    intro value
    cases value
    · exact falseValue.symm
    · exact trueValue.symm
  · have trueValue : permutation true = false := by
      cases value_eq : permutation true
      · rfl
      · exfalso
        have contradiction : true = false :=
          permutation.injective (value_eq.trans falseValue.symm)
        cases contradiction
    refine ⟨.toggle, ?_⟩
    apply Equiv.ext
    intro value
    cases value
    · exact falseValue.symm
    · exact trueValue.symm

/-- The old two-symbol evaluator image is exactly the Boolean specialization
of the arbitrary finite-permutation image. -/
theorem finiteAxisFoldBackwardToggleSyntax_evaluate_range_eq_boolPermutation_range :
    Set.range FiniteAxisFoldBackwardToggleSyntax.evaluate =
      Set.range
        (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Bool) := by
  apply Set.ext
  intro element
  constructor
  · rintro ⟨code, rfl⟩
    refine ⟨FiniteAxisFoldBackwardToggleSyntax.boolPerm code, ?_⟩
    exact congrArg
      (fun hom : FiniteAxisFoldBackwardToggleSyntax →*
          FiniteAxisFoldResidualLocalFiberKernel => hom code)
      finiteAxisFoldBackwardToggleSyntax_evaluate_eq_boolPermutationSection
  · rintro ⟨permutation, rfl⟩
    obtain ⟨code, rfl⟩ :=
      finiteAxisFoldBackwardToggleSyntax_boolPerm_surjective permutation
    refine ⟨code, ?_⟩
    exact (congrArg
      (fun hom : FiniteAxisFoldBackwardToggleSyntax →*
          FiniteAxisFoldResidualLocalFiberKernel => hom code)
      finiteAxisFoldBackwardToggleSyntax_evaluate_eq_boolPermutationSection).symm

/-! ## A non-involutive source-generated element -/

/-- An independently presented three-cycle on a three-element Extension
carrier. -/
def finiteAxisFoldExtensionThreeCycle : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2

/-- The three-cycle is not involutive. -/
theorem finiteAxisFoldExtensionThreeCycle_mul_self_ne_one :
    finiteAxisFoldExtensionThreeCycle *
        finiteAxisFoldExtensionThreeCycle ≠ 1 := by
  intro equality
  have pointEquality := Equiv.congr_fun equality (0 : Fin 3)
  have leftValue :
      (finiteAxisFoldExtensionThreeCycle *
          finiteAxisFoldExtensionThreeCycle) (0 : Fin 3) = 2 := by
    decide
  rw [leftValue] at pointEquality
  simp at pointEquality

/-- Injectivity of the actual normalized local-kernel section retains the
non-involutive order of the source three-cycle. -/
theorem finiteAxisFoldExtensionThreeCycle_localFiberKernel_mul_self_ne_one :
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom (Fin 3)
          finiteAxisFoldExtensionThreeCycle *
        finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom (Fin 3)
          finiteAxisFoldExtensionThreeCycle ≠ 1 := by
  intro equality
  apply finiteAxisFoldExtensionThreeCycle_mul_self_ne_one
  apply finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_injective
    (Fin 3)
  rw [map_mul, map_one]
  exact equality

/-- Every element in the independent C2 evaluator image is involutive. -/
theorem FiniteAxisFoldBackwardToggleSyntax.evaluate_mul_self
    (code : FiniteAxisFoldBackwardToggleSyntax) :
    FiniteAxisFoldBackwardToggleSyntax.evaluate code *
        FiniteAxisFoldBackwardToggleSyntax.evaluate code = 1 := by
  cases code
  · simp
  · exact finiteAxisFoldNormalizedExtensionBackwardLocalFiberKernel_mul_self

/-- The actual normalized element generated by the source three-cycle lies
outside the old C2 evaluator range.  This is a strict image separation inside
the same actual local-fiber kernel, not a comparison after forgetting data. -/
theorem finiteAxisFoldExtensionThreeCycle_not_mem_backwardToggleSyntax_range :
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom (Fin 3)
        finiteAxisFoldExtensionThreeCycle ∉
      Set.range FiniteAxisFoldBackwardToggleSyntax.evaluate := by
  rintro ⟨code, equality⟩
  apply finiteAxisFoldExtensionThreeCycle_localFiberKernel_mul_self_ne_one
  rw [← equality]
  exact FiniteAxisFoldBackwardToggleSyntax.evaluate_mul_self code

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
