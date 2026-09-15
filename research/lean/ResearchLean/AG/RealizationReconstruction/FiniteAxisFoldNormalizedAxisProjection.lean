import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldAxisSwapPresentation
import Formal.Util.AssertStandardAxioms

/-!
# The finite axis quotient of the normalized direct automorphism group

Every automorphism of the actual normalized direct endpoint acts on the three
global signature axes.  Its inverse supplies the inverse axis table, so this
action defines a group homomorphism to `Equiv.Perm (Fin 3)`.  The primitive
finite-axis construction is a section of this projection.  Consequently every
normalized automorphism splits, without any coverage hypothesis, into an
axis-trivial kernel remainder and its explicitly displayed finite permutation.

The final theorem isolates the remaining source-coverage obligation exactly:
canonical-section source coverage for all normalized endpoint automorphisms is
equivalent to such coverage on the axis-trivial kernel.  It does not assert that
the kernel is covered, finite, or trivial.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldNormalizedAxisProjectionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The actual normalized direct endpoint used throughout the finite-axis-fold
instance. -/
noncomputable abbrev FiniteAxisFoldNormalizedDirectGeometry :=
  (geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).obj
    finiteAxisFoldActualDirectAdmissibleGeometry

/-- An automorphism of the actual normalized direct endpoint acts on its three
signature axes.  The axis map of the inverse automorphism supplies the inverse
finite table. -/
noncomputable def finiteAxisFoldNormalizedAxisEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm (Fin 3) where
  toFun := automorphism.hom.f.hom.base.upper.axisMap
  invFun := automorphism.inv.f.hom.base.upper.axisMap
  left_inv axis := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.upper.axisMap)
      automorphism.hom_inv_id
    change automorphism.inv.f.hom.base.upper.axisMap ∘
        automorphism.hom.f.hom.base.upper.axisMap = _root_.id at equality
    exact congrFun equality axis
  right_inv axis := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.upper.axisMap)
      automorphism.inv_hom_id
    change automorphism.hom.f.hom.base.upper.axisMap ∘
        automorphism.inv.f.hom.base.upper.axisMap = _root_.id at equality
    exact congrFun equality axis

/-- The complete normalized direct automorphism group projects to the finite
permutation group carried by its global signature-axis component. -/
noncomputable def finiteAxisFoldNormalizedAxisProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →* Equiv.Perm (Fin 3) where
  toFun := finiteAxisFoldNormalizedAxisEquiv
  map_one' := by
    apply Equiv.ext
    intro axis
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro axis
    rfl

/-- Primitive finite axis tables form a group in the southwest geometry fiber.
This is the pre-normalization construction, not a semantic choice of a completed
normalized automorphism. -/
noncomputable def finiteAxisFoldSouthwestPermutationSectionHom :
    Equiv.Perm (Fin 3) →* Aut finiteAxisFoldSouthwestGeometryFiber where
  toFun := finiteAxisFoldSouthwestPermutationAut
  map_one' := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldPermutationGeometry_refl
  map_mul' first second := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldPermutationGeometry_comp second first

/-- Pulling and transporting the primitive southwest action gives the actual
direct finite-axis action as a group homomorphism. -/
noncomputable def finiteAxisFoldActualDirectPermutationSectionHom :
    Equiv.Perm (Fin 3) →*
      Aut (authoredExactDirectGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))) :=
  ((geomFiberTransportFunctor
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).mapAut _).comp
    (((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapAut _).comp
      finiteAxisFoldSouthwestPermutationSectionHom)

/-- Package an actual direct automorphism in the independently fixed
admissible direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectAdmissibleAutomorphismHom :
    Aut (authoredExactDirectGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))) →*
      Aut finiteAxisFoldActualDirectAdmissibleGeometry where
  toFun automorphism :=
    { hom := ObjectProperty.homMk automorphism.hom.1
      inv := ObjectProperty.homMk automorphism.inv.1
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact congrArg Subtype.val automorphism.hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact congrArg Subtype.val automorphism.inv_hom_id }
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    rfl
  map_mul' first second := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    rfl

/-- The fixed primitive finite-axis construction, followed by the fixed
pull-push route and canonical normalization, is a group homomorphism into the
full normalized direct automorphism group. -/
noncomputable def finiteAxisFoldNormalizedAxisSectionHom :
    Equiv.Perm (Fin 3) →* Aut FiniteAxisFoldNormalizedDirectGeometry :=
  ((geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).mapAut _).comp
    (finiteAxisFoldActualDirectAdmissibleAutomorphismHom.comp
      finiteAxisFoldActualDirectPermutationSectionHom)

/-- The group-homomorphic section agrees with the previously constructed
normalized finite-axis automorphism. -/
theorem finiteAxisFoldNormalizedAxisSectionHom_apply
    (permutation : Equiv.Perm (Fin 3)) :
    finiteAxisFoldNormalizedAxisSectionHom permutation =
      finiteAxisFoldNormalizedDirectPermutationAut permutation := by
  apply Iso.ext
  rfl

/-- Reading the axis table after the primitive construction gives back the
entire input table. -/
theorem finiteAxisFoldNormalizedAxisProjection_section
    (permutation : Equiv.Perm (Fin 3)) :
      finiteAxisFoldNormalizedAxisProjection
        (finiteAxisFoldNormalizedAxisSectionHom permutation) =
      permutation := by
  rw [finiteAxisFoldNormalizedAxisSectionHom_apply]
  apply Equiv.ext
  intro axis
  change (finiteAxisFoldActualDirectPermutationAut
      permutation).hom.1.base.upper.axisMap axis = permutation axis
  rw [finiteAxisFoldActualDirectPermutationAut_axisMap]

/-- The normalized axis projection has the explicit primitive finite-table
construction as a right inverse. -/
theorem finiteAxisFoldNormalizedAxisProjection_hasRightInverse :
    Function.RightInverse finiteAxisFoldNormalizedAxisSectionHom
      finiteAxisFoldNormalizedAxisProjection :=
  finiteAxisFoldNormalizedAxisProjection_section

/-- Automorphisms invisible to the global three-axis table.  Membership says
only that the axis projection is the identity; no coverage is embedded here. -/
noncomputable abbrev FiniteAxisFoldNormalizedAxisKernel :=
  MonoidHom.ker finiteAxisFoldNormalizedAxisProjection

/-- Remove the explicitly constructed finite-axis component of an arbitrary
normalized endpoint automorphism. -/
noncomputable def finiteAxisFoldNormalizedAxisKernelRemainder
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    FiniteAxisFoldNormalizedAxisKernel :=
  ⟨automorphism *
      (finiteAxisFoldNormalizedAxisSectionHom
        (finiteAxisFoldNormalizedAxisProjection automorphism))⁻¹,
    by
      simp [finiteAxisFoldNormalizedAxisProjection_section]⟩

/-- Exact decomposition into the axis-trivial remainder and the displayed
finite permutation component. -/
theorem finiteAxisFoldNormalizedAxisKernelRemainder_mul_section
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    (finiteAxisFoldNormalizedAxisKernelRemainder automorphism).1 *
        finiteAxisFoldNormalizedAxisSectionHom
          (finiteAxisFoldNormalizedAxisProjection automorphism) =
      automorphism := by
  simp [finiteAxisFoldNormalizedAxisKernelRemainder]

/-- Source coverage of the canonical normalization section at one actual
normalized direct automorphism.  The witness is an arrow of the independently
generated presentation, not semantic data stored in the syntax. -/
def FiniteAxisFoldCanonicalSectionSourceCovered
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) : Prop :=
  ∃ sourceAutomorphism :
      Aut (FiniteAxisFoldAxisSwapPresentation.ofObject
        (.direct finiteAxisFoldG122CellInput)),
    FiniteAxisFoldAxisSwapPresentation.directAutomorphismEvaluationHom
        sourceAutomorphism =
      canonicalNormalizationAutomorphismSectionHom
        finiteAxisFoldActualDirectAdmissibleGeometry automorphism

/-- All normalized canonical-section source coverage is equivalent to the
remaining axis-trivial-kernel coverage.  The reverse implication uses the
already constructed source term for every finite permutation and the exact
kernel-times-section decomposition above. -/
theorem finiteAxisFoldCanonicalSectionSourceCovered_all_iff_kernel :
    (∀ automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry,
      FiniteAxisFoldCanonicalSectionSourceCovered automorphism) ↔
    (∀ remainder : FiniteAxisFoldNormalizedAxisKernel,
      FiniteAxisFoldCanonicalSectionSourceCovered remainder.1) := by
  constructor
  · intro coverage remainder
    exact coverage remainder.1
  · intro kernelCoverage automorphism
    obtain ⟨kernelSource, kernelSource_evaluation⟩ :=
      kernelCoverage (finiteAxisFoldNormalizedAxisKernelRemainder automorphism)
    refine ⟨kernelSource *
      FiniteAxisFoldAxisSwapPresentation.sectionedDirectAxisPermutationAut
        (finiteAxisFoldNormalizedAxisProjection automorphism), ?_⟩
    rw [map_mul, kernelSource_evaluation]
    rw [FiniteAxisFoldAxisSwapPresentation.sectionedDirectAxisPermutationAut_evaluation]
    rw [← finiteAxisFoldNormalizedAxisSectionHom_apply]
    rw [← map_mul]
    rw [finiteAxisFoldNormalizedAxisKernelRemainder_mul_section]

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
