import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationResidualKernel
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBackwardToggleLocalAction
import Formal.Util.AssertStandardAxioms

/-!
# Arbitrary finite Extension permutations in the residual local-fiber kernel

Every independently supplied permutation of an Extension carrier acts trivially
on the complete dependent Support, Axis, and Observable families after the fixed
southwest, exact-left, top-transport, admissible, and normalization route.  The
proof transports the source identities through the same constructed geometry
action used by the residual context-kernel section; no local-action certificate
is supplied as input.

The three identities place the whole permutation family in the actual joint
local-fiber kernel.  Injectivity and image coverage are separate obligations.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

local instance finiteAxisFoldGenericPermutationLocalFiberAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

variable {E : Type} (permutation : Equiv.Perm E)

local notation "genericPermutationGeometry" =>
  finiteAxisFoldSourceBackwardPermutationGeometry permutation⁻¹
local notation "genericPermutationGeometryFiberAut" =>
  (finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) permutation
local notation "southwestGenericPermutationAut" =>
  (finiteAxisFoldSouthwestPermutationGeometrySectionHom E) permutation
local notation "actualDirectGenericPermutationAut" =>
  (finiteAxisFoldActualDirectPermutationGeometrySectionHom E) permutation
local notation "normalizedGenericPermutationAut" =>
  (finiteAxisFoldNormalizedPermutationGeometrySectionHom E) permutation

private noncomputable abbrev FiniteAxisFoldGenericPermutationLocalPulledGeometryFiber :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).obj
      finiteAxisFoldSouthwestGeometryFiber

/-! ## Complete dependent Support action -/

/-- The primitive source permutation fixes every dependent Support value. -/
theorem finiteAxisFoldSourceGenericPermutation_supportSigmaMap_eq_id :
    geometrySupportSigmaMap genericPermutationGeometry = _root_.id := by
  funext value
  rcases value with ⟨context, support⟩
  rfl

/-- The southwest transport of an arbitrary source permutation fixes every
dependent Support value. -/
theorem finiteAxisFoldSouthwestGenericPermutation_supportSigmaMap_eq_id :
    geometrySupportSigmaMap (southwestGenericPermutationAut).hom.1 =
      _root_.id := by
  let canonical :=
    geomFiberLift finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  have canonicalSurjective :
      Function.Surjective (geometrySupportSigmaMap canonical) := by
    exact geomFiberLiftSupportSigmaMap_surjective
      finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  funext value
  obtain ⟨sourceValue, rfl⟩ := canonicalSurjective value
  have factorization := congrArg geometrySupportSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldSourceToSouthwestExtInstHom
      (genericPermutationGeometryFiberAut).hom)
  have pointwise := congrFun factorization sourceValue
  simpa [geometrySupportSigmaMap_comp,
    finiteAxisFoldSouthwestPermutationGeometrySectionHom,
    finiteAxisFoldSourcePermutationGeometryFiberSectionHom,
    finiteAxisFoldSourcePermutationGeometryAut,
    finiteAxisFoldSourceGenericPermutation_supportSigmaMap_eq_id,
    canonical] using pointwise

/-- The exact-left pull of an arbitrary source permutation fixes every
dependent Support value. -/
theorem finiteAxisFoldExactLeftGenericPermutation_supportSigmaMap_eq_id :
    geometrySupportSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 =
      _root_.id := by
  let lift := exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber
  have liftInjective : Function.Injective (geometrySupportSigmaMap lift) := by
    exact exactGeometryPullSupportSigmaMap_injective
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber
  funext value
  apply liftInjective
  have factorization := congrArg geometrySupportSigmaMap
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      (southwestGenericPermutationAut).hom)
  have pointwise := congrFun factorization value
  change geometrySupportSigmaMap lift
      (geometrySupportSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 value) =
    geometrySupportSigmaMap (southwestGenericPermutationAut).hom.1
      (geometrySupportSigmaMap lift value) at pointwise
  rw [finiteAxisFoldSouthwestGenericPermutation_supportSigmaMap_eq_id]
    at pointwise
  simpa using pointwise

/-- The fixed top transport of an arbitrary source permutation fixes every
dependent Support value. -/
theorem finiteAxisFoldActualDirectGenericPermutation_supportSigmaMap_eq_id :
    geometrySupportSigmaMap (actualDirectGenericPermutationAut).hom.1 =
      _root_.id := by
  let lift :=
    geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldGenericPermutationLocalPulledGeometryFiber
  have liftSurjective :
      Function.Surjective (geometrySupportSigmaMap lift) := by
    exact geomFiberLiftSupportSigmaMap_surjective
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldGenericPermutationLocalPulledGeometryFiber
  funext value
  obtain ⟨sourceValue, rfl⟩ := liftSurjective value
  have factorization := congrArg geometrySupportSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          (southwestGenericPermutationAut).hom))
  have pointwise := congrFun factorization sourceValue
  change geometrySupportSigmaMap (actualDirectGenericPermutationAut).hom.1
      (geometrySupportSigmaMap lift sourceValue) =
    geometrySupportSigmaMap lift
      (geometrySupportSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 sourceValue) at pointwise
  rw [finiteAxisFoldExactLeftGenericPermutation_supportSigmaMap_eq_id]
    at pointwise
  simpa [finiteAxisFoldActualDirectPermutationGeometrySectionHom] using pointwise

/-- Normalization preserves the complete dependent Support identity. -/
theorem finiteAxisFoldNormalizedGenericPermutation_supportSigmaMap_eq_id :
    geometrySupportSigmaMap (normalizedGenericPermutationAut).hom.f.hom =
      _root_.id := by
  change geometrySupportSigmaMap (actualDirectGenericPermutationAut).hom.1 =
    _root_.id
  exact finiteAxisFoldActualDirectGenericPermutation_supportSigmaMap_eq_id
    permutation

/-! ## Complete dependent Axis action -/

/-- The primitive source permutation fixes every dependent Axis value. -/
theorem finiteAxisFoldSourceGenericPermutation_axisSigmaMap_eq_id :
    geometryAxisSigmaMap genericPermutationGeometry = _root_.id := by
  funext value
  rcases value with ⟨context, axis⟩
  rfl

/-- The southwest transport of an arbitrary source permutation fixes every
dependent Axis value. -/
theorem finiteAxisFoldSouthwestGenericPermutation_axisSigmaMap_eq_id :
    geometryAxisSigmaMap (southwestGenericPermutationAut).hom.1 =
      _root_.id := by
  let canonical := geomFiberLift finiteAxisFoldSourceToSouthwestExtInstHom
    (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  have canonicalSurjective : Function.Surjective (geometryAxisSigmaMap canonical) := by
    exact geomFiberLiftAxisSigmaMap_surjective
      finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  funext value
  obtain ⟨sourceValue, rfl⟩ := canonicalSurjective value
  have factorization := congrArg geometryAxisSigmaMap
    (geomFiberTransportMap_fac finiteAxisFoldSourceToSouthwestExtInstHom
      (genericPermutationGeometryFiberAut).hom)
  have pointwise := congrFun factorization sourceValue
  simpa [geometryAxisSigmaMap_comp,
    finiteAxisFoldSouthwestPermutationGeometrySectionHom,
    finiteAxisFoldSourcePermutationGeometryFiberSectionHom,
    finiteAxisFoldSourcePermutationGeometryAut,
    finiteAxisFoldSourceGenericPermutation_axisSigmaMap_eq_id,
    canonical] using pointwise

/-- The exact-left pull of an arbitrary source permutation fixes every
dependent Axis value. -/
theorem finiteAxisFoldExactLeftGenericPermutation_axisSigmaMap_eq_id :
    geometryAxisSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 =
      _root_.id := by
  let lift := exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber
  have liftInjective : Function.Injective (geometryAxisSigmaMap lift) := by
    exact exactGeometryPullAxisSigmaMap_injective
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber
  funext value
  apply liftInjective
  have factorization := congrArg geometryAxisSigmaMap
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      (southwestGenericPermutationAut).hom)
  have pointwise := congrFun factorization value
  change geometryAxisSigmaMap lift
      (geometryAxisSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 value) =
    geometryAxisSigmaMap (southwestGenericPermutationAut).hom.1
      (geometryAxisSigmaMap lift value) at pointwise
  rw [finiteAxisFoldSouthwestGenericPermutation_axisSigmaMap_eq_id] at pointwise
  simpa using pointwise

/-- The fixed top transport of an arbitrary source permutation fixes every
dependent Axis value. -/
theorem finiteAxisFoldActualDirectGenericPermutation_axisSigmaMap_eq_id :
    geometryAxisSigmaMap (actualDirectGenericPermutationAut).hom.1 =
      _root_.id := by
  let lift := geomFiberLift
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    FiniteAxisFoldGenericPermutationLocalPulledGeometryFiber
  have liftSurjective : Function.Surjective (geometryAxisSigmaMap lift) := by
    exact geomFiberLiftAxisSigmaMap_surjective
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldGenericPermutationLocalPulledGeometryFiber
  funext value
  obtain ⟨sourceValue, rfl⟩ := liftSurjective value
  have factorization := congrArg geometryAxisSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          (southwestGenericPermutationAut).hom))
  have pointwise := congrFun factorization sourceValue
  change geometryAxisSigmaMap (actualDirectGenericPermutationAut).hom.1
      (geometryAxisSigmaMap lift sourceValue) =
    geometryAxisSigmaMap lift
      (geometryAxisSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 sourceValue) at pointwise
  rw [finiteAxisFoldExactLeftGenericPermutation_axisSigmaMap_eq_id] at pointwise
  simpa [finiteAxisFoldActualDirectPermutationGeometrySectionHom] using pointwise

/-- Normalization preserves the complete dependent Axis identity. -/
theorem finiteAxisFoldNormalizedGenericPermutation_axisSigmaMap_eq_id :
    geometryAxisSigmaMap (normalizedGenericPermutationAut).hom.f.hom =
      _root_.id := by
  change geometryAxisSigmaMap (actualDirectGenericPermutationAut).hom.1 =
    _root_.id
  exact finiteAxisFoldActualDirectGenericPermutation_axisSigmaMap_eq_id
    permutation

/-! ## Complete dependent Observable action -/

/-- The primitive source permutation fixes every dependent Observable value. -/
theorem finiteAxisFoldSourceGenericPermutation_observableSigmaMap_eq_id :
    geometryObservableSigmaMap genericPermutationGeometry = _root_.id := by
  funext value
  rcases value with ⟨context, observable⟩
  rfl

/-- The southwest transport of an arbitrary source permutation fixes every
dependent Observable value. -/
theorem finiteAxisFoldSouthwestGenericPermutation_observableSigmaMap_eq_id :
    geometryObservableSigmaMap (southwestGenericPermutationAut).hom.1 =
      _root_.id := by
  let canonical := geomFiberLift finiteAxisFoldSourceToSouthwestExtInstHom
    (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  have canonicalSurjective :
      Function.Surjective (geometryObservableSigmaMap canonical) := by
    exact geomFiberLiftObservableSigmaMap_surjective
      finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  funext value
  obtain ⟨sourceValue, rfl⟩ := canonicalSurjective value
  have factorization := congrArg geometryObservableSigmaMap
    (geomFiberTransportMap_fac finiteAxisFoldSourceToSouthwestExtInstHom
      (genericPermutationGeometryFiberAut).hom)
  have pointwise := congrFun factorization sourceValue
  simpa [geometryObservableSigmaMap_comp,
    finiteAxisFoldSouthwestPermutationGeometrySectionHom,
    finiteAxisFoldSourcePermutationGeometryFiberSectionHom,
    finiteAxisFoldSourcePermutationGeometryAut,
    finiteAxisFoldSourceGenericPermutation_observableSigmaMap_eq_id,
    canonical] using pointwise

/-- The exact-left pull of an arbitrary source permutation fixes every
dependent Observable value. -/
theorem finiteAxisFoldExactLeftGenericPermutation_observableSigmaMap_eq_id :
    geometryObservableSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 =
      _root_.id := by
  let lift := exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber
  have liftInjective : Function.Injective (geometryObservableSigmaMap lift) := by
    exact exactGeometryPullObservableSigmaMap_injective
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber
  funext value
  apply liftInjective
  have factorization := congrArg geometryObservableSigmaMap
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      (southwestGenericPermutationAut).hom)
  have pointwise := congrFun factorization value
  change geometryObservableSigmaMap lift
      (geometryObservableSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 value) =
    geometryObservableSigmaMap (southwestGenericPermutationAut).hom.1
      (geometryObservableSigmaMap lift value) at pointwise
  rw [finiteAxisFoldSouthwestGenericPermutation_observableSigmaMap_eq_id]
    at pointwise
  simpa using pointwise

/-- The fixed top transport of an arbitrary source permutation fixes every
dependent Observable value. -/
theorem finiteAxisFoldActualDirectGenericPermutation_observableSigmaMap_eq_id :
    geometryObservableSigmaMap (actualDirectGenericPermutationAut).hom.1 =
      _root_.id := by
  let lift := geomFiberLift
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    FiniteAxisFoldGenericPermutationLocalPulledGeometryFiber
  have liftSurjective :
      Function.Surjective (geometryObservableSigmaMap lift) := by
    exact geomFiberLiftObservableSigmaMap_surjective
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldGenericPermutationLocalPulledGeometryFiber
  funext value
  obtain ⟨sourceValue, rfl⟩ := liftSurjective value
  have factorization := congrArg geometryObservableSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          (southwestGenericPermutationAut).hom))
  have pointwise := congrFun factorization sourceValue
  change geometryObservableSigmaMap (actualDirectGenericPermutationAut).hom.1
      (geometryObservableSigmaMap lift sourceValue) =
    geometryObservableSigmaMap lift
      (geometryObservableSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1 sourceValue) at pointwise
  rw [finiteAxisFoldExactLeftGenericPermutation_observableSigmaMap_eq_id]
    at pointwise
  simpa [finiteAxisFoldActualDirectPermutationGeometrySectionHom] using pointwise

/-- Normalization preserves the complete dependent Observable identity. -/
theorem finiteAxisFoldNormalizedGenericPermutation_observableSigmaMap_eq_id :
    geometryObservableSigmaMap (normalizedGenericPermutationAut).hom.f.hom =
      _root_.id := by
  change geometryObservableSigmaMap (actualDirectGenericPermutationAut).hom.1 =
    _root_.id
  exact finiteAxisFoldActualDirectGenericPermutation_observableSigmaMap_eq_id
    permutation

/-! ## Joint local-fiber kernel landing -/

/-- Every local Support equivalence induced by the normalized arbitrary
permutation is the identity. -/
theorem finiteAxisFoldNormalizedGenericPermutation_supportEquiv_eq_one
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelSupportEquiv
        (finiteAxisFoldNormalizedPermutationContextKernelSectionHom E permutation)
        context = 1 := by
  apply Equiv.ext
  intro support
  rw [finiteAxisFoldResidualContextKernelSupportEquiv_apply]
  have pairEquality := congrFun
    (finiteAxisFoldNormalizedGenericPermutation_supportSigmaMap_eq_id permutation)
    (⟨context, support⟩ :
      Sigma fun value : FiniteAxisFoldResidualContextObject =>
        value.ctx.Support)
  have localEquality := support_eq_of_sigma_eq pairEquality
  convert localEquality using 1

/-- Every local Axis equivalence induced by the normalized arbitrary
permutation is the identity. -/
theorem finiteAxisFoldNormalizedGenericPermutation_axisEquiv_eq_one
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelAxisEquiv
        (finiteAxisFoldNormalizedPermutationContextKernelSectionHom E permutation)
        context = 1 := by
  apply Equiv.ext
  intro axis
  rw [finiteAxisFoldResidualContextKernelAxisEquiv_apply]
  have pairEquality := congrFun
    (finiteAxisFoldNormalizedGenericPermutation_axisSigmaMap_eq_id permutation)
    (⟨context, axis⟩ :
      Sigma fun value : FiniteAxisFoldResidualContextObject =>
        value.ctx.Axis)
  have localEquality := axis_eq_of_sigma_eq pairEquality
  convert localEquality using 1

/-- Every local Observable equivalence induced by the normalized arbitrary
permutation is the identity. -/
theorem finiteAxisFoldNormalizedGenericPermutation_observableEquiv_eq_one
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelObservableEquiv
        (finiteAxisFoldNormalizedPermutationContextKernelSectionHom E permutation)
        context = 1 := by
  apply Equiv.ext
  intro observable
  rw [finiteAxisFoldResidualContextKernelObservableEquiv_apply]
  have pairEquality := congrFun
    (finiteAxisFoldNormalizedGenericPermutation_observableSigmaMap_eq_id permutation)
    (⟨context, observable⟩ :
      Sigma fun value : FiniteAxisFoldResidualContextObject =>
        value.ctx.Observable)
  have localEquality := observable_eq_of_sigma_eq pairEquality
  convert localEquality using 1

/-- The complete arbitrary finite permutation family lands in the actual joint
residual local-fiber kernel. -/
theorem finiteAxisFoldNormalizedGenericPermutation_mem_localFiberKernel :
    finiteAxisFoldNormalizedPermutationContextKernelSectionHom E permutation ∈
      FiniteAxisFoldResidualLocalFiberKernel := by
  rw [finiteAxisFoldResidualLocalFiberKernel_mem_iff]
  exact ⟨finiteAxisFoldNormalizedGenericPermutation_supportEquiv_eq_one permutation,
    finiteAxisFoldNormalizedGenericPermutation_axisEquiv_eq_one permutation,
      finiteAxisFoldNormalizedGenericPermutation_observableEquiv_eq_one permutation⟩

/-- The arbitrary finite Extension action as a homomorphism into the actual
joint residual local-fiber kernel. -/
noncomputable def finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom
    (E : Type) :
    Equiv.Perm E →* FiniteAxisFoldResidualLocalFiberKernel :=
  (finiteAxisFoldNormalizedPermutationContextKernelSectionHom E).codRestrict
    FiniteAxisFoldResidualLocalFiberKernel
    (fun permutation =>
      finiteAxisFoldNormalizedGenericPermutation_mem_localFiberKernel permutation)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end
end AAT.AG.RealizationReconstruction
