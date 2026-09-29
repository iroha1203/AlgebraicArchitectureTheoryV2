import ResearchLean.AG.AbelianLiftingObstruction.GeometryKernel
import ResearchLean.AG.AbelianLiftingObstruction.CrossStageKernel
import ResearchLean.AG.AbelianLiftingObstruction.KernelTransportLaws

/-!
# Applying the actual-kernel construction to the concrete geometry input

G-129 A/D and completion condition 4: the full abelian `InnerFiberAut` is
transported through the arrow-preserving kernel equivalence. Identity-edge
transport is computed by the general construction and is bijective.
The same nonidentity coefficient swap centralizes this entire actual kernel.
-/

namespace AAT.AG.AbelianLiftingObstruction.GeometryKernelTransport

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence.Arbitrary GeometryInput

/-- The coefficient group is the kernel of the actual geometry-to-core pushforward. -/
noncomputable abbrev ActualKernel :=
  Kernel (geometryProjection FiniteModel.carrier) (packageProjection FiniteModel.carrier) package

/-- G-129 A condition 1 is discharged on the same actual kernel through the full equivalence. -/
noncomputable instance actualKernelCommGroup : CommGroup ActualKernel :=
  kernelCommGroup _ _ _ (fun a b => by
    apply (innerKernelEquiv package).symm.injective
    rw [map_mul, map_mul]
    exact GeometryKernel.inner_mul_comm _ _)

/-- The authored nonidentity element is the original full coefficient-swap automorphism. -/
noncomputable def authoredKernelElement : ActualKernel := innerKernelEquiv package innerSwap

/-- API: this comparison remains nonidentity in the actual kernel. -/
theorem authoredKernelElement_ne_one : authoredKernelElement ≠ 1 := by
  intro h
  apply innerSwap_ne_one
  apply (innerKernelEquiv package).injective
  exact h.trans (map_one (innerKernelEquiv package)).symm

/-- G-129 concrete input: additivization preserves a nontrivial coefficient group. -/
instance actualKernelNontrivial : Nontrivial ActualKernel :=
  ⟨⟨authoredKernelElement, 1, authoredKernelElement_ne_one⟩⟩

/-- The actual identity edge satisfies the upper strong-lifting requirement. -/
theorem upper_identity_strong :
    (geometryProjection FiniteModel.carrier ⋙ packageProjection FiniteModel.carrier).IsStronglyCocartesian
      (𝟙 (packagePoint core)) (𝟙 package) :=
  identityStrong _ _

/-- The image of the actual identity edge satisfies the lower strong-lifting requirement. -/
theorem lower_identity_strong :
    (packageProjection FiniteModel.carrier).IsStronglyCocartesian (𝟙 (packagePoint core))
      ((geometryProjection FiniteModel.carrier).map (𝟙 package)) :=
  identityStrong _ _

/-- The general kernel transport on this input's identity edge. -/
noncomputable def identityTransport : ActualKernel →* ActualKernel :=
  kernelTransportHom _ _ (𝟙 package) upper_identity_strong lower_identity_strong

/-- G-129 A condition 2 is discharged by computation of the same general map. -/
theorem identityTransport_eq_id : identityTransport = MonoidHom.id ActualKernel :=
  kernelTransport_identity _ _ package

/-- API: every actual kernel element is unchanged by the selected edge. -/
@[simp] theorem identityTransport_apply (a : ActualKernel) : identityTransport a = a :=
  DFunLike.congr_fun identityTransport_eq_id a

/-- G-129 A condition 2: no bijectivity assumption is needed on this concrete input. -/
theorem identityTransport_bijective : Function.Bijective identityTransport := by
  rw [identityTransport_eq_id]
  exact Function.bijective_id

/-- G-129 A condition 3: the nonidentity authored comparison centralizes the whole kernel. -/
theorem authored_centralizes (a : ActualKernel) :
    kernelInclusion _ _ package authoredKernelElement * kernelInclusion _ _ package a =
      kernelInclusion _ _ package a * kernelInclusion _ _ package authoredKernelElement := by
  rw [← map_mul, ← map_mul, mul_comm authoredKernelElement a]

/-- The actual-kernel identification preserves the coefficient action on the original arrow. -/
theorem authored_coefficient_first :
    (FiberAut.hom (kernelInclusion _ _ package authoredKernelElement)).geometry.coefficientHom
      ((1, 0) : package.Coefficient) = (0, 1) := rfl

/-- API for the later same-input obstruction: the authored element is not a square. -/
theorem authored_not_square (a : ActualKernel) : a * a ≠ authoredKernelElement := by
  intro h
  apply GeometryKernel.innerSwap_not_square ((innerKernelEquiv package).symm a)
  have hm := congrArg (innerKernelEquiv package).symm h
  simpa only [map_mul, authoredKernelElement, MulEquiv.symm_apply_apply] using hm

end AAT.AG.AbelianLiftingObstruction.GeometryKernelTransport

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.GeometryKernelTransport
