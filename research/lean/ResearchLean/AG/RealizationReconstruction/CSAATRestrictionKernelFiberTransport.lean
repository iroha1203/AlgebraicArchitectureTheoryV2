import ResearchLean.AG.RealizationReconstruction.CSAATFullyFaithfulComparisonTransport
import Formal.Util.AssertStandardAxioms

/-!
# Restricted-kernel and lift-fiber transport

A commuting square of group homomorphisms whose horizontal maps are group
equivalences transports the literal kernel of the vertical restriction and
every literal restriction fiber.  The fibers carry their intrinsic free and
transitive right action by the opposite kernel, and the transported fiber
equivalence intertwines those actions.

The final section applies this construction to the source projection from the
whole comparison group transported by a fully faithful realization.  This is
the restricted comparison kernel.  No ambient endpoint kernel is identified
with it here; ambient restriction is a separate homomorphism and remains a
separate G-123(D) obligation.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v w x

noncomputable section

namespace RestrictionKernelFiberTransport

variable {G H G' H' : Type*}
variable [Group G] [Group H] [Group G'] [Group H']

/-- The literal fiber of a group homomorphism over one target element. -/
abbrev Fiber (r : G →* H) (h : H) := {g : G // r g = h}

/-- Named right multiplication by the literal kernel preserves every fiber.
It is deliberately not a global `SMul` instance, so it cannot collide with
model-specific fiber actions. -/
def rightKernelAction (r : G →* H) (h : H)
    (kernelElement : (MonoidHom.ker r)ᵐᵒᵖ) (point : Fiber r h) :
    Fiber r h :=
  ⟨point.1 * (MulOpposite.unop kernelElement).1, by
    rw [map_mul, point.property,
      MonoidHom.mem_ker.mp (MulOpposite.unop kernelElement).property,
      mul_one]⟩

theorem rightKernelAction_one (r : G →* H) (h : H) (point : Fiber r h) :
    rightKernelAction r h 1 point = point := by
  apply Subtype.ext
  exact mul_one point.1

theorem rightKernelAction_mul (r : G →* H) (h : H)
    (first second : (MonoidHom.ker r)ᵐᵒᵖ) (point : Fiber r h) :
    rightKernelAction r h (first * second) point =
      rightKernelAction r h first (rightKernelAction r h second point) := by
  apply Subtype.ext
  exact (mul_assoc point.1
    (MulOpposite.unop second).1 (MulOpposite.unop first).1).symm

/-- The literal kernel action on each nonempty fiber is free. -/
theorem fiber_action_free (r : G →* H) (h : H) (point : Fiber r h) :
    Function.Injective
      (fun kernelElement : (MonoidHom.ker r)ᵐᵒᵖ =>
        rightKernelAction r h kernelElement point) := by
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have values := congrArg (fun value : Fiber r h => value.1) equality
  exact mul_left_cancel values

/-- Any two points of one literal fiber differ by a kernel element. -/
theorem fiber_action_transitive (r : G →* H) (h : H)
    (first second : Fiber r h) :
    ∃ kernelElement : (MonoidHom.ker r)ᵐᵒᵖ,
      rightKernelAction r h kernelElement first = second := by
  let displacement : G := first.1⁻¹ * second.1
  have displacement_mem : displacement ∈ MonoidHom.ker r := by
    rw [MonoidHom.mem_ker]
    change r (first.1⁻¹ * second.1) = 1
    rw [map_mul, map_inv, first.property, second.property, inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, displacement_mem⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- The kernel displacement between two points of one fiber is unique. -/
theorem fiber_existsUnique_smul_eq (r : G →* H) (h : H)
    (first second : Fiber r h) :
    ∃! kernelElement : (MonoidHom.ker r)ᵐᵒᵖ,
      rightKernelAction r h kernelElement first = second := by
  rcases fiber_action_transitive r h first second with ⟨kernelElement, equality⟩
  refine ⟨kernelElement, equality, ?_⟩
  intro other otherEquality
  exact fiber_action_free r h first (otherEquality.trans equality.symm)

/-- A commuting square with horizontal equivalences transports the restricted
kernel.  Kernel membership is reconstructed from the square, not supplied as
an additional field. -/
noncomputable def kernelMulEquiv
    (r : G →* H) (r' : G' →* H') (E : G ≃* G') (B : H ≃* H')
    (commutes : ∀ g, r' (E g) = B (r g)) :
    MonoidHom.ker r ≃* MonoidHom.ker r' where
  toFun kernelElement := ⟨E kernelElement.1, by
    rw [MonoidHom.mem_ker, commutes,
      MonoidHom.mem_ker.mp kernelElement.property, map_one]⟩
  invFun kernelElement := ⟨E.symm kernelElement.1, by
    rw [MonoidHom.mem_ker]
    apply B.injective
    rw [← commutes, E.apply_symm_apply,
      MonoidHom.mem_ker.mp kernelElement.property, map_one]⟩
  left_inv kernelElement := by
    apply Subtype.ext
    exact E.symm_apply_apply kernelElement.1
  right_inv kernelElement := by
    apply Subtype.ext
    exact E.apply_symm_apply kernelElement.1
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul E first.1 second.1

/-- The same square transports every literal lift fiber, over the transported
base element. -/
noncomputable def fiberEquiv
    (r : G →* H) (r' : G' →* H') (E : G ≃* G') (B : H ≃* H')
    (commutes : ∀ g, r' (E g) = B (r g)) (h : H) :
    Fiber r h ≃ Fiber r' (B h) where
  toFun point := ⟨E point.1, by rw [commutes, point.property]⟩
  invFun point := ⟨E.symm point.1, by
    apply B.injective
    rw [← commutes, E.apply_symm_apply, point.property]⟩
  left_inv point := by
    apply Subtype.ext
    exact E.symm_apply_apply point.1
  right_inv point := by
    apply Subtype.ext
    exact E.apply_symm_apply point.1

/-- Fiber transport respects the literal right action of the corresponding
restricted kernels. -/
theorem fiberEquiv_smul
    (r : G →* H) (r' : G' →* H') (E : G ≃* G') (B : H ≃* H')
    (commutes : ∀ g, r' (E g) = B (r g)) (h : H)
    (kernelElement : (MonoidHom.ker r)ᵐᵒᵖ) (point : Fiber r h) :
    fiberEquiv r r' E B commutes h
        (rightKernelAction r h kernelElement point) =
      rightKernelAction r' (B h)
        (MulOpposite.op
          (kernelMulEquiv r r' E B commutes
            (MulOpposite.unop kernelElement)))
        (fiberEquiv r r' E B commutes h point) := by
  apply Subtype.ext
  change E (point.1 * (MulOpposite.unop kernelElement).1) =
    E point.1 * E (MulOpposite.unop kernelElement).1
  exact map_mul E point.1 (MulOpposite.unop kernelElement).1

end RestrictionKernelFiberTransport

/-! ## Source-restriction specialization for a fully faithful realization -/

/-- The restricted source-projection kernels of the complete comparison
groups correspond under a fully faithful realization. -/
noncomputable def generatedArrowComparisonSourceKernelMulEquiv
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y) :
    MonoidHom.ker (generatedArrowComparisonSourceHom c) ≃*
      MonoidHom.ker (generatedArrowComparisonSourceHom (F.map c)) :=
  RestrictionKernelFiberTransport.kernelMulEquiv
    (generatedArrowComparisonSourceHom c)
    (generatedArrowComparisonSourceHom (F.map c))
    (generatedArrowComparisonMulEquivOfFullyFaithful F hf c)
    (fullyFaithfulEndpointAutMulEquiv F hf X)
    (generatedArrowComparison_source_compatibility F hf c)

/-- Every source-restriction lift fiber is recovered, not only a chosen lift. -/
noncomputable def generatedArrowComparisonSourceFiberEquiv
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y)
    (a : Aut X) :
    RestrictionKernelFiberTransport.Fiber
        (generatedArrowComparisonSourceHom c) a ≃
      RestrictionKernelFiberTransport.Fiber
        (generatedArrowComparisonSourceHom (F.map c))
        (fullyFaithfulEndpointAutMulEquiv F hf X a) :=
  RestrictionKernelFiberTransport.fiberEquiv
    (generatedArrowComparisonSourceHom c)
    (generatedArrowComparisonSourceHom (F.map c))
    (generatedArrowComparisonMulEquivOfFullyFaithful F hf c)
    (fullyFaithfulEndpointAutMulEquiv F hf X)
    (generatedArrowComparison_source_compatibility F hf c) a

/-- The comparison-fiber equivalence intertwines the restricted source-kernel
actions. -/
theorem generatedArrowComparisonSourceFiberEquiv_smul
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y)
    (a : Aut X)
    (kernelElement :
      (MonoidHom.ker (generatedArrowComparisonSourceHom c))ᵐᵒᵖ)
    (point : RestrictionKernelFiberTransport.Fiber
      (generatedArrowComparisonSourceHom c) a) :
    generatedArrowComparisonSourceFiberEquiv F hf c a
        (RestrictionKernelFiberTransport.rightKernelAction
          (generatedArrowComparisonSourceHom c) a kernelElement point) =
      RestrictionKernelFiberTransport.rightKernelAction
        (generatedArrowComparisonSourceHom (F.map c))
        (fullyFaithfulEndpointAutMulEquiv F hf X a)
        (MulOpposite.op
          (generatedArrowComparisonSourceKernelMulEquiv F hf c
            (MulOpposite.unop kernelElement)))
        (generatedArrowComparisonSourceFiberEquiv F hf c a point) :=
  RestrictionKernelFiberTransport.fiberEquiv_smul
    (generatedArrowComparisonSourceHom c)
    (generatedArrowComparisonSourceHom (F.map c))
    (generatedArrowComparisonMulEquivOfFullyFaithful F hf c)
    (fullyFaithfulEndpointAutMulEquiv F hf X)
    (generatedArrowComparison_source_compatibility F hf c) a
    kernelElement point

/-! ## Independent generated-package applications -/

/-- Lens generated packages recover the whole restricted source kernel. -/
noncomputable def lensAATIndependentPackageComparisonSourceKernelMulEquiv
    (input : LensFamilyInput.{u})
    {X Y : LensAATIndependentPackageObject input} (c : X ⟶ Y) :
    MonoidHom.ker (generatedArrowComparisonSourceHom c) ≃*
      MonoidHom.ker (generatedArrowComparisonSourceHom
        ((lensAATIndependentPackageSemanticFunctor input).map c)) :=
  generatedArrowComparisonSourceKernelMulEquiv
    (lensAATIndependentPackageSemanticFunctor input)
    (lensAATIndependentPackageSemanticFullyFaithful input) c

/-- Lens generated packages recover every source-projection lift fiber. -/
noncomputable def lensAATIndependentPackageComparisonSourceFiberEquiv
    (input : LensFamilyInput.{u})
    {X Y : LensAATIndependentPackageObject input} (c : X ⟶ Y)
    (a : Aut X) :
    RestrictionKernelFiberTransport.Fiber
        (generatedArrowComparisonSourceHom c) a ≃
      RestrictionKernelFiberTransport.Fiber
        (generatedArrowComparisonSourceHom
          ((lensAATIndependentPackageSemanticFunctor input).map c))
        (lensAATIndependentPackageAutMulEquiv input X a) :=
  generatedArrowComparisonSourceFiberEquiv
    (lensAATIndependentPackageSemanticFunctor input)
    (lensAATIndependentPackageSemanticFullyFaithful input) c a

/-- Protocol generated packages recover the whole restricted source kernel. -/
noncomputable def protocolAATIndependentPackageComparisonSourceKernelMulEquiv
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolAATIndependentPackageObject input} (c : X ⟶ Y) :
    MonoidHom.ker (generatedArrowComparisonSourceHom c) ≃*
      MonoidHom.ker (generatedArrowComparisonSourceHom
        ((protocolAATIndependentPackageSemanticFunctor input).map c)) :=
  generatedArrowComparisonSourceKernelMulEquiv
    (protocolAATIndependentPackageSemanticFunctor input)
    (protocolAATIndependentPackageSemanticFullyFaithful input) c

/-- Protocol generated packages recover every source-projection lift fiber. -/
noncomputable def protocolAATIndependentPackageComparisonSourceFiberEquiv
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolAATIndependentPackageObject input} (c : X ⟶ Y)
    (a : Aut X) :
    RestrictionKernelFiberTransport.Fiber
        (generatedArrowComparisonSourceHom c) a ≃
      RestrictionKernelFiberTransport.Fiber
        (generatedArrowComparisonSourceHom
          ((protocolAATIndependentPackageSemanticFunctor input).map c))
        (protocolAATIndependentPackageAutMulEquiv input X a) :=
  generatedArrowComparisonSourceFiberEquiv
    (protocolAATIndependentPackageSemanticFunctor input)
    (protocolAATIndependentPackageSemanticFullyFaithful input) c a

end

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
