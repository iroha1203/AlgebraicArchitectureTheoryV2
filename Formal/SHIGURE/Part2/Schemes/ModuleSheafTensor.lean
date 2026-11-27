import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Tensor operations on module sheaves

## Implementation notes

The tensor in Appendix B.3 is the sheafification of the presheaf tensor
on sections. This construction describes all bilinear operations directly
over every open. A presentation using affine charts would have to compare
the constructions across all choices of affine cover.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TensorProduct

noncomputable section

universe u

variable {X : Scheme.{u}}

/-- The presheaf of tensors of sections uses the actual restriction maps
of the two input modules and the commutative structure sheaf. -/
def moduleTensorPresheaf (M N : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val

/-- The tensor product of module sheaves in the finite tensor operations of
B.3 is the associated sheaf of the presheaf of sectionwise tensors. -/
def moduleSheafTensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj (moduleTensorPresheaf M N)

/-- Morphisms from the sheaf tensor are precisely maps from sectionwise
tensor presheaves, by the actual module sheafification adjunction. -/
def moduleSheafTensorHomEquiv (M N P : X.Modules) :
    (moduleSheafTensor M N ⟶ P) ≃
      (moduleTensorPresheaf M N ⟶ (Scheme.Modules.toPresheafOfModules X).obj P) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _

/-- An operation on pairs of local sections is bilinear over the section
ring and commutes with the actual restriction maps. -/
@[ext]
structure BilinearSectionFamily (M N P : X.Modules) where
  /-- The bilinear operation over the section ring of the open. -/
  app (U : X.Opensᵒᵖ) :
    M.val.obj U →ₗ[X.sheaf.val.obj U] N.val.obj U →ₗ[X.sheaf.val.obj U] P.val.obj U
  /-- Restriction preserves the operation on all pairs of sections. -/
  naturality {U V : X.Opensᵒᵖ} (i : U ⟶ V) (m : M.val.obj U) (n : N.val.obj U) :
    P.val.map i (app U m n) = app V (M.val.map i m) (N.val.map i n)

variable {M N P : X.Modules}

/-- Restricting a pure tensor restricts each of its two factors. -/
theorem moduleTensorPresheaf_map_tmul {U V : X.Opensᵒᵖ} (i : U ⟶ V) (m : M.val.obj U) (n : N.val.obj U) :
    (moduleTensorPresheaf M N).map i (m ⊗ₜ[X.sheaf.val.obj U] n) =
      M.val.map i m ⊗ₜ[X.sheaf.val.obj V] N.val.map i n :=
  rfl

/-- The map on local tensors is obtained by the tensor-product
universal property at every open. -/
def BilinearSectionFamily.toPresheafHom (β : BilinearSectionFamily M N P) :
    moduleTensorPresheaf M N ⟶ P.val where
  app U := ModuleCat.ofHom (TensorProduct.lift (β.app U))
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    change TensorProduct.lift (β.app V) ((moduleTensorPresheaf M N).map i (m ⊗ₜ n)) =
      P.val.map i (TensorProduct.lift (β.app U) (m ⊗ₜ n))
    have source : TensorProduct.lift (β.app V) ((moduleTensorPresheaf M N).map i
        (m ⊗ₜ[X.sheaf.val.obj U] n)) = β.app V (M.val.map i m) (N.val.map i n) := by
      rw [moduleTensorPresheaf_map_tmul i m n]
      exact TensorProduct.lift.tmul _ _
    exact source.trans ((β.naturality i m n).symm.trans (congrArg (fun v => P.val.map i v)
      (TensorProduct.lift.tmul (f' := β.app U) m n).symm))

/-- Applying a map of tensor presheaves to pairs of pure tensors gives
a compatible bilinear family of local operations. -/
def BilinearSectionFamily.ofPresheafHom (f : moduleTensorPresheaf M N ⟶ P.val) :
    BilinearSectionFamily M N P where
  app U := TensorProduct.curry (f.app U).hom
  naturality {U V} i m n := by
    rw [TensorProduct.curry_apply, TensorProduct.curry_apply]
    have h := (PresheafOfModules.naturality_apply f i (m ⊗ₜ n)).symm
    change P.val.map i ((f.app U) (m ⊗ₜ n)) =
      (f.app V) ((moduleTensorPresheaf M N).map i (m ⊗ₜ n)) at h
    have equal := moduleTensorPresheaf_map_tmul i m n
    exact h.trans (congrArg (fun element : (moduleTensorPresheaf M N).obj V => (f.app V).hom element) equal)

/-- Bilinear operations on local sections give exactly the morphisms of the
tensor sheaf. -/
def moduleSheafTensorBilinearEquiv (M N P : X.Modules) :
    (moduleSheafTensor M N ⟶ P) ≃ BilinearSectionFamily M N P :=
  (moduleSheafTensorHomEquiv M N P).trans
    { toFun := BilinearSectionFamily.ofPresheafHom
      invFun := BilinearSectionFamily.toPresheafHom
      left_inv := fun f => by
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.MonoidalCategory.tensor_ext
        intros
        rfl
      right_inv := fun β => by
        ext
        rfl }

end

end SHIGURE.SchemeDescent
