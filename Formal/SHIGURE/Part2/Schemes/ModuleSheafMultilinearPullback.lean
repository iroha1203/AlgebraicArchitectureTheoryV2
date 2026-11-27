import Formal.SHIGURE.Part2.Schemes.ModuleSheafMultilinear

/-! # The natural comparison for pulling back sheaf tensors -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

variable {X Y : Scheme.{u}} {I : Type u}
  {M : I → X.Modules} {P : X.Modules}

/-- A compatible multilinear operation pushes forward by taking its original
value on the inverse-image open and restricting the scalars there. -/
def MultilinearSectionFamily.pushforward (f : X ⟶ Y)
    (a : MultilinearSectionFamily (R := X.sheaf.val) (fun i => (M i).val) P.val) :
    MultilinearSectionFamily (R := Y.sheaf.val)
      (fun i => ((pushforward f).obj (M i)).val) ((pushforward f).obj P).val where
  app U :=
    { toFun := fun x => a.app (op (f ⁻¹ᵁ U.unop)) x
      map_update_add' := by
        intro _ x i y z
        exact (a.app (op (f ⁻¹ᵁ U.unop))).map_update_add x i y z
      map_update_smul' := by
        intro _ x i r y
        exact (a.app (op (f ⁻¹ᵁ U.unop))).map_update_smul x i ((f.app U.unop).hom r) y }
  naturality {U V} g x :=
    a.naturality ((Opens.map f.base).map g.unop).op x

/-- The tensor of direct images maps to the direct image of the tensor. -/
def moduleMultilinearPushforwardComparison (f : X ⟶ Y) (M : I → X.Modules) :
    moduleMultilinearTensor (fun i => (pushforward f).obj (M i)) ⟶
      (pushforward f).obj (moduleMultilinearTensor M) :=
  (moduleMultilinearTensorHomEquiv _ _).symm
    ((moduleMultilinearTensorHomEquiv M _ (𝟙 _)).pushforward f)

/-- The adjoint comparison from the inverse image of the tensor to the
tensor of the inverse images is induced by the units of the original module adjunction. -/
def moduleMultilinearPullbackComparison (f : X ⟶ Y) (N : I → Y.Modules) :
    (pullback f).obj (moduleMultilinearTensor N) ⟶
      moduleMultilinearTensor (fun i => (pullback f).obj (N i)) :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (moduleMultilinearTensorMap (fun i => (pullbackPushforwardAdjunction f).unit.app (N i)) ≫
      moduleMultilinearPushforwardComparison f (fun i => (pullback f).obj (N i)))

end

end SHIGURE.SchemeDescent
