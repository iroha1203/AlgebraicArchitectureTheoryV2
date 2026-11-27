import Formal.SHIGURE.Part2.Schemes.ModuleSheafMultilinearPullback

/-! # The adjoint formula for actual scheme operations on sections -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory Opposite PiTensorProduct

noncomputable section

universe u

variable {X : Scheme.{u}} {I : Type u} {M N : I → X.Modules} {P Q : X.Modules}

/-- The sectionwise multilinear map is computed by the adjoint map on tensors. -/
private def tensorAdjunct (a : moduleMultilinearTensor M ⟶ P) :
    moduleMultilinearPresheaf (R := X.sheaf.val) (fun i => (M i).val) ⟶ P.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _ a

/-- Read the sheafified map by evaluating its adjoint on one pure tensor. -/
private theorem read_tensorAdjunct (a : moduleMultilinearTensor M ⟶ P)
    (U : X.Opensᵒᵖ) (x : ∀ i, (M i).val.obj U) :
    (moduleMultilinearTensorHomEquiv M P a).app U x =
      (tensorAdjunct a).app U (tprod (X.sheaf.val.obj U) x) :=
  rfl

/-- Postcomposing a tensor operation applies the original map to its result. -/
private theorem sectionPostcompose (a : moduleMultilinearTensor M ⟶ P)
    (g : P ⟶ Q) (U : X.Opensᵒᵖ) (x : ∀ i, (M i).val.obj U) :
    (moduleMultilinearTensorHomEquiv M Q (a ≫ g)).app U x =
      g.val.app U ((moduleMultilinearTensorHomEquiv M P a).app U x) := by
  have comparison : tensorAdjunct (a ≫ g) = tensorAdjunct a ≫ g.val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv_naturality_right a g
  rw [read_tensorAdjunct, comparison, read_tensorAdjunct]
  rfl

/-- Precomposing with the tensor of input maps applies the original maps to
each section fed to the operation. -/
private theorem sectionPrecompose (f : ∀ i, M i ⟶ N i)
    (a : moduleMultilinearTensor N ⟶ P) (U : X.Opensᵒᵖ) (x : ∀ i, (M i).val.obj U) :
    (moduleMultilinearTensorHomEquiv M P (moduleMultilinearTensorMap f ≫ a)).app U x =
      (moduleMultilinearTensorHomEquiv N P a).app U (fun i => (f i).val.app U (x i)) := by
  let s := moduleMultilinearPresheafMap (R := X.sheaf.val) (fun i => (f i).val)
  have comparison : tensorAdjunct (moduleMultilinearTensorMap f ≫ a) = s ≫ tensorAdjunct a :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv_naturality_left s a
  rw [read_tensorAdjunct, comparison, read_tensorAdjunct]
  change (tensorAdjunct a).app U (s.app U (tprod (X.sheaf.val.obj U) x)) = _
  exact congrArg ((tensorAdjunct a).app U) (moduleMultilinearPresheafMap_app_tprod _ U x)

section Adjunction

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct-image comparison followed by the direct image of an operation
reads that operation on the actual inverse-image open. -/
theorem moduleMultilinearPushforwardComparison_read (M : I → X.Modules) (P : X.Modules)
    (a : moduleMultilinearTensor M ⟶ P) (U : Y.Opensᵒᵖ)
    (x : ∀ i, ((pushforward f).obj (M i)).val.obj U) :
    (moduleMultilinearTensorHomEquiv (fun i => (pushforward f).obj (M i)) ((pushforward f).obj P)
      (moduleMultilinearPushforwardComparison f M ≫ (pushforward f).map a)).app U x =
      (moduleMultilinearTensorHomEquiv M P a).app (op (f ⁻¹ᵁ U.unop)) x := by
  let N := moduleMultilinearTensor M
  let V := op (f ⁻¹ᵁ U.unop)
  let v := moduleMultilinearTensorHomEquiv (fun i => (pushforward f).obj (M i)) ((pushforward f).obj N)
  let w := (moduleMultilinearTensorHomEquiv M N (𝟙 N)).pushforward f
  have zeroStep : v (moduleMultilinearPushforwardComparison f M) = w :=
    v.apply_symm_apply w
  have evaluated := sectionPostcompose (moduleMultilinearPushforwardComparison f M) ((pushforward f).map a) U x
  rw [zeroStep] at evaluated
  have direct := sectionPostcompose (𝟙 N) a V x
  rw [Category.id_comp] at direct
  exact evaluated.trans direct.symm

/-- The adjunct of a comparison followed by an operation is evaluated by
applying the adjunct of each original factor map to its input section. -/
theorem moduleMultilinearPullbackComparison_read
    (N : I → Y.Modules) (M : I → X.Modules) (P : X.Modules)
    (v : ∀ i, (pullback f).obj (N i) ⟶ M i) (a : moduleMultilinearTensor M ⟶ P)
    (U : Y.Opensᵒᵖ) (x : ∀ i, (N i).val.obj U) :
    let adj := pullbackPushforwardAdjunction f
    (moduleMultilinearTensorHomEquiv N ((pushforward f).obj P)
      (adj.homEquiv _ _
        (moduleMultilinearPullbackComparison f N ≫ moduleMultilinearTensorMap v ≫ a))).app U x =
      (moduleMultilinearTensorHomEquiv M P a).app (op (f ⁻¹ᵁ U.unop))
        (fun i => (adj.homEquiv _ _ (v i)).val.app U (x i)) := by
  let adj := pullbackPushforwardAdjunction f
  let P' := pushforward f
  let M' (i : I) := (pullback f).obj (N i)
  let C := moduleMultilinearPushforwardComparison f M'
  let u (i : I) := adj.unit.app (N i)
  let W := moduleMultilinearTensorMap v ≫ a
  have eq : adj.homEquiv _ _ (moduleMultilinearPullbackComparison f N ≫ W) =
      moduleMultilinearTensorMap u ≫ C ≫ P'.map W := by
    rw [adj.homEquiv_naturality_right]
    have initial : adj.homEquiv _ _ (moduleMultilinearPullbackComparison f N) =
        moduleMultilinearTensorMap u ≫ C :=
      (adj.homEquiv _ _).apply_symm_apply _
    rw [initial, Category.assoc]
  change (moduleMultilinearTensorHomEquiv N (P'.obj P)
      (adj.homEquiv _ _ (moduleMultilinearPullbackComparison f N ≫ W))).app U x = _
  rw [eq, sectionPrecompose]
  let y (i : I) := (u i).val.app U (x i)
  let V := op (f ⁻¹ᵁ U.unop)
  have first := moduleMultilinearPushforwardComparison_read f M' P W U y
  have next := sectionPrecompose v a V y
  exact first.trans next

/-- Evaluating the adjunct of a pulled-back operation uses the original
value followed by the adjunct of the given target map. -/
theorem moduleMultilinearOriginalBaseChange_read
    (N : I → Y.Modules) (A : Y.Modules) (P : X.Modules)
    (a : moduleMultilinearTensor N ⟶ A) (v : (pullback f).obj A ⟶ P)
    (U : Y.Opensᵒᵖ) (x : ∀ i, (N i).val.obj U) :
    let adj := pullbackPushforwardAdjunction f
    (moduleMultilinearTensorHomEquiv N ((pushforward f).obj P)
      (adj.homEquiv _ _ ((pullback f).map a ≫ v))).app U x =
      (adj.homEquiv _ _ v).val.app U
        ((moduleMultilinearTensorHomEquiv N A a).app U x) := by
  let adj := pullbackPushforwardAdjunction f
  change (moduleMultilinearTensorHomEquiv N ((pushforward f).obj P)
    (adj.homEquiv _ _ ((pullback f).map a ≫ v))).app U x = _
  rw [adj.homEquiv_naturality_left]
  exact sectionPostcompose a (adj.homEquiv _ _ v) U x

end Adjunction

end

end SHIGURE.SchemeDescent
