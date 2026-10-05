import ResearchLean.AG.AtlasDefectComposition.SupportConeFunctor
import Formal.Util.AssertStandardAxioms
/-! # 台署名上の H¹ 核・余核関手

Implementation notes: 元の実比較を標準 homology へ送り、実可換正方形の
kernel・quotient map を用いる。点ごとの抽象線形同型は射の代わりにしない。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex Opposite
namespace AAT.AG.AtlasDefectComposition.SupportFunctor
open CanonicalResolution ResolutionInvariance TwoPhase
universe u v
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve.{u,v} q) (E : TargetSupportedNerve.{u,v} r) (h : q.CoarserThan r)
variable (M : TargetSupportedNerveMorphism q r h N E)
variable {s t z : SupportSignature.Signature N E h}
/-- 実署名比較の標準 H¹ 核。既存 H¹ との自然同型は oldH1Iso が与える。 -/
abbrev h1Kernel (s : SupportSignature.Signature N E h) :=
  LinearMap.ker (HomologicalComplex.homologyMap (comparison N E h M s) 1).hom
/-- 実署名比較の標準 H¹ 余核。 -/
abbrev h1Cokernel (s : SupportSignature.Signature N E h) :=
  (fineComplex N E h s).homology 1 ⧸ LinearMap.range (HomologicalComplex.homologyMap (comparison N E h M s) 1).hom
/-- 署名包含が実 source 制限から生成する H¹ 核射。 -/
def h1KernelMap (hst : s ≤ t) : h1Kernel N E h M t →ₗ[ℚ] h1Kernel N E h M s :=
  homologyKernelMap _ _ (coarseMap N E h hst) (fineMap N E h hst) (comparison_natural N E h M hst) 1
/-- 核射の値は元の粗側制限の H¹ 射である。 -/
@[simp] theorem h1KernelMap_val (hst : s ≤ t) (x : h1Kernel N E h M t) :
    (h1KernelMap N E h M hst x).val = HomologicalComplex.homologyMap (coarseMap N E h hst) 1 x.val :=
  homologyKernelMap_val _ _ _ _ _ _ x
/-- 署名包含が実 target 制限から生成する H¹ 余核射。 -/
def h1CokernelMap (hst : s ≤ t) : h1Cokernel N E h M t →ₗ[ℚ] h1Cokernel N E h M s :=
  homologyCokernelMap _ _ (coarseMap N E h hst) (fineMap N E h hst) (comparison_natural N E h M hst) 1
/-- 余核射の代表元評価は元の細側制限の H¹ 射である。 -/
@[simp] theorem h1CokernelMap_mk (hst : s ≤ t) (x : (fineComplex N E h t).homology 1) :
    h1CokernelMap N E h M hst ((LinearMap.range (HomologicalComplex.homologyMap (comparison N E h M t) 1).hom).mkQ x) =
      (LinearMap.range (HomologicalComplex.homologyMap (comparison N E h M s) 1).hom).mkQ
        (HomologicalComplex.homologyMap (fineMap N E h hst) 1 x) :=
  homologyCokernelMap_mk _ _ _ _ _ _ x
/-- 実 H¹ 核制限の恒等則。 -/
theorem h1KernelMap_id (s : SupportSignature.Signature N E h) : h1KernelMap N E h M (le_refl s) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [h1KernelMap_val,coarseMap_id,HomologicalComplex.homologyMap_id,ModuleCat.id_apply,LinearMap.id_apply]
/-- 実 H¹ 核制限の合成則。 -/
theorem h1KernelMap_comp (hst : s ≤ t) (htz : t ≤ z) :
    (h1KernelMap N E h M hst).comp (h1KernelMap N E h M htz) = h1KernelMap N E h M (hst.trans htz) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply,h1KernelMap_val]
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f 1) (coarseMap_comp N E h hst htz)
  dsimp only at hh
  rw [HomologicalComplex.homologyMap_comp] at hh
  exact congrArg (fun f : (coarseComplex N E h z).homology 1 ⟶ (coarseComplex N E h s).homology 1 => f x.val) hh
/-- 実 H¹ 余核制限の恒等則。 -/
theorem h1CokernelMap_id (s : SupportSignature.Signature N E h) : h1CokernelMap N E h M (le_refl s) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (LinearMap.range (HomologicalComplex.homologyMap (comparison N E h M s) 1).hom).mkQ_surjective x
  simp only [h1CokernelMap_mk,fineMap_id,HomologicalComplex.homologyMap_id,ModuleCat.id_apply,LinearMap.id_apply]
/-- 実 H¹ 余核制限の合成則。 -/
theorem h1CokernelMap_comp (hst : s ≤ t) (htz : t ≤ z) :
    (h1CokernelMap N E h M hst).comp (h1CokernelMap N E h M htz) = h1CokernelMap N E h M (hst.trans htz) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (LinearMap.range (HomologicalComplex.homologyMap (comparison N E h M z) 1).hom).mkQ_surjective x
  simp only [LinearMap.comp_apply,h1CokernelMap_mk]
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f 1) (fineMap_comp N E h hst htz)
  dsimp only at hh
  rw [HomologicalComplex.homologyMap_comp] at hh
  exact congrArg (fun f : (fineComplex N E h z).homology 1 ⟶ (fineComplex N E h s).homology 1 =>
    (LinearMap.range (HomologicalComplex.homologyMap (comparison N E h M s) 1).hom).mkQ (f x)) hh
/-- 実 H¹ 核を全署名制限に接続する反対圏関手。 -/
def h1KernelFunctor : (SupportSignature.Signature N E h)ᵒᵖ ⥤ ModuleCat.{v} ℚ where
  obj s := ModuleCat.of ℚ (h1Kernel N E h M s.unop)
  map f := ModuleCat.ofHom (h1KernelMap N E h M (leOfHom f.unop))
  map_id s := by rw [h1KernelMap_id]; rfl
  map_comp f g := by rw [← h1KernelMap_comp]; rfl
/-- 実 H¹ 余核を全署名制限に接続する反対圏関手。 -/
def h1CokernelFunctor : (SupportSignature.Signature N E h)ᵒᵖ ⥤ ModuleCat.{v} ℚ where
  obj s := ModuleCat.of ℚ (h1Cokernel N E h M s.unop)
  map f := ModuleCat.ofHom (h1CokernelMap N E h M (leOfHom f.unop))
  map_id s := by rw [h1CokernelMap_id]; rfl
  map_comp f g := by rw [← h1CokernelMap_comp]; rfl
end AAT.AG.AtlasDefectComposition.SupportFunctor
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportFunctor
