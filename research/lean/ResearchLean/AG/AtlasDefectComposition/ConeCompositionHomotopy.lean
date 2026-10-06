import ResearchLean.AG.AtlasDefectComposition.ConeCompositionTriangle
import Formal.Util.AssertStandardAxioms
/-! # 合成錐 triangle の実 null homotopy と shift 符号

Implementation notes: chain map の合成を零と宣言せず、標準 inl から homotopy を生成する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition
universe w
variable {K L M : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (f : K ⟶ L) (g : L ⟶ M) (direct : K ⟶ M) (h : direct = f ≫ g)
/-- 標準 inl の次数−1 cochain から構成する二射の実 null homotopy。 -/
def compositionTriangleNullHomotopy :
    Homotopy ((compositionTriangle f g direct h).mor₁ ≫
      (compositionTriangle f g direct h).mor₂) 0 := by
  subst direct
  refine mappingCone.descHomotopy f _ _ 0 (mappingCone.inl g) ?_ ?_
  · ext p
    simp [compositionTriangle,mappingCone.map]
  · simp [compositionTriangle,mappingCone.map]
/-- 三射目の shift を外した全整数次数の符号付き実 cochain 式。 -/
theorem compositionTriangle_third (m : ℤ) :
    (compositionTriangle f g direct h).mor₃.f m ≫
      (shiftFunctorObjXIso (mappingCone f) (1 : ℤ) m (m+1) rfl).hom =
      -((mappingCone.fst g).1.v m (m+1) rfl ≫ (mappingCone.inr f).f (m+1)) := by
  rw [mappingCone.ext_from_iff g (m+1) m rfl]
  constructor <;>
    simp [compositionTriangle,shiftFunctor_map_f']
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
