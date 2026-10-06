import ResearchLean.AG.AtlasDefectComposition.ConeCompositionNaturality
import Formal.Util.AssertStandardAxioms
/-! # 合成錐の指定同値の射の自然性

Implementation notes: 任意の隣接正方形に沿い、標準反復錐から後段錐への実 desc 射を追う。
choice で得る逆射の自然性を仮定せず、標準指定射そのものを評価する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition
universe w
variable {K L M K' L' M' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (f : K ⟶ L) (g : L ⟶ M) (f' : K' ⟶ L') (g' : L' ⟶ M')
variable (a : K ⟶ K') (b : L ⟶ L') (c : M ⟶ M')
variable (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g')
/-- F の反復錐から隣接錐への指定標準射は全 cochain 正方形に自然である。 -/
theorem compositionConeEquiv_inv_natural :
    mappingCone.map (mappingConeCompTriangle f g).mor₁ (mappingConeCompTriangle f' g').mor₁
      (mappingCone.map f f' a b hf)
      (mappingCone.map (f ≫ g) (f' ≫ g') a c
        (composition_direct_square f g (f ≫ g) rfl f' g' (f' ≫ g') rfl a b c hf hg))
      (compositionTriangle_first_natural f g (f ≫ g) rfl f' g' (f' ≫ g') rfl a b c hf hg) ≫
        (mappingConeCompHomotopyEquiv f' g').inv =
      (mappingConeCompHomotopyEquiv f g).inv ≫ mappingCone.map g g' b c hg := by
  apply HomologicalComplex.Hom.ext
  funext m
  simp only [HomologicalComplex.comp_f]
  rw [mappingCone.ext_from_iff (mappingConeCompTriangle f g).mor₁ (m+1) m rfl]
  constructor
  · rw [mappingCone.ext_from_iff f (m+2) (m+1) (by omega)]
    constructor <;> simp [mappingCone.map,mappingConeCompHomotopyEquiv,
      MappingConeCompHomotopyEquiv.inv,Category.assoc]
  · rw [mappingCone.ext_from_iff (f ≫ g) (m+1) m rfl]
    constructor <;> simp [mappingCone.map,mappingConeCompHomotopyEquiv,
      MappingConeCompHomotopyEquiv.inv,Category.assoc]
    have hfm := congrArg (fun k => k.f (m+1)) hf
    simp only [HomologicalComplex.comp_f] at hfm
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ (mappingCone.inl g').v (m+1) m (by omega)) hfm.symm
/-- 独立直接射を middle とする指定反復錐射の自然性。 -/
theorem compositionTriangleConeEquiv_inv_natural
    (d : K ⟶ M) (h : d = f ≫ g) (d' : K' ⟶ M') (h' : d' = f' ≫ g') :
    mappingCone.map (compositionTriangle f g d h).mor₁ (compositionTriangle f' g' d' h').mor₁
      (mappingCone.map f f' a b hf)
      (mappingCone.map d d' a c (composition_direct_square f g d h f' g' d' h' a b c hf hg))
      (compositionTriangle_first_natural f g d h f' g' d' h' a b c hf hg) ≫
        (compositionTriangleConeEquiv f' g' d' h').inv =
      (compositionTriangleConeEquiv f g d h).inv ≫ mappingCone.map g g' b c hg := by
  subst d; subst d'
  exact compositionConeEquiv_inv_natural f g f' g' a b c hf hg
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
