import ResearchLean.AG.AtlasDefectComposition.ConeCompositionTriangle
import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Formal.Util.AssertStandardAxioms
/-! # 単射と同じ錐の商を生成する mapping cylinder モデル

Implementation notes: Cone(id K) ⊞ L への実包含を構成する。
元の射の単射性を使わず、contractible 成分の射影を chain homotopy 同値にする。
-/
noncomputable section
open CategoryTheory Limits CochainComplex HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.MappingCylinder
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
universe w
variable {K L : CochainComplex (ModuleCat.{w} ℚ) ℤ} (φ : K ⟶ L)
/-- 元の射から構成する contractible summand 付きモデル。 -/
def model (_φ : K ⟶ L) : CochainComplex (ModuleCat.{w} ℚ) ℤ := mappingCone (𝟙 K) ⊞ L
/-- 原始射を第二成分に保持する実 chain inclusion。 -/
def inclusion : K ⟶ model φ := biprod.lift (mappingCone.inr (𝟙 K)) φ
/-- 元の target への指定 chain projection。 -/
def projection : model φ ⟶ L := biprod.snd
/-- モデルを経由しても元の射そのものに一致する。 -/
@[simp] theorem factorization : inclusion φ ≫ projection φ = φ := by
  simp [inclusion,projection]
/-- モデル包含の各次数に対する指定の左逆線形射。 -/
def degreeRetraction (m : ℤ) : (model φ).X m ⟶ K.X m :=
  (biprod.fst : model φ ⟶ mappingCone (𝟙 K)).f m ≫
    (mappingCone.snd (𝟙 K)).v m m (by simp)
/-- 元の射が単射でなくても、モデル包含は全整数次数で左逆を持つ。 -/
@[simp] theorem inclusion_degreeRetraction (m : ℤ) :
    (inclusion φ).f m ≫ degreeRetraction φ m = 𝟙 _ := by
  simp [degreeRetraction,inclusion,← Category.assoc,biprod_lift_fst_f]
/-- 各次数のモデル包含の単射性は指定左逆から導く。 -/
instance inclusion_degree_mono (m : ℤ) : Mono ((inclusion φ).f m) :=
  mono_of_mono_fac (inclusion_degreeRetraction φ m)
/-- 全次数の単射性から実 chain inclusion の単射性を導く。 -/
instance inclusion_mono : Mono (inclusion φ) :=
  HomologicalComplex.mono_of_mono_f (inclusion φ) (fun _ => inferInstance)
/-- contractible summand を除く指定射影の chain homotopy 同値。 -/
def projectionHomotopyEquiv : HomotopyEquiv (model φ) L where
  hom := projection φ
  inv := biprod.inr
  homotopyHomInvId :=
    let h₀ := mappingCone.homotopyToZeroOfId K
    let h₁ := (h₀.compRight (biprod.inl : mappingCone (𝟙 K) ⟶ model φ)).compLeft
      (biprod.fst : model φ ⟶ mappingCone (𝟙 K))
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.snd ≫ biprod.inr))
    (Homotopy.ofEq (by simp [projection])).trans (h₂.symm.trans (Homotopy.ofEq (by simp [model])))
  homotopyInvHomId := Homotopy.ofEq (by simp [projection])
/-- モデルの逐次商を標準錐へ送る指定 chain quotient map。 -/
def quotient : model φ ⟶ mappingCone φ :=
  biprod.desc (-(mappingCone.map (𝟙 K) φ (𝟙 K) φ (by simp))) (mappingCone.inr φ)
/-- モデル包含の像は指定錐への商射で零へ送られる。 -/
theorem inclusion_quotient : inclusion φ ≫ quotient φ = 0 := by
  simp [inclusion,quotient,mappingCone.map]
/-- 実包含と実錐射を持つ短複体。 -/
def shortComplex : ShortComplex (CochainComplex (ModuleCat.{w} ℚ) ℤ) :=
  ShortComplex.mk (inclusion φ) (quotient φ) (inclusion_quotient φ)
/-- 商射の各次数に対する指定の右逆線形射。 -/
def degreeSection (m : ℤ) : (mappingCone φ).X m ⟶ (model φ).X m :=
  biprod.lift
    (-((mappingCone.fst φ).1.v m (m+1) rfl ≫
      (mappingCone.inl (𝟙 K)).v (m+1) m (by simp)))
    ((mappingCone.snd φ).v m m (by simp)) ≫
      (HomologicalComplex.biprodXIso (mappingCone (𝟙 K)) L m).inv
/-- 次数別分裂は元の射の単射性を仮定しない。 -/
def degreeSplitting (m : ℤ) :
    ((shortComplex φ).map (HomologicalComplex.eval _ _ m)).Splitting where
  r := degreeRetraction φ m
  s := degreeSection φ m
  f_r := inclusion_degreeRetraction φ m
  s_g := by
    dsimp [shortComplex,degreeSection,quotient]
    simp [mappingCone.map,HomologicalComplex.biprodXIso,Category.assoc]
    exact mappingCone.id_X φ m (m+1) rfl
  id := by
    dsimp [shortComplex,degreeRetraction,degreeSection,inclusion,quotient]
    apply (cancel_mono (HomologicalComplex.biprodXIso (mappingCone (𝟙 K)) L m).hom).mp
    apply biprod.hom_ext
    all_goals
      apply (cancel_epi (HomologicalComplex.biprodXIso (mappingCone (𝟙 K)) L m).inv).mp
      apply biprod.hom_ext'
    all_goals
      simp [Category.assoc,biprod_lift_fst_f,biprod_lift_snd_f,
        mappingCone.map, mappingCone.desc_f _ _ _ _ m (m+1) rfl]
    simpa only [add_comm] using mappingCone.id_X (𝟙 K) m (m+1) rfl
/-- 実包含の実商は全次数で短完全である。 -/
theorem shortExact : (shortComplex φ).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun m => (degreeSplitting φ m).shortExact)
/-- 実cokernelと標準錐の普遍性による同型。 -/
def cokernelIso : cokernel (inclusion φ) ≅ mappingCone φ :=
  (cokernelIsCokernel (inclusion φ)).coconePointUniqueUpToIso
    (shortExact φ).gIsCokernel
/-- 全次数の有限次元性は元のsourceとtargetから導く。 -/
instance degreeFiniteDimensional (m : ℤ) [FiniteDimensional ℚ (K.X m)]
    [FiniteDimensional ℚ (K.X (m+1))] [FiniteDimensional ℚ (L.X m)] :
    FiniteDimensional ℚ ((model φ).X m) :=
  FiniteDimensional.of_injective
    ((HomologicalComplex.biprodXIso (mappingCone (𝟙 K)) L m ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv).toLinearMap
    ((HomologicalComplex.biprodXIso (mappingCone (𝟙 K)) L m ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv).injective
/-- F の実モデル短完全性の公開 snake_case API。 -/
alias short_exact := shortExact
attribute [deprecated short_exact (since := "2026-10-06")] shortExact
end AAT.AG.AtlasDefectComposition.MappingCylinder
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.MappingCylinder
