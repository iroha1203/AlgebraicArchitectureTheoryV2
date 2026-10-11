import ResearchLean.AG.AtlasGluingWidth.QuotientKernelRow
import ResearchLean.AG.AtlasGluingWidth.LinearSnake
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import ResearchLean.AG.UniformInvariance.DefectSemantics

import Formal.Util.AssertStandardAxioms
/-! # 同じQ/P図式のsnake列と局所同型下の一次欠損

GOAL C／設計 exact-sequence §3–4。Q/P二行図式の同じ合併比較の実核・実余核を扱う。
一般hS/hTは方向仮定で、原始適用ではAのcellRow_shortExactから生成する。
hLは局所J零の特殊化だけの方向仮定で、原始適用ではPairHomologyにより放電する。
Implementation notes: LinearSnakeの標準δと普遍的核・余核同型を使い、各実射の代表式を保持する。
abstractな同次元モデルや任意分裂を使う案は、同じδ・制限・粗細比較の同定を失うため退けた。
Zへの射は元の局所逆比較と粗差制限であり、交差比較への全単射仮定は不要。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.GluingDefect
open AAT.AG.AtlasGluingWidth AAT.AG.AtlasDefectComposition
universe u
variable (S T : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ))
variable (hS : S.ShortExact) (hT : T.ShortExact) (v : S ⟶ T)
/-- 生成されたQ/P二行図式を標準snake入力へ接続する。 -/
def snake := LinearSnake.snake (QuotientKernelRow.row S hS) (QuotientKernelRow.row T hT)
  (QuotientKernelRow.row_shortExact S hS) (QuotientKernelRow.row_shortExact T hT)
  (QuotientKernelRow.rowMap S hS v hT)
/-- 同じ合併H¹比較のliteral kernel。 -/
abbrev Phantom := LinearMap.ker (homologyMap v.τ₁ (1:ℤ)).hom
/-- 同じ合併H¹比較のliteral range quotient。 -/
abbrev Hidden := (T.X₁.homology (1:ℤ)) ⧸ LinearMap.range (homologyMap v.τ₁ 1).hom
/-- Q比較核から同じ合併比較核への実snake射。 -/
def first : LinearMap.ker (QuotientKernelRow.q S v) →ₗ[ℚ] Phantom S T v :=
  (LinearSnake.first (snake S T hS hT v)).hom
/-- 合併比較核からP比較核への実snake射。 -/
def second : Phantom S T v →ₗ[ℚ] LinearMap.ker (QuotientKernelRow.p S v) :=
  (LinearSnake.second (snake S T hS hT v)).hom
/-- P比較核からQ比較余核への標準連結射。 -/
def connecting : LinearMap.ker (QuotientKernelRow.p S v) →ₗ[ℚ]
    (QuotientKernelRow.Q T ⧸ LinearMap.range (QuotientKernelRow.q S v)) :=
  (LinearSnake.connecting (snake S T hS hT v)).hom
/-- Q比較余核から合併比較余核への実snake射。 -/
def fourth : (QuotientKernelRow.Q T ⧸ LinearMap.range (QuotientKernelRow.q S v)) →ₗ[ℚ] Hidden S T v :=
  (LinearSnake.fourth (snake S T hS hT v)).hom
/-- 合併比較余核からP比較余核への実snake射。 -/
def fifth : Hidden S T v →ₗ[ℚ]
    (QuotientKernelRow.P T ⧸ LinearMap.range (QuotientKernelRow.p S v)) :=
  (LinearSnake.fifth (snake S T hS hT v)).hom
/-- 第一snake射は実Q包含を読む。 -/
theorem first_val (a : LinearMap.ker (QuotientKernelRow.q S v)) :
    (first S T hS hT v a).val = QuotientKernelRow.inclusion S hS a.val :=
  LinearSnake.first_val (snake S T hS hT v) a
/-- 第二snake射は実P射を読む。 -/
theorem second_val (a : Phantom S T v) :
    (second S T hS hT v a).val = QuotientKernelRow.projection S hS a.val :=
  LinearSnake.second_val (snake S T hS hT v) a
/-- 第四snake射は全商代表元で実Q包含を読む。 -/
theorem fourth_mk (z : QuotientKernelRow.Q T) :
    fourth S T hS hT v ((LinearMap.range (QuotientKernelRow.q S v)).mkQ z) =
      (LinearMap.range (homologyMap v.τ₁ 1).hom).mkQ (QuotientKernelRow.inclusion T hT z) :=
  LinearSnake.fourth_mk (snake S T hS hT v) z
/-- 第五snake射は全商代表元で実P射を読む。 -/
theorem fifth_mk (z : T.X₁.homology (1:ℤ)) :
    fifth S T hS hT v ((LinearMap.range (homologyMap v.τ₁ 1).hom).mkQ z) =
      (LinearMap.range (QuotientKernelRow.p S v)).mkQ (QuotientKernelRow.projection T hT z) :=
  LinearSnake.fifth_mk (snake S T hS hT v) z
/-- 標準snake連結射は同じP射で持ち上げた元とQ包含で貼り合わせた元の商。 -/
theorem connecting_representative (a : LinearMap.ker (QuotientKernelRow.p S v))
    (b : S.X₁.homology (1:ℤ)) (hb : QuotientKernelRow.projection S hS b = a.val)
    (z : QuotientKernelRow.Q T) (hz : QuotientKernelRow.inclusion T hT z = homologyMap v.τ₁ 1 b) :
    connecting S T hS hT v a = (LinearMap.range (QuotientKernelRow.q S v)).mkQ z :=
  LinearSnake.connecting_representative (snake S T hS hT v) a b hb z hz
/-- 全P比較核元に対し同じ連結射の代表式を生成する。 -/
theorem connecting_lift (a : LinearMap.ker (QuotientKernelRow.p S v)) :
    ∃ b : S.X₁.homology (1:ℤ), QuotientKernelRow.projection S hS b = a.val ∧
      ∃ z : QuotientKernelRow.Q T, QuotientKernelRow.inclusion T hT z = homologyMap v.τ₁ 1 b ∧
        connecting S T hS hT v a = (LinearMap.range (QuotientKernelRow.q S v)).mkQ z :=
by
  obtain ⟨b,z,hb,hz⟩ := LinearSnake.connecting_lift (snake S T hS hT v) a
  exact ⟨b,hb,z,hz,connecting_representative S T hS hT v a b hb z hz⟩
/-- 生成された粗Q/P行の包含から第一snake射の単射性を導く。 -/
theorem first_injective : Function.Injective (first S T hS hT v) := by
  letI : Mono (snake S T hS hT v).L₁.f := (QuotientKernelRow.row_shortExact S hS).mono_f
  exact LinearSnake.first_injective (snake S T hS hT v)
/-- 生成された細Q/P行のP射から第五snake射の全射性を導く。 -/
theorem fifth_surjective : Function.Surjective (fifth S T hS hT v) := by
  letI : Epi (snake S T hS hT v).L₂.g := (QuotientKernelRow.row_shortExact T hT).epi_g
  exact LinearSnake.fifth_surjective (snake S T hS hT v)
/-- 標準snakeの第一位置の実完全性。 -/
theorem exact₁ : Function.Exact (first S T hS hT v) (second S T hS hT v) :=
  LinearSnake.exact1 (snake S T hS hT v)
/-- 標準snakeの第二位置の実完全性。 -/
theorem exact₂ : Function.Exact (second S T hS hT v) (connecting S T hS hT v) :=
  LinearSnake.exact2 (snake S T hS hT v)
/-- 標準snakeの第三位置の実完全性。 -/
theorem exact₃ : Function.Exact (connecting S T hS hT v) (fourth S T hS hT v) :=
  LinearSnake.exact3 (snake S T hS hT v)
/-- 標準snakeの第四位置の実完全性。 -/
theorem exact₄ : Function.Exact (fourth S T hS hT v) (fifth S T hS hT v) :=
  LinearSnake.exact4 (snake S T hS hT v)
variable (hL : Function.Bijective (homologyMap v.τ₂ (1:ℤ)))
/-- 局所同型下で同じ実phantomをQ比較核へ同定する。 -/
def phantomEquiv : Phantom S T v ≃ₗ[ℚ] LinearMap.ker (QuotientKernelRow.q S v) := by
  letI : Mono (snake S T hS hT v).L₁.f := (QuotientKernelRow.row_shortExact S hS).mono_f
  exact (LinearSnake.firstEquiv (snake S T hS hT v) (QuotientKernelRow.p_injective S v hL)).symm

/-- 標準snakeの後半を同じ実余核の短複体へ置く。 -/
def hiddenSnakeRow := LinearSnake.hiddenRow (snake S T hS hT v)
include hL in
/-- 局所同型からP比較単射を導き、実hiddenの短完全列を生成する。 -/
theorem hiddenSnakeRow_shortExact : (hiddenSnakeRow S T hS hT v).ShortExact := by
  letI : Epi (snake S T hS hT v).L₂.g := (QuotientKernelRow.row_shortExact T hT).epi_g
  exact LinearSnake.hiddenRow_shortExact _ (QuotientKernelRow.p_injective S v hL)

/-- 同じhidden余核から交差H¹内の実Zへの射。 -/
def hiddenZProjection : Hidden S T v →ₗ[ℚ] QuotientKernelRow.Z S v :=
  (QuotientKernelRow.cokerPZEquiv S v hL).toLinearMap.comp (fifth S T hS hT v)
/-- Z射の代表式は元の制限、局所逆比較、粗差制限の合成。 -/
theorem hiddenZProjection_mk (z : T.X₁.homology (1:ℤ)) :
    (hiddenZProjection S T hS hT v hL ((LinearMap.range (homologyMap v.τ₁ 1).hom).mkQ z)).val =
      homologyMap S.g 1 ((QuotientKernelRow.localEquiv S v hL).symm (homologyMap T.f 1 z)) := by
  change (QuotientKernelRow.cokerPZEquiv S v hL
    (fifth S T hS hT v ((LinearMap.range (homologyMap v.τ₁ 1).hom).mkQ z))).val = _
  rw [fifth_mk, QuotientKernelRow.cokerPZEquiv_mk, QuotientKernelRow.zMap_val,
    QuotientKernelRow.projection_val]

/-- 実Q比較余核、実hidden、実Zの同じ短複体。 -/
def hiddenZRow : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.mk (hiddenSnakeRow S T hS hT v).f
    ((hiddenSnakeRow S T hS hT v).g ≫ (QuotientKernelRow.cokerPZEquiv S v hL).toModuleIso.hom)
    (by rw [← Category.assoc, (hiddenSnakeRow S T hS hT v).zero, zero_comp])
/-- snake後半を実Zへ移す、両前項を固定する短複体同型。 -/
def hiddenZRowIso : hiddenSnakeRow S T hS hT v ≅ hiddenZRow S T hS hT v hL :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (QuotientKernelRow.cokerPZEquiv S v hL).toModuleIso
    (by simp only [hiddenZRow, Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by simp only [hiddenZRow, Iso.refl_hom, Category.id_comp])
/-- 局所同型下の実hidden/Z短完全列。 -/
theorem hiddenZRow_shortExact : (hiddenZRow S T hS hT v hL).ShortExact :=
  ShortComplex.shortExact_of_iso (hiddenZRowIso S T hS hT v hL)
    (hiddenSnakeRow_shortExact S T hS hT v hL)

variable (R : ShortComplex (ModuleCat.{u} ℚ)) (hR : R.ShortExact)
include hR in
/-- G-133の実核商次元式から任意の有限次元短完全列の加法性を導く。 -/
theorem shortExact_dimension [FiniteDimensional ℚ R.X₂] :
    Module.finrank ℚ R.X₂ = Module.finrank ℚ R.X₁ + Module.finrank ℚ R.X₃ := by
  have h := ShortExactFive.dimension (0 : ℚ →ₗ[ℚ] R.X₁) R.f.hom R.g.hom (0 : R.X₃ →ₗ[ℚ] ℚ)
    ((LinearMap.exact_zero_iff_injective ℚ R.f.hom).mpr ((ModuleCat.mono_iff_injective _).mp hR.mono_f))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hR.exact)
    ((LinearMap.exact_zero_iff_surjective ℚ R.g.hom).mpr ((ModuleCat.epi_iff_surjective _).mp hR.epi_g))
  rw [LinearMap.range_zero, LinearMap.ker_zero] at h
  letI : FiniteDimensional ℚ R.X₁ := FiniteDimensional.of_injective R.f.hom
    ((ModuleCat.mono_iff_injective _).mp hR.mono_f)
  have hq := Submodule.finrank_quotient_add_finrank (⊥ : Submodule ℚ R.X₁)
  simp only [finrank_bot, add_zero] at hq
  simpa only [finrank_top, hq] using h
variable [FiniteDimensional ℚ (S.X₁.homology (1:ℤ))]
    [FiniteDimensional ℚ (T.X₁.homology (1:ℤ))]
omit [FiniteDimensional ℚ (S.X₁.homology (1:ℤ))] in
include hS hT hL in
/-- 局所同型下の同じ合併比較の二成分欠損は実Q比較核と余核/Zの次元。 -/
theorem defect_dimension :
    AAT.AG.ResolutionInvariance.blockDefect (homologyMap v.τ₁ (1:ℤ)).hom =
      (Module.finrank ℚ (LinearMap.ker (QuotientKernelRow.q S v)),
       Module.finrank ℚ (QuotientKernelRow.Q T ⧸ LinearMap.range (QuotientKernelRow.q S v)) +
         Module.finrank ℚ (QuotientKernelRow.Z S v)) := by
  apply Prod.ext
  · exact (phantomEquiv S T hS hT v hL).finrank_eq
  · letI : FiniteDimensional ℚ (hiddenZRow S T hS hT v hL).X₂ := by
      change FiniteDimensional ℚ (Hidden S T v)
      infer_instance
    exact shortExact_dimension (hiddenZRow S T hS hT v hL)
      (hiddenZRow_shortExact S T hS hT v hL)

variable [FiniteDimensional ℚ (S.X₃.homology (0:ℤ))]
    [FiniteDimensional ℚ (T.X₃.homology (0:ℤ))]
    [FiniteDimensional ℚ (S.X₃.homology (1:ℤ))]
omit [FiniteDimensional ℚ (S.X₁.homology (1:ℤ))] in
include hS hT hL in
/-- 同じ合併欠損の零は、Q比較全単射かつ実Z零と同値。 -/
theorem defect_zero_iff :
    AAT.AG.ResolutionInvariance.blockDefect (homologyMap v.τ₁ (1:ℤ)).hom = (0,0) ↔
      Function.Bijective (QuotientKernelRow.q S v) ∧ QuotientKernelRow.Z S v = ⊥ := by
  rw [defect_dimension S T hS hT v hL]
  constructor
  · intro h
    have hker := congrArg Prod.fst h
    have hsum := congrArg Prod.snd h
    have hcoker : Module.finrank ℚ (QuotientKernelRow.Q T ⧸ LinearMap.range (QuotientKernelRow.q S v)) = 0 := by omega
    have hz : Module.finrank ℚ (QuotientKernelRow.Z S v) = 0 := by omega
    refine ⟨(AAT.AG.ResolutionInvariance.blockDefect_eq_zero_iff_bijective _).mp ?_, Submodule.finrank_eq_zero.mp hz⟩
    exact Prod.ext hker hcoker
  · rintro ⟨hq,hz⟩
    have h := (AAT.AG.ResolutionInvariance.blockDefect_eq_zero_iff_bijective (QuotientKernelRow.q S v)).mpr hq
    have hk := congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    have hzf := Submodule.finrank_eq_zero.mpr hz
    exact Prod.ext hk (by simpa only [hc, hzf, add_zero])
end AAT.AG.AtlasGluingWidth.GluingDefect

#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
