import ResearchLean.AG.AtlasGluingWidth.MayerVietoris
import ResearchLean.AG.AtlasDefectComposition.ShortExactFive
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

import Formal.Util.AssertStandardAxioms
/-! # 同じMayer–Vietoris列の実Q/P短完全列と自然な粗細比較

GOAL C／設計 exact-sequence §3–4。Q は H⁰差制限のliteral range quotient、P は H¹差制限の
literal kernelである。一般SESは方向仮定であり、原始適用では StandardRow.cellRow_shortExact が
Aから生成する。局所比較の全単射性 hL はCの特殊化だけの方向仮定で、原始適用では同じ局所J零から導く。
Implementation notes: G-133 ShortExactFive の実商・核 API と標準LESの三つの完全性を使う。
同次元の別空間や選択した分裂でQ/Pを置換する案は、同じδ・制限・比較の射を保持しないため退けた。
Zへの射は元の局所比較の逆と元の差制限を合成する。交差比較の全単射を追加する案は固定前提を強めるため退けた。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth
namespace QuotientKernelRow
open AAT.AG.AtlasGluingWidth AAT.AG.AtlasDefectComposition
universe u
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)) (hS : S.ShortExact)

/-- H⁰差制限の実余核。標準homologyの同じ差制限を商にする。 -/
abbrev Q := (S.X₃.homology (0:ℤ)) ⧸ LinearMap.range (homologyMap S.g 0).hom
/-- H¹差制限の実核。標準homologyの同じ差制限を制限する。 -/
abbrev P := LinearMap.ker (homologyMap S.g (1:ℤ)).hom

/-- 実Qから合併H¹への包含は同じ標準連結射δの商写像。 -/
def inclusion : Q S →ₗ[ℚ] S.X₁.homology (1:ℤ) :=
  ShortExactFive.inclusion (homologyMap S.g 0).hom
    (StandardLES.connecting S hS 0).hom (StandardLES.exact_before S hS 0)

/-- 合併H¹から実Pへの射は同じ元の制限射。 -/
def projection : S.X₁.homology (1:ℤ) →ₗ[ℚ] P S :=
  ShortExactFive.projection (homologyMap S.f 1).hom
    (homologyMap S.g 1).hom (StandardLES.exact_middle S hS 1)

/-- 標準LESの前後三位置から、Q包含とP射の中間完全性を導く。 -/
theorem exact : Function.Exact (inclusion S hS) (projection S hS) :=
  ShortExactFive.exact _ _ _ _ (StandardLES.exact_before S hS 0)
    (StandardLES.exact_after S hS 0) (StandardLES.exact_middle S hS 1)

/-- GOAL C／設計§3: 同じδと制限から実Q/H¹/Pの短複体を作る。 -/
def row : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.moduleCatMk (inclusion S hS) (projection S hS) (by
    apply LinearMap.ext
    intro x
    exact (exact S hS (inclusion S hS x)).mpr ⟨x,rfl⟩)

/-- GOAL C／設計§3: 実Q/H¹/PのSES。一般hSは方向仮定、原始適用ではAから生成する。 -/
theorem row_shortExact : (row S hS).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (exact S hS)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (ShortExactFive.inclusion_injective _ _ (StandardLES.exact_before S hS 0))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (ShortExactFive.projection_surjective _ _ (StandardLES.exact_middle S hS 1))

variable {T : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)} (v : S ⟶ T)

/-- 元の二行図式の右squareを全整数次数の標準homologyへ移す。 -/
theorem homology_comm23 (m : ℤ) :
    homologyMap S.g m ≫ homologyMap v.τ₃ m = homologyMap v.τ₂ m ≫ homologyMap T.g m := by
  rw [← homologyMap_comp, ← homologyMap_comp, v.comm₂₃]

/-- 交差H⁰比較が誘導する実Qの商比較。局所H⁰差制限との元のsquareでwell-defined。 -/
def q : Q S →ₗ[ℚ] Q T :=
  (LinearMap.range (homologyMap S.g 0).hom).mapQ
    (LinearMap.range (homologyMap T.g 0).hom) (homologyMap v.τ₃ 0).hom (by
      rintro z ⟨x,rfl⟩
      refine ⟨homologyMap v.τ₂ 0 x, ?_⟩
      have hc := congrArg (fun f => f x) (homology_comm23 S v 0)
      exact hc.symm)

/-- 同じ局所H¹比較の二領域射を実Pの核へ制限する。 -/
def p : P S →ₗ[ℚ] P T :=
  ((homologyMap v.τ₂ 1).hom.comp (LinearMap.ker (homologyMap S.g 1).hom).subtype).codRestrict _ (by
    intro z
    have hc := congrArg (fun f => f z.val) (homology_comm23 S v 1)
    change homologyMap v.τ₃ 1 (homologyMap S.g 1 z.val) =
      homologyMap T.g 1 (homologyMap v.τ₂ 1 z.val) at hc
    rw [z.property, map_zero] at hc
    exact hc.symm)

variable (hT : T.ShortExact)

/-- 実Qの比較は全代表元で元の交差H⁰比較を読む。 -/
@[simp] theorem q_mk (z : S.X₃.homology (0:ℤ)) :
    q S v ((LinearMap.range (homologyMap S.g 0).hom).mkQ z) =
    (LinearMap.range (homologyMap T.g 0).hom).mkQ (homologyMap v.τ₃ 0 z) := rfl
/-- 実Qの包含は全代表元で元の標準δを読む。 -/
@[simp] theorem inclusion_mk (z : S.X₃.homology (0:ℤ)) :
    inclusion S hS ((LinearMap.range (homologyMap S.g 0).hom).mkQ z) =
      StandardLES.connecting S hS 0 z :=
  ShortExactFive.inclusion_mk _ _ _ z
/-- 実Pへの射は元の合併制限を読む。 -/
@[simp] theorem projection_val (z : S.X₁.homology (1:ℤ)) :
    (projection S hS z).val = homologyMap S.f 1 z := rfl
/-- 実Pの比較は元の局所H¹比較の作用を読む。 -/
@[simp] theorem p_val (z : P S) : (p S v z).val = homologyMap v.τ₂ 1 z.val := rfl

/-- 元のδ自然性により実Qの包含と同じ合併H¹比較が可換。 -/
theorem inclusion_natural :
    (inclusion T hT).comp (q S v) = (homologyMap v.τ₁ 1).hom.comp (inclusion S hS) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x,rfl⟩ := (LinearMap.range (homologyMap S.g 0).hom).mkQ_surjective z
  simp only [LinearMap.comp_apply, q_mk, inclusion_mk]
  exact (congrArg (fun f => f x) (HomologySequence.δ_naturality v hS hT 0 1 rfl)).symm

/-- 元の左squareにより実Pの射と同じ合併H¹比較が可換。 -/
theorem projection_natural :
    (projection T hT).comp (homologyMap v.τ₁ 1).hom = (p S v).comp (projection S hS) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [LinearMap.comp_apply, projection_val, p_val]
  have h := congrArg (fun f => f z) (congrArg (fun f => homologyMap f (1:ℤ)) v.comm₁₂)
  simpa only [homologyMap_comp, ModuleCat.comp_apply] using h

/-- GOAL C／設計§3: 実q、同じ合併比較、実pから二行Q/H¹/P図式を生成する。 -/
def rowMap : row S hS ⟶ row T hT where
  τ₁ := ModuleCat.ofHom (q S v)
  τ₂ := homologyMap v.τ₁ 1
  τ₃ := ModuleCat.ofHom (p S v)
  comm₁₂ := ModuleCat.hom_ext (inclusion_natural S hS v hT)
  comm₂₃ := ModuleCat.hom_ext (projection_natural S hS v hT)

/-- 交差粗H¹内の実差制限像と実交差比較核との交差。 -/
abbrev Z := LinearMap.range (homologyMap S.g (1:ℤ)).hom ⊓
  LinearMap.ker (homologyMap v.τ₃ (1:ℤ)).hom
variable (hL : Function.Bijective (homologyMap v.τ₂ (1:ℤ)))
/-- 同じ局所H¹比較の全単射性から生成する実逆比較。 -/
def localEquiv := LinearEquiv.ofBijective (homologyMap v.τ₂ (1:ℤ)).hom hL
/-- 局所同型の順写像は元の局所比較そのもの。 -/
@[simp] theorem localEquiv_apply (x : S.X₂.homology (1:ℤ)) :
    localEquiv S v hL x = homologyMap v.τ₂ 1 x := rfl

/-- 細PからZへの射は、同じ局所逆比較の後に粗差制限を作用させる。 -/
def zMap : P T →ₗ[ℚ] Z S v :=
  ((homologyMap S.g 1).hom.comp
    ((localEquiv S v hL).symm.toLinearMap.comp (LinearMap.ker (homologyMap T.g 1).hom).subtype)).codRestrict _ (by
    intro y
    constructor
    · exact ⟨(localEquiv S v hL).symm y.val, rfl⟩
    · have hc := congrArg (fun f => f ((localEquiv S v hL).symm y.val)) (homology_comm23 S v 1)
      change homologyMap v.τ₃ 1 (homologyMap S.g 1 ((localEquiv S v hL).symm y.val)) =
        homologyMap T.g 1 (localEquiv S v hL ((localEquiv S v hL).symm y.val)) at hc
      rw [LinearEquiv.apply_symm_apply, y.property] at hc
      exact hc)
/-- Zへの射の元の交差H¹における代表式。 -/
@[simp] theorem zMap_val (y : P T) :
    (zMap S v hL y).val = homologyMap S.g 1 ((localEquiv S v hL).symm y.val) := rfl

include hL in
/-- 局所比較の単射性からPの実制限比較も単射。 -/
theorem p_injective : Function.Injective (p S v) := by
  intro x y hxy
  apply Subtype.ext
  apply hL.1
  exact congrArg Subtype.val hxy

/-- GOAL C／設計§4: 局所比較の逆と差制限からp像とZ射の核の一致を証明する。 -/
theorem p_z_exact : Function.Exact (p S v) (zMap S v hL) := by
  intro y
  constructor
  · intro hy
    have hk : homologyMap S.g 1 ((localEquiv S v hL).symm y.val) = 0 := congrArg Subtype.val hy
    refine ⟨⟨(localEquiv S v hL).symm y.val,hk⟩, ?_⟩
    apply Subtype.ext
    change localEquiv S v hL ((localEquiv S v hL).symm y.val) = y.val
    exact LinearEquiv.apply_symm_apply _ _
  · rintro ⟨x,rfl⟩
    apply Subtype.ext
    rw [zMap_val, p_val]
    change homologyMap S.g 1 ((localEquiv S v hL).symm (localEquiv S v hL x.val)) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact x.property

/-- Zの任意元を差制限の原像から持ち上げ、Z射の全射性を証明する。 -/
theorem zMap_surjective : Function.Surjective (zMap S v hL) := by
  intro z
  obtain ⟨x,hx⟩ := z.property.1
  have hk : homologyMap T.g 1 (localEquiv S v hL x) = 0 := by
    have hc := congrArg (fun f => f x) (homology_comm23 S v 1)
    change homologyMap v.τ₃ 1 (homologyMap S.g 1 x) = homologyMap T.g 1 (localEquiv S v hL x) at hc
    rw [hx, z.property.2] at hc
    exact hc.symm
  refine ⟨⟨localEquiv S v hL x,hk⟩,?_⟩
  apply Subtype.ext
  rw [zMap_val]
  change homologyMap S.g 1 ((localEquiv S v hL).symm (localEquiv S v hL x)) = z.val
  rw [LinearEquiv.symm_apply_apply]
  exact hx
/-- GOAL C: 局所比較が全単射なら、pの実余核は同じ交差のZと線形同型。 -/
def cokerPZEquiv : (P T ⧸ LinearMap.range (p S v)) ≃ₗ[ℚ] Z S v :=
  (p_z_exact S v hL).linearEquivOfSurjective (zMap_surjective S v hL)
/-- 余核同型は全代表元で元の差制限と同じ局所逆比較を読む。 -/
@[simp] theorem cokerPZEquiv_mk (y : P T) :
    cokerPZEquiv S v hL ((LinearMap.range (p S v)).mkQ y) = zMap S v hL y := rfl
end QuotientKernelRow
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
