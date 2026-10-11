import ResearchLean.AG.AtlasGluingWidth.SelectionComparison
import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

import Formal.Util.AssertStandardAxioms
/-! # 原始三項短完全列の標準零延長

GOAL B／設計 exact-sequence §2 の原始 cochain SES を標準零延長へ移す。
三次数の exact/injective/surjective は一般補題の方向仮定であり、cellRow_shortExact では
A の unionInclusion と intersectionDifference の生成定理がすべて放電する。
Implementation notes: G-133 の既存零延長を採用し、同じ全 Hom と全整数次数を保持する。
独自の有限次数複体を再定義する案は、標準複体との同定と支え外の議論を重複させるため退けた。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth
namespace StandardRow
open AAT.AG.TwoPhase AAT.AG.AtlasDefectComposition
universe u
variable {C D E : ThreeCochainComplex.{0,u} ℚ}
variable (f : ThreeCochainComplex.Hom C D) (g : ThreeCochainComplex.Hom D E)
variable (he0 : Function.Exact f.f0 g.f0) (he1 : Function.Exact f.f1 g.f1)
variable (he2 : Function.Exact f.f2 g.f2)

include he0 he1 he2 in
/-- 三次数の実完全性から標準零延長射の合成零を生成する。 -/
theorem row_zero : zeroExtensionMap f ≫ zeroExtensionMap g = 0 := by
  apply HomologicalComplex.hom_ext
  intro m
  by_cases h0 : m = 0
  · subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (he0 (f.f0 x)).mpr ⟨x, rfl⟩
  · by_cases h1 : m = 1
    · subst m
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (he1 (f.f1 x)).mpr ⟨x, rfl⟩
    · by_cases h2 : m = 2
      · subst m
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (he2 (f.f2 x)).mpr ⟨x, rfl⟩
      · exact (degreeObject_isZero C m h0 h1 h2).eq_of_src _ _

/-- 同じ三項射を標準複体の短複体へ置く。 -/
def row : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (zeroExtensionMap f) (zeroExtensionMap g) (row_zero f g he0 he1 he2)

variable (hi0 : Function.Injective f.f0) (hi1 : Function.Injective f.f1)
variable (hi2 : Function.Injective f.f2) (hs0 : Function.Surjective g.f0)
variable (hs1 : Function.Surjective g.f1) (hs2 : Function.Surjective g.f2)

include hi0 hi1 hi2 hs0 hs1 hs2 in
/-- GOAL B／設計 exact-sequence §2: 三次数の単射・完全性・全射から標準 SES を生成する。
一般射の方向仮定は、cellRow_shortExact で A のセルごとの生成定理により放電する。 -/
theorem row_shortExact : (row f g he0 he1 he2).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro m
  by_cases h0 : m = 0
  · subst m
    exact { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr he0
            mono_f := (ModuleCat.mono_iff_injective _).mpr hi0
            epi_g := (ModuleCat.epi_iff_surjective _).mpr hs0 }
  · by_cases h1 : m = 1
    · subst m
      exact { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr he1
              mono_f := (ModuleCat.mono_iff_injective _).mpr hi1
              epi_g := (ModuleCat.epi_iff_surjective _).mpr hs1 }
    · by_cases h2 : m = 2
      · subst m
        exact { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr he2
                mono_f := (ModuleCat.mono_iff_injective _).mpr hi2
                epi_g := (ModuleCat.epi_iff_surjective _).mpr hs2 }
      · have hzC := degreeObject_isZero C m h0 h1 h2
        have hzD := degreeObject_isZero D m h0 h1 h2
        have hzE := degreeObject_isZero E m h0 h1 h2
        exact { exact := ShortComplex.exact_of_isZero_X₂ _ hzD
                mono_f := hzC.mono _
                epi_g := hzE.epi _ }

open AAT.AG.AtlasGluingWidth AAT.AG.ResolutionInvariance AAT.AG.CanonicalResolution
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison qc qf h Nc Nf)

/-- 元セルの和・二領域・真のセル交差の同じ射を標準零延長する。 -/
def cellRow {q : Reading Source} {D : TargetSupportedNerve q} (S T : CellSelection D) :=
  row (S.unionInclusion T) (S.intersectionDifference T)
    (S.union_intersection_exact0 T) (S.union_intersection_exact1 T) (S.union_intersection_exact2 T)

/-- 原始セル構成から生成された標準零延長のSES。 -/
theorem cellRow_shortExact {q : Reading Source} {D : TargetSupportedNerve q}
    (S T : CellSelection D) : (cellRow S T).ShortExact :=
  row_shortExact _ _ _ _ _ (S.unionInclusion_injective0 T) (S.unionInclusion_injective1 T)
    (S.unionInclusion_injective2 T) (S.intersectionDifference_surjective0 T)
    (S.intersectionDifference_surjective1 T) (S.intersectionDifference_surjective2 T)

/-- 二つの三項比較を同じ二領域積の各次数へ作用させる。 -/
def pairHom {C D E F : ThreeCochainComplex.{0,u} ℚ}
    (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F) :
    ThreeCochainComplex.Hom (pairComplex C D) (pairComplex E F) where
  f0 := f.f0.prodMap g.f0
  f1 := f.f1.prodMap g.f1
  f2 := f.f2.prodMap g.f2
  comm0 x := Prod.ext (f.comm0 x.1) (g.comm0 x.2)
  comm1 x := Prod.ext (f.comm1 x.1) (g.comm1 x.2)

/-- 二領域比較の次数0成分は同じ二つの比較の積。 -/
@[simp] theorem pairHom_f0 {C D E F : ThreeCochainComplex.{0,u} ℚ}
    (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F)
    (x : C.C0 × D.C0) : (pairHom f g).f0 x = (f.f0 x.1,g.f0 x.2) := rfl
/-- 二領域比較の次数1成分は同じ二つの比較の積。 -/
@[simp] theorem pairHom_f1 {C D E F : ThreeCochainComplex.{0,u} ℚ}
    (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F)
    (x : C.C1 × D.C1) : (pairHom f g).f1 x = (f.f1 x.1,g.f1 x.2) := rfl
/-- 二領域比較の次数2成分は同じ二つの比較の積。 -/
@[simp] theorem pairHom_f2 {C D E F : ThreeCochainComplex.{0,u} ℚ}
    (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F)
    (x : C.C2 × D.C2) : (pairHom f g).f2 x = (f.f2 x.1,g.f2 x.2) := rfl

variable {Sc Tc : CellSelection Nc} {Sf Tf : CellSelection Nf}
variable (hs : SelectionCompatible M Sc Sf) (ht : SelectionCompatible M Tc Tf)

/-- 原始Mの六つの正方形から、同じ二行SESの比較を生成する。 -/
def cellRowMap : cellRow Sc Tc ⟶ cellRow Sf Tf where
  τ₁ := zeroExtensionMap (hs.union M ht).hom
  τ₂ := zeroExtensionMap (pairHom hs.hom ht.hom)
  τ₃ := zeroExtensionMap (hs.inter M ht).hom
  comm₁₂ := by
    change zeroExtensionMap _ ≫ zeroExtensionMap _ = zeroExtensionMap _ ≫ zeroExtensionMap _
    rw [← zeroExtensionMap_comp, ← zeroExtensionMap_comp]
    congr 1
    apply cochain_ext
    · exact (hs.union_square0 ht).symm
    · exact (hs.union_square1 ht).symm
    · exact (hs.union_square2 ht).symm
  comm₂₃ := by
    change zeroExtensionMap _ ≫ zeroExtensionMap _ = zeroExtensionMap _ ≫ zeroExtensionMap _
    rw [← zeroExtensionMap_comp, ← zeroExtensionMap_comp]
    congr 1
    apply cochain_ext
    · exact (hs.inter_square0 ht).symm
    · exact (hs.inter_square1 ht).symm
    · exact (hs.inter_square2 ht).symm
end StandardRow
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
