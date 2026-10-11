import ResearchLean.AG.AtlasGluingWidth.PrimitiveGluing
import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import ResearchLean.AG.AtlasDefectComposition.FiniteLinearFamily
import Formal.Util.AssertStandardAxioms
/-! # 有限ラベル族の同じcochain短完全列と実Q/P

GOAL D／設計exact-sequence §5。各成分の原始SESを同じ有限族へ集める。
一般hRは方向仮定で、Law適用では各labelのcellRow_shortExactが生成する。
Implementation notes: G133の元を保持する有限族複体とhomology同型を採用する。
labelの支持集合へ添字を圧縮する案は同じ支持の重複度を消すため退けた。
実Q/Pは同じrange quotient/kernelを保ち、同じ標準δの自然性で成分に戻す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.FiniteGluing
open AAT.AG.AtlasDefectComposition
universe u
variable {J : Type u}
variable (R : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ))
/-- 全ラベルの実短複体を元の二射の成分族として作る。 -/
def row : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (FiniteComplexFamily.map _ _ (fun j => (R j).f))
    (FiniteComplexFamily.map _ _ (fun j => (R j).g)) (by
      apply HomologicalComplex.hom_ext
      intro m
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext j
      exact congrArg (fun f => f.f m (x j)) (R j).zero)
/-- 有限族SESの第一射は同じ元の制限の成分評価。 -/
@[simp] theorem row_f_apply (m : ℤ) (x : (row R).X₁.X m) (j : J) :
    (row R).f.f m x j = (R j).f.f m (x j) := rfl
/-- 有限族SESの第二射は同じ元の差制限の成分評価。 -/
@[simp] theorem row_g_apply (m : ℤ) (x : (row R).X₂.X m) (j : J) :
    (row R).g.f m x j = (R j).g.f m (x j) := rfl
/-- 各成分で生成されたSESから全整数次数の族SESを生成する。 -/
theorem row_shortExact (hR : ∀ j, (R j).ShortExact) : (row R).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro m
  have hs := fun j => (shortExact_iff_degreewise_shortExact (R j)).mp (hR j) m
  have he := fun j => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hs j).exact
  have hi := fun j => (ModuleCat.mono_iff_injective _).mp (hs j).mono_f
  have hp := fun j => (ModuleCat.epi_iff_surjective _).mp (hs j).epi_g
  refine { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr ?_
           mono_f := (ModuleCat.mono_iff_injective _).mpr ?_
           epi_g := (ModuleCat.epi_iff_surjective _).mpr ?_ }
  · intro y
    constructor
    · intro hy
      have hyj := fun j => congrFun hy j
      have hx : ∀ j, ∃ x, (R j).f.f m x = y j := fun j => (he j (y j)).mp (hyj j)
      choose x hx using hx
      exact ⟨x,funext hx⟩
    · rintro ⟨x,rfl⟩
      funext j
      exact (he j ((R j).f.f m (x j))).mpr ⟨x j,rfl⟩
  · intro x y hxy
    funext j
    exact hi j (congrFun hxy j)
  · intro z
    choose x hx using fun j => hp j (z j)
    exact ⟨x,funext hx⟩
variable {T : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)}
/-- 原始二行比較を各実ラベル成分のまま族比較へ集める。 -/
def rowMap (v : ∀ j, R j ⟶ T j) : row R ⟶ row T where
  τ₁ := FiniteComplexFamily.map _ _ (fun j => (v j).τ₁)
  τ₂ := FiniteComplexFamily.map _ _ (fun j => (v j).τ₂)
  τ₃ := FiniteComplexFamily.map _ _ (fun j => (v j).τ₃)
  comm₁₂ := by
    apply HomologicalComplex.hom_ext
    intro m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    exact congrArg (fun f => f.f m (x j)) (v j).comm₁₂
  comm₂₃ := by
    apply HomologicalComplex.hom_ext
    intro m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    exact congrArg (fun f => f.f m (x j)) (v j).comm₂₃
/-- 族の短複体から同じ元のラベル行への射影。 -/
def projection (j : J) : row R ⟶ R j where
  τ₁ := FiniteComplexFamily.projection _ j
  τ₂ := FiniteComplexFamily.projection _ j
  τ₃ := FiniteComplexFamily.projection _ j
  comm₁₂ := (FiniteComplexFamily.map_projection (fun j => (R j).X₁) (fun j => (R j).X₂) (fun j => (R j).f) j).symm
  comm₂₃ := (FiniteComplexFamily.map_projection (fun j => (R j).X₂) (fun j => (R j).X₃) (fun j => (R j).g) j).symm
/-- 元の二行図式の全ラベル合併比較は同じ成分値を読む。 -/
@[simp] theorem rowMap_tau1_apply (v : ∀ j, R j ⟶ T j) (m : ℤ)
    (x : (row R).X₁.X m) (j : J) : (rowMap R v).τ₁.f m x j = (v j).τ₁.f m (x j) := rfl
/-- 元の二行図式の全ラベル局所比較は同じ成分値を読む。 -/
@[simp] theorem rowMap_tau2_apply (v : ∀ j, R j ⟶ T j) (m : ℤ)
    (x : (row R).X₂.X m) (j : J) : (rowMap R v).τ₂.f m x j = (v j).τ₂.f m (x j) := rfl
/-- 元の二行図式の全ラベル交差比較は同じ成分値を読む。 -/
@[simp] theorem rowMap_tau3_apply (v : ∀ j, R j ⟶ T j) (m : ℤ)
    (x : (row R).X₃.X m) (j : J) : (rowMap R v).τ₃.f m x j = (v j).τ₃.f m (x j) := rfl
variable [Fintype J]
/-- 有限族の実Qを同じ各ラベルの実Qへ同定する。 -/
def qEquiv : QuotientKernelRow.Q (row R) ≃ₗ[ℚ] ((j : J) → QuotientKernelRow.Q (R j)) :=
  (LinearConjugation.cokernelEquiv _ _ (FiniteComplexFamily.homologyEquiv _ 0)
    (FiniteComplexFamily.homologyEquiv _ 0) (fun x => funext fun j =>
      FiniteComplexFamily.homologyEquiv_natural _ _ (fun j => (R j).g) 0 x j)).trans
    (FiniteLinearFamily.cokernelEquiv _)
/-- 有限族の実Pを同じ各ラベルの実Pへ同定する。 -/
def pEquiv : QuotientKernelRow.P (row R) ≃ₗ[ℚ] ((j : J) → QuotientKernelRow.P (R j)) :=
  (LinearConjugation.kernelEquiv _ _ (FiniteComplexFamily.homologyEquiv _ 1)
    (FiniteComplexFamily.homologyEquiv _ 1) (fun x => funext fun j =>
      FiniteComplexFamily.homologyEquiv_natural _ _ (fun j => (R j).g) 1 x j)).trans
    (FiniteLinearFamily.kernelEquiv _)
/-- Q同定は元の交差H⁰代表の同じラベル商類を読む。 -/
@[simp] theorem qEquiv_mk (z : (row R).X₃.homology (0:ℤ)) (j : J) :
    qEquiv R ((LinearMap.range (homologyMap (row R).g 0).hom).mkQ z) j =
      (LinearMap.range (homologyMap (R j).g 0).hom).mkQ
        (FiniteComplexFamily.homologyEquiv _ 0 z j) := rfl
/-- P同定は元の二領域H¹の同じラベル成分値を保持する。 -/
@[simp] theorem pEquiv_val (z : QuotientKernelRow.P (row R)) (j : J) :
    (pEquiv R z j).val = FiniteComplexFamily.homologyEquiv _ 1 z.val j := rfl
/-- Q/H¹包含は同じ標準δの各ラベル成分として自然である。 -/
theorem inclusion_component (hR : ∀ j, (R j).ShortExact)
    (z : QuotientKernelRow.Q (row R)) (j : J) :
    FiniteComplexFamily.homologyEquiv _ 1
        (QuotientKernelRow.inclusion (row R) (row_shortExact R hR) z) j =
      QuotientKernelRow.inclusion (R j) (hR j) (qEquiv R z j) := by
  obtain ⟨x,rfl⟩ := (LinearMap.range (homologyMap (row R).g 0).hom).mkQ_surjective z
  rw [qEquiv_mk,QuotientKernelRow.inclusion_mk,QuotientKernelRow.inclusion_mk]
  rw [FiniteComplexFamily.homologyEquiv_component,FiniteComplexFamily.homologyEquiv_component]
  simpa only [ModuleCat.comp_apply] using congrArg (fun f => f x) (HomologySequence.δ_naturality (projection R j)
    (row_shortExact R hR) (hR j) 0 1 rfl)
/-- H¹/P射影は同じ元の合併制限の各ラベル成分である。 -/
theorem projection_component (hR : ∀ j, (R j).ShortExact)
    (z : (row R).X₁.homology (1:ℤ)) (j : J) :
    pEquiv R (QuotientKernelRow.projection (row R) (row_shortExact R hR) z) j =
      QuotientKernelRow.projection (R j) (hR j) (FiniteComplexFamily.homologyEquiv _ 1 z j) := by
  apply Subtype.ext
  rw [pEquiv_val,QuotientKernelRow.projection_val,QuotientKernelRow.projection_val]
  exact FiniteComplexFamily.homologyEquiv_natural _ _ (fun j => (R j).f) 1 z j
/-- 全ラベルのQ比較は各同じ交差H⁰比較の商射である。 -/
theorem q_component (v : ∀ j, R j ⟶ T j) (z : QuotientKernelRow.Q (row R)) (j : J) :
    qEquiv T (QuotientKernelRow.q (row R) (rowMap R v) z) j =
      QuotientKernelRow.q (R j) (v j) (qEquiv R z j) := by
  obtain ⟨x,rfl⟩ := (LinearMap.range (homologyMap (row R).g 0).hom).mkQ_surjective z
  rw [QuotientKernelRow.q_mk,qEquiv_mk,qEquiv_mk,QuotientKernelRow.q_mk]
  exact congrArg (LinearMap.range (homologyMap (T j).g 0).hom).mkQ
    (FiniteComplexFamily.homologyEquiv_natural _ _ (fun j => (v j).τ₃) 0 x j)
/-- 全ラベルのP比較は各同じ局所H¹比較の核制限である。 -/
theorem p_component (v : ∀ j, R j ⟶ T j) (z : QuotientKernelRow.P (row R)) (j : J) :
    pEquiv T (QuotientKernelRow.p (row R) (rowMap R v) z) j =
      QuotientKernelRow.p (R j) (v j) (pEquiv R z j) := by
  apply Subtype.ext
  rw [pEquiv_val,QuotientKernelRow.p_val,QuotientKernelRow.p_val,pEquiv_val]
  exact FiniteComplexFamily.homologyEquiv_natural _ _ (fun j => (v j).τ₂) 1 z.val j
/-- 全整数次数の族標準連結射は同じラベルの連結射を読む。 -/
theorem connecting_component (hR : ∀ j, (R j).ShortExact) (m : ℤ)
    (x : (row R).X₃.homology m) (j : J) :
    FiniteComplexFamily.homologyEquiv _ (m+1)
      (StandardLES.connecting (row R) (row_shortExact R hR) m x) j =
    StandardLES.connecting (R j) (hR j) m (FiniteComplexFamily.homologyEquiv _ m x j) := by
  rw [FiniteComplexFamily.homologyEquiv_component,FiniteComplexFamily.homologyEquiv_component]
  simpa only [ModuleCat.comp_apply] using congrArg (fun f => f x)
    (HomologySequence.δ_naturality (projection R j) (row_shortExact R hR) (hR j) m (m+1) rfl)
/-- 同じ全ラベル合併H¹比較の核を各実核へ同定する。 -/
def phantomEquiv (v : ∀ j, R j ⟶ T j) :
    LinearMap.ker (homologyMap (rowMap R v).τ₁ (1:ℤ)).hom ≃ₗ[ℚ]
      ((j : J) → LinearMap.ker (homologyMap (v j).τ₁ (1:ℤ)).hom) :=
  (LinearConjugation.kernelEquiv _ _ (FiniteComplexFamily.homologyEquiv _ 1)
    (FiniteComplexFamily.homologyEquiv _ 1) (fun x => funext fun j =>
      FiniteComplexFamily.homologyEquiv_natural _ _ (fun j => (v j).τ₁) 1 x j)).trans
    (FiniteLinearFamily.kernelEquiv _)
/-- 同じ全ラベル合併H¹比較の余核を各実余核へ同定する。 -/
def hiddenEquiv (v : ∀ j, R j ⟶ T j) :
    ((row T).X₁.homology (1:ℤ) ⧸ LinearMap.range (homologyMap (rowMap R v).τ₁ 1).hom) ≃ₗ[ℚ]
      ((j : J) → (T j).X₁.homology (1:ℤ) ⧸ LinearMap.range (homologyMap (v j).τ₁ 1).hom) :=
  (LinearConjugation.cokernelEquiv _ _ (FiniteComplexFamily.homologyEquiv _ 1)
    (FiniteComplexFamily.homologyEquiv _ 1) (fun x => funext fun j =>
      FiniteComplexFamily.homologyEquiv_natural _ _ (fun j => (v j).τ₁) 1 x j)).trans
    (FiniteLinearFamily.cokernelEquiv _)
/-- 核同定は同じ粗合併H¹のラベル成分を読む。 -/
@[simp] theorem phantomEquiv_val (v : ∀ j, R j ⟶ T j)
    (x : LinearMap.ker (homologyMap (rowMap R v).τ₁ (1:ℤ)).hom) (j : J) :
    (phantomEquiv R v x j).val = FiniteComplexFamily.homologyEquiv _ 1 x.val j := rfl
/-- 余核同定は同じ細合併H¹の全商代表元を読む。 -/
@[simp] theorem hiddenEquiv_mk (v : ∀ j, R j ⟶ T j) (x : (row T).X₁.homology (1:ℤ)) (j : J) :
    hiddenEquiv R v ((LinearMap.range (homologyMap (rowMap R v).τ₁ 1).hom).mkQ x) j =
      (LinearMap.range (homologyMap (v j).τ₁ 1).hom).mkQ (FiniteComplexFamily.homologyEquiv _ 1 x j) := rfl
/-- 各ラベルの同じhomology比較の全単射性から族比較の全単射性を生成する。 -/
theorem homology_bijective
    (F G : J → CochainComplex (ModuleCat.{u} ℚ) ℤ) (φ : ∀ j, F j ⟶ G j) (m : ℤ)
    (hφ : ∀ j, Function.Bijective (homologyMap (φ j) m)) :
    Function.Bijective (homologyMap (FiniteComplexFamily.map F G φ) m) := by
  constructor
  · intro x y hxy
    apply (FiniteComplexFamily.homologyEquiv F m).injective
    funext j
    apply (hφ j).1
    rw [← FiniteComplexFamily.homologyEquiv_natural F G φ m x j,
      ← FiniteComplexFamily.homologyEquiv_natural F G φ m y j,hxy]
  · intro y
    have hz : ∀ j, ∃ z, homologyMap (φ j) m z = FiniteComplexFamily.homologyEquiv G m y j :=
      fun j => (hφ j).2 _
    choose z hz using hz
    refine ⟨(FiniteComplexFamily.homologyEquiv F m).symm z,?_⟩
    apply (FiniteComplexFamily.homologyEquiv G m).injective
    funext j
    rw [FiniteComplexFamily.homologyEquiv_natural F G φ m _ j,LinearEquiv.apply_symm_apply]
    exact hz j
end AAT.AG.AtlasGluingWidth.FiniteGluing
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.FiniteGluing
