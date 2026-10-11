import ResearchLean.AG.AtlasGluingWidth.MayerVietoris
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Formal.Util.AssertStandardAxioms
/-! # 標準snake列を実線形核・余核へ移す

GOAL C／設計 exact-sequence §3–4。一般二行のSESは方向仮定であり、原始適用では
QuotientKernelRow.row_shortExact が標準MV列から生成する。全可換条件はその同じrowMapを使う。
Implementation notes: ShortComplex圏の標準kernel/cokernelから標準SnakeInputを生成し、
成分の普遍性でliteral LinearMap.ker/range quotientへ移す。独自のsnake連結射を持ち上げの選択から
定義する案は、標準δとの符号と選択独立性の同定を重複させるため退けた。
同次元の空間への置換案は元の包含・商・代表式を保持しないため退けた。
-/
noncomputable section
open CategoryTheory Limits
namespace AAT.AG.AtlasGluingWidth
namespace LinearSnake
universe u
variable (R S : ShortComplex (ModuleCat.{u} ℚ)) (hR : R.ShortExact) (hS : S.ShortExact) (v : R ⟶ S)
/-- GOAL C／設計§3: 同じ二行SESと比較から標準snake入力の全fieldを生成する。 -/
def snake : ShortComplex.SnakeInput (ModuleCat.{u} ℚ) where
  L₀ := kernel v
  L₁ := R
  L₂ := S
  L₃ := cokernel v
  v₀₁ := kernel.ι v
  v₁₂ := v
  v₂₃ := cokernel.π v
  w₀₂ := kernel.condition v
  w₁₃ := cokernel.condition v
  h₀ := kernelIsKernel v
  h₃ := cokernelIsCokernel v
  L₁_exact := hR.exact
  epi_L₁_g := hR.epi_g
  L₂_exact := hS.exact
  mono_L₂_f := hS.mono_f

variable {K X Y : ModuleCat.{u} ℚ}
/-- 核の普遍性によりliteral kernelへ移す、包含を保つ同型／API。 -/
def kernelIso (f : X ⟶ Y) (i : K ⟶ X) (hi : i ≫ f = 0)
    (H : IsLimit (KernelFork.ofι i hi)) : K ≅ ModuleCat.of ℚ (LinearMap.ker f.hom) :=
  IsLimit.conePointUniqueUpToIso H (ModuleCat.kernelIsLimit f)
/-- 余核の普遍性によりliteral range quotientへ移す、商を保つ同型／API。 -/
def cokerIso (f : X ⟶ Y) (i : Y ⟶ K) (hi : f ≫ i = 0)
    (H : IsColimit (CokernelCofork.ofπ i hi)) : K ≅ ModuleCat.of ℚ (Y ⧸ LinearMap.range f.hom) :=
  IsColimit.coconePointUniqueUpToIso H (ModuleCat.cokernelIsColimit f)
/-- 核の普遍性によりliteral kernelへ移す、包含を保つ同型／API。 -/
@[reassoc] theorem kernelIso_subtype (f : X ⟶ Y) (i : K ⟶ X) (hi : i ≫ f = 0)
    (H : IsLimit (KernelFork.ofι i hi)) :
    (kernelIso f i hi H).hom ≫ ModuleCat.ofHom (LinearMap.ker f.hom).subtype = i :=
  IsLimit.conePointUniqueUpToIso_hom_comp H (ModuleCat.kernelIsLimit f) WalkingParallelPair.zero
/-- 核の普遍性によりliteral kernelへ移す、包含を保つ同型／API。 -/
@[reassoc] theorem kernelIso_inv_inclusion (f : X ⟶ Y) (i : K ⟶ X) (hi : i ≫ f = 0)
    (H : IsLimit (KernelFork.ofι i hi)) :
    (kernelIso f i hi H).inv ≫ i = ModuleCat.ofHom (LinearMap.ker f.hom).subtype :=
  IsLimit.conePointUniqueUpToIso_inv_comp H (ModuleCat.kernelIsLimit f) WalkingParallelPair.zero
/-- 余核の普遍性によりliteral range quotientへ移す、商を保つ同型／API。 -/
@[reassoc] theorem cokerIso_mk (f : X ⟶ Y) (i : Y ⟶ K) (hi : f ≫ i = 0)
    (H : IsColimit (CokernelCofork.ofπ i hi)) :
    i ≫ (cokerIso f i hi H).hom = ModuleCat.ofHom (LinearMap.range f.hom).mkQ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom H (ModuleCat.cokernelIsColimit f) WalkingParallelPair.one
/-- 余核の普遍性によりliteral range quotientへ移す、商を保つ同型／API。 -/
@[reassoc] theorem cokerIso_inv_mk (f : X ⟶ Y) (i : Y ⟶ K) (hi : f ≫ i = 0)
    (H : IsColimit (CokernelCofork.ofπ i hi)) :
    ModuleCat.ofHom (LinearMap.range f.hom).mkQ ≫ (cokerIso f i hi H).inv = i :=
  IsColimit.comp_coconePointUniqueUpToIso_inv H (ModuleCat.cokernelIsColimit f) WalkingParallelPair.one

variable (D : ShortComplex.SnakeInput (ModuleCat.{u} ℚ))
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
def K1 := kernelIso D.v₁₂.τ₁ D.v₀₁.τ₁ D.w₀₂_τ₁ D.h₀τ₁
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
def K2 := kernelIso D.v₁₂.τ₂ D.v₀₁.τ₂ D.w₀₂_τ₂ D.h₀τ₂
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
def K3 := kernelIso D.v₁₂.τ₃ D.v₀₁.τ₃ D.w₀₂_τ₃ D.h₀τ₃
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
def C1 := cokerIso D.v₁₂.τ₁ D.v₂₃.τ₁ D.w₁₃_τ₁ D.h₃τ₁
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
def C2 := cokerIso D.v₁₂.τ₂ D.v₂₃.τ₂ D.w₁₃_τ₂ D.h₃τ₂
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
def C3 := cokerIso D.v₁₂.τ₃ D.v₂₃.τ₃ D.w₁₃_τ₃ D.h₃τ₃

/-- 標準snakeの同じ射を、普遍同型で実核・実余核の型へ輸送する。 -/
def first := (K1 D).inv ≫ D.L₀.f ≫ (K2 D).hom
/-- 標準snakeの同じ射を、普遍同型で実核・実余核の型へ輸送する。 -/
def second := (K2 D).inv ≫ D.L₀.g ≫ (K3 D).hom
/-- 標準snakeの同じ射を、普遍同型で実核・実余核の型へ輸送する。 -/
def connecting := (K3 D).inv ≫ D.δ ≫ (C1 D).hom
/-- 標準snakeの同じ射を、普遍同型で実核・実余核の型へ輸送する。 -/
def fourth := (C1 D).inv ≫ D.L₃.f ≫ (C2 D).hom
/-- 標準snakeの同じ射を、普遍同型で実核・実余核の型へ輸送する。 -/
def fifth := (C2 D).inv ≫ D.L₃.g ≫ (C3 D).hom

variable {A B C A' B' C' : ModuleCat.{u} ℚ}
/-- 線形同型に沿う実射の輸送と、標準exactnessの保持API。 -/
def conjugate (f : A ⟶ B) (eA : A ≅ A') (eB : B ≅ B') := eA.inv ≫ f ≫ eB.hom
/-- 線形同型に沿う実射の輸送と、標準exactnessの保持API。 -/
@[simp] theorem conjugate_apply (f : A ⟶ B) (eA : A ≅ A') (eB : B ≅ B') (x : A') :
  conjugate f eA eB x = eB.hom (f (eA.inv x)) := rfl

/-- 線形同型に沿う実射の輸送と、標準exactnessの保持API。 -/
theorem conjugate_exact (f : A ⟶ B) (g : B ⟶ C) (hfg : Function.Exact f g)
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C') :
    Function.Exact (conjugate f eA eB) (conjugate g eB eC) := by
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := eA.toLinearEquiv) (e₂ := eB.toLinearEquiv) (e₃ := eC.toLinearEquiv)
    (f₁₂ := f.hom) (f₂₃ := g.hom) (H := hfg)
  · apply LinearMap.ext
    intro x
    change eB.hom (f (eA.inv (eA.hom x))) = eB.hom (f x)
    have h := congrArg (fun t => t x) eA.hom_inv_id
    change eA.inv (eA.hom x) = x at h
    rw [h]
  · apply LinearMap.ext
    intro x
    change eC.hom (g (eB.inv (eB.hom x))) = eC.hom (g x)
    have h := congrArg (fun t => t x) eB.hom_inv_id
    change eB.inv (eB.hom x) = x at h
    rw [h]

/-- 標準snakeの対応位置の完全性を、実核・実余核の同じ射へ移す。 -/
theorem exact1 : Function.Exact (first D) (second D) :=
  conjugate_exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp D.L₀_exact)
    (K1 D) (K2 D) (K3 D)
/-- 標準snakeの対応位置の完全性を、実核・実余核の同じ射へ移す。 -/
theorem exact2 : Function.Exact (second D) (connecting D) :=
  conjugate_exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp D.L₁'_exact)
    (K2 D) (K3 D) (C1 D)
/-- 標準snakeの対応位置の完全性を、実核・実余核の同じ射へ移す。 -/
theorem exact3 : Function.Exact (connecting D) (fourth D) :=
  conjugate_exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp D.L₂'_exact)
    (K3 D) (C1 D) (C2 D)
/-- 標準snakeの対応位置の完全性を、実核・実余核の同じ射へ移す。 -/
theorem exact4 : Function.Exact (fourth D) (fifth D) :=
  conjugate_exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp D.L₃_exact)
    (C1 D) (C2 D) (C3 D)

/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
@[reassoc] theorem K1_inv_inclusion : (K1 D).inv ≫ D.v₀₁.τ₁ = ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₁.hom).subtype :=
  kernelIso_inv_inclusion _ _ _ _
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
@[reassoc] theorem K2_inv_inclusion : (K2 D).inv ≫ D.v₀₁.τ₂ = ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₂.hom).subtype :=
  kernelIso_inv_inclusion _ _ _ _
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
@[reassoc] theorem K3_inv_inclusion : (K3 D).inv ≫ D.v₀₁.τ₃ = ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₃.hom).subtype :=
  kernelIso_inv_inclusion _ _ _ _
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
@[reassoc] theorem K1_subtype : (K1 D).hom ≫ ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₁.hom).subtype = D.v₀₁.τ₁ :=
  kernelIso_subtype _ _ _ _
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
@[reassoc] theorem K2_subtype : (K2 D).hom ≫ ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₂.hom).subtype = D.v₀₁.τ₂ :=
  kernelIso_subtype _ _ _ _
/-- 標準snakeの対応核成分とliteral kernelとの包含を保つ普遍同型／評価API。 -/
@[reassoc] theorem K3_subtype : (K3 D).hom ≫ ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₃.hom).subtype = D.v₀₁.τ₃ :=
  kernelIso_subtype _ _ _ _
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
@[reassoc] theorem C1_mk : D.v₂₃.τ₁ ≫ (C1 D).hom = ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₁.hom).mkQ :=
  cokerIso_mk _ _ _ _
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
@[reassoc] theorem C2_mk : D.v₂₃.τ₂ ≫ (C2 D).hom = ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₂.hom).mkQ :=
  cokerIso_mk _ _ _ _
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
@[reassoc] theorem C3_mk : D.v₂₃.τ₃ ≫ (C3 D).hom = ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₃.hom).mkQ :=
  cokerIso_mk _ _ _ _
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
@[reassoc] theorem C1_inv_mk : ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₁.hom).mkQ ≫ (C1 D).inv = D.v₂₃.τ₁ :=
  cokerIso_inv_mk _ _ _ _
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
@[reassoc] theorem C2_inv_mk : ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₂.hom).mkQ ≫ (C2 D).inv = D.v₂₃.τ₂ :=
  cokerIso_inv_mk _ _ _ _
/-- 標準snakeの対応余核成分とliteral range quotientとの商を保つ普遍同型／評価API。 -/
@[reassoc] theorem C3_inv_mk : ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₃.hom).mkQ ≫ (C3 D).inv = D.v₂₃.τ₃ :=
  cokerIso_inv_mk _ _ _ _

/-- 輸送したsnake射は元の行射を全実元／商代表元で読む。 -/
theorem first_val (a : LinearMap.ker D.v₁₂.τ₁.hom) : (first D a).val = D.L₁.f a.val := by
  have h : first D ≫ ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₂.hom).subtype =
      ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₁.hom).subtype ≫ D.L₁.f := by
    simp only [first, Category.assoc, K2_subtype, ← D.v₀₁.comm₁₂, K1_inv_inclusion_assoc]
  exact congrArg (fun f => f a) h

/-- 輸送したsnake射は元の行射を全実元／商代表元で読む。 -/
theorem second_val (a : LinearMap.ker D.v₁₂.τ₂.hom) : (second D a).val = D.L₁.g a.val := by
  have h : second D ≫ ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₃.hom).subtype =
      ModuleCat.ofHom (LinearMap.ker D.v₁₂.τ₂.hom).subtype ≫ D.L₁.g := by
    simp only [second, Category.assoc, K3_subtype, ← D.v₀₁.comm₂₃, K2_inv_inclusion_assoc]
  exact congrArg (fun f => f a) h

/-- 輸送したsnake射は元の行射を全実元／商代表元で読む。 -/
theorem fourth_mk (z : D.L₂.X₁) :
    fourth D ((LinearMap.range D.v₁₂.τ₁.hom).mkQ z) =
      (LinearMap.range D.v₁₂.τ₂.hom).mkQ (D.L₂.f z) := by
  have h : ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₁.hom).mkQ ≫ fourth D =
      D.L₂.f ≫ ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₂.hom).mkQ := by
    simp only [fourth, C1_inv_mk_assoc, D.v₂₃.comm₁₂_assoc, C2_mk]
  exact congrArg (fun f => f z) h

/-- 輸送したsnake射は元の行射を全実元／商代表元で読む。 -/
theorem fifth_mk (z : D.L₂.X₂) :
    fifth D ((LinearMap.range D.v₁₂.τ₂.hom).mkQ z) =
      (LinearMap.range D.v₁₂.τ₃.hom).mkQ (D.L₂.g z) := by
  have h : ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₂.hom).mkQ ≫ fifth D =
      D.L₂.g ≫ ModuleCat.ofHom (LinearMap.range D.v₁₂.τ₃.hom).mkQ := by
    simp only [fifth, C2_inv_mk_assoc, D.v₂₃.comm₂₃_assoc, C3_mk]
  exact congrArg (fun f => f z) h

/-- 粗行包含の単射性から、実核のsnake包含は単射。 -/
theorem first_injective [Mono D.L₁.f] : Function.Injective (first D) := by
  intro x y h
  apply Subtype.ext
  apply (ModuleCat.mono_iff_injective D.L₁.f).mp inferInstance
  exact (first_val D x).symm.trans ((congrArg Subtype.val h).trans (first_val D y))

/-- 細行射の全射性から、実余核のsnake射は全射。 -/
theorem fifth_surjective [Epi D.L₂.g] : Function.Surjective (fifth D) := by
  intro z
  obtain ⟨x,rfl⟩ := (LinearMap.range D.v₁₂.τ₃.hom).mkQ_surjective z
  obtain ⟨y,hy⟩ := (ModuleCat.epi_iff_surjective D.L₂.g).mp inferInstance x
  refine ⟨(LinearMap.range D.v₁₂.τ₂.hom).mkQ y,?_⟩
  rw [fifth_mk, hy]

/-- GOAL C／設計§3: 粗行の持ち上げと細行の原像は符号込みで標準snakeδの実余核class。 -/
theorem connecting_representative (a : LinearMap.ker D.v₁₂.τ₃.hom)
    (b : D.L₁.X₂) (hb : D.L₁.g b = a.val) (z : D.L₂.X₁)
    (hz : D.L₂.f z = D.v₁₂.τ₂ b) :
    connecting D a = (LinearMap.range D.v₁₂.τ₁.hom).mkQ z := by
  open AAT.AG.AtlasGluingWidth.CohomologyRepresentatives in
  have h := D.δ_eq (scalarPoint ((K3 D).inv a)) (scalarPoint b) (scalarPoint z)
    (by
      rw [scalarPoint_comp, scalarPoint_comp]
      congr 1
      have hK := congrArg (fun f => f a) (K3_inv_inclusion D)
      exact hb.trans hK.symm)
    (by rw [scalarPoint_comp, scalarPoint_comp, hz])
  have he := congrArg (fun f => f (ULift.up (1:ℚ))) h
  change D.δ ((1:ℚ) • ((K3 D).inv a)) = D.v₂₃.τ₁ ((1:ℚ) • z) at he
  simp only [one_smul] at he
  have hm := congrArg (fun f => f z) (C1_mk D)
  change (C1 D).hom (D.v₂₃.τ₁ z) = (LinearMap.range D.v₁₂.τ₁.hom).mkQ z at hm
  exact (congrArg (fun x => (C1 D).hom x) he).trans hm

/-- 標準snakeの任意実核元から、粗行の持ち上げと細行の原像を生成する。 -/
theorem connecting_lift (a : LinearMap.ker D.v₁₂.τ₃.hom) :
    ∃ (b : D.L₁.X₂) (z : D.L₂.X₁), D.L₁.g b = a.val ∧ D.L₂.f z = D.v₁₂.τ₂ b := by
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective D.L₁.g).mp inferInstance a.val
  have hk : D.L₂.g (D.v₁₂.τ₂ b) = 0 := by
    have h := congrArg (fun f => f b) D.v₁₂.comm₂₃
    change D.L₂.g (D.v₁₂.τ₂ b) = D.v₁₂.τ₃ (D.L₁.g b) at h
    rw [hb, a.property] at h
    exact h
  obtain ⟨z,hz⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp D.L₂_exact _).mp hk
  exact ⟨b,z,hb,hz⟩
/-- 同じ実核元の二つの持ち上げは同じ実余核classを与える。 -/
theorem connecting_choice_independent (a : LinearMap.ker D.v₁₂.τ₃.hom)
    (b b' : D.L₁.X₂) (hb : D.L₁.g b = a.val) (hb' : D.L₁.g b' = a.val)
    (z z' : D.L₂.X₁) (hz : D.L₂.f z = D.v₁₂.τ₂ b) (hz' : D.L₂.f z' = D.v₁₂.τ₂ b') :
    (LinearMap.range D.v₁₂.τ₁.hom).mkQ z = (LinearMap.range D.v₁₂.τ₁.hom).mkQ z' := by
  rw [← connecting_representative D a b hb z hz, connecting_representative D a b' hb' z' hz']

/-- 右端の比較が単射なら、snakeの右実核は零対象。 -/
theorem lastKernel_subsingleton (hp : Function.Injective D.v₁₂.τ₃) :
    Subsingleton (LinearMap.ker D.v₁₂.τ₃.hom) := by
  constructor
  intro a b
  apply Subtype.ext
  apply hp
  exact a.property.trans b.property.symm
/-- 右端比較の単射性とsnake完全性から、左実核比較は全射。 -/
theorem first_surjective_of_last_injective (hp : Function.Injective D.v₁₂.τ₃) :
    Function.Surjective (first D) := by
  letI := lastKernel_subsingleton D hp
  intro y
  exact (exact1 D y).mp (Subsingleton.elim _ _)
/-- 左行の単射性と右端比較の単射性から、実phantomは左実核に同定される。 -/
def firstEquiv [Mono D.L₁.f] (hp : Function.Injective D.v₁₂.τ₃) :
    LinearMap.ker D.v₁₂.τ₁.hom ≃ₗ[ℚ] LinearMap.ker D.v₁₂.τ₂.hom :=
  LinearEquiv.ofBijective (first D).hom ⟨first_injective D, first_surjective_of_last_injective D hp⟩
/-- 核同型の順写像は元の粗行包含を制限した同じ射。 -/
@[simp] theorem firstEquiv_val [Mono D.L₁.f] (hp : Function.Injective D.v₁₂.τ₃)
    (a : LinearMap.ker D.v₁₂.τ₁.hom) : (firstEquiv D hp a).val = D.L₁.f a.val := first_val D a
/-- 右端比較の単射性から、実余核のsnake包含は単射。 -/
theorem fourth_injective_of_last_injective (hp : Function.Injective D.v₁₂.τ₃) :
    Function.Injective (fourth D) := by
  letI := lastKernel_subsingleton D hp
  intro x y hxy
  have hk : fourth D (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨a,ha⟩ := (exact3 D (x-y)).mp hk
  have ha0 : a = 0 := Subsingleton.elim _ _
  rw [ha0, map_zero] at ha
  exact sub_eq_zero.mp ha.symm
/-- 実coker q→hidden→実coker pの同じsnake短複体。 -/
def hiddenRow : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.mk (fourth D) (fifth D) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (exact4 D (fourth D x)).mpr ⟨x,rfl⟩)
/-- GOAL C／設計§4: 右端比較が単射なら、実hiddenのsnake短完全列。 -/
theorem hiddenRow_shortExact [Epi D.L₂.g] (hp : Function.Injective D.v₁₂.τ₃) :
    (hiddenRow D).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (exact4 D)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (fourth_injective_of_last_injective D hp)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (fifth_surjective D)
end LinearSnake
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
