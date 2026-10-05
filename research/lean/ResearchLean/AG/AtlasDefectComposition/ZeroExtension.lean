import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Formal.Util.AssertStandardAxioms
/-! # 三項複体の標準零延長

G-133 Cの零延長・全Hom・恒等/合成・既存H¹自然同型を構成する。

Implementation notes: 明示的な三項空間と零加群をCochainComplex.ofへ渡す。
元のH¹を新しい商へ定義し直す経路は採用せず、標準短複体のModuleCat homology
データと次数別自然同型を通す。原始比較には追加条件を課さない。
-/

noncomputable section
open CategoryTheory Limits
open scoped ZeroObject
namespace AAT.AG.AtlasDefectComposition
open TwoPhase
universe w
variable (C : ThreeCochainComplex.{0,w} ℚ)
/-- Cの零延長の各次数。三つの実空間と明示零加群を用いる基礎API。 -/
def degreeObject (C : ThreeCochainComplex.{0,w} ℚ) (n : ℤ) : ModuleCat.{w} ℚ :=
  if n = 0 then ModuleCat.of ℚ C.C0
  else if n = 1 then ModuleCat.of ℚ C.C1
  else if n = 2 then ModuleCat.of ℚ C.C2
  else ModuleCat.of ℚ (PUnit.{w+1})

/-- Cの二つの実微分を保つ次数別射。次数外の射は零である。 -/
def degreeDifferential (n : ℤ) : degreeObject C n ⟶ degreeObject C (n + 1) :=
  if h₀ : n = 0 then by subst n; exact ModuleCat.ofHom C.d0
  else if h₁ : n = 1 then by subst n; exact ModuleCat.ofHom C.d1
  else 0

/-- 元のd¹d⁰零性から零延長の全隣接微分の合成零性を放電する。 -/
theorem degreeDifferential_square (n : ℤ) :
    degreeDifferential C n ≫ degreeDifferential C (n + 1) = 0 := by
  by_cases h₀ : n = 0
  · subst n
    change ModuleCat.ofHom C.d0 ≫ ModuleCat.ofHom C.d1 = 0
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact C.d1_comp_d0 x
  · by_cases h₁ : n = 1
    · subst n
      simp [degreeDifferential]
    · simp only [degreeDifferential, dif_neg h₀, dif_neg h₁, zero_comp]

/-- Cの三項複体を標準ModuleCat有理ℤ cochain complexへ零延長する。 -/
def zeroExtension : CochainComplex (ModuleCat.{w} ℚ) ℤ :=
  CochainComplex.of (degreeObject C) (degreeDifferential C) (degreeDifferential_square C)

variable {C D E : ThreeCochainComplex.{0,w} ℚ}
/-- 入力Homの三成分を零延長する。追加の可換certificateは受け取らない。 -/
def degreeMap (f : ThreeCochainComplex.Hom C D) (n : ℤ) :
    degreeObject C n ⟶ degreeObject D n :=
  if h₀ : n = 0 then by subst n; exact ModuleCat.ofHom f.f0
  else if h₁ : n = 1 then by subst n; exact ModuleCat.ofHom f.f1
  else if h₂ : n = 2 then by subst n; exact ModuleCat.ofHom f.f2
  else 0

/-- 元のHom可換式から全次数のchain-map義務を放電する。 -/
theorem degreeMap_comm (f : ThreeCochainComplex.Hom C D) (n : ℤ) :
    degreeMap f n ≫ degreeDifferential D n =
      degreeDifferential C n ≫ degreeMap f (n + 1) := by
  by_cases h₀ : n = 0
  · subst n
    change ModuleCat.ofHom f.f0 ≫ ModuleCat.ofHom D.d0 =
      ModuleCat.ofHom C.d0 ≫ ModuleCat.ofHom f.f1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.comm0 x).symm
  · by_cases h₁ : n = 1
    · subst n
      change ModuleCat.ofHom f.f1 ≫ ModuleCat.ofHom D.d1 =
        ModuleCat.ofHom C.d1 ≫ ModuleCat.ofHom f.f2
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (f.comm1 x).symm
    · simp only [degreeDifferential, dif_neg h₀, dif_neg h₁, zero_comp, comp_zero]

/-- 元の全Homから標準零延長間の実chain mapを生成する。 -/
def zeroExtensionMap (f : ThreeCochainComplex.Hom C D) : zeroExtension C ⟶ zeroExtension D :=
  CochainComplex.ofHom _ _ _ _ _ _ (degreeMap f) (degreeMap_comm f)

/-- 生成されたHomの合成は標準complex射の合成と全次数で一致する。 -/
theorem zeroExtensionMap_comp (f : ThreeCochainComplex.Hom C D)
    (g : ThreeCochainComplex.Hom D E) :
    zeroExtensionMap (cochainComp f g) = zeroExtensionMap f ≫ zeroExtensionMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degreeMap (cochainComp f g) n = degreeMap f n ≫ degreeMap g n
  by_cases h₀ : n = 0
  · subst n; rfl
  · by_cases h₁ : n = 1
    · subst n; rfl
    · by_cases h₂ : n = 2
      · subst n; rfl
      · simp [degreeMap, h₀, h₁, h₂]

/-- 元のd⁰/d¹を標準短複体へ置く。Cの既存H¹とhomology APIの橋。 -/
def oldShort (C : ThreeCochainComplex.{0,w} ℚ) : ShortComplex (ModuleCat.{w} ℚ) :=
  ShortComplex.moduleCatMk C.d0 C.d1 (by ext x; exact C.d1_comp_d0 x)

/-- 零延長の次数1短複体を元の二微分の短複体へ同定する。 -/
def zeroExtensionScIso (C : ThreeCochainComplex.{0,w} ℚ) :
    (zeroExtension C).sc (1 : ℤ) ≅ oldShort C :=
  (zeroExtension C).isoSc' (i := 0) (j := 1) (k := 2) (by simp) (by simp) ≪≫
    eqToIso (by rfl)

/-- 既存H¹商と零延長の標準次数1 homologyの両方向同型。 -/
def oldH1Iso (C : ThreeCochainComplex.{0,w} ℚ) :
    ModuleCat.of ℚ C.H1 ≅ (zeroExtension C).homology (1 : ℤ) :=
  (oldShort C).moduleCatHomologyIso.symm ≪≫
    (ShortComplex.homologyMapIso (zeroExtensionScIso C)).symm

/-- 元のHom三成分から二微分の短複体射を生成する。 -/
def oldShortMap (f : ThreeCochainComplex.Hom C D) : oldShort C ⟶ oldShort D where
  τ₁ := ModuleCat.ofHom f.f0
  τ₂ := ModuleCat.ofHom f.f1
  τ₃ := ModuleCat.ofHom f.f2
  comm₁₂ := by apply ModuleCat.hom_ext; ext x; exact (f.comm0 x).symm
  comm₂₃ := by apply ModuleCat.hom_ext; ext x; exact (f.comm1 x).symm

/-- 既存cyclesMap/h1Mapから標準LeftHomologyMapDataの全可換条件を証明する。 -/
def oldShortMapData (f : ThreeCochainComplex.Hom C D) :
    ShortComplex.LeftHomologyMapData (oldShortMap f)
      (oldShort C).moduleCatLeftHomologyData (oldShort D).moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom f.cyclesMap
  φH := ModuleCat.ofHom f.h1Map
  commi := rfl
  commf' := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact f.comm0 x
  commπ := by
    apply ModuleCat.hom_ext
    ext z
    exact f.h1Map_mk z

/-- 既存H¹比較と標準短複体homology mapの自然性。 -/
theorem oldShortMap_homology (f : ThreeCochainComplex.Hom C D) :
    (oldShort C).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap (oldShortMap f) =
      ModuleCat.ofHom f.h1Map ≫ (oldShort D).moduleCatHomologyIso.inv := by
  rw [(oldShortMapData f).homologyMap_eq]
  simp [ShortComplex.moduleCatHomologyIso, oldShortMapData]

/-- 零延長の次数別同定は全Homと可換である。 -/
theorem zeroExtensionScIso_natural (f : ThreeCochainComplex.Hom C D) :
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) 1).map
      (zeroExtensionMap f)) ≫ (zeroExtensionScIso D).hom =
    (zeroExtensionScIso C).hom ≫ oldShortMap f := by
  change _ ≫ ((HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
    (ComplexShape.up ℤ) 0 1 2 (by simp) (by simp)).hom.app (zeroExtension D)) =
    ((HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) 0 1 2 (by simp) (by simp)).hom.app (zeroExtension C)) ≫ _
  exact (HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
    (ComplexShape.up ℤ) 0 1 2 (by simp) (by simp)).hom.naturality (zeroExtensionMap f)

/-- Cの既存H¹自然同型は任意Homの実商写像と標準homology mapを結ぶ。 -/
theorem oldH1Iso_natural (f : ThreeCochainComplex.Hom C D) :
    (oldH1Iso C).hom ≫ HomologicalComplex.homologyMap (zeroExtensionMap f) 1 =
      ModuleCat.ofHom f.h1Map ≫ (oldH1Iso D).hom := by
  have h := congrArg (fun φ : (zeroExtension C).sc (1 : ℤ) ⟶ oldShort D =>
    ShortComplex.homologyMap φ) (zeroExtensionScIso_natural f)
  simp only [ShortComplex.homologyMap_comp] at h
  let eC := ShortComplex.homologyMapIso (zeroExtensionScIso C)
  let eD := ShortComplex.homologyMapIso (zeroExtensionScIso D)
  have he : eC.inv ≫ HomologicalComplex.homologyMap (zeroExtensionMap f) 1 =
      ShortComplex.homologyMap (oldShortMap f) ≫ eD.inv := by
    rw [← cancel_mono eD.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change eC.inv ≫ (HomologicalComplex.homologyMap (zeroExtensionMap f) 1 ≫ eD.hom) = _
    rw [show HomologicalComplex.homologyMap (zeroExtensionMap f) 1 ≫ eD.hom =
      eC.hom ≫ ShortComplex.homologyMap (oldShortMap f) from h]
    simp
  change ((oldShort C).moduleCatHomologyIso.inv ≫ eC.inv) ≫ _ =
    ModuleCat.ofHom f.h1Map ≫ ((oldShort D).moduleCatHomologyIso.inv ≫ eD.inv)
  rw [Category.assoc, he, ← Category.assoc, oldShortMap_homology, Category.assoc]

/-- 零延長の全次数は元の有限次元加群または明示零加群である。 -/
instance degreeObjectFiniteDimensional (C : ThreeCochainComplex.{0,w} ℚ) (n : ℤ) :
    FiniteDimensional ℚ (degreeObject C n) := by
  classical
  by_cases h₀ : n = 0
  · subst n; change FiniteDimensional ℚ C.C0; infer_instance
  · by_cases h₁ : n = 1
    · subst n; change FiniteDimensional ℚ C.C1; infer_instance
    · by_cases h₂ : n = 2
      · subst n; change FiniteDimensional ℚ C.C2; infer_instance
      · have he : degreeObject C n = ModuleCat.of ℚ (PUnit.{w+1}) := by
          simp [degreeObject, h₀, h₁, h₂]
        exact FiniteDimensional.of_injective (eqToIso he).toLinearEquiv.toLinearMap
          (eqToIso he).toLinearEquiv.injective

/-- 零延長の各次数の対象を読む公開API。 -/
@[simp] theorem zeroExtension_X (C : ThreeCochainComplex.{0,w} ℚ) (n : ℤ) :
    (zeroExtension C).X n = degreeObject C n := rfl

/-- 三つの元の次数を外れた零延長対象は標準圏でも零対象である。 -/
theorem degreeObject_isZero (C : ThreeCochainComplex.{0,w} ℚ) (n : ℤ)
    (h₀ : n ≠ 0) (h₁ : n ≠ 1) (h₂ : n ≠ 2) : IsZero (degreeObject C n) := by
  simp only [degreeObject, if_neg h₀, if_neg h₁, if_neg h₂]
  exact ModuleCat.isZero_of_subsingleton _

/-- 零延長の隣接微分は元の次数別射で評価される。 -/
@[simp] theorem zeroExtension_d (C : ThreeCochainComplex.{0,w} ℚ) (n : ℤ) :
    (zeroExtension C).d n (n+1) = degreeDifferential C n :=
  CochainComplex.of_d _ _ _ _

/-- 零延長Homの全次数の計算成分を読む公開API。 -/
@[simp] theorem zeroExtensionMap_f (f : ThreeCochainComplex.Hom C D) (n : ℤ) :
    (zeroExtensionMap f).f n = degreeMap f n := rfl

/-- 恒等Homの零延長は標準complexの恒等射と一致する。 -/
theorem zeroExtensionMap_id (C : ThreeCochainComplex.{0,w} ℚ) :
    zeroExtensionMap (cochainId C) = 𝟙 (zeroExtension C) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degreeMap (cochainId C) n = 𝟙 (degreeObject C n)
  by_cases h₀ : n = 0
  · subst n; rfl
  · by_cases h₁ : n = 1
    · subst n; rfl
    · by_cases h₂ : n = 2
      · subst n; rfl
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simp only [degreeMap, dif_neg h₀, dif_neg h₁, dif_neg h₂,
          ModuleCat.hom_zero, LinearMap.zero_apply, ModuleCat.hom_id, LinearMap.id_apply]
        have : Subsingleton (degreeObject C n) := by
          simp only [degreeObject, if_neg h₀, if_neg h₁, if_neg h₂]
          infer_instance
        exact Subsingleton.elim _ _

/-- Cの既存H¹商を標準homologyへ移す線形同型。 -/
def oldH1Equiv (C : ThreeCochainComplex.{0,w} ℚ) :
    C.H1 ≃ₗ[ℚ] (zeroExtension C).homology (1 : ℤ) := (oldH1Iso C).toLinearEquiv

/-- H¹線形同型は全Homの全実商類において標準homology mapと可換である。 -/
theorem oldH1Equiv_natural (f : ThreeCochainComplex.Hom C D) (x : C.H1) :
    oldH1Equiv D (f.h1Map x) =
      HomologicalComplex.homologyMap (zeroExtensionMap f) 1 (oldH1Equiv C x) := by
  exact (congrArg (fun h : ModuleCat.of ℚ C.H1 ⟶ (zeroExtension D).homology 1 => h x)
    (oldH1Iso_natural f)).symm

/-- 零延長の標準complex対象の各次数は有限次元である。 -/
instance zeroExtensionDegreeFiniteDimensional (C : ThreeCochainComplex.{0,w} ℚ) (n : ℤ) :
    FiniteDimensional ℚ ((zeroExtension C).X n) := by
  rw [zeroExtension_X]
  infer_instance

/-- 元の三項次数外では標準homologyも零対象である。 -/
theorem zeroExtension_homology_isZero (C : ThreeCochainComplex.{0,w} ℚ) (n : ℤ)
    (h₀ : n ≠ 0) (h₁ : n ≠ 1) (h₂ : n ≠ 2) :
    IsZero ((zeroExtension C).homology n) :=
  ((zeroExtension C).sc n).isZero_homology_of_isZero_X₂
    (degreeObject_isZero C n h₀ h₁ h₂)

/-- 短複体同定の可換正方形からhomology同定の自然性を導く汎用API。 -/
theorem homologyTransport_natural
    {K L : CochainComplex (ModuleCat.{w} ℚ) ℤ} (φ : K ⟶ L) (m : ℤ)
    {S T : ShortComplex (ModuleCat.{w} ℚ)} (eK : K.sc m ≅ S) (eL : L.sc m ≅ T)
    (ψ : S ⟶ T)
    (comm : ((HomologicalComplex.shortComplexFunctor (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) m).map φ) ≫ eL.hom = eK.hom ≫ ψ) :
    (ShortComplex.homologyMapIso eK).inv ≫ HomologicalComplex.homologyMap φ m =
      ShortComplex.homologyMap ψ ≫ (ShortComplex.homologyMapIso eL).inv := by
  have h := congrArg (fun f : K.sc m ⟶ T => ShortComplex.homologyMap f) comm
  simp only [ShortComplex.homologyMap_comp] at h
  rw [← cancel_mono (ShortComplex.homologyMapIso eL).hom]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [show HomologicalComplex.homologyMap φ m ≫ (ShortComplex.homologyMapIso eL).hom =
    (ShortComplex.homologyMapIso eK).hom ≫ ShortComplex.homologyMap ψ from h]
  change ShortComplex.homologyMap eK.inv ≫ ShortComplex.homologyMap eK.hom ≫
    ShortComplex.homologyMap ψ = _
  rw [← Category.assoc,← ShortComplex.homologyMap_comp,eK.inv_hom_id,
    ShortComplex.homologyMap_id,Category.id_comp]

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
