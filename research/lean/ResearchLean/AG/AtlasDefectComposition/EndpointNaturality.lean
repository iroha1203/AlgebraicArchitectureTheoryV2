import ResearchLean.AG.AtlasDefectComposition.EndpointHomology
import Formal.Util.AssertStandardAxioms
/-! # 三項端homologyの比較自然性

元の次数0核・次数2余核上の実Homを標準homology mapへ接続する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open TwoPhase
universe w
variable {C D : ThreeCochainComplex.{0,w} ℚ} (f : ThreeCochainComplex.Hom C D)
/-- 元のHomの次数0成分が誘導するd⁰核の実射。 -/
def oldH0Map : LinearMap.ker C.d0 →ₗ[ℚ] LinearMap.ker D.d0 :=
  (f.f0.comp (LinearMap.ker C.d0).subtype).codRestrict _ (by
    intro x
    change D.d0 (f.f0 x.val) = 0
    rw [← f.comm0,x.property,map_zero])
/-- 元のHomの次数2成分が誘導するd¹像の実商射。 -/
def oldH2Map : (C.C2 ⧸ LinearMap.range C.d1) →ₗ[ℚ] (D.C2 ⧸ LinearMap.range D.d1) :=
  (LinearMap.range C.d1).mapQ _ f.f2 (by
    rintro x ⟨y,rfl⟩
    exact ⟨f.f1 y,(f.comm1 y).symm⟩)
/-- 次数0核射は元のHomの次数0成分で評価される。 -/
@[simp] theorem oldH0Map_val (x : LinearMap.ker C.d0) : (oldH0Map f x).val = f.f0 x.val := rfl
/-- 次数2商射は元のHomの次数2成分で代表元を写す。 -/
@[simp] theorem oldH2Map_mk (x : C.C2) :
    oldH2Map f ((LinearMap.range C.d1).mkQ x) = (LinearMap.range D.d1).mkQ (f.f2 x) := rfl
/-- 元のHomを次数0端短複体へ移す。 -/
def oldZeroShortMap : oldZeroShort C ⟶ oldZeroShort D where
  τ₁ := 0
  τ₂ := ModuleCat.ofHom f.f0
  τ₃ := ModuleCat.ofHom f.f1
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (0 : D.C0) = f.f0 0
    exact f.f0.map_zero.symm
  comm₂₃ := by apply ModuleCat.hom_ext; ext x; exact (f.comm0 x).symm
/-- 元のHomを次数2端短複体へ移す。 -/
def oldTwoShortMap : oldTwoShort C ⟶ oldTwoShort D where
  τ₁ := ModuleCat.ofHom f.f1
  τ₂ := ModuleCat.ofHom f.f2
  τ₃ := 0
  comm₁₂ := by apply ModuleCat.hom_ext; ext x; exact (f.comm1 x).symm
  comm₂₃ := by apply ModuleCat.hom_ext; ext x; simp [oldTwoShort]
/-- 次数0端短複体同定は実Homと可換である。 -/
theorem zeroExtensionZeroScIso_natural :
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) 0).map
      (zeroExtensionMap f)) ≫ (zeroExtensionZeroScIso D).hom =
    (zeroExtensionZeroScIso C).hom ≫ oldZeroShortMap f := by
  change _ ≫ ((HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
    (ComplexShape.up ℤ) (-1) 0 1 (by simp) (by simp)).hom.app (zeroExtension D)) =
    ((HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) (-1) 0 1 (by simp) (by simp)).hom.app (zeroExtension C)) ≫ _
  exact (HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
    (ComplexShape.up ℤ) (-1) 0 1 (by simp) (by simp)).hom.naturality (zeroExtensionMap f)
/-- 次数2端短複体同定は実Homと可換である。 -/
theorem zeroExtensionTwoScIso_natural :
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) 2).map
      (zeroExtensionMap f)) ≫ (zeroExtensionTwoScIso D).hom =
    (zeroExtensionTwoScIso C).hom ≫ oldTwoShortMap f := by
  change _ ≫ ((HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
    (ComplexShape.up ℤ) 1 2 3 (by simp) (by simp)).hom.app (zeroExtension D)) =
    ((HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) 1 2 3 (by simp) (by simp)).hom.app (zeroExtension C)) ≫ _
  exact (HomologicalComplex.natIsoSc' (ModuleCat.{w} ℚ)
    (ComplexShape.up ℤ) 1 2 3 (by simp) (by simp)).hom.naturality (zeroExtensionMap f)
/-- 次数0端の実核同定は標準cycles mapと可換である。 -/
theorem oldZeroCycles_natural :
    (oldZeroShort C).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (oldZeroShortMap f) =
      ModuleCat.ofHom (oldH0Map f) ≫ (oldZeroShort D).moduleCatCyclesIso.inv := by
  rw [← cancel_mono (oldZeroShort D).iCycles]
  simp only [Category.assoc,ShortComplex.cyclesMap_i,
    ShortComplex.moduleCatCyclesIso_inv_iCycles,ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
  rfl
/-- 次数2端の実商同定は標準opcycles mapと可換である。 -/
theorem oldTwoOpcycles_natural :
    (oldTwoShort C).moduleCatOpcyclesIso.inv ≫ ShortComplex.opcyclesMap (oldTwoShortMap f) =
      ModuleCat.ofHom (oldH2Map f) ≫ (oldTwoShort D).moduleCatOpcyclesIso.inv := by
  have hp : ShortComplex.opcyclesMap (oldTwoShortMap f) ≫
      (oldTwoShort D).moduleCatOpcyclesIso.hom =
      (oldTwoShort C).moduleCatOpcyclesIso.hom ≫ ModuleCat.ofHom (oldH2Map f) := by
    apply (cancel_epi (oldTwoShort C).pOpcycles).mp
    simp only [← Category.assoc,ShortComplex.p_opcyclesMap]
    simp only [Category.assoc,ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  rw [← cancel_mono (oldTwoShort D).moduleCatOpcyclesIso.hom]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,hp]
  simp
/-- 元のH⁰核同型は全Homについて標準H⁰比較と可換である。 -/
theorem oldH0Iso_natural :
    (oldH0Iso C).hom ≫ HomologicalComplex.homologyMap (zeroExtensionMap f) 0 =
      ModuleCat.ofHom (oldH0Map f) ≫ (oldH0Iso D).hom := by
  have he := homologyTransport_natural (zeroExtensionMap f) 0
    (zeroExtensionZeroScIso C) (zeroExtensionZeroScIso D) (oldZeroShortMap f)
    (zeroExtensionZeroScIso_natural f)
  simp only [oldH0Iso,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [he]
  change _ ≫ (oldZeroShort C).homologyπ ≫ _ ≫ _ = _
  rw [ShortComplex.homologyπ_naturality_assoc,← Category.assoc,
    oldZeroCycles_natural,Category.assoc]
  rfl
/-- 元のH²商同型は全Homについて標準H²比較と可換である。 -/
theorem oldH2Iso_natural :
    (oldH2Iso C).hom ≫ HomologicalComplex.homologyMap (zeroExtensionMap f) 2 =
      ModuleCat.ofHom (oldH2Map f) ≫ (oldH2Iso D).hom := by
  have he := homologyTransport_natural (zeroExtensionMap f) 2
    (zeroExtensionTwoScIso C) (zeroExtensionTwoScIso D) (oldTwoShortMap f)
    (zeroExtensionTwoScIso_natural f)
  simp only [oldH2Iso,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [he]
  have hs : (oldTwoShort C).moduleCatOpcyclesIso.inv ≫
      ((oldTwoShort C).asIsoHomologyι (by rfl)).inv ≫
      ShortComplex.homologyMap (oldTwoShortMap f) =
      ModuleCat.ofHom (oldH2Map f) ≫ (oldTwoShort D).moduleCatOpcyclesIso.inv ≫
      ((oldTwoShort D).asIsoHomologyι (by rfl)).inv := by
    rw [← cancel_mono ((oldTwoShort D).asIsoHomologyι (by rfl)).hom]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    change _ ≫ _ ≫ (ShortComplex.homologyMap (oldTwoShortMap f) ≫ (oldTwoShort D).homologyι) = _
    rw [ShortComplex.homologyι_naturality]
    change _ ≫ ((oldTwoShort C).asIsoHomologyι (by rfl)).inv ≫
      ((oldTwoShort C).asIsoHomologyι (by rfl)).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc,oldTwoOpcycles_natural]
  simpa only [Category.assoc] using congrArg (fun t =>
    t ≫ (ShortComplex.homologyMapIso (zeroExtensionTwoScIso D)).inv) hs
/-- H⁰の自然性を全実核元で読む公開API。 -/
theorem oldH0Equiv_natural (x : LinearMap.ker C.d0) :
    oldH0Equiv D (oldH0Map f x) =
      HomologicalComplex.homologyMap (zeroExtensionMap f) 0 (oldH0Equiv C x) :=
  (congrArg (fun h : ModuleCat.of ℚ (LinearMap.ker C.d0) ⟶ (zeroExtension D).homology 0 => h x)
    (oldH0Iso_natural f)).symm
/-- H²の自然性を全実終端商元で読む公開API。 -/
theorem oldH2Equiv_natural (x : C.C2 ⧸ LinearMap.range C.d1) :
    oldH2Equiv D (oldH2Map f x) =
      HomologicalComplex.homologyMap (zeroExtensionMap f) 2 (oldH2Equiv C x) :=
  (congrArg (fun h : ModuleCat.of ℚ (C.C2 ⧸ LinearMap.range C.d1) ⟶ (zeroExtension D).homology 2 => h x)
    (oldH2Iso_natural f)).symm
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
