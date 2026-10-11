import ResearchLean.AG.AtlasGluingWidth.PrimitiveGluing
import ResearchLean.AG.AtlasCoefficientFiber.DefectDiagnostics
import Formal.Util.AssertStandardAxioms
/-! # 同じ通常領域の実欠損と係数・fiber分解

GOAL D／設計exact-sequence §5。任意Xの元の旧H¹核商からG135の同じdirectH1へ
射と全代表元を保持して同定する。合併UではCと係数側の両SESの中間項を同じ実商に置く。
Implementation notes: G135 directH1_oldと実係数余核SESを使う。同次元モデルの選択と
二つのSESの両端を相互同型にする案は元の射を失うため退けた。真の交差IへG135を適用しない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.CoefficientBridge
open AAT.AG.CanonicalResolution AAT.AG.ResolutionInvariance AAT.AG.TwoPhase
open AAT.AG.AtlasDefectComposition AAT.AG.AtlasCoefficientFiber
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison qc qf h Nc Nf)
/-- 同じ通常Xの旧実phantomからG135の独立directH1核への同型。 -/
def phantomEquiv (X : Set qc.Target) : LinearMap.ker (M.aSubnerveComparisonHom X).h1Map ≃ₗ[ℚ]
    LinearMap.ker (directH1 M X) :=
  LinearConjugation.kernelEquiv _ _ (oldH1Equiv _) (oldH1Equiv _)
    (fun x => (directH1_old M X x).symm)
/-- 同じ通常Xの旧実hiddenからG135の独立directH1余核への同型。 -/
def hiddenEquiv (X : Set qc.Target) :
    ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' X)).H1 ⧸
      LinearMap.range (M.aSubnerveComparisonHom X).h1Map) ≃ₗ[ℚ]
    ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' X))).homology (1:ℤ) ⧸
      LinearMap.range (directH1 M X)) :=
  LinearConjugation.cokernelEquiv _ _ (oldH1Equiv _) (oldH1Equiv _)
    (fun x => (directH1_old M X x).symm)
/-- phantom同定は同じ旧粗H¹ classを標準H¹へ移す。 -/
@[simp] theorem phantomEquiv_val (X : Set qc.Target)
    (x : LinearMap.ker (M.aSubnerveComparisonHom X).h1Map) :
    (phantomEquiv M X x).val = oldH1Equiv (Nc.targetSubsetComplex X) x.val := rfl
/-- hidden同定は同じ旧細H¹の全商代表元を移す。 -/
@[simp] theorem hiddenEquiv_mk (X : Set qc.Target)
    (y : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' X)).H1) :
    hiddenEquiv M X ((LinearMap.range (M.aSubnerveComparisonHom X).h1Map).mkQ y) =
      (LinearMap.range (directH1 M X)).mkQ (oldH1Equiv _ y) := rfl
/-- 逆hidden同定も同じ細標準H¹代表元を旧H¹へ戻す。 -/
@[simp] theorem hiddenEquiv_symm_mk (X : Set qc.Target)
    (y : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' X))).homology (1:ℤ)) :
    (hiddenEquiv M X).symm ((LinearMap.range (directH1 M X)).mkQ y) =
      (LinearMap.range (M.aSubnerveComparisonHom X).h1Map).mkQ ((oldH1Equiv _).symm y) := by
  apply (hiddenEquiv M X).injective
  rw [LinearEquiv.apply_symm_apply,hiddenEquiv_mk,LinearEquiv.apply_symm_apply]
/-- 同じ旧phantomは原係数unitH1核へ元を保持して接続する。 -/
def phantomUnitEquiv (X : Set qc.Target) : LinearMap.ker (M.aSubnerveComparisonHom X).h1Map ≃ₗ[ℚ]
    LinearMap.ker (unitH1 M X) :=
  (phantomEquiv M X).trans (directKernelUnitEquiv M X)
/-- 原係数核への同定は同じ粗旧classを読む。 -/
@[simp] theorem phantomUnitEquiv_val (X : Set qc.Target)
    (x : LinearMap.ker (M.aSubnerveComparisonHom X).h1Map) :
    (phantomUnitEquiv M X x).val = oldH1Equiv (Nc.targetSubsetComplex X) x.val := rfl
/-- G135の同じ実係数包含・fiber射を持つ標準短複体。 -/
def coefficientRow (X : Set qc.Target) : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.moduleCatMk (X₃ := LinearMap.ker (connectingTau M X)) (coefficientCokernelInclusion M X) (totalCokernelFiberProjection M X) (by
    apply LinearMap.ext
    intro x
    exact (coefficientCokernel_exact M X (coefficientCokernelInclusion M X x)).mpr ⟨x,rfl⟩)
/-- 原始MからのG135受理定理を同じ実係数SESへ接続する。 -/
theorem coefficientRow_shortExact (X : Set qc.Target) : (coefficientRow M X).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (coefficientCokernel_exact M X)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (coefficientCokernelInclusion_injective M X)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (totalCokernelFiberProjection_surjective M X)
/-- 通常Xの元の旧実hiddenを中間項に置く同じ係数SES。 -/
def oldCoefficientRow (X : Set qc.Target) : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.mk ((coefficientRow M X).f ≫ (hiddenEquiv M X).symm.toModuleIso.hom)
    ((hiddenEquiv M X).toModuleIso.hom ≫ (coefficientRow M X).g) (by
      rw [Category.assoc,← Category.assoc (hiddenEquiv M X).symm.toModuleIso.hom,
        show (hiddenEquiv M X).symm.toModuleIso.hom ≫ (hiddenEquiv M X).toModuleIso.hom = 𝟙 _ from
          (hiddenEquiv M X).toModuleIso.inv_hom_id,Category.id_comp]
      exact (coefficientRow M X).zero)
/-- 両端を固定し、元の実hiddenに中間項を輸送する短複体同型。 -/
def oldCoefficientRowIso (X : Set qc.Target) : coefficientRow M X ≅ oldCoefficientRow M X :=
  ShortComplex.isoMk (Iso.refl _) (hiddenEquiv M X).symm.toModuleIso (Iso.refl _)
    (by simp only [oldCoefficientRow,Iso.refl_hom,Category.id_comp])
    (by simp only [oldCoefficientRow,Iso.refl_hom,Category.comp_id,← Category.assoc,
      show (hiddenEquiv M X).symm.toModuleIso.hom ≫ (hiddenEquiv M X).toModuleIso.hom = 𝟙 _ from
        (hiddenEquiv M X).toModuleIso.inv_hom_id]
        erw [Category.id_comp])
/-- 任意通常Xの同じ旧実hiddenを持つ係数・fiber短完全列。 -/
theorem oldCoefficientRow_shortExact (X : Set qc.Target) : (oldCoefficientRow M X).ShortExact :=
  ShortComplex.shortExact_of_iso (oldCoefficientRowIso M X) (coefficientRow_shortExact M X)
/-- 原係数余核の包含は同じ実evaluationH1の商類を旧hiddenへ送る。 -/
theorem oldCoefficientRow_f_mk (X : Set qc.Target)
    (x : (zeroExtension (pushforwardComplex M X)).homology (1:ℤ)) :
    (oldCoefficientRow M X).f ((LinearMap.range (unitH1 M X)).mkQ x) =
      (LinearMap.range (M.aSubnerveComparisonHom X).h1Map).mkQ
        ((oldH1Equiv _).symm (evaluationH1 M X x)) := by
  change (hiddenEquiv M X).symm (coefficientCokernelInclusion M X _) = _
  have hi : coefficientCokernelInclusion M X ((LinearMap.range (unitH1 M X)).mkQ x) =
      (LinearMap.range (directH1 M X)).mkQ (evaluationH1 M X x) :=
    coefficientCokernelInclusion_mk M X x
  rw [hi,hiddenEquiv_symm_mk]
/-- 旧hiddenからkerτへの射は同じ実fine標準H¹の原fiber制限を読む。 -/
theorem oldCoefficientRow_g_mk_val (X : Set qc.Target)
    (y : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' X)).H1) :
    ((oldCoefficientRow M X).g ((LinearMap.range (M.aSubnerveComparisonHom X).h1Map).mkQ y)).val =
      fiberRestrictionH1 M X (oldH1Equiv _ y) := by
  change (totalCokernelFiberProjection M X (hiddenEquiv M X _)).val = _
  rw [hiddenEquiv_mk]
  exact totalCokernelFiberProjection_mk_val M X _
/-- Cと係数・fiber方向のSESは同じ通常Uのliteral hiddenを中間項に持つ。 -/
theorem union_hidden_same (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    (oldCoefficientRow M (A ∪ B)).X₂ = (PrimitiveGluing.oldHiddenRow M A B hA hB).X₂ := rfl
/-- Cのq/Z判定とG135のunit/τ判定は同じ通常UのJ零を介して両方向で一致する。 -/
theorem union_zero_iff (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    (Function.Bijective (QuotientKernelRow.q (PrimitiveGluing.coarseRow (Nc := Nc) A B)
        (PrimitiveGluing.comparison M A B)) ∧
      QuotientKernelRow.Z (PrimitiveGluing.coarseRow (Nc := Nc) A B) (PrimitiveGluing.comparison M A B) = ⊥) ↔
      (Function.Bijective (unitH1 M (A ∪ B)) ∧ Function.Injective (connectingTau M (A ∪ B))) :=
  (PrimitiveGluing.defect_zero_iff M A B hA hB).symm.trans (coefficient_zeroDefect_iff M (A ∪ B))
end AAT.AG.AtlasGluingWidth.CoefficientBridge
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.CoefficientBridge
