import ResearchLean.AG.AtlasCoefficientFiber.PositiveOperationPath
import ResearchLean.AG.FaceRelationSubdivision.OperationPathDiagnostics

/-!
# 原始正部分比較の保存と既存G134出力

Implementation notes: 同じG134列の逆有限和・両補正を保ち、順射の全Hom等号で
元部分比較と元Law比較へ接続する。全錐消滅は同じ原始ホモトピー同値から導く。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AAT.AG.AtlasCoefficientFiber.PositiveOperationPath
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (path : PositiveOperationPath qc Nc qf Nf)

/-- 同じ全Aの原始G134 r/sと二補正から標準同値を得る。 -/
def subsetHomotopyEquiv (A : Set qc.Target) := path.toPrimitive.subsetHomotopyEquiv A
/-- 順射は独立に生成した同じ元aSubnerve全Hom。 -/
theorem subsetHomotopyEquiv_hom (A : Set qc.Target) :
    (path.subsetHomotopyEquiv A).hom = zeroExtensionMap (path.comparison.aSubnerveComparisonHom A) := by
  change (path.toPrimitive.subsetHomotopyEquiv A).hom = _
  rw [PrimitiveOperationPath.subsetHomotopyEquiv_hom, path.subsetR_eq_generated]
/-- 逆射は同じ原始有限和sの全Hom。 -/
theorem subsetHomotopyEquiv_inv (A : Set qc.Target) :
    (path.subsetHomotopyEquiv A).inv = zeroExtensionMap (path.toPrimitive.subsetS A) :=
  path.toPrimitive.subsetHomotopyEquiv_inv A

/-- 同じ元比較の全整数次数同型。 -/
def subsetHomologyIso (A : Set qc.Target) (n : ℤ) := path.toPrimitive.subsetHomologyIso A n
/-- 全次数同型の順射は同じ独立生成比較。 -/
theorem subsetHomologyIso_hom (A : Set qc.Target) (n : ℤ) :
    (path.subsetHomologyIso A n).hom =
      HomologicalComplex.homologyMap (zeroExtensionMap (path.comparison.aSubnerveComparisonHom A)) n := by
  change (path.toPrimitive.subsetHomologyIso A n).hom = _
  rw [PrimitiveOperationPath.subsetHomologyIso_hom, path.subsetR_eq_generated]
/-- 全次数同型の逆射は同じG134有限和s。 -/
theorem subsetHomologyIso_inv (A : Set qc.Target) (n : ℤ) :
    (path.subsetHomologyIso A n).inv =
      HomologicalComplex.homologyMap (zeroExtensionMap (path.toPrimitive.subsetS A)) n :=
  path.toPrimitive.subsetHomologyIso_inv A n

/-- 同じ実比較の旧H1商同型は同じG134商同型。 -/
def subsetOldH1Iso (A : Set qc.Target) := path.toPrimitive.subsetOldH1Iso A
/-- 商同型の順射は同じ独立aSubnerve比較。 -/
theorem subsetOldH1Iso_hom (A : Set qc.Target) :
    (path.subsetOldH1Iso A).hom = ModuleCat.ofHom (path.comparison.aSubnerveComparisonHom A).h1Map := by
  change (path.toPrimitive.subsetOldH1Iso A).hom = _
  rw [PrimitiveOperationPath.subsetOldH1Iso_hom, path.subsetR_eq_generated]
/-- 商同型の逆射も同じ生成有限和。 -/
theorem subsetOldH1Iso_inv (A : Set qc.Target) :
    (path.subsetOldH1Iso A).inv = ModuleCat.ofHom (path.toPrimitive.subsetS A).h1Map :=
  path.toPrimitive.subsetOldH1Iso_inv A

/-- 全Aの元実H1比較は両方向全単射。 -/
theorem subsetH1_bijective (A : Set qc.Target) :
    Function.Bijective (path.comparison.aSubnerveComparisonHom A).h1Map := by
  rw [← path.subsetR_eq_generated]
  exact path.toPrimitive.subsetH1_bijective A
/-- 全Aの同じ既存blockDefectは二成分とも零。 -/
theorem subsetDefect_zero (A : Set qc.Target) :
    blockDefect (path.comparison.aSubnerveComparisonHom A).h1Map = (0,0) := by
  rw [← path.subsetR_eq_generated]
  exact path.toPrimitive.subsetDefect_zero A
/-- 元独立比較の標準錐は全整数次数で零。 -/
theorem subsetCone_isZero (A : Set qc.Target) (n : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (path.comparison.aSubnerveComparisonHom A))).homology n) := by
  rw [← path.subsetR_eq_generated]
  exact path.toPrimitive.subsetCone_isZero A n

variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 全Lawの同じ原始G134 r/sと両補正を保つ標準同値。 -/
def lawHomotopyEquiv := path.toPrimitive.lawHomotopyEquiv laws ha
/-- Law順射は元独立generatedComparisonHom。 -/
theorem lawHomotopyEquiv_hom : (path.lawHomotopyEquiv laws ha).hom =
    zeroExtensionMap (path.comparison.generatedComparisonHom laws ha (adequate_of_coarser laws path.coarser ha)) := by
  change (path.toPrimitive.lawHomotopyEquiv laws ha).hom = _
  rw [PrimitiveOperationPath.lawHomotopyEquiv_hom, path.lawR_eq_generated]
/-- Law逆射は同じ原始G134 s有限和。 -/
theorem lawHomotopyEquiv_inv : (path.lawHomotopyEquiv laws ha).inv =
    zeroExtensionMap (path.toPrimitive.lawS laws ha) := path.toPrimitive.lawHomotopyEquiv_inv laws ha

/-- 原Law独立比較の全整数次数同型。 -/
def lawHomologyIso (n : ℤ) := path.toPrimitive.lawHomologyIso laws ha n
/-- Law同型の全次数順射は同じ元比較。 -/
theorem lawHomologyIso_hom (n : ℤ) : (path.lawHomologyIso laws ha n).hom =
    HomologicalComplex.homologyMap (zeroExtensionMap
      (path.comparison.generatedComparisonHom laws ha (adequate_of_coarser laws path.coarser ha))) n := by
  change (path.toPrimitive.lawHomologyIso laws ha n).hom = _
  rw [PrimitiveOperationPath.lawHomologyIso_hom, path.lawR_eq_generated]
/-- Law同型の全次数逆射は同じ元有限和。 -/
theorem lawHomologyIso_inv (n : ℤ) : (path.lawHomologyIso laws ha n).inv =
    HomologicalComplex.homologyMap (zeroExtensionMap (path.toPrimitive.lawS laws ha)) n :=
  path.toPrimitive.lawHomologyIso_inv laws ha n

/-- 同じ実Law比較の旧H1商同型。 -/
def lawOldH1Iso := path.toPrimitive.lawOldH1Iso laws ha
/-- 旧Law商の順射は同じ元独立比較。 -/
theorem lawOldH1Iso_hom : (path.lawOldH1Iso laws ha).hom =
    ModuleCat.ofHom (path.comparison.generatedComparisonHom laws ha (adequate_of_coarser laws path.coarser ha)).h1Map := by
  change (path.toPrimitive.lawOldH1Iso laws ha).hom = _
  rw [PrimitiveOperationPath.lawOldH1Iso_hom, path.lawR_eq_generated]
/-- 旧Law商の逆射は同じ原始有限和。 -/
theorem lawOldH1Iso_inv : (path.lawOldH1Iso laws ha).inv =
    ModuleCat.ofHom (path.toPrimitive.lawS laws ha).h1Map := path.toPrimitive.lawOldH1Iso_inv laws ha
/-- 任意粗adequate Lawの元実比較はH1全単射。 -/
theorem lawH1_bijective : Function.Bijective
    (path.comparison.generatedComparisonHom laws ha (adequate_of_coarser laws path.coarser ha)).h1Map := by
  rw [← path.lawR_eq_generated]
  exact path.toPrimitive.lawH1_bijective laws ha
/-- 同じ実Lawの元blockDefectは零。 -/
theorem lawDefect_zero : blockDefect
    (path.comparison.generatedComparisonHom laws ha (adequate_of_coarser laws path.coarser ha)).h1Map = (0,0) := by
  rw [← path.lawR_eq_generated]
  exact path.toPrimitive.lawDefect_zero laws ha
/-- 同じ元Law標準錐は全整数次数で零。 -/
theorem lawCone_isZero (n : ℤ) : IsZero ((mappingCone (zeroExtensionMap
    (path.comparison.generatedComparisonHom laws ha (adequate_of_coarser laws path.coarser ha)))).homology n) := by
  rw [← path.lawR_eq_generated]
  exact path.toPrimitive.lawCone_isZero laws ha n

end AAT.AG.AtlasCoefficientFiber.PositiveOperationPath
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetHomotopyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetHomotopyEquiv_hom
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetHomotopyEquiv_inv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetHomologyIso
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetHomologyIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetHomologyIso_inv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetOldH1Iso
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetOldH1Iso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetOldH1Iso_inv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetH1_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetDefect_zero
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetCone_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawHomotopyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawHomotopyEquiv_hom
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawHomotopyEquiv_inv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawHomologyIso
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawHomologyIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawHomologyIso_inv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawOldH1Iso
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawOldH1Iso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawOldH1Iso_inv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawH1_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawDefect_zero
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawCone_isZero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.PositiveOperationPath
