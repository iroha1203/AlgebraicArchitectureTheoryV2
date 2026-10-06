import ResearchLean.AG.FaceRelationSubdivision.ElementaryBlockHomotopy
import ResearchLean.AG.FaceRelationSubdivision.HomotopyDiagnostics
import Formal.Util.AssertStandardAxioms

/-!
# 正操作の同じ実診断・標準錐

## Implementation notes

入力幾何から構成した二射とホモトピーを標準homologyへ移し、旧商との自然性で
実H1写像を同定する。零欠損は同じ実写像に既存blockDefectを適用する。
錐の零性はG133実短完全列から得て、次元一致だけを根拠とする方法を採らない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}

namespace TriangleAddition
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じ実Law比較と逆有限和sectionによる全整数次数の標準homology同型。 -/
def lawHomologyIso (n : ℤ) := (lawHomotopyEquiv N e laws ha).toHomologyIso n
/-- 同型の順方向は独立生成した同じ実Law r。 -/
@[simp] theorem lawHomologyIso_hom (n : ℤ) :
    (lawHomologyIso N e laws ha n).hom =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawR N e laws ha)) n := rfl
/-- 同型の逆方向も独立生成した同じ実Law s。 -/
@[simp] theorem lawHomologyIso_inv (n : ℤ) :
    (lawHomologyIso N e laws ha n).inv =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawS N e laws ha)) n := rfl

/-- 同じ実Law二射の標準同値を既存H1商へ読み戻す。 -/
def lawOldH1Iso := homotopyOldH1Iso (lawHomotopyEquiv N e laws ha)
/-- 旧H1商同型の射は同じlawR.h1Mapそのもの。 -/
theorem lawOldH1Iso_hom : (lawOldH1Iso N e laws ha).hom =
    ModuleCat.ofHom (lawR N e laws ha).h1Map :=
  homotopyOldH1Iso_hom _ _ (lawHomotopyEquiv_hom N e laws ha)
/-- 旧H1商同型の逆射も同じlawS.h1Mapそのもの。 -/
theorem lawOldH1Iso_inv : (lawOldH1Iso N e laws ha).inv =
    ModuleCat.ofHom (lawS N e laws ha).h1Map :=
  homotopyOldH1Iso_inv _ _ (lawHomotopyEquiv_inv N e laws ha)

/-- 原始正操作から生成した同じLaw H1比較は全単射。 -/
theorem lawH1_bijective : Function.Bijective (lawR N e laws ha).h1Map :=
  homotopyH1_bijective _ _ (lawHomotopyEquiv_hom N e laws ha)
/-- 同じLaw H1比較の実核・実余核の二成分は零。 -/
theorem lawH1_blockDefect_zero : blockDefect (lawR N e laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (lawHomotopyEquiv_hom N e laws ha)
/-- 同じ実Law比較の標準錐は全整数次数のhomologyが零。 -/
theorem lawCone_isZero (m : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (lawR N e laws ha))).homology m) := by
  rw [← lawHomotopyEquiv_hom]
  exact homotopyCone_isZero (lawHomotopyEquiv N e laws ha) m

variable (l : LawValueLabel laws)
/-- 同じラベルの実block r/sが与える全整数次数同型。 -/
def blockHomologyIso (n : ℤ) := (blockHomotopyEquiv N e laws ha l).toHomologyIso n
/-- 全次数block同型の射は同じ独立生成r。 -/
theorem blockHomologyIso_hom (n : ℤ) :
    (blockHomologyIso N e laws ha l n).hom =
      HomologicalComplex.homologyMap (zeroExtensionMap (blockR N e laws ha l)) n := by
  change HomologicalComplex.homologyMap (blockHomotopyEquiv N e laws ha l).hom n = _
  rw [blockHomotopyEquiv_hom]
/-- 全次数block同型の逆射は同じ独立生成s。 -/
theorem blockHomologyIso_inv (n : ℤ) :
    (blockHomologyIso N e laws ha l n).inv =
      HomologicalComplex.homologyMap (zeroExtensionMap (blockS N e laws ha l)) n := by
  change HomologicalComplex.homologyMap (blockHomotopyEquiv N e laws ha l).inv n = _
  rw [blockHomotopyEquiv_inv]

/-- 同じラベルblockの既存H1商同型。 -/
def blockOldH1Iso := homotopyOldH1Iso (blockHomotopyEquiv N e laws ha l)
/-- block旧H1商同型は同じ独立生成rのh1Map。 -/
theorem blockOldH1Iso_hom : (blockOldH1Iso N e laws ha l).hom =
    ModuleCat.ofHom (blockR N e laws ha l).h1Map :=
  homotopyOldH1Iso_hom _ _ (blockHomotopyEquiv_hom N e laws ha l)
/-- block旧H1商同型の逆も同じ独立生成sのh1Map。 -/
theorem blockOldH1Iso_inv : (blockOldH1Iso N e laws ha l).inv =
    ModuleCat.ofHom (blockS N e laws ha l).h1Map :=
  homotopyOldH1Iso_inv _ _ (blockHomotopyEquiv_inv N e laws ha l)

/-- 各ラベルの同じ実block H1比較は全単射。 -/
theorem blockH1_bijective : Function.Bijective (blockR N e laws ha l).h1Map :=
  homotopyH1_bijective _ _ (blockHomotopyEquiv_hom N e laws ha l)
/-- 各ラベルの同じ実核・実余核の二成分は零。 -/
theorem blockH1_blockDefect_zero : blockDefect (blockR N e laws ha l).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (blockHomotopyEquiv_hom N e laws ha l)
/-- 同じblock実比較の標準錐は全整数次数でhomology零。 -/
theorem blockCone_isZero (m : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (blockR N e laws ha l))).homology m) := by
  rw [← blockHomotopyEquiv_hom]
  exact homotopyCone_isZero (blockHomotopyEquiv N e laws ha l) m

omit [Fintype Source] in
/-- 任意Aの同じ実subset比較の錐も全整数次数でhomology零。 -/
theorem subsetCone_isZero (A : Set q.Target) (m : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (chainContraction N e A).rHom)).homology m) := by
  rw [← SubsetChainContraction.cochainHomotopyEquiv_hom]
  exact homotopyCone_isZero (chainContraction N e A).cochainHomotopyEquiv m

omit [Fintype Source] in
/-- 任意Aの同じ旧subset H1比較は零欠損を与える。 -/
theorem subsetH1_blockDefect_zero (A : Set q.Target) :
    blockDefect (chainContraction N e A).rHom.h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (SubsetChainContraction.cochainHomotopyEquiv_hom _)

end TriangleAddition


namespace EdgeSubdivision
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じ実Law比較と逆有限和sectionによる全整数次数の標準homology同型。 -/
def lawHomologyIso (n : ℤ) := (lawHomotopyEquiv N e laws ha).toHomologyIso n
/-- 同型の順方向は独立生成した同じ実Law r。 -/
@[simp] theorem lawHomologyIso_hom (n : ℤ) :
    (lawHomologyIso N e laws ha n).hom =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawR N e laws ha)) n := rfl
/-- 同型の逆方向も独立生成した同じ実Law s。 -/
@[simp] theorem lawHomologyIso_inv (n : ℤ) :
    (lawHomologyIso N e laws ha n).inv =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawS N e laws ha)) n := rfl

/-- 同じ実Law二射の標準同値を既存H1商へ読み戻す。 -/
def lawOldH1Iso := homotopyOldH1Iso (lawHomotopyEquiv N e laws ha)
/-- 旧H1商同型の射は同じlawR.h1Mapそのもの。 -/
theorem lawOldH1Iso_hom : (lawOldH1Iso N e laws ha).hom =
    ModuleCat.ofHom (lawR N e laws ha).h1Map :=
  homotopyOldH1Iso_hom _ _ (lawHomotopyEquiv_hom N e laws ha)
/-- 旧H1商同型の逆射も同じlawS.h1Mapそのもの。 -/
theorem lawOldH1Iso_inv : (lawOldH1Iso N e laws ha).inv =
    ModuleCat.ofHom (lawS N e laws ha).h1Map :=
  homotopyOldH1Iso_inv _ _ (lawHomotopyEquiv_inv N e laws ha)

/-- 原始正操作から生成した同じLaw H1比較は全単射。 -/
theorem lawH1_bijective : Function.Bijective (lawR N e laws ha).h1Map :=
  homotopyH1_bijective _ _ (lawHomotopyEquiv_hom N e laws ha)
/-- 同じLaw H1比較の実核・実余核の二成分は零。 -/
theorem lawH1_blockDefect_zero : blockDefect (lawR N e laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (lawHomotopyEquiv_hom N e laws ha)
/-- 同じ実Law比較の標準錐は全整数次数のhomologyが零。 -/
theorem lawCone_isZero (m : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (lawR N e laws ha))).homology m) := by
  rw [← lawHomotopyEquiv_hom]
  exact homotopyCone_isZero (lawHomotopyEquiv N e laws ha) m

variable (l : LawValueLabel laws)
/-- 同じラベルの実block r/sが与える全整数次数同型。 -/
def blockHomologyIso (n : ℤ) := (blockHomotopyEquiv N e laws ha l).toHomologyIso n
/-- 全次数block同型の射は同じ独立生成r。 -/
theorem blockHomologyIso_hom (n : ℤ) :
    (blockHomologyIso N e laws ha l n).hom =
      HomologicalComplex.homologyMap (zeroExtensionMap (blockR N e laws ha l)) n := by
  change HomologicalComplex.homologyMap (blockHomotopyEquiv N e laws ha l).hom n = _
  rw [blockHomotopyEquiv_hom]
/-- 全次数block同型の逆射は同じ独立生成s。 -/
theorem blockHomologyIso_inv (n : ℤ) :
    (blockHomologyIso N e laws ha l n).inv =
      HomologicalComplex.homologyMap (zeroExtensionMap (blockS N e laws ha l)) n := by
  change HomologicalComplex.homologyMap (blockHomotopyEquiv N e laws ha l).inv n = _
  rw [blockHomotopyEquiv_inv]

/-- 同じラベルblockの既存H1商同型。 -/
def blockOldH1Iso := homotopyOldH1Iso (blockHomotopyEquiv N e laws ha l)
/-- block旧H1商同型は同じ独立生成rのh1Map。 -/
theorem blockOldH1Iso_hom : (blockOldH1Iso N e laws ha l).hom =
    ModuleCat.ofHom (blockR N e laws ha l).h1Map :=
  homotopyOldH1Iso_hom _ _ (blockHomotopyEquiv_hom N e laws ha l)
/-- block旧H1商同型の逆も同じ独立生成sのh1Map。 -/
theorem blockOldH1Iso_inv : (blockOldH1Iso N e laws ha l).inv =
    ModuleCat.ofHom (blockS N e laws ha l).h1Map :=
  homotopyOldH1Iso_inv _ _ (blockHomotopyEquiv_inv N e laws ha l)

/-- 各ラベルの同じ実block H1比較は全単射。 -/
theorem blockH1_bijective : Function.Bijective (blockR N e laws ha l).h1Map :=
  homotopyH1_bijective _ _ (blockHomotopyEquiv_hom N e laws ha l)
/-- 各ラベルの同じ実核・実余核の二成分は零。 -/
theorem blockH1_blockDefect_zero : blockDefect (blockR N e laws ha l).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (blockHomotopyEquiv_hom N e laws ha l)
/-- 同じblock実比較の標準錐は全整数次数でhomology零。 -/
theorem blockCone_isZero (m : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (blockR N e laws ha l))).homology m) := by
  rw [← blockHomotopyEquiv_hom]
  exact homotopyCone_isZero (blockHomotopyEquiv N e laws ha l) m

omit [Fintype Source] in
/-- 任意Aの同じ実subset比較の錐も全整数次数でhomology零。 -/
theorem subsetCone_isZero (A : Set q.Target) (m : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (chainContraction N e A).rHom)).homology m) := by
  rw [← SubsetChainContraction.cochainHomotopyEquiv_hom]
  exact homotopyCone_isZero (chainContraction N e A).cochainHomotopyEquiv m

omit [Fintype Source] in
/-- 任意Aの同じ旧subset H1比較は零欠損を与える。 -/
theorem subsetH1_blockDefect_zero (A : Set q.Target) :
    blockDefect (chainContraction N e A).rHom.h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (SubsetChainContraction.cochainHomotopyEquiv_hom _)

end EdgeSubdivision

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
