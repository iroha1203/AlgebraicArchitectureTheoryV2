import ResearchLean.AG.FaceRelationSubdivision.OperationPathMaps
import ResearchLean.AG.FaceRelationSubdivision.HomotopyDiagnostics

/-!
# 原始有限列の同じ実比較の全次数診断

## Implementation notes

既に独立生成した同じ射の標準同値を旧H1自然性へ渡す。
錐はG-133の同じ射の短完全列から全次数零性を得る。
期待rankや次元一致を保存証明の入力にする案は用いない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace PrimitiveOperationPath
variable (path : PrimitiveOperationPath qc Nc qf Nf)

/-- 全Aの同じ実subset比較の全整数次数同型。 -/
def subsetHomologyIso (A : Set qc.Target) (n : ℤ) := (path.subsetHomotopyEquiv A).toHomologyIso n
/-- 全次数同型の順射は同じ実subset比較のhomologyMap。 -/
@[simp] theorem subsetHomologyIso_hom (A) (n : ℤ) :
    (path.subsetHomologyIso A n).hom = HomologicalComplex.homologyMap (zeroExtensionMap (path.subsetR A)) n := rfl
/-- 全次数同型の逆射は同じ実subset逆比較のhomologyMap。 -/
@[simp] theorem subsetHomologyIso_inv (A) (n : ℤ) :
    (path.subsetHomologyIso A n).inv = HomologicalComplex.homologyMap (zeroExtensionMap (path.subsetS A)) n := rfl

/-- 同じ標準subset同型を既存H1商へ読む。 -/
def subsetOldH1Iso (A : Set qc.Target) := homotopyOldH1Iso (path.subsetHomotopyEquiv A)
/-- 旧商同型の順射は同じ実subset h1Map。 -/
theorem subsetOldH1Iso_hom (A) : (path.subsetOldH1Iso A).hom = ModuleCat.ofHom (path.subsetR A).h1Map :=
  homotopyOldH1Iso_hom _ _ (path.subsetHomotopyEquiv_hom A)
/-- 旧商同型の逆射は同じ実subset逆 h1Map。 -/
theorem subsetOldH1Iso_inv (A) : (path.subsetOldH1Iso A).inv = ModuleCat.ofHom (path.subsetS A).h1Map :=
  homotopyOldH1Iso_inv _ _ (path.subsetHomotopyEquiv_inv A)
/-- 任意Aの同じ実subset H1比較は全単射。 -/
theorem subsetH1_bijective (A) : Function.Bijective (path.subsetR A).h1Map :=
  homotopyH1_bijective _ _ (path.subsetHomotopyEquiv_hom A)
/-- 同じ実subset比較の核・余核二欠損は零。 -/
theorem subsetDefect_zero (A) : blockDefect (path.subsetR A).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (path.subsetHomotopyEquiv_hom A)
/-- 同じ実subset比較の標準錐は全整数次数で零。 -/
theorem subsetCone_isZero (A) (n : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (path.subsetR A))).homology n) := by
  have h := homotopyCone_isZero (path.subsetHomotopyEquiv A) n
  rw [path.subsetHomotopyEquiv_hom] at h
  exact h

/-- 同じ実subset逆比較も既存H1で全単射。 -/
theorem subsetSH1_bijective (A) : Function.Bijective (path.subsetS A).h1Map :=
  homotopyH1_bijective (path.subsetHomotopyEquiv A).symm _ (path.subsetHomotopyEquiv_inv A)
/-- 同じ実subset逆比較の実核・余核二欠損も零。 -/
theorem subsetSDefect_zero (A) : blockDefect (path.subsetS A).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero (path.subsetHomotopyEquiv A).symm _ (path.subsetHomotopyEquiv_inv A)
/-- 同じ実subset逆比較の標準錐も全整数次数で零。 -/
theorem subsetSCone_isZero (A) (n : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (path.subsetS A))).homology n) := by
  have h : IsZero ((mappingCone (path.subsetHomotopyEquiv A).inv).homology n) :=
    homotopyCone_isZero (path.subsetHomotopyEquiv A).symm n
  rw [path.subsetHomotopyEquiv_inv] at h
  exact h

variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 任意Lawの同じ実比較の全整数次数同型。 -/
def lawHomologyIso (n : ℤ) := (path.lawHomotopyEquiv laws ha).toHomologyIso n
/-- Law全次数同型の順射は同じ実Law比較のhomologyMap。 -/
@[simp] theorem lawHomologyIso_hom (n : ℤ) :
    (path.lawHomologyIso laws ha n).hom = HomologicalComplex.homologyMap (zeroExtensionMap (path.lawR laws ha)) n := rfl
/-- Law全次数同型の逆射は同じ実Law逆比較のhomologyMap。 -/
@[simp] theorem lawHomologyIso_inv (n : ℤ) :
    (path.lawHomologyIso laws ha n).inv = HomologicalComplex.homologyMap (zeroExtensionMap (path.lawS laws ha)) n := rfl
/-- 同じLaw全次数同型を既存H1商へ読む。 -/
def lawOldH1Iso := homotopyOldH1Iso (path.lawHomotopyEquiv laws ha)
/-- 旧Law商同型の順射は同じ独立実Law h1Map。 -/
theorem lawOldH1Iso_hom : (path.lawOldH1Iso laws ha).hom = ModuleCat.ofHom (path.lawR laws ha).h1Map :=
  homotopyOldH1Iso_hom _ _ (path.lawHomotopyEquiv_hom laws ha)
/-- 旧Law商同型の逆射は同じ独立実Law逆 h1Map。 -/
theorem lawOldH1Iso_inv : (path.lawOldH1Iso laws ha).inv = ModuleCat.ofHom (path.lawS laws ha).h1Map :=
  homotopyOldH1Iso_inv _ _ (path.lawHomotopyEquiv_inv laws ha)
/-- 同じ全Law実H1比較は全単射。 -/
theorem lawH1_bijective : Function.Bijective (path.lawR laws ha).h1Map :=
  homotopyH1_bijective _ _ (path.lawHomotopyEquiv_hom laws ha)
/-- 同じ全Law実H1比較の二欠損は零。 -/
theorem lawDefect_zero : blockDefect (path.lawR laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (path.lawHomotopyEquiv_hom laws ha)
/-- 同じ全Law実比較の標準錐は全整数次数で零。 -/
theorem lawCone_isZero (n : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (path.lawR laws ha))).homology n) := by
  have h := homotopyCone_isZero (path.lawHomotopyEquiv laws ha) n
  rw [path.lawHomotopyEquiv_hom] at h
  exact h

/-- 同じ全Law実逆H1比較も全単射。 -/
theorem lawSH1_bijective : Function.Bijective (path.lawS laws ha).h1Map :=
  homotopyH1_bijective (path.lawHomotopyEquiv laws ha).symm _ (path.lawHomotopyEquiv_inv laws ha)
/-- 同じ全Law実逆比較の二欠損も零。 -/
theorem lawSDefect_zero : blockDefect (path.lawS laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero (path.lawHomotopyEquiv laws ha).symm _ (path.lawHomotopyEquiv_inv laws ha)
/-- 同じ全Law実逆比較の標準錐も全整数次数で零。 -/
theorem lawSCone_isZero (n : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (path.lawS laws ha))).homology n) := by
  have h : IsZero ((mappingCone (path.lawHomotopyEquiv laws ha).inv).homology n) :=
    homotopyCone_isZero (path.lawHomotopyEquiv laws ha).symm n
  rw [path.lawHomotopyEquiv_inv] at h
  exact h

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
