import ResearchLean.AG.FaceRelationSubdivision.OperationPathMaps
import ResearchLean.AG.FaceRelationSubdivision.RawBlockDiagnostics
import ResearchLean.AG.FaceRelationSubdivision.MixedLawDecomposition

/-!
# 原始有限列の同じ実全Law・block診断への接続

## Implementation notes

列の幾何と原始出力を先に固定し、任意Lawのadequacyと全ラベルを後で量化する。
一般分解bridgeのchain仮定は列が生成した原始可換式で放電する。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace PrimitiveOperationPath
variable (path : PrimitiveOperationPath qc Nc qf Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 有限列の同じ原始rから独立生成する実block比較。 -/
def blockR (l : LawValueLabel laws) := path.rawEquivalence.blockR laws ha (path.adequate laws ha) l
/-- 有限列の同じ原始sから独立生成する実逆block比較。 -/
def blockS (l : LawValueLabel laws) := path.rawEquivalence.blockS laws ha (path.adequate laws ha) l
/-- 同じ独立block正逆射の標準同値。 -/
def blockHomotopyEquiv (l : LawValueLabel laws) :=
  path.rawEquivalence.blockHomotopyEquiv laws ha (path.adequate laws ha) l
/-- 有限列block標準同値の順射は同じ独立比較。 -/
theorem blockHomotopyEquiv_hom (l) : (path.blockHomotopyEquiv laws ha l).hom =
    zeroExtensionMap (path.blockR laws ha l) := path.rawEquivalence.blockHomotopyEquiv_hom laws ha (path.adequate laws ha) l
/-- 有限列block標準同値の逆射は同じ独立逆比較。 -/
theorem blockHomotopyEquiv_inv (l) : (path.blockHomotopyEquiv laws ha l).inv =
    zeroExtensionMap (path.blockS laws ha l) := path.rawEquivalence.blockHomotopyEquiv_inv laws ha (path.adequate laws ha) l

/-- 同じ有限列全Law射と独立block射の全三成分は可換。 -/
theorem lawR_block_square (l) :
    cochainComp (path.lawR laws ha) (lawBlockHom laws (path.adequate laws ha) Nf l) =
      cochainComp (lawBlockHom laws ha Nc l) (path.blockR laws ha l) :=
  mixedLawFiniteBlock_square Nc Nf laws ha (path.adequate laws ha)
    path.rawEquivalence.r0 path.rawEquivalence.r1 path.rawEquivalence.r2
    path.rawEquivalence.r_comm01 path.rawEquivalence.r_comm12 l

/-- 同じ有限列全Law射と独立block射は既存H1商でも可換。 -/
theorem lawR_block_h1_square (l) :
    (lawBlockHom laws (path.adequate laws ha) Nf l).h1Map.comp (path.lawR laws ha).h1Map =
      (path.blockR laws ha l).h1Map.comp (lawBlockHom laws ha Nc l).h1Map := by
  have he := congrArg ThreeCochainComplex.Hom.h1Map (path.lawR_block_square laws ha l)
  simpa only [cochainComp_h1Map] using he

/-- 同じ有限列全Law実射の実H1核を全ラベルの実核へ読む。 -/
def lawRKernelFamilyEquiv : LinearMap.ker (path.lawR laws ha).h1Map ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → LinearMap.ker (path.blockR laws ha l).h1Map) :=
  mixedLawFiniteKernelFamilyEquiv laws ha (path.adequate laws ha)
    path.rawEquivalence.r0 path.rawEquivalence.r1 path.rawEquivalence.r2
    path.rawEquivalence.r_comm01 path.rawEquivalence.r_comm12
/-- 同じ有限列全Law実射の実H1余核を全ラベルの実余核へ読む。 -/
def lawRCokernelFamilyEquiv :
    ((Nf.lawGeneratedComplex laws (path.adequate laws ha)).H1 ⧸ LinearMap.range (path.lawR laws ha).h1Map) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (Nf.lawValueBlockComplex laws (path.adequate laws ha) l).H1 ⧸
        LinearMap.range (path.blockR laws ha l).h1Map) :=
  mixedLawFiniteCokernelFamilyEquiv laws ha (path.adequate laws ha)
    path.rawEquivalence.r0 path.rawEquivalence.r1 path.rawEquivalence.r2
    path.rawEquivalence.r_comm01 path.rawEquivalence.r_comm12
/-- 同じ有限列の実二欠損は重複を保持した全ラベルの実欠損の和。 -/
theorem lawRDefect_sum : blockDefect (path.lawR laws ha).h1Map =
    (∑ l, (blockDefect (path.blockR laws ha l).h1Map).1,
      ∑ l, (blockDefect (path.blockR laws ha l).h1Map).2) :=
  mixedLawFiniteDefect_sum laws ha (path.adequate laws ha)
    path.rawEquivalence.r0 path.rawEquivalence.r1 path.rawEquivalence.r2
    path.rawEquivalence.r_comm01 path.rawEquivalence.r_comm12

/-- 同じ有限列の実標準錐を全ラベルの同じ実錐族へ接続する。 -/
def lawRConeFamilyIso : mappingCone (zeroExtensionMap (path.lawR laws ha)) ≅
    FiniteComplexFamily.complex (fun l => mappingCone (zeroExtensionMap (path.blockR laws ha l))) :=
  mixedLawFiniteConeFamilyIso laws ha (path.adequate laws ha)
    path.rawEquivalence.r0 path.rawEquivalence.r1 path.rawEquivalence.r2
    path.rawEquivalence.r_comm01 path.rawEquivalence.r_comm12
/-- 同じ有限列錐の全整数次数homologyを同じ実ラベル錐へ読む。 -/
def lawRConeHomologyEquiv (n : ℤ) :
    (mappingCone (zeroExtensionMap (path.lawR laws ha))).homology n ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (mappingCone (zeroExtensionMap (path.blockR laws ha l))).homology n) :=
  mixedLawFiniteConeHomologyEquiv laws ha (path.adequate laws ha)
    path.rawEquivalence.r0 path.rawEquivalence.r1 path.rawEquivalence.r2
    path.rawEquivalence.r_comm01 path.rawEquivalence.r_comm12 n
/-- 各発生ラベルの同じ有限列実比較の二欠損は零。 -/
theorem blockDefect_zero (l) : blockDefect (path.blockR laws ha l).h1Map = (0,0) :=
  path.rawEquivalence.blockDefect_zero laws ha (path.adequate laws ha) l
/-- 各発生ラベルの同じ有限列実比較錐は全整数次数で零。 -/
theorem blockCone_isZero (l) (n : ℤ) : IsZero ((mappingCone (zeroExtensionMap (path.blockR laws ha l))).homology n) :=
  path.rawEquivalence.blockCone_isZero laws ha (path.adequate laws ha) l n

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
