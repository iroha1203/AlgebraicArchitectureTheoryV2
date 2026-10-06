import ResearchLean.AG.FaceRelationSubdivision.RawBlockHomotopy
import ResearchLean.AG.FaceRelationSubdivision.HomotopyDiagnostics

/-!
# 同じ混在reading原始block射の実診断

## Implementation notes

同じ独立block正逆射を持つ標準同値から全次数・旧H1・実欠損・実錐を読む。
Law値型全体の有限性を入力にする案は採らず、既存の発生座標有限性を使う。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf) (laws : FiniteLawFamily Source)
variable (hc : laws.Adequate qc) (hf : laws.Adequate qf) (l : LawValueLabel laws)

/-- 任意Lawの同じ実比較の全整数次数同型。 -/
def blockHomologyIso (n : ℤ) := (P.blockHomotopyEquiv laws hc hf l).toHomologyIso n
/-- Law全次数同型の順射は同じ実Law比較のhomologyMap。 -/
@[simp] theorem blockHomologyIso_hom (n : ℤ) :
    (P.blockHomologyIso laws hc hf l n).hom = HomologicalComplex.homologyMap (zeroExtensionMap (P.blockR laws hc hf l)) n := by
  change HomologicalComplex.homologyMap _ _ = _
  rw [blockHomotopyEquiv_hom]
/-- Law全次数同型の逆射は同じ実Law逆比較のhomologyMap。 -/
@[simp] theorem blockHomologyIso_inv (n : ℤ) :
    (P.blockHomologyIso laws hc hf l n).inv = HomologicalComplex.homologyMap (zeroExtensionMap (P.blockS laws hc hf l)) n := by
  change HomologicalComplex.homologyMap _ _ = _
  rw [blockHomotopyEquiv_inv]
/-- 同じLaw全次数同型を既存H1商へ読む。 -/
def blockOldH1Iso := homotopyOldH1Iso (P.blockHomotopyEquiv laws hc hf l)
/-- 旧Law商同型の順射は同じ独立実Law h1Map。 -/
theorem blockOldH1Iso_hom : (P.blockOldH1Iso laws hc hf l).hom = ModuleCat.ofHom (P.blockR laws hc hf l).h1Map :=
  homotopyOldH1Iso_hom _ _ (P.blockHomotopyEquiv_hom laws hc hf l)
/-- 旧Law商同型の逆射は同じ独立実Law逆 h1Map。 -/
theorem blockOldH1Iso_inv : (P.blockOldH1Iso laws hc hf l).inv = ModuleCat.ofHom (P.blockS laws hc hf l).h1Map :=
  homotopyOldH1Iso_inv _ _ (P.blockHomotopyEquiv_inv laws hc hf l)
/-- 同じ全Law実H1比較は全単射。 -/
theorem blockH1_bijective : Function.Bijective (P.blockR laws hc hf l).h1Map :=
  homotopyH1_bijective _ _ (P.blockHomotopyEquiv_hom laws hc hf l)
/-- 同じ全Law実H1比較の二欠損は零。 -/
theorem blockDefect_zero : blockDefect (P.blockR laws hc hf l).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (P.blockHomotopyEquiv_hom laws hc hf l)
/-- 同じ全Law実比較の標準錐は全整数次数で零。 -/
theorem blockCone_isZero (n : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (P.blockR laws hc hf l))).homology n) := by
  have h := homotopyCone_isZero (P.blockHomotopyEquiv laws hc hf l) n
  rw [P.blockHomotopyEquiv_hom] at h
  exact h

/-- 同じ独立実block逆H1比較も全単射。 -/
theorem blockSH1_bijective : Function.Bijective (P.blockS laws hc hf l).h1Map :=
  homotopyH1_bijective (P.blockHomotopyEquiv laws hc hf l).symm _ (P.blockHomotopyEquiv_inv laws hc hf l)
/-- 同じ独立実block逆比較の二欠損も零。 -/
theorem blockSDefect_zero : blockDefect (P.blockS laws hc hf l).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero (P.blockHomotopyEquiv laws hc hf l).symm _ (P.blockHomotopyEquiv_inv laws hc hf l)
/-- 同じ独立実block逆比較の標準錐も全整数次数で零。 -/
theorem blockSCone_isZero (n : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap (P.blockS laws hc hf l))).homology n) := by
  have h : IsZero ((mappingCone (P.blockHomotopyEquiv laws hc hf l).inv).homology n) :=
    homotopyCone_isZero (P.blockHomotopyEquiv laws hc hf l).symm n
  rw [P.blockHomotopyEquiv_inv] at h
  exact h

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
