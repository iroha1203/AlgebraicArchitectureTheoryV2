import ResearchLean.AG.AtlasCoefficientFiber.LawSupportComposition

/-!
# G-135 D：同じ台の発生ラベルを別成分として保持

## Implementation notes

元canonical族同型の逆射へ単一ラベルの実cochainまたはliteral Rを入れる。
全族恒等則から同ラベルで元を回復し、異ラベルでは零を返すことを示す。
台の一致によるラベル同一視を構成に入れない。
-/
noncomputable section
open scoped Classical
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory HomologicalComplex CanonicalResolution ResolutionInvariance
open FaceRelationSubdivision AtlasDefectComposition
universe u
variable {Source : Type u} [finiteSource : Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 元Law Pの逆canonical族射から戻る全整数次数・全族値。 -/
theorem lawSupportFamilyP_inverse (n : ℤ)
    (z : (l : LawValueLabel laws) → (zeroExtension (pushforwardComplex M (labelValueFiber laws qc ha l))).X n) :
    (lawSupportFamilyP M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l))).f n
      ((lawPushforwardStandardIso M laws ha).inv.f n z) = z := by
  rw [lawSupportFamilyP_refl]
  exact congrArg (fun f => f.f n z) (lawPushforwardStandardIso M laws ha).inv_hom_id

/-- 同じ元Lawラベルに入れた原P cochainは全次数でそのまま回復する。 -/
theorem lawSupportP_single (n : ℤ) (l : LawValueLabel laws)
    (z : (zeroExtension (pushforwardComplex M (labelValueFiber laws qc ha l))).X n) :
    (lawSupportP M laws ha l (Set.Subset.refl _)).f n
      ((lawPushforwardStandardIso M laws ha).inv.f n (Pi.single l z)) = z := by
  have hh := congrFun (lawSupportFamilyP_inverse M laws ha n (Pi.single l z)) l
  rw [lawSupportFamilyP_apply, Pi.single_eq_same] at hh
  exact hh

/-- 異なる元Lawラベルは台が同じ場合でも原Pの別成分として零を読む。 -/
theorem lawSupportP_single_other (n : ℤ) (l j : LawValueLabel laws) (hne : j ≠ l)
    (z : (zeroExtension (pushforwardComplex M (labelValueFiber laws qc ha l))).X n) :
    (lawSupportP M laws ha j (Set.Subset.refl _)).f n
      ((lawPushforwardStandardIso M laws ha).inv.f n (Pi.single l z)) = 0 := by
  have hh := congrFun (lawSupportFamilyP_inverse M laws ha n (Pi.single l z)) j
  rw [lawSupportFamilyP_apply, Pi.single_eq_of_ne hne] at hh
  exact hh

omit finiteSource in
/-- 元Law literal Rの逆族座標から戻る全ラベル値。 -/
theorem lawSupportFamilyR_inverse
    (z : (l : LawValueLabel laws) → R M (labelValueFiber laws qc ha l)) :
    lawSupportFamilyR M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l))
      ((lawRFamilyEquiv M laws ha).symm z) = z := by
  rw [lawSupportFamilyR_refl]
  exact (lawRFamilyEquiv M laws ha).apply_symm_apply z

omit finiteSource in
/-- 同ラベルのliteral原R元は同じ直接Phi射で回復する。 -/
theorem lawSupportR_single (l : LawValueLabel laws) (z : R M (labelValueFiber laws qc ha l)) :
    lawSupportR M laws ha l (Set.Subset.refl _)
      ((lawRFamilyEquiv M laws ha).symm (Pi.single l z)) = z := by
  have hh := congrFun (lawSupportFamilyR_inverse M laws ha (Pi.single l z)) l
  rw [lawSupportFamilyR_apply, Pi.single_eq_same] at hh
  exact hh

omit finiteSource in
/-- 台が同じ異ラベルのliteral原R元も同一視されず零を読む。 -/
theorem lawSupportR_single_other (l j : LawValueLabel laws) (hne : j ≠ l)
    (z : R M (labelValueFiber laws qc ha l)) :
    lawSupportR M laws ha j (Set.Subset.refl _)
      ((lawRFamilyEquiv M laws ha).symm (Pi.single l z)) = 0 := by
  have hh := congrFun (lawSupportFamilyR_inverse M laws ha (Pi.single l z)) j
  rw [lawSupportFamilyR_apply, Pi.single_eq_of_ne hne] at hh
  exact hh

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP_single
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP_single_other
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyR_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportR_single
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportR_single_other
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
