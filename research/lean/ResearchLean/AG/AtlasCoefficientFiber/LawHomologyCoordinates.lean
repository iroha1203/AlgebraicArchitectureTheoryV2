import ResearchLean.AG.AtlasCoefficientFiber.LawFiberSequence
import ResearchLean.AG.AtlasCoefficientFiber.DefectMaps

/-!
# G-135 D：原Law五項列の全ラベル値

## Implementation notes

全整数次数で標準homology射と原ラベル射の可換正方形を使う。
原Lawの旧H¹商もその標準同型を介して同じ元に接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CochainComplex HomologicalComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u

/-- 実複体同型と元の有限族homologyから全次数座標を生成する。 -/
def coefficientFamilyHomologyEquiv {J : Type u} [Fintype J]
    {X : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    {F : J → CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (e : X ≅ FiniteComplexFamily.complex F) (n : ℤ) :
    X.homology n ≃ₗ[ℚ] ((j : J) → (F j).homology n) :=
  (homologyMapIso e n).toLinearEquiv.trans (FiniteComplexFamily.homologyEquiv F n)

/-- 同じ族homology同型の各値は実projectionのhomology射。 -/
theorem coefficientFamilyHomologyEquiv_component {J : Type u} [Fintype J]
    {X : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    {F : J → CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (e : X ≅ FiniteComplexFamily.complex F) (n : ℤ) (x : X.homology n) (j : J) :
    coefficientFamilyHomologyEquiv e n x j =
      homologyMap (e.hom ≫ FiniteComplexFamily.projection F j) n x := by
  dsimp only [coefficientFamilyHomologyEquiv, LinearEquiv.trans_apply]
  rw [FiniteComplexFamily.homologyEquiv_component, homologyMap_comp]
  rfl

/-- 実可換正方形は全次数・全homology元の元ラベル射と可換。 -/
theorem coefficientFamilyHomologyEquiv_natural {J : Type u} [Fintype J]
    {X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    {F G : J → CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (φ : X ⟶ Y) (ψ : ∀ j, F j ⟶ G j)
    (eX : X ≅ FiniteComplexFamily.complex F) (eY : Y ≅ FiniteComplexFamily.complex G)
    (comm : φ ≫ eY.hom = eX.hom ≫ FiniteComplexFamily.map F G ψ)
    (n : ℤ) (x : X.homology n) (j : J) :
    coefficientFamilyHomologyEquiv eY n (homologyMap φ n x) j =
      homologyMap (ψ j) n (coefficientFamilyHomologyEquiv eX n x j) := by
  rw [coefficientFamilyHomologyEquiv_component, coefficientFamilyHomologyEquiv_component,
    ← ModuleCat.comp_apply, ← homologyMap_comp, ← ModuleCat.comp_apply, ← homologyMap_comp]
  have hs : φ ≫ (eY.hom ≫ FiniteComplexFamily.projection G j) =
      (eX.hom ≫ FiniteComplexFamily.projection F j) ≫ ψ j := by
    rw [← Category.assoc, comm, Category.assoc, FiniteComplexFamily.map_projection,
      ← Category.assoc]
  rw [hs]

variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 同じ粗Law標準homologyを原粗部分集合の全ラベル族へ送る。 -/
def lawCoarseHomologyEquiv (n : ℤ) : (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology n ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (zeroExtension (Nc.targetSubsetComplex (labelValueFiber laws qc ha l))).homology n) :=
  coefficientFamilyHomologyEquiv (lawCoarseStandardIso (Nc := Nc) laws ha) n

/-- 同じ細Law標準homologyを原canonical逆像の全ラベル族へ送る。 -/
def lawFineHomologyEquiv (n : ℤ) :
    (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology n ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (zeroExtension
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' labelValueFiber laws qc ha l))).homology n) :=
  coefficientFamilyHomologyEquiv (lawFineStandardIso (Nf := Nf) (h := h) laws ha) n

/-- 同じLaw P homology同型を汎用実族APIとして読む。 -/
theorem lawPushforwardHomologyEquiv_eq (n : ℤ) : lawPushforwardHomologyEquiv M laws ha n =
    coefficientFamilyHomologyEquiv (lawPushforwardStandardIso M laws ha) n := rfl

/-- 同じLaw Q homology同型を汎用実族APIとして読む。 -/
theorem lawRestrictionHomologyEquiv_eq (n : ℤ) : lawRestrictionHomologyEquiv M laws ha n =
    coefficientFamilyHomologyEquiv (lawRestrictionStandardIso M laws ha) n := rfl

/-- 同じ実Law ηの標準homologyは全次数で同じ原ηの各値になる。 -/
theorem lawUnit_homology_component (n : ℤ)
    (x : (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology n) (l : LawValueLabel laws) :
    lawPushforwardHomologyEquiv M laws ha n
      (homologyMap (zeroExtensionMap (lawUnitHom M laws ha)) n x) l =
      homologyMap (zeroExtensionMap (unitHom M (labelValueFiber laws qc ha l))) n
        (lawCoarseHomologyEquiv (Nc := Nc) laws ha n x l) :=
  coefficientFamilyHomologyEquiv_natural _ _ _ _ (lawUnitStandard_square M laws ha) n x l

/-- 同じ実Law εの標準homologyは全次数で同じ原εの各値になる。 -/
theorem lawEvaluation_homology_component (n : ℤ)
    (x : (zeroExtension (lawPushforwardComplex M laws ha)).homology n) (l : LawValueLabel laws) :
    lawFineHomologyEquiv (Nf := Nf) (h := h) laws ha n
      (homologyMap (zeroExtensionMap (lawEvaluationHom M laws ha)) n x) l =
      homologyMap (zeroExtensionMap (evaluationHom M (labelValueFiber laws qc ha l))) n
        (lawPushforwardHomologyEquiv M laws ha n x l) :=
  coefficientFamilyHomologyEquiv_natural _ _ _ _ (lawEvaluationStandard_square M laws ha) n x l

/-- 独立生成実Law uの標準homologyは全次数で同じ原uの各値になる。 -/
theorem lawGenerated_homology_component (n : ℤ)
    (x : (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology n) (l : LawValueLabel laws) :
    lawFineHomologyEquiv (Nf := Nf) (h := h) laws ha n
      (homologyMap (zeroExtensionMap
        (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n x) l =
      homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l))) n
        (lawCoarseHomologyEquiv (Nc := Nc) laws ha n x l) :=
  coefficientFamilyHomologyEquiv_natural _ _ _ _ (lawGeneratedStandard_square M laws ha) n x l

/-- 同じLaw原L制限の標準homologyは全次数で同じ原制限の各値になる。 -/
theorem lawRestriction_homology_component (n : ℤ)
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology n)
    (l : LawValueLabel laws) : lawRestrictionHomologyEquiv M laws ha n
      (homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) n x) l =
      homologyMap (zeroExtensionMap (restrictionHom M (labelValueFiber laws qc ha l))) n
        (lawFineHomologyEquiv (Nf := Nf) (h := h) laws ha n x l) :=
  coefficientFamilyHomologyEquiv_natural _ _ _ _ (lawRestrictionStandard_square M laws ha) n x l

/-- 同じ粗Law旧H¹と同じ標準homologyの元を保つ同型。 -/
def lawOldCoarseH1Equiv : (Nc.lawGeneratedComplex laws ha).H1 ≃ₗ[ℚ]
    (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology (1 : ℤ) :=
  oldH1Equiv (Nc.lawGeneratedComplex laws ha)

/-- 同じ細Law旧H¹と同じ標準homologyの元を保つ同型。 -/
def lawOldFineH1Equiv : (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)).H1 ≃ₗ[ℚ]
    (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) :=
  oldH1Equiv (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))

/-- 同じ原Law ηの標準H¹射a。 -/
def lawUnitH1 := (homologyMap (zeroExtensionMap (lawUnitHom M laws ha)) (1 : ℤ)).hom

/-- 独立生成同じ原Law uの標準H¹射T。 -/
def lawDirectH1 := (homologyMap (zeroExtensionMap
  (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) (1 : ℤ)).hom

/-- 原Lawの独立Tは同じεH¹と同じaの合成に一致する。 -/
theorem lawDirectH1_factor : lawDirectH1 M laws ha = (lawEvaluationH1 M laws ha).comp (lawUnitH1 M laws ha) := by
  rw [lawEvaluationH1_eq_standard]
  apply LinearMap.ext
  intro x
  change homologyMap (zeroExtensionMap
    (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) 1 x = _
  rw [lawStandardComparison_factorization, homologyMap_comp]
  rfl

/-- 同じ旧LawH¹比較は同じ独立標準Tと元を保って可換である。 -/
theorem lawDirectH1_old (x : (Nc.lawGeneratedComplex laws ha).H1) :
    lawDirectH1 M laws ha (lawOldCoarseH1Equiv (Nc := Nc) laws ha x) =
      lawOldFineH1Equiv (Nf := Nf) (h := h) laws ha
        (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha) x) :=
  (oldH1Equiv_natural (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha)) x).symm

/-- 全ラベルのLaw実fiber制限値は同じ原R値になる。 -/
theorem lawFiberRestrictionH1_component
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ))
    (l : LawValueLabel laws) : lawRFamilyEquiv M laws ha (lawFiberRestrictionH1 M laws ha x) l =
      fiberRestrictionH1 M (labelValueFiber laws qc ha l)
        (lawFineHomologyEquiv (Nf := Nf) (h := h) laws ha 1 x l) := by
  rw [lawFiberRestrictionH1_apply, lawRestrictionHomologyREquiv_component, lawRestriction_homology_component,
    fiberRestrictionH1_apply]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyHomologyEquiv_component
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyHomologyEquiv_natural
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoarseHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawPushforwardHomologyEquiv_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionHomologyEquiv_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnit_homology_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluation_homology_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawGenerated_homology_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestriction_homology_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCoarseH1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldFineH1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnitH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawDirectH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawDirectH1_factor
#print axioms AAT.AG.AtlasCoefficientFiber.lawDirectH1_old
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberRestrictionH1_component
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
