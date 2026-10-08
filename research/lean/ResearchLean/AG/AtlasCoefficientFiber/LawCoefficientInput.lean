import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.PushforwardEvaluation

/-!
# G-135 D：実Law座標と同じ粗台・細逆像

## Implementation notes

発生ラベルをそのまま添字に保ち、既存block同値と台等号だけで三次数を移す。
同じ台のラベルを集合へ圧縮しない。細adequacyは粗adequacyとreading因子から作る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u

/-- 三項同値の合成は各実次数の線形同値を合成する。 -/
def coefficientCochainEquivTrans {C D E : ThreeCochainComplex.{0,u} ℚ}
    (e : ThreeCochainComplex.CochainEquiv C D) (f : ThreeCochainComplex.CochainEquiv D E) :
    ThreeCochainComplex.CochainEquiv C E where
  e0 := e.e0.trans f.e0
  e1 := e.e1.trans f.e1
  e2 := e.e2.trans f.e2
  comm0 x := by rw [LinearEquiv.trans_apply, e.comm0, f.comm0]; rfl
  comm1 x := by rw [LinearEquiv.trans_apply, e.comm1, f.comm1]; rfl

/-- 同値合成の実Homは全三成分の実合成である。 -/
theorem coefficientCochainEquivTrans_toHom {C D E : ThreeCochainComplex.{0,u} ℚ}
    (e : ThreeCochainComplex.CochainEquiv C D) (f : ThreeCochainComplex.CochainEquiv D E) :
    (coefficientCochainEquivTrans e f).toHom = cochainComp e.toHom f.toHom := rfl

/-- 等号で与えられた同じ三項複体の全次数同値。 -/
def coefficientCochainEquivOfEq {C D : ThreeCochainComplex.{0,u} ℚ} (h : C = D) :
    ThreeCochainComplex.CochainEquiv C D := by
  cases h
  exact {
    e0 := LinearEquiv.refl ℚ _
    e1 := LinearEquiv.refl ℚ _
    e2 := LinearEquiv.refl ℚ _
    comm0 := fun _ => rfl
    comm1 := fun _ => rfl }

/-- 等号同値の後合成は同じ既存Homの全体transportである。 -/
theorem coefficientCochainEquivOfEq_comp {C D E : ThreeCochainComplex.{0,u} ℚ}
    (h : D = E) (f : ThreeCochainComplex.Hom C D) :
    cochainComp f (coefficientCochainEquivOfEq h).toHom = subsetTransportHom h f := by
  cases h
  apply cochain_ext <;> apply LinearMap.ext <;> intro x <;> rfl

/-- 成分ごとの三項同値を同じ有限ラベル族の同値へ集める。 -/
def coefficientFamilyCochainEquiv {J : Type u} [Fintype J]
    {C D : J → ThreeCochainComplex.{0,u} ℚ}
    (e : ∀ j, ThreeCochainComplex.CochainEquiv (C j) (D j)) :
    ThreeCochainComplex.CochainEquiv (ThreeComplexFamily.complex C)
      (ThreeComplexFamily.complex D) where
  e0 := LinearEquiv.piCongrRight fun j => (e j).e0
  e1 := LinearEquiv.piCongrRight fun j => (e j).e1
  e2 := LinearEquiv.piCongrRight fun j => (e j).e2
  comm0 x := by funext j; exact (e j).comm0 (x j)
  comm1 x := by funext j; exact (e j).comm1 (x j)

/-- 族同値の順射は同じ実成分Homの族である。 -/
theorem coefficientFamilyCochainEquiv_toHom {J : Type u} [Fintype J]
    {C D : J → ThreeCochainComplex.{0,u} ℚ}
    (e : ∀ j, ThreeCochainComplex.CochainEquiv (C j) (D j)) :
    (coefficientFamilyCochainEquiv e).toHom = ThreeComplexFamily.map C D (fun j => (e j).toHom) := rfl

/-- 実Law複体から各発生ラベルの同じtarget部分集合複体への三次数同値。 -/
def lawSelectedCochainEquiv {Source : Type u} [Fintype Source] {q : Reading Source}
    (N : TargetSupportedNerve.{u,u} q) (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    ThreeCochainComplex.CochainEquiv (N.lawGeneratedComplex laws ha)
      (ThreeComplexFamily.complex fun l => N.targetSubsetComplex (labelValueFiber laws q ha l)) :=
  coefficientCochainEquivTrans (lawFamilyCochainEquiv N laws ha)
    (coefficientFamilyCochainEquiv fun l => N.lawValueBlockTargetSubsetComplexEquiv laws ha l)

variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

omit [Fintype Source] in
include h ha in
/-- 粗adequacyから原reading因子に沿って生成した細adequacy。 -/
theorem lawFineAdequate : laws.Adequate qf := adequate_of_coarser laws h ha

omit [Fintype Source] in
/-- 細Law値fiberは同じ粗値fiberのcanonical逆像。 -/
theorem lawFineFiber_eq_preimage (l : LawValueLabel laws) :
    labelValueFiber laws qf (lawFineAdequate (h := h) laws ha) l =
      comparisonFactor qc qf h ⁻¹' labelValueFiber laws qc ha l :=
  labelValueFiber_eq_preimage laws qc qf ha (lawFineAdequate (h := h) laws ha) h l

/-- 細側blockから、同じ粗fiberのcanonical逆像複体への三次数同値。 -/
def lawFineBlockCanonicalEquiv (l : LawValueLabel laws) :
    ThreeCochainComplex.CochainEquiv
      (Nf.lawValueBlockComplex laws (lawFineAdequate (h := h) laws ha) l)
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' labelValueFiber laws qc ha l)) :=
  coefficientCochainEquivTrans
    (Nf.lawValueBlockTargetSubsetComplexEquiv laws (lawFineAdequate (h := h) laws ha) l)
    (coefficientCochainEquivOfEq (congrArg Nf.targetSubsetComplex
      (lawFineFiber_eq_preimage (h := h) laws ha l)))

/-- 実細Law複体を粗側発生ラベルの同じcanonical逆像族へ移す。 -/
def lawFineCanonicalEquiv :
    ThreeCochainComplex.CochainEquiv
      (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))
      (ThreeComplexFamily.complex fun l =>
        Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' labelValueFiber laws qc ha l)) :=
  coefficientCochainEquivTrans (lawFamilyCochainEquiv Nf laws (lawFineAdequate (h := h) laws ha))
    (coefficientFamilyCochainEquiv (lawFineBlockCanonicalEquiv (Nf := Nf) (h := h) laws ha))

/-- 実粗Law複体を同じ粗台族へ移す三次数同値。 -/
def lawCoarseCanonicalEquiv : ThreeCochainComplex.CochainEquiv
    (Nc.lawGeneratedComplex laws ha)
    (ThreeComplexFamily.complex fun l => Nc.targetSubsetComplex (labelValueFiber laws qc ha l)) :=
  lawSelectedCochainEquiv Nc laws ha


/-- 同じ三項Homの三重合成を全成分で結合する。 -/
theorem coefficientCochain_comp_assoc {B C D E : ThreeCochainComplex.{0,u} ℚ}
    (f : ThreeCochainComplex.Hom B C) (g : ThreeCochainComplex.Hom C D)
    (k : ThreeCochainComplex.Hom D E) :
    cochainComp (cochainComp f g) k = cochainComp f (cochainComp g k) := by
  apply cochain_ext <;> rfl

/-- 同じ有限族の合成は各成分の実合成である。 -/
theorem coefficientFamily_map_comp {J : Type u} [Fintype J]
    {C D E : J → ThreeCochainComplex.{0,u} ℚ}
    (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j))
    (g : ∀ j, ThreeCochainComplex.Hom (D j) (E j)) :
    cochainComp (ThreeComplexFamily.map C D f) (ThreeComplexFamily.map D E g) =
      ThreeComplexFamily.map C E (fun j => cochainComp (f j) (g j)) := by
  apply cochain_ext <;> rfl

/-- 成分で証明された全Hom正方形は同じ有限族でも可換。 -/
theorem coefficientFamilyEquiv_natural {J : Type u} [Fintype J]
    {C D C' D' : J → ThreeCochainComplex.{0,u} ℚ}
    (e : ∀ j, ThreeCochainComplex.CochainEquiv (C j) (C' j))
    (e' : ∀ j, ThreeCochainComplex.CochainEquiv (D j) (D' j))
    (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j))
    (g : ∀ j, ThreeCochainComplex.Hom (C' j) (D' j))
    (hs : ∀ j, cochainComp (f j) (e' j).toHom = cochainComp (e j).toHom (g j)) :
    cochainComp (ThreeComplexFamily.map C D f) (coefficientFamilyCochainEquiv e').toHom =
      cochainComp (coefficientFamilyCochainEquiv e).toHom (ThreeComplexFamily.map C' D' g) := by
  apply cochain_ext
  · apply LinearMap.ext; intro x; funext j
    exact congrArg (fun k => k.f0 (x j)) (hs j)
  · apply LinearMap.ext; intro x; funext j
    exact congrArg (fun k => k.f1 (x j)) (hs j)
  · apply LinearMap.ext; intro x; funext j
    exact congrArg (fun k => k.f2 (x j)) (hs j)

/-- 細blockの同値の順Homは既存block同値とcanonical台transportの合成。 -/
theorem lawFineBlockCanonicalEquiv_toHom (l : LawValueLabel laws) :
    (lawFineBlockCanonicalEquiv (Nf := Nf) (h := h) laws ha l).toHom =
      cochainComp (Nf.lawValueBlockTargetSubsetComplexEquiv laws
        (lawFineAdequate (h := h) laws ha) l).toHom
        (coefficientCochainEquivOfEq (congrArg Nf.targetSubsetComplex
          (lawFineFiber_eq_preimage (h := h) laws ha l))).toHom := rfl

/-- 実粗Law同値の順Homの二段階表示。 -/
theorem lawCoarseCanonicalEquiv_toHom :
    (lawCoarseCanonicalEquiv (Nc := Nc) laws ha).toHom =
      cochainComp (lawFamilyCochainEquiv Nc laws ha).toHom
        (coefficientFamilyCochainEquiv fun l =>
          Nc.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom := rfl

/-- 実細Law同値の順Homの二段階表示。 -/
theorem lawFineCanonicalEquiv_toHom :
    (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).toHom =
      cochainComp (lawFamilyCochainEquiv Nf laws (lawFineAdequate (h := h) laws ha)).toHom
        (coefficientFamilyCochainEquiv (lawFineBlockCanonicalEquiv (Nf := Nf) (h := h) laws ha)).toHom := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCochainEquivTrans
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCochainEquivTrans_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCochainEquivOfEq
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCochainEquivOfEq_comp
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyCochainEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyCochainEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.lawSelectedCochainEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineAdequate
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineFiber_eq_preimage
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineBlockCanonicalEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineCanonicalEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoarseCanonicalEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCochain_comp_assoc
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamily_map_comp
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyEquiv_natural
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineBlockCanonicalEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoarseCanonicalEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineCanonicalEquiv_toHom
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
