import ResearchLean.AG.AtlasCoefficientFiber.FilteredSpectralObject
import ResearchLean.AG.AtlasDefectComposition.ConeHomologySequence

/-!
# G-135 B：原filtrationの低次数exact coupleと独立derived微分

## Implementation notes

各i/j/kは同じ実graded短完全列の標準homology射とδである。
E₂の必要な二項を独立に核・商として作り、exactnessによる持ち上げの商類をd₂とする。
τをd₂の定義に使う案は指定の比較義務を消すため採用しない。持ち上げの線形性を
入力に置かず、曖昧さが同じk像に入ることから商上の線形性を証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 第零列のiは原F¹包含のhomology射。 -/
def firstCoupleI (n : ℤ) : (zeroExtension (firstFiltrationComplex M A)).homology n →ₗ[ℚ]
    (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (firstFiltrationInclusion M A)) n).hom

/-- 第零列のjは原gr⁰射影のhomology射。 -/
def firstCoupleJ (n : ℤ) :
    (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n →ₗ[ℚ]
      (zeroExtension (firstGradedComplex M A)).homology n :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (firstGradedProjection M A)) n).hom

/-- 第零列のkは同じ原短完全列の標準δ。 -/
def firstCoupleK (n : ℤ) : (zeroExtension (firstGradedComplex M A)).homology n →ₗ[ℚ]
    (zeroExtension (firstFiltrationComplex M A)).homology (n + 1) :=
  ((firstGraded_shortExact M A).δ n (n + 1) rfl).hom

/-- 第一列のiは原F²包含のhomology射。 -/
def secondCoupleI (n : ℤ) : (zeroExtension (secondFiltrationComplex M A)).homology n →ₗ[ℚ]
    (zeroExtension (firstFiltrationComplex M A)).homology n :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (secondFiltrationInclusion M A)) n).hom

/-- 第一列のjは原gr¹射影のhomology射。 -/
def secondCoupleJ (n : ℤ) : (zeroExtension (firstFiltrationComplex M A)).homology n →ₗ[ℚ]
    (zeroExtension (secondGradedComplex M A)).homology n :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (secondGradedProjection M A)) n).hom

/-- 第一列のkは同じ原短完全列の標準δ。 -/
def secondCoupleK (n : ℤ) : (zeroExtension (secondGradedComplex M A)).homology n →ₗ[ℚ]
    (zeroExtension (secondFiltrationComplex M A)).homology (n + 1) :=
  ((secondGraded_shortExact M A).δ n (n + 1) rfl).hom

/-- 原第零列のi/jの完全性。 -/
theorem firstCouple_exact_ij (n : ℤ) : Function.Exact (firstCoupleI M A n) (firstCoupleJ M A n) :=
  transportShortComplex_exact _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((firstGraded_shortExact M A).homology_exact₂ n)

/-- 原第零列のj/kの完全性。 -/
theorem firstCouple_exact_jk (n : ℤ) : Function.Exact (firstCoupleJ M A n) (firstCoupleK M A n) :=
  transportShortComplex_exact _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((firstGraded_shortExact M A).homology_exact₃ n (n + 1) rfl)

/-- 原第零列のk/iの完全性。 -/
theorem firstCouple_exact_ki (n : ℤ) : Function.Exact (firstCoupleK M A n) (firstCoupleI M A (n + 1)) :=
  transportShortComplex_exact _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((firstGraded_shortExact M A).homology_exact₁ n (n + 1) rfl)

/-- 原第一列のi/jの完全性。 -/
theorem secondCouple_exact_ij (n : ℤ) : Function.Exact (secondCoupleI M A n) (secondCoupleJ M A n) :=
  transportShortComplex_exact _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((secondGraded_shortExact M A).homology_exact₂ n)

/-- 原第一列のj/kの完全性。 -/
theorem secondCouple_exact_jk (n : ℤ) : Function.Exact (secondCoupleJ M A n) (secondCoupleK M A n) :=
  transportShortComplex_exact _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((secondGraded_shortExact M A).homology_exact₃ n (n + 1) rfl)

/-- 原第一列のk/iの完全性。 -/
theorem secondCouple_exact_ki (n : ℤ) : Function.Exact (secondCoupleK M A n) (secondCoupleI M A (n + 1)) :=
  transportShortComplex_exact _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((secondGraded_shortExact M A).homology_exact₁ n (n + 1) rfl)

/-- E₁の第零列から第一列への実j∘k微分。 -/
def firstPageDifferential (n : ℤ) : (zeroExtension (firstGradedComplex M A)).homology n →ₗ[ℚ]
    (zeroExtension (secondGradedComplex M A)).homology (n + 1) :=
  (secondCoupleJ M A (n + 1)).comp (firstCoupleK M A n)

/-- E₁第一列から第二列への実k微分。第二gradedはF²自身。 -/
def secondPageRowDifferential (n : ℤ) : (zeroExtension (secondGradedComplex M A)).homology n →ₗ[ℚ]
    (zeroExtension (secondFiltrationComplex M A)).homology (n + 1) := secondCoupleK M A n

/-- exact coupleの完全性からE₁微分のsquare-zeroを生成する。 -/
theorem firstPageDifferential_square (n : ℤ) :
    (secondPageRowDifferential M A (n + 1)).comp (firstPageDifferential M A n) = 0 := by
  rw [firstPageDifferential, secondPageRowDifferential, ← LinearMap.comp_assoc,
    (secondCouple_exact_jk M A (n + 1)).linearMap_comp_eq_zero, LinearMap.zero_comp]

/-- 第零列のδの実評価API。 -/
@[simp] theorem firstCoupleK_apply (n : ℤ) (x : (zeroExtension (firstGradedComplex M A)).homology n) :
    firstCoupleK M A n x = (firstGraded_shortExact M A).δ n (n + 1) rfl x := rfl

/-- 第一列jの実標準homology評価API。 -/
@[simp] theorem secondCoupleJ_apply (n : ℤ) (x : (zeroExtension (firstFiltrationComplex M A)).homology n) :
    secondCoupleJ M A n x = HomologicalComplex.homologyMap
      (zeroExtensionMap (secondGradedProjection M A)) n x := rfl

/-- 第一列iの実標準homology評価API。 -/
@[simp] theorem secondCoupleI_apply (n : ℤ) (x : (zeroExtension (secondFiltrationComplex M A)).homology n) :
    secondCoupleI M A n x = HomologicalComplex.homologyMap
      (zeroExtensionMap (secondFiltrationInclusion M A)) n x := rfl

/-- 第一列kの実標準δ評価API。 -/
@[simp] theorem secondCoupleK_apply (n : ℤ) (x : (zeroExtension (secondGradedComplex M A)).homology n) :
    secondCoupleK M A n x = (secondGraded_shortExact M A).δ n (n + 1) rfl x := rfl

/-- E₁微分は実j∘kの値。 -/
@[simp] theorem firstPageDifferential_apply (n : ℤ) (x : (zeroExtension (firstGradedComplex M A)).homology n) :
    firstPageDifferential M A n x = secondCoupleJ M A (n + 1) (firstCoupleK M A n x) := rfl

/-- 入射のない(0,1)項の実E₂核。Rから独立に構成する。 -/
abbrev DerivedFiberPage := LinearMap.ker (firstPageDifferential M A (1 : ℤ))

/-- 出射のない(2,0)項の実E₂商。H²Pから独立に構成する。 -/
abbrev DerivedHorizontalPage :=
  (zeroExtension (secondFiltrationComplex M A)).homology (2 : ℤ) ⧸
    LinearMap.range (secondCoupleK M A (1 : ℤ))

/-- E₁閉性と原i/j完全性から、同じk値のF²持ち上げを生成する。 -/
theorem derivedLift_exists (x : DerivedFiberPage M A) :
    ∃ y : (zeroExtension (secondFiltrationComplex M A)).homology (2 : ℤ),
      secondCoupleI M A 2 y = firstCoupleK M A 1 x.1 :=
  (secondCouple_exact_ij M A 2 (firstCoupleK M A 1 x.1)).mp x.2

/-- 存在producerだけから選ぶ実F² homology持ち上げ。 -/
def derivedLift (x : DerivedFiberPage M A) : (zeroExtension (secondFiltrationComplex M A)).homology (2 : ℤ) :=
  Classical.choose (derivedLift_exists M A x)

/-- 選択した持ち上げは同じ原k値に戻る。 -/
theorem derivedLift_spec (x : DerivedFiberPage M A) :
    secondCoupleI M A 2 (derivedLift M A x) = firstCoupleK M A 1 x.1 :=
  Classical.choose_spec (derivedLift_exists M A x)

/-- 同じ第一微分像で商した持ち上げ類。τを定義に使わない。 -/
def derivedClass (x : DerivedFiberPage M A) : DerivedHorizontalPage M A :=
  Submodule.Quotient.mk (derivedLift M A x)

/-- 原k/i完全性により、任意の持ち上げが同じderived商類を返す。 -/
theorem derivedClass_eq_of_lift (x : DerivedFiberPage M A)
    (y : (zeroExtension (secondFiltrationComplex M A)).homology (2 : ℤ))
    (hy : secondCoupleI M A 2 y = firstCoupleK M A 1 x.1) :
    derivedClass M A x = Submodule.Quotient.mk y := by
  rw [derivedClass, Submodule.Quotient.eq]
  apply (secondCouple_exact_ki M A 1 _).mp
  change secondCoupleI M A 2 (derivedLift M A x - y) = 0
  rw [map_sub, hy, derivedLift_spec, sub_self]

/-- 同じ原exact coupleから独立生成する低次数d₂。 -/
def derivedSecondDifferential : DerivedFiberPage M A →ₗ[ℚ] DerivedHorizontalPage M A where
  toFun := derivedClass M A
  map_add' x y := by
    change derivedClass M A (x + y) =
      (LinearMap.range (secondCoupleK M A 1)).mkQ (derivedLift M A x) +
        (LinearMap.range (secondCoupleK M A 1)).mkQ (derivedLift M A y)
    rw [← map_add]
    apply derivedClass_eq_of_lift
    rw [map_add, derivedLift_spec, derivedLift_spec, Submodule.coe_add, map_add]
  map_smul' r x := by
    change derivedClass M A (r • x) = r • (LinearMap.range (secondCoupleK M A 1)).mkQ (derivedLift M A x)
    rw [← map_smul]
    apply derivedClass_eq_of_lift
    rw [map_smul, derivedLift_spec, Submodule.coe_smul, map_smul]

/-- 独立d₂の値は任意の同じ原持ち上げで評価できる。 -/
theorem derivedSecondDifferential_apply (x : DerivedFiberPage M A)
    (y : (zeroExtension (secondFiltrationComplex M A)).homology (2 : ℤ))
    (hy : secondCoupleI M A 2 y = firstCoupleK M A 1 x.1) :
    derivedSecondDifferential M A x = Submodule.Quotient.mk y := derivedClass_eq_of_lift M A x y hy

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.firstCoupleI
#print axioms AAT.AG.AtlasCoefficientFiber.firstCoupleJ
#print axioms AAT.AG.AtlasCoefficientFiber.firstCoupleK
#print axioms AAT.AG.AtlasCoefficientFiber.secondCoupleI
#print axioms AAT.AG.AtlasCoefficientFiber.secondCoupleJ
#print axioms AAT.AG.AtlasCoefficientFiber.secondCoupleK
#print axioms AAT.AG.AtlasCoefficientFiber.firstCouple_exact_ij
#print axioms AAT.AG.AtlasCoefficientFiber.firstCouple_exact_jk
#print axioms AAT.AG.AtlasCoefficientFiber.firstCouple_exact_ki
#print axioms AAT.AG.AtlasCoefficientFiber.secondCouple_exact_ij
#print axioms AAT.AG.AtlasCoefficientFiber.secondCouple_exact_jk
#print axioms AAT.AG.AtlasCoefficientFiber.secondCouple_exact_ki
#print axioms AAT.AG.AtlasCoefficientFiber.firstPageDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.secondPageRowDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.firstPageDifferential_square
#print axioms AAT.AG.AtlasCoefficientFiber.firstCoupleK_apply
#print axioms AAT.AG.AtlasCoefficientFiber.secondCoupleJ_apply
#print axioms AAT.AG.AtlasCoefficientFiber.secondCoupleI_apply
#print axioms AAT.AG.AtlasCoefficientFiber.secondCoupleK_apply
#print axioms AAT.AG.AtlasCoefficientFiber.firstPageDifferential_apply
#print axioms AAT.AG.AtlasCoefficientFiber.DerivedFiberPage
#print axioms AAT.AG.AtlasCoefficientFiber.DerivedHorizontalPage
#print axioms AAT.AG.AtlasCoefficientFiber.derivedLift_exists
#print axioms AAT.AG.AtlasCoefficientFiber.derivedLift
#print axioms AAT.AG.AtlasCoefficientFiber.derivedLift_spec
#print axioms AAT.AG.AtlasCoefficientFiber.derivedClass
#print axioms AAT.AG.AtlasCoefficientFiber.derivedClass_eq_of_lift
#print axioms AAT.AG.AtlasCoefficientFiber.derivedSecondDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.derivedSecondDifferential_apply
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
