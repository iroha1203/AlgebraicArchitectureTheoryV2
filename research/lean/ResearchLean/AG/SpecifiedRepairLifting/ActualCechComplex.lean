import ResearchLean.AG.SpecifiedRepairLifting.SquareNaturality
import ResearchLean.AG.ObstructionDiagnosticBridge.SpecifiedClassReflection
import ResearchLean.AG.ObstructionDiagnosticBridge.ActualCechReadingComparison

/-! # 元の Čech 複体と診断複体の整数加群への接続

Implementation notes: Čech 側は元の全次数の群と微分をそのまま使う。
診断側だけ三項複体の次数外を零にし、有理線形写像を加法写像として忘却する。
元の整数係数を有理化する方式と、Čech 側を三項へ切断する方式は採らない。
H¹ は元の商への代表元写像と標準 homology の降下を使って比較する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.SpecifiedRepairLifting
open Cohomology TwoPhase ObstructionDiagnosticBridge CanonicalResolution ResolutionInvariance
universe u

section Cech
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {V : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
variable (K : CoverRelativeCechComplex V Ob)
/-- 元の Čech の全次数の群。整数作用は加法群の標準作用。 -/
def cechObject (n : ℕ) : ModuleCat.{u} ℤ :=
  letI := K.cochainAddCommGroup n
  ModuleCat.of ℤ (K.Cn n)
/-- 元の微分を整数線形射として保持する。 -/
def cechDifferential (n : ℕ) : cechObject K n ⟶ cechObject K (n+1) :=
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n+1)
  ModuleCat.ofHom (K.d n).toIntLinearMap
/-- 元の複体則が全次数の標準複体則を与える。 -/
theorem cechDifferential_square (n : ℕ) :
    cechDifferential K n ≫ cechDifferential K (n+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact K.differential_comp n
/-- 切断せず元の全次数を用いた非負複体。 -/
def cechNative : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  CochainComplex.of (cechObject K) (cechDifferential K) (cechDifferential_square K)
/-- 元の cochain と同じ次数の標準 cochain の加法同定。 -/
def cechNativeEquiv (n : ℕ) : (cechNative K).X n ≃+ K.AdditiveCochain n :=
  AddEquiv.refl _
/-- 全次数の同定は元の cochain の値を変えない。 -/
@[simp] theorem cechNativeEquiv_apply (n : ℕ) (a : (cechNative K).X n) :
    cechNativeEquiv K n a = a := rfl
/-- 全次数で微分の値を保持する。 -/
theorem cechNative_d (n : ℕ) (a : (cechNative K).X n) :
    (cechNative K).d n (n+1) a = K.d n a := by
  exact congrArg (fun g : cechObject K n ⟶ cechObject K (n+1) => g a)
    (CochainComplex.of_d (cechObject K) (cechDifferential K) (cechDifferential_square K) n)

/-- 元の Čech cycle を同じ値の標準 cycle へ同定する。 -/
def cechCycleEquiv : K.CechCocycleSubgroup 1 ≃+ LinearMap.ker ((cechNative K).sc 1).g.hom where
  toFun z := oneCycle z.val (by rw [cechNative_d]; exact z.property)
  invFun z := ⟨z.val, by
    have hz := z.property
    change (cechNative K).d 1 ((ComplexShape.up ℕ).next 1) z.val = 0 at hz
    rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 1 2 by decide),
      cechNative_d] at hz
    exact hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
/-- 元の cycle の標準類を作る実加法写像。 -/
def cechCycleClass : K.CechCocycleSubgroup 1 →+ (cechNative K).homology 1 :=
  (moduleCycleClass _).comp (cechCycleEquiv K).toAddMonoidHom
/-- 元の全ての coboundary を同じ標準 homology が零にする。 -/
theorem cechCycleClass_boundary (a : K.Cn 0) :
    cechCycleClass K (K.coboundaryCocycle 0 a) = 0 := by
  apply (oneCycleClass_zero_iff _).mpr
  exact ⟨a, cechNative_d K 0 a⟩
/-- 元の AdditiveCechH1 から標準 H¹ への商写像。 -/
def cechH1Map : K.AdditiveCechH1 →+ (cechNative K).homology 1 :=
  QuotientAddGroup.lift _ (cechCycleClass K) (by
    rintro _ ⟨a,rfl⟩
    exact cechCycleClass_boundary K a)
/-- 全ての元の代表について H¹ の比較を計算する。 -/
@[simp] theorem cechH1Map_mk (z : K.CechCocycleSubgroup 1) :
    cechH1Map K (QuotientAddGroup.mk' _ z) = moduleCycleClass _ (cechCycleEquiv K z) := rfl
/-- 元の商の全ての類は標準 H¹ に忠実に対応する。 -/
theorem cechH1Map_injective : Function.Injective (cechH1Map K) := by
  have hz : ∀ x, cechH1Map K x = 0 → x = 0 := by
    intro x hx
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective (K.CechCoboundarySubgroupSucc 0) x
    rw [cechH1Map_mk, oneCycleClass_zero_iff] at hx
    obtain ⟨a,ha⟩ := hx
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    refine ⟨a, Subtype.ext ?_⟩
    change z.val = K.d 0 a
    rw [cechNative_d] at ha
    exact ha.symm
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,h,sub_self]
/-- 標準 H¹ の全ての類が元の Čech 商から来る。 -/
theorem cechH1Map_surjective : Function.Surjective (cechH1Map K) := by
  intro x
  obtain ⟨z,rfl⟩ := moduleCycleClass_surjective ((cechNative K).sc 1) x
  refine ⟨QuotientAddGroup.mk' _ ((cechCycleEquiv K).symm z), ?_⟩
  rw [cechH1Map_mk, AddEquiv.apply_symm_apply]
/-- 元の AdditiveCechH1 と標準 H¹ の同じ代表元による群同型。 -/
def cechH1Equiv : K.AdditiveCechH1 ≃+ (cechNative K).homology 1 :=
  AddEquiv.ofBijective (cechH1Map K) ⟨cechH1Map_injective K, cechH1Map_surjective K⟩
end Cech

/-- 診断三項複体の元の群と次数外の零群。 -/
def diagnosticObject (K : ThreeCochainComplex.{0,u} ℚ) : ℕ → ModuleCat.{u} ℤ
  | 0 => ModuleCat.of ℤ K.C0
  | 1 => ModuleCat.of ℤ K.C1
  | 2 => ModuleCat.of ℤ K.C2
  | _+3 => ModuleCat.of ℤ PUnit.{u+1}
/-- 診断の二つの微分の加法的忘却。 -/
def diagnosticDifferential (K : ThreeCochainComplex.{0,u} ℚ) :
    (n : ℕ) → diagnosticObject K n ⟶ diagnosticObject K (n+1)
  | 0 => ModuleCat.ofHom K.d0.toAddMonoidHom.toIntLinearMap
  | 1 => ModuleCat.ofHom K.d1.toAddMonoidHom.toIntLinearMap
  | _+2 => 0
/-- 元の診断複体則から零延長の複体則を生成する。 -/
theorem diagnosticDifferential_square (K : ThreeCochainComplex.{0,u} ℚ) (n : ℕ) :
    diagnosticDifferential K n ≫ diagnosticDifferential K (n+1) = 0 := by
  rcases n with _ | _ | n
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact K.d1_comp_d0
  · exact CategoryTheory.Limits.comp_zero
  · exact CategoryTheory.Limits.zero_comp
/-- 有理群を加法群として忘却した診断の非負零延長。 -/
def diagnosticNative (K : ThreeCochainComplex.{0,u} ℚ) : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  CochainComplex.of (diagnosticObject K) (diagnosticDifferential K) (diagnosticDifferential_square K)
/-- 診断の零次群は元の有理群の加法群そのもの。 -/
def diagnosticNativeEquiv0 (K : ThreeCochainComplex.{0,u} ℚ) : (diagnosticNative K).X 0 ≃+ K.C0 := AddEquiv.refl _
/-- 診断の一次群は元の有理群の加法群そのもの。 -/
def diagnosticNativeEquiv1 (K : ThreeCochainComplex.{0,u} ℚ) : (diagnosticNative K).X 1 ≃+ K.C1 := AddEquiv.refl _
/-- 診断の二次群も切り捨てず元の群として保持する。 -/
def diagnosticNativeEquiv2 (K : ThreeCochainComplex.{0,u} ℚ) : (diagnosticNative K).X 2 ≃+ K.C2 := AddEquiv.refl _
/-- 診断の次数外の各群は零群。 -/
theorem diagnosticNative_higher_zero (K : ThreeCochainComplex.{0,u} ℚ) (n : ℕ)
    (a : (diagnosticNative K).X (n+3)) : a = 0 := by
  exact @Subsingleton.elim PUnit.{u+1} inferInstance a (0 : PUnit.{u+1})
/-- 診断零延長の隣接微分は同じ二微分と零射。 -/
theorem diagnosticNative_d (K : ThreeCochainComplex.{0,u} ℚ) (n : ℕ) :
    (diagnosticNative K).d n (n+1) = diagnosticDifferential K n :=
  CochainComplex.of_d _ _ _ n

section DiagnosticH1
variable (K : ThreeCochainComplex.{0,u} ℚ)
/-- 診断の元の有理 cycle を同じ値の整数加群 cycle へ移す。 -/
def diagnosticCycleEquiv : LinearMap.ker K.d1 ≃+ LinearMap.ker ((diagnosticNative K).sc 1).g.hom where
  toFun z := oneCycle z.val (by rw [diagnosticNative_d]; exact z.property)
  invFun z := ⟨z.val, by
    have hz := z.property
    change (diagnosticNative K).d 1 ((ComplexShape.up ℕ).next 1) z.val = 0 at hz
    rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 1 2 by decide),
      diagnosticNative_d] at hz
    exact hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
/-- 診断 cycle の元の値から標準類を作る。 -/
def diagnosticCycleClass : LinearMap.ker K.d1 →+ (diagnosticNative K).homology 1 :=
  (moduleCycleClass _).comp (diagnosticCycleEquiv K).toAddMonoidHom
/-- 元の診断 boundary は標準類でも零となる。 -/
theorem diagnosticCycleClass_boundary (a : K.C0) :
    diagnosticCycleClass K (K.boundaryToCycles a) = 0 := by
  apply (oneCycleClass_zero_iff _).mpr
  refine ⟨a, ?_⟩
  rw [diagnosticNative_d]
  rfl
/-- 元の診断 H¹ 商から標準 H¹ への加法写像。 -/
def diagnosticH1Map : K.H1 →+ (diagnosticNative K).homology 1 :=
  QuotientAddGroup.lift (LinearMap.range K.boundaryToCycles).toAddSubgroup
    (diagnosticCycleClass K) (by
      rintro _ ⟨a,rfl⟩
      exact diagnosticCycleClass_boundary K a)
/-- 診断 H¹ 比較は全ての元の代表で同じ cycle の類を返す。 -/
@[simp] theorem diagnosticH1Map_mk (z : LinearMap.ker K.d1) :
    diagnosticH1Map K ((LinearMap.range K.boundaryToCycles).mkQ z) =
      moduleCycleClass _ (diagnosticCycleEquiv K z) := rfl
/-- 有理 H¹ の加法群を忘却しても類を同一視し過ぎない。 -/
theorem diagnosticH1Map_injective : Function.Injective (diagnosticH1Map K) := by
  have hz : ∀ x, diagnosticH1Map K x = 0 → x = 0 := by
    intro x hx
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.boundaryToCycles) x
    rw [diagnosticH1Map_mk, oneCycleClass_zero_iff] at hx
    obtain ⟨a,ha⟩ := hx
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨a, Subtype.ext ?_⟩
    rw [diagnosticNative_d] at ha
    exact ha
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,h,sub_self]
/-- 標準診断 H¹ の全ての類が元の診断商に対応する。 -/
theorem diagnosticH1Map_surjective : Function.Surjective (diagnosticH1Map K) := by
  intro x
  obtain ⟨z,rfl⟩ := moduleCycleClass_surjective ((diagnosticNative K).sc 1) x
  refine ⟨(LinearMap.range K.boundaryToCycles).mkQ ((diagnosticCycleEquiv K).symm z), ?_⟩
  rw [diagnosticH1Map_mk, AddEquiv.apply_symm_apply]
/-- 元の診断 H¹ の加法群と標準 H¹ の同型。 -/
def diagnosticH1Equiv : K.H1 ≃+ (diagnosticNative K).homology 1 :=
  AddEquiv.ofBijective (diagnosticH1Map K) ⟨diagnosticH1Map_injective K, diagnosticH1Map_surjective K⟩
end DiagnosticH1

section ActualComparison
variable {Source : Type u} [Fintype Source] {q : Reading Source} {laws : FiniteLawFamily Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S} [IsEmpty D.nerve.FaceComponent]
variable (P : GeneratorPresentation laws) (V : GeneratorPresentation.FaceEmptyAATCechCover D G)
variable (ha : laws.Adequate q)
omit [Fintype Source] in
/-- 元 Čech の高次群の零性は元 cover の空な simplex 添字から従う。 -/
theorem actualCechHigher_zero (n : ℕ) (a : (cechNative (P.faceEmptyCechComplex V)).X (n+2)) :
    a = 0 := by
  funext simplex
  exact isEmptyElim simplex
/-- 元の実係数比較の三成分と次数外の一意な射。 -/
def actualComparisonDegree : (n : ℕ) → cechObject (P.faceEmptyCechComplex V) n ⟶
    diagnosticObject (D.lawGeneratedComplex laws ha) n
  | 0 => ModuleCat.ofHom (P.actualCechCoefficientCochainMap V ha).f0.toIntLinearMap
  | 1 => ModuleCat.ofHom (P.actualCechCoefficientCochainMap V ha).f1.toIntLinearMap
  | 2 => ModuleCat.ofHom (P.actualCechCoefficientCochainMap V ha).f2.toIntLinearMap
  | _+3 => 0
/-- 元の比較可換式から全次数の cochain 条件を生成する。 -/
theorem actualComparisonDegree_comm (n : ℕ) :
    actualComparisonDegree P V ha n ≫ diagnosticDifferential (D.lawGeneratedComplex laws ha) n =
      cechDifferential (P.faceEmptyCechComplex V) n ≫ actualComparisonDegree P V ha (n+1) := by
  rcases n with _ | _ | _ | n
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (P.actualCechCoefficient_comm0 V ha a).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (P.actualCechCoefficient_comm1 V ha a).symm
  · simp only [diagnosticDifferential, actualComparisonDegree, Limits.comp_zero]
  · simp only [diagnosticDifferential, actualComparisonDegree, Limits.comp_zero]
/-- 元の実 Čech 比較から生成された同じ標準 cochain 射。 -/
def actualComparison : cechNative (P.faceEmptyCechComplex V) ⟶
    diagnosticNative (D.lawGeneratedComplex laws ha) :=
  CochainComplex.ofHom _ _ _ _ _ _ (actualComparisonDegree P V ha)
    (actualComparisonDegree_comm P V ha)
/-- 実比較の全次数成分の同定。 -/
@[simp] theorem actualComparison_f (n : ℕ) :
    (actualComparison P V ha).f n = actualComparisonDegree P V ha n := rfl
/-- 元の実診断 H¹ 比較と標準 H¹ 比較の全類での可換図式。 -/
theorem actualComparison_h1 (x : (P.faceEmptyCechComplex V).AdditiveCechH1) :
    homologyMap (actualComparison P V ha) 1 (cechH1Equiv (P.faceEmptyCechComplex V) x) =
      diagnosticH1Equiv (D.lawGeneratedComplex laws ha) (P.actualCechDiagnosticH1Map V ha x) := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective
    ((P.faceEmptyCechComplex V).CechCoboundarySubgroupSucc 0) x
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ 1).map (actualComparison P V ha))
    (moduleCycleClass _ (cechCycleEquiv _ z)) =
      moduleCycleClass _ (diagnosticCycleEquiv _ (P.actualCechDiagnosticCyclesMap V ha z))
  rw [moduleCycleClass_naturality]
  congr 1
end ActualComparison
end AAT.AG.SpecifiedRepairLifting

#print axioms AAT.AG.SpecifiedRepairLifting.cechObject
#print axioms AAT.AG.SpecifiedRepairLifting.cechDifferential
#print axioms AAT.AG.SpecifiedRepairLifting.cechDifferential_square
#print axioms AAT.AG.SpecifiedRepairLifting.cechNative
#print axioms AAT.AG.SpecifiedRepairLifting.cechNativeEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.cechNativeEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.cechNative_d
#print axioms AAT.AG.SpecifiedRepairLifting.cechCycleEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.cechCycleClass
#print axioms AAT.AG.SpecifiedRepairLifting.cechCycleClass_boundary
#print axioms AAT.AG.SpecifiedRepairLifting.cechH1Map
#print axioms AAT.AG.SpecifiedRepairLifting.cechH1Map_mk
#print axioms AAT.AG.SpecifiedRepairLifting.cechH1Map_injective
#print axioms AAT.AG.SpecifiedRepairLifting.cechH1Map_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.cechH1Equiv
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticObject
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticDifferential
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticDifferential_square
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNative
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNativeEquiv0
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNativeEquiv1
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNativeEquiv2
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNative_higher_zero
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNative_d
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticCycleEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticCycleClass
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticCycleClass_boundary
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticH1Map
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticH1Map_mk
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticH1Map_injective
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticH1Map_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticH1Equiv
#print axioms AAT.AG.SpecifiedRepairLifting.actualCechHigher_zero
#print axioms AAT.AG.SpecifiedRepairLifting.actualComparisonDegree
#print axioms AAT.AG.SpecifiedRepairLifting.actualComparisonDegree_comm
#print axioms AAT.AG.SpecifiedRepairLifting.actualComparison
#print axioms AAT.AG.SpecifiedRepairLifting.actualComparison_f
#print axioms AAT.AG.SpecifiedRepairLifting.actualComparison_h1
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting
