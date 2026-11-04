import ResearchLean.AG.SpecifiedRepairLifting.PresentedGroups
import ResearchLean.AG.SpecifiedRepairLifting.SquareNaturality

/-! # 原始有限表示からの複体と比較の有限検査

Implementation notes: 六群は元の整数関係像による商であり、二つの微分と
三つの比較行列の全関係保存・複体則・cochain則を有限列検査する。
次数二の群と非零d¹を保持し、次数三以降だけを零延長する。
構造則を原始入力の証明fieldにせず、計算可能な検査条件から構成する。
有理化やd¹の零への置換は採用しない。
-/
namespace AAT.AG.SpecifiedRepairLifting.PresentedComplex
open CategoryTheory
open Matrix IntegerElimination PresentedGroups

/-- 全列の元関係membershipを原始整数solverで検査する。 -/
def ZeroColumns (P : Presentation) {n : ℕ} (A : Mat P.generators n) : Prop :=
  ∀ j, Divisible (produce P.matrix) (A.col j)
/-- 全列検査は有限個の整数整除で決定可能。 -/
instance zeroColumnsDecidable (P : Presentation) {n : ℕ} (A : Mat P.generators n) :
    Decidable (ZeroColumns P A) := by unfold ZeroColumns; infer_instance
/-- 全列検査は元商上の全入力での零性と必要十分。 -/
theorem zeroColumns_iff (P : Presentation) {n : ℕ} (A : Mat P.generators n) :
    ZeroColumns P A ↔ ∀ x, quotientClass P (A *ᵥ x) = 0 := by
  constructor
  · intro h x
    have hc : ∀ j, quotientClass P (A.col j) = 0 := by
      intro j
      exact (class_zero_iff P _).mpr ((divisible_iff_solution _ (produce_valid _) _).mp (h j))
    have he : A *ᵥ x = ∑ j, x j • A.col j := by
      ext i
      simp [mulVec,dotProduct,mul_comm]
    rw [he,map_sum]
    simp only [map_smul,hc,smul_zero,Finset.sum_const_zero]
  · intro h j
    apply (divisible_iff_solution _ (produce_valid _) _).mpr
    apply (class_zero_iff P _).mp
    simpa only [mulVec_single_one] using h (Pi.single j 1)
/-- 二行列の商上の等号は差の列の有限検査で得られる。 -/
theorem zeroColumns_sub_iff (P : Presentation) {n : ℕ} (A B : Mat P.generators n) :
    ZeroColumns P (A-B) ↔ ∀ x, quotientClass P (A *ᵥ x) = quotientClass P (B *ᵥ x) := by
  rw [zeroColumns_iff]
  simp only [sub_mulVec,map_sub,sub_eq_zero]
/-- 三つの元有限表示と二つの原始微分行列。 -/
structure ComplexData where
  P0 : Presentation
  P1 : Presentation
  P2 : Presentation
  d0 : Mat P1.generators P0.generators
  d1 : Mat P2.generators P1.generators
/-- 原始複体の全関係保存と複体則の有限検査。 -/
def ComplexValid (C : ComplexData) : Prop :=
  MapValid C.P0 C.P1 C.d0 ∧ MapValid C.P1 C.P2 C.d1 ∧ ZeroColumns C.P2 (C.d1*C.d0)
/-- 複体検査は全て有限。 -/
instance complexValidDecidable (C : ComplexData) : Decidable (ComplexValid C) := by
  unfold ComplexValid
  infer_instance
/-- 複体則は有限検査から元の全商元に対して生成される。 -/
theorem differential_square (C : ComplexData) (h : ComplexValid C) :
    (PresentedGroups.map C.P1 C.P2 C.d1 h.2.1).comp (PresentedGroups.map C.P0 C.P1 C.d0 h.1) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨a,rfl⟩ := class_surjective C.P0 x
  change PresentedGroups.map C.P1 C.P2 C.d1 h.2.1
    (PresentedGroups.map C.P0 C.P1 C.d0 h.1 (quotientClass C.P0 a)) = 0
  rw [map_class,map_class,mulVec_mulVec]
  exact (zeroColumns_iff _ _).mp h.2.2 a
/-- 元の三群を保持した非負次数の対象群。 -/
def nativeObject (C : ComplexData) : ℕ → ModuleCat ℤ
  | 0 => ModuleCat.of ℤ (PresentedGroups.Group C.P0)
  | 1 => ModuleCat.of ℤ (PresentedGroups.Group C.P1)
  | 2 => ModuleCat.of ℤ (PresentedGroups.Group C.P2)
  | _+3 => ModuleCat.of ℤ PUnit
/-- 有限検査を通った同じ二微分、次数外は零射。 -/
def nativeDifferential (C : ComplexData) (h : ComplexValid C) :
    (n : ℕ) → nativeObject C n ⟶ nativeObject C (n+1)
  | 0 => ModuleCat.ofHom (PresentedGroups.map C.P0 C.P1 C.d0 h.1)
  | 1 => ModuleCat.ofHom (PresentedGroups.map C.P1 C.P2 C.d1 h.2.1)
  | _+2 => 0
/-- 全次数の複体則を原始検査から得る。 -/
theorem nativeDifferential_square (C : ComplexData) (h : ComplexValid C) (n : ℕ) :
    nativeDifferential C h n ≫ nativeDifferential C h (n+1) = 0 := by
  rcases n with _ | _ | n
  · apply ModuleCat.hom_ext
    exact differential_square C h
  · exact CategoryTheory.Limits.comp_zero
  · exact CategoryTheory.Limits.zero_comp
/-- 原始有限表示をA/Bの非負複体へdecodeする。 -/
def native (C : ComplexData) (h : ComplexValid C) : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (nativeObject C) (nativeDifferential C h) (nativeDifferential_square C h)
/-- decodeした複体の微分は同じ元商射。 -/
theorem native_d (C : ComplexData) (h : ComplexValid C) (n : ℕ) :
    (native C h).d n (n+1) = nativeDifferential C h n := CochainComplex.of_d _ _ _ n
/-- 次数零は元商群そのもの。 -/
def nativeEquiv0 (C : ComplexData) (h : ComplexValid C) :
    (native C h).X 0 ≃ₗ[ℤ] PresentedGroups.Group C.P0 := LinearEquiv.refl _ _
/-- 次数一は元商群そのもの。 -/
def nativeEquiv1 (C : ComplexData) (h : ComplexValid C) :
    (native C h).X 1 ≃ₗ[ℤ] PresentedGroups.Group C.P1 := LinearEquiv.refl _ _
/-- 次数二も元商群そのもので、非零d¹を保持する。 -/
def nativeEquiv2 (C : ComplexData) (h : ComplexValid C) :
    (native C h).X 2 ≃ₗ[ℤ] PresentedGroups.Group C.P2 := LinearEquiv.refl _ _
/-- 二つの原始複体間の三つの比較行列。 -/
structure ComparisonData (C D : ComplexData) where
  f0 : Mat D.P0.generators C.P0.generators
  f1 : Mat D.P1.generators C.P1.generators
  f2 : Mat D.P2.generators C.P2.generators
/-- 三成分の関係保存と二つのcochain則を全て有限検査する。 -/
def ComparisonValid {C D : ComplexData} (f : ComparisonData C D) : Prop :=
  MapValid C.P0 D.P0 f.f0 ∧ MapValid C.P1 D.P1 f.f1 ∧ MapValid C.P2 D.P2 f.f2 ∧
    ZeroColumns D.P1 (D.d0*f.f0-f.f1*C.d0) ∧ ZeroColumns D.P2 (D.d1*f.f1-f.f2*C.d1)
/-- 比較検査も全て有限。 -/
instance comparisonValidDecidable {C D : ComplexData} (f : ComparisonData C D) :
    Decidable (ComparisonValid f) := by unfold ComparisonValid; infer_instance
/-- 比較の各次数射を同じ原始行列からdecodeする。 -/
def comparisonDegree {C D : ComplexData} (f : ComparisonData C D) (h : ComparisonValid f) :
    (n : ℕ) → nativeObject C n ⟶ nativeObject D n
  | 0 => ModuleCat.ofHom (PresentedGroups.map C.P0 D.P0 f.f0 h.1)
  | 1 => ModuleCat.ofHom (PresentedGroups.map C.P1 D.P1 f.f1 h.2.1)
  | 2 => ModuleCat.ofHom (PresentedGroups.map C.P2 D.P2 f.f2 h.2.2.1)
  | _+3 => 0
/-- 元商上の全cochain則を有限検査から生成する。 -/
theorem comparisonDegree_comm {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (f : ComparisonData C D) (hf : ComparisonValid f) (n : ℕ) :
    comparisonDegree f hf n ≫ nativeDifferential D hd n =
      nativeDifferential C hc n ≫ comparisonDegree f hf (n+1) := by
  rcases n with _ | _ | _ | n
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a,rfl⟩ := class_surjective C.P0 x
    change PresentedGroups.map D.P0 D.P1 D.d0 hd.1
      (PresentedGroups.map C.P0 D.P0 f.f0 hf.1 (quotientClass C.P0 a)) =
      PresentedGroups.map C.P1 D.P1 f.f1 hf.2.1
        (PresentedGroups.map C.P0 C.P1 C.d0 hc.1 (quotientClass C.P0 a))
    simp only [map_class,mulVec_mulVec]
    exact (zeroColumns_sub_iff _ _ _).mp hf.2.2.2.1 a
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a,rfl⟩ := class_surjective C.P1 x
    change PresentedGroups.map D.P1 D.P2 D.d1 hd.2.1
      (PresentedGroups.map C.P1 D.P1 f.f1 hf.2.1 (quotientClass C.P1 a)) =
      PresentedGroups.map C.P2 D.P2 f.f2 hf.2.2.1
        (PresentedGroups.map C.P1 C.P2 C.d1 hc.2.1 (quotientClass C.P1 a))
    simp only [map_class,mulVec_mulVec]
    exact (zeroColumns_sub_iff _ _ _).mp hf.2.2.2.2 a
  · simp only [nativeDifferential,comparisonDegree,CategoryTheory.Limits.comp_zero]
  · simp only [nativeDifferential,comparisonDegree,CategoryTheory.Limits.comp_zero]
/-- 原始行列の同じ比較をA/Bのcochain写像へdecodeする。 -/
def comparison {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (f : ComparisonData C D) (hf : ComparisonValid f) : native C hc ⟶ native D hd :=
  CochainComplex.ofHom _ _ _ _ _ _ (comparisonDegree f hf) (comparisonDegree_comm hc hd f hf)
/-- decodeした比較は元の同じ全次数射。 -/
theorem comparison_f {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (f : ComparisonData C D) (hf : ComparisonValid f) (n : ℕ) :
    (comparison hc hd f hf).f n = comparisonDegree f hf n := rfl
/-- 指定z,bの原始代表を含む全入力の有限検査。 -/
def InputValid (C D : ComplexData) (f : ComparisonData C D)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) : Prop :=
  ComplexValid C ∧ ComplexValid D ∧ ComparisonValid f ∧
    isZero C.P2 (C.d1 *ᵥ z) = true ∧ isZero D.P1 (D.d0 *ᵥ b - f.f1 *ᵥ z) = true
/-- 全入力検査は有限整数演算だけで決定する。 -/
instance inputValidDecidable (C D : ComplexData) (f : ComparisonData C D)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) : Decidable (InputValid C D f z b) := by
  unfold InputValid
  infer_instance
/-- 全原始入力の実行可能な検査。 -/
def checkInput (C D : ComplexData) (f : ComparisonData C D)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) : Bool := decide (InputValid C D f z b)
/-- 検査結果から全構造条件と指定入力条件を得る。 -/
theorem checkInput_correct (C D : ComplexData) (f : ComparisonData C D)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) :
    checkInput C D f z b = true ↔ InputValid C D f z b := by
  simp only [checkInput,decide_eq_true_eq]
/-- 閉性は元整数代表の有限検査から生成される。 -/
theorem input_closed (C D : ComplexData) (f : ComparisonData C D)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b) :
    (native C h.1).d 1 2 (quotientClass C.P1 z) = 0 := by
  rw [native_d]
  change PresentedGroups.map C.P1 C.P2 C.d1 h.1.2.1 (quotientClass C.P1 z) = 0
  rw [map_class]
  exact (isZero_correct _ _).mp h.2.2.2.1
/-- 指定補正の適合性も元代表の有限検査から生成される。 -/
theorem input_compatible (C D : ComplexData) (f : ComparisonData C D)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b) :
    (native D h.2.1).d 0 1 (quotientClass D.P0 b) =
      (comparison h.1 h.2.1 f h.2.2.1).f 1 (quotientClass C.P1 z) := by
  rw [native_d,comparison_f]
  change PresentedGroups.map D.P0 D.P1 D.d0 h.2.1.1 (quotientClass D.P0 b) =
    PresentedGroups.map C.P1 D.P1 f.f1 h.2.2.1.2.1 (quotientClass C.P1 z)
  rw [map_class,map_class]
  have he := (isZero_correct _ _).mp h.2.2.2.2
  simpa only [map_sub,sub_eq_zero] using he

/-- 零次微分は同じ原始代表にd⁰行列を適用する。 -/
theorem native_d0_class (C : ComplexData) (h : ComplexValid C) (x : Vec C.P0.generators) :
    (native C h).d 0 1 (quotientClass C.P0 x) = quotientClass C.P1 (C.d0 *ᵥ x) := by
  rw [native_d]
  exact map_class _ _ _ h.1 x
/-- 一次微分は同じ原始代表にd¹行列を適用する。 -/
theorem native_d1_class (C : ComplexData) (h : ComplexValid C) (x : Vec C.P1.generators) :
    (native C h).d 1 2 (quotientClass C.P1 x) = quotientClass C.P2 (C.d1 *ᵥ x) := by
  rw [native_d]
  exact map_class _ _ _ h.2.1 x
/-- 比較零次成分の同じ原始代表での評価。 -/
theorem comparison_apply0 {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (f : ComparisonData C D) (hf : ComparisonValid f) (x : Vec C.P0.generators) :
    (comparison hc hd f hf).f 0 (quotientClass C.P0 x) = quotientClass D.P0 (f.f0 *ᵥ x) := by
  rw [comparison_f]
  exact map_class _ _ _ hf.1 x
/-- 比較一次成分の同じ原始代表での評価。 -/
theorem comparison_apply1 {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (f : ComparisonData C D) (hf : ComparisonValid f) (x : Vec C.P1.generators) :
    (comparison hc hd f hf).f 1 (quotientClass C.P1 x) = quotientClass D.P1 (f.f1 *ᵥ x) := by
  rw [comparison_f]
  exact map_class _ _ _ hf.2.1 x
/-- 比較二次成分の同じ原始代表での評価。 -/
theorem comparison_apply2 {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (f : ComparisonData C D) (hf : ComparisonValid f) (x : Vec C.P2.generators) :
    (comparison hc hd f hf).f 2 (quotientClass C.P2 x) = quotientClass D.P2 (f.f2 *ᵥ x) := by
  rw [comparison_f]
  exact map_class _ _ _ hf.2.2.1 x

/-- 三次以降は明示的な零群であり、元の次数二は含めない。 -/
theorem native_higher_zero (C : ComplexData) (h : ComplexValid C) (n : ℕ)
    (x : (native C h).X (n+3)) : x = 0 := by
  exact @Subsingleton.elim PUnit inferInstance x 0

end AAT.AG.SpecifiedRepairLifting.PresentedComplex

#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.ZeroColumns
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.zeroColumnsDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.zeroColumns_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.zeroColumns_sub_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.ComplexData
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.ComplexValid
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.complexValidDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.differential_square
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.nativeObject
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.nativeDifferential
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.nativeDifferential_square
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.native
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.native_d
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.nativeEquiv0
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.nativeEquiv1
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.nativeEquiv2
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.ComparisonData
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.ComparisonValid
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparisonValidDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparisonDegree
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparisonDegree_comm
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparison
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparison_f
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.InputValid
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.inputValidDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.checkInput
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.checkInput_correct
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.input_closed
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.input_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.native_d0_class
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.native_d1_class
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparison_apply0
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparison_apply1
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.comparison_apply2
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedComplex.native_higher_zero
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.PresentedComplex
