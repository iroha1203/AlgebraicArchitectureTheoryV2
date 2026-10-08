import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveMatrices
import ResearchLean.AG.AtlasCoefficientFiber.LawFiberSequence
import Mathlib.Data.Set.Finite.Basic

/-!
# G-135 B：原始有理blockによるτ消滅の有限検査

実行kernelは有限行列とBoolだけを読む。任意Setを含む数学入力からの
セル列挙は非計算的表示であり、期待rank・核基底・消滅を入力にしない。
全Law検査は元の発生label型を保ち、Value型全体の有限性を要求しない。

## Implementation notes

四つの有理表から符号・零・二制約を生成し、受理済みGram rank kernelで等式を判定する。
semantic rankや供給核基底を実行入力にする方法は、原始表からの判定にならないため採らない。
抽象Setを含む元入力のセル列挙は非計算的表示に置き、有理kernelとは全entry等号で接続する。
全Aは有限targetの全Finsetと全Setの同値で扱い、選択した支持集合だけの検査は採らない。
Lawは元の発生labelを保持し、同じ台を持つlabelの商による重複除去を行わない。
-/
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module
open ExecutableRationalLinearAlgebra
universe u

/-- 有理Gram rankの三つの値だけから原始block等式を判定するkernel。 -/
def rationalBlockTauDecision {I J K L S T : Type u}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype S] [Fintype T]
    (giant : Matrix I J ℚ) (base : Matrix K L ℚ) (constraint : Matrix S T ℚ) : Bool :=
  decide (rationalMatrixRank giant = rationalMatrixRank base + rationalMatrixRank constraint)

/-- 有限有理表のGram rank判定は、同じ三行列の意味的rank加法と必要十分。 -/
theorem rationalBlockTauDecision_eq_true_iff {I J K L S T : Type u}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype S] [Fintype T]
    (giant : Matrix I J ℚ) (base : Matrix K L ℚ) (constraint : Matrix S T ℚ) :
    rationalBlockTauDecision giant base constraint = true ↔
      giant.rank = base.rank + constraint.rank := by
  simp only [rationalBlockTauDecision, decide_eq_true_eq, rationalMatrixRank_eq_rank]

/-- 原有理B/H表から生成するBy-Hx行列。 -/
def rationalConstraintMatrix {E F G : Type u} (B : Matrix E F ℚ) (H : Matrix E G ℚ) :
    Matrix E (F ⊕ G) ℚ := fun e => Sum.elim (B e) (fun f => -H e f)

/-- 原有理V/D/B表から生成する(Vv+Dt,Bt)行列。 -/
def rationalBaseMatrix {E K F G : Type u}
    (B : Matrix E F ℚ) (D : Matrix K F ℚ) (V : Matrix K G ℚ) :
    Matrix (K ⊕ E) (G ⊕ F) ℚ := Matrix.fromBlocks V D 0 B

/-- 元の二制約を別の行blockに保つ原表だけからの行列。 -/
def rationalGiantMatrix {E K F G S : Type u}
    (B : Matrix E F ℚ) (D : Matrix K F ℚ) (H : Matrix E S ℚ) (V : Matrix K G ℚ) :
    Matrix (K ⊕ (E ⊕ E)) ((G ⊕ F) ⊕ (F ⊕ S)) ℚ := fun e f =>
  match e, f with
  | .inl e, .inl (.inl f) => V e f
  | .inl e, .inl (.inr f) => D e f
  | .inl e, .inr (.inl f) => D e f
  | .inl _, .inr (.inr _) => 0
  | .inr (.inl _), .inl (.inl _) => 0
  | .inr (.inl e), .inl (.inr f) => B e f
  | .inr (.inl _), .inr _ => 0
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr e), .inr (.inl f) => B e f
  | .inr (.inr e), .inr (.inr f) => -H e f

/-- B/D/H/V有理表だけを読むτ零判定。期待rankや核基底は入力にない。 -/
def rationalPrimitiveTauDecision {E K F G S : Type u}
    [Fintype E] [Fintype K] [Fintype F] [Fintype G] [Fintype S]
    (B : Matrix E F ℚ) (D : Matrix K F ℚ) (H : Matrix E S ℚ) (V : Matrix K G ℚ) : Bool :=
  rationalBlockTauDecision (rationalGiantMatrix B D H V) (rationalBaseMatrix B D V)
    (rationalConstraintMatrix B H)

/-- 原始四有理表からの判定は、そこから生成した二制約blockのrank加法と必要十分。 -/
theorem rationalPrimitiveTauDecision_eq_true_iff {E K F G S : Type u}
    [Fintype E] [Fintype K] [Fintype F] [Fintype G] [Fintype S]
    (B : Matrix E F ℚ) (D : Matrix K F ℚ) (H : Matrix E S ℚ) (V : Matrix K G ℚ) :
    rationalPrimitiveTauDecision B D H V = true ↔
      (rationalGiantMatrix B D H V).rank =
        (rationalBaseMatrix B D V).rank + (rationalConstraintMatrix B H).rank :=
  rationalBlockTauDecision_eq_true_iff _ _ _

/-- 有限添字の全Boolを保持するkernel。重複する台を商にしない。 -/
def finiteFamilyDecision {J : Type u} [Fintype J] (check : J → Bool) : Bool :=
  decide (∀ j, check j = true)

/-- 有限添字族の判定は、空族と重複する台の添字も含む全成分のtrueと必要十分。 -/
theorem finiteFamilyDecision_eq_true_iff {J : Type u} [Fintype J] (check : J → Bool) :
    finiteFamilyDecision check = true ↔ ∀ j, check j = true := by
  simp only [finiteFamilyDecision, decide_eq_true_eq]

/-- kernelの空行列発火検査。これはWの代替例ではなく有限演算の検査。 -/
theorem rationalPrimitiveTauDecision_empty :
    rationalPrimitiveTauDecision (0 : Matrix (Fin 0) (Fin 0) ℚ)
      (0 : Matrix (Fin 0) (Fin 0) ℚ) (0 : Matrix (Fin 0) (Fin 0) ℚ)
      (0 : Matrix (Fin 0) (Fin 0) ℚ) = true := by decide +kernel

/-- kernelは非零制約障害を実際にfalseへ評価する。W表の置換には使わない。 -/
theorem rationalPrimitiveTauDecision_failure :
    rationalPrimitiveTauDecision (1 : Matrix (Fin 1) (Fin 1) ℚ)
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (1 : Matrix (Fin 1) (Fin 1) ℚ)
      (0 : Matrix (Fin 1) (Fin 0) ℚ) = false := by decide +kernel

/-- 空の添字族も同じ有限kernelでtrueとなる。 -/
theorem finiteFamilyDecision_empty (check : Fin 0 → Bool) :
    finiteFamilyDecision check = true := by
  rw [finiteFamilyDecision_eq_true_iff]
  exact fun j => Fin.elim0 j

noncomputable section
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

/-- 純有理制約constructorは同じ元By-Hx表示と一致する。 -/
theorem rationalConstraintMatrix_eq_primitive (A : Set qc.Target)
    [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] :
    rationalConstraintMatrix (primitiveBMatrix M A) (primitiveHMatrix M A) =
      primitiveConstraintMatrix M A := by
  classical
  ext e f
  cases f <;>
    simp [rationalConstraintMatrix, primitiveConstraintMatrix_entry,
      Basis.prod_apply, primitiveConstraint_apply, primitiveBMatrix_entry, primitiveHMatrix_entry]

/-- 純有理WB constructorは同じ元(Vv+Dt,Bt)表示と一致する。 -/
theorem rationalBaseMatrix_eq_primitive (A : Set qc.Target)
    [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] :
    rationalBaseMatrix (primitiveBMatrix M A) (primitiveDMatrix M A) (primitiveVMatrix M A) =
      primitiveBaseMatrix M A := by
  classical
  ext e f
  cases e <;> cases f <;>
    simp [rationalBaseMatrix, primitiveBaseMatrix_entry,
      Basis.prod_apply, primitiveBaseBlock_apply, primitiveBMatrix_entry,
      primitiveDMatrix_entry, primitiveVMatrix_entry]

/-- 純有理Giant constructorは原二制約を保った同じ元射表示と一致する。 -/
theorem rationalGiantMatrix_eq_primitive (A : Set qc.Target)
    [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] :
    rationalGiantMatrix (primitiveBMatrix M A) (primitiveDMatrix M A)
      (primitiveHMatrix M A) (primitiveVMatrix M A) = primitiveGiantMatrix M A := by
  classical
  ext e f
  rcases e with e | (e | e) <;> rcases f with (f | f) | (f | f) <;>
    simp [rationalGiantMatrix, primitiveGiantMatrix_entry,
      Basis.prod_apply, primitiveGiantBlock_apply_all, primitiveBMatrix_entry,
      primitiveDMatrix_entry, primitiveHMatrix_entry, primitiveVMatrix_entry]

/-- 元有限セルを列挙し、同じ原B/D/H/Vの三block表示へkernelを適用する。 -/
def primitiveTauZeroDecision (A : Set qc.Target) : Bool := by
  classical
  letI := Fintype.ofFinite (MixedFace M A)
  letI := Fintype.ofFinite (VerticalFace M A)
  letI := Fintype.ofFinite (HorizontalFace M A)
  letI := Fintype.ofFinite (HorizontalEdge M A)
  letI := Fintype.ofFinite (VerticalEdge M A)
  exact rationalPrimitiveTauDecision (primitiveBMatrix M A) (primitiveDMatrix M A)
    (primitiveHMatrix M A) (primitiveVMatrix M A)

/-- 原始入力だけから生成した有限判定は同じ元τの零性と必要十分。 -/
theorem primitiveTauZeroDecision_eq_true_iff (A : Set qc.Target) :
    primitiveTauZeroDecision M A = true ↔ connectingTau M A = 0 := by
  classical
  letI := Fintype.ofFinite (MixedFace M A)
  letI := Fintype.ofFinite (VerticalFace M A)
  letI := Fintype.ofFinite (HorizontalFace M A)
  letI := Fintype.ofFinite (HorizontalEdge M A)
  letI := Fintype.ofFinite (VerticalEdge M A)
  rw [primitiveTauZeroDecision, rationalPrimitiveTauDecision_eq_true_iff,
    rationalGiantMatrix_eq_primitive, rationalBaseMatrix_eq_primitive,
    rationalConstraintMatrix_eq_primitive,
    primitiveGiantMatrix_rank, primitiveBaseMatrix_rank, primitiveConstraintMatrix_rank]
  exact (connectingTau_zero_iff_block_rank M A).symm

/-- 同じ判定は設計のBy=Hxに対する実D像包含とも必要十分。 -/
theorem primitiveTauZeroDecision_eq_true_iff_primitive (A : Set qc.Target) :
    primitiveTauZeroDecision M A = true ↔ PrimitiveTransgressionVanishing M A :=
  (primitiveTauZeroDecision_eq_true_iff M A).trans (connectingTau_zero_iff_primitive M A)

/-- T0の有限Sourceと全射readingから全targetの有限性を導く。 -/
theorem readingTarget_finite [Finite Source] (q : Reading Source) : Finite q.Target :=
  Finite.of_surjective q.read q.surjective

/-- finiteFamilyDecisionの全有限台検査は任意Setの全称と同値。 -/
theorem allFinsets_iff_allSets {T : Type u} [Fintype T] (p : Set T → Prop) :
    (∀ s : Finset T, p s) ↔ ∀ A : Set T, p A := by
  constructor
  · intro hh A
    simpa only [Set.Finite.coe_toFinset] using hh A.toFinite.toFinset
  · intro hh s
    exact hh s

variable [Fintype Source]

/-- 入力から全targetを有限化し、全部分集合で同じ原始判定を走査する。 -/
def allATauZeroDecision : Bool := by
  classical
  letI := readingTarget_finite qc
  letI := Fintype.ofFinite qc.Target
  exact finiteFamilyDecision (fun s : Finset qc.Target => primitiveTauZeroDecision M s)

/-- 全Aでの原τ零は、入力から生成した有限個のBool検査と必要十分。 -/
theorem allATauZeroDecision_eq_true_iff :
    allATauZeroDecision M = true ↔ ∀ A : Set qc.Target, connectingTau M A = 0 := by
  classical
  letI := readingTarget_finite qc
  letI := Fintype.ofFinite qc.Target
  rw [allATauZeroDecision, finiteFamilyDecision_eq_true_iff]
  simp only [primitiveTauZeroDecision_eq_true_iff]
  exact allFinsets_iff_allSets (T := qc.Target) (fun A => connectingTau M A = 0)

variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 元発生labelごとの同じ台の有限判定。Lawの重複度を保つ。 -/
def lawTauZeroDecision : Bool :=
  finiteFamilyDecision (fun l : LawValueLabel laws =>
    primitiveTauZeroDecision M (labelValueFiber laws qc ha l))

/-- 発生label有限検査は各原τ零と必要十分。 -/
theorem lawTauZeroDecision_eq_true_iff_labels : lawTauZeroDecision M laws ha = true ↔
    ∀ l : LawValueLabel laws, connectingTau M (labelValueFiber laws qc ha l) = 0 := by
  rw [lawTauZeroDecision, finiteFamilyDecision_eq_true_iff]
  exact forall_congr' (fun l => primitiveTauZeroDecision_eq_true_iff M _)

/-- 原Law SESの同じτ零は各原labelτ零と必要十分。 -/
theorem lawConnectingTau_zero_iff_labels : lawConnectingTau M laws ha = 0 ↔
    ∀ l : LawValueLabel laws, connectingTau M (labelValueFiber laws qc ha l) = 0 := by
  classical
  constructor
  · intro hh l
    apply LinearMap.ext
    intro r
    let z := (lawRFamilyEquiv M laws ha).symm (Pi.single l r)
    have he := lawConnectingTau_component M laws ha z l
    rw [hh, LinearMap.zero_apply, map_zero] at he
    have hz : lawRFamilyEquiv M laws ha z l = r := by
      simp only [z, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
    rw [hz] at he
    exact he.symm
  · intro hh
    apply LinearMap.ext
    intro r
    apply (lawPushforwardHomologyEquiv M laws ha 2).injective
    ext l
    rw [lawConnectingTau_component, hh l]
    simp only [LinearMap.zero_apply, map_zero, Pi.zero_apply]

/-- 原発生label有限判定は同じ実Law τの零性と必要十分。 -/
theorem lawTauZeroDecision_eq_true_iff :
    lawTauZeroDecision M laws ha = true ↔ lawConnectingTau M laws ha = 0 :=
  (lawTauZeroDecision_eq_true_iff_labels M laws ha).trans
    (lawConnectingTau_zero_iff_labels M laws ha).symm

end
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.rationalBlockTauDecision
#print axioms AAT.AG.AtlasCoefficientFiber.rationalBlockTauDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.rationalConstraintMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.rationalBaseMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.rationalGiantMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPrimitiveTauDecision
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPrimitiveTauDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.finiteFamilyDecision
#print axioms AAT.AG.AtlasCoefficientFiber.finiteFamilyDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPrimitiveTauDecision_empty
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPrimitiveTauDecision_failure
#print axioms AAT.AG.AtlasCoefficientFiber.finiteFamilyDecision_empty
#print axioms AAT.AG.AtlasCoefficientFiber.rationalConstraintMatrix_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.rationalBaseMatrix_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.rationalGiantMatrix_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveTauZeroDecision
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveTauZeroDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveTauZeroDecision_eq_true_iff_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.readingTarget_finite
#print axioms AAT.AG.AtlasCoefficientFiber.allFinsets_iff_allSets
#print axioms AAT.AG.AtlasCoefficientFiber.allATauZeroDecision
#print axioms AAT.AG.AtlasCoefficientFiber.allATauZeroDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.lawTauZeroDecision
#print axioms AAT.AG.AtlasCoefficientFiber.lawTauZeroDecision_eq_true_iff_labels
#print axioms AAT.AG.AtlasCoefficientFiber.lawConnectingTau_zero_iff_labels
#print axioms AAT.AG.AtlasCoefficientFiber.lawTauZeroDecision_eq_true_iff
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
