import ResearchLean.AG.FaceRelationSubdivision.SupportedChain

/-!
# 支持を保つセル基底の有限和

原始セル像をFinsuppとして固定し、非零係数の各セルへの台包含だけを課す。
任意のAで同じ有限和を選択セルへ持ち上げる。chain-mapや保存結論は入力でない。

## Implementation notes

全セルの自由加群へ選択セルを零延長して、基底像を先に定めた射との一致を検査する。
支持交差点ごとに基底を作る案は同一セルを重複させるため採らず、既存subsetと同じ
存在命題付きセル名を基底とする。係数を一つのOption像へ制限する案は分割の逆sに
必要な有限和を表せないため採らない。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
universe u
variable {T I J L : Type u}

/-- Aと台が交わるセル名。交差点はproofであり追加の基底ではない。 -/
abbrev Selected (supp : I → Set T) (A : Set T) := {i : I // ∃ t, t ∈ supp i ∧ t ∈ A}

/-- 選択セルのchainを全セルへ零延長する。 -/
def selectedEmbed (supp : I → Set T) (A : Set T) :
    (Selected supp A →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ) := by
  classical
  exact {
  toFun x := x.extendDomain
  map_add' x y := by
    classical
    ext i
    by_cases h : ∃ t, t ∈ supp i ∧ t ∈ A <;> simp [Finsupp.extendDomain_apply, h]
  map_smul' a x := by
    classical
    ext i
    by_cases h : ∃ t, t ∈ supp i ∧ t ∈ A <;> simp [Finsupp.extendDomain_apply, h] }

/-- 零延長の基底評価。 -/
@[simp] theorem selectedEmbed_single (supp : I → Set T) (A : Set T)
    (i : Selected supp A) (a : ℚ) :
    selectedEmbed supp A (Finsupp.single i a) = Finsupp.single i.1 a :=
by
  classical
  exact Finsupp.extendDomain_single i a

/-- 同じセル名への零延長は単射。 -/
theorem selectedEmbed_injective (supp : I → Set T) (A : Set T) :
    Function.Injective (selectedEmbed supp A) := by
  intro x y h
  have := congrArg (Finsupp.subtypeDomain (fun i => ∃ t, t ∈ supp i ∧ t ∈ A)) h
  simpa [selectedEmbed] using this

/-- 支持選択による基底制限は同じセル名の選択基底になる。 -/
theorem subtypeDomain_single_selected (supp : I → Set T) (A : Set T)
    (i : Selected supp A) (a : ℚ) :
    (Finsupp.single i.1 a).subtypeDomain (fun j => ∃ t, t ∈ supp j ∧ t ∈ A) =
      Finsupp.single i a := by
  classical
  have h := congrArg (Finsupp.subtypeDomain (fun j => ∃ t, t ∈ supp j ∧ t ∈ A))
    (Finsupp.extendDomain_single i a)
  rw [Finsupp.subtypeDomain_extendDomain] at h
  exact h.symm

/-- 有限和の原始セル像と各非零項への台包含。可換性や同型は保持しない。 -/

structure SupportedBasisMap (suppI : I → Set T) (suppJ : J → Set T) where
  basisImage : I → J →₀ ℚ
  support_compatible : ∀ i j, basisImage i j ≠ 0 → suppI i ⊆ suppJ j

namespace SupportedBasisMap
variable {suppI : I → Set T} {suppJ : J → Set T}

/-- 原始セル像の全セル上の線形延長。 -/
def raw (M : SupportedBasisMap suppI suppJ) := freeMap M.basisImage

/-- 任意Aの選択セルへ同じ原始有限和を制限する。 -/
def selected (M : SupportedBasisMap suppI suppJ) (A : Set T) :
    (Selected suppI A →₀ ℚ) →ₗ[ℚ] (Selected suppJ A →₀ ℚ) :=
  freeMap fun i => (M.basisImage i.1).subtypeDomain (fun j => ∃ t, t ∈ suppJ j ∧ t ∈ A)

/-- 原始像の各非零項は、入力セルと同じAに選択される。 -/
theorem basis_support_selected (M : SupportedBasisMap suppI suppJ) (A : Set T)
    (i : Selected suppI A) (j : J) (hj : j ∈ (M.basisImage i.1).support) :
    ∃ t, t ∈ suppJ j ∧ t ∈ A := by
  obtain ⟨t, ht, ha⟩ := i.2
  exact ⟨t, M.support_compatible i.1 j (Finsupp.mem_support_iff.mp hj) ht, ha⟩

/-- 選択して零延長した原始基底像は、元の有限和と一致する。 -/
theorem selectedEmbed_basis (M : SupportedBasisMap suppI suppJ) (A : Set T)
    (i : Selected suppI A) :
    selectedEmbed suppJ A ((M.basisImage i.1).subtypeDomain
      (fun j => ∃ t, t ∈ suppJ j ∧ t ∈ A)) = M.basisImage i.1 :=
by
  classical
  exact Finsupp.extendDomain_subtypeDomain _ (M.basis_support_selected A i)

/-- 選択セルの射は全セルの原始射と零延長の下で一致する。 -/
theorem selectedEmbed_comm (M : SupportedBasisMap suppI suppJ) (A : Set T) :
    (selectedEmbed suppJ A).comp (M.selected A) = M.raw.comp (selectedEmbed suppI A) := by
  apply Finsupp.lhom_ext
  intro i a
  simp [selected, raw, LinearMap.comp_apply, freeMap_single, M.selectedEmbed_basis]


/-- 支持を保つ原始射の基底評価。 -/
@[simp] theorem raw_single (M : SupportedBasisMap suppI suppJ) (i : I) (a : ℚ) :
    M.raw (Finsupp.single i a) = a • M.basisImage i := freeMap_single _ _ _

/-- 選択された原始射の基底評価。 -/
@[simp] theorem selected_single (M : SupportedBasisMap suppI suppJ) (A : Set T)
    (i : Selected suppI A) (a : ℚ) :
    M.selected A (Finsupp.single i a) = a • (M.basisImage i.1).subtypeDomain
      (fun j => ∃ t, t ∈ suppJ j ∧ t ∈ A) := freeMap_single _ _ _

/-- 零延長と選択された原始射の可換性の点ごとの式。 -/
theorem selectedEmbed_apply (M : SupportedBasisMap suppI suppJ) (A : Set T)
    (x : Selected suppI A →₀ ℚ) :
    selectedEmbed suppJ A (M.selected A x) = M.raw (selectedEmbed suppI A x) :=
  LinearMap.congr_fun (M.selectedEmbed_comm A) x

/-- 全セルで証明した射の等号は任意の支持部分集合へ降りる。 -/
theorem selected_eq_of_raw_eq (M N : SupportedBasisMap suppI suppJ)
    (h : M.raw = N.raw) (A : Set T) : M.selected A = N.selected A := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective suppJ A
  rw [M.selectedEmbed_apply, N.selectedEmbed_apply, h]

/-- 台を保つ四つの原始射の可換式を、任意Aの同じ四射へ制限する。 -/
theorem selected_square_of_raw_square {I0 J0 : Type u}
    {suppI0 : I0 → Set T} {suppJ0 : J0 → Set T}
    (M1 : SupportedBasisMap suppI suppJ) (M0 : SupportedBasisMap suppI0 suppJ0)
    (di : SupportedBasisMap suppI suppI0) (dj : SupportedBasisMap suppJ suppJ0)
    (h : dj.raw.comp M1.raw = M0.raw.comp di.raw) (A : Set T) :
    (dj.selected A).comp (M1.selected A) = (M0.selected A).comp (di.selected A) := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective suppJ0 A
  change selectedEmbed suppJ0 A (dj.selected A (M1.selected A x)) =
    selectedEmbed suppJ0 A (M0.selected A (di.selected A x))
  rw [dj.selectedEmbed_apply, M1.selectedEmbed_apply,
    M0.selectedEmbed_apply, di.selectedEmbed_apply]
  exact LinearMap.congr_fun h (selectedEmbed suppI A x)


/-- 全セルの原始射は指定された有限和を直接評価する。 -/
theorem raw_apply (M : SupportedBasisMap suppI suppJ) (x : I →₀ ℚ) :
    M.raw x = x.sum (fun i a => a • M.basisImage i) := freeMap_apply _ _

/-- 入力chainの全非零セルがtに支持されれば、原始像の全非零セルもtに支持される。 -/
theorem raw_point_support (M : SupportedBasisMap suppI suppJ) (x : I →₀ ℚ)
    (t : T) (hx : ∀ i ∈ x.support, t ∈ suppI i) (j : J) (hj : M.raw x j ≠ 0) :
    t ∈ suppJ j := by
  classical
  by_contra ht
  apply hj
  rw [M.raw_apply]
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have hz : M.basisImage i j = 0 := by
    by_contra hne
    exact ht (M.support_compatible i j hne (hx i hi))
  simp [hz]

/-- 原始セル像の有限和を合成し、台包含を入力dataから導出する。 -/
def comp {suppL : L → Set T} (M : SupportedBasisMap suppI suppJ)
    (N : SupportedBasisMap suppJ suppL) : SupportedBasisMap suppI suppL where
  basisImage i := N.raw (M.basisImage i)
  support_compatible := by
    intro i k hk t ht
    apply N.raw_point_support (M.basisImage i) t ?_ k hk
    intro j hj
    exact M.support_compatible i j (Finsupp.mem_support_iff.mp hj) ht

/-- 直接有限和からの原始合成は二つの全セル線形射の合成に一致する。 -/
theorem raw_comp {suppL : L → Set T} (M : SupportedBasisMap suppI suppJ)
    (N : SupportedBasisMap suppJ suppL) : (M.comp N).raw = N.raw.comp M.raw := by
  apply Finsupp.lhom_ext
  intro i a
  simp [LinearMap.comp_apply, raw_single, comp]

/-- 原始合成を直接制限した射は、各段を制限した同じ射の合成である。 -/
theorem selected_comp {suppL : L → Set T} (M : SupportedBasisMap suppI suppJ)
    (N : SupportedBasisMap suppJ suppL) (A : Set T) :
    (M.comp N).selected A = (N.selected A).comp (M.selected A) := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective suppL A
  change selectedEmbed suppL A ((M.comp N).selected A x) =
    selectedEmbed suppL A (N.selected A (M.selected A x))
  rw [(M.comp N).selectedEmbed_apply, N.selectedEmbed_apply, M.selectedEmbed_apply, raw_comp]
  rfl


/-- 単一セル像と原始台包含から基底射を作る。 -/
def ofSingle (f : I → J) (hf : ∀ i, suppI i ⊆ suppJ (f i)) :
    SupportedBasisMap suppI suppJ where
  basisImage i := Finsupp.single (f i) 1
  support_compatible := by
    classical
    intro i j hj
    by_cases h : j = f i
    · subst j; exact hf i
    · exact False.elim (hj (by simp [h]))

/-- 原始零セル像。 -/
def zero (suppI : I → Set T) (suppJ : J → Set T) : SupportedBasisMap suppI suppJ where
  basisImage _ := 0
  support_compatible := by intro i j hj; exact False.elim (hj rfl)

/-- 原始セル像の和。同じ台条件は非零項から導出する。 -/
def add (M N : SupportedBasisMap suppI suppJ) : SupportedBasisMap suppI suppJ where
  basisImage i := M.basisImage i + N.basisImage i
  support_compatible := by
    intro i j hj
    by_cases hm : M.basisImage i j = 0
    · exact N.support_compatible i j (by intro hn; exact hj (by simp [hm, hn]))
    · exact M.support_compatible i j hm

/-- 原始セル像の符号反転。 -/
def neg (M : SupportedBasisMap suppI suppJ) : SupportedBasisMap suppI suppJ where
  basisImage i := - M.basisImage i
  support_compatible := by
    intro i j hj
    exact M.support_compatible i j (by intro hm; exact hj (by simp [hm]))

/-- 全セルの自由加群での和の評価。 -/
theorem raw_add (M N : SupportedBasisMap suppI suppJ) : (M.add N).raw = M.raw + N.raw := by
  apply Finsupp.lhom_ext
  intro i a
  simp [raw_single, add, smul_add]

/-- 全セルの自由加群での符号反転の評価。 -/
theorem raw_neg (M : SupportedBasisMap suppI suppJ) : M.neg.raw = -M.raw := by
  apply Finsupp.lhom_ext
  intro i a
  simp [raw_single, neg]

/-- 恒等の原始セル像。 -/
def identity (supp : I → Set T) : SupportedBasisMap supp supp :=
  ofSingle id (fun _ => Set.Subset.refl _)

/-- 原始恒等の全セル射は実線形恒等。 -/
theorem raw_identity (supp : I → Set T) : (identity supp).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i a
  simp [identity, ofSingle, raw_single, Finsupp.smul_single]

/-- 原始恒等の選択セル射も実線形恒等。 -/
theorem selected_identity (supp : I → Set T) (A : Set T) :
    (identity supp).selected A = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective supp A
  rw [(identity supp).selectedEmbed_apply, raw_identity]
  rfl


/-- 支持選択の後も有限和の加法は同じ二射の和。 -/
theorem selected_add (M N : SupportedBasisMap suppI suppJ) (A : Set T) :
    (M.add N).selected A = M.selected A + N.selected A := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective suppJ A
  change selectedEmbed suppJ A ((M.add N).selected A x) =
    selectedEmbed suppJ A (M.selected A x + N.selected A x)
  rw [(M.add N).selectedEmbed_apply, map_add, M.selectedEmbed_apply,
    N.selectedEmbed_apply, raw_add]
  rfl

/-- 支持選択の後も符号反転は同じ射の符号反転。 -/
theorem selected_neg (M : SupportedBasisMap suppI suppJ) (A : Set T) :
    M.neg.selected A = -M.selected A := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective suppJ A
  change selectedEmbed suppJ A (M.neg.selected A x) =
    selectedEmbed suppJ A (-M.selected A x)
  rw [M.neg.selectedEmbed_apply, map_neg, M.selectedEmbed_apply, raw_neg]
  rfl

/-- 零延長の単射を使い、原始3項補正式を同じ選択射の補正式へ制限する。 -/
theorem selected_identity_correction {I0 I2 : Type u}
    {supp0 : I0 → Set T} {supp2 : I2 → Set T}
    (P : SupportedBasisMap suppI suppI)
    (d : SupportedBasisMap supp2 suppI) (h : SupportedBasisMap suppI supp2)
    (k : SupportedBasisMap supp0 suppI) (b : SupportedBasisMap suppI supp0)
    (heq : ∀ x : I →₀ ℚ, x = P.raw x + d.raw (h.raw x) + k.raw (b.raw x)) (A : Set T)
    (x : Selected suppI A →₀ ℚ) :
    x = P.selected A x + d.selected A (h.selected A x) + k.selected A (b.selected A x) := by
  apply selectedEmbed_injective suppI A
  rw [map_add, map_add, P.selectedEmbed_apply, d.selectedEmbed_apply,
    h.selectedEmbed_apply, k.selectedEmbed_apply, b.selectedEmbed_apply]
  exact heq (selectedEmbed suppI A x)


/-- 部分セル写像を零または単一基底の原始像へ送る。 -/
def ofOption (f : I → Option J)
    (hf : ∀ i j, f i = some j → suppI i ⊆ suppJ j) : SupportedBasisMap suppI suppJ where
  basisImage i := rationalOptionCell (f i)
  support_compatible := by
    classical
    intro i j hj
    cases hfi : f i with
    | none => simp [hfi] at hj
    | some k =>
      by_cases h : j = k
      · subst j; exact hf i k hfi
      · exact False.elim (hj (by simp [hfi, h]))

/-- 単一セルconstructorの原始基底像。 -/
@[simp] theorem ofSingle_basis (f : I → J) (hf : ∀ i, suppI i ⊆ suppJ (f i)) (i : I) :
    (ofSingle f hf).basisImage i = Finsupp.single (f i) 1 := rfl

/-- 部分セルconstructorの原始基底像。 -/
@[simp] theorem ofOption_basis (f : I → Option J)
    (hf : ∀ i j, f i = some j → suppI i ⊆ suppJ j) (i : I) :
    (ofOption f hf).basisImage i = rationalOptionCell (f i) := rfl

/-- 零constructorの原始基底像。 -/
@[simp] theorem zero_basis (suppI : I → Set T) (suppJ : J → Set T) (i : I) :
    (zero suppI suppJ).basisImage i = 0 := rfl

/-- 和constructorの原始基底像。 -/
@[simp] theorem add_basis (M N : SupportedBasisMap suppI suppJ) (i : I) :
    (M.add N).basisImage i = M.basisImage i + N.basisImage i := rfl

/-- 符号反転constructorの原始基底像。 -/
@[simp] theorem neg_basis (M : SupportedBasisMap suppI suppJ) (i : I) :
    M.neg.basisImage i = -M.basisImage i := rfl

/-- 合成constructorの独立した原始有限和。 -/
@[simp] theorem comp_basis {suppL : L → Set T} (M : SupportedBasisMap suppI suppJ)
    (N : SupportedBasisMap suppJ suppL) (i : I) :
    (M.comp N).basisImage i = N.raw (M.basisImage i) := rfl


/-- 全セルでの両逆の一方を、同じ原始射の支持制限へ降ろす。 -/
theorem selected_comp_eq_identity (M : SupportedBasisMap suppI suppJ)
    (N : SupportedBasisMap suppJ suppI) (h : N.raw.comp M.raw = LinearMap.id) (A : Set T) :
    (N.selected A).comp (M.selected A) = LinearMap.id := by
  rw [← selected_comp]
  calc
    (M.comp N).selected A = (identity suppI).selected A :=
      selected_eq_of_raw_eq _ _ (by rw [raw_comp, h, raw_identity]) A
    _ = LinearMap.id := selected_identity _ _

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision

#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
