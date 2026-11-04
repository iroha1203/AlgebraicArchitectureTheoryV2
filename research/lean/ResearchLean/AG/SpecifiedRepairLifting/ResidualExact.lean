import ResearchLean.AG.SpecifiedRepairLifting.LiftTorsor
import Mathlib.GroupTheory.QuotientGroup.Basic
/-! # 指定補正の余核障害

実零次比較の余核で残差を比較する。元の補正の選択を追加の構造へ隠さず、
任意二つの補正から差のcycleを生成する。

Implementation notes: mathlibの標準homologyを保持し、実kernel/range商との
既存同型を介して加法写像を降ろす。これによりjの(b,0)とpのsource成分を
全ての元のcycleで評価でき、同じ代表元から符号と完全性を検証できる。
短完全列を外部の構造fieldとして受け取る方式や独自のH¹商を終域にする方式は、
固定targetの標準比較との一致を別途必要にするため採らない。
categoryの抽象exactnessだけから結論を得る方式より、必要な補正証人を
元のcochainへ直接戻せる具体商の降下を用いる。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.SpecifiedRepairLifting
open CochainComplex
universe w
variable {R : Type} [CommRing R]
/-- 標準短複体の実cycleから標準homologyへの加法写像。 -/
def moduleCycleClass (S : ShortComplex (ModuleCat.{w} R)) :
    LinearMap.ker S.g.hom →+ S.homology :=
  S.moduleCatHomologyIso.inv.hom.toAddMonoidHom.comp
    (LinearMap.range S.moduleCatToCycles).mkQ.toAddMonoidHom
/-- 標準類の零性は実微分の像への所属と同値。 -/
theorem moduleCycleClass_zero_iff (S : ShortComplex (ModuleCat.{w} R))
    (c : LinearMap.ker S.g.hom) :
    moduleCycleClass S c = 0 ↔ ∃ a : S.X₁, S.f a = c.val := by
  change S.moduleCatHomologyIso.toLinearEquiv.symm _ = 0 ↔ _
  rw [← map_zero S.moduleCatHomologyIso.toLinearEquiv.symm,
    S.moduleCatHomologyIso.toLinearEquiv.symm.injective.eq_iff]
  change (LinearMap.range S.moduleCatToCycles).mkQ c = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨a,ha⟩; exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a,ha⟩; exact ⟨a, Subtype.ext ha⟩
/-- 二つの標準類は差が実微分であるとき、かつそのときだけ一致する。 -/
theorem moduleCycleClass_eq_iff (S : ShortComplex (ModuleCat.{w} R))
    (c c' : LinearMap.ker S.g.hom) :
    moduleCycleClass S c = moduleCycleClass S c' ↔
      ∃ a : S.X₁, S.f a = c.val - c'.val := by
  rw [← sub_eq_zero, ← map_sub, moduleCycleClass_zero_iff]
  rfl
/-- 全ての標準homology類は実cycleから来る。 -/
theorem moduleCycleClass_surjective (S : ShortComplex (ModuleCat.{w} R)) :
    Function.Surjective (moduleCycleClass S) :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
    (Submodule.mkQ_surjective _)
/-- 実微分を零にするcycle写像を、標準homologyからの写像に降ろす。 -/
def moduleDescClass (S : ShortComplex (ModuleCat.{w} R))
    {A : Type*} [AddCommGroup A] (g : LinearMap.ker S.g.hom →+ A)
    (hg : ∀ a : S.X₁, g (S.moduleCatToCycles a) = 0) : S.homology →+ A :=
  (QuotientAddGroup.lift (LinearMap.range S.moduleCatToCycles).toAddSubgroup g
    (by rintro _ ⟨a,rfl⟩; exact hg a)).comp
    S.moduleCatHomologyIso.hom.hom.toAddMonoidHom
/-- 標準類への降下は全ての実cycleで元の写像と一致する。 -/
@[simp] theorem moduleDescClass_class (S : ShortComplex (ModuleCat.{w} R))
    {A : Type*} [AddCommGroup A] (g : LinearMap.ker S.g.hom →+ A)
    (hg : ∀ a : S.X₁, g (S.moduleCatToCycles a) = 0)
    (c : LinearMap.ker S.g.hom) :
    moduleDescClass S g hg (moduleCycleClass S c) = g c := by
  change QuotientAddGroup.lift _ g (by rintro _ ⟨a,rfl⟩; exact hg a)
    (S.moduleCatHomologyIso.toLinearEquiv
      (S.moduleCatHomologyIso.toLinearEquiv.symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl
/-- 標準短複体射が元のcycleへ誘導する写像。 -/
def moduleCycleMap {S T : ShortComplex (ModuleCat.{w} R)} (φ : S ⟶ T) :
    LinearMap.ker S.g.hom →+ LinearMap.ker T.g.hom where
  toFun c := ⟨φ.τ₂ c.val, by
    have h := congrArg (fun g : S.X₂ ⟶ T.X₃ => g c.val) φ.comm₂₃
    change T.g (φ.τ₂ c.val) = φ.τ₃ (S.g c.val) at h
    have hc : S.g c.val = 0 := c.property
    change T.g (φ.τ₂ c.val) = 0
    simpa only [hc, map_zero] using h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c c' := Subtype.ext (map_add _ _ _)
/-- 具体cycleと標準cycles objectの間の同型の評価。 -/
theorem moduleCycles_inv_i (S : ShortComplex (ModuleCat.{w} R))
    (c : LinearMap.ker S.g.hom) : S.iCycles (S.moduleCatCyclesIso.inv c) = c.val :=
  congrArg (fun g => g c) S.moduleCatCyclesIso_inv_iCycles
/-- 元のcycleの標準類は標準homology射に自然である。 -/
theorem moduleCycleClass_naturality {S T : ShortComplex (ModuleCat.{w} R)}
    (φ : S ⟶ T) (c : LinearMap.ker S.g.hom) :
    ShortComplex.homologyMap φ (moduleCycleClass S c) =
      moduleCycleClass T (moduleCycleMap φ c) := by
  have hc : ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv c) =
      T.moduleCatCyclesIso.inv (moduleCycleMap φ c) := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [moduleCycles_inv_i]
    have h := congrArg (fun g => g (S.moduleCatCyclesIso.inv c)) (ShortComplex.cyclesMap_i φ)
    change T.iCycles (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv c)) =
      φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv c)) at h
    rw [moduleCycles_inv_i] at h
    exact h
  have hs : S.homologyπ (S.moduleCatCyclesIso.inv c) = moduleCycleClass S c :=
    congrArg (fun g => g c) S.moduleCatCyclesIso_inv_π
  have ht : T.homologyπ (T.moduleCatCyclesIso.inv (moduleCycleMap φ c)) =
      moduleCycleClass T (moduleCycleMap φ c) :=
    congrArg (fun g => g (moduleCycleMap φ c)) T.moduleCatCyclesIso_inv_π
  have h := congrArg (fun g => g (S.moduleCatCyclesIso.inv c)) (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv c)) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv c)) at h
  rw [hs, hc, ht] at h
  exact h
variable {C D : CochainComplex (ModuleCat.{w} ℤ) ℕ} (f : C ⟶ D)
/-- 同じ実零次比較の余核。 -/
abbrev CorrectionCokernel := zeroCycles D ⧸ (cycleComparison f).range
/-- 元の補正から生成する余核の指定残差。 -/
def residualClass (z : C.X 1) (b : D.X 0) (a₀ : C.X 0)
    (ha₀ : C.d 0 1 a₀ = z) (hb : D.d 0 1 b = f.f 1 z) : CorrectionCokernel f :=
  QuotientAddGroup.mk' _ (residualCycle f z b a₀ ha₀ hb)
/-- 元の補正の選択によらず余核類が一致する。 -/
theorem residualClass_independent (z : C.X 1) (b : D.X 0) (a₀ a₁ : C.X 0)
    (ha₀ : C.d 0 1 a₀ = z) (ha₁ : C.d 0 1 a₁ = z)
    (hb : D.d 0 1 b = f.f 1 z) :
    residualClass f z b a₀ ha₀ hb = residualClass f z b a₁ ha₁ hb := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  refine ⟨⟨a₁-a₀, ?_⟩, ?_⟩
  · change C.d 0 1 (a₁-a₀) = 0
    rw [map_sub, ha₁, ha₀, sub_self]
  · apply Subtype.ext
    change f.f 0 (a₁-a₀) = (b-f.f 0 a₀) - (b-f.f 0 a₁)
    rw [map_sub]
    abel
/-- 余核類零から、指定補正そのものを実現する元の補正を構成する。 -/
theorem residualClass_zero_iff_lift (z : C.X 1) (b : D.X 0) (a₀ : C.X 0)
    (ha₀ : C.d 0 1 a₀ = z) (hb : D.d 0 1 b = f.f 1 z) :
    residualClass f z b a₀ ha₀ hb = 0 ↔ Nonempty (NonnegativeLift f z b) := by
  change (QuotientAddGroup.mk (residualCycle f z b a₀ ha₀ hb) : CorrectionCokernel f) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨h,hh⟩
    have hf : f.f 0 h.val = b - f.f 0 a₀ := congrArg Subtype.val hh
    refine ⟨⟨a₀+h.val, ?_, ?_⟩⟩
    · have hd : C.d 0 1 h.val = 0 := h.property
      rw [map_add, ha₀, hd, add_zero]
    · rw [map_add, hf]
      abel
  · rintro ⟨a⟩
    refine ⟨⟨a.val-a₀, ?_⟩, ?_⟩
    · change C.d 0 1 (a.val-a₀) = 0
      rw [map_sub, a.property.1, ha₀, sub_self]
    · apply Subtype.ext
      change f.f 0 (a.val-a₀) = b-f.f 0 a₀
      rw [map_sub, a.property.2]

/-- Z⁰Dを標準錐の実cycle(b,0)へ送る。 -/
def zeroCycleToCone : zeroCycles D →+
    LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom where
  toFun b := specifiedCycle (zeroExtensionMap C D f) 0
    ((zeroExtensionEquiv D 0).symm b.val) (map_zero _)
    (by
      simpa only [map_zero] using
        zeroExtension_compatible f 0 b.val (by simpa only [map_zero] using b.property))
  map_zero' := by
    apply Subtype.ext
    apply (coneCoordinateEquiv (zeroExtensionMap C D f) 0).injective
    simp [specifiedRepresentative, specifiedCycle]
  map_add' b b' := by
    apply Subtype.ext
    change (coneCoordinateEquiv (zeroExtensionMap C D f) 0).symm
      ((zeroExtensionEquiv D 0).symm (b.val+b'.val), -0) =
      (coneCoordinateEquiv (zeroExtensionMap C D f) 0).symm
        ((zeroExtensionEquiv D 0).symm b.val,-0) +
      (coneCoordinateEquiv (zeroExtensionMap C D f) 0).symm
        ((zeroExtensionEquiv D 0).symm b'.val,-0)
    rw [← map_add]
    congr 1
    simp only [map_add, Prod.mk_add_mk, neg_zero, add_zero]
/-- 余核への降下前の標準H⁰への実加法写像。 -/
def cokernelPreinclusion : zeroCycles D →+
    (mappingCone (zeroExtensionMap C D f)).homology 0 :=
  (moduleCycleClass _).comp (zeroCycleToCone f)
/-- 前写像の値はAの同じ標準障害のz=0の場合。 -/
theorem cokernelPreinclusion_eq (b : zeroCycles D) :
    cokernelPreinclusion f b = nonnegativeObstruction f 0 b.val (map_zero _)
      (by simpa only [map_zero] using b.property) := by
  unfold cokernelPreinclusion nonnegativeObstruction specifiedObstruction
  simp only [map_zero]
  rfl
/-- 標準H⁰への前写像の核は実kの像と厳密に一致する。 -/
theorem cokernelPreinclusion_zero_iff (b : zeroCycles D) :
    cokernelPreinclusion f b = 0 ↔ b ∈ (cycleComparison f).range := by
  rw [cokernelPreinclusion_eq, nonnegativeObstruction_zero_iff_lift]
  constructor
  · rintro ⟨a⟩
    exact ⟨⟨a.val,a.property.1⟩, Subtype.ext a.property.2⟩
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val,a.property,congrArg Subtype.val ha⟩⟩
/-- Bのj。余核を独立な標準錐H⁰へ送る実加法写像。 -/
def cokernelInclusion : CorrectionCokernel f →+
    (mappingCone (zeroExtensionMap C D f)).homology 0 :=
  QuotientAddGroup.lift _ (cokernelPreinclusion f)
    (fun b hb => (cokernelPreinclusion_zero_iff f b).mpr hb)
/-- jは零次cycleの同じ代表元(b,0)を標準類へ送る。 -/
@[simp] theorem cokernelInclusion_mk (b : zeroCycles D) :
    cokernelInclusion f (QuotientAddGroup.mk' _ b) = cokernelPreinclusion f b := rfl
/-- jの単射性は標準錐での零性から実kの像を復元して導く。 -/
theorem cokernelInclusion_injective : Function.Injective (cokernelInclusion f) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply (AddSubgroup.eq_bot_iff_forall _).mpr
  intro x hx
  obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (cycleComparison f).range x
  exact (QuotientAddGroup.eq_zero_iff b).mpr
    ((cokernelPreinclusion_zero_iff f b).mp hx)

/-- 零延長された標準錐の次数0を元のD⁰×C¹として読む。 -/
def nonnegativeConeCoordinateEquiv :
    (mappingCone (zeroExtensionMap C D f)).X 0 ≃+ D.X 0 × C.X 1 where
  toFun x := (zeroExtensionEquiv D 0 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 x).1,
    zeroExtensionEquiv C 1 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 x).2)
  invFun x := (coneCoordinateEquiv (zeroExtensionMap C D f) 0).symm
    ((zeroExtensionEquiv D 0).symm x.1, (zeroExtensionEquiv C 1).symm x.2)
  left_inv x := by simp only [LinearEquiv.symm_apply_apply, Prod.mk.eta]
  right_inv x := by simp only [LinearEquiv.apply_symm_apply, Prod.mk.eta]
  map_add' x y := by simp only [map_add, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
/-- 標準錐の実cycleの元の二成分は、元の二つの閉性等式を満たす。 -/
theorem coneCycle_coordinate_closed
    (c : LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom) :
    D.d 0 1 (nonnegativeConeCoordinateEquiv f c.val).1 +
      f.f 1 (nonnegativeConeCoordinateEquiv f c.val).2 = 0 ∧
    C.d 1 2 (nonnegativeConeCoordinateEquiv f c.val).2 = 0 := by
  have hc : (mappingCone (zeroExtensionMap C D f)).d 0 1 c.val = 0 := by
    have h := c.property
    change (mappingCone (zeroExtensionMap C D f)).d 0 ((ComplexShape.up ℤ).next 0) c.val = 0 at h
    rw [ComplexShape.next_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel 0 1 by decide)] at h
    exact h
  have hd : coneCoordinateEquiv (zeroExtensionMap C D f) 1
      ((mappingCone (zeroExtensionMap C D f)).d 0 1 c.val) =
      ((zeroExtension D).d 0 1 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).1 +
        (zeroExtensionMap C D f).f 1 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2,
      -(zeroExtension C).d 1 2 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2) :=
    coneCoordinateEquiv_d_apply (zeroExtensionMap C D f) 0 c.val
  rw [hc, map_zero] at hd
  have hb := congrArg (fun x => zeroExtensionEquiv D 1 (Prod.fst x)) hd
  have hz := congrArg (fun x => zeroExtensionEquiv C 2 (Prod.snd x)) hd
  simp only [Prod.fst_zero, map_zero] at hb
  simp only [Prod.snd_zero, map_zero] at hz
  change 0 = zeroExtensionEquiv D 1
    ((zeroExtension D).d 0 1 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).1 +
      (zeroExtensionMap C D f).f 1 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2) at hb
  change 0 = zeroExtensionEquiv C 2
    (- (zeroExtension C).d 1 2 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2) at hz
  have hd0 : zeroExtensionEquiv D 1 ((zeroExtension D).d 0 1
      (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).1) =
      D.d 0 1 (zeroExtensionEquiv D 0
        (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).1) :=
    zeroExtensionEquiv_d D 0 1 _
  have hf1 : zeroExtensionEquiv D 1 ((zeroExtensionMap C D f).f 1
      (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2) =
      f.f 1 (zeroExtensionEquiv C 1
        (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2) :=
    zeroExtensionEquiv_map C D f 1 _
  have hd1 : zeroExtensionEquiv C 2 ((zeroExtension C).d 1 2
      (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2) =
      C.d 1 2 (zeroExtensionEquiv C 1
        (coneCoordinateEquiv (zeroExtensionMap C D f) 0 c.val).2) :=
    zeroExtensionEquiv_d C 1 2 _
  rw [map_add, hd0, hf1] at hb
  rw [map_neg, hd1] at hz
  exact ⟨hb.symm, neg_eq_zero.mp hz.symm⟩
/-- 標準錐cycleのsource成分を、元Cの実次数1cycleへ送る。 -/
def coneCycleProjection :
    LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom →+
      LinearMap.ker (C.sc 1).g.hom where
  toFun c := ⟨(nonnegativeConeCoordinateEquiv f c.val).2, by
    change C.d 1 ((ComplexShape.up ℕ).next 1) _ = 0
    rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 1 2 by decide)]
    exact (coneCycle_coordinate_closed f c).2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' c c' := Subtype.ext (by simp)

/-- 元の適合入力からAと同じ標準錐cycleを生成する。 -/
def nonnegativeSpecifiedCycle (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom :=
  specifiedCycle (zeroExtensionMap C D f)
    ((zeroExtensionEquiv C 1).symm z) ((zeroExtensionEquiv D 0).symm b)
    (zeroExtension_closed z hz) (zeroExtension_compatible f z b hb)
/-- 同じcycleの標準類はAの障害そのものである。 -/
theorem nonnegativeSpecifiedCycle_class (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    moduleCycleClass _ (nonnegativeSpecifiedCycle f z b hz hb) =
      nonnegativeObstruction f z b hz hb := rfl
/-- 指定cycleの元の座標は符号を含めて(b,−z)と一致する。 -/
@[simp] theorem nonnegativeSpecifiedCycle_coordinates (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    nonnegativeConeCoordinateEquiv f (nonnegativeSpecifiedCycle f z b hz hb).val = (b,-z) := by
  change (zeroExtensionEquiv D 0
      (coneCoordinateEquiv (zeroExtensionMap C D f) 0
        ((coneCoordinateEquiv (zeroExtensionMap C D f) 0).symm _)).1,
    zeroExtensionEquiv C 1
      (coneCoordinateEquiv (zeroExtensionMap C D f) 0
        ((coneCoordinateEquiv (zeroExtensionMap C D f) 0).symm _)).2) = _
  simp only [LinearEquiv.apply_symm_apply, map_neg]
/-- 任意の標準錐cycleの類零性を、元の補正の二等式へ戻す。 -/
theorem coneCycleClass_zero_iff
    (c : LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom) :
    moduleCycleClass _ c = 0 ↔ ∃ a : C.X 0,
      f.f 0 a = (nonnegativeConeCoordinateEquiv f c.val).1 ∧
      -C.d 0 1 a = (nonnegativeConeCoordinateEquiv f c.val).2 := by
  let b := (nonnegativeConeCoordinateEquiv f c.val).1
  let z := -(nonnegativeConeCoordinateEquiv f c.val).2
  have hz : C.d 1 2 z = 0 := by
    dsimp [z]; rw [map_neg, (coneCycle_coordinate_closed f c).2, neg_zero]
  have hb : D.d 0 1 b = f.f 1 z := by
    change D.d 0 1 b = f.f 1 (-(nonnegativeConeCoordinateEquiv f c.val).2)
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left (coneCycle_coordinate_closed f c).1
  have he : c = nonnegativeSpecifiedCycle f z b hz hb := by
    apply Subtype.ext
    apply (nonnegativeConeCoordinateEquiv f).injective
    rw [nonnegativeSpecifiedCycle_coordinates]
    dsimp [b,z]
    simp only [neg_neg, Prod.mk.eta]
  rw [he, nonnegativeSpecifiedCycle_class, nonnegativeObstruction_zero_iff_lift]
  constructor
  · rintro ⟨a⟩
    refine ⟨a.val, ?_, ?_⟩
    · simpa only [nonnegativeSpecifiedCycle_coordinates] using a.property.2
    · simpa only [nonnegativeSpecifiedCycle_coordinates] using congrArg Neg.neg a.property.1
  · rintro ⟨a,hfa,hda⟩
    refine ⟨⟨a, ?_, ?_⟩⟩
    · simpa only [nonnegativeSpecifiedCycle_coordinates, neg_inj] using hda
    · simpa only [nonnegativeSpecifiedCycle_coordinates] using hfa

/-- 元の非負複体H¹の標準類零性を元のd⁰へ戻す。 -/
theorem oneCycleClass_zero_iff (c : LinearMap.ker (C.sc 1).g.hom) :
    moduleCycleClass (C.sc 1) c = 0 ↔ ∃ a : C.X 0, C.d 0 1 a = c.val := by
  rw [moduleCycleClass_zero_iff]
  change (∃ a : C.X ((ComplexShape.up ℕ).prev 1),
    C.d ((ComplexShape.up ℕ).prev 1) 1 a = c.val) ↔ _
  rw [ComplexShape.prev_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 0 1 by decide)]
/-- 錐cycleを元のH¹のsource成分の類へ送る。 -/
def coneCycleProjectionClass :
    LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom →+ C.homology 1 :=
  (moduleCycleClass (C.sc 1)).comp (coneCycleProjection f)
/-- 実錐微分のsource成分は元Cの実微分なので、H¹では零になる。 -/
theorem coneCycleProjectionClass_boundary
    (x : ((mappingCone (zeroExtensionMap C D f)).sc 0).X₁) :
    coneCycleProjectionClass f
      (((mappingCone (zeroExtensionMap C D f)).sc 0).moduleCatToCycles x) = 0 := by
  let c := ((mappingCone (zeroExtensionMap C D f)).sc 0).moduleCatToCycles x
  have hc : moduleCycleClass _ c = 0 := (moduleCycleClass_zero_iff _ _).mpr ⟨x,rfl⟩
  obtain ⟨a,_,ha⟩ := (coneCycleClass_zero_iff f c).mp hc
  apply (oneCycleClass_zero_iff (coneCycleProjection f c)).mpr
  exact ⟨-a, by rw [map_neg]; exact ha⟩
/-- Bのpの、標準H¹Cへの値を持つ実加法写像。 -/
def coneProjection : (mappingCone (zeroExtensionMap C D f)).homology 0 →+ C.homology 1 :=
  moduleDescClass _ (coneCycleProjectionClass f) (coneCycleProjectionClass_boundary f)
/-- pは全ての元の標準錐cycleでsource成分の類として評価できる。 -/
@[simp] theorem coneProjection_class
    (c : LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom) :
    coneProjection f (moduleCycleClass _ c) =
      moduleCycleClass (C.sc 1) (coneCycleProjection f c) :=
  moduleDescClass_class _ _ _ c

/-- 元の次数1の閉元を標準短複体のcycleへ入れる。 -/
def oneCycle (z : C.X 1) (hz : C.d 1 2 z = 0) : LinearMap.ker (C.sc 1).g.hom :=
  ⟨z, by
    change C.d 1 ((ComplexShape.up ℕ).next 1) z = 0
    rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 1 2 by decide)]
    exact hz⟩
/-- 元の閉元の標準H¹類。 -/
def oneClass (z : C.X 1) (hz : C.d 1 2 z = 0) : C.homology 1 :=
  moduleCycleClass (C.sc 1) (oneCycle z hz)
/-- Bの符号条件。pは指定障害を元の−[z]へ送る。 -/
theorem coneProjection_obstruction (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    coneProjection f (nonnegativeObstruction f z b hz hb) = -oneClass z hz := by
  rw [← nonnegativeSpecifiedCycle_class, coneProjection_class]
  change moduleCycleClass (C.sc 1) _ = -moduleCycleClass (C.sc 1) _
  rw [← map_neg]
  congr 1
  apply Subtype.ext
  exact congrArg Prod.snd (nonnegativeSpecifiedCycle_coordinates f z b hz hb)
/-- pの値は同じ標準H¹比較の実kernelに属する。 -/
theorem coneProjection_mem_kernel
    (x : (mappingCone (zeroExtensionMap C D f)).homology 0) : homologyMap f 1 (coneProjection f x) = 0 := by
  obtain ⟨c,rfl⟩ := moduleCycleClass_surjective ((mappingCone (zeroExtensionMap C D f)).sc 0) x
  rw [coneProjection_class]
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ 1).map f) _ = 0
  rw [moduleCycleClass_naturality]
  apply (oneCycleClass_zero_iff _).mpr
  refine ⟨-(nonnegativeConeCoordinateEquiv f c.val).1, ?_⟩
  change D.d 0 1 (-(nonnegativeConeCoordinateEquiv f c.val).1) =
    f.f 1 (nonnegativeConeCoordinateEquiv f c.val).2
  rw [map_neg]
  exact neg_eq_of_add_eq_zero_right (coneCycle_coordinate_closed f c).1
/-- Bのpは実H¹比較のkernelを終域に持つ。 -/
def coneKernelProjection : (mappingCone (zeroExtensionMap C D f)).homology 0 →+
    (homologyMap f 1).hom.toAddMonoidHom.ker where
  toFun x := ⟨coneProjection f x, coneProjection_mem_kernel f x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)
/-- H¹比較で零になる任意の類から錐の類を復元し、pの全射性を示す。 -/
theorem coneKernelProjection_surjective : Function.Surjective (coneKernelProjection f) := by
  intro y
  obtain ⟨c,hc⟩ := moduleCycleClass_surjective (C.sc 1) y.val
  have hy : homologyMap f 1 (moduleCycleClass (C.sc 1) c) = 0 := by rw [hc]; exact y.property
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ 1).map f) _ = 0 at hy
  rw [moduleCycleClass_naturality, oneCycleClass_zero_iff] at hy
  obtain ⟨b,hb⟩ := hy
  have hz : C.d 1 2 c.val = 0 := by
    have h := c.property
    change C.d 1 ((ComplexShape.up ℕ).next 1) c.val = 0 at h
    rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 1 2 by decide)] at h
    exact h
  have hzn : C.d 1 2 (-c.val) = 0 := by rw [map_neg,hz,neg_zero]
  have hbn : D.d 0 1 (-b) = f.f 1 (-c.val) := by
    change D.d 0 1 b = f.f 1 c.val at hb
    rw [map_neg,map_neg,hb]
  refine ⟨nonnegativeObstruction f (-c.val) (-b) hzn hbn, ?_⟩
  apply Subtype.ext
  change coneProjection f _ = y.val
  rw [coneProjection_obstruction, ← hc]
  change -moduleCycleClass (C.sc 1) _ = moduleCycleClass (C.sc 1) c
  rw [← map_neg]
  congr 1
  apply Subtype.ext
  exact neg_neg c.val

/-- jの代表cycleは元の座標で(b,0)。 -/
@[simp] theorem zeroCycleToCone_coordinates (b : zeroCycles D) :
    nonnegativeConeCoordinateEquiv f (zeroCycleToCone f b).val = (b.val,0) := by
  have he : zeroCycleToCone f b = nonnegativeSpecifiedCycle f 0 b.val (map_zero _)
      (by simpa only [map_zero] using b.property) := by
    unfold zeroCycleToCone nonnegativeSpecifiedCycle
    simp only [map_zero]
    rfl
  rw [he, nonnegativeSpecifiedCycle_coordinates, neg_zero]
/-- 残差をjで標準錐へ送ると、選択前の指定障害そのものになる。 -/
theorem cokernelInclusion_residual (z : C.X 1) (b : D.X 0) (a₀ : C.X 0)
    (hz : C.d 1 2 z = 0) (ha₀ : C.d 0 1 a₀ = z) (hb : D.d 0 1 b = f.f 1 z) :
    cokernelInclusion f (residualClass f z b a₀ ha₀ hb) = nonnegativeObstruction f z b hz hb := by
  change moduleCycleClass _ (zeroCycleToCone f (residualCycle f z b a₀ ha₀ hb)) =
    moduleCycleClass _ (nonnegativeSpecifiedCycle f z b hz hb)
  rw [← sub_eq_zero, ← map_sub, coneCycleClass_zero_iff]
  have hc : nonnegativeConeCoordinateEquiv f
      (zeroCycleToCone f (residualCycle f z b a₀ ha₀ hb) - nonnegativeSpecifiedCycle f z b hz hb).val =
      (b - f.f 0 a₀, 0) - (b,-z) := by
    change nonnegativeConeCoordinateEquiv f
      ((zeroCycleToCone f (residualCycle f z b a₀ ha₀ hb)).val -
        (nonnegativeSpecifiedCycle f z b hz hb).val) = _
    rw [map_sub, zeroCycleToCone_coordinates, nonnegativeSpecifiedCycle_coordinates]
    rfl
  rw [hc]
  refine ⟨-a₀, ?_, ?_⟩
  · simp only [map_neg, Prod.fst_sub]
    abel
  · simp only [map_neg, ha₀, neg_neg, Prod.snd_sub, zero_sub]
/-- pが零であることは、同じjの像に属することと同値。 -/
theorem coneProjection_zero_iff (x : (mappingCone (zeroExtensionMap C D f)).homology 0) :
    coneProjection f x = 0 ↔ ∃ q : CorrectionCokernel f, cokernelInclusion f q = x := by
  constructor
  · intro hx
    obtain ⟨c,rfl⟩ := moduleCycleClass_surjective ((mappingCone (zeroExtensionMap C D f)).sc 0) x
    rw [coneProjection_class, oneCycleClass_zero_iff] at hx
    obtain ⟨a,ha⟩ := hx
    change C.d 0 1 a = (nonnegativeConeCoordinateEquiv f c.val).2 at ha
    let b : zeroCycles D := ⟨(nonnegativeConeCoordinateEquiv f c.val).1 + f.f 0 a, by
      change D.d 0 1 (_ + _) = 0
      have hf := congrArg (fun g : C.X 0 ⟶ D.X 1 => g a) (f.comm 0 1)
      change D.d 0 1 (f.f 0 a) = f.f 1 (C.d 0 1 a) at hf
      rw [map_add, hf, ha]
      exact (coneCycle_coordinate_closed f c).1⟩
    refine ⟨QuotientAddGroup.mk' _ b, ?_⟩
    change moduleCycleClass _ (zeroCycleToCone f b) = moduleCycleClass _ c
    rw [← sub_eq_zero, ← map_sub, coneCycleClass_zero_iff]
    have hc : nonnegativeConeCoordinateEquiv f (zeroCycleToCone f b - c).val =
        (b.val,0) - nonnegativeConeCoordinateEquiv f c.val := by
      change nonnegativeConeCoordinateEquiv f ((zeroCycleToCone f b).val - c.val) = _
      rw [map_sub, zeroCycleToCone_coordinates]
    rw [hc]
    refine ⟨a, ?_, ?_⟩
    · change f.f 0 a = ((nonnegativeConeCoordinateEquiv f c.val).1 + f.f 0 a) -
        (nonnegativeConeCoordinateEquiv f c.val).1
      abel
    · simpa only [Prod.snd_sub, Prod.snd, zero_sub, neg_inj] using ha
  · rintro ⟨q,rfl⟩
    obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (cycleComparison f).range q
    change coneProjection f (moduleCycleClass _ (zeroCycleToCone f b)) = 0
    rw [coneProjection_class]
    have hc : coneCycleProjection f (zeroCycleToCone f b) = 0 := by
      apply Subtype.ext
      exact congrArg Prod.snd (zeroCycleToCone_coordinates f b)
    rw [hc,map_zero]

/-- 同じj,pは標準H⁰において完全である。 -/
theorem cokernel_kernel_exact : Function.Exact (cokernelInclusion f) (coneKernelProjection f) := by
  intro x
  have hz : coneKernelProjection f x = 0 ↔ coneProjection f x = 0 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact hz.trans (coneProjection_zero_iff f x)
/-- Bの実短完全列。各射は上で元の複体から構成したj,pである。 -/
theorem correction_short_exact :
    Function.Injective (cokernelInclusion f) ∧
    Function.Exact (cokernelInclusion f) (coneKernelProjection f) ∧
    Function.Surjective (coneKernelProjection f) :=
  ⟨cokernelInclusion_injective f, cokernel_kernel_exact f, coneKernelProjection_surjective f⟩
/-- 零微分整数複体の元1は元の標準H¹で非零。 -/
theorem integer_oneClass_ne_zero :
    oneClass (C := integerZeroDifferential) (1 : ℤ)
      (by rw [integerZeroDifferential_d]; rfl) ≠ 0 := by
  intro h
  obtain ⟨a,ha⟩ := (oneCycleClass_zero_iff _).mp h
  rw [integerZeroDifferential_d] at ha
  change (0 : ℤ) = 1 at ha
  exact zero_ne_one ha
/-- 同じ整数零比較でpは非零のH¹類を実際に回収する。指定Wの代替ではない。 -/
theorem integer_projection_nonzero :
    coneProjection (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      (nonnegativeObstruction 0 (1 : ℤ) (0 : ℤ)
        (by rw [integerZeroDifferential_d]; rfl) (by rw [integerZeroDifferential_d]; rfl)) ≠ 0 := by
  rw [coneProjection_obstruction, neg_ne_zero]
  exact integer_oneClass_ne_zero
/-- 同じ整数零比較ではjも非零の指定残差を保持する。 -/
theorem integer_residual_inclusion_nonzero :
    cokernelInclusion (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      (residualClass 0 (0 : ℤ) (1 : ℤ) (0 : ℤ)
        (map_zero _) zero_comparison_compatible) ≠ 0 := by
  rw [cokernelInclusion_residual _ _ _ _ (map_zero _)]
  exact zero_comparison_obstruction_ne_zero

end AAT.AG.SpecifiedRepairLifting
#print axioms AAT.AG.SpecifiedRepairLifting.moduleCycleClass
#print axioms AAT.AG.SpecifiedRepairLifting.moduleCycleClass_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.moduleCycleClass_eq_iff
#print axioms AAT.AG.SpecifiedRepairLifting.moduleCycleClass_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.moduleDescClass
#print axioms AAT.AG.SpecifiedRepairLifting.moduleDescClass_class
#print axioms AAT.AG.SpecifiedRepairLifting.moduleCycleMap
#print axioms AAT.AG.SpecifiedRepairLifting.moduleCycles_inv_i
#print axioms AAT.AG.SpecifiedRepairLifting.moduleCycleClass_naturality
#print axioms AAT.AG.SpecifiedRepairLifting.CorrectionCokernel
#print axioms AAT.AG.SpecifiedRepairLifting.residualClass
#print axioms AAT.AG.SpecifiedRepairLifting.residualClass_independent
#print axioms AAT.AG.SpecifiedRepairLifting.residualClass_zero_iff_lift
#print axioms AAT.AG.SpecifiedRepairLifting.zeroCycleToCone
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelPreinclusion
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelPreinclusion_eq
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelPreinclusion_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelInclusion
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelInclusion_mk
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelInclusion_injective
#print axioms AAT.AG.SpecifiedRepairLifting.nonnegativeConeCoordinateEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.coneCycle_coordinate_closed
#print axioms AAT.AG.SpecifiedRepairLifting.coneCycleProjection
#print axioms AAT.AG.SpecifiedRepairLifting.nonnegativeSpecifiedCycle
#print axioms AAT.AG.SpecifiedRepairLifting.nonnegativeSpecifiedCycle_class
#print axioms AAT.AG.SpecifiedRepairLifting.nonnegativeSpecifiedCycle_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.coneCycleClass_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.oneCycleClass_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.coneCycleProjectionClass
#print axioms AAT.AG.SpecifiedRepairLifting.coneCycleProjectionClass_boundary
#print axioms AAT.AG.SpecifiedRepairLifting.coneProjection
#print axioms AAT.AG.SpecifiedRepairLifting.coneProjection_class
#print axioms AAT.AG.SpecifiedRepairLifting.oneCycle
#print axioms AAT.AG.SpecifiedRepairLifting.oneClass
#print axioms AAT.AG.SpecifiedRepairLifting.coneProjection_obstruction
#print axioms AAT.AG.SpecifiedRepairLifting.coneProjection_mem_kernel
#print axioms AAT.AG.SpecifiedRepairLifting.coneKernelProjection
#print axioms AAT.AG.SpecifiedRepairLifting.coneKernelProjection_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.zeroCycleToCone_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelInclusion_residual
#print axioms AAT.AG.SpecifiedRepairLifting.coneProjection_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.cokernel_kernel_exact
#print axioms AAT.AG.SpecifiedRepairLifting.correction_short_exact
#print axioms AAT.AG.SpecifiedRepairLifting.integer_oneClass_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.integer_projection_nonzero
#print axioms AAT.AG.SpecifiedRepairLifting.integer_residual_inclusion_nonzero
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting
