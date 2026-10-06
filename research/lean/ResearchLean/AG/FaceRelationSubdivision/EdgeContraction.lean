import ResearchLean.AG.FaceRelationSubdivision.EdgeSubdivision
import ResearchLean.AG.FaceRelationSubdivision.SubsetContraction

/-!
# 面付き辺分割の全出現の切断と補正

## Implementation notes

s2は中心面に第0・第2出現を加え、第1出現を引く。出現名には面と位置を
含めるため、同じ辺の繰返しにもこの三つの有限和をそのまま用いる。
基底像と台包含だけからr/s/hを作り、chain式を全セルで検査して全Aへ制限する。
-/
noncomputable section
open scoped Classical
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)

/-- 原始収縮の頂点像。 -/
def r0 := (collapse N e).basis0
/-- 原始収縮の辺像。 -/
def r1 := (collapse N e).basis1
/-- 原始収縮の面像。 -/
def r2 := (collapse N e).basis2

/-- 旧頂点名を保つ切断。 -/
def s0 : SupportedBasisMap N.chartSupport (supported N e).chartSupport :=
  SupportedBasisMap.ofSingle Sum.inl (by intro v t ht; exact ht)

/-- 旧辺をc+bへ送る切断。保持辺は同じ名前である。 -/
def s1 : SupportedBasisMap N.edgeSupport (supported N e).edgeSupport := by
  classical
  exact {
    basisImage a := if h : a = e then Finsupp.single (.inr (.inl false)) 1 +
      Finsupp.single (.inr (.inl true)) 1 else Finsupp.single (.inl ⟨a, h⟩) 1
    support_compatible := by
      intro a j hj t ht
      split_ifs at hj with h
      · subst a
        by_cases hc : j = .inr (.inl false)
        · subst j; rw [edgeSupport_c]; exact (N.mem_edgeSupport_iff e t).mp ht |>.1
        · by_cases hb : j = .inr (.inl true)
          · subst j; rw [edgeSupport_b]; exact ht
          · simp [hc, hb] at hj
      · have hj' : j = .inl ⟨a, h⟩ := by
          by_contra hn; simp [hn] at hj
        subst j
        rw [edgeSupport_old]
        exact ht }

/-- 中心面の単一像。 -/
def centerSection : SupportedBasisMap N.faceSupport (supported N e).faceSupport :=
  SupportedBasisMap.ofSingle Sum.inl (by intro F t ht; rw [faceSupport_center]; exact ht)

/-- 一つの位置の出現を追加面へ送る原始像。 -/
def slotSection (i : Fin 3) : SupportedBasisMap N.faceSupport (supported N e).faceSupport := by
  classical
  exact SupportedBasisMap.ofOption
    (fun F => if h : faceSlot N F i = e then some (.inr ⟨(F,i), h⟩) else none)
    (by
      intro F G hG t ht
      dsimp only at hG
      split_ifs at hG with h
      · cases Option.some.inj hG
        rw [faceSupport_triangle, ← h]
        fin_cases i
        · exact (N.mem_faceSupport_iff F t).mp ht |>.1
        · exact (N.mem_faceSupport_iff F t).mp ht |>.2.1
        · exact (N.mem_faceSupport_iff F t).mp ht |>.2.2
      )

/-- 各旧面を中心面と三つの符号付き出現の有限和へ送る。 -/
def s2 := ((centerSection N e).add (slotSection N e 0)).add
  ((slotSection N e 1).neg) |>.add (slotSection N e 2)

/-- 新頂点をcへ送る補正。 -/
def h0 : SupportedBasisMap (supported N e).chartSupport (supported N e).edgeSupport :=
  SupportedBasisMap.ofOption (fun v => match v with
    | .inl _ => none | .inr _ => some (.inr (.inl false))) (by
      rintro (v | x) a ha t ht
      · cases ha
      · cases x; cases Option.some.inj ha
        simpa only [chartSupport_new, edgeSupport_c] using ht)

/-- 各対角辺をその出現の追加面の負へ送る補正。 -/
def h1 : SupportedBasisMap (supported N e).edgeSupport (supported N e).faceSupport :=
  (SupportedBasisMap.ofOption (fun a => match a with
    | .inl _ => none | .inr (.inl _) => none | .inr (.inr o) => some (.inr o)) (by
      rintro (a | (b | o)) F hF t ht
      · cases hF
      · cases hF
      · cases Option.some.inj hF
        simpa only [edgeSupport_diagonal, faceSupport_triangle] using ht)).neg

/-- 収縮の頂点基底像。 -/
@[simp] theorem r0_basis (v : (supported N e).nerve.Chart) :
    (r0 N e).basisImage v = Finsupp.single (chartImage N e v) 1 := rfl
/-- 収縮の辺基底像。 -/
@[simp] theorem r1_basis (a : Edge N e) :
    (r1 N e).basisImage a = rationalOptionCell (edgeImage N e a) := rfl
/-- 収縮の面基底像。 -/
@[simp] theorem r2_basis (F : Face N e) :
    (r2 N e).basisImage F = rationalOptionCell (faceImage N e F) := rfl
/-- 頂点切断の基底像。 -/
@[simp] theorem s0_basis (v : N.nerve.Chart) :
    (s0 N e).basisImage v = Finsupp.single (.inl v) 1 := rfl
/-- 分割辺の切断基底像。 -/
@[simp] theorem s1_target_basis : (s1 N e).basisImage e =
    Finsupp.single (.inr (.inl false)) 1 + Finsupp.single (.inr (.inl true)) 1 := by
  classical
  simp [s1]
/-- 保持辺の切断基底像。 -/
@[simp] theorem s1_retained_basis (a : RetainedEdge N e) :
    (s1 N e).basisImage a.1 = Finsupp.single (.inl a) 1 := by
  classical
  simp [s1, a.2]
/-- 中心面切断の基底像。 -/
@[simp] theorem centerSection_basis (F : N.nerve.FaceComponent) :
    (centerSection N e).basisImage F = Finsupp.single (.inl F) 1 := rfl
/-- 一つの出現の切断基底像。 -/
@[simp] theorem slotSection_basis (F : N.nerve.FaceComponent) (i : Fin 3) :
    (slotSection N e i).basisImage F =
      (if h : faceSlot N F i = e then Finsupp.single (.inr ⟨(F,i),h⟩) 1 else (0 : Face N e →₀ ℚ)) := by
  classical
  dsimp [slotSection]; split_ifs <;> rfl
/-- 面切断の符号付き有限和。 -/
theorem s2_basis (F : N.nerve.FaceComponent) :
    (s2 N e).basisImage F = Finsupp.single (.inl F) 1 +
      (slotSection N e 0).basisImage F - (slotSection N e 1).basisImage F +
      (slotSection N e 2).basisImage F := by
  simp only [s2, SupportedBasisMap.add_basis, SupportedBasisMap.neg_basis,
    centerSection_basis, sub_eq_add_neg]
/-- 頂点補正の旧セル像。 -/
@[simp] theorem h0_old_basis (v : N.nerve.Chart) : (h0 N e).basisImage (.inl v) = 0 := rfl
/-- 頂点補正の新セル像。 -/
@[simp] theorem h0_new_basis : (h0 N e).basisImage (.inr PUnit.unit) =
    Finsupp.single (.inr (.inl false)) 1 := rfl
/-- 辺補正の保持セル像。 -/
@[simp] theorem h1_old_basis (a : RetainedEdge N e) : (h1 N e).basisImage (.inl a) = 0 := by
  simp [h1, SupportedBasisMap.neg_basis, SupportedBasisMap.ofOption_basis]
/-- 辺補正の分割セル像。 -/
@[simp] theorem h1_segment_basis (b : Bool) : (h1 N e).basisImage (.inr (.inl b)) = 0 := by
  simp [h1, SupportedBasisMap.neg_basis, SupportedBasisMap.ofOption_basis]
/-- 辺補正の対角セル像。 -/
@[simp] theorem h1_diagonal_basis (o : Occurrence N e) :
    (h1 N e).basisImage (.inr (.inr o)) = -Finsupp.single (.inr o) 1 := rfl

/-- rとsの頂点往復。 -/
theorem rs0 : (r0 N e).raw.comp (s0 N e).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  simp [LinearMap.comp_apply, SupportedBasisMap.raw_single, Finsupp.smul_single]

/-- rとsの辺往復。 -/
theorem rs1 : (r1 N e).raw.comp (s1 N e).raw = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro v a
  by_cases hv : v = e
  · subst v
    simp [LinearMap.comp_apply, SupportedBasisMap.raw_single, smul_add,
      Finsupp.smul_single]
  · have he : v = (⟨v,hv⟩ : RetainedEdge N e).1 := rfl
    have hs := s1_retained_basis N e ⟨v,hv⟩
    simp [hs, LinearMap.comp_apply, SupportedBasisMap.raw_single, Finsupp.smul_single]


/-- rとsの面往復。追加面の原始像は零。 -/
theorem rs2 : (r2 N e).raw.comp (s2 N e).raw = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro F a
  simp [LinearMap.comp_apply, SupportedBasisMap.raw_single, s2_basis, slotSection_basis,
    smul_add, smul_sub, Finsupp.smul_single]
  split_ifs <;> simp [SupportedBasisMap.raw_single]

/-- 収縮は辺境界と可換。 -/
theorem r_comm01 : (TargetSupportedNerve.rawD1 N).raw.comp (r1 N e).raw =
    (r0 N e).raw.comp (TargetSupportedNerve.rawD1 (supported N e)).raw := by
  apply Finsupp.lhom_ext
  rintro (a | (b | o)) x
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single]
  · cases b <;> simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single]
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single]

/-- 収縮は面境界と可換。中心面はslot番号を保つ。 -/
theorem r_comm12 : (TargetSupportedNerve.rawD2 N).raw.comp (r2 N e).raw =
    (r1 N e).raw.comp (TargetSupportedNerve.rawD2 (supported N e)).raw := by
  apply Finsupp.lhom_ext
  rintro (F | o) a
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, Finsupp.smul_single]
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, Finsupp.smul_single]

/-- 切断は辺境界と可換。分割辺では中間頂点が相殺される。 -/
theorem s_comm01 : (TargetSupportedNerve.rawD1 (supported N e)).raw.comp (s1 N e).raw =
    (s0 N e).raw.comp (TargetSupportedNerve.rawD1 N).raw := by
  classical
  apply Finsupp.lhom_ext
  intro a x
  by_cases ha : a = e
  · subst a
    simp [LinearMap.comp_apply, SupportedBasisMap.raw_single, smul_add,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single, smul_sub]
  · have hs := s1_retained_basis N e ⟨a,ha⟩
    simp [hs, LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single]

/-- 各slotの三角面境界は、切断辺と中心辺の差である。 -/
theorem slot_boundary (F : N.nerve.FaceComponent) (i : Fin 3) :
    (TargetSupportedNerve.rawD2 (supported N e)).raw ((slotSection N e i).basisImage F) =
      (s1 N e).basisImage (faceSlot N F i) -
        (Finsupp.single (centerEdge N e F i) 1 : (supported N e).nerve.EdgeComponent →₀ ℚ) := by
  classical
  by_cases h : faceSlot N F i = e
  · rw [centerEdge_of_eq N e F i h]
    simp [slotSection_basis, h, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis]
    abel
  · have hs := s1_retained_basis N e ⟨faceSlot N F i,h⟩
    rw [centerEdge_of_ne N e F i h]
    simp [slotSection_basis, h, hs]

/-- 全出現の符号付き和により切断は面境界と可換。 -/
theorem s_comm12 : (TargetSupportedNerve.rawD2 (supported N e)).raw.comp (s2 N e).raw =
    (s1 N e).raw.comp (TargetSupportedNerve.rawD2 N).raw := by
  apply Finsupp.lhom_ext
  intro F x
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, s2_basis,
    map_smul, map_add, map_sub, slot_boundary, TargetSupportedNerve.rawD2_basis,
    faceEdge0_center, faceEdge1_center, faceEdge2_center, faceSlot_zero, faceSlot_one,
    faceSlot_two, smul_add, smul_sub, SupportedBasisMap.raw_single, one_smul]
  abel

/-- 各中心slotの補正は、その出現の三角面の負である。 -/
theorem h1_center (F : N.nerve.FaceComponent) (i : Fin 3) :
    (h1 N e).basisImage (centerEdge N e F i) = -(slotSection N e i).basisImage F := by
  classical
  by_cases h : faceSlot N F i = e
  · rw [centerEdge_of_eq N e F i h]
    simp [slotSection_basis, h]
  · rw [centerEdge_of_ne N e F i h]
    simp [slotSection_basis, h]

/-- 頂点の収縮補正式。 -/
theorem sr_h0 : (s0 N e).raw.comp (r0 N e).raw +
    (TargetSupportedNerve.rawD1 (supported N e)).raw.comp (h0 N e).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro (v | x) a
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single]
  · cases x
    simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single, smul_sub]

/-- 辺の収縮補正式。各対角辺は自分の出現の三角面だけを使う。 -/
theorem sr_h1 : (s1 N e).raw.comp (r1 N e).raw +
    (TargetSupportedNerve.rawD2 (supported N e)).raw.comp (h1 N e).raw +
    (h0 N e).raw.comp (TargetSupportedNerve.rawD1 (supported N e)).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro (v | (b | o)) a
  · have hs := s1_retained_basis N e v
    simp [hs, LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single, smul_sub]
  · cases b <;> simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single, smul_sub, smul_add]
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, TargetSupportedNerve.rawD2_basis,
      Finsupp.smul_single, smul_sub, smul_add]
    abel

/-- 面の収縮補正式。中心面の三位置と追加面をすべて検査する。 -/
theorem sr_h2 : (s2 N e).raw.comp (r2 N e).raw +
    (h1 N e).raw.comp (TargetSupportedNerve.rawD2 (supported N e)).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro (F | o) a
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, SupportedBasisMap.raw_single,
      r2_basis, faceImage_center, rationalOptionCell_some, map_smul, s2_basis,
      TargetSupportedNerve.rawD2_basis, faceEdge0_center, faceEdge1_center, faceEdge2_center,
      map_add, map_sub]
    rw [h1_center, h1_center, h1_center]
    simp only [smul_add, smul_sub, smul_neg, one_smul, Finsupp.smul_single,
      smul_eq_mul, mul_one, LinearMap.id_apply]
    abel
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, Finsupp.smul_single, smul_sub, smul_add]


/-- 任意Aに対する収縮の同じ実subset Hom。 -/
def rHom (A : Set q.Target) :
    ThreeCochainComplex.Hom (N.targetSubsetComplex A) ((supported N e).targetSubsetComplex A) :=
  dualSubsetHom A A ((r0 N e).selected A) ((r1 N e).selected A) ((r2 N e).selected A)
    (by
      simpa only [TargetSupportedNerve.selected_rawD1] using
        (SupportedBasisMap.selected_square_of_raw_square (r1 N e) (r0 N e)
        (TargetSupportedNerve.rawD1 (supported N e)) (TargetSupportedNerve.rawD1 N)
          (r_comm01 N e) A))
    (by
      simpa only [TargetSupportedNerve.selected_rawD2] using
        (SupportedBasisMap.selected_square_of_raw_square (r2 N e) (r1 N e)
        (TargetSupportedNerve.rawD2 (supported N e)) (TargetSupportedNerve.rawD2 N)
          (r_comm12 N e) A))

/-- 任意Aに対する切断の同じ実subset Hom。 -/
def sHom (A : Set q.Target) :
    ThreeCochainComplex.Hom ((supported N e).targetSubsetComplex A) (N.targetSubsetComplex A) :=
  dualSubsetHom A A ((s0 N e).selected A) ((s1 N e).selected A) ((s2 N e).selected A)
    (by
      simpa only [TargetSupportedNerve.selected_rawD1] using
        (SupportedBasisMap.selected_square_of_raw_square (s1 N e) (s0 N e)
        (TargetSupportedNerve.rawD1 N) (TargetSupportedNerve.rawD1 (supported N e))
          (s_comm01 N e) A))
    (by
      simpa only [TargetSupportedNerve.selected_rawD2] using
        (SupportedBasisMap.selected_square_of_raw_square (s2 N e) (s1 N e)
        (TargetSupportedNerve.rawD2 N) (TargetSupportedNerve.rawD2 (supported N e))
          (s_comm12 N e) A))

/-- 任意Aの頂点往復は恒等。 -/
theorem selected_rs0 (A : Set q.Target) :
    ((r0 N e).selected A).comp ((s0 N e).selected A) = LinearMap.id :=
  SupportedBasisMap.selected_comp_eq_identity _ _ (rs0 N e) A

/-- 任意Aの辺往復は恒等。 -/
theorem selected_rs1 (A : Set q.Target) :
    ((r1 N e).selected A).comp ((s1 N e).selected A) = LinearMap.id :=
  SupportedBasisMap.selected_comp_eq_identity _ _ (rs1 N e) A

/-- 任意Aの面往復は恒等。 -/
theorem selected_rs2 (A : Set q.Target) :
    ((r2 N e).selected A).comp ((s2 N e).selected A) = LinearMap.id :=
  SupportedBasisMap.selected_comp_eq_identity _ _ (rs2 N e) A


/-- 任意Aで頂点の補正式を同じ原始像から制限する。 -/
theorem selected_sr_h0 (A : Set q.Target) :
    ((s0 N e).selected A).comp ((r0 N e).selected A) +
    (chainD1 (supported N e) A).comp ((h0 N e).selected A) = LinearMap.id := by
  have hraw : ((r0 N e).comp (s0 N e) |>.add
      ((h0 N e).comp (TargetSupportedNerve.rawD1 (supported N e)))).raw =
      (SupportedBasisMap.identity (supported N e).chartSupport).raw := by
    rw [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp,
      SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity]
    exact sr_h0 N e
  have h := SupportedBasisMap.selected_eq_of_raw_eq _ _ hraw A
  simpa only [SupportedBasisMap.selected_add, SupportedBasisMap.selected_comp,
    SupportedBasisMap.selected_identity, TargetSupportedNerve.selected_rawD1] using h

/-- 任意Aで辺の補正式を同じ原始像から制限する。 -/
theorem selected_sr_h1 (A : Set q.Target) :
    ((s1 N e).selected A).comp ((r1 N e).selected A) +
    (chainD2 (supported N e) A).comp ((h1 N e).selected A) +
    ((h0 N e).selected A).comp (chainD1 (supported N e) A) = LinearMap.id := by
  have hraw : (((r1 N e).comp (s1 N e)).add
      ((h1 N e).comp (TargetSupportedNerve.rawD2 (supported N e))) |>.add
      ((TargetSupportedNerve.rawD1 (supported N e)).comp (h0 N e))).raw =
      (SupportedBasisMap.identity (supported N e).edgeSupport).raw := by
    rw [SupportedBasisMap.raw_add, SupportedBasisMap.raw_add,
      SupportedBasisMap.raw_comp, SupportedBasisMap.raw_comp,
      SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity]
    exact sr_h1 N e
  have h := SupportedBasisMap.selected_eq_of_raw_eq _ _ hraw A
  simpa only [SupportedBasisMap.selected_add, SupportedBasisMap.selected_comp,
    SupportedBasisMap.selected_identity, TargetSupportedNerve.selected_rawD1,
    TargetSupportedNerve.selected_rawD2] using h

/-- 任意Aで面の補正式を同じ原始像から制限する。 -/
theorem selected_sr_h2 (A : Set q.Target) :
    ((s2 N e).selected A).comp ((r2 N e).selected A) +
    ((h1 N e).selected A).comp (chainD2 (supported N e) A) = LinearMap.id := by
  have hraw : ((r2 N e).comp (s2 N e) |>.add
      ((TargetSupportedNerve.rawD2 (supported N e)).comp (h1 N e))).raw =
      (SupportedBasisMap.identity (supported N e).faceSupport).raw := by
    rw [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp,
      SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity]
    exact sr_h2 N e
  have h := SupportedBasisMap.selected_eq_of_raw_eq _ _ hraw A
  simpa only [SupportedBasisMap.selected_add, SupportedBasisMap.selected_comp,
    SupportedBasisMap.selected_identity, TargetSupportedNerve.selected_rawD2] using h


/-- 原始面付き辺分割から全fieldを生成した支持chain収縮の出力。 -/
def chainContraction (A : Set q.Target) : SubsetChainContraction N (supported N e) A A where
  r0 := (r0 N e).selected A
  r1 := (r1 N e).selected A
  r2 := (r2 N e).selected A
  s0 := (s0 N e).selected A
  s1 := (s1 N e).selected A
  s2 := (s2 N e).selected A
  h0 := (h0 N e).selected A
  h1 := (h1 N e).selected A
  r_comm01 := by simpa only [TargetSupportedNerve.selected_rawD1] using
    (SupportedBasisMap.selected_square_of_raw_square (r1 N e) (r0 N e)
      (TargetSupportedNerve.rawD1 (supported N e)) (TargetSupportedNerve.rawD1 N) (r_comm01 N e) A)
  r_comm12 := by simpa only [TargetSupportedNerve.selected_rawD2] using
    (SupportedBasisMap.selected_square_of_raw_square (r2 N e) (r1 N e)
      (TargetSupportedNerve.rawD2 (supported N e)) (TargetSupportedNerve.rawD2 N) (r_comm12 N e) A)
  s_comm01 := by simpa only [TargetSupportedNerve.selected_rawD1] using
    (SupportedBasisMap.selected_square_of_raw_square (s1 N e) (s0 N e)
      (TargetSupportedNerve.rawD1 N) (TargetSupportedNerve.rawD1 (supported N e)) (s_comm01 N e) A)
  s_comm12 := by simpa only [TargetSupportedNerve.selected_rawD2] using
    (SupportedBasisMap.selected_square_of_raw_square (s2 N e) (s1 N e)
      (TargetSupportedNerve.rawD2 N) (TargetSupportedNerve.rawD2 (supported N e)) (s_comm12 N e) A)
  rs0 := selected_rs0 N e A
  rs1 := selected_rs1 N e A
  rs2 := selected_rs2 N e A
  sr_h0 := selected_sr_h0 N e A
  sr_h1 := selected_sr_h1 N e A
  sr_h2 := selected_sr_h2 N e A

/-- 同じ原始r/s/hから得た全Aの標準cochainホモトピー同値。 -/
def cochainHomotopyEquiv (A : Set q.Target) := (chainContraction N e A).cochainHomotopyEquiv

/-- 構成したrの実Homは原始collapseから独立生成した同じ比較である。 -/
theorem rHom_eq_generated (A : Set q.Target) :
    rHom N e A = (collapse N e).targetSubsetComparisonHom A A
      (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  change (collapse N e).basisHom A = _
  exact (collapse N e).basisHom_eq_generated A

/-- 出力recordのrHomは全次数で同じ原始収縮Hom。 -/
theorem chainContraction_rHom (A : Set q.Target) : (chainContraction N e A).rHom = rHom N e A := rfl

/-- 出力recordのsHomは全次数で同じ原始切断Hom。 -/
theorem chainContraction_sHom (A : Set q.Target) : (chainContraction N e A).sHom = sHom N e A := rfl

/-- 原始面付き辺分割の実比較の全標準次数同型。 -/
def homologyIso (A : Set q.Target) (n : ℤ) := (chainContraction N e A).homologyIso n

/-- 同型の順方向は同じ実生成比較のhomology mapである。 -/
theorem homologyIso_hom (A : Set q.Target) (n : ℤ) :
    (homologyIso N e A n).hom = HomologicalComplex.homologyMap
      (zeroExtensionMap ((collapse N e).targetSubsetComparisonHom A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A))) n := by
  rw [homologyIso, SubsetChainContraction.homologyIso_hom,
    chainContraction_rHom, rHom_eq_generated]

/-- 既存H1商上の実比較の同型。 -/
def oldH1ComparisonIso (A : Set q.Target) := (chainContraction N e A).oldH1ComparisonIso

/-- H1同型の順方向も既存実診断の同じh1Mapである。 -/
theorem oldH1ComparisonIso_hom (A : Set q.Target) :
    (oldH1ComparisonIso N e A).hom = ModuleCat.ofHom
      ((collapse N e).targetSubsetComparisonHom A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A)).h1Map := by
  rw [oldH1ComparisonIso, SubsetChainContraction.oldH1ComparisonIso_hom,
    chainContraction_rHom, rHom_eq_generated]

end EdgeSubdivision
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
