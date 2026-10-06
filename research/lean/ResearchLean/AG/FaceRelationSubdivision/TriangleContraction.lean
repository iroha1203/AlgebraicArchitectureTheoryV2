import ResearchLean.AG.FaceRelationSubdivision.TriangleGeometry
import ResearchLean.AG.FaceRelationSubdivision.IncidenceBasis
import ResearchLean.AG.FaceRelationSubdivision.SubsetContraction
import Formal.Util.AssertStandardAxioms

/-!
# 三角形追加の原始収縮・切断・補正

## Implementation notes

rは原始collapseの基底像、sは旧セルの包含、hは新セル表から生成する。
保存やhomotopyのcertificateを操作入力にする案は固定Bの構成義務を放電しないため
採らない。全セルで基底式を検算した後、支持を保つ原始有限和のAPIで任意Aへ制限する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)

/-- 旧セルの原始包含。端点・面・支持は旧データそのものである。 -/
def inclusion : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) (supported N e) N where
  chartMap := Sum.inl
  edgeMap := fun a => some (.inl a)
  faceMap := fun f => some (.inl f)
  edge_some_left := by intro a b h; cases Option.some.inj h; exact edgeLeft_old N e a
  edge_some_right := by intro a b h; cases Option.some.inj h; exact edgeRight_old N e a
  edge_none_fiber := by intro a h; cases h
  face_some_edge0 := by intro f g h; cases Option.some.inj h; rw [faceEdge0_old]
  face_some_edge1 := by intro f g h; cases Option.some.inj h; rw [faceEdge1_old]
  face_some_edge2 := by intro f g h; cases Option.some.inj h; rw [faceEdge2_old]
  face_none_incidence := by intro f h; cases h
  chartSupport_compatible := by intro v t ht; rw [self_factor]; exact ht

/-- 原始collapseから生成した頂点の台を保つ像。 -/
def r0 := (collapse N e).basis0
/-- 原始collapseから生成した辺の台を保つ像。 -/
def r1 := (collapse N e).basis1
/-- 原始collapseから生成した面の台を保つ像。 -/
def r2 := (collapse N e).basis2
/-- 原始包含から生成した頂点の切断。 -/
def s0 := (inclusion N e).basis0
/-- 原始包含から生成した辺の切断。 -/
def s1 := (inclusion N e).basis1
/-- 原始包含から生成した面の切断。 -/
def s2 := (inclusion N e).basis2

/-- 頂点の補正像。新頂点だけを追加辺cへ送る。 -/
def h0 : SupportedBasisMap (supported N e).chartSupport (supported N e).edgeSupport :=
  SupportedBasisMap.ofOption (fun v => match v with
    | .inl _ => none
    | .inr _ => some (.inr false)) (by
      rintro (v | x) a ha t ht
      · cases ha
      · cases x
        cases Option.some.inj ha
        simpa only [chartSupport_new, edgeSupport_c] using ht)

/-- 辺の補正像。e2だけを追加面fへ送る。 -/
def h1 : SupportedBasisMap (supported N e).edgeSupport (supported N e).faceSupport :=
  SupportedBasisMap.ofOption (fun a => match a with
    | .inl _ => none
    | .inr false => none
    | .inr true => some (.inr PUnit.unit)) (by
      rintro (a | b) f hf t ht
      · cases hf
      · cases b
        · cases hf
        · cases Option.some.inj hf
          simpa only [edgeSupport_e2, faceSupport_new] using ht)

/-! ## 原始基底像の評価API -/

/-- rの原始頂点像。 -/
@[simp] theorem r0_basis (v : (supported N e).nerve.Chart) :
    (r0 N e).basisImage v = Finsupp.single ((collapse N e).chartMap v) 1 := rfl
/-- rの原始辺像。 -/
@[simp] theorem r1_basis (v : (supported N e).nerve.EdgeComponent) :
    (r1 N e).basisImage v = rationalOptionCell ((collapse N e).edgeMap v) := rfl
/-- rの原始面像。 -/
@[simp] theorem r2_basis (v : (supported N e).nerve.FaceComponent) :
    (r2 N e).basisImage v = rationalOptionCell ((collapse N e).faceMap v) := rfl
/-- sの原始頂点像。 -/
@[simp] theorem s0_basis (v : N.nerve.Chart) :
    (s0 N e).basisImage v = Finsupp.single (.inl v) 1 := rfl
/-- sの原始辺像。 -/
@[simp] theorem s1_basis (v : N.nerve.EdgeComponent) :
    (s1 N e).basisImage v = Finsupp.single (.inl v) 1 := rfl
/-- sの原始面像。 -/
@[simp] theorem s2_basis (v : N.nerve.FaceComponent) :
    (s2 N e).basisImage v = Finsupp.single (.inl v) 1 := rfl
/-- h0の旧頂点像。 -/
@[simp] theorem h0_old_basis (v : N.nerve.Chart) : (h0 N e).basisImage (.inl v) = 0 := rfl
/-- h0の新頂点像。 -/
@[simp] theorem h0_new_basis : (h0 N e).basisImage (.inr PUnit.unit) =
    Finsupp.single (.inr false) 1 := rfl
/-- h1の旧辺像。 -/
@[simp] theorem h1_old_basis (v : N.nerve.EdgeComponent) : (h1 N e).basisImage (.inl v) = 0 := rfl
/-- h1のc像。 -/
@[simp] theorem h1_c_basis : (h1 N e).basisImage (.inr false) = 0 := rfl
/-- h1のe2像。 -/
@[simp] theorem h1_e2_basis : (h1 N e).basisImage (.inr true) =
    Finsupp.single (.inr PUnit.unit) 1 := rfl

/-- rの頂点基底評価。 -/
@[simp] theorem r0_single (v : (supported N e).nerve.Chart) (a : ℚ) :
    (r0 N e).raw (Finsupp.single v a) = Finsupp.single ((collapse N e).chartMap v) a := by
  simp [r0, SupportedBasisMap.raw_single, IncidenceSupportedComparison.basis0_image,
    Finsupp.smul_single]

/-- rの辺基底評価。 -/
@[simp] theorem r1_single (v : (supported N e).nerve.EdgeComponent) (a : ℚ) :
    (r1 N e).raw (Finsupp.single v a) = a • rationalOptionCell ((collapse N e).edgeMap v) := by
  simp [r1, SupportedBasisMap.raw_single]

/-- rの面基底評価。 -/
@[simp] theorem r2_single (v : (supported N e).nerve.FaceComponent) (a : ℚ) :
    (r2 N e).raw (Finsupp.single v a) = a • rationalOptionCell ((collapse N e).faceMap v) := by
  simp [r2, SupportedBasisMap.raw_single]

/-- sの頂点基底評価。 -/
@[simp] theorem s0_single (v : N.nerve.Chart) (a : ℚ) :
    (s0 N e).raw (Finsupp.single v a) = Finsupp.single (.inl v) a := by
  simp [s0, inclusion, SupportedBasisMap.raw_single, Finsupp.smul_single]

/-- sの辺基底評価。 -/
@[simp] theorem s1_single (v : N.nerve.EdgeComponent) (a : ℚ) :
    (s1 N e).raw (Finsupp.single v a) = Finsupp.single (.inl v) a := by
  simp [s1, inclusion, SupportedBasisMap.raw_single, Finsupp.smul_single]

/-- sの面基底評価。 -/
@[simp] theorem s2_single (v : N.nerve.FaceComponent) (a : ℚ) :
    (s2 N e).raw (Finsupp.single v a) = Finsupp.single (.inl v) a := by
  simp [s2, inclusion, SupportedBasisMap.raw_single, Finsupp.smul_single]

/-- h0は旧頂点で零。 -/
@[simp] theorem h0_old (v : N.nerve.Chart) (a : ℚ) :
    (h0 N e).raw (Finsupp.single (.inl v) a) = 0 := by
  simp [h0, SupportedBasisMap.raw_single]

/-- h0は新頂点をcへ送る。 -/
@[simp] theorem h0_new (a : ℚ) :
    (h0 N e).raw (Finsupp.single (.inr PUnit.unit) a) = Finsupp.single (.inr false) a := by
  simp [h0, SupportedBasisMap.raw_single, Finsupp.smul_single]

/-- h1は旧辺で零。 -/
@[simp] theorem h1_old (v : N.nerve.EdgeComponent) (a : ℚ) :
    (h1 N e).raw (Finsupp.single (.inl v) a) = 0 := by
  simp [h1, SupportedBasisMap.raw_single]

/-- h1はcで零。 -/
@[simp] theorem h1_c (a : ℚ) :
    (h1 N e).raw (Finsupp.single (.inr false) a) = 0 := by
  simp [h1, SupportedBasisMap.raw_single]

/-- h1はe2をfへ送る。 -/
@[simp] theorem h1_e2 (a : ℚ) :
    (h1 N e).raw (Finsupp.single (.inr true) a) = Finsupp.single (.inr PUnit.unit) a := by
  simp [h1, SupportedBasisMap.raw_single, Finsupp.smul_single]

/-- r・sの頂点往復は恒等。 -/
theorem rs0 : (r0 N e).raw.comp (s0 N e).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  simp [LinearMap.comp_apply]

/-- r・sの辺往復は恒等。 -/
theorem rs1 : (r1 N e).raw.comp (s1 N e).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  simp [LinearMap.comp_apply, Finsupp.smul_single]

/-- r・sの面往復は恒等。 -/
theorem rs2 : (r2 N e).raw.comp (s2 N e).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  simp [LinearMap.comp_apply, Finsupp.smul_single]


/-- 収縮rの全セルd1可換性。追加cの両端は同じ旧頂点へ写る。 -/
theorem r_comm01 : (TargetSupportedNerve.rawD1 N).raw.comp (r1 N e).raw =
    (r0 N e).raw.comp (TargetSupportedNerve.rawD1 (supported N e)).raw := by
  apply Finsupp.lhom_ext
  rintro (a | b) x
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single]
  · cases b <;> simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single]

/-- 収縮rの全セルd2可換性。新面の像は0-e+e=0。 -/
theorem r_comm12 : (TargetSupportedNerve.rawD2 N).raw.comp (r2 N e).raw =
    (r1 N e).raw.comp (TargetSupportedNerve.rawD2 (supported N e)).raw := by
  apply Finsupp.lhom_ext
  rintro (f | x) a
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, Finsupp.smul_single]
  · cases x
    simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, Finsupp.smul_single]

/-- 包含sの全セルd1可換性。旧端点とセル名を保持する。 -/
theorem s_comm01 : (TargetSupportedNerve.rawD1 (supported N e)).raw.comp (s1 N e).raw =
    (s0 N e).raw.comp (TargetSupportedNerve.rawD1 N).raw := by
  apply Finsupp.lhom_ext
  intro a x
  simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
    TargetSupportedNerve.rawD1_basis, Finsupp.smul_single]

/-- 包含sの全セルd2可換性。旧面の各符号位置を保持する。 -/
theorem s_comm12 : (TargetSupportedNerve.rawD2 (supported N e)).raw.comp (s2 N e).raw =
    (s1 N e).raw.comp (TargetSupportedNerve.rawD2 N).raw := by
  apply Finsupp.lhom_ext
  intro f x
  simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
    TargetSupportedNerve.rawD2_basis, Finsupp.smul_single]

/-- 頂点でid-sr=d1h0。新頂点の境界はv'-vである。 -/
theorem sr_h0 : (s0 N e).raw.comp (r0 N e).raw +
    (TargetSupportedNerve.rawD1 (supported N e)).raw.comp (h0 N e).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro (v | x) a
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single]
  · cases x
    simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single, smul_sub]

/-- 辺でid-sr=d2h1+h0d1。cとe2の補正は同じ新面を使用する。 -/
theorem sr_h1 : (s1 N e).raw.comp (r1 N e).raw +
    (TargetSupportedNerve.rawD2 (supported N e)).raw.comp (h1 N e).raw +
    (h0 N e).raw.comp (TargetSupportedNerve.rawD1 (supported N e)).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro (v | b) a
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, Finsupp.smul_single, smul_sub]
  · cases b <;> simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, TargetSupportedNerve.rawD2_basis, Finsupp.smul_single,
      smul_sub, smul_add]
    abel

/-- 面でid-sr=h1d2。追加面は同じh1の像であり旧面上は零。 -/
theorem sr_h2 : (s2 N e).raw.comp (r2 N e).raw +
    (h1 N e).raw.comp (TargetSupportedNerve.rawD2 (supported N e)).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro (f | x) a
  · simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, Finsupp.smul_single]
  · cases x
    simp [LinearMap.comp_apply, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, Finsupp.smul_single]


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


/-- 原始三角形追加から全fieldを生成した支持chain収縮の出力。 -/
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

/-- 生成された収縮のr0は同じ原始支持射。 -/
@[simp] theorem chainContraction_r0 (A : Set q.Target) :
    (chainContraction N e A).r0 = (r0 N e).selected A := rfl

/-- 生成された収縮のr1は同じ原始支持射。 -/
@[simp] theorem chainContraction_r1 (A : Set q.Target) :
    (chainContraction N e A).r1 = (r1 N e).selected A := rfl

/-- 生成された収縮のr2は同じ原始支持射。 -/
@[simp] theorem chainContraction_r2 (A : Set q.Target) :
    (chainContraction N e A).r2 = (r2 N e).selected A := rfl

/-- 生成された収縮のs0は同じ原始支持射。 -/
@[simp] theorem chainContraction_s0 (A : Set q.Target) :
    (chainContraction N e A).s0 = (s0 N e).selected A := rfl

/-- 生成された収縮のs1は同じ原始支持射。 -/
@[simp] theorem chainContraction_s1 (A : Set q.Target) :
    (chainContraction N e A).s1 = (s1 N e).selected A := rfl

/-- 生成された収縮のs2は同じ原始支持射。 -/
@[simp] theorem chainContraction_s2 (A : Set q.Target) :
    (chainContraction N e A).s2 = (s2 N e).selected A := rfl

/-- 生成された収縮のh0は同じ原始支持射。 -/
@[simp] theorem chainContraction_h0 (A : Set q.Target) :
    (chainContraction N e A).h0 = (h0 N e).selected A := rfl

/-- 生成された収縮のh1は同じ原始支持射。 -/
@[simp] theorem chainContraction_h1 (A : Set q.Target) :
    (chainContraction N e A).h1 = (h1 N e).selected A := rfl

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

/-- 出力recordのsHomは全次数で同じ旧セル包含Hom。 -/
theorem chainContraction_sHom (A : Set q.Target) : (chainContraction N e A).sHom = sHom N e A := rfl

/-- 原始三角形追加の実比較の全標準次数同型。 -/
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

end TriangleAddition
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
