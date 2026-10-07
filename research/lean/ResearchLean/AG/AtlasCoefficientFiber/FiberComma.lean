import ResearchLean.AG.AtlasCoefficientFiber.LocalFiber

/-!
# G-135 A：原始局所セルとcomma圏の接続

## Implementation notes

同じcarrierの原始セルを恒等輸送射とともにcomma圏へ入れる。
φの写像が同じ粗セルのendomorphismなら恒等であることをIncのAPIから使い、
compatibilityを新しい入力fieldにはしない。Λでは面からの射の分類を使って
comma対象との全単射を得る。Φ・Γの高carrier対象との成分同定は別の義務である。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じcarrierの細incidenceに沿う恒等輸送の可換性。新規仮定は所属の等号のみ。 -/
theorem constantCarrier_transport {i j : Inc Nf (comparisonFactor qc qf h ⁻¹' A)}
    (σ : Inc Nc A) (hi : (Carrier.preimageFunctor M A).obj i = σ)
    (hj : (Carrier.preimageFunctor M A).obj j = σ) (f : i ⟶ j) :
    eqToHom hi.symm ≫ (Carrier.preimageFunctor M A).map f = eqToHom hj.symm := by
  have hh := inc_endomorphism_eq_id σ
    (eqToHom hi.symm ≫ (Carrier.preimageFunctor M A).map f ≫ eqToHom hj)
  have ht := congrArg (fun g => g ≫ eqToHom hj.symm) hh
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp] using ht

/-- 原始セル対象写像と同一carrier証明から、commaへの実関手を作る一般API。 -/
def constantCarrierCommaFunctor (X : Type u)
    (obj : X → Inc Nf (comparisonFactor qc qf h ⁻¹' A)) (σ : Inc Nc A)
    (ho : ∀ x, (Carrier.preimageFunctor M A).obj (obj x) = σ) :
    InducedCategory (Inc Nf (comparisonFactor qc qf h ⁻¹' A)) obj ⥤
      StructuredArrow σ (Carrier.preimageFunctor M A) where
  obj x := StructuredArrow.mk (eqToHom (ho x).symm)
  map {x y} f := StructuredArrow.homMk f.hom (constantCarrier_transport M A σ (ho x) (ho y) f.hom)
  map_id x := by apply StructuredArrow.ext; rfl
  map_comp f g := by apply StructuredArrow.ext; rfl

/-- 原始Φの全セルから同じchart-commaへの包含。所属はphiCellObj_carrierで放電。 -/
def phiCommaFunctor (c : Nc.ChartInTargetSubset A) :
    PhiInc M A c ⥤ StructuredArrow (.chart c) (Carrier.preimageFunctor M A) :=
  constantCarrierCommaFunctor M A _ (phiCellObj M A c) (.chart c) (phiCellObj_carrier M A c)

/-- 原始Γのmapped辺と混在面から同じedge-commaへの包含。 -/
def gammaCommaFunctor (e : Nc.EdgeInTargetSubset A) :
    GammaInc M A e ⥤ StructuredArrow (.edge e) (Carrier.preimageFunctor M A) :=
  constantCarrierCommaFunctor M A _ (gammaCellObj M A e) (.edge e) (gammaCellObj_carrier M A e)

/-- constant carrier包含は元の全incidence射をそのまま保つfully faithful関手。 -/
def constantCarrierCommaFullyFaithful (X : Type u)
    (obj : X → Inc Nf (comparisonFactor qc qf h ⁻¹' A)) (σ : Inc Nc A)
    (ho : ∀ x, (Carrier.preimageFunctor M A).obj (obj x) = σ) :
    (constantCarrierCommaFunctor M A X obj σ ho).FullyFaithful where
  preimage f := InducedCategory.homMk f.right
  map_preimage f := by apply StructuredArrow.ext; rfl
  preimage_map f := rfl

/-- 同じ原始対象を持つcomma対象からconstant carrier包含へ戻す恒等輸送射。 -/
def constantCarrierCommaBackwardArrow (X : Type u)
    (obj : X → Inc Nf (comparisonFactor qc qf h ⁻¹' A)) (σ : Inc Nc A)
    (ho : ∀ x, (Carrier.preimageFunctor M A).obj (obj x) = σ)
    (y : StructuredArrow σ (Carrier.preimageFunctor M A)) (z : X) (hz : obj z = y.right) :
    y ⟶ (constantCarrierCommaFunctor M A X obj σ ho).obj z :=
  StructuredArrow.homMk (eqToHom hz.symm) (by
    rw [← cancel_mono (eqToHom (ho z))]
    exact (inc_endomorphism_eq_id σ _).trans (inc_endomorphism_eq_id σ _).symm)

/-- constant carrier逆輸送の細側成分。定義所有者API。 -/
@[simp] theorem constantCarrierCommaBackwardArrow_right (X : Type u)
    (obj : X → Inc Nf (comparisonFactor qc qf h ⁻¹' A)) (σ : Inc Nc A)
    (ho : ∀ x, (Carrier.preimageFunctor M A).obj (obj x) = σ)
    (y : StructuredArrow σ (Carrier.preimageFunctor M A)) (z : X) (hz : obj z = y.right) :
    (constantCarrierCommaBackwardArrow M A X obj σ ho y z hz).right = eqToHom hz.symm := rfl

/-- strict carrier像の同じcomma行先に至る二原像は、元のincidence圏内で連結する。 -/
theorem constantCarrierComma_common_target (X : Type u)
    (obj : X → Inc Nf (comparisonFactor qc qf h ⁻¹' A)) (σ : Inc Nc A)
    (ho : ∀ x, (Carrier.preimageFunctor M A).obj (obj x) = σ)
    (y : StructuredArrow σ (Carrier.preimageFunctor M A)) (z : X) (hz : obj z = y.right)
    (x x' : InducedCategory (Inc Nf (comparisonFactor qc qf h ⁻¹' A)) obj)
    (f : (constantCarrierCommaFunctor M A X obj σ ho).obj x ⟶ y)
    (g : (constantCarrierCommaFunctor M A X obj σ ho).obj x' ⟶ y) : Zigzag x x' := by
  let b := constantCarrierCommaBackwardArrow M A X obj σ ho y z hz
  exact (Zigzag.of_hom ((constantCarrierCommaFullyFaithful M A X obj σ ho).preimage (f ≫ b))).trans
    (Zigzag.of_hom ((constantCarrierCommaFullyFaithful M A X obj σ ho).preimage (g ≫ b))).symm

/-- 原始Φ包含はfully faithful。同じ端点・辺・頂点位置の全incidence射を保つ。 -/
def phiCommaFullyFaithful (c : Nc.ChartInTargetSubset A) :
    (phiCommaFunctor M A c).FullyFaithful :=
  constantCarrierCommaFullyFaithful M A _ (phiCellObj M A c) (.chart c) (phiCellObj_carrier M A c)

/-- Φ包含の細対象を読む定義所有者API。 -/
@[simp] theorem phiCommaFunctor_obj_right (c : Nc.ChartInTargetSubset A) (x : PhiInc M A c) :
    ((phiCommaFunctor M A c).obj x).right = phiCellObj M A c x := rfl

/-- Φ包含のcomma incidenceは同じcarrier所属の恒等輸送。 -/
@[simp] theorem phiCommaFunctor_obj_hom (c : Nc.ChartInTargetSubset A) (x : PhiInc M A c) :
    ((phiCommaFunctor M A c).obj x).hom = eqToHom (phiCellObj_carrier M A c x).symm := rfl

/-- 原始Γの包含はfully faithful。生成されたcarrier所属と同じincidence射を用いる。 -/
def gammaCommaFullyFaithful (e : Nc.EdgeInTargetSubset A) :
    (gammaCommaFunctor M A e).FullyFaithful :=
  constantCarrierCommaFullyFaithful M A _ (gammaCellObj M A e) (.edge e) (gammaCellObj_carrier M A e)

/-- Γ包含の細対象を読む定義所有者API。 -/
@[simp] theorem gammaCommaFunctor_obj_right (e : Nc.EdgeInTargetSubset A) (x : GammaInc M A e) :
    ((gammaCommaFunctor M A e).obj x).right = gammaCellObj M A e x := rfl

/-- Γ包含のcomma incidenceは同じcarrier所属の恒等輸送。 -/
@[simp] theorem gammaCommaFunctor_obj_hom (e : Nc.EdgeInTargetSubset A) (x : GammaInc M A e) :
    ((gammaCommaFunctor M A e).obj x).hom = eqToHom (gammaCellObj_carrier M A e x).symm := rfl

/-- 原始面の持ち上げを同じface-comma対象にする。 -/
def lambdaCommaObj (F : Nc.FaceInTargetSubset A) (f : LambdaFace M A F) :
    StructuredArrow (.face F) (Carrier.preimageFunctor M A) :=
  StructuredArrow.mk (eqToHom (lambdaFace_carrier M A F f).symm)

/-- 同じcomma対象に写った持ち上げは元の名前付き細面として同じ。 -/
theorem lambdaCommaObj_injective (F : Nc.FaceInTargetSubset A) :
    Function.Injective (lambdaCommaObj M A F) := by
  intro f g hh
  have hr := congrArg (fun y : StructuredArrow (.face F) (Carrier.preimageFunctor M A) => y.right) hh
  exact Subtype.ext (Inc.face.inj hr)

/-- 面commaの全対象は原始faceMapがFである持ち上げから生じる。 -/
theorem lambdaCommaObj_surjective (F : Nc.FaceInTargetSubset A) :
    Function.Surjective (lambdaCommaObj M A F) := by
  intro y
  have ht := incHom_target_of_face F y.hom
  cases hy : y.right with
  | chart c =>
    rw [hy, Carrier.preimageFunctor_obj_chart] at ht
    cases ht
  | edge e =>
    cases he : M.edgeMap e.1 with
    | none => rw [hy, Carrier.preimageFunctor_obj_edge_of_none M A e he] at ht; cases ht
    | some a => rw [hy, Carrier.preimageFunctor_obj_edge_of_some M A e a he] at ht; cases ht
  | face f =>
    have hm : M.faceMap f.1 = some F.1 := by
      apply (Carrier.face_eq_face_iff M A _ (fun _ ht => ht) f F).mp
      exact (Carrier.preimageFunctor_obj_face M A f).symm.trans (by simpa only [hy] using ht)
    let ff : LambdaFace M A F := ⟨f, hm⟩
    refine ⟨ff, StructuredArrow.obj_ext _ y hy.symm ?_⟩
    exact incHom_from_face_eq F _ _

/-- Λの原始持ち上げ集合とface-comma対象の全単射。空の場合も同じ構成。 -/
def lambdaCommaEquiv (F : Nc.FaceInTargetSubset A) :
    LambdaFace M A F ≃ StructuredArrow (.face F) (Carrier.preimageFunctor M A) :=
  Equiv.ofBijective (lambdaCommaObj M A F)
    ⟨lambdaCommaObj_injective M A F, lambdaCommaObj_surjective M A F⟩

/-- 面commaの各射は同じ持ち上げ対象を結ぶ。原始面からの射の分類を使用。 -/
theorem faceComma_obj_eq_of_hom (F : Nc.FaceInTargetSubset A)
    {x y : StructuredArrow (.face F) (Carrier.preimageFunctor M A)} (f : x ⟶ y) : x = y := by
  obtain ⟨fx, rfl⟩ := lambdaCommaObj_surjective M A F x
  obtain ⟨fy, rfl⟩ := lambdaCommaObj_surjective M A F y
  have hr := (incHom_target_of_face fx.1 f.right).symm
  exact StructuredArrow.obj_ext _ _ hr (incHom_from_face_eq F _ _)

/-- 面commaの成分から原始持ち上げへの写像。zigzag全体の不変性を証明して降ろす。 -/
def lambdaComponentToFace (F : Nc.FaceInTargetSubset A) :
    CategoryTheory.ConnectedComponents (StructuredArrow (.face F) (Carrier.preimageFunctor M A)) → LambdaFace M A F :=
  Quotient.lift (lambdaCommaEquiv M A F).symm (fun _ _ hh =>
    invariant_of_zigzag (lambdaCommaEquiv M A F).symm
      (fun f => congrArg (lambdaCommaEquiv M A F).symm (faceComma_obj_eq_of_hom M A F f)) hh)

/-- Λと面comma成分の全単射。対象の全単射に加え、射による同一視がないことを使用。 -/
def lambdaComponentsEquiv (F : Nc.FaceInTargetSubset A) :
    CategoryTheory.ConnectedComponents (StructuredArrow (.face F) (Carrier.preimageFunctor M A)) ≃ LambdaFace M A F where
  toFun := lambdaComponentToFace M A F
  invFun f := CategoryTheory.ConnectedComponents.mk (lambdaCommaObj M A F f)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h y =>
      change CategoryTheory.ConnectedComponents.mk
        (lambdaCommaObj M A F ((lambdaCommaEquiv M A F).symm y)) = CategoryTheory.ConnectedComponents.mk y
      exact congrArg CategoryTheory.ConnectedComponents.mk ((lambdaCommaEquiv M A F).apply_symm_apply y)
  right_inv f := (lambdaCommaEquiv M A F).symm_apply_apply f

/-- A・設計§2の面stalk成分式。標準comma極限からΛ上のℚ関数へ同定する。 -/
def lambdaCoefficientEquiv (F : Nc.FaceInTargetSubset A) :
    (pushforwardCoefficients M A).obj (.face F) ≃ₗ[ℚ] (LambdaFace M A F → ℚ) :=
  ((coefficientCellIso (Carrier.preimageFunctor M A) (.face F)).toLinearEquiv.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : CategoryTheory.ConnectedComponents
        (StructuredArrow (.face F) (Carrier.preimageFunctor M A)) => ULift.{u} ℚ)
      (lambdaComponentsEquiv M A F))).trans
    (LinearEquiv.piCongrRight (fun _ => ULift.moduleEquiv))

/-- Λ成分式の同じ持ち上げでの評価。定義所有者API。 -/
@[simp] theorem lambdaCoefficientEquiv_apply (F : Nc.FaceInTargetSubset A)
    (z : (pushforwardCoefficients M A).obj (.face F)) (f : LambdaFace M A F) :
    lambdaCoefficientEquiv M A F z f =
      ((coefficientCellIso (Carrier.preimageFunctor M A) (.face F)).hom z
        (CategoryTheory.ConnectedComponents.mk (lambdaCommaObj M A F f))).down := rfl

/-- Λ包含の細面名を読む定義所有者API。 -/
@[simp] theorem lambdaCommaObj_right (F : Nc.FaceInTargetSubset A) (f : LambdaFace M A F) :
    (lambdaCommaObj M A F f).right = Inc.face f.1 := rfl

/-- Λ包含のcomma射は原始面所属の恒等輸送。 -/
@[simp] theorem lambdaCommaObj_hom (F : Nc.FaceInTargetSubset A) (f : LambdaFace M A F) :
    (lambdaCommaObj M A F f).hom = eqToHom (lambdaFace_carrier M A F f).symm := rfl

/-- Λの成分同型の逆向きは同じ持ち上げの標準comma成分である。 -/
@[simp] theorem lambdaComponentsEquiv_symm_apply (F : Nc.FaceInTargetSubset A) (f : LambdaFace M A F) :
    (lambdaComponentsEquiv M A F).symm f =
      CategoryTheory.ConnectedComponents.mk (lambdaCommaObj M A F f) := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.constantCarrier_transport
#print axioms AAT.AG.AtlasCoefficientFiber.constantCarrierCommaFunctor
#print axioms AAT.AG.AtlasCoefficientFiber.phiCommaFunctor
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCommaFunctor
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCommaObj
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCommaObj_injective
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCommaObj_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCommaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.faceComma_obj_eq_of_hom
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaComponentToFace
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaComponentsEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCoefficientEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.constantCarrierCommaFullyFaithful
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCommaFunctor_obj_right
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCommaFunctor_obj_hom
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCommaFullyFaithful
#print axioms AAT.AG.AtlasCoefficientFiber.constantCarrierCommaBackwardArrow
#print axioms AAT.AG.AtlasCoefficientFiber.constantCarrierCommaBackwardArrow_right
#print axioms AAT.AG.AtlasCoefficientFiber.constantCarrierComma_common_target
#print axioms AAT.AG.AtlasCoefficientFiber.phiCommaFullyFaithful
#print axioms AAT.AG.AtlasCoefficientFiber.phiCommaFunctor_obj_right
#print axioms AAT.AG.AtlasCoefficientFiber.phiCommaFunctor_obj_hom
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCommaObj_right
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCommaObj_hom
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaComponentsEquiv_symm_apply
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
