import ResearchLean.AG.AtlasGluingWidth.WidthConnecting

/-! # 指定貼り合わせ類と既存hidden商

GOAL E / witnesses §4。指定標準δ類を同じG-134の通常U実商とCのhidden包含へ
接続し、その同じ商からG-135の既存fiber射への代表式を保持する。

## Implementation notes

生成因子の逆像を全短複体同型で正規化する。H¹だけを任意に同定する代替は
標準δと同じ元の接続を失うため採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable (n : ℕ) [NeZero n]

/-- 指定比較の元の通常領域二行図式の細行。 -/
abbrev primitiveFineRow := PrimitiveGluing.fineRow (h := coarser n) (Nf := fine n false)
  (regionA n) (regionB n)
/-- 元の生成因子を指定射影へ正規化すると全短複体が同じになる。 -/
theorem primitive_fine_row_eq : primitiveFineRow n = widthFineRow n := by
  unfold primitiveFineRow PrimitiveGluing.fineRow
  rw [factor]
  rfl
/-- 同じ全短複体等号から生成する短複体同型。 -/
def primitiveFineRowIso : primitiveFineRow n ≅ widthFineRow n := eqToIso (primitive_fine_row_eq n)
/-- 同じ和標準H¹を同型の第一成分で正規化する。 -/
def primitiveUnionH1Equiv : (primitiveFineRow n).X₁.homology (1:ℤ) ≃ₗ[ℚ]
    (widthFineRow n).X₁.homology (1:ℤ) :=
  (homologyMapIso (ShortComplex.π₁.mapIso (primitiveFineRowIso n)) 1).toLinearEquiv
/-- 同じ交差標準H⁰を同型の第三成分で正規化する。 -/
def primitiveIntersectionH0Equiv : (primitiveFineRow n).X₃.homology (0:ℤ) ≃ₗ[ℚ]
    (widthFineRow n).X₃.homology (0:ℤ) :=
  (homologyMapIso (ShortComplex.π₃.mapIso (primitiveFineRowIso n)) 0).toLinearEquiv
/-- 指定交差classを元の通常領域図式へ戻す。 -/
def primitiveIntersectionClass (hn : 2 ≤ n) (z : Bool → ℚ) :
    (primitiveFineRow n).X₃.homology (0:ℤ) :=
  (primitiveIntersectionH0Equiv n).symm (intersectionClass n hn z)
/-- 元の通常領域図式の同じ標準δ class。 -/
def primitiveDelta (hn : 2 ≤ n) (z : Bool → ℚ) : (primitiveFineRow n).X₁.homology (1:ℤ) :=
  StandardLES.connecting (primitiveFineRow n) (StandardRow.cellRow_shortExact _ _) 0
    (primitiveIntersectionClass n hn z)
/-- 全短複体同型は指定標準δ classを符号込みで保つ。 -/
theorem primitive_delta_same (hn : 2 ≤ n) (z : Bool → ℚ) :
    primitiveUnionH1Equiv n (primitiveDelta n hn z) = unionGeneratorClass n z := by
  have hc := congrArg (fun f => f (primitiveIntersectionClass n hn z))
    (HomologySequence.δ_naturality (primitiveFineRowIso n).hom
      (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) 0 1 rfl)
  change primitiveUnionH1Equiv n (primitiveDelta n hn z) =
    StandardLES.connecting (widthFineRow n) (StandardRow.cellRow_shortExact _ _) 0
      (primitiveIntersectionH0Equiv n (primitiveIntersectionClass n hn z)) at hc
  rw [primitiveIntersectionClass, LinearEquiv.apply_symm_apply, standard_connecting_generator] at hc
  exact hc
/-- 元の通常領域図式の同じ標準δ classは指定periodを持つ。 -/
theorem primitive_delta_period (hn : 2 ≤ n) (z : Bool → ℚ) :
    unionPeriodEquiv n (primitiveUnionH1Equiv n (primitiveDelta n hn z)) = endpointDifference z := by
  rw [primitive_delta_same, union_generator_value]
omit [NeZero n] in
/-- 同じUは全概念集合。 -/
theorem region_union_full : regionA n ∪ regionB n = Set.univ := Set.union_compl_self _
/-- 同じ通常Uの実fine商へ元の標準δ classを戻す。 -/
def gluingOldClass (hn : 2 ≤ n) (z : Bool → ℚ) : fineH1 n false (regionA n ∪ regionB n) :=
  (PrimitiveGluing.fineUnionEquiv (h := coarser n) (Nf := fine n false) (regionA n) (regionB n)).symm
    (primitiveDelta n hn z)
/-- 同じ通常Uの実oldhidden商へ指定δ classを入れる。 -/
def gluingHiddenClass (hn : 2 ≤ n) (z : Bool → ℚ) :=
  (LinearMap.range (actualMap n false (regionA n ∪ regionB n))).mkQ (gluingOldClass n hn z)
/-- 指定交差classの元の細Q代表。 -/
def primitiveQClass (hn : 2 ≤ n) (z : Bool → ℚ) : QuotientKernelRow.Q (primitiveFineRow n) :=
  (LinearMap.range (homologyMap (primitiveFineRow n).g 0).hom).mkQ (primitiveIntersectionClass n hn z)
/-- Cの元hidden包含は同じ実商の指定δ classを生む。 -/
theorem hidden_inclusion_same (hn : 2 ≤ n) (z : Bool → ℚ) :
    (PrimitiveGluing.oldHiddenRow (comparison n false) (regionA n) (regionB n)
      (local_defects_zero n hn).1 (local_defects_zero n hn).2).f
      ((LinearMap.range (QuotientKernelRow.q
        (PrimitiveGluing.coarseRow (Nc := coarse n) (regionA n) (regionB n))
        (PrimitiveGluing.comparison (comparison n false) (regionA n) (regionB n)))).mkQ
          (primitiveQClass n hn z)) = gluingHiddenClass n hn z := by
  rw [PrimitiveGluing.oldHiddenRow_f_mk]
  apply (PrimitiveGluing.hiddenEquiv (comparison n false) (regionA n) (regionB n)).injective
  dsimp only [gluingHiddenClass]
  rw [LinearEquiv.apply_symm_apply, PrimitiveGluing.hiddenEquiv_mk]
  simp only [gluingOldClass, LinearEquiv.apply_symm_apply,
    primitiveQClass, QuotientKernelRow.inclusion_mk, primitiveDelta]
/-- Cの同じ実hidden classをD/G-135へ渡すと既存fiber制限を同じ元に適用する。 -/
theorem coefficient_hidden_same (hn : 2 ≤ n) (z : Bool → ℚ) :
    ((CoefficientBridge.oldCoefficientRow (comparison n false) (regionA n ∪ regionB n)).g
      (gluingHiddenClass n hn z)).val =
      AtlasCoefficientFiber.fiberRestrictionH1 (comparison n false) (regionA n ∪ regionB n)
        (oldH1Equiv _ (gluingOldClass n hn z)) :=
  CoefficientBridge.oldCoefficientRow_g_mk_val _ _ _

/-- 指定(0,1)の同じ通常U old classはperiod1から非零。 -/
theorem gluing_old_nonzero (hn : 2 ≤ n) :
    gluingOldClass n hn (fun b => if b then 1 else 0) ≠ 0 := by
  intro hz
  have h := primitive_delta_period n hn (fun b => if b then 1 else 0)
  have he := congrArg (PrimitiveGluing.fineUnionEquiv (h := coarser n)
    (Nf := fine n false) (regionA n) (regionB n)) hz
  change PrimitiveGluing.fineUnionEquiv (h := coarser n) (Nf := fine n false)
    (regionA n) (regionB n) ((PrimitiveGluing.fineUnionEquiv (h := coarser n)
      (Nf := fine n false) (regionA n) (regionB n)).symm (primitiveDelta n hn _)) = _ at he
  rw [LinearEquiv.apply_symm_apply, map_zero] at he
  rw [he, map_zero, map_zero] at h
  norm_num [endpointDifference] at h
/-- 同じ粗U H¹が零なので原比較の実像は零。 -/
theorem union_actual_range_zero : LinearMap.range (actualMap n false (regionA n ∪ regionB n)) = ⊥ := by
  letI := coarse_H1_zero n (regionA n ∪ regionB n)
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    rw [Subsingleton.elim x 0, map_zero]
    exact Submodule.zero_mem _
  · intro hz
    exact ⟨0, by simpa using (show z = 0 from hz).symm⟩
/-- Cが生む同じ通常U hidden商類は原商で非零。 -/
theorem gluing_hidden_nonzero (hn : 2 ≤ n) :
    gluingHiddenClass n hn (fun b => if b then 1 else 0) ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [union_actual_range_zero] at hm
  exact gluing_old_nonzero n hn hm

/-- 同じ通常領域図式のliteral細Qを全短複体等号でℚへ移す。 -/
def primitiveQEquiv (hn : 2 ≤ n) : QuotientKernelRow.Q (primitiveFineRow n) ≃ₗ[ℚ] ℚ := by
  rw [primitive_fine_row_eq]
  exact fineQEquiv n hn
/-- 同じ通常領域図式のliteral細Pは零。 -/
theorem primitive_P_zero (hn : 2 ≤ n) : Subsingleton (QuotientKernelRow.P (primitiveFineRow n)) := by
  rw [primitive_fine_row_eq]
  exact fine_P_zero n hn
/-- 同じ通常領域図式のliteral比較qは元粗Qが零なので零射。 -/
theorem primitive_q_zero (hn : 2 ≤ n) : QuotientKernelRow.q
    (PrimitiveGluing.coarseRow (Nc := coarse n) (regionA n) (regionB n))
    (PrimitiveGluing.comparison (comparison n false) (regionA n) (regionB n)) = 0 := by
  letI : Subsingleton (QuotientKernelRow.Q (PrimitiveGluing.coarseRow
    (Nc := coarse n) (regionA n) (regionB n))) := coarse_Q_zero n hn
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0, map_zero]
  rfl
/-- 同じ通常領域図式のliteral Zは実粗交差H¹零から零。 -/
theorem primitive_Z_zero : QuotientKernelRow.Z
    (PrimitiveGluing.coarseRow (Nc := coarse n) (regionA n) (regionB n))
    (PrimitiveGluing.comparison (comparison n false) (regionA n) (regionB n)) = ⊥ := by
  letI : Subsingleton ((PrimitiveGluing.coarseRow (Nc := coarse n)
    (regionA n) (regionB n)).X₃.homology (1 : ℤ)) :=
      coarse_intersection_standard_H1_zero n
  exact Subsingleton.elim _ _

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
