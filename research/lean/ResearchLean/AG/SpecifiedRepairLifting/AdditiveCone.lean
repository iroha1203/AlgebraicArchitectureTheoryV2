import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
/-! # 一般整数加群の標準錐座標

G-138 T0・Aの全整数次数の標準mappingConeの成分式。
Implementation notes: G-133 ConeCoordinatesのprojection/inclusionによる構成を
整数加群へ一般化する。有限性・自由性・無捩れ性は仮定しない。
標準錐そのものを用い、独立な錐recordや有理化は導入しない。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex
namespace AAT.AG.SpecifiedRepairLifting
open CochainComplex
universe w
variable {R : Type} [CommRing R]
variable {F G : CochainComplex (ModuleCat.{w} R) ℤ} (φ : F ⟶ G)
/-- 標準錐の次数別成分をカードCのtarget/source順序へ交換する両方向同型。 -/
def coneCoordinateEquiv (m : ℤ) :
    (mappingCone φ).X m ≃ₗ[R] G.X m × F.X (m + 1) where
  toFun z := ((mappingCone.snd φ).v m m (by simp) z,
    (mappingCone.fst φ).1.v m (m+1) rfl z)
  invFun p := (mappingCone.inr φ).f m p.1 +
    (mappingCone.inl φ).v (m+1) m (by simp) p.2
  left_inv z := by
    have h := congrArg (fun f : (mappingCone φ).X m ⟶ (mappingCone φ).X m => f z)
      (mappingCone.id_X φ m (m+1) rfl)
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, ModuleCat.id_apply, add_comm] using h
  right_inv p := by
    apply Prod.ext <;> dsimp only <;>
      simp only [map_add, ← ModuleCat.comp_apply, mappingCone.inl_v_snd_v,
        mappingCone.inl_v_fst_v, mappingCone.inr_f_snd_v, mappingCone.inr_f_fst_v,
        ModuleCat.hom_zero, LinearMap.zero_apply, ModuleCat.id_apply, zero_add, add_zero]
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- 標準錐座標の逆写像は、実target包含とshifted source包含の和である。 -/
theorem coneCoordinateEquiv_symm_eq (m : ℤ) (p : G.X m × F.X (m+1)) :
    (coneCoordinateEquiv φ m).symm p = (mappingCone.inr φ).f m p.1 +
      (mappingCone.inl φ).v (m+1) m (by simp) p.2 := rfl

/-- 実target包含は全次数でtarget/source座標の第一成分に入る。 -/
@[simp] theorem coneCoordinateEquiv_inr (m : ℤ) (y : G.X m) :
    coneCoordinateEquiv φ m ((mappingCone.inr φ).f m y) = (y,0) := by
  apply (coneCoordinateEquiv φ m).symm.injective
  rw [LinearEquiv.symm_apply_apply, coneCoordinateEquiv_symm_eq]
  simp only [map_zero, add_zero]

/-- 実shifted source包含は全次数でtarget/source座標の第二成分に入る。 -/
@[simp] theorem coneCoordinateEquiv_inl (m : ℤ) (x : F.X (m+1)) :
    coneCoordinateEquiv φ m ((mappingCone.inl φ).v (m+1) m (by simp) x) = (0,x) := by
  apply (coneCoordinateEquiv φ m).symm.injective
  rw [LinearEquiv.symm_apply_apply, coneCoordinateEquiv_symm_eq]
  simp only [map_zero, zero_add]

/-- Cのtarget成分は標準錐のsecond projectionで読む。 -/
@[simp] theorem coneCoordinateEquiv_snd (m : ℤ) (z : (mappingCone φ).X m) :
    (coneCoordinateEquiv φ m z).1 = (mappingCone.snd φ).v m m (by simp) z := rfl
/-- Cのshifted source成分は標準錐のfirst projectionで読む。 -/
@[simp] theorem coneCoordinateEquiv_fst (m : ℤ) (z : (mappingCone φ).X m) :
    (coneCoordinateEquiv φ m z).2 = (mappingCone.fst φ).1.v m (m+1) rfl z := rfl

/-- 次数別同型の逆構成はtarget成分をそのまま復元する。 -/
@[simp] theorem coneCoordinateEquiv_symm_snd (m : ℤ) (p : G.X m × F.X (m+1)) :
    (mappingCone.snd φ).v m m (by simp) ((coneCoordinateEquiv φ m).symm p) = p.1 := by
  have h := congrArg Prod.fst ((coneCoordinateEquiv φ m).apply_symm_apply p)
  exact h
/-- 次数別同型の逆構成はshifted source成分をそのまま復元する。 -/
@[simp] theorem coneCoordinateEquiv_symm_fst (m : ℤ) (p : G.X m × F.X (m+1)) :
    (mappingCone.fst φ).1.v m (m+1) rfl ((coneCoordinateEquiv φ m).symm p) = p.2 := by
  have h := congrArg Prod.snd ((coneCoordinateEquiv φ m).apply_symm_apply p)
  exact h

/-- カードCの順序と負号の微分を、標準錐の両projection APIから全整数次数で導く。 -/
theorem coneCoordinateEquiv_d (m : ℤ) (p : G.X m × F.X (m+1)) :
    coneCoordinateEquiv φ (m+1)
      ((mappingCone φ).d m (m+1) ((coneCoordinateEquiv φ m).symm p)) =
      (G.d m (m+1) p.1 + φ.f (m+1) p.2, -F.d (m+1) (m+1+1) p.2) := by
  apply Prod.ext
  · rw [coneCoordinateEquiv_snd]
    have h := congrArg (fun f : (mappingCone φ).X m ⟶ G.X (m+1) =>
      f ((coneCoordinateEquiv φ m).symm p)) (mappingCone.d_snd_v φ m (m+1) rfl)
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
      coneCoordinateEquiv_symm_snd, coneCoordinateEquiv_symm_fst, add_comm] using h
  · rw [coneCoordinateEquiv_fst]
    have h := congrArg (fun f : (mappingCone φ).X m ⟶ F.X (m+1+1) =>
      f ((coneCoordinateEquiv φ m).symm p))
        (mappingCone.d_fst_v φ m (m+1) (m+1+1) rfl rfl)
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_neg, LinearMap.neg_apply,
      coneCoordinateEquiv_symm_fst, map_neg] using h

/-- 実錐の任意の元に対する隣接微分の公開成分式。 -/
theorem coneCoordinateEquiv_d_apply (m : ℤ) (x : (mappingCone φ).X m) :
    coneCoordinateEquiv φ (m+1) ((mappingCone φ).d m (m+1) x) =
      (G.d m (m+1) (coneCoordinateEquiv φ m x).1 +
        φ.f (m+1) (coneCoordinateEquiv φ m x).2,
        -F.d (m+1) (m+1+1) (coneCoordinateEquiv φ m x).2) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    coneCoordinateEquiv_d φ m (coneCoordinateEquiv φ m x)

/-- 標準錐の可換正方形射は同じtarget/sourceの二成分で作用する。 -/
theorem coneCoordinateEquiv_map {F' G' : CochainComplex (ModuleCat.{w} R) ℤ}
    (φ' : F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G')
    (comm : φ ≫ b = a ≫ φ') (m : ℤ) (x : (mappingCone φ).X m) :
    coneCoordinateEquiv φ' m ((mappingCone.map φ φ' a b comm).f m x) =
      (b.f m (coneCoordinateEquiv φ m x).1,
        a.f (m+1) (coneCoordinateEquiv φ m x).2) := by
  apply Prod.ext <;>
    simp only [coneCoordinateEquiv_snd,coneCoordinateEquiv_fst,mappingCone.map,
      mappingCone.desc_f _ _ _ _ m (m+1) rfl,
      HomComplex.Cochain.zero_cochain_comp_v,HomComplex.Cochain.ofHom_v,
      HomologicalComplex.comp_f,ModuleCat.hom_add,LinearMap.add_apply,
      ModuleCat.comp_apply,map_add] <;>
    simp only [Prod.fst_add,Prod.snd_add,coneCoordinateEquiv_snd,coneCoordinateEquiv_fst] <;>
    simp only [← ModuleCat.comp_apply,Category.assoc,
      mappingCone.inl_v_snd_v,mappingCone.inr_f_snd_v,
      mappingCone.inl_v_fst_v,mappingCone.inr_f_fst_v,
      Category.comp_id,comp_zero,ModuleCat.hom_zero,LinearMap.zero_apply,
      zero_add,add_zero]

section Nonnegative
variable (C D : CochainComplex (ModuleCat.{w} ℤ) ℕ)
/-- T0の負次数零延長はmathlibのshape embeddingによる標準構成を使う。 -/
abbrev zeroExtension := C.extend ComplexShape.embeddingUpNat
/-- 零延長の非負次数と元の同じ次数の標準同型。 -/
def zeroExtensionEquiv (n : ℕ) : (zeroExtension C).X (n : ℤ) ≃ₗ[ℤ] C.X n :=
  (C.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv
/-- T0の比較写像は元の全次数の成分を保って零延長する。 -/
abbrev zeroExtensionMap (φ : C ⟶ D) := extendMap φ ComplexShape.embeddingUpNat
/-- 零延長の同型で微分を評価するAPI。高次数も元の微分を保持する。 -/
theorem zeroExtensionEquiv_d (i j : ℕ) (x : (zeroExtension C).X (i : ℤ)) :
    zeroExtensionEquiv C j ((zeroExtension C).d (i : ℤ) (j : ℤ) x) =
      C.d i j (zeroExtensionEquiv C i x) := by
  rw [HomologicalComplex.extend_d_eq C ComplexShape.embeddingUpNat (i := i) (j := j) (i' := (i : ℤ)) (j' := (j : ℤ)) rfl rfl]
  simp [zeroExtensionEquiv]
/-- 零延長の比較は元の同じcochain写像の成分へ一致する。 -/
theorem zeroExtensionEquiv_map (φ : C ⟶ D) (n : ℕ)
    (x : (zeroExtension C).X (n : ℤ)) :
    zeroExtensionEquiv D n ((zeroExtensionMap C D φ).f (n : ℤ) x) =
      φ.f n (zeroExtensionEquiv C n x) := by
  rw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
  simp [zeroExtensionEquiv]
/-- 標準零延長の負次数は零対象である。 -/
theorem zeroExtension_isZero (n : ℤ) (hn : n < 0) : IsZero ((zeroExtension C).X n) := by
  apply C.isZero_extend_X ComplexShape.embeddingUpNat n
  intro i hi
  change (i : ℤ) = n at hi
  omega
/-- 元の非負複体のHⁿと零延長のHⁿを標準homology同型で接続する。 -/
def zeroExtensionHomologyIso (n : ℕ) :
    (zeroExtension C).homology (n : ℤ) ≅ C.homology n :=
  C.extendHomologyIso ComplexShape.embeddingUpNat rfl
/-- 零延長のHⁿ同型は標準cycleの類写像と可換になる。 -/
theorem zeroExtensionHomologyIso_class (n : ℕ) :
    (zeroExtension C).homologyπ (n : ℤ) ≫ (zeroExtensionHomologyIso C n).hom =
      (C.extendCyclesIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom ≫
        C.homologyπ n := by
  exact C.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat rfl
/-- 零延長のHⁿ同型は元の比較から誘導したHⁿ写像と可換になる。 -/
theorem zeroExtensionHomologyIso_naturality (f : C ⟶ D) (n : ℕ) :
    homologyMap (zeroExtensionMap C D f) (n : ℤ) ≫
        (zeroExtensionHomologyIso D n).hom =
      (zeroExtensionHomologyIso C n).hom ≫ homologyMap f n := by
  exact extendHomologyIso_hom_naturality f ComplexShape.embeddingUpNat rfl
end Nonnegative

section SpecifiedClass
variable {C D : CochainComplex (ModuleCat.{w} R) ℤ} (f : C ⟶ D)
/-- T0の二つの厳密なcochain等式による解。解の存在をfieldとして受け取らない。 -/
def Lift (z : C.X 1) (b : D.X 0) := {a : C.X 0 // C.d 0 1 a = z ∧ f.f 0 a = b}
/-- Aの指定cocycleの代表は標準錐座標で(b,-z)である。 -/
def specifiedRepresentative (z : C.X 1) (b : D.X 0) : (mappingCone f).X 0 :=
  (coneCoordinateEquiv f 0).symm (b, -z)
/-- T0の適合条件とcocycle条件から標準錐での閉性を導く。 -/
theorem specifiedRepresentative_closed (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    (mappingCone f).d 0 1 (specifiedRepresentative f z b) = 0 := by
  apply (coneCoordinateEquiv f 1).injective
  rw [map_zero]
  change coneCoordinateEquiv f (0+1)
    ((mappingCone f).d 0 (0+1) ((coneCoordinateEquiv f 0).symm (b,-z))) = 0
  rw [coneCoordinateEquiv_d]
  simp [hb, hz]
/-- Aの指定閉元を標準短複体の実kernelへ入れる。 -/
def specifiedCycle (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    LinearMap.ker ((mappingCone f).sc 0).g.hom :=
  ⟨specifiedRepresentative f z b, by
    change (mappingCone f).d 0 ((ComplexShape.up ℤ).next 0) _ = 0
    rw [ComplexShape.next_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel 0 1 by decide)]
    exact specifiedRepresentative_closed f z b hz hb⟩
/-- Aの障害は標準mappingConeのH⁰の元。標準homology同型を逆に通して生成する。 -/
def specifiedObstruction (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    (mappingCone f).homology 0 :=
  ((mappingCone f).sc 0).moduleCatHomologyIso.inv
    ((LinearMap.range ((mappingCone f).sc 0).moduleCatToCycles).mkQ
      (specifiedCycle f z b hz hb))
/-- 標準H⁰の零性を標準錐の次数−1からの実微分の証人へ戻すAPI。 -/
theorem specifiedObstruction_zero_iff_boundary (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    specifiedObstruction f z b hz hb = 0 ↔
      ∃ x : (mappingCone f).X (-1),
        (mappingCone f).d (-1) 0 x = specifiedRepresentative f z b := by
  let S := (mappingCone f).sc 0
  have hi := S.moduleCatHomologyIso.toLinearEquiv.symm.injective
  change S.moduleCatHomologyIso.toLinearEquiv.symm _ = 0 ↔ _
  rw [← map_zero S.moduleCatHomologyIso.toLinearEquiv.symm, hi.eq_iff]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change (∃ x, S.moduleCatToCycles x = specifiedCycle f z b hz hb) ↔ _
  have he : (∃ x, S.moduleCatToCycles x = specifiedCycle f z b hz hb) ↔
      ∃ x : S.X₁, S.f x = specifiedRepresentative f z b := by
    constructor
    · rintro ⟨x,hx⟩; exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x,hx⟩; exact ⟨x, Subtype.ext hx⟩
  rw [he]
  change (∃ x : (mappingCone f).X ((ComplexShape.up ℤ).prev 0),
    (mappingCone f).d ((ComplexShape.up ℤ).prev 0) 0 x = _) ↔ _
  rw [ComplexShape.prev_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)]
/-- Aの零性判定。負次数のtarget零性は非負複体の零延長から放電される。 -/
theorem specifiedObstruction_zero_iff_lift [Subsingleton (D.X (-1))]
    (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    specifiedObstruction f z b hz hb = 0 ↔ Nonempty (Lift f z b) := by
  rw [specifiedObstruction_zero_iff_boundary]
  constructor
  · rintro ⟨x,hx⟩
    let a : C.X 0 := (coneCoordinateEquiv f (-1) x).2
    have hd := coneCoordinateEquiv_d_apply f (-1) x
    change coneCoordinateEquiv f 0 ((mappingCone f).d (-1) 0 x) =
      (D.d (-1) 0 (coneCoordinateEquiv f (-1) x).1 + f.f 0 a, -C.d 0 1 a) at hd
    rw [hx] at hd
    have hc : coneCoordinateEquiv f 0 (specifiedRepresentative f z b) = (b,-z) :=
      (coneCoordinateEquiv f 0).apply_symm_apply _
    rw [hc] at hd
    have hzero : (coneCoordinateEquiv f (-1) x).1 = 0 := Subsingleton.elim _ _
    have hfirst := congrArg Prod.fst hd
    have hsecond := congrArg Prod.snd hd
    refine ⟨⟨a, ?_, ?_⟩⟩
    · exact neg_injective hsecond.symm
    · simpa only [Prod.fst, hzero, map_zero, zero_add] using hfirst.symm
  · rintro ⟨a⟩
    refine ⟨(coneCoordinateEquiv f (-1)).symm (0,a.val), ?_⟩
    apply (coneCoordinateEquiv f 0).injective
    have hd := coneCoordinateEquiv_d f (-1) (0,(by simpa using a.val))
    change coneCoordinateEquiv f 0
      ((mappingCone f).d (-1) 0 ((coneCoordinateEquiv f (-1)).symm (0,a.val))) =
      (D.d (-1) 0 0 + f.f 0 a.val, -C.d 0 1 a.val) at hd
    rw [hd]
    rw [show coneCoordinateEquiv f 0 (specifiedRepresentative f z b) = (b,-z) from
      (coneCoordinateEquiv f 0).apply_symm_apply _]
    simp only [map_zero, zero_add, a.property.1, a.property.2]
/-- Aの次数−1の標準錐とC⁰の同型。targetの負次数零性だけを用いる。 -/
def coneMinusOneEquiv [Subsingleton (D.X (-1))] :
    (mappingCone f).X (-1) ≃ₗ[R] C.X 0 := by
  letI : Unique (D.X (-1)) := ⟨⟨0⟩, fun x => Subsingleton.elim x 0⟩
  exact (coneCoordinateEquiv f (-1)).trans (LinearEquiv.uniqueProd (R := R))
/-- 次数−1の同型は標準錐のsource成分を読む。 -/
theorem coneMinusOneEquiv_apply [Subsingleton (D.X (-1))]
    (x : (mappingCone f).X (-1)) :
    coneMinusOneEquiv f x = (coneCoordinateEquiv f (-1) x).2 := rfl
/-- 標準錐の零性の証人と補正の二等式を元ごとに対応させる。 -/
theorem cone_boundary_iff [Subsingleton (D.X (-1))]
    (z : C.X 1) (b : D.X 0) (x : (mappingCone f).X (-1)) :
    (mappingCone f).d (-1) 0 x = specifiedRepresentative f z b ↔
      C.d 0 1 (coneMinusOneEquiv f x) = z ∧ f.f 0 (coneMinusOneEquiv f x) = b := by
  have hd : coneCoordinateEquiv f 0 ((mappingCone f).d (-1) 0 x) =
      (D.d (-1) 0 (coneCoordinateEquiv f (-1) x).1 +
        f.f 0 (coneMinusOneEquiv f x), -C.d 0 1 (coneMinusOneEquiv f x)) :=
    coneCoordinateEquiv_d_apply f (-1) x
  have hzero : (coneCoordinateEquiv f (-1) x).1 = 0 := Subsingleton.elim _ _
  have hc : coneCoordinateEquiv f 0 (specifiedRepresentative f z b) = (b,-z) :=
    (coneCoordinateEquiv f 0).apply_symm_apply _
  rw [← (coneCoordinateEquiv f 0).injective.eq_iff, hd, hc, hzero]
  simp only [map_zero, zero_add, Prod.mk.injEq, neg_inj]
  exact and_comm
/-- Aの零性の実微分証人とLiftの両逆。選択による存在証人だけに留めない。 -/
def boundaryWitnessEquiv [Subsingleton (D.X (-1))] (z : C.X 1) (b : D.X 0) :
    {x : (mappingCone f).X (-1) //
      (mappingCone f).d (-1) 0 x = specifiedRepresentative f z b} ≃ Lift f z b where
  toFun x := ⟨coneMinusOneEquiv f x.val, (cone_boundary_iff f z b x.val).mp x.property⟩
  invFun a := ⟨(coneMinusOneEquiv f).symm a.val, (cone_boundary_iff f z b _).mpr (by
    rw [LinearEquiv.apply_symm_apply]
    exact a.property)⟩
  left_inv x := by apply Subtype.ext; exact (coneMinusOneEquiv f).symm_apply_apply x.val
  right_inv a := by apply Subtype.ext; exact (coneMinusOneEquiv f).apply_symm_apply a.val

end SpecifiedClass

section NonnegativeTarget
variable {C D : CochainComplex (ModuleCat.{w} ℤ) ℕ} (f : C ⟶ D)
/-- 元の非負複体の指定補正。T0のcochain等号をそのまま保持する。 -/
def NonnegativeLift (z : C.X 1) (b : D.X 0) :=
  {a : C.X 0 // C.d 0 1 a = z ∧ f.f 0 a = b}
/-- 零延長前後の指定解は同じ次数0の同型で両方向に対応する。 -/
def zeroExtensionLiftEquiv (z : C.X 1) (b : D.X 0) :
    Lift (zeroExtensionMap C D f) ((zeroExtensionEquiv C 1).symm z)
      ((zeroExtensionEquiv D 0).symm b) ≃ NonnegativeLift f z b where
  toFun a := ⟨zeroExtensionEquiv C 0 a.val, by
    constructor
    · have h : zeroExtensionEquiv C 1 ((zeroExtension C).d 0 1 a.val) =
          C.d 0 1 (zeroExtensionEquiv C 0 a.val) := zeroExtensionEquiv_d C 0 1 a.val
      rw [a.property.1] at h
      simpa only [LinearEquiv.apply_symm_apply] using h.symm
    · have h : zeroExtensionEquiv D 0 ((zeroExtensionMap C D f).f 0 a.val) =
          f.f 0 (zeroExtensionEquiv C 0 a.val) := zeroExtensionEquiv_map C D f 0 a.val
      rw [a.property.2] at h
      simpa only [LinearEquiv.apply_symm_apply] using h.symm⟩
  invFun a := ⟨(zeroExtensionEquiv C 0).symm a.val, by
    constructor
    · apply (zeroExtensionEquiv C 1).injective
      have h : zeroExtensionEquiv C 1
          ((zeroExtension C).d 0 1 ((zeroExtensionEquiv C 0).symm a.val)) =
          C.d 0 1 (zeroExtensionEquiv C 0 ((zeroExtensionEquiv C 0).symm a.val)) :=
        zeroExtensionEquiv_d C 0 1 _
      rw [h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact a.property.1
    · apply (zeroExtensionEquiv D 0).injective
      have h : zeroExtensionEquiv D 0
          ((zeroExtensionMap C D f).f 0 ((zeroExtensionEquiv C 0).symm a.val)) =
          f.f 0 (zeroExtensionEquiv C 0 ((zeroExtensionEquiv C 0).symm a.val)) :=
        zeroExtensionEquiv_map C D f 0 _
      rw [h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact a.property.2⟩
  left_inv a := by apply Subtype.ext; exact (zeroExtensionEquiv C 0).symm_apply_apply a.val
  right_inv a := by apply Subtype.ext; exact (zeroExtensionEquiv C 0).apply_symm_apply a.val
/-- 元のcocycle条件から零延長の同じ代表元の閉性を生成する。 -/
theorem zeroExtension_closed (z : C.X 1) (hz : C.d 1 2 z = 0) :
    (zeroExtension C).d 1 2 ((zeroExtensionEquiv C 1).symm z) = 0 := by
  apply (zeroExtensionEquiv C 2).injective
  have h : zeroExtensionEquiv C 2
      ((zeroExtension C).d 1 2 ((zeroExtensionEquiv C 1).symm z)) =
      C.d 1 2 (zeroExtensionEquiv C 1 ((zeroExtensionEquiv C 1).symm z)) :=
    zeroExtensionEquiv_d C 1 2 _
  rw [h, LinearEquiv.apply_symm_apply, map_zero, hz]
/-- 元の適合条件を同じ写像の零延長へ移す。 -/
theorem zeroExtension_compatible (z : C.X 1) (b : D.X 0)
    (hb : D.d 0 1 b = f.f 1 z) :
    (zeroExtension D).d 0 1 ((zeroExtensionEquiv D 0).symm b) =
      (zeroExtensionMap C D f).f 1 ((zeroExtensionEquiv C 1).symm z) := by
  apply (zeroExtensionEquiv D 1).injective
  have hd : zeroExtensionEquiv D 1
      ((zeroExtension D).d 0 1 ((zeroExtensionEquiv D 0).symm b)) =
      D.d 0 1 (zeroExtensionEquiv D 0 ((zeroExtensionEquiv D 0).symm b)) :=
    zeroExtensionEquiv_d D 0 1 _
  have hf : zeroExtensionEquiv D 1
      ((zeroExtensionMap C D f).f 1 ((zeroExtensionEquiv C 1).symm z)) =
      f.f 1 (zeroExtensionEquiv C 1 ((zeroExtensionEquiv C 1).symm z)) :=
    zeroExtensionEquiv_map C D f 1 _
  rw [hd, hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hb]
/-- Aの標準錐障害。入力は任意の非負複体、z,bとその適合条件だけである。 -/
def nonnegativeObstruction (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    (mappingCone (zeroExtensionMap C D f)).homology 0 :=
  specifiedObstruction (zeroExtensionMap C D f)
    ((zeroExtensionEquiv C 1).symm z) ((zeroExtensionEquiv D 0).symm b)
    (zeroExtension_closed z hz) (zeroExtension_compatible f z b hb)
/-- 固定target Aの全量化された零性判定。a₀を仮定せず両方向を得る。 -/
theorem nonnegativeObstruction_zero_iff_lift (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    nonnegativeObstruction f z b hz hb = 0 ↔ Nonempty (NonnegativeLift f z b) := by
  letI : Subsingleton ((zeroExtension D).X (-1)) :=
    ModuleCat.subsingleton_of_isZero (zeroExtension_isZero D (-1) (by decide))
  exact (specifiedObstruction_zero_iff_lift (zeroExtensionMap C D f) _ _ _ _).trans
    (zeroExtensionLiftEquiv f z b).nonempty_congr
end NonnegativeTarget

section Nonvacuity
/-- Aの非空虚性検査用。全非負次数に整数群を置き、微分を零とする原始複体。
Implementation notes: 高次数も非零であり、単元集合への退化を用いない。
固定W1–W6の代替としては数えない。 -/
def integerZeroDifferential : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun _ => ModuleCat.of ℤ ℤ) (fun _ => 0) (by intros; simp)
/-- 原始整数複体の各微分の評価API。 -/
theorem integerZeroDifferential_d (i j : ℕ) : integerZeroDifferential.d i j = 0 := by
  simp [integerZeroDifferential, CochainComplex.of]
/-- 恒等比較では整数補正3を厳密に実現する解がある。 -/
theorem identity_lift_nonempty :
    Nonempty (NonnegativeLift (𝟙 integerZeroDifferential) 0 (3 : ℤ)) := by
  refine ⟨⟨(3 : ℤ), ?_, rfl⟩⟩
  rw [integerZeroDifferential_d]
  rfl
/-- 零比較では指定した整数補正1を実現する解がない。 -/
theorem zero_comparison_no_lift :
    ¬Nonempty (NonnegativeLift (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      0 (1 : ℤ)) := by
  rintro ⟨a⟩
  have h : (0 : ℤ) = 1 := a.property.2
  exact zero_ne_one h
/-- 同じ零比較・同じ指定補正で実際に適合条件を満たす。 -/
theorem zero_comparison_compatible :
    integerZeroDifferential.d 0 1 (1 : ℤ) =
      (0 : integerZeroDifferential ⟶ integerZeroDifferential).f 1 (0 : ℤ) := by
  rw [integerZeroDifferential_d]
  rfl
/-- 原始整数例の非零障害を一般Aの同じ経路から得る。 -/
theorem zero_comparison_obstruction_ne_zero :
    nonnegativeObstruction (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      (0 : ℤ) (1 : ℤ) (map_zero _) zero_comparison_compatible ≠ 0 := by
  intro h
  exact zero_comparison_no_lift
    ((nonnegativeObstruction_zero_iff_lift
      (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      (0 : ℤ) (1 : ℤ) (map_zero _) zero_comparison_compatible).mp h)
end Nonvacuity

end AAT.AG.SpecifiedRepairLifting
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_symm_eq
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_inr
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_inl
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_snd
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_fst
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_symm_snd
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_symm_fst
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_d
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_d_apply
#print axioms AAT.AG.SpecifiedRepairLifting.coneCoordinateEquiv_map
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtension
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionMap
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionEquiv_d
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionEquiv_map
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtension_isZero
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionHomologyIso
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionHomologyIso_class
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionHomologyIso_naturality
#print axioms AAT.AG.SpecifiedRepairLifting.Lift
#print axioms AAT.AG.SpecifiedRepairLifting.specifiedRepresentative
#print axioms AAT.AG.SpecifiedRepairLifting.specifiedRepresentative_closed
#print axioms AAT.AG.SpecifiedRepairLifting.specifiedCycle
#print axioms AAT.AG.SpecifiedRepairLifting.specifiedObstruction
#print axioms AAT.AG.SpecifiedRepairLifting.specifiedObstruction_zero_iff_boundary
#print axioms AAT.AG.SpecifiedRepairLifting.specifiedObstruction_zero_iff_lift
#print axioms AAT.AG.SpecifiedRepairLifting.coneMinusOneEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.coneMinusOneEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.cone_boundary_iff
#print axioms AAT.AG.SpecifiedRepairLifting.boundaryWitnessEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.NonnegativeLift
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtensionLiftEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtension_closed
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtension_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.nonnegativeObstruction
#print axioms AAT.AG.SpecifiedRepairLifting.nonnegativeObstruction_zero_iff_lift
#print axioms AAT.AG.SpecifiedRepairLifting.integerZeroDifferential
#print axioms AAT.AG.SpecifiedRepairLifting.integerZeroDifferential_d
#print axioms AAT.AG.SpecifiedRepairLifting.identity_lift_nonempty
#print axioms AAT.AG.SpecifiedRepairLifting.zero_comparison_no_lift
#print axioms AAT.AG.SpecifiedRepairLifting.zero_comparison_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.zero_comparison_obstruction_ne_zero
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting
