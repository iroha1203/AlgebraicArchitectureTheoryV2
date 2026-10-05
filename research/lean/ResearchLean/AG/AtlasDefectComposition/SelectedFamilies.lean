import ResearchLean.AG.AtlasDefectComposition.SignatureGeometry
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic
import Formal.Util.AssertStandardAxioms
/-! # 選択 block 族と署名を保つ射

Implementation notes: 有限添字の subset 族を先に取り、実 Law の fiber 分割より
広い指定対象として扱う。射は非零署名の添字全単射だけである。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
/-- 有限 selected block 族。全 fiber 分割という条件は追加しない。 -/
structure Family (S : T → Set Ω) where
  /-- 元の block 名を保持する有限添字。 -/
  Index : Type u
  /-- 指定対象の有限性。 -/
  finite : Finite Index
  /-- 元の target subset の族。 -/
  subset : Index → Set T
attribute [instance] Family.finite
/-- bottom 以外の全セル署名。 -/
abbrev NonzeroSignature := {s : SignatureGeometry.Signature S // s ≠ ⊥}
/-- 零署名だけを除いた元の添字。重複署名の添字は削除しない。 -/
abbrev Active (F : Family S) := {i : F.Index // SignatureGeometry.sigma S (F.subset i) ≠ ⊥}
/-- 各非零添字が保持する実署名。 -/
def activeSignature (F : Family S) (i : Active S F) : NonzeroSignature S :=
  ⟨SignatureGeometry.sigma S (F.subset i.1),i.2⟩
/-- 指定射は非零添字の署名を保つ全単射である。 -/
structure Hom (F G : Family S) where
  /-- 元の非零 block 名の全単射。 -/
  equiv : Active S F ≃ Active S G
  /-- 各 block の全セル署名を保存する。 -/
  signature_eq : ∀ i, activeSignature S G (equiv i) = activeSignature S F i
/-- 指定射は添字での値の一致によって同定できる。 -/
@[ext] theorem hom_ext {F G : Family S} {f g : Hom S F G}
    (heq : ∀ i, f.equiv i = g.equiv i) : f = g := by
  cases f
  cases g
  congr 1
  exact Equiv.ext heq
/-- selected block 族の指定恒等射。 -/
def homId (F : Family S) : Hom S F F := ⟨Equiv.refl _,fun _ => rfl⟩
/-- selected block 族の指定合成射。 -/
def homComp {F G H : Family S} (f : Hom S F G) (g : Hom S G H) : Hom S F H :=
  ⟨f.equiv.trans g.equiv,fun i => (g.signature_eq (f.equiv i)).trans (f.signature_eq i)⟩
/-- 各指定射を元の全単射の逆で反転する。 -/
def homSymm {F G : Family S} (f : Hom S F G) : Hom S G F :=
  ⟨f.equiv.symm,fun i => by simpa only [Equiv.apply_symm_apply] using (f.signature_eq (f.equiv.symm i)).symm⟩
/-- selected block 族と指定射から構成した圏。 -/
instance familyCategory : Category (Family S) where
  Hom := Hom S
  id := homId S
  comp := homComp S
  id_comp := fun _ => by ext i; rfl
  comp_id := fun _ => by ext i; rfl
  assoc := fun _ _ _ => by ext i; rfl
/-- 指定添字全単射は元の圏で両方向の同型になる。 -/
def isoOfHom {F G : Family S} (f : Hom S F G) : F ≅ G where
  hom := f
  inv := homSymm S f
  hom_inv_id := by
    change homComp S f (homSymm S f) = homId S F
    apply hom_ext S
    intro i
    exact f.equiv.symm_apply_apply i
  inv_hom_id := by
    change homComp S (homSymm S f) f = homId S G
    apply hom_ext S
    intro i
    exact f.equiv.apply_symm_apply i
/-- 非零署名の元の添字 fiber。 -/
abbrev Fiber (F : Family S) (s : NonzeroSignature S) :=
  {i : Active S F // activeSignature S F i = s}
/-- 指定射は各署名の添字 fiber 全単射を生成する。 -/
def fiberEquiv {F G : Family S} (f : Hom S F G) (s : NonzeroSignature S) : Fiber S F s ≃ Fiber S G s where
  toFun i := ⟨f.equiv i.1,(f.signature_eq i.1).trans i.2⟩
  invFun i := ⟨f.equiv.symm i.1,by
    rw [← f.signature_eq (f.equiv.symm i.1),Equiv.apply_symm_apply]
    exact i.2⟩
  left_inv i := by apply Subtype.ext; exact f.equiv.symm_apply_apply i.1
  right_inv i := by apply Subtype.ext; exact f.equiv.apply_symm_apply i.1
/-- 有限な署名 fiber の濃度が一致すると指定添字全単射を構成できる。 -/
def homOfFiberCards {F G : Family S}
    (hc : ∀ s, Nat.card (Fiber S F s) = Nat.card (Fiber S G s)) : Hom S F G := by
  classical
  let e : ∀ s, Fiber S F s ≃ Fiber S G s := fun s => by
    letI := Fintype.ofFinite (Fiber S F s)
    letI := Fintype.ofFinite (Fiber S G s)
    exact Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hc s)
  exact ⟨Equiv.ofFiberEquiv e,Equiv.ofFiberEquiv_map e⟩
/-- selected block 族の非零署名多重度。有限 support は有限実セルから出る。 -/
def multiplicity [Finite Ω] (F : Family S) : NonzeroSignature S →₀ ℕ :=
  Finsupp.ofSupportFinite (fun s => Nat.card (Fiber S F s)) (Set.toFinite _)
/-- 多重度の元評価は元の非零添字 fiber の濃度。 -/
@[simp] theorem multiplicity_apply [Finite Ω] (F : Family S) (s : NonzeroSignature S) :
    multiplicity S F s = Nat.card (Fiber S F s) := rfl
/-- 指定射は各署名の多重度を保存する。 -/
theorem multiplicity_eq_of_hom [Finite Ω] {F G : Family S} (f : Hom S F G) :
    multiplicity S F = multiplicity S G := by
  ext s
  exact Nat.card_congr (fiberEquiv S f s)
/-- 全セル署名の多重度は指定圏での同型類を必要十分に分類する。 -/
theorem multiplicity_classifies [Finite Ω] (F G : Family S) :
    multiplicity S F = multiplicity S G ↔ Nonempty (Hom S F G) := by
  constructor
  · intro h
    exact ⟨homOfFiberCards S (fun s => congrArg (fun m : NonzeroSignature S →₀ ℕ => m s) h)⟩
  · rintro ⟨f⟩
    exact multiplicity_eq_of_hom S f
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
