import ResearchLean.AG.AtlasDefectComposition.SelectedFamilies
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.Fintype.Sum
import Formal.Util.AssertStandardAxioms
/-! # selected block 族の非交和と指定同型

Implementation notes: 積の添字は元の有限添字の非交和である。
零署名の block を許したまま、非零添字の標準同値で射を作る。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
/-- 単位は空の selected block 族である。 -/
def empty : Family S where
  Index := PEmpty.{u+1}
  finite := inferInstance
  subset := PEmpty.elim
/-- 空族の元の添字型は空である。 -/
instance emptyIndexIsEmpty : IsEmpty (empty S).Index := inferInstanceAs (IsEmpty PEmpty.{u+1})
/-- 単独 selected block。Law 全体の二 fiber とは区別する。 -/
def single (A : Set T) : Family S where
  Index := PUnit.{u+1}
  finite := inferInstance
  subset := fun _ => A
/-- 指定積は元の block 添字の非交和であり、多重度を保持する。 -/
def sum (F G : Family S) : Family S where
  Index := F.Index ⊕ G.Index
  finite := by
    letI := Fintype.ofFinite F.Index
    letI := Fintype.ofFinite G.Index
    infer_instance
  subset := Sum.elim F.subset G.subset
/-- 元の全添字の全単射と全署名保存から指定射を生成する。 -/
def reindexHom {F G : Family S} (e : F.Index ≃ G.Index)
    (he : ∀ i, SignatureGeometry.sigma S (G.subset (e i)) = SignatureGeometry.sigma S (F.subset i)) : Hom S F G where
  equiv :=
    { toFun := fun i => ⟨e i.1,by rw [he]; exact i.2⟩
      invFun := fun i => ⟨e.symm i.1,by rw [← he,Equiv.apply_symm_apply]; exact i.2⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_apply i.1)
      right_inv := fun i => Subtype.ext (e.apply_symm_apply i.1) }
  signature_eq := fun i => Subtype.ext (he i.1)
/-- 非交和の非零添字は両側の非零添字の非交和と同じである。 -/
def activeSumEquiv (F G : Family S) : Active S (sum S F G) ≃ Active S F ⊕ Active S G where
  toFun i := match i with
    | ⟨Sum.inl a,ha⟩ => Sum.inl ⟨a,ha⟩
    | ⟨Sum.inr b,hb⟩ => Sum.inr ⟨b,hb⟩
  invFun i := match i with
    | Sum.inl a => ⟨Sum.inl a.1,a.2⟩
    | Sum.inr b => ⟨Sum.inr b.1,b.2⟩
  left_inv := by rintro ⟨a | b,h⟩ <;> rfl
  right_inv := by rintro (a | b) <;> rfl
/-- 指定射の積は元の非零添字全単射の非交和である。 -/
def tensorHom {F F' G G' : Family S} (f : Hom S F F') (g : Hom S G G') : Hom S (sum S F G) (sum S F' G') where
  equiv := (activeSumEquiv S F G).trans ((Equiv.sumCongr f.equiv g.equiv).trans (activeSumEquiv S F' G').symm)
  signature_eq := by
    rintro ⟨a | b,h⟩
    · exact f.signature_eq ⟨a,h⟩
    · exact g.signature_eq ⟨b,h⟩
/-- 非交和の指定結合子は元の添字の標準 Sum.assoc である。 -/
def associatorHom (F G H : Family S) : Hom S (sum S (sum S F G) H) (sum S F (sum S G H)) :=
  reindexHom S (Equiv.sumAssoc _ _ _) (by rintro ((a | b) | c) <;> rfl)
/-- 左単位子は空添字の標準除去である。 -/
def leftUnitorHom (F : Family S) : Hom S (sum S (empty S) F) F :=
  reindexHom S (Equiv.emptySum _ _) (by rintro (a | b); exact a.elim; rfl)
/-- 右単位子は空添字の標準除去である。 -/
def rightUnitorHom (F : Family S) : Hom S (sum S F (empty S)) F :=
  reindexHom S (Equiv.sumEmpty _ _) (by rintro (a | b); rfl; exact b.elim)
/-- 対称性は元の非交和添字の標準入れ替えである。 -/
def braidingHom (F G : Family S) : Hom S (sum S F G) (sum S G F) :=
  reindexHom S (Equiv.sumComm _ _) (by rintro (a | b) <;> rfl)
/-- 同署名の単独 selected block は指定圏で同型である。 -/
def singleHom {A B : Set T} (he : SignatureGeometry.sigma S A = SignatureGeometry.sigma S B) :
    Hom S (single S A) (single S B) := reindexHom S (Equiv.refl _) (fun _ => he.symm)
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
