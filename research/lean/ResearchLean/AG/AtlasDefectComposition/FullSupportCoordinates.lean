import ResearchLean.AG.ResolutionInvariance.LawValueBlockDecomposition
import Formal.Util.AssertStandardAxioms

/-!
# 全台のK0座標と発生ラベル

G-133 W1 のLaw座標同定を支えるAPI。全target台のセル座標を元のセル名と発生ラベルの
組へ同定する。labelのSource証人とreading全射から座標を構成する。

## Implementation notes

Law値型の有限性を仮定しない。Sourceで発生した既存 `LawValueLabel` を使い、
任意の値を結論に合わせて追加しない。台が全targetである仮定はW1の指定入力から放電する。
-/

noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source Cell : Type u}

/-- 全台K0座標の名付きセル・発生ラベル同定。W1の標準座標API。 -/
def fullCoordinateEquiv (laws : FiniteLawFamily Source) (q : Reading Source)
    (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ) :
    CellCoordinate laws q ha Cell support ≃ Cell × LawValueLabel laws where
  toFun c := (c.cell, c.lawValueLabel laws q ha Cell support)
  invFun p := by
    let s := Classical.choose p.2.generated
    have hv := Classical.choose_spec p.2.generated
    exact ⟨p.1, p.2.law, p.2.value, q.read s, by rw [hs]; trivial,
      (lawDescend_commutes laws q ha p.2.law s).trans hv⟩
  left_inv c := by apply CellCoordinate.ext <;> rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply LawValueLabel.ext <;> rfl

/-- 全台座標の逆同定は元のセル名を保持する。 -/
@[simp] theorem fullCoordinateEquiv_symm_cell (laws : FiniteLawFamily Source)
    (q : Reading Source) (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ) (p : Cell × LawValueLabel laws) :
    ((fullCoordinateEquiv laws q ha support hs).symm p).cell = p.1 := rfl

/-- 全台のcochainを名付きセル・発生ラベルの関数へ移送する線形同型。 -/
def fullCochainEquiv (laws : FiniteLawFamily Source) (q : Reading Source)
    (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ) :
    (CellCoordinate laws q ha Cell support → ℚ) ≃ₗ[ℚ]
      (Cell × LawValueLabel laws → ℚ) :=
  LinearEquiv.piCongrLeft ℚ (fun _ : Cell × LawValueLabel laws => ℚ)
    (fullCoordinateEquiv laws q ha support hs)

/-- 全台cochain同型の評価API。 -/
@[simp] theorem fullCochainEquiv_apply (laws : FiniteLawFamily Source)
    (q : Reading Source) (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ)
    (x : CellCoordinate laws q ha Cell support → ℚ) (p : Cell × LawValueLabel laws) :
    fullCochainEquiv laws q ha support hs x p =
      x ((fullCoordinateEquiv laws q ha support hs).symm p) := rfl

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
