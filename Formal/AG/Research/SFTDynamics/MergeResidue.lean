import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Formal.AG.Research.SFTDynamics.ForceSchema

/-!
SFT v2 Lean tower, target **L3** (skeleton note §10; SFT v2 text Part III and
付録 D.5).

This file fixes the abelian, constant-fiber, trivial-transport reading of the
diamond merge residue and the stage-1 obstruction of the merge-diagnosis
filtration:

* `TwoBranchLawDatum` carries the two transported law sections on the selected
  overlap and a selected adjustment subgroup (SFT 定義 20.3: the adjustment
  subgroup is the supplied image of `δ⁰`; it is selected data here, not
  computed from a vertex complex).
* `mismatch` is the overlap difference; `ObstructionVanishes` is the
  predicate-level membership `mismatch ∈ adjust` (SFT 段階1 通過).  In this
  constant-fiber regime the stage-1 class coincides with the diamond merge
  residue (SFT 定義 16.1 と 定義 20.3 の注記).
* `compositeResidue` is the pointwise difference of the two application
  orders; `compositeResidue_eq_zero_of_disjoint` derives residue zero from the
  distant-commutation theorem of L2 (SFT 定理 21.1 の二枝 Lean shadow).
* The canonical rounding datum of SFT 付録 D.5 is instantiated on `ZMod 2`
  with pinned adjustments (`⊥`): its obstruction does not vanish.  Relaxing
  the adjustments to `⊤` makes it vanish — resolution is a choice.

Claim boundary: constant fiber, identity transports, one selected overlap,
supplied adjustment subgroup, abelian coefficients.  The nerve-level Čech
complex with vertex coboundaries (the ∂Δ² witness of SFT 付録 D.12), stage 0
(cocone validity), and stage 2 (positive-degree Tor) are outside this file.
Nothing is claimed about real merges, textual diffs, or extraction.
-/

namespace Formal.AG.Research
namespace SFTDynamics

/--
A two-branch law datum on a selected overlap (SFT 定義 20.3 の有限読み).

`sectionA` and `sectionC` are the transported law sections of the two
branches on the overlap; `adjust` is the selected adjustment subgroup (the
supplied image of `δ⁰` in the additive regime).
-/
structure TwoBranchLawDatum (Coeff : Type u) [AddCommGroup Coeff] where
  sectionA : Coeff
  sectionC : Coeff
  adjust : AddSubgroup Coeff

namespace TwoBranchLawDatum

variable {Coeff : Type u} [AddCommGroup Coeff]

/-- The mismatch cochain on the overlap (SFT 定義 20.3). -/
def mismatch (d : TwoBranchLawDatum Coeff) : Coeff :=
  d.sectionA - d.sectionC

/--
Stage-1 pass: the mismatch is killed by the selected adjustments
(SFT 定義 20.3「段階1 通過 := [m] = 0」の predicate-level 読み).
-/
def ObstructionVanishes (d : TwoBranchLawDatum Coeff) : Prop :=
  d.mismatch ∈ d.adjust

/-- With full adjustments every mismatch is absorbed. -/
theorem obstructionVanishes_of_top (d : TwoBranchLawDatum Coeff)
    (h : d.adjust = ⊤) : d.ObstructionVanishes := by
  simp [ObstructionVanishes, h]

/--
With pinned adjustments (`⊥`, the both-branches-pinned regime of SFT 付録
D.5) the obstruction vanishes exactly when the two transported sections agree.
-/
theorem obstructionVanishes_iff_of_bot (d : TwoBranchLawDatum Coeff)
    (h : d.adjust = ⊥) :
    d.ObstructionVanishes ↔ d.sectionA = d.sectionC := by
  simp [ObstructionVanishes, mismatch, h, sub_eq_zero]

end TwoBranchLawDatum

/-! ## Composite residue and the L2 bridge -/

/--
The composite residue of two force schemas at a context: the pointwise
difference of the two application orders (SFT 定義 16.1 のダイヤモンドを
自明輸送で読んだ場合の残差).
-/
def compositeResidue {Ctx : Type u} {Coeff : Type v} [AddCommGroup Coeff]
    (f g : ForceSchema Ctx Coeff) (φ : FieldConfig Ctx Coeff) (c : Ctx) :
    Coeff :=
  f.act (g.act φ) c - g.act (f.act φ) c

/--
Disjoint closures force zero composite residue at every context
(SFT 定理 21.1 の二枝 Lean shadow; 定理 14.3 の系).
-/
theorem compositeResidue_eq_zero_of_disjoint
    {Ctx : Type u} {Coeff : Type v} [AddCommGroup Coeff]
    (f g : ForceSchema Ctx Coeff) (h : ForceSchema.DisjointClosures f g)
    (φ : FieldConfig Ctx Coeff) (c : Ctx) :
    compositeResidue f g φ c = 0 := by
  unfold compositeResidue
  rw [ForceSchema.distant_commute f g h φ]
  exact sub_self _

/-! ## Canonical instance: the rounding conflict of SFT 付録 D.5 -/

/--
The canonical rounding datum: branch A pins `floor = 0`, branch C pins
`half-even = 1`, and both branches' tests pin the adjustments to `⊥`
(SFT 付録 D.5).
-/
def roundingDatum : TwoBranchLawDatum (ZMod 2) where
  sectionA := 0
  sectionC := 1
  adjust := ⊥

/-- The canonical mismatch is the nonzero class `1 ∈ Z/2` (SFT 付録 D.5). -/
theorem roundingDatum_mismatch : roundingDatum.mismatch = 1 := by
  decide

/--
The canonical stage-1 obstruction does **not** vanish: the textual merge may
pass while the law data cannot be glued within the allowed adjustments
(SFT 付録 D.5 の非零衝突類).
-/
theorem roundingDatum_not_obstructionVanishes :
    ¬ roundingDatum.ObstructionVanishes := by
  simp only [TwoBranchLawDatum.ObstructionVanishes, roundingDatum,
    AddSubgroup.mem_bot]
  decide

/--
Relaxing the adjustments to `⊤` resolves the conflict — resolution is an
explicit gluing choice, not a theorem (SFT 付録 D.5 の解決の読み).
-/
def resolvedRoundingDatum : TwoBranchLawDatum (ZMod 2) :=
  { roundingDatum with adjust := ⊤ }

theorem resolvedRoundingDatum_obstructionVanishes :
    resolvedRoundingDatum.ObstructionVanishes :=
  TwoBranchLawDatum.obstructionVanishes_of_top _ rfl

end SFTDynamics
end Formal.AG.Research
