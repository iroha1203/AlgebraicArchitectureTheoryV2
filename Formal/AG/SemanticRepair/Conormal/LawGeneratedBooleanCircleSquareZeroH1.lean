import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleTupleProfile
import Formal.Util.AssertStandardAxioms
import Mathlib.Tactic

/-!
# Nonzero square-zero conormal H1 on the Boolean circle

This file evaluates the three oriented circle edges in the actual canonical
tuple complex.  The resulting period vanishes on every degree-zero
coboundary, while the explicit raw cocycle has the nonzero square-zero
generator as period.  The Cycle 21 canonical sheafification comparison is then
extended pointwise to cochains and used to transport the nonzero class to the
first sheafified term of the ideal-power sequence.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedBooleanCircleSquareZeroH1

open CategoryTheory
open AAT.AG
open LawGeneratedBooleanCircleSite
open LawGeneratedBooleanCircleLawCore
open LawGeneratedBooleanCircleRawConormalSheaf
open LawGeneratedBooleanCircleConormalSheafification
open LawGeneratedBooleanCircleTupleProfile
open LawGeneratedIdealPowerSequence
open LawGeneratedIdealPowerLiftedSheafification
open LawGeneratedLargeCoefficientCech

local instance : DecidableEq geometry.cover.Index := Classical.decEq _

/-- The degree-zero tuple displaying one selected chart. -/
def vertex (i : Fin 3) : Tuple geometry 0 := fun _ => i

/-- The degree-one tuple displaying one oriented selected edge. -/
def edge (i j : Fin 3) : Tuple geometry 1 := Fin.cases i (fun _ => j)

@[simp] theorem edge_zero (i j : Fin 3) : edge i j 0 = i := rfl
@[simp] theorem edge_one (i j : Fin 3) : edge i j 1 = j := rfl

@[simp] theorem face_edge_zero (i j : Fin 3) :
    face geometry 0 (edge i j) 0 = vertex j := by
  funext k
  fin_cases k
  rfl

@[simp] theorem face_edge_one (i j : Fin 3) :
    face geometry 0 (edge i j) 1 = vertex i := by
  funext k
  fin_cases k
  rfl

/-- Active-value formula for the degree-zero differential on one oriented edge. -/
theorem activeValue_d0_edge
    (b : Cochain geometry rawConormal 0) (i j : Fin 3) :
    activeValue (overlapObject geometry 1 (edge i j))
        (d0 geometry rawConormal b (edge i j)) =
      activeValue (overlapObject geometry 0 (vertex j)) (b (vertex j)) -
        activeValue (overlapObject geometry 0 (vertex i)) (b (vertex i)) := by
  dsimp [d0, differential]
  simp [Fin.sum_univ_succ]
  rw [activeValue_add, activeValue_neg]
  rw [activeValue_faceRestriction 0 b (edge i j) 0 (pairOverlap_not_deep (edge i j)),
    activeValue_faceRestriction 0 b (edge i j) 1 (pairOverlap_not_deep (edge i j))]
  rw [face_edge_zero, face_edge_one]
  simp [sub_eq_add_neg]

/-- The oriented `01 + 12 + 20` period of a raw degree-one cochain. -/
def rawPeriod (c : Cochain geometry rawConormal 1) : AmbientRing :=
  activeValue (overlapObject geometry 1 (edge 0 1)) (c (edge 0 1)) +
    activeValue (overlapObject geometry 1 (edge 1 2)) (c (edge 1 2)) +
    activeValue (overlapObject geometry 1 (edge 2 0)) (c (edge 2 0))

/-- Every raw degree-zero coboundary has zero circle period. -/
theorem rawPeriod_d0 (b : Cochain geometry rawConormal 0) :
    rawPeriod (d0 geometry rawConormal b) = 0 := by
  rw [rawPeriod, activeValue_d0_edge, activeValue_d0_edge,
    activeValue_d0_edge]
  abel

/-- The explicit raw circle cocycle has the nonzero generator as period. -/
theorem rawPeriod_rawOmega : rawPeriod rawOmega = squareZeroGenerator := by
  rw [rawPeriod]
  simp only [activeValue_rawOmega, edge_zero, edge_one]
  simp only [if_neg (show (0 : Fin 3) ≠ 1 by decide),
    if_neg (show (1 : Fin 3) ≠ 2 by decide),
    if_neg (show (2 : Fin 3) ≠ 0 by decide)]
  rw [squareZeroGenerator_add_self, zero_add]

/-- The explicit raw cocycle is not a degree-zero coboundary. -/
theorem rawOmega_not_coboundary :
    ¬ ∃ b : Cochain geometry rawConormal 0,
      rawOmega = d0 geometry rawConormal b := by
  rintro ⟨b, hb⟩
  have hp := congrArg rawPeriod hb
  rw [rawPeriod_rawOmega, rawPeriod_d0] at hp
  exact squareZeroGenerator_ne_zero hp

/-! ## Canonical cochainwise transport to the sheafified first term -/

/-- The square-zero first sheafified coefficient used by the large Cech complex. -/
abbrev SquareZeroX1 := (sheafifiedShortComplex squareZeroCore).X₁.val

/-- Pointwise canonical comparison on generated cochains. -/
noncomputable def toX1Cochain (n : Nat) :
    Cochain geometry rawConormal n →+ Cochain geometry SquareZeroX1 n where
  toFun c sigma := squareZeroRawConormalX1Equiv _ (c sigma)
  map_zero' := by
    funext sigma
    exact map_zero (squareZeroRawConormalX1Equiv _)
  map_add' x y := by
    funext sigma
    exact map_add (squareZeroRawConormalX1Equiv _) _ _

/-- Pointwise inverse canonical comparison on generated cochains. -/
noncomputable def fromX1Cochain (n : Nat) :
    Cochain geometry SquareZeroX1 n →+ Cochain geometry rawConormal n where
  toFun c sigma := (squareZeroRawConormalX1Equiv _).symm (c sigma)
  map_zero' := by
    funext sigma
    exact map_zero (squareZeroRawConormalX1Equiv _).symm
  map_add' x y := by
    funext sigma
    exact map_add (squareZeroRawConormalX1Equiv _).symm _ _

@[simp] theorem from_to_cochain (n : Nat)
    (c : Cochain geometry rawConormal n) :
    fromX1Cochain n (toX1Cochain n c) = c := by
  funext sigma
  exact (squareZeroRawConormalX1Equiv _).symm_apply_apply (c sigma)

@[simp] theorem to_from_cochain (n : Nat)
    (c : Cochain geometry SquareZeroX1 n) :
    toX1Cochain n (fromX1Cochain n c) = c := by
  funext sigma
  exact (squareZeroRawConormalX1Equiv _).apply_symm_apply (c sigma)

theorem toX1Cochain_injective (n : Nat) :
    Function.Injective (toX1Cochain n) := by
  intro x y h
  funext sigma
  exact (squareZeroRawConormalX1Equiv _).injective (congrFun h sigma)

/-- The canonical comparison commutes with every generated face restriction. -/
theorem toX1_faceRestriction (n : Nat)
    (c : Cochain geometry rawConormal n)
    (sigma : Tuple geometry (n + 1)) (i : Fin (n + 2)) :
    squareZeroRawConormalX1Equiv _
        (faceRestriction geometry rawConormal n c sigma i) =
      faceRestriction geometry SquareZeroX1 n (toX1Cochain n c) sigma i := by
  exact squareZeroRawConormalX1Equiv_restrict _ _

/-- The canonical comparison is a cochain map for every generated degree. -/
theorem toX1Cochain_differential (n : Nat)
    (c : Cochain geometry rawConormal n) :
    toX1Cochain (n + 1) (differential geometry rawConormal n c) =
      differential geometry SquareZeroX1 n (toX1Cochain n c) := by
  funext sigma
  classical
  dsimp [toX1Cochain, differential]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : Even i.val
  · simp only [hi, if_true]
    exact toX1_faceRestriction n c sigma i
  · simp only [hi, if_false, map_neg]
    exact congrArg Neg.neg (toX1_faceRestriction n c sigma i)

/-- The pointwise inverse comparison is also a cochain map. -/
theorem fromX1Cochain_differential (n : Nat)
    (c : Cochain geometry SquareZeroX1 n) :
    fromX1Cochain (n + 1) (differential geometry SquareZeroX1 n c) =
      differential geometry rawConormal n (fromX1Cochain n c) := by
  apply toX1Cochain_injective (n + 1)
  rw [to_from_cochain, toX1Cochain_differential, to_from_cochain]

/-- The explicit cocycle transported by the canonical sheafification comparison. -/
noncomputable def squareZeroOmega : Cochain geometry SquareZeroX1 1 :=
  toX1Cochain 1 rawOmega

theorem squareZeroOmega_cocycle_eq :
    d1 geometry SquareZeroX1 squareZeroOmega = 0 := by
  change differential geometry SquareZeroX1 1 squareZeroOmega = 0
  rw [squareZeroOmega, ← toX1Cochain_differential 1 rawOmega]
  have hraw : differential geometry rawConormal 1 rawOmega = 0 := rawOmega_cocycle
  rw [hraw]
  exact map_zero (toX1Cochain 2)

/-- The transported cochain as an actual repository H1 cocycle. -/
noncomputable def squareZeroOmegaCocycle :
    (threeTermComplex geometry SquareZeroX1).H1Cocycle :=
  ⟨squareZeroOmega, squareZeroOmega_cocycle_eq⟩

/-- Canonical transport preserves the non-coboundary result. -/
theorem squareZeroOmega_not_coboundary :
    ¬ ∃ b : Cochain geometry SquareZeroX1 0,
      squareZeroOmega = d0 geometry SquareZeroX1 b := by
  rintro ⟨b, hb⟩
  apply rawOmega_not_coboundary
  refine ⟨fromX1Cochain 0 b, ?_⟩
  have h := congrArg (fun c => fromX1Cochain 1 c) hb
  simpa [squareZeroOmega, d0, fromX1Cochain_differential] using h

/-- The square-zero conormal coefficient has a concrete nonzero H1 class. -/
theorem squareZeroOmegaClass_not_zero :
    ¬ (threeTermComplex geometry SquareZeroX1).H1IsZero
      (h1Class geometry SquareZeroX1 squareZeroOmegaCocycle) := by
  intro hz
  apply squareZeroOmega_not_coboundary
  exact (h1Class_isZero_iff geometry SquareZeroX1 squareZeroOmegaCocycle).1 hz

end LawGeneratedBooleanCircleSquareZeroH1
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleSquareZeroH1
