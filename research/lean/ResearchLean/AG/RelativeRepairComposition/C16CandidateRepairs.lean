import ResearchLean.AG.RelativeRepairComposition.C16CandidateGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Whole original affine repair values before internal-candidate projection -/
namespace AAT.AG.RelativeRepairComposition.C16CandidateRepairs
open TransportCoherence AbelianLiftingObstruction NativeAffine C16CandidateGeometry

/-- The repeated original candidate word has coefficient one or two in F3. -/
def scale (double : Bool) : ZMod 3 := if double then 2 else 1

/-- The scalar acts on the full original one-coordinate translation vector. -/
def scaled (double : Bool) (v : V) : V := fun j => scale double * v j

/-- Multiplication by the original coefficient is its own inverse in both inputs. -/
theorem scaled_inverse (double : Bool) (v : V) : scaled double (scaled double v) = v := by
  funext j
  cases double
  · simp [scaled,scale]
  · change (2 : ZMod 3) * (2 * v j) = v j
    rw [← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide,one_mul]

/-- Both original loop operations are reconstructed from the full actual internal translation. -/
def operations (double : Bool) (v : V) : ∀ {i j : (geometry double).Vertex},
    (geometry double).Edge i j → Operations (ZMod 3) V :=
  fun e => translation (k := ZMod 3) (Bool.rec (scaled double v) v e)

/-- Original whole candidate zero conditions specify exactly whether the true loop is forbidden. -/
theorem forbidden (double permit : Bool) (S : Set (EdgeName (K := boundaryGeometry)))
    (e : EdgeName (K := geometry double)) :
    e ∈ fixedEdgesForRange (input double).fixed.edges (input double).candidates
      (permissions double permit S).allowed ↔ e.2.2 = true ∧ permit = false := by
  cases permit <;> simp [fixedEdgesForRange,input,ClosedRegion.empty,candidates,permissions]

/-- A complete actual affine repair is generated before projecting away its internal candidate. -/
def repair (double permit : Bool) (S : Set (EdgeName (K := boundaryGeometry)))
    (v : V) (hv : permit = false → v = 0) : (input double).Repairs (permissions double permit S) where
  operation := operations double v
  linear e := by
    change projection (translation (k := ZMod 3) (Bool.rec (scaled double v) v e)) = 1
    exact projection_translation _
  face _ := by
    cases double
    · change translation (k := ZMod 3) (0 : V) *
        (1 * translation (k := ZMod 3) v) = 1 * translation (k := ZMod 3) (scaled false v)
      have hs : scaled false v = v := by funext j; exact one_mul (v j)
      simp only [translation_zero,one_mul,hs]
    · change translation (k := ZMod 3) (0 : V) *
        ((1 * translation (k := ZMod 3) v) * translation (k := ZMod 3) v) =
          1 * translation (k := ZMod 3) (scaled true v)
      have h : v + v = scaled true v := by funext j; simp [scaled,scale,two_mul]
      simp only [translation_zero,one_mul,translation_mul,h]
  fixed_value e he := by
    obtain ⟨he,hp⟩ := (forbidden double permit S e).mp he
    change translation (k := ZMod 3) (Bool.rec (motive := fun _ => V) (scaled double v) v e.2.2) = 1
    rw [he,hv hp]
    exact translation_zero

/-- The independently evaluated internal candidate retains exactly its original full value. -/
theorem repair_internal (double permit : Bool) (S : Set (EdgeName (K := boundaryGeometry)))
    (v : V) (hv : permit = false → v = 0) :
    realCorrection (geometry double) (reference double) (fun _ => 0)
      (fixedEdgesForRange (input double).fixed.edges (input double).candidates
        (permissions double permit S).allowed)
      (repair double permit S v hv) ⟨(),(),true⟩ = v := by
  change (translation (k := ZMod 3) v * (1 : Operations (ZMod 3) V)⁻¹) 0 = v
  simp

/-- The actual original shared operation reads the generated coefficient times the internal value. -/
theorem repair_boundary (double permit : Bool) (S : Set (EdgeName (K := boundaryGeometry)))
    (v : V) (hv : permit = false → v = 0) :
    (input double).boundary (permissions double permit S) (repair double permit S v hv) =
      fun _ => scaled double v := by
  funext ⟨i,j,e⟩
  cases i; cases j; cases e
  change (translation (k := ZMod 3) (scaled double v) * (1 : Operations (ZMod 3) V)⁻¹) 0 = _
  simp

end AAT.AG.RelativeRepairComposition.C16CandidateRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C16CandidateRepairs
