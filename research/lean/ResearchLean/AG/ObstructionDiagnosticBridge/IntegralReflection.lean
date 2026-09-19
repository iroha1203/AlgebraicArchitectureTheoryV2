import ResearchLean.AG.ObstructionDiagnosticBridge.GeneratorPresentation
import Mathlib.Data.Rat.Floor
import Formal.Util.AssertStandardAxioms

/-!
# Integral reflection for the obstruction--diagnostic bridge

This module proves the arithmetic core of G-125(B2).  Suppose an integral
edge cochain becomes the edge difference of a rational vertex cochain.  Taking
the floor of that particular rational witness produces an integral vertex
cochain with exactly the same edge difference.

The construction does not treat floor as an additive homomorphism.  It uses
only `Int.floor_add_intCast` after the hypothesis identifies each rational
edge difference with a specific integer.  The block-indexed API reads each
obstruction component through the label map constructed by
`GeneratorPresentation`; deriving its premise from diagnostic zero-class data
and `R_q` remains a later B2 obligation.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution ResolutionInvariance

universe u

namespace IntegralReflection

variable {Vertex Edge Block : Type u}

/--
G-125(B2) witness constructor: floor a rational degree-zero cochain
coordinatewise.  This is not exposed as an additive map.
-/
def floorCorrection (b : Vertex → Block → ℚ) : Vertex → Block → ℤ :=
  fun vertex block => ⌊b vertex block⌋

/--
G-125(B2) arithmetic kernel: if every rational edge difference of `b` equals
the cast of the integral edge value `z`, flooring `b` preserves that edge
difference.  The premise is the rational coboundary witness supplied by the
later diagnostic comparison.
-/
theorem floorCorrection_edgeDifference
    (source target : Edge → Vertex)
    (z : Edge → Block → ℤ)
    (b : Vertex → Block → ℚ)
    (h : ∀ edge block,
      b (target edge) block - b (source edge) block = (z edge block : ℚ))
    (edge : Edge) (block : Block) :
    floorCorrection b (target edge) block -
        floorCorrection b (source edge) block = z edge block := by
  have hsum :
      b (target edge) block = b (source edge) block + (z edge block : ℚ) := by
    linarith [h edge block]
  rw [floorCorrection, floorCorrection, hsum, Int.floor_add_intCast]
  exact add_sub_cancel_left _ _

/--
G-125(B2) witness API: a rational zero-cochain whose edge difference is an
integral cochain yields an explicitly constructed integral zero-cochain with
the same edge difference.
-/
theorem exists_integral_correction
    (source target : Edge → Vertex)
    (z : Edge → Block → ℤ)
    (b : Vertex → Block → ℚ)
    (h : ∀ edge block,
      b (target edge) block - b (source edge) block = (z edge block : ℚ)) :
    ∃ correction : Vertex → Block → ℤ,
      ∀ edge block,
        correction (target edge) block - correction (source edge) block =
          z edge block := by
  refine ⟨floorCorrection b, ?_⟩
  exact floorCorrection_edgeDifference source target z b h

end IntegralReflection

namespace GeneratorPresentation

variable {Source Vertex Edge : Type u}
variable {laws : FiniteLawFamily Source}

/--
G-125(B2) bridge constructor: read a rational diagnostic witness at the label
of every obstruction block, then floor it.  This uses the presentation's
derived quotient map but does not require or claim `R_q`.
-/
def blockFloorCorrection (P : GeneratorPresentation laws)
    (b : Vertex → LawValueLabel laws → ℚ) : Vertex → P.Block → ℤ :=
  fun vertex block => ⌊b vertex (P.blockLabel block)⌋

/--
G-125(B2) bridge kernel: after reading each block through `blockLabel`, an
integral edge value supplied as a rational diagnostic edge difference is also
the edge difference of `blockFloorCorrection`.
-/
theorem blockFloorCorrection_edgeDifference
    (P : GeneratorPresentation laws)
    (source target : Edge → Vertex)
    (z : Edge → P.Block → ℤ)
    (b : Vertex → LawValueLabel laws → ℚ)
    (h : ∀ edge block,
      b (target edge) (P.blockLabel block) -
          b (source edge) (P.blockLabel block) =
        (z edge block : ℚ))
    (edge : Edge) (block : P.Block) :
    P.blockFloorCorrection b (target edge) block -
        P.blockFloorCorrection b (source edge) block =
      z edge block := by
  exact IntegralReflection.floorCorrection_edgeDifference source target z
    (fun vertex block => b vertex (P.blockLabel block)) h edge block

/--
G-125(B2) bridge witness: a block-indexed rational diagnostic coboundary
witness constructs an integral obstruction-side correction.  Producing that
premise from actual diagnostic zero-class data and `R_q` is not assumed solved
by this theorem.
-/
theorem exists_block_integral_correction
    (P : GeneratorPresentation laws)
    (source target : Edge → Vertex)
    (z : Edge → P.Block → ℤ)
    (b : Vertex → LawValueLabel laws → ℚ)
    (h : ∀ edge block,
      b (target edge) (P.blockLabel block) -
          b (source edge) (P.blockLabel block) =
        (z edge block : ℚ)) :
    ∃ correction : Vertex → P.Block → ℤ,
      ∀ edge block,
        correction (target edge) block - correction (source edge) block =
          z edge block := by
  refine ⟨P.blockFloorCorrection b, ?_⟩
  exact P.blockFloorCorrection_edgeDifference source target z b h

end GeneratorPresentation

/-! ## Nonvacuity fixture for a genuinely rational witness -/

namespace IntegralReflectionFixtures

/-- Fixture vertex type with one oriented edge from `false` to `true`. -/
abbrev Vertex := Bool

/-- Fixture edge type containing the single edge. -/
abbrev Edge := PUnit

/-- Fixture coefficient type containing the single coordinate. -/
abbrev Block := PUnit

/-- Source endpoint of the fixture edge. -/
def source : Edge → Vertex := fun _ => false

/-- Target endpoint of the fixture edge. -/
def target : Edge → Vertex := fun _ => true

/-- Nonzero integral edge cochain used by the fixture. -/
def z : Edge → Block → ℤ := fun _ _ => 1

/--
Genuinely rational witness: its values are `1/2` and `3/2`, while their edge
difference is the integer `1`.
-/
def rationalWitness : Vertex → Block → ℚ :=
  fun vertex _ => if vertex then 3 / 2 else 1 / 2

/-- The fixture's rational witness has the declared integral edge difference. -/
theorem rationalWitness_edgeDifference :
    ∀ edge block,
      rationalWitness (target edge) block - rationalWitness (source edge) block =
        (z edge block : ℚ) := by
  intro edge block
  cases edge
  cases block
  norm_num [rationalWitness, source, target, z]

/-- Flooring the genuinely rational fixture preserves its nonzero edge value. -/
theorem floorCorrection_edgeDifference :
    IntegralReflection.floorCorrection rationalWitness (target PUnit.unit) PUnit.unit -
        IntegralReflection.floorCorrection rationalWitness (source PUnit.unit) PUnit.unit =
      z PUnit.unit PUnit.unit :=
  IntegralReflection.floorCorrection_edgeDifference source target z rationalWitness
    rationalWitness_edgeDifference PUnit.unit PUnit.unit

/-- The source value `1/2` shows that the fixture witness is not integer-valued. -/
theorem source_value_not_integral :
    ¬ ∃ value : ℤ, (value : ℚ) = rationalWitness false PUnit.unit := by
  intro h
  obtain ⟨value, hvalue⟩ := h
  have hvalue' : (value : ℚ) = 1 / 2 := by
    simpa [rationalWitness] using hvalue
  have htwiceQ : (2 : ℚ) * value = 1 := by
    linarith
  have htwice : 2 * value = 1 := by
    exact_mod_cast htwiceQ
  omega

end IntegralReflectionFixtures

#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge

end AAT.AG.ObstructionDiagnosticBridge
