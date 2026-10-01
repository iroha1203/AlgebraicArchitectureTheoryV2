import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.StrictCoverSupportAPIs

/-!
# Original affine equations with every forbidden candidate fixed

## Implementation notes

Objects are independently given original affine solutions with zero correction
on forbidden named candidates. Labels are the entire relative zero-cochain
subgroup whose original coboundary is zero on those same edges. The subgroup
retains labels with identical effects as distinct arrows.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace SupportedEquation
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))

/-- Full original labels whose coboundary fixes every forbidden candidate. -/
def Labels : AddSubgroup (RelativeCover.C0 M U P) where
  carrier := {b | ∀ e : U.edges, e.1 ∈ candidates \ allowed →
    (RelativeCover.d0 M U P b).1 e = 0}
  zero_mem' := by
    intro e _
    rw [map_zero]
    rfl
  add_mem' := by
    intro b c hb hc e he
    rw [map_add]
    change (RelativeCover.d0 M U P b).1 e + (RelativeCover.d0 M U P c).1 e = 0
    rw [hb e he,hc e he,zero_add]
  neg_mem' := by
    intro b hb e he
    rw [map_neg]
    change -(RelativeCover.d0 M U P b).1 e = 0
    rw [hb e he,neg_zero]

/-- Membership retains all original label values and imposes only the original edge constraint. -/
theorem mem_labels (b : RelativeCover.C0 M U P) : b ∈ Labels M P U candidates allowed ↔
    ∀ e : U.edges, e.1 ∈ candidates \ allowed → (RelativeCover.d0 M U P b).1 e = 0 := Iff.rfl

/-- A nonzero coboundary on a forbidden original edge excludes that label. -/
theorem not_mem_labels_of_ne (b : RelativeCover.C0 M U P) (e : U.edges)
    (he : e.1 ∈ candidates \ allowed) (hne : (RelativeCover.d0 M U P b).1 e ≠ 0) :
    b ∉ Labels M P U candidates allowed := fun hb => hne (hb e he)

/-- Allowing every candidate retains the complete original relative label group. -/
theorem labels_all : Labels M P U candidates candidates = ⊤ := by
  ext b
  constructor
  · intro _; exact AddSubgroup.mem_top b
  · intro _ e he; exact (he.2 he.1).elim

variable (δ : RelativeCover.C2 M ClosedRegion.all P)

/-- Independent full affine solutions with the same named forbidden edges fixed. -/
def Objects := {h : CoverEquation.Solution M P δ U //
  ∀ e : U.edges, e.1 ∈ candidates \ allowed → h.1.1 e = 0}

/-- The object condition fixes each forbidden original correction value. -/
theorem object_zero (h : Objects M P U candidates allowed δ) (e : U.edges)
    (he : e.1 ∈ candidates \ allowed) : h.1.1.1 e = 0 := h.2 e he

/-- A nonzero original forbidden correction cannot satisfy the object condition. -/
theorem not_supported_of_ne (h : CoverEquation.Solution M P δ U) (e : U.edges)
    (he : e.1 ∈ candidates \ allowed) (hne : h.1.1 e ≠ 0) :
    ¬ (∀ e : U.edges, e.1 ∈ candidates \ allowed → h.1.1 e = 0) :=
  fun hh => hne (hh e he)

/-- Act by every allowed original label while preserving all forbidden correction values. -/
noncomputable def gauge (b : Labels M P U candidates allowed) (h : Objects M P U candidates allowed δ) :
    Objects M P U candidates allowed δ :=
  ⟨Equation.gauge _ _ _ _ b.1 h.1,by
    intro e he
    change h.1.1.1 e + (RelativeCover.d0 M U P b.1).1 e = 0
    rw [h.2 e he,b.2 e he,zero_add]⟩

/-- Zero allowed gauge fixes the full original solution. -/
theorem gauge_zero (h : Objects M P U candidates allowed δ) :
    gauge M P U candidates allowed δ 0 h = h := by
  apply Subtype.ext
  apply Subtype.ext
  change h.1.1 + RelativeCover.d0 M U P 0 = h.1.1
  rw [map_zero,add_zero]

/-- Full original labels compose by their original sum. -/
theorem gauge_add (b c : Labels M P U candidates allowed)
    (h : Objects M P U candidates allowed δ) :
    gauge M P U candidates allowed δ (b+c) h =
      gauge M P U candidates allowed δ b (gauge M P U candidates allowed δ c h) := by
  apply Subtype.ext
  apply Subtype.ext
  change h.1.1 + RelativeCover.d0 M U P (b.1+c.1) =
    (h.1.1 + RelativeCover.d0 M U P c.1) + RelativeCover.d0 M U P b.1
  rw [map_add]
  abel

/-- The supported action retains the full label subgroup. -/
noncomputable instance addAction : AddAction (Labels M P U candidates allowed)
    (Objects M P U candidates allowed δ) where
  vadd := gauge M P U candidates allowed δ
  zero_vadd := gauge_zero M P U candidates allowed δ
  add_vadd := gauge_add M P U candidates allowed δ

/-- Native action groupoid with every original allowed vertex label as an arrow. -/
abbrev Groupoid := ActionCategory (Multiplicative (Labels M P U candidates allowed))
  (Objects M P U candidates allowed δ)

/-- The supported action reads the same original edge correction and coboundary. -/
theorem gauge_value (b : Labels M P U candidates allowed)
    (h : Objects M P U candidates allowed δ) (e : U.edges) :
    (gauge M P U candidates allowed δ b h).1.1.1 e =
      h.1.1.1 e + (RelativeCover.d0 M U P b.1).1 e := rfl

/-- With zero actual defect, zero correction satisfies every original face and every candidate condition. -/
def zeroObject : Objects M P U candidates allowed 0 :=
  ⟨⟨0,by
    change RelativeCover.d1 M U P 0 = -CoverEquation.defect M P 0 U
    simp only [map_zero,CoverEquation.defect_zero,neg_zero]⟩,by intro e he; rfl⟩

end SupportedEquation
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
