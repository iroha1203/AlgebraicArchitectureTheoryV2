import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.SupportedEquation
import ResearchLean.AG.RelativeRepairComposition.IndexedClosedCovers

/-!
# Strict supported gluing of full original local equations

## Implementation notes

Shared original edge corrections must be equal. Separately, shared original
vertex labels must be equal. Each local label is the full permitted subgroup,
so the strict groupoid preserves every stabilizer and does not insert seams.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA uI
namespace StrictSupportedCover
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))

/-- Full permitted local labels strictly agreeing at every shared original vertex. -/
def Labels : AddSubgroup (∀ i,SupportedEquation.Labels M P (U i) candidates allowed) where
  carrier := {b | ∀ i j v (hi : v ∈ (U i).vertices) (hj : v ∈ (U j).vertices),
    (b i).1.1 ⟨v,hi⟩ = (b j).1.1 ⟨v,hj⟩}
  zero_mem' := by intro i j v hi hj; rfl
  add_mem' := by
    intro b c hb hc i j v hi hj
    change (b i).1.1 ⟨v,hi⟩ + (c i).1.1 ⟨v,hi⟩ =
      (b j).1.1 ⟨v,hj⟩ + (c j).1.1 ⟨v,hj⟩
    rw [hb i j v hi hj,hc i j v hi hj]
  neg_mem' := by
    intro b hb i j v hi hj
    change -(b i).1.1 ⟨v,hi⟩ = -(b j).1.1 ⟨v,hj⟩
    rw [hb i j v hi hj]

/-- The strict label condition compares original vertex values, independently of their effects. -/
theorem mem_labels (b : ∀ i,SupportedEquation.Labels M P (U i) candidates allowed) :
    b ∈ Labels M P U candidates allowed ↔
      ∀ i j v (hi : v ∈ (U i).vertices) (hj : v ∈ (U j).vertices),
        (b i).1.1 ⟨v,hi⟩ = (b j).1.1 ⟨v,hj⟩ := Iff.rfl

/-- Different original labels on a shared vertex cannot be strictly glued. -/
theorem not_mem_labels_of_ne (b : ∀ i,SupportedEquation.Labels M P (U i) candidates allowed)
    (i j : I) (v : K.Vertex) (hi : v ∈ (U i).vertices) (hj : v ∈ (U j).vertices)
    (hne : (b i).1.1 ⟨v,hi⟩ ≠ (b j).1.1 ⟨v,hj⟩) :
    b ∉ Labels M P U candidates allowed := fun hb => hne (hb i j v hi hj)

/-- The full compatible original vertex family retained by the strict labels. -/
def localLabels (b : Labels M P U candidates allowed) : IndexedCover.Compatible0 M P U :=
  ⟨fun i => (b.1 i).1,b.2⟩

/-- Strict labels restrict to exactly the same full label on every overlap. -/
theorem label_overlap (b : Labels M P U candidates allowed) (i j : I) :
    RelativeCover.r0 M P (ClosedRegion.inter_left (U i) (U j)) (b.1 i).1 =
      RelativeCover.r0 M P (ClosedRegion.inter_right (U i) (U j)) (b.1 j).1 := by
  apply Subtype.ext
  funext v
  exact b.2 i j v.1 v.2.1 v.2.2

variable (δ : RelativeCover.C2 M ClosedRegion.all P)

/-- Full supported local affine solutions strictly agreeing at every shared original edge. -/
def Objects := {h : ∀ i,SupportedEquation.Objects M P (U i) candidates allowed δ //
  ∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges),
    (h i).1.1.1 ⟨e,hi⟩ = (h j).1.1.1 ⟨e,hj⟩}

/-- Strict objects retain the full compatible original edge family. -/
def localEdges (h : Objects M P U candidates allowed δ) : IndexedCover.Compatible1 M P U :=
  ⟨fun i => (h.1 i).1.1,h.2⟩

/-- Unequal corrections on an original shared edge exclude strict gluing. -/
theorem not_strict_of_ne (h : ∀ i,SupportedEquation.Objects M P (U i) candidates allowed δ)
    (i j : I) (e : EdgeName (K := K)) (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges)
    (hne : (h i).1.1.1 ⟨e,hi⟩ ≠ (h j).1.1.1 ⟨e,hj⟩) :
    ¬ (∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges),
      (h i).1.1.1 ⟨e,hi⟩ = (h j).1.1.1 ⟨e,hj⟩) := fun hh => hne (hh i j e hi hj)

/-- All full strict local labels act on all strict supported objects. -/
noncomputable def gauge (b : Labels M P U candidates allowed) (h : Objects M P U candidates allowed δ) :
    Objects M P U candidates allowed δ :=
  ⟨fun i => SupportedEquation.gauge M P (U i) candidates allowed δ (b.1 i) (h.1 i),by
    intro i j e hi hj
    have hd := congrArg (RelativeCover.d0 M (ClosedRegion.inter (U i) (U j)) P)
      (label_overlap M P U candidates allowed b i j)
    rw [← RelativeCover.r_d0,← RelativeCover.r_d0] at hd
    have hv := congrArg (fun c => c.1 ⟨e,⟨hi,hj⟩⟩) hd
    change (h.1 i).1.1.1 ⟨e,hi⟩ + (RelativeCover.d0 M (U i) P (b.1 i).1).1 ⟨e,hi⟩ =
      (h.1 j).1.1.1 ⟨e,hj⟩ + (RelativeCover.d0 M (U j) P (b.1 j).1).1 ⟨e,hj⟩
    exact congrArg₂ (· + ·) (h.2 i j e hi hj) hv⟩

/-- Zero full strict label fixes the whole local object tuple. -/
theorem gauge_zero (h : Objects M P U candidates allowed δ) :
    gauge M P U candidates allowed δ 0 h = h := by
  apply Subtype.ext
  funext i
  exact SupportedEquation.gauge_zero M P (U i) candidates allowed δ (h.1 i)

/-- Strict gauge composition keeps the full sum of original labels. -/
theorem gauge_add (b c : Labels M P U candidates allowed) (h : Objects M P U candidates allowed δ) :
    gauge M P U candidates allowed δ (b+c) h =
      gauge M P U candidates allowed δ b (gauge M P U candidates allowed δ c h) := by
  apply Subtype.ext
  funext i
  exact SupportedEquation.gauge_add M P (U i) candidates allowed δ (b.1 i) (c.1 i) (h.1 i)

/-- The strict action retains every original compatible local label. -/
noncomputable instance addAction : AddAction (Labels M P U candidates allowed)
    (Objects M P U candidates allowed δ) where
  vadd := gauge M P U candidates allowed δ
  zero_vadd := gauge_zero M P U candidates allowed δ
  add_vadd := gauge_add M P U candidates allowed δ

/-- Strict gluing is a native groupoid with all compatible original arrows. -/
abbrev Groupoid := ActionCategory (Multiplicative (Labels M P U candidates allowed))
  (Objects M P U candidates allowed δ)

end StrictSupportedCover
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
