import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.GeneratedStrictCover

/-!
# Full compatible original-label action on strict generated interfaces

## Implementation notes

The action applies the already generated local action to every component.
No new elimination or section is performed after choosing an allowed range.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
namespace GeneratedCoverAction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
variable (allowed : Set (EdgeName (K := K)))

local notation "Y" => GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
local notation "C" => GeneratedStrictCover.coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
local notation "R" => GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed

/-- The full strict original action is the existing generated action at every region. -/
theorem coordinate_equivariant (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    ((C) (StrictSupportedCover.gauge M P U candidates allowed δ b h)).1 =
      fun i => Multiplicative.ofAdd (b.1 i).1 • ((C) h).1 i := by
  funext i
  exact FiniteNative.generated_solution_equivariant M bases (U i) P
    (ClosedRegion.privateAlwaysEdges U P candidates i) hlinear δ enumK enumEdges enumFaces
    (Multiplicative.ofAdd (b.1 i).1) (h.1 i).1

/-- All full compatible labels act by the generated public and private action formulas. -/
def gauge (b : StrictSupportedCover.Labels M P U candidates allowed) (y : Y) : Y :=
  ⟨fun i => Multiplicative.ofAdd (b.1 i).1 • y.1 i,by
    have he := coordinate_equivariant M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed b ((R) y)
    rw [GeneratedStrictCover.coordinate_restore] at he
    exact he ▸ ((C) (StrictSupportedCover.gauge M P U candidates allowed δ b ((R) y))).2⟩

/-- Zero compatible label fixes all generated coordinates. -/
theorem gauge_zero (y : Y) : gauge M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed 0 y = y := by
  apply Subtype.ext
  funext i
  change (0 : RelativeCover.C0 M (U i) P) +ᵥ y.1 i = y.1 i
  exact zero_vadd _ _

/-- Summing full labels composes the generated actions, without identifying labels by their effects. -/
theorem gauge_add (b c : StrictSupportedCover.Labels M P U candidates allowed) (y : Y) :
    gauge M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed (b+c) y =
      gauge M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed b
        (gauge M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed c y) := by
  apply Subtype.ext
  funext i
  change ((b.1 i).1 + (c.1 i).1) +ᵥ y.1 i =
    (b.1 i).1 +ᵥ ((c.1 i).1 +ᵥ y.1 i)
  exact add_vadd _ _ _

/-- The strict full-label action on the generated relation times every private kernel. -/
instance addAction : AddAction (StrictSupportedCover.Labels M P U candidates allowed) Y where
  vadd := gauge M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
  zero_vadd := gauge_zero M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
  add_vadd := gauge_add M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed

/-- The strict generated groupoid retains all original compatible local arrows. -/
abbrev Groupoid := ActionCategory (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)) Y

/-- Coordinates preserve the complete permitted-label action. -/
theorem equivariant (b : Multiplicative (StrictSupportedCover.Labels M P U candidates allowed))
    (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    (C) (b • h) = b • (C) h := by
  apply Subtype.ext
  exact coordinate_equivariant M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed b.toAdd h

/-- Whole original local equations and generated strict coordinates have inverse native functors. -/
def equivalence : StrictSupportedCover.Groupoid M P U candidates allowed δ ≌
    Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (GeneratedStrictCover.objectEquiv M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)
    (equivariant M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)

/-- Forward then inverse is exactly identity on the original local objects and all labels. -/
theorem functor_inverse :
    (equivalence M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed).functor ⋙
      (equivalence M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed).inverse =
        𝟭 (StrictSupportedCover.Groupoid M P U candidates allowed δ) :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (GeneratedStrictCover.objectEquiv M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)
    (equivariant M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)

/-- Inverse then forward is exactly identity on every public value, private vector and full label. -/
theorem inverse_functor :
    (equivalence M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed).inverse ⋙
      (equivalence M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed).functor =
        𝟭 (Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed) :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (GeneratedStrictCover.objectEquiv M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)
    (equivariant M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)

/-- Every forward arrow has precisely its original full compatible label. -/
theorem functor_label {h j : StrictSupportedCover.Groupoid M P U candidates allowed δ} (b : h ⟶ j) :
    ((equivalence M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed).functor.map b).1 = b.1 := rfl

/-- Every inverse arrow restores precisely the same full compatible label. -/
theorem inverse_label
    {h j : Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed} (b : h ⟶ j) :
    ((equivalence M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed).inverse.map b).1 = b.1 := rfl

end GeneratedCoverAction
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
