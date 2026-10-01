import ResearchLean.AG.RelativeRepairComposition.SymbolicStrictCover
import ResearchLean.AG.RelativeRepairComposition.SymbolicInterfaceAction

/-!
# Strict symbolic cover evaluation on full original arrows

## Implementation notes

The action is transported through exact coordinate evaluation. Its component
formula is proved to be the same parameter-independent public and private label
increments of the one-time local generators. All original compatible vertex
labels, including stabilizers, are retained by both strict inverse functors.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI uV
namespace SymbolicCoverAction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ₀ : RelativeCover.C2 M ClosedRegion.all P)
variable (Δ : V →ₗ[k] RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
variable (allowed : Set (EdgeName (K := K))) (v : V)
local notation "δ" => SymbolicNativeLocal.defectFamily M P δ₀ Δ v
local notation "Y" => SymbolicStrictCover.Objects M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v
local notation "E" => SymbolicStrictCover.objectEquiv M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v
local notation "Labels" => StrictSupportedCover.Labels M P U candidates allowed
local notation "priv" i => ClosedRegion.privateAlwaysEdges U P candidates i

/-- Every full original compatible label acts in the same strict parameter fibre. -/
def gauge (b : Labels) (y : Y) : Y :=
  (E).symm (GeneratedCoverAction.gauge M bases P U candidates hlinear (δ) ek ee ef allowed b ((E) y))

/-- Each local symbolic action has exactly the generated public increment and whole private-kernel increment. -/
theorem gauge_component (b : Labels) (y : Y) (i : I) :
    (gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v b y).1 i =
      SymbolicInterface.fiberGauge
        (FiniteNative.D M bases (U i) P (priv i) hlinear)
        (FiniteNative.F M bases (U i) P (priv i) hlinear)
        (FiniteNative.generatedSection M bases (U i) P (priv i) hlinear ek ee ef)
        (FiniteNative.generatedSection_regular M bases (U i) P (priv i) hlinear ek ee ef)
        (SymbolicNativeLocal.rhsLinear M bases (U i) P Δ) (FiniteNative.rhs M bases (U i) P δ₀)
        (FiniteNative.a M bases (U i) P (priv i) hlinear)
        (FiniteNative.c M bases (U i) P (priv i) hlinear)
        (FiniteNative.D_a_add_F_c M bases (U i) P (priv i) hlinear) v (b.1 i).1 (y.1 i) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- Evaluation commutes with the full original compatible-label action. -/
theorem evaluation_gauge (b : Labels) (y : Y) :
    (E) (gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v b y) =
      GeneratedCoverAction.gauge M bases P U candidates hlinear (δ) ek ee ef allowed b ((E) y) :=
  (E).apply_symm_apply _

/-- Zero full label fixes every symbolic cover coordinate. -/
theorem gauge_zero (y : Y) : gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v 0 y = y := by
  apply (E).injective
  rw [evaluation_gauge, GeneratedCoverAction.gauge_zero]

/-- Sum of complete original compatible labels composes their symbolic cover actions. -/
theorem gauge_add (b c : Labels) (y : Y) :
    gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v (b + c) y =
      gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v b
        (gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v c y) := by
  apply (E).injective
  rw [evaluation_gauge, evaluation_gauge, evaluation_gauge, GeneratedCoverAction.gauge_add]

/-- The strict symbolic parameter fibre carries all full compatible original labels. -/
instance addAction : AddAction Labels Y where
  vadd := gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v
  zero_vadd := gauge_zero M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v
  add_vadd := gauge_add M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v

/-- Full native symbolic cover groupoids retain every compatible original vertex label. -/
abbrev Groupoid := ActionCategory (Multiplicative Labels) Y

/-- Evaluation preserves each entire original compatible label's native action. -/
theorem evaluation_equivariant (b : Multiplicative Labels) (y : Y) :
    (E) (b • y) = b • (E) y := evaluation_gauge M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v b.toAdd y

/-- Evaluation is a full native equivalence onto the same generated strict original cover. -/
def equivalence : Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v ≌
    GeneratedCoverAction.Groupoid M bases P U candidates hlinear (δ) ek ee ef allowed :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative Labels)) (E)
    (evaluation_equivariant M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v)

/-- Forward evaluation followed by inverse is exactly identity on all symbolic objects and original arrows. -/
theorem functor_inverse : (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).functor ⋙
    (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).inverse =
      𝟭 (Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v) :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative Labels)) (E)
    (evaluation_equivariant M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v)

/-- Inverse evaluation followed by forward is exactly identity on all original public values, private vectors and labels. -/
theorem inverse_functor : (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).inverse ⋙
    (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).functor =
      𝟭 (GeneratedCoverAction.Groupoid M bases P U candidates hlinear (δ) ek ee ef allowed) :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative Labels)) (E)
    (evaluation_equivariant M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v)

/-- Forward evaluation keeps every complete compatible original vertex label. -/
theorem functor_label {x y : Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v} (f : x ⟶ y) :
    ((equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).functor.map f).1 = f.1 := rfl

/-- Inverse evaluation keeps every complete compatible original vertex label. -/
theorem inverse_label {x y : GeneratedCoverAction.Groupoid M bases P U candidates hlinear (δ) ek ee ef allowed}
    (f : x ⟶ y) :
    ((equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).inverse.map f).1 = f.1 := rfl

end SymbolicCoverAction
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
