import ResearchLean.AG.RelativeRepairComposition.SymbolicCoverAction
import ResearchLean.AG.RelativeRepairComposition.GeneratedRangeInclusion

/-!
# Every allowed range uses the same symbolic evaluation

## Implementation notes

Only the original forbidden-candidate predicate changes under range relaxation.
Evaluation conjugates the existing original-label range functor through strict
inverse coordinate functors. The commuting square retains every public value,
every private kernel vector and every original vertex-label value.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI uV
namespace SymbolicCoverRanges
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
variable (ef : FiniteElimination.Enumeration K.TwoCell) (v : V)
variable {S T : Set (EdgeName (K := K))}
local notation "δ" => SymbolicNativeLocal.defectFamily M P δ₀ Δ v
local notation "E" s => SymbolicCoverAction.equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef s v

/-- Every allowed range relaxation acts on the same complete symbolic fibres and full original compatible labels. -/
def functor (h : S ⊆ T) :
    SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef S v ⥤
      SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef T v :=
  (E S).functor ⋙ GeneratedRangeInclusion.functor M bases P U candidates hlinear (δ) ek ee ef h ⋙ (E T).inverse

/-- Evaluation commutes strictly with every original allowed-range relaxation on objects and all arrows. -/
theorem evaluation_range (h : S ⊆ T) :
    functor M bases P U candidates hlinear δ₀ Δ ek ee ef v h ⋙ (E T).functor =
      (E S).functor ⋙ GeneratedRangeInclusion.functor M bases P U candidates hlinear (δ) ek ee ef h := by
  change (E S).functor ⋙ (GeneratedRangeInclusion.functor M bases P U candidates hlinear (δ) ek ee ef h ⋙
    ((E T).inverse ⋙ (E T).functor)) = _
  rw [SymbolicCoverAction.inverse_functor, Functor.comp_id]

/-- Range relaxation leaves every original public coordinate of every symbolic local relation unchanged. -/
theorem public_value (h : S ⊆ T)
    (y : SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef S v) (i : I) :
    (((functor M bases P U candidates hlinear δ₀ Δ ek ee ef v h).obj y).back.1 i).1.1 =
      (y.back.1 i).1.1 := rfl

/-- Range relaxation leaves every entire original local private-kernel vector unchanged. -/
theorem private_value (h : S ⊆ T)
    (y : SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef S v) (i : I) :
    (((functor M bases P U candidates hlinear δ₀ Δ ek ee ef v h).obj y).back.1 i).2 =
      (y.back.1 i).2 := rfl

/-- Range relaxation preserves every original included vertex value of every full compatible label. -/
theorem label_value (h : S ⊆ T)
    {x y : SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef S v}
    (b : x ⟶ y) (i : I) (w : (U i).vertices) :
    ((((functor M bases P U candidates hlinear δ₀ Δ ek ee ef v h).map b).1.toAdd).1 i).1.1 w =
      (b.1.toAdd.1 i).1.1 w := rfl

/-- Successive original range inclusions compose on the full symbolic native groupoid. -/
theorem functor_comp {W : Set (EdgeName (K := K))} (h : S ⊆ T) (g : T ⊆ W) :
    functor M bases P U candidates hlinear δ₀ Δ ek ee ef v h ⋙
      functor M bases P U candidates hlinear δ₀ Δ ek ee ef v g =
        functor M bases P U candidates hlinear δ₀ Δ ek ee ef v (h.trans g) := by
  change (E S).functor ⋙ (GeneratedRangeInclusion.functor M bases P U candidates hlinear (δ) ek ee ef h ⋙
    (((E T).inverse ⋙ (E T).functor) ⋙
      GeneratedRangeInclusion.functor M bases P U candidates hlinear (δ) ek ee ef g)) ⋙ (E W).inverse = _
  rw [SymbolicCoverAction.inverse_functor, Functor.id_comp, GeneratedRangeInclusion.functor_comp]
  rfl

end SymbolicCoverRanges
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
