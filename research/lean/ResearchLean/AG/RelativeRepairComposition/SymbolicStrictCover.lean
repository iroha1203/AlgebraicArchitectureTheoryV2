import ResearchLean.AG.RelativeRepairComposition.SymbolicNativeLocal
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction

/-!
# Symbolic evaluation commutes with strict original cover constraints

## Implementation notes

The original leaf cover fixes the private sets once. Before evaluation each
local relation includes the common external parameter; all candidate and shared
edge coordinates stay public. Evaluation preserves every public value and every
private kernel coordinate, so candidate zero conditions and strict shared-edge
equalities are exactly the same predicates for every allowed range.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI uV
namespace SymbolicStrictCover
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
local notation "priv" i => ClosedRegion.privateAlwaysEdges U P candidates i
local notation "δ" v => SymbolicNativeLocal.defectFamily M P δ₀ Δ v

/-- The original cover fixes each complete symbolic local relation and its full private kernel once. -/
abbrev LocalFiber (v : V) (i : I) :=
  SymbolicNativeLocal.Fiber M bases (U i) P δ₀ Δ (priv i) hlinear ek ee ef v

variable (allowed : Set (EdgeName (K := K)))

/-- Candidate support and all strict shared original edge values are read from the same retained public coordinates. -/
def PublicCompatible (v : V) (y : ∀ i, LocalFiber M bases P U candidates hlinear δ₀ Δ ek ee ef v i) : Prop :=
  (∀ i (e : (U i).edges), e.1 ∈ candidates \ allowed →
    GeneratedStrictCover.publicValue M bases P U candidates i (y i).1.1 e = 0) ∧
  (∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges), j ≠ i →
    GeneratedStrictCover.publicValue M bases P U candidates i (y i).1.1 ⟨e,hi⟩ =
      GeneratedStrictCover.publicValue M bases P U candidates j (y j).1.1 ⟨e,hj⟩)

/-- The parameter fibre retains all local private kernel freedoms under the strict original public predicates. -/
def Objects (v : V) := {y : ∀ i, LocalFiber M bases P U candidates hlinear δ₀ Δ ek ee ef v i //
  PublicCompatible M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v y}

/-- Evaluation preserves the identical support and strict shared-edge predicate for every allowed range. -/
theorem compatibility_evaluation (v : V)
    (y : ∀ i, LocalFiber M bases P U candidates hlinear δ₀ Δ ek ee ef v i) :
    PublicCompatible M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v y ↔
      GeneratedStrictCover.PublicCompatible M bases P U candidates hlinear (δ v) ek ee ef allowed
        (fun i => SymbolicNativeLocal.fiberEquiv M bases (U i) P δ₀ Δ (priv i) hlinear ek ee ef v (y i)) := Iff.rfl

/-- Every evaluated strict object retains the same public values and every full local private kernel. -/
def objectEquiv (v : V) : Objects M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v ≃
    GeneratedStrictCover.Objects M bases P U candidates hlinear (δ v) ek ee ef allowed where
  toFun y := ⟨fun i => SymbolicNativeLocal.fiberEquiv M bases (U i) P δ₀ Δ (priv i) hlinear ek ee ef v (y.1 i),
    (compatibility_evaluation M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v y.1).mp y.2⟩
  invFun y := ⟨fun i => (SymbolicNativeLocal.fiberEquiv M bases (U i) P δ₀ Δ (priv i) hlinear ek ee ef v).symm (y.1 i),
    y.2⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    exact (SymbolicNativeLocal.fiberEquiv M bases (U i) P δ₀ Δ (priv i) hlinear ek ee ef v).symm_apply_apply (y.1 i)
  right_inv y := by
    apply Subtype.ext
    funext i
    exact (SymbolicNativeLocal.fiberEquiv M bases (U i) P δ₀ Δ (priv i) hlinear ek ee ef v).apply_symm_apply (y.1 i)

/-- Each strict symbolic fibre restores the whole independent original supported leaf equation family. -/
def originalObjectEquiv (v : V) : Objects M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v ≃
    StrictSupportedCover.Objects M P U candidates allowed (δ v) :=
  (objectEquiv M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).trans
    (GeneratedStrictCover.objectEquiv M bases P U candidates hlinear (δ v) ek ee ef allowed).symm

/-- Every retained shared or candidate edge reads the identical original public value after evaluation. -/
theorem evaluated_public_value (v : V)
    (y : Objects M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v) (i : I) (e : (U i).edges) :
    GeneratedStrictCover.publicValue M bases P U candidates i
      ((objectEquiv M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v y).1 i).1.1 e =
        GeneratedStrictCover.publicValue M bases P U candidates i (y.1 i).1.1 e := rfl

/-- Every local internal kernel vector is identical after strict symbolic evaluation. -/
theorem evaluated_private_value (v : V)
    (y : Objects M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v) (i : I) :
    ((objectEquiv M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v y).1 i).2 = (y.1 i).2 := rfl

end SymbolicStrictCover
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
