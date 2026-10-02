import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedStrictCover

/-!
# Every range inclusion uses the same independent local generator

## Implementation notes

Only candidate permission predicates change. Every full local relation,
section, public value and private kernel coordinate remains literal. Actual
extraction and full restoration commute with every range inclusion.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k) (x : M.A s),
  M.edge e (a • x) = a • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)

variable (S V : Set (EdgeName (K := K))) (hSV : S ⊆ V)

/-- Enlarging permissions retains every independently generated local object. -/
def includeObjects (values : ∀ j, RelativeCover.C2 M (U j) P)
    (y : RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ S)) :
    RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ V) :=
  ⟨y.1,⟨fun j e he => y.2.1 j e ⟨he.1,fun hs => he.2 (hSV hs)⟩,y.2.2⟩⟩

/-- Enlarging permissions retains every full actual local equation. -/
def includeEquations (values : ∀ j, RelativeCover.C2 M (U j) P)
    (h : RelativeGeneratedStrictCover.EquationObjects M U P values (candidates \ S)) :
    RelativeGeneratedStrictCover.EquationObjects M U P values (candidates \ V) :=
  ⟨h.1,⟨fun j e he => h.2.1 j e ⟨he.1,fun hs => he.2 (hSV hs)⟩,h.2.2⟩⟩

/-- The independent actual-to-generated extraction commutes with every permission inclusion. -/
theorem coordinate_include (values : ∀ j, RelativeCover.C2 M (U j) P)
    (h : RelativeGeneratedStrictCover.EquationObjects M U P values (candidates \ S)) :
    RelativeGeneratedStrictCover.objectEquiv M bases U P candidates hlinear ek ee ef
      (candidates \ V) Set.diff_subset values
      (includeEquations M U P candidates S V hSV values h) =
    includeObjects M bases U P candidates hlinear ek ee ef S V hSV values
      (RelativeGeneratedStrictCover.objectEquiv M bases U P candidates hlinear ek ee ef
        (candidates \ S) Set.diff_subset values h) := rfl

/-- Full actual restoration commutes with every permission inclusion. -/
theorem restore_include (values : ∀ j, RelativeCover.C2 M (U j) P)
    (y : RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ S)) :
    (RelativeGeneratedStrictCover.objectEquiv M bases U P candidates hlinear ek ee ef
      (candidates \ V) Set.diff_subset values).symm
      (includeObjects M bases U P candidates hlinear ek ee ef S V hSV values y) =
    includeEquations M U P candidates S V hSV values
      ((RelativeGeneratedStrictCover.objectEquiv M bases U P candidates hlinear ek ee ef
        (candidates \ S) Set.diff_subset values).symm y) := rfl

/-- The full generated data at every region is unchanged by enlarging permissions. -/
theorem include_component (values : ∀ j, RelativeCover.C2 M (U j) P)
    (y : RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ S)) (j : I) :
    (includeObjects M bases U P candidates hlinear ek ee ef S V hSV values y).1 j = y.1 j := rfl

/-- Successive permission inclusions retain the identical full coordinate family. -/
theorem include_comp (values : ∀ j, RelativeCover.C2 M (U j) P)
    (W : Set (EdgeName (K := K))) (hVW : V ⊆ W)
    (y : RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ S)) :
    includeObjects M bases U P candidates hlinear ek ee ef V W hVW values
      (includeObjects M bases U P candidates hlinear ek ee ef S V hSV values y) =
    includeObjects M bases U P candidates hlinear ek ee ef S W (Set.Subset.trans hSV hVW) values y := rfl

end AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges
