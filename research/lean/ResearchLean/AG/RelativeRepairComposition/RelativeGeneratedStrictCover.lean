import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedStrictConditions
import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinatePartition

/-!
# Independent strict generated coordinates for arbitrary local right-hand sides

## Implementation notes

Each local generator uses its own actual differential and full private kernel.
The strict generated predicate reads only public values. The independent actual
predicate reads all original corrections. Full restoration proves these two
predicates equivalent, without restricting any private kernel coordinate.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover
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
local notation "priv" j => ClosedRegion.privateAlwaysEdges U P candidates j

/-- All independent local generated relations and full private kernels. -/
abbrev LocalObject (values : ∀ j, RelativeCover.C2 M (U j) P) (j : I) :=
  FiniteNative.GeneratedRelativeObjects M bases (U j) P (priv j) hlinear (values j) ek ee ef

/-- All actual local equations before imposing any support or shared conditions. -/
abbrev EquationFamily (values : ∀ j, RelativeCover.C2 M (U j) P) :=
  ∀ j, FiniteNative.RelativeEquation M (U j) P (values j)

/-- Every local extraction and restoration is retained pointwise. -/
def familyEquiv (values : ∀ j, RelativeCover.C2 M (U j) P) :
    EquationFamily M U P values ≃ (∀ j, LocalObject M bases U P candidates hlinear ek ee ef values j) :=
  Equiv.piCongrRight (fun j => FiniteNative.generatedRelativeEquiv M bases (U j) P (priv j)
    hlinear (values j) ek ee ef)

/-- Original public support and strict shared-value conditions on the independent generated outputs. -/
def PublicCompatible (values : ∀ j, RelativeCover.C2 M (U j) P)
    (forbidden : Set (EdgeName (K := K)))
    (y : ∀ j, LocalObject M bases U P candidates hlinear ek ee ef values j) : Prop :=
  (∀ j (e : (U j).edges), e.1 ∈ forbidden →
    RelativeGeneratedPublicReadings.publicValue M bases (U j) P (priv j) (y j).1.1 e = 0) ∧
  (∀ j l e (hj : e ∈ (U j).edges) (hl : e ∈ (U l).edges), l ≠ j →
    RelativeGeneratedPublicReadings.publicValue M bases (U j) P (priv j) (y j).1.1 ⟨e,hj⟩ =
      RelativeGeneratedPublicReadings.publicValue M bases (U l) P (priv l) (y l).1.1 ⟨e,hl⟩)

/-- All independent strict original equations, with the full correction families. -/
def EquationObjects (values : ∀ j, RelativeCover.C2 M (U j) P)
    (forbidden : Set (EdgeName (K := K))) :=
  {h : EquationFamily M U P values //
    Subdivision.GeneratedStrictConditions.Compatible M U P forbidden (fun j => (h j).1)}

/-- All generated strict objects, retaining the entire product of private kernels. -/
def Objects (values : ∀ j, RelativeCover.C2 M (U j) P)
    (forbidden : Set (EdgeName (K := K))) :=
  {y : ∀ j, LocalObject M bases U P candidates hlinear ek ee ef values j //
    PublicCompatible M bases U P candidates hlinear ek ee ef values forbidden y}

variable (forbidden : Set (EdgeName (K := K))) (hf : forbidden ⊆ candidates)

include hf in
/-- Complete independent public predicates hold exactly when all restored actual strict predicates hold. -/
theorem compatibility_iff (values : ∀ j, RelativeCover.C2 M (U j) P)
    (y : ∀ j, LocalObject M bases U P candidates hlinear ek ee ef values j) :
    PublicCompatible M bases U P candidates hlinear ek ee ef values forbidden y ↔
      Subdivision.GeneratedStrictConditions.Compatible M U P forbidden
        (fun j => (((familyEquiv M bases U P candidates hlinear ek ee ef values).symm y) j).1) := by
  constructor
  · rintro ⟨hz,hg⟩
    constructor
    · intro j e he
      exact (RelativeGeneratedPublicReadings.restored_value_public M bases (U j) P (priv j)
        hlinear ek ee ef (values j) (y j) e
        (ClosedRegion.candidate_not_private U P candidates j e.1 (hf he))).trans (hz j e he)
    · intro j l e hj hl hlj
      have hvj := RelativeGeneratedPublicReadings.restored_value_public M bases (U j) P (priv j)
        hlinear ek ee ef (values j) (y j) ⟨e,hj⟩
        (ClosedRegion.overlap_not_private U P candidates j l hlj e ⟨hj,hl⟩)
      have hvl := RelativeGeneratedPublicReadings.restored_value_public M bases (U l) P (priv l)
        hlinear ek ee ef (values l) (y l) ⟨e,hl⟩
        (ClosedRegion.overlap_not_private U P candidates l j (Ne.symm hlj) e ⟨hl,hj⟩)
      exact hvj.trans ((hg j l e hj hl hlj).trans hvl.symm)
  · rintro ⟨hz,hg⟩
    constructor
    · intro j e he
      exact (RelativeGeneratedPublicReadings.restored_value_public M bases (U j) P (priv j)
        hlinear ek ee ef (values j) (y j) e
        (ClosedRegion.candidate_not_private U P candidates j e.1 (hf he))).symm.trans (hz j e he)
    · intro j l e hj hl hlj
      have hvj := RelativeGeneratedPublicReadings.restored_value_public M bases (U j) P (priv j)
        hlinear ek ee ef (values j) (y j) ⟨e,hj⟩
        (ClosedRegion.overlap_not_private U P candidates j l hlj e ⟨hj,hl⟩)
      have hvl := RelativeGeneratedPublicReadings.restored_value_public M bases (U l) P (priv l)
        hlinear ek ee ef (values l) (y l) ⟨e,hl⟩
        (ClosedRegion.overlap_not_private U P candidates l j (Ne.symm hlj) e ⟨hl,hj⟩)
      exact hvj.symm.trans ((hg j l e hj hl hlj).trans hvl)

/-- Full independent actual and generated strict objects have both inverse maps. -/
def objectEquiv (values : ∀ j, RelativeCover.C2 M (U j) P) :
    EquationObjects M U P values forbidden ≃ Objects M bases U P candidates hlinear ek ee ef values forbidden where
  toFun h := ⟨familyEquiv M bases U P candidates hlinear ek ee ef values h.1,by
    apply (compatibility_iff M bases U P candidates hlinear ek ee ef forbidden hf values _).mpr
    rw [Equiv.symm_apply_apply]
    exact h.2⟩
  invFun y := ⟨(familyEquiv M bases U P candidates hlinear ek ee ef values).symm y.1,
    (compatibility_iff M bases U P candidates hlinear ek ee ef forbidden hf values y.1).mp y.2⟩
  left_inv h := Subtype.ext ((familyEquiv M bases U P candidates hlinear ek ee ef values).symm_apply_apply h.1)
  right_inv y := Subtype.ext ((familyEquiv M bases U P candidates hlinear ek ee ef values).apply_symm_apply y.1)

/-- Changing any private kernel values preserves the independent public predicate when public coordinates agree. -/
theorem same_public_compatibility (values : ∀ j, RelativeCover.C2 M (U j) P)
    (y z : ∀ j, LocalObject M bases U P candidates hlinear ek ee ef values j)
    (hpublic : ∀ j, (y j).1.1 = (z j).1.1) :
    PublicCompatible M bases U P candidates hlinear ek ee ef values forbidden y ↔
      PublicCompatible M bases U P candidates hlinear ek ee ef values forbidden z := by
  unfold PublicCompatible
  simp only [hpublic]

end AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover
