import ResearchLean.AG.TwoPhase.CoefficientComplex
import Formal.Util.AssertStandardAxioms

/-!
# Cohomology comparison for the two-phase coefficient sequence

This module discharges stage E2 of `G-102-aat-two-phase-obstruction`.
For every finite three-term linear cochain complex it constructs
`H^1 = ker d1 / im d0`, and every cochain map induces the standard map on that
quotient.  Applied to the canonical structural inclusion and semantic quotient
from E1, these maps are exact in the middle.  Vanishing of structural `H^1`
then makes the standard semantic quotient map injective.

The middle-exactness proof uses all three relevant pieces of the E1 short exact
sequence: degree-zero surjectivity lifts a semantic primitive, degree-one
exactness lifts the adjusted cocycle to structural support, and degree-two
injectivity proves that lift is a structural cocycle.
-/

noncomputable section

namespace AAT.AG.TwoPhase

universe u n v w

namespace ThreeCochainComplex

variable {k : Type v} [Field k]

/-- Degree-zero boundaries regarded as degree-one cocycles. -/
def boundaryToCycles (K : ThreeCochainComplex k) :
    K.C0 →ₗ[k] LinearMap.ker K.d1 where
  toFun c := ⟨K.d0 c, by simpa using K.d1_comp_d0 c⟩
  map_add' x y := by ext; simp
  map_smul' scalar x := by ext; simp

/-- Evaluate a degree-zero boundary after it is packaged as a cocycle.  This
public definition-owner API exposes only the existing differential and
introduces no boundary-membership or cohomology premise. -/
@[simp]
theorem boundaryToCycles_apply (K : ThreeCochainComplex k) (cochain : K.C0) :
    (K.boundaryToCycles cochain).1 = K.d0 cochain :=
  rfl

/-- Degree-one cohomology of a finite three-term complex. -/
abbrev H1 (K : ThreeCochainComplex k) : Type w :=
  (LinearMap.ker K.d1) ⧸ LinearMap.range K.boundaryToCycles

/-- The additive quotient structure inherited by the standard `H^1` construction. -/
instance h1AddCommGroup (K : ThreeCochainComplex k) : AddCommGroup K.H1 := by
  dsimp [H1]
  infer_instance

/-- The coefficient-field module structure inherited by the standard `H^1` quotient. -/
instance h1Module (K : ThreeCochainComplex k) : Module k K.H1 := by
  dsimp [H1]
  infer_instance

/-- Finite dimensionality inherited from the finite three-term cochain data. -/
instance h1FiniteDimensional (K : ThreeCochainComplex k) :
    FiniteDimensional k K.H1 := by
  dsimp [H1]
  infer_instance

/-- The explicit vanishing proposition used by the support theorem. -/
def H1Zero (K : ThreeCochainComplex k) : Prop :=
  ∀ x : K.H1, x = 0

namespace Hom

variable {source target : ThreeCochainComplex k}

/-- A cochain map restricted to degree-one cocycles. -/
def cyclesMap (f : Hom source target) :
    LinearMap.ker source.d1 →ₗ[k] LinearMap.ker target.d1 where
  toFun z := ⟨f.f1 z.1, by
    change target.d1 (f.f1 z.1) = 0
    rw [← f.comm1 z.1, z.2]
    exact map_zero f.f2⟩
  map_add' x y := by ext; simp
  map_smul' scalar x := by ext; simp

/-- Evaluate the cocycle restriction of a cochain morphism on underlying
degree-one cochains.  This public definition-owner API exposes the existing
`f1` action and carries no cycle, boundary, or cohomology conclusion as an
extra premise. -/
@[simp]
theorem cyclesMap_apply (f : Hom source target)
    (cycle : LinearMap.ker source.d1) :
    (f.cyclesMap cycle).1 = f.f1 cycle.1 :=
  rfl

/-- Evaluate a difference of mapped cocycles on underlying degree-one
cochains.  This companion definition-owner API exposes only linearity of
`cyclesMap`, avoiding downstream expansion of the kernel subtype's inherited
subtraction. -/
@[simp]
theorem cyclesMap_sub_apply (f : Hom source target)
    (left right : LinearMap.ker source.d1) :
    (f.cyclesMap left - f.cyclesMap right).1 =
      f.f1 left.1 - f.f1 right.1 :=
  rfl

/-- A cochain map sends degree-one boundaries to degree-one boundaries. -/
theorem boundaries_le_comap (f : Hom source target) :
    LinearMap.range source.boundaryToCycles ≤
      (LinearMap.range target.boundaryToCycles).comap f.cyclesMap := by
  rintro _ ⟨c, rfl⟩
  refine ⟨f.f0 c, ?_⟩
  apply Subtype.ext
  exact (f.comm0 c).symm

/-- The standard map on `H^1` induced by a cochain map. -/
def h1Map (f : Hom source target) : source.H1 →ₗ[k] target.H1 :=
  Submodule.mapQ
    (LinearMap.range source.boundaryToCycles)
    (LinearMap.range target.boundaryToCycles)
    f.cyclesMap f.boundaries_le_comap

/-- The induced map is represented by the degree-one map on every cocycle. -/
@[simp]
theorem h1Map_mk (f : Hom source target)
    (z : LinearMap.ker source.d1) :
    f.h1Map ((LinearMap.range source.boundaryToCycles).mkQ z) =
      (LinearMap.range target.boundaryToCycles).mkQ (f.cyclesMap z) :=
  rfl

/-- The range of the induced `H¹` map is the quotient image of the range of
the degree-one cocycle map.  This is the range-level API for `h1Map`; clients
need not unfold either `h1Map` or `Submodule.mapQ`. -/
theorem range_h1Map (f : Hom source target) :
    LinearMap.range f.h1Map =
      (LinearMap.range f.cyclesMap).map
        (LinearMap.range target.boundaryToCycles).mkQ := by
  unfold h1Map Submodule.mapQ
  rw [Submodule.range_liftQ, LinearMap.range_comp]

end Hom

end ThreeCochainComplex

namespace AtomIndexedCoefficientComplex

variable {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
variable {family : DeclaredSemanticFamily D}
variable {N : Cohomology.CoverNerve.{n}} {k : Type v} [Field k]

/-- The `H^1` map induced by the canonical structural inclusion. -/
def structuralH1Map
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k)
    (hE : P.ConditionE) :
    (P.structuralComplex hE).H1 →ₗ[k] P.allComplex.H1 :=
  (P.inclusion hE).h1Map

/-- The standard `H^1` map induced by the canonical semantic quotient. -/
def standardSemanticH1Map
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k)
    (hE : P.ConditionE) :
    P.allComplex.H1 →ₗ[k] (P.semanticComplex hE).H1 :=
  (P.projection hE).h1Map

/--
The canonical comparison sequence is exact at `H^1(F_all)`.

This is the full all-classes statement, not only composition-zero or a selected
subspace statement.
-/
theorem h1_middle_exact
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k)
    (hE : P.ConditionE) :
    Function.Exact (P.structuralH1Map hE) (P.standardSemanticH1Map hE) := by
  let I := P.inclusion hE
  let Q := P.projection hE
  let hshort := P.degreewise_shortExact hE
  apply LinearMap.exact_of_comp_of_mem_range
  · ext x
    apply (Submodule.Quotient.mk_eq_zero _).2
    have hzero : Q.cyclesMap (I.cyclesMap x) = 0 := by
      apply Subtype.ext
      exact P.projection_inclusion_zero1 hE x.1
    rw [hzero]
    exact Submodule.zero_mem _
  · intro x hx
    obtain ⟨z, rfl⟩ :=
      (LinearMap.range P.allComplex.boundaryToCycles).mkQ_surjective x
    change
      (LinearMap.range (P.semanticComplex hE).boundaryToCycles).mkQ
          (Q.cyclesMap z) = 0 at hx
    have hboundary :
        Q.cyclesMap z ∈
          LinearMap.range (P.semanticComplex hE).boundaryToCycles :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    rcases hboundary with ⟨q0, hq0⟩
    obtain ⟨b0, hb0⟩ := hshort.1.2.2 q0
    let adjusted : P.allComplex.C1 := z.1 - P.allComplex.d0 b0
    have hq0_val :
        (P.semanticComplex hE).d0 q0 = Q.f1 z.1 :=
      congrArg Subtype.val hq0
    have hadjusted_ker : Q.f1 adjusted = 0 := by
      calc
        Q.f1 adjusted = Q.f1 z.1 - Q.f1 (P.allComplex.d0 b0) := by
          simp [adjusted]
        _ = Q.f1 z.1 - (P.semanticComplex hE).d0 (Q.f0 b0) := by
          rw [Q.comm0]
        _ = Q.f1 z.1 - (P.semanticComplex hE).d0 q0 := by rw [hb0]
        _ = 0 := sub_eq_zero.mpr hq0_val.symm
    have hadjusted_range : adjusted ∈ LinearMap.range I.f1 := by
      rw [← LinearMap.exact_iff.mp hshort.2.1.2.1]
      exact hadjusted_ker
    rcases hadjusted_range with ⟨s1, hs1⟩
    have hs1_cycle : (P.structuralComplex hE).d1 s1 = 0 := by
      apply hshort.2.2.1
      calc
        I.f2 ((P.structuralComplex hE).d1 s1) =
            P.allComplex.d1 (I.f1 s1) := I.comm1 s1
        _ = P.allComplex.d1 adjusted := by rw [hs1]
        _ = 0 := by
          simp [adjusted, P.allComplex.d1_comp_d0]
        _ = I.f2 0 := (map_zero I.f2).symm
    let sCycle : LinearMap.ker (P.structuralComplex hE).d1 :=
      ⟨s1, hs1_cycle⟩
    refine ⟨
      (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ sCycle,
      ?_⟩
    apply (Submodule.Quotient.eq _).2
    refine ⟨-b0, ?_⟩
    apply Subtype.ext
    change P.allComplex.d0 (-b0) = (P.inclusion hE).f1 s1 - z.1
    change (P.inclusion hE).f1 s1 = adjusted at hs1
    rw [hs1]
    dsimp [adjusted]
    rw [map_neg]
    abel

/--
If structural `H^1` vanishes, the map induced by the canonical semantic
quotient is injective.
-/
theorem standardSemanticH1Map_injective
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k)
    (hE : P.ConditionE)
    (hStructural : (P.structuralComplex hE).H1Zero) :
    Function.Injective (P.standardSemanticH1Map hE) := by
  intro x y hxy
  have hkernel : P.standardSemanticH1Map hE (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hrange : x - y ∈ LinearMap.range (P.structuralH1Map hE) := by
    rw [← LinearMap.exact_iff.mp (P.h1_middle_exact hE)]
    exact hkernel
  rcases hrange with ⟨s, hs⟩
  rw [hStructural s, map_zero] at hs
  exact sub_eq_zero.mp hs.symm

end AtomIndexedCoefficientComplex

end AAT.AG.TwoPhase

#assert_standard_axioms_only AAT.AG.TwoPhase
