import Formal.AG.Cohomology.CoverNerve
import Formal.AG.Cohomology.LocalFlatnessGap
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace AAT.AG
namespace Cohomology
namespace FiniteExamples

universe u v w

namespace PseudoCircleGolden

/--
IV.R10 / AC13: three selected charts in the pseudo-circle boundary model.

This is the Lean-side finite golden surface corresponding to the ArchSig v0.4.0
R14 pseudo-circle fixture: local chart witnesses are individually lawful, the
H0-style witness count is zero, but the cyclic boundary mismatch is represented
by a nonzero selected H1 class.  The fixture correspondence is only a docstring
boundary; this file does not import or validate ArchSig JSON.
-/
inductive Chart where
  | A
  | B
  | C
  deriving DecidableEq

/-- IV.R10 / AC13: pairwise boundary overlaps around the pseudo-circle. -/
inductive BoundaryEdge where
  | AB
  | BC
  | CA
  deriving DecidableEq

/-- IV.R10 / AC13: source chart of a selected boundary overlap. -/
def edgeLeft : BoundaryEdge -> Chart
  | BoundaryEdge.AB => Chart.A
  | BoundaryEdge.BC => Chart.B
  | BoundaryEdge.CA => Chart.C

/-- IV.R10 / AC13: target chart of a selected boundary overlap. -/
def edgeRight : BoundaryEdge -> Chart
  | BoundaryEdge.AB => Chart.B
  | BoundaryEdge.BC => Chart.C
  | BoundaryEdge.CA => Chart.A

/-- IV.R10 / AC13: the selected pseudo-circle cover nerve has no triple face. -/
def coverNerve : CoverNerve where
  Chart := Chart
  EdgeComponent := BoundaryEdge
  FaceComponent := Empty
  edgeLeft := edgeLeft
  edgeRight := edgeRight
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => False
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := Empty.elim

/-- IV.R10 / AC13: local chart lawfulness predicate for the selected example. -/
def LocallyLawful (_chart : Chart) : Prop :=
  True

/-- IV.R10 / AC13: every chart is locally lawful. -/
theorem each_chart_lawful (chart : Chart) : LocallyLawful chart :=
  trivial

/--
IV.R10 / AC13: H0-style witness counting sees no obstruction.

This is the "all local charts pass" reading.  It is intentionally separated
from the H1 class below, so the example records the PRD distinction between
local witness counting and gluing obstruction.
-/
def witnessCountingObstruction : Nat :=
  0

/-- IV.R10 / AC13: witness counting reports zero obstruction on the pseudo-circle. -/
theorem h0_witness_counting_sees_no_obstruction :
    witnessCountingObstruction = 0 :=
  rfl

/-- IV.R10 / AC13: selected finite edge-value carrier for the boundary mismatch. -/
abbrev BoundaryMismatchValue : Type :=
  ZMod 2

/--
IV.R10 / AC13: concrete cyclic boundary cocycle.

The three edge values are the selected normalized boundary mismatches around
the pseudo-circle.  The cover-relative H1 class is supplied by
`CoverRelativeH1NonzeroWitness` below, so this finite edge-value surface does
not claim to compute arbitrary cover cohomology.
-/
def boundaryCocycle : BoundaryEdge -> BoundaryMismatchValue
  | BoundaryEdge.AB => 1
  | BoundaryEdge.BC => 0
  | BoundaryEdge.CA => 0

/-- IV.R10 / AC13: the selected finite boundary cocycle is visibly nonzero. -/
theorem boundaryCocycle_AB_nonzero :
    boundaryCocycle BoundaryEdge.AB ≠ 0 := by
  native_decide

/--
IV.R10 / AC13: cover-relative H1 witness for the pseudo-circle golden example.

This is the bridge from the finite edge-value model to the genuine PRD-4
cover-relative cohomology surface.  The concrete cocycle lives in
`K.CechCocycle 1`, its class is the existing `HiddenCouplingData` class
`[hc_U(X)] in H^1(𝒰, Ob_U)`, and nonvanishing is stated in that actual
`K.CoverRelativeHn 1` type.
-/
structure CoverRelativeH1NonzeroWitness {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K) where
  concreteCocycle : K.CechCocycle 1
  concreteCocycle_eq_hidden : concreteCocycle = H.hiddenCouplingCocycle
  concreteClass_eq_hidden :
    K.cohomologyClassSucc 0 concreteCocycle = H.hiddenCouplingClass
  hiddenCouplingClass_nonzero : H.hiddenCouplingClass ≠ h1ZeroClass K

namespace CoverRelativeH1NonzeroWitness

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}
variable {M : GluingMismatchData Ob D}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {H : HiddenCouplingData M K}

/-- IV.R10 / AC13: read the concrete cocycle as a genuine cover-relative H1 class. -/
theorem concreteClass_nonzero (W : CoverRelativeH1NonzeroWitness H) :
    K.cohomologyClassSucc 0 W.concreteCocycle ≠ h1ZeroClass K := by
  rw [W.concreteClass_eq_hidden]
  exact W.hiddenCouplingClass_nonzero

end CoverRelativeH1NonzeroWitness

/--
IV.R10 / AC13: finite specialization of Theorem 7.1's contrapositive.

This theorem calls the existing `localFlatnessGap_no_globalLawfulSection`; it is
not a parallel toy proof.  The conclusion is therefore stated for the real
`CompatibleGlobalLawfulSection H` type attached to the selected
`HiddenCouplingData`.
-/
theorem no_global_lawful_section_by_localFlatnessGap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} {H : HiddenCouplingData M K}
    (W : CoverRelativeH1NonzeroWitness H)
    (Hyp : LocalFlatnessGapHypotheses.{u, v, w} H) :
    ¬ Nonempty (CompatibleGlobalLawfulSection.{u, v, w} H) :=
  localFlatnessGap_no_globalLawfulSection H Hyp W.hiddenCouplingClass_nonzero

/--
IV.R10 / AC13: the pseudo-circle golden example combines the two readings.

The H0-style witness count is zero, while the selected H1 class is nonzero and
therefore no compatible global lawful section exists by Theorem 7.1.
-/
theorem pseudoCircle_h0_invisible_h1_obstructed
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} {H : HiddenCouplingData M K}
    (W : CoverRelativeH1NonzeroWitness H)
    (Hyp : LocalFlatnessGapHypotheses.{u, v, w} H) :
    witnessCountingObstruction = 0 ∧
      H.hiddenCouplingClass ≠ h1ZeroClass K ∧
        ¬ Nonempty (CompatibleGlobalLawfulSection.{u, v, w} H) :=
  ⟨h0_witness_counting_sees_no_obstruction,
    W.hiddenCouplingClass_nonzero,
    no_global_lawful_section_by_localFlatnessGap W Hyp⟩

end PseudoCircleGolden
end FiniteExamples
end Cohomology
end AAT.AG
