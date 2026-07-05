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
  intro h
  have hv : (1 : ZMod 2).val = (0 : ZMod 2).val := congrArg ZMod.val h
  rw [ZMod.val_one] at hv
  simp at hv

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
R5 / IV-3: finite pseudo-circle specialization of Theorem 7.1 through a
selected overlap-wise global-restriction/coboundary soundness package.

Compared with `no_global_lawful_section_by_localFlatnessGap`, this route does
not take an already-packaged `LocalFlatnessGapHypotheses`; it consumes finite
overlap-wise checks and assembles them into the selected restriction surface.
-/
theorem no_global_lawful_section_by_finiteGlobalRestrictionPointwiseSoundness
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} {H : HiddenCouplingData M K}
    (W : CoverRelativeH1NonzeroWitness H)
    (P : FiniteGlobalRestrictionPointwiseSoundness.{u, v, w} H) :
    ¬ Nonempty (CompatibleGlobalLawfulSection.{u, v, w} H) :=
  localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionPointwiseSoundness H
    P W.hiddenCouplingClass_nonzero

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

/--
R5 / IV-2: Part IV firing package for a selected pseudo-circle nonzero
cover-relative `H^1` instance.

This package is independent of the `HiddenCouplingData` interface above.  It is
the direct Part IV reading consumed by PRD-10 circle-nerve examples: H0-style
witness counting is zero, but a selected degree-one cover-relative class is
nonzero.
-/
structure PartIVCircleNonzeroH1Firing {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  residualCocycle : K.CechCocycle 1
  zeroCocycle : K.CechCocycle 1
  h0WitnessCountingZero : witnessCountingObstruction = 0
  coverRelativeResidualClass_nonzero :
    K.cohomologyClassSucc 0 residualCocycle ≠
      K.cohomologyClassSucc 0 zeroCocycle

namespace PartIVCircleNonzeroH1Firing

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}

/--
R5 / IV-2: the selected pseudo-circle firing records the PRD distinction:
local H0 witness counting is zero while degree-one cover-relative cohomology is
nonzero.
-/
theorem h0_invisible_and_coverRelativeH1_nonzero
    (P : PartIVCircleNonzeroH1Firing K) :
    witnessCountingObstruction = 0 ∧
      K.cohomologyClassSucc 0 P.residualCocycle ≠
        K.cohomologyClassSucc 0 P.zeroCocycle :=
  ⟨P.h0WitnessCountingZero, P.coverRelativeResidualClass_nonzero⟩

/--
R5 / IV-2: the same pseudo-circle nonzero class read through the additive H1
quotient surface added in IV-1.
-/
theorem additiveResidualClass_nonzero
    (P : PartIVCircleNonzeroH1Firing K) :
    K.additiveH1Class P.residualCocycle ≠
      K.additiveH1Class P.zeroCocycle := by
  intro h
  exact P.coverRelativeResidualClass_nonzero
    ((K.cohomologyClassSucc_eq_iff_additiveH1Class_eq
      P.residualCocycle P.zeroCocycle).2 h)

/--
R5 / IV-2: combined H0-invisible and additive-H1-nonzero reading.
-/
theorem h0_invisible_and_additiveH1_nonzero
    (P : PartIVCircleNonzeroH1Firing K) :
    witnessCountingObstruction = 0 ∧
      K.additiveH1Class P.residualCocycle ≠
        K.additiveH1Class P.zeroCocycle :=
  ⟨P.h0WitnessCountingZero, P.additiveResidualClass_nonzero⟩

end PartIVCircleNonzeroH1Firing

end PseudoCircleGolden

namespace BoundaryResidueGolden

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}
variable {𝒰 : CoverRelativeCechCover S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {D : TwoChartConnectingHomomorphism Ob E K}
variable {b : BoundaryMismatchSection Ob E}

/--
IV.R10 / AC14: zero boundary residue glues.

This is the finite-example theorem shape for the `delta(b) = 0` direction of
Theorem 9.2, relative to an explicit `BoundaryResidueHypotheses` package.
-/
theorem zero_boundaryResidue_glues
    (H : BoundaryResidueHypotheses D b)
    (hzero : BoundaryHolonomyVanishes D b) :
    H.globallyUFlat :=
  H.globallyUFlat_of_boundaryHolonomy_zero hzero

/--
IV-7 / IV.R10: theorem-level two-chart soundness for zero boundary agreement.

Unlike `zero_boundaryResidue_glues`, this does not use the Boundary Residue
hypothesis package.  It reads the concrete two-chart boundary equation
`b_U = d0 s` and `d0 s = 0`, then proves `Hol_U = 0`.
-/
theorem zero_boundaryAgreement_forces_zero_holonomy
    (s : D.twoChartCech.C0)
    (hb :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      b.b_U = D.twoChartCech.d0 s)
    (hs :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      D.twoChartCech.d0 s = 0) :
    BoundaryHolonomyVanishes D b :=
  D.boundaryHolonomy_zero_of_twoChartBoundaryAgreement s hb hs

/--
IV.R10 / AC14: nonzero boundary residue prevents gluing.

This is the finite-example theorem shape for the `delta(b) != 0` direction:
if a global U-flat gluing existed, Theorem 9.2 would force zero boundary
holonomy, contradicting the selected nonzero residue.
-/
theorem nonzero_boundaryResidue_blocks_gluing
    (H : BoundaryResidueHypotheses D b)
    (hnonzero : ¬ BoundaryHolonomyVanishes D b) :
    ¬ H.globallyUFlat := by
  intro hflat
  exact hnonzero (H.boundaryHolonomy_zero_of_globallyUFlat hflat)

/-- IV.R10 / AC14: bundled Boundary Residue two-direction example. -/
theorem boundaryResidue_two_direction_example
    (H : BoundaryResidueHypotheses D b) :
    (BoundaryHolonomyVanishes D b -> H.globallyUFlat) ∧
      ((¬ BoundaryHolonomyVanishes D b) -> ¬ H.globallyUFlat) :=
  ⟨zero_boundaryResidue_glues H, nonzero_boundaryResidue_blocks_gluing H⟩

end BoundaryResidueGolden

namespace NerveGolden

/-- IV.R10 / AC14: selected two-chart forest nerve. -/
inductive ForestChart where
  | root
  | leaf
  deriving DecidableEq

/-- IV.R10 / AC14: the unique forest edge. -/
inductive ForestEdge where
  | root_leaf
  deriving DecidableEq

/-- IV.R10 / AC14: cover nerve for a one-edge forest. -/
def forestCoverNerve : CoverNerve where
  Chart := ForestChart
  EdgeComponent := ForestEdge
  FaceComponent := Empty
  edgeLeft := fun _ => ForestChart.root
  edgeRight := fun _ => ForestChart.leaf
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => False
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := Empty.elim

/-- IV.R10 / AC14: explicit forest-cover gluing data with trivial selected H1. -/
def forestCoverGluingData :
    ForestCoverGluingData forestCoverNerve where
  H1 := PUnit
  noTripleFaces := by
    change IsEmpty Empty
    infer_instance
  forestNerve := True
  forestNerve_holds := trivial
  restrictionSurjective := True
  restrictionSurjective_holds := trivial
  baseClass := 0
  baseClass_eq_zero := rfl
  absorbsEveryClassByForestInduction := by
    intro _hforest _hsurj _hfaces x
    cases x
    rfl

/-- IV.R10 / AC14: forest cover example verifies Theorem 12.4's `H^1 = 0`. -/
theorem forestCover_H1_zero :
    ∀ x : forestCoverGluingData.H1, x = 0 :=
  forestCoverGluingData.localGluingSufficiency

/-- IV.R10 / AC14: selected cycle charts for the constant-coefficient nerve example. -/
inductive CycleChart where
  | A
  | B
  | C
  deriving DecidableEq

/-- IV.R10 / AC14: selected cycle edges. -/
inductive CycleEdge where
  | AB
  | BC
  | CA
  deriving DecidableEq

/-- IV.R10 / AC14: cover nerve with one visible 1-cycle and no triple face. -/
def cycleCoverNerve : CoverNerve where
  Chart := CycleChart
  EdgeComponent := CycleEdge
  FaceComponent := Empty
  edgeLeft
    | CycleEdge.AB => CycleChart.A
    | CycleEdge.BC => CycleChart.B
    | CycleEdge.CA => CycleChart.C
  edgeRight
    | CycleEdge.AB => CycleChart.B
    | CycleEdge.BC => CycleChart.C
    | CycleEdge.CA => CycleChart.A
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => False
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := Empty.elim

/-- IV.R10 / AC14: constant-coefficient `b_1` reading for the selected cycle nerve. -/
def cycleConstantCoefficientReading :
    ConstantCoefficientNerveReading cycleCoverNerve where
  k := ZMod 2
  spaceH1 := ZMod 2
  nerveH1 := ZMod 2
  h1LinearEquiv := LinearEquiv.refl (ZMod 2) (ZMod 2)
  dimSpaceH1 := Module.finrank (ZMod 2) (ZMod 2)
  dimNerveH1 := Module.finrank (ZMod 2) (ZMod 2)
  b1 := Module.finrank (ZMod 2) (ZMod 2)
  dimSpace_eq_finrank := rfl
  dimNerve_eq_finrank := rfl
  dimNerve_eq_b1 := rfl

/-- IV.R10 / AC14: cycle nerve example verifies Corollary 12.3's `b_1` reading. -/
theorem cycleNerve_dimH1_eq_b1 :
    cycleConstantCoefficientReading.dimSpaceH1 =
      cycleConstantCoefficientReading.b1 :=
  cycleConstantCoefficientReading.dimH1_eq_b1

end NerveGolden
end FiniteExamples
end Cohomology
end AAT.AG
