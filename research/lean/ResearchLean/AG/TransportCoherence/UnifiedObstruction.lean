import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Unified route-level transport obstruction

This module supplies the G-106/J4 connection theorems.  It first records the
single-disk positive example in the same route evaluator as the closed
obstructions.  It then defines genuinely specialized formulas for the finite
double diamond and three-reading triangle and proves that their raw values,
conjugacy classes, and all-reselection nonvanishing predicates agree with the
unified typed-pasting definitions.

The triangle formula composes its local G-101 canonical comparators in temporal
order before taking a quotient.  It is therefore not the generally incorrect
product of its two local raw defects.
-/

namespace AAT.AG.TransportCoherence

universe u

open CategoryTheory
open AtomFoundation

/-! ## General closed-pasting nonvanishing and its J2 consequence -/

/-- The closed route class is nonidentity at every allowed edge coordinate. -/
def ClosedPastingObstructionNonvanishing
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cell : G.ThreeCell) : Prop :=
  ∀ reselection : EdgeReselection data.lift,
    closedPastingObstructionClass data reselection cell ≠ ConjClasses.mk 1

/-- Pointwise coherence makes every closed route obstruction equal to identity. -/
theorem coherentAt_closedPastingRawObstruction_eq_one
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    (coherent : CoherentAt data reselection) (cell : G.ThreeCell) :
    closedPastingRawObstruction data reselection cell = 1 :=
  closedPastingRawObstruction_eq_one_of_syzygy data reselection
    (syzygyCompatible_of_coherentAt data reselection coherent) cell

/-- An everywhere-nonidentity closed route class forbids coherentization. -/
theorem closedPastingObstructionNonvanishing_not_coherentizable
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cell : G.ThreeCell)
    (nonvanishing : ClosedPastingObstructionNonvanishing data cell) :
    ¬ Coherentizable data := by
  rintro ⟨reselection, coherent⟩
  apply nonvanishing reselection
  unfold closedPastingObstructionClass
  rw [coherentAt_closedPastingRawObstruction_eq_one data reselection coherent cell]

/-- The same closed-class hypothesis forbids orbit vanishing by the J2 theorem. -/
theorem closedPastingObstructionNonvanishing_not_obstructionVanishes
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cell : G.ThreeCell)
    (nonvanishing : ClosedPastingObstructionNonvanishing data cell) :
    ¬ TransportObstructionVanishes data := by
  intro vanishes
  exact closedPastingObstructionNonvanishing_not_coherentizable
    data cell nonvanishing
      ((transportObstructionVanishes_iff_coherentizable data).mp vanishes)

/-! ## The single-disk positive instance in the route evaluator -/

/-- The unique disk face with empty outer whiskers. -/
def singleDiskWhiskeredFace (Marker : Type u) :
    WhiskeredFace
      (singleDiskPresentation Marker).toFiniteTransportTwoPresentation
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker) where
  cell := .face
  incoming := .nil SingleDiskVertex.source
  outgoing := .nil SingleDiskVertex.target
  orientation := .forward

/-- The typed rewrite step associated with the unique disk face. -/
def singleDiskRewriteStep (Marker : Type u) :
    RewriteStep
      (singleDiskPresentation Marker).toFiniteTransportTwoPresentation
      (singleDiskLeftPath Marker) (singleDiskRightPath Marker) where
  face := singleDiskWhiskeredFace Marker
  before_eq := by
    simp [singleDiskWhiskeredFace, WhiskeredFace.before,
      WhiskeredFace.localBefore, singleDiskPresentation,
      PresentedPath.append]
  after_eq := by
    simp [singleDiskWhiskeredFace, WhiskeredFace.after,
      WhiskeredFace.localAfter, singleDiskPresentation,
      PresentedPath.append]

/-- The one-step typed pasting of the unique disk face. -/
def singleDiskPasting (Marker : Type u) :
    RewritePasting
      (singleDiskPresentation Marker).toFiniteTransportTwoPresentation
      (singleDiskLeftPath Marker) (singleDiskRightPath Marker) :=
  .cons (singleDiskRewriteStep Marker)
    (@RewritePasting.nil
      (singleDiskPresentation Marker).toFiniteTransportTwoPresentation
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker)
      (singleDiskRightPath Marker))

/-- A one-face disk route reduces to the original J1 raw 2-cell defect. -/
theorem singleDiskPastingRawDefect_eq_rawTwoCellDefect
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U)
    (reselection : EdgeReselection data.lift) :
    pastingRawDefect data reselection (singleDiskPasting U.Atom) =
      rawTwoCellDefect data reselection SingleDiskTwoCell.face := by
  simp [pastingRawDefect, authoredPastingComparator,
    canonicalPastingComparator, pastingComparator, singleDiskPasting,
    singleDiskRewriteStep, singleDiskWhiskeredFace,
    orientedFaceComparator, authoredComparatorFamily,
    canonicalComparatorFamily, rawTwoCellDefect]
  have authoredNil :
      whiskerFiberAut data.lift reselection
          (data.comparator SingleDiskTwoCell.face)
          (.nil (SingleDiskVertex.target : SingleDiskVertex U.Atom)) =
        data.comparator SingleDiskTwoCell.face := by
    simpa [singleDiskPresentation] using
      (whiskerFiberAut_nil data.lift reselection
        (vertex := (SingleDiskVertex.target : SingleDiskVertex U.Atom))
        (show PackageFiberAut
            (data.lift.package
              (SingleDiskVertex.target : SingleDiskVertex U.Atom)) from
          data.comparator SingleDiskTwoCell.face))
  have canonicalNil :
      whiskerFiberAut data.lift reselection
          (canonicalTwoCellComparator data reselection SingleDiskTwoCell.face)
          (.nil (SingleDiskVertex.target : SingleDiskVertex U.Atom)) =
        canonicalTwoCellComparator data reselection SingleDiskTwoCell.face := by
    simpa [singleDiskPresentation] using
      (whiskerFiberAut_nil data.lift reselection
        (vertex := (SingleDiskVertex.target : SingleDiskVertex U.Atom))
        (show PackageFiberAut
            (data.lift.package
              (SingleDiskVertex.target : SingleDiskVertex U.Atom)) from
          canonicalTwoCellComparator data reselection
            SingleDiskTwoCell.face))
  rw [authoredNil, canonicalNil]

/-- Disk absorption is identity in the unified route-level evaluator. -/
theorem singleDiskPastingRawDefect_after_absorption
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    pastingRawDefect data (singleDiskAbsorbingReselection data)
        (singleDiskPasting U.Atom) = 1 := by
  rw [singleDiskPastingRawDefect_eq_rawTwoCellDefect]
  exact (rawTwoCellDefect_eq_one_iff data
    (singleDiskAbsorbingReselection data) SingleDiskTwoCell.face).2
      (singleDisk_canonicalComparator_after_absorption data).symm

/-! ## Specialized double-diamond formula and agreement -/

/--
The specialized diamond formula is the ratio of the two local J1 defects.
It is defined without mentioning a 3-cell pasting evaluator.
-/
noncomputable def finiteDoubleDiamondSpecializedRawObstruction
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    PackageFiberAut finiteWitnessTargetPackage :=
  (show PackageFiberAut finiteWitnessTargetPackage from
    rawTwoCellDefect finiteDoubleDiamondData reselection
      DoubleDiamondTwoCell.second)⁻¹ *
    (show PackageFiberAut finiteWitnessTargetPackage from
      rawTwoCellDefect finiteDoubleDiamondData reselection
        DoubleDiamondTwoCell.first)

/-- Conjugacy class extracted from the specialized diamond formula. -/
noncomputable def finiteDoubleDiamondSpecializedObstructionClass
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    ConjClasses (PackageFiberAut finiteWitnessTargetPackage) :=
  ConjClasses.mk (finiteDoubleDiamondSpecializedRawObstruction reselection)

/-- All-coordinate nonvanishing stated solely with the specialized formula. -/
def FiniteDoubleDiamondSpecializedNonvanishing : Prop :=
  ∀ reselection : EdgeReselection finiteDoubleDiamondData.lift,
    finiteDoubleDiamondSpecializedObstructionClass reselection ≠
      ConjClasses.mk 1

/-- Empty target whiskering is literal on the concrete double diamond. -/
private theorem finiteDoubleDiamond_whisker_nil
    (reselection : EdgeReselection finiteDoubleDiamondData.lift)
    (automorphism : PackageFiberAut finiteWitnessTargetPackage) :
    whiskerFiberAut finiteDoubleDiamondLiftData reselection
        (i := (SingleDiskVertex.target :
          SingleDiskVertex FiniteModel.carrier.Atom))
        (j := (SingleDiskVertex.target :
          SingleDiskVertex FiniteModel.carrier.Atom)) automorphism
        (.nil (SingleDiskVertex.target :
          SingleDiskVertex FiniteModel.carrier.Atom)) =
      automorphism :=
  whiskerFiberAut_nil finiteDoubleDiamondLiftData reselection
    (vertex := (SingleDiskVertex.target :
      SingleDiskVertex FiniteModel.carrier.Atom)) automorphism

/-- Each one-face diamond route is exactly its local J1 raw defect. -/
theorem finiteDoubleDiamondPastingRawDefect_eq_rawTwoCellDefect
    (reselection : EdgeReselection finiteDoubleDiamondData.lift)
    (cell : DoubleDiamondTwoCell FiniteModel.carrier.Atom) :
    pastingRawDefect finiteDoubleDiamondData reselection
        (doubleDiamondPasting FiniteModel.carrier.Atom cell) =
      rawTwoCellDefect finiteDoubleDiamondData reselection cell := by
  cases cell <;>
    simp [pastingRawDefect, authoredPastingComparator,
      canonicalPastingComparator, pastingComparator, doubleDiamondPasting,
      doubleDiamondStep, doubleDiamondFace, orientedFaceComparator,
      authoredComparatorFamily, canonicalComparatorFamily,
      finiteDoubleDiamondData, rawTwoCellDefect,
      finiteDoubleDiamond_whisker_nil]

/-- The independent diamond raw formula equals the unified closed-pasting value. -/
theorem finiteDoubleDiamondSpecializedRawObstruction_eq_closedPastingRawObstruction
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    finiteDoubleDiamondSpecializedRawObstruction reselection =
      closedPastingRawObstruction finiteDoubleDiamondData reselection
        DoubleDiamondThreeCell.comparison := by
  unfold finiteDoubleDiamondSpecializedRawObstruction
  unfold closedPastingRawObstruction
  change
    ((show PackageFiberAut finiteWitnessTargetPackage from
        rawTwoCellDefect finiteDoubleDiamondData reselection .second)⁻¹ *
      (show PackageFiberAut finiteWitnessTargetPackage from
        rawTwoCellDefect finiteDoubleDiamondData reselection .first)) =
      (pastingRawDefect finiteDoubleDiamondData reselection
          (doubleDiamondPasting FiniteModel.carrier.Atom .second))⁻¹ *
        pastingRawDefect finiteDoubleDiamondData reselection
          (doubleDiamondPasting FiniteModel.carrier.Atom .first)
  rw [finiteDoubleDiamondPastingRawDefect_eq_rawTwoCellDefect,
    finiteDoubleDiamondPastingRawDefect_eq_rawTwoCellDefect]

/-- The new independent formula also recovers the Cycle-4 finite raw name. -/
theorem finiteDoubleDiamondSpecializedRawObstruction_eq_finiteRawObstruction
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    finiteDoubleDiamondSpecializedRawObstruction reselection =
      finiteDoubleDiamondRawObstruction reselection := by
  simpa [finiteDoubleDiamondRawObstruction] using
    finiteDoubleDiamondSpecializedRawObstruction_eq_closedPastingRawObstruction
      reselection

/-- The specialized and unified diamond conjugacy classes coincide. -/
theorem finiteDoubleDiamondSpecializedObstructionClass_eq_closedPastingObstructionClass
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    finiteDoubleDiamondSpecializedObstructionClass reselection =
      closedPastingObstructionClass finiteDoubleDiamondData reselection
        DoubleDiamondThreeCell.comparison := by
  unfold finiteDoubleDiamondSpecializedObstructionClass
  unfold closedPastingObstructionClass
  rw [finiteDoubleDiamondSpecializedRawObstruction_eq_closedPastingRawObstruction]

/-- The new independent class also recovers the Cycle-4 finite class name. -/
theorem finiteDoubleDiamondSpecializedObstructionClass_eq_finiteObstructionClass
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    finiteDoubleDiamondSpecializedObstructionClass reselection =
      finiteDoubleDiamondObstructionClass reselection := by
  simpa [finiteDoubleDiamondObstructionClass] using
    finiteDoubleDiamondSpecializedObstructionClass_eq_closedPastingObstructionClass
      reselection

/-- Specialized diamond nonvanishing is exactly unified closed-pasting nonvanishing. -/
theorem finiteDoubleDiamondSpecializedNonvanishing_iff_closedPastingNonvanishing :
    FiniteDoubleDiamondSpecializedNonvanishing ↔
      ClosedPastingObstructionNonvanishing finiteDoubleDiamondData
        DoubleDiamondThreeCell.comparison := by
  constructor
  · intro specialized reselection classIdentity
    exact specialized reselection
      ((finiteDoubleDiamondSpecializedObstructionClass_eq_closedPastingObstructionClass
        reselection).trans classIdentity)
  · intro unified reselection classIdentity
    exact unified reselection
      ((finiteDoubleDiamondSpecializedObstructionClass_eq_closedPastingObstructionClass
        reselection).symm.trans classIdentity)

/-- The concrete diamond satisfies its independent specialized nonvanishing predicate. -/
theorem finiteDoubleDiamondSpecialized_nonvanishing :
    FiniteDoubleDiamondSpecializedNonvanishing := by
  intro reselection
  rw [finiteDoubleDiamondSpecializedObstructionClass_eq_closedPastingObstructionClass]
  simpa [finiteDoubleDiamondObstructionClass] using
    finiteDoubleDiamond_class_nonvanishing reselection

/-- The concrete diamond therefore satisfies the unified nonvanishing predicate. -/
theorem finiteDoubleDiamondClosedPasting_nonvanishing :
    ClosedPastingObstructionNonvanishing finiteDoubleDiamondData
      DoubleDiamondThreeCell.comparison :=
  finiteDoubleDiamondSpecializedNonvanishing_iff_closedPastingNonvanishing.mp
    finiteDoubleDiamondSpecialized_nonvanishing

/-- The J4 diamond class recovers the J2 orbit-nonvanishing conclusion. -/
theorem finiteDoubleDiamondClosedPasting_not_obstructionVanishes :
    ¬ TransportObstructionVanishes finiteDoubleDiamondData :=
  closedPastingObstructionNonvanishing_not_obstructionVanishes
    finiteDoubleDiamondData DoubleDiamondThreeCell.comparison
      finiteDoubleDiamondClosedPasting_nonvanishing

/-! ## Specialized three-reading formula and agreement -/

/--
The specialized indirect route first composes authored and local canonical
comparators in temporal order, then takes their quotient.
-/
noncomputable def finiteTransportTriangleSpecializedIndirectRawDefect
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    PackageFiberAut finiteWitnessTargetPackage :=
  (finiteWitnessSwap12 * finiteWitnessSwap01) *
    ((show PackageFiberAut finiteWitnessTargetPackage from
        canonicalTwoCellComparator finiteTransportTriangleData reselection
          TransportTriangleTwoCell.c12) *
      (show PackageFiberAut finiteWitnessTargetPackage from
        canonicalTwoCellComparator finiteTransportTriangleData reselection
          TransportTriangleTwoCell.c01))⁻¹

/-- Specialized direct-route quotient for the `c02` translation. -/
noncomputable def finiteTransportTriangleSpecializedDirectRawDefect
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    PackageFiberAut finiteWitnessTargetPackage :=
  (finiteWitnessSwap01 * finiteWitnessSwap12) *
    (show PackageFiberAut finiteWitnessTargetPackage from
      canonicalTwoCellComparator finiteTransportTriangleData reselection
        TransportTriangleTwoCell.c02)⁻¹

/--
The specialized triangle obstruction compares the direct and indirect route
quotients.  No generic pasting object occurs in this definition.
-/
noncomputable def finiteTransportTriangleSpecializedRawObstruction
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    PackageFiberAut finiteWitnessTargetPackage :=
  (finiteTransportTriangleSpecializedDirectRawDefect reselection)⁻¹ *
    finiteTransportTriangleSpecializedIndirectRawDefect reselection

/-- Conjugacy class extracted from the specialized triangle formula. -/
noncomputable def finiteTransportTriangleSpecializedObstructionClass
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    ConjClasses (PackageFiberAut finiteWitnessTargetPackage) :=
  ConjClasses.mk (finiteTransportTriangleSpecializedRawObstruction reselection)

/-- All-coordinate nonvanishing stated solely with the specialized triangle formula. -/
def FiniteTransportTriangleSpecializedNonvanishing : Prop :=
  ∀ reselection : EdgeReselection finiteTransportTriangleData.lift,
    finiteTransportTriangleSpecializedObstructionClass reselection ≠
      ConjClasses.mk 1

/-- Empty target whiskering is literal on the concrete triangle. -/
private theorem finiteTransportTriangle_whisker_nil
    (reselection : EdgeReselection finiteTransportTriangleData.lift)
    (automorphism : PackageFiberAut finiteWitnessTargetPackage) :
    whiskerFiberAut finiteTransportTriangleData.lift reselection
        (i := (SingleDiskVertex.target :
          SingleDiskVertex FiniteModel.carrier.Atom))
        (j := (SingleDiskVertex.target :
          SingleDiskVertex FiniteModel.carrier.Atom)) automorphism
        (.nil (SingleDiskVertex.target :
          SingleDiskVertex FiniteModel.carrier.Atom)) =
      automorphism := by
  change whiskerFiberAut finiteTransportTriangleLiftData reselection
      (i := (SingleDiskVertex.target :
        SingleDiskVertex FiniteModel.carrier.Atom))
      (j := (SingleDiskVertex.target :
        SingleDiskVertex FiniteModel.carrier.Atom)) automorphism
        (.nil (SingleDiskVertex.target :
          SingleDiskVertex FiniteModel.carrier.Atom)) = automorphism
  exact whiskerFiberAut_nil finiteTransportTriangleLiftData reselection
    (vertex := (SingleDiskVertex.target :
      SingleDiskVertex FiniteModel.carrier.Atom)) automorphism

/-- The unified indirect route has the independently written specialized formula. -/
theorem finiteTransportTriangleSpecializedIndirectRawDefect_eq_pastingRawDefect
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleSpecializedIndirectRawDefect reselection =
      pastingRawDefect finiteTransportTriangleData reselection
        (transportTriangleIndirectPasting FiniteModel.carrier.Atom) := by
  unfold finiteTransportTriangleSpecializedIndirectRawDefect
  unfold pastingRawDefect
  have authored :
      authoredPastingComparator finiteTransportTriangleData reselection
          (transportTriangleIndirectPasting FiniteModel.carrier.Atom) =
        finiteWitnessSwap12 * finiteWitnessSwap01 := by
    simpa [transportTrianglePresentation] using
      finiteTransportTriangle_indirectAuthoredPasting reselection
  rw [authored]
  congr 1
  simp [canonicalPastingComparator, pastingComparator,
    transportTriangleIndirectPasting, transportTriangleStep,
    transportTriangleFace, orientedFaceComparator,
    canonicalComparatorFamily]
  rw [finiteTransportTriangle_whisker_nil,
    finiteTransportTriangle_whisker_nil]

/-- The unified direct route has the independently written specialized formula. -/
theorem finiteTransportTriangleSpecializedDirectRawDefect_eq_pastingRawDefect
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleSpecializedDirectRawDefect reselection =
      pastingRawDefect finiteTransportTriangleData reselection
        (transportTriangleDirectPasting FiniteModel.carrier.Atom) := by
  unfold finiteTransportTriangleSpecializedDirectRawDefect
  unfold pastingRawDefect
  have authored :
      authoredPastingComparator finiteTransportTriangleData reselection
          (transportTriangleDirectPasting FiniteModel.carrier.Atom) =
        finiteWitnessSwap01 * finiteWitnessSwap12 := by
    simpa [transportTrianglePresentation] using
      finiteTransportTriangle_directAuthoredPasting reselection
  rw [authored]
  congr 1
  simp [canonicalPastingComparator, pastingComparator,
    transportTriangleDirectPasting, transportTriangleStep,
    transportTriangleFace, orientedFaceComparator,
    canonicalComparatorFamily]
  exact (finiteTransportTriangle_whisker_nil reselection
    (show PackageFiberAut finiteWitnessTargetPackage from
      canonicalTwoCellComparator finiteTransportTriangleData reselection
        TransportTriangleTwoCell.c02)).symm

/-- The independent triangle raw formula equals the unified closed-pasting value. -/
theorem finiteTransportTriangleSpecializedRawObstruction_eq_closedPastingRawObstruction
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleSpecializedRawObstruction reselection =
      closedPastingRawObstruction finiteTransportTriangleData reselection
        TransportTriangleThreeCell.triangle := by
  unfold finiteTransportTriangleSpecializedRawObstruction
  unfold closedPastingRawObstruction
  change
    (finiteTransportTriangleSpecializedDirectRawDefect reselection)⁻¹ *
        finiteTransportTriangleSpecializedIndirectRawDefect reselection =
      (pastingRawDefect finiteTransportTriangleData reselection
          (transportTriangleDirectPasting FiniteModel.carrier.Atom))⁻¹ *
        pastingRawDefect finiteTransportTriangleData reselection
          (transportTriangleIndirectPasting FiniteModel.carrier.Atom)
  rw [finiteTransportTriangleSpecializedDirectRawDefect_eq_pastingRawDefect,
    finiteTransportTriangleSpecializedIndirectRawDefect_eq_pastingRawDefect]

/-- The new independent formula also recovers the Cycle-4 finite triangle raw name. -/
theorem finiteTransportTriangleSpecializedRawObstruction_eq_finiteRawObstruction
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleSpecializedRawObstruction reselection =
      finiteTransportTriangleRawObstruction reselection := by
  simpa [finiteTransportTriangleRawObstruction] using
    finiteTransportTriangleSpecializedRawObstruction_eq_closedPastingRawObstruction
      reselection

/-- The specialized and unified triangle conjugacy classes coincide. -/
theorem finiteTransportTriangleSpecializedObstructionClass_eq_closedPastingObstructionClass
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleSpecializedObstructionClass reselection =
      closedPastingObstructionClass finiteTransportTriangleData reselection
        TransportTriangleThreeCell.triangle := by
  unfold finiteTransportTriangleSpecializedObstructionClass
  unfold closedPastingObstructionClass
  rw [finiteTransportTriangleSpecializedRawObstruction_eq_closedPastingRawObstruction]

/-- The new independent class also recovers the Cycle-4 finite triangle class name. -/
theorem finiteTransportTriangleSpecializedObstructionClass_eq_finiteObstructionClass
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleSpecializedObstructionClass reselection =
      finiteTransportTriangleObstructionClass reselection := by
  simpa [finiteTransportTriangleObstructionClass] using
    finiteTransportTriangleSpecializedObstructionClass_eq_closedPastingObstructionClass
      reselection

/-- Specialized triangle nonvanishing is exactly unified closed-pasting nonvanishing. -/
theorem finiteTransportTriangleSpecializedNonvanishing_iff_closedPastingNonvanishing :
    FiniteTransportTriangleSpecializedNonvanishing ↔
      ClosedPastingObstructionNonvanishing finiteTransportTriangleData
        TransportTriangleThreeCell.triangle := by
  constructor
  · intro specialized reselection classIdentity
    exact specialized reselection
      ((finiteTransportTriangleSpecializedObstructionClass_eq_closedPastingObstructionClass
        reselection).trans classIdentity)
  · intro unified reselection classIdentity
    exact unified reselection
      ((finiteTransportTriangleSpecializedObstructionClass_eq_closedPastingObstructionClass
        reselection).symm.trans classIdentity)

/-- The concrete triangle satisfies its independent specialized nonvanishing predicate. -/
theorem finiteTransportTriangleSpecialized_nonvanishing :
    FiniteTransportTriangleSpecializedNonvanishing := by
  intro reselection
  rw [finiteTransportTriangleSpecializedObstructionClass_eq_closedPastingObstructionClass]
  simpa [finiteTransportTriangleObstructionClass] using
    finiteTransportTriangle_class_nonvanishing reselection

/-- The concrete triangle therefore satisfies the unified nonvanishing predicate. -/
theorem finiteTransportTriangleClosedPasting_nonvanishing :
    ClosedPastingObstructionNonvanishing finiteTransportTriangleData
      TransportTriangleThreeCell.triangle :=
  finiteTransportTriangleSpecializedNonvanishing_iff_closedPastingNonvanishing.mp
    finiteTransportTriangleSpecialized_nonvanishing

/-- The J4 triangle class recovers the J2 orbit-nonvanishing conclusion. -/
theorem finiteTransportTriangleClosedPasting_not_obstructionVanishes :
    ¬ TransportObstructionVanishes finiteTransportTriangleData :=
  closedPastingObstructionNonvanishing_not_obstructionVanishes
    finiteTransportTriangleData TransportTriangleThreeCell.triangle
      finiteTransportTriangleClosedPasting_nonvanishing

end AAT.AG.TransportCoherence

#assert_standard_axioms_only AAT.AG.TransportCoherence
