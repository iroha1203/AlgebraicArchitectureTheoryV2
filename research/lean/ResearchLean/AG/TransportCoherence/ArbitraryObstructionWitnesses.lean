import ResearchLean.AG.TransportCoherence.ArbitraryObstruction
import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Nonvacuity witnesses for arbitrary-functor transport obstruction

This module supplies positive and negative instances for the predicates added
in `ArbitraryObstruction`.  The positive disk has an explicit absorbing edge
choice.  The negative double diamond has two incompatible authored comparisons.
Both are transported through the proved package-fiber equivalence, so they are
actual instances of the arbitrary-functor definitions rather than restatements
of the package-specific conclusions.

A second double diamond with two identity authored comparisons supplies a
nonempty positive 3-cell syzygy.  Thus positive syzygy compatibility is not
obtained from an empty family of 3-cells.
-/

namespace AAT.AG.TransportCoherence.Arbitrary.Witnesses

universe u

open CategoryTheory
open AtomFoundation
open AAT.AG.TransportCoherence

/-- The package single disk gives a concrete coherent arbitrary-functor coordinate. -/
theorem packageSingleDisk_coherentAt
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    Arbitrary.CoherentAt (Arbitrary.packageTransportData data)
      (Arbitrary.packageEdgeReselection data.lift
        (singleDiskAbsorbingReselection data)) :=
  (Arbitrary.package_coherentAt_iff data
    (singleDiskAbsorbingReselection data)).mpr
      (singleDisk_coherentAt_absorbingReselection data)

/-- The package single disk is a positive coherentizability instance. -/
theorem packageSingleDisk_coherentizable
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    Arbitrary.Coherentizable (Arbitrary.packageTransportData data) :=
  (Arbitrary.package_coherentizable_iff data).mpr
    (singleDisk_coherentizable data)

/-- The package single disk is a positive obstruction-vanishing instance. -/
theorem packageSingleDisk_obstruction_vanishes
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    Arbitrary.TransportObstructionVanishes
      (Arbitrary.packageTransportData data) :=
  (Arbitrary.package_transportObstructionVanishes_iff data).mpr
    (singleDisk_obstruction_vanishes data)

/-- The concrete double diamond is not coherent at the mapped identity coordinate. -/
theorem packageFiniteDoubleDiamond_not_coherentAt_identity :
    ¬ Arbitrary.CoherentAt
      (Arbitrary.packageTransportData finiteDoubleDiamondData)
      (Arbitrary.packageEdgeReselection finiteDoubleDiamondData.lift 1) := by
  intro coherent
  exact finiteDoubleDiamond_not_coherentizable
    ⟨1, (Arbitrary.package_coherentAt_iff
      finiteDoubleDiamondData 1).mp coherent⟩

/-- The concrete double diamond is a negative coherentizability instance. -/
theorem packageFiniteDoubleDiamond_not_coherentizable :
    ¬ Arbitrary.Coherentizable
      (Arbitrary.packageTransportData finiteDoubleDiamondData) := by
  intro coherentizable
  exact finiteDoubleDiamond_not_coherentizable
    ((Arbitrary.package_coherentizable_iff
      finiteDoubleDiamondData).mp coherentizable)

/-- The concrete double diamond is a negative obstruction-vanishing instance. -/
theorem packageFiniteDoubleDiamond_obstruction_does_not_vanish :
    ¬ Arbitrary.TransportObstructionVanishes
      (Arbitrary.packageTransportData finiteDoubleDiamondData) := by
  intro vanishes
  exact finiteDoubleDiamond_obstruction_does_not_vanish
    ((Arbitrary.package_transportObstructionVanishes_iff
      finiteDoubleDiamondData).mp vanishes)

/--
The double-diamond geometry with both authored face comparisons set to the
identity.

Implementation notes: this deliberately reuses the existing nonidentity edge
lifts and base equalities.  Only the authored comparison input is changed, so
the witness tests the comparison equations rather than replacing the geometry
by a terminal or singleton presentation.  The alternative empty-3-cell disk is
not used because it would make syzygy compatibility vacuous.
-/
noncomputable def coherentDoubleDiamondData :
    AdmissibleTransportData
      (doubleDiamondPresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  lift := finiteDoubleDiamondLiftData
  twoCellBase := finiteDoubleDiamondData.twoCellBase
  comparator := fun _ => 1

/-- Both identity-authored diamond faces are coherent at one explicit edge choice. -/
theorem coherentDoubleDiamond_coherentAt :
    AAT.AG.TransportCoherence.CoherentAt coherentDoubleDiamondData
      (finiteDoubleDiamondFaceReselection .first) := by
  intro cell
  have firstCoherent := finiteDoubleDiamond_face_coherent
    DoubleDiamondTwoCell.first
  cases cell <;>
    simpa only [coherentDoubleDiamondData] using firstCoherent

/-- The coherent double diamond supplies a positive, nonempty 3-cell syzygy. -/
theorem coherentDoubleDiamond_syzygyCompatible :
    AAT.AG.TransportCoherence.SyzygyCompatible coherentDoubleDiamondData
      (finiteDoubleDiamondFaceReselection .first) :=
  AAT.AG.TransportCoherence.syzygyCompatible_of_coherentAt
    coherentDoubleDiamondData
    (finiteDoubleDiamondFaceReselection .first)
    coherentDoubleDiamond_coherentAt

/-- The positive double-diamond syzygy remains positive for the arbitrary functor. -/
theorem packageCoherentDoubleDiamond_syzygyCompatible :
    Arbitrary.SyzygyCompatible
      (Arbitrary.packageTransportData coherentDoubleDiamondData)
      (Arbitrary.packageEdgeReselection coherentDoubleDiamondData.lift
        (finiteDoubleDiamondFaceReselection .first)) :=
  (Arbitrary.package_syzygyCompatible_iff coherentDoubleDiamondData
    (finiteDoubleDiamondFaceReselection .first)).mpr
      coherentDoubleDiamond_syzygyCompatible

/-- The incompatible double diamond is a negative arbitrary-functor syzygy instance. -/
theorem packageFiniteDoubleDiamond_not_syzygyCompatible :
    ¬ Arbitrary.SyzygyCompatible
      (Arbitrary.packageTransportData finiteDoubleDiamondData)
      (Arbitrary.packageEdgeReselection finiteDoubleDiamondData.lift 1) := by
  intro compatible
  exact finiteDoubleDiamond_not_syzygyCompatible 1
    ((Arbitrary.package_syzygyCompatible_iff
      finiteDoubleDiamondData 1).mp compatible)

end AAT.AG.TransportCoherence.Arbitrary.Witnesses

#assert_standard_axioms_only AAT.AG.TransportCoherence.Arbitrary.Witnesses
