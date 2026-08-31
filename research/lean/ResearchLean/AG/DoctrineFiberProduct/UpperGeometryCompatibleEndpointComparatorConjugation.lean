import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointNaturality
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleGlobalMate

/-!
# Endpoint comparator conjugation

The canonical-authored route comparators are constructed directly by
Cartesian pullback of the literal comparator stored in the source transport.
They are not defined by conjugating the generated comparators with the
endpoint isomorphisms.  Cartesian uniqueness and the endpoint factor
triangles then prove the two required conjugation equations.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- Core projection of the canonical-authored base comparator. -/
noncomputable def canonicalAuthoredBaseRouteComparatorCore
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    PackageTotalHom
      (input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell)).core
      (input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell)).core := by
  simpa only [input.canonicalAuthoredBaseRouteGeometryAt_core] using
    (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell)).base

/-- Direct Cartesian pullback of the literal source comparator through the
canonical-authored base route leg. -/
noncomputable def canonicalAuthoredBaseRouteComparatorRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    RefinementGeometryHom
      (input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell))
      (input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell)) := by
  let target := P.twoTarget cell
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredBaseRouteGeometryHomAt target).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt target) :=
    input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian target
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredBaseRouteGeometryHomAt target)
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.sourceTransport.comparator cell)))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (input.canonicalAuthoredBaseRouteGeometryHomAt target).base
    (input.canonicalAuthoredBaseRouteGeometryHomAt target)
    (g := (exactPackageToRefinement U).map
      (input.canonicalAuthoredBaseRouteComparatorCore cell))
    (f' := candidate.base)
    (by
      simpa [canonicalAuthoredBaseRouteComparatorCore] using
        congrArg RefinementGeometryHom.base
          (input.generatedBaseRouteComparator_fac cell).symm)
    candidate

theorem canonicalAuthoredBaseRouteComparatorRefinement_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredBaseRouteComparatorRefinement cell).base =
      (exactPackageToRefinement U).map
        (input.canonicalAuthoredBaseRouteComparatorCore cell) := by
  let target := P.twoTarget cell
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredBaseRouteGeometryHomAt target).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt target) :=
    input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian target
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredBaseRouteGeometryHomAt target)
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.sourceTransport.comparator cell)))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  unfold canonicalAuthoredBaseRouteComparatorRefinement
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (input.canonicalAuthoredBaseRouteComparatorCore cell))
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (input.canonicalAuthoredBaseRouteGeometryHomAt target).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt target)
      (by
        simpa [canonicalAuthoredBaseRouteComparatorCore] using
          congrArg RefinementGeometryHom.base
            (input.generatedBaseRouteComparator_fac cell).symm)
      candidate)).symm

/-- Exact canonical-authored base comparator, independently generated from
the literal source comparator. -/
noncomputable def canonicalAuthoredBaseRouteComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    GeometryTotalHom
      (input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell))
      (input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell)) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredBaseRouteComparatorCore cell)
    (input.canonicalAuthoredBaseRouteComparatorRefinement cell)
    (input.canonicalAuthoredBaseRouteComparatorRefinement_base cell)

theorem canonicalAuthoredBaseRouteComparator_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseRouteComparator cell) =
      input.canonicalAuthoredBaseRouteComparatorRefinement cell :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The direct base comparator factors through the literal source-authored
comparator. -/
theorem canonicalAuthoredBaseRouteComparator_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteComparator cell)).comp
        (input.canonicalAuthoredBaseRouteGeometryHomAt (P.twoTarget cell)) =
      (input.canonicalAuthoredBaseRouteGeometryHomAt (P.twoTarget cell)).comp
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.sourceTransport.comparator cell))) := by
  rw [input.canonicalAuthoredBaseRouteComparator_toRefinement cell]
  unfold canonicalAuthoredBaseRouteComparatorRefinement
  let target := P.twoTarget cell
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredBaseRouteGeometryHomAt target).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt target) :=
    input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian target
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredBaseRouteGeometryHomAt target)
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.sourceTransport.comparator cell)))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (input.canonicalAuthoredBaseRouteGeometryHomAt target).base
    (input.canonicalAuthoredBaseRouteGeometryHomAt target)
    (by
      simpa [canonicalAuthoredBaseRouteComparatorCore] using
        congrArg RefinementGeometryHom.base
          (input.generatedBaseRouteComparator_fac cell).symm)
    candidate

/-- Endpoint comparison conjugates the independently generated base
canonical-authored comparator to the generated base comparator. -/
theorem canonicalAuthoredBaseRouteComparator_conjugation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteComparator cell)) ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
          (P.twoTarget cell)).hom =
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
        (P.twoTarget cell)).hom ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.generatedBaseRouteComparator cell))) := by
  let target := P.twoTarget cell
  let left := ((exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteComparator cell)) ≫
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom
  let right := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom ≫
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell)))
  have hbase : left.base = right.base := by
    dsimp [left, right]
    rw [input.canonicalAuthoredBaseRouteComparator_toRefinement cell]
    change (input.canonicalAuthoredBaseRouteComparatorRefinement cell).base ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom.base =
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom.base ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom
            (input.generatedBaseRouteComparator cell)).base
    rw [input.canonicalAuthoredBaseRouteComparatorRefinement_base cell,
      input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_base target]
    rw [Category.id_comp]
    change (exactPackageToRefinement U).map
        (CompositeFiberAut.hom
          (input.generatedBaseRouteComparator cell)).base ≫ 𝟙 _ =
      (exactPackageToRefinement U).map
        (CompositeFiberAut.hom
          (input.generatedBaseRouteComparator cell)).base
    exact Category.comp_id _
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift left
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      left.base right hbase.symm
  letI := input.generatedBaseRouteLegAt_isStronglyCartesian target
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedBaseRouteLegAt target).base
    (input.generatedBaseRouteLegAt target)
    left.base
  change RefinementGeometryHom.comp left
      (input.generatedBaseRouteLegAt target) =
    RefinementGeometryHom.comp right
      (input.generatedBaseRouteLegAt target)
  dsimp only [left, right]
  change RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteComparator cell))
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom)
      (input.generatedBaseRouteLegAt target) =
    RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))))
      (input.generatedBaseRouteLegAt target)
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
  calc
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteComparator cell))
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom
          (input.generatedBaseRouteLegAt target)) =
      RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteComparator cell))
        (input.canonicalAuthoredBaseRouteGeometryHomAt target) := by
      exact congrArg _
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac target)
    _ = RefinementGeometryHom.comp
        (input.canonicalAuthoredBaseRouteGeometryHomAt target)
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.sourceTransport.comparator cell))) :=
      input.canonicalAuthoredBaseRouteComparator_fac cell
    _ = RefinementGeometryHom.comp
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt target).hom
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (input.generatedBaseRouteComparator cell))))
        (input.generatedBaseRouteLegAt target) := by
      rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
        input.generatedBaseRouteComparator_fac cell,
        ← UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
      exact congrArg
        (fun hom => RefinementGeometryHom.comp hom
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (input.sourceTransport.comparator cell))))
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac target).symm

/-- Returning along the inverse endpoint comparison recovers the literal
canonical-authored base comparator equation. -/
theorem canonicalAuthoredBaseRouteComparator_conjugation_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedBaseRouteComparator cell))) ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
          (P.twoTarget cell)).inv =
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
        (P.twoTarget cell)).inv ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteComparator cell)) := by
  let comparison := input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)
  apply (cancel_epi comparison.hom).1
  calc
    comparison.hom ≫
        (((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.generatedBaseRouteComparator cell))) ≫ comparison.inv) =
      (comparison.hom ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.generatedBaseRouteComparator cell)))) ≫ comparison.inv :=
      (Category.assoc _ _ _).symm
    _ = (((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteComparator cell)) ≫
        comparison.hom) ≫ comparison.inv := by
      rw [input.canonicalAuthoredBaseRouteComparator_conjugation cell]
    _ = (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseRouteComparator cell) := by simp
    _ = comparison.hom ≫
        (comparison.inv ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.canonicalAuthoredBaseRouteComparator cell))) := by simp

/-- Core projection of the canonical-authored pulled comparator. -/
noncomputable def canonicalAuthoredPulledRouteComparatorCore
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    PackageTotalHom
      (input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell)).core
      (input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell)).core := by
  simpa only [input.canonicalAuthoredPulledRouteGeometryAt_core] using
    input.generatedPulledPackageComparatorAt (P.twoTarget cell)
      (input.sourceTransport.comparator cell)

/-- Direct Cartesian pullback of the literal source comparator through the
canonical-authored pulled route leg. -/
noncomputable def canonicalAuthoredPulledRouteComparatorRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    let G := input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell)
    RefinementGeometryHom G G := by
  let target := P.twoTarget cell
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredPulledRouteGeometryHomAt target).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt target) :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian target
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredPulledRouteGeometryHomAt target)
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.sourceTransport.comparator cell)))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (input.canonicalAuthoredPulledRouteGeometryHomAt target).base
    (input.canonicalAuthoredPulledRouteGeometryHomAt target)
    (g := (exactPackageToRefinement U).map
      (input.canonicalAuthoredPulledRouteComparatorCore cell))
    (f' := candidate.base)
    (by
      change (input.generatedPulledGeometryComparatorCandidateAt target
          (input.sourceTransport.comparator cell)).base =
        ((exactPackageToRefinement U).map
          (input.generatedPulledPackageComparatorAt target
            (input.sourceTransport.comparator cell))).comp
          (input.generatedPulledRouteLegAt target).base
      exact input.generatedPulledGeometryComparatorCandidateAt_base target
        (input.sourceTransport.comparator cell))
    candidate

theorem canonicalAuthoredPulledRouteComparatorRefinement_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredPulledRouteComparatorRefinement cell).base =
      (exactPackageToRefinement U).map
        (input.canonicalAuthoredPulledRouteComparatorCore cell) := by
  let target := P.twoTarget cell
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredPulledRouteGeometryHomAt target).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt target) :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian target
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredPulledRouteGeometryHomAt target)
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.sourceTransport.comparator cell)))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  unfold canonicalAuthoredPulledRouteComparatorRefinement
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (input.canonicalAuthoredPulledRouteComparatorCore cell))
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (input.canonicalAuthoredPulledRouteGeometryHomAt target).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt target)
      (by
        change (input.generatedPulledGeometryComparatorCandidateAt target
            (input.sourceTransport.comparator cell)).base =
          ((exactPackageToRefinement U).map
            (input.generatedPulledPackageComparatorAt target
              (input.sourceTransport.comparator cell))).comp
            (input.generatedPulledRouteLegAt target).base
        exact input.generatedPulledGeometryComparatorCandidateAt_base target
          (input.sourceTransport.comparator cell))
      candidate)).symm

/-- Exact canonical-authored pulled comparator, independently generated from
the literal source comparator. -/
noncomputable def canonicalAuthoredPulledRouteComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    let G := input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell)
    GeometryTotalHom G G :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredPulledRouteComparatorCore cell)
    (input.canonicalAuthoredPulledRouteComparatorRefinement cell)
    (input.canonicalAuthoredPulledRouteComparatorRefinement_base cell)

theorem canonicalAuthoredPulledRouteComparator_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledRouteComparator cell) =
      input.canonicalAuthoredPulledRouteComparatorRefinement cell :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The direct pulled comparator factors through the literal source-authored
comparator. -/
theorem canonicalAuthoredPulledRouteComparator_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledRouteComparator cell)).comp
        (input.canonicalAuthoredPulledRouteGeometryHomAt (P.twoTarget cell)) =
      (input.canonicalAuthoredPulledRouteGeometryHomAt (P.twoTarget cell)).comp
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.sourceTransport.comparator cell))) := by
  rw [input.canonicalAuthoredPulledRouteComparator_toRefinement cell]
  unfold canonicalAuthoredPulledRouteComparatorRefinement
  let target := P.twoTarget cell
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredPulledRouteGeometryHomAt target).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt target) :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian target
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredPulledRouteGeometryHomAt target)
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.sourceTransport.comparator cell)))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (input.canonicalAuthoredPulledRouteGeometryHomAt target).base
    (input.canonicalAuthoredPulledRouteGeometryHomAt target)
    (by
      change (input.generatedPulledGeometryComparatorCandidateAt target
          (input.sourceTransport.comparator cell)).base =
        ((exactPackageToRefinement U).map
          (input.generatedPulledPackageComparatorAt target
            (input.sourceTransport.comparator cell))).comp
          (input.generatedPulledRouteLegAt target).base
      exact input.generatedPulledGeometryComparatorCandidateAt_base target
        (input.sourceTransport.comparator cell))
    candidate

/-- Endpoint comparison conjugates the independently generated pulled
canonical-authored comparator to the generated pulled comparator. -/
theorem canonicalAuthoredPulledRouteComparator_conjugation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledRouteComparator cell)) ≫
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
          (P.twoTarget cell)).hom =
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
        (P.twoTarget cell)).hom ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell))) := by
  let target := P.twoTarget cell
  let left := ((exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteComparator cell)) ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom
  let right := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom ≫
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell)))
  have hbase : left.base = right.base := by
    dsimp [left, right]
    rw [input.canonicalAuthoredPulledRouteComparator_toRefinement cell]
    change (input.canonicalAuthoredPulledRouteComparatorRefinement cell).base ≫
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom.base =
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom.base ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell)).base
    rw [input.canonicalAuthoredPulledRouteComparatorRefinement_base cell,
      input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_base target,
      Category.id_comp]
    change (exactPackageToRefinement U).map
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)).base ≫ 𝟙 _ =
      (exactPackageToRefinement U).map
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)).base
    exact Category.comp_id _
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift left
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      left.base right hbase.symm
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian target
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt target).base
    (input.generatedPulledRouteLegAt target)
    left.base
  change RefinementGeometryHom.comp left
      (input.generatedPulledRouteLegAt target) =
    RefinementGeometryHom.comp right
      (input.generatedPulledRouteLegAt target)
  dsimp only [left, right]
  change RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteComparator cell))
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom)
      (input.generatedPulledRouteLegAt target) =
    RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))))
      (input.generatedPulledRouteLegAt target)
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
  calc
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteComparator cell))
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom
          (input.generatedPulledRouteLegAt target)) =
      RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteComparator cell))
        (input.canonicalAuthoredPulledRouteGeometryHomAt target) := by
      exact congrArg _
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac target)
    _ = RefinementGeometryHom.comp
        (input.canonicalAuthoredPulledRouteGeometryHomAt target)
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.sourceTransport.comparator cell))) :=
      input.canonicalAuthoredPulledRouteComparator_fac cell
    _ = RefinementGeometryHom.comp
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt target).hom
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (input.generatedPulledRouteComparator cell))))
        (input.generatedPulledRouteLegAt target) := by
      rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
        input.generatedPulledRouteComparator_fac cell,
        ← UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
      exact congrArg
        (fun hom => RefinementGeometryHom.comp hom
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (input.sourceTransport.comparator cell))))
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac target).symm

/-- Returning along the inverse endpoint comparison recovers the literal
canonical-authored pulled comparator equation. -/
theorem canonicalAuthoredPulledRouteComparator_conjugation_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedPulledRouteComparator cell))) ≫
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
          (P.twoTarget cell)).inv =
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
        (P.twoTarget cell)).inv ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteComparator cell)) := by
  let comparison := input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)
  apply (cancel_epi comparison.hom).1
  calc
    comparison.hom ≫
        (((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell))) ≫ comparison.inv) =
      (comparison.hom ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell)))) ≫ comparison.inv :=
      (Category.assoc _ _ _).symm
    _ = (((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteComparator cell)) ≫
        comparison.hom) ≫ comparison.inv := by
      rw [input.canonicalAuthoredPulledRouteComparator_conjugation cell]
    _ = (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledRouteComparator cell) := by simp
    _ = comparison.hom ≫
        (comparison.inv ≫
          ((exactGeometryToRefinementGeometry U).map
            (input.canonicalAuthoredPulledRouteComparator cell))) := by simp

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
