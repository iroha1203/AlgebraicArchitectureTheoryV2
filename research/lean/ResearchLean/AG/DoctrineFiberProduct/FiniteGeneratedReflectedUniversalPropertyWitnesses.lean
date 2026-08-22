import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedUniversalProperty
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedPackageTotalHomTriangleWitnesses

/-!
# Concrete reflected universal-property witness

This module fires the exact Cycle 16 reflection surface on the selective-two
fixture.  The universal-property problem uses the noninvertible prefix and the
generated outer competitor from Cycle 25.  Its factor is definitionally the
actual-high-derived ambient factor, and uniqueness remains quantified over an
arbitrary candidate for that concrete noninvertible problem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Reflected hom and component packet -/

/-- The reflected normalized hom on the selective-two supplied high lift. -/
noncomputable def finiteSelectiveTwoReflectNormalizedHighHom :
    finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain ⟶
      FiniteModel.corePackage :=
  reflectNormalizedHighHom.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}

/-- The concrete reflected hom lies over the selective-two tail arrow. -/
@[simp]
theorem finiteSelectiveTwoReflectNormalizedHighHom_base :
    finiteSelectiveTwoReflectNormalizedHighHom.{u}.base =
      finiteSelectiveTwoObjectContextWitnessInput.hom := by
  exact reflectNormalizedHighHom_base.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}

/-- The concrete reflected hom carries the complete generated component graph. -/
theorem finiteSelectiveTwoReflectNormalizedHighHom_components :
    ReflectedGeneratedComponentGraph.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoReflectNormalizedHighHom.{u} := by
  exact reflectNormalizedHighHom_components.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}

/-- The concrete reflection retracts to the named generated low hom. -/
@[simp]
theorem finiteSelectiveTwoReflectNormalizedHighHom_retraction :
    finiteSelectiveTwoReflectNormalizedHighHom.{u} =
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.hom :=
  rfl

/-! ## Universal property on the noninvertible ambient problem -/

/-- The complete reflected universal-property packet on the selective-two input. -/
noncomputable def finiteSelectiveTwoReflectNormalizedUniversalProperty :=
  reflectNormalizedUniversalProperty.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}

/--
The packet chooses exactly the Cycle 25 actual-high-derived factor for the
concrete generated outer competitor.
-/
theorem finiteSelectiveTwoReflectNormalizedUniversalProperty_factor :
    letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
    (finiteSelectiveTwoReflectNormalizedUniversalProperty.{u}).factor
        finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
        finiteSelectiveTwoGeneratedAmbientCompetitor =
      finiteSelectiveTwoReflectedAmbientFactor.{u} := by
  letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
  rfl

/-- The concrete packet's factor lies over the noninvertible prefix. -/
theorem finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_isHomLift :
    letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
    (packageProjection FiniteModel.carrier).IsHomLift
      finiteSelectiveTwoObjectContextWitnessBase
      ((finiteSelectiveTwoReflectNormalizedUniversalProperty.{u}).factor
        finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
        finiteSelectiveTwoGeneratedAmbientCompetitor) := by
  letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_base_eq] using
    (finiteSelectiveTwoReflectNormalizedUniversalProperty.{u}).factor_isHomLift
      finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
      finiteSelectiveTwoGeneratedAmbientCompetitor

/-- The concrete packet's generated factor reaches the concrete competitor. -/
theorem finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_fac :
    letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
    (finiteSelectiveTwoReflectNormalizedUniversalProperty.{u}).factor
          finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
          finiteSelectiveTwoGeneratedAmbientCompetitor ≫
        finiteSelectiveTwoReflectNormalizedHighHom.{u} =
      finiteSelectiveTwoGeneratedAmbientCompetitor := by
  letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
  exact (finiteSelectiveTwoReflectNormalizedUniversalProperty.{u}).factor_fac
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
    finiteSelectiveTwoGeneratedAmbientCompetitor

/--
Every candidate for the concrete noninvertible ambient problem equals the
actual-high-derived generated factor.
-/
theorem finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_unique
    (candidate :
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain ⟶
        finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain)
    [(packageProjection FiniteModel.carrier).IsHomLift
      finiteSelectiveTwoReflectedPackageTotalHom.{u}.base candidate]
    (hfac : candidate ≫ finiteSelectiveTwoReflectNormalizedHighHom.{u} =
      finiteSelectiveTwoGeneratedAmbientCompetitor) :
    candidate =
      (letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
       (finiteSelectiveTwoReflectNormalizedUniversalProperty.{u}).factor
        finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
        finiteSelectiveTwoGeneratedAmbientCompetitor) := by
  letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
  exact (finiteSelectiveTwoReflectNormalizedUniversalProperty.{u}).factor_unique
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
    finiteSelectiveTwoGeneratedAmbientCompetitor candidate hfac

/-- The prefix used by the concrete universal-property problem is noninvertible. -/
theorem finiteSelectiveTwoReflectNormalizedUniversalProperty_base_not_isIso :
    ¬ IsIso finiteSelectiveTwoObjectContextWitnessBase :=
  finiteSelectiveTwoObjectContextWitnessBase_not_isIso

/-- The concrete ambient competitor also lies over a noninvertible composite. -/
theorem finiteSelectiveTwoReflectNormalizedUniversalProperty_competitor_base_not_isIso :
    ¬ IsIso
      (finiteSelectiveTwoGeneratedChain.first ≫
        finiteSelectiveTwoGeneratedChain.second) :=
  finiteSelectiveTwoGeneratedAmbientCompetitor_base_not_isIso

/-! ## Strong cartesianness and the reflected strong lift -/

/-- The concrete reflected hom has the newly generated strong-cartesian proof. -/
theorem finiteSelectiveTwoReflectNormalizedHighHom_isStronglyCartesian :
    (packageProjection FiniteModel.carrier).IsStronglyCartesian
      finiteSelectiveTwoObjectContextWitnessInput.lowInput.hom
      finiteSelectiveTwoReflectNormalizedHighHom.{u} :=
  reflectNormalizedHighHom_isStronglyCartesian.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}

/-- The complete reflected strong lift on the selective-two supplied high lift. -/
noncomputable def finiteSelectiveTwoReflectNormalizedStrongCartesianLift :
    StrongCartesianLift
      finiteSelectiveTwoObjectContextWitnessInput.lowInput
      finiteSelectiveTwoObjectContextWitnessInput.lowTarget :=
  reflectNormalizedStrongCartesianLift.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}

/-- The concrete reflected strong lift has the generated low domain. -/
@[simp]
theorem finiteSelectiveTwoReflectNormalizedStrongCartesianLift_domain :
    finiteSelectiveTwoReflectNormalizedStrongCartesianLift.{u}.domain =
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain :=
  rfl

/-- The concrete reflected strong lift has the reflected normalized hom. -/
@[simp]
theorem finiteSelectiveTwoReflectNormalizedStrongCartesianLift_hom :
    finiteSelectiveTwoReflectNormalizedStrongCartesianLift.{u}.hom =
      finiteSelectiveTwoReflectNormalizedHighHom.{u} :=
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
