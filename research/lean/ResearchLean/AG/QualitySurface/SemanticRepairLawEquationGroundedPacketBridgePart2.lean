import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacket
import Formal.AG.SemanticRepair.LawEquationGeneratedPair

/-!
The first conclusion adapter for the grounded law-equation packet.

The body and Research cochain-realization records have the same mathematical
fields, but are distinct Lean structures.  This adapter copies all nine body
fields into the Research presentation over the canonical generated envelope.
-/

noncomputable section

universe v r

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCechGrounding

open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1

namespace SemanticRepairCoverRelativeCochainRealization
namespace CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
namespace GroundedPacketBridge

open CoverRelativeCechGeneratedSemanticCoefficient

variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {semanticSite : SemanticRepairSite.{r, v} U.Atom}
variable {S : AAT.AG.Site.AATSite A}
variable {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob}

/--
Convert body conjunct 6 to Research conjunct 6 by using every field of the
body cochain-realization witness.
-/
def toResearchCochainRealization
    (boundary :
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient semanticSite K)
    (canonical :
      CoverRelativeCechGeneratedCanonicalH1Envelope
        boundary.toGeneratedCoefficient)
    (body :
      AAT.AG.SemanticRepair.SemanticRepairCoverRelativeCochainRealization
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          K boundary.primitive)
        K) :
    SemanticRepairCoverRelativeCochainRealization
      canonical.toAdditiveCechH1Data K := by
  refine
    { c0Equiv := ?_
      c1Equiv := ?_
      c2Equiv := ?_
      c2Equiv_zero := ?_
      c2Equiv_symm_zero := ?_
      d0_to := ?_
      d0_from := ?_
      d1_to := ?_
      d1_from := ?_ }
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.c0Equiv
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.c1Equiv
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.c2Equiv
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.c2Equiv_zero
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.c2Equiv_symm_zero
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.d0_to
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.d0_from
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.d1_to
  · simpa [
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using body.d1_from

/--
Convert body conjunct 7 through an explicit equivalence between the Research
and body quotient presentations.  Every field of the body comparison package
is used in the corresponding Research field.
-/
def toResearchH1ComparisonPackage
    (boundary :
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient semanticSite K)
    (canonical :
      CoverRelativeCechGeneratedCanonicalH1Envelope
        boundary.toGeneratedCoefficient)
    (bodyRealization :
      AAT.AG.SemanticRepair.SemanticRepairCoverRelativeCochainRealization
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          K boundary.primitive)
        K)
    (bodyPackage :
      AAT.AG.SemanticRepair.SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          bodyRealization.toH1Comparison) :
    ResearchLean.AG.QualitySurface.SemanticRepairCechGrounding.SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (toResearchCochainRealization boundary canonical bodyRealization).toH1Comparison := by
  let bodyAdditive :=
    AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
      K boundary.primitive
  let researchAdditive := canonical.toAdditiveCechH1Data
  let researchToBody :
      SemanticRepairAdditiveH1Class researchAdditive -> bodyAdditive.H1 :=
    Quotient.map
      (fun cocycle =>
        (⟨cocycle.1, by
          simpa [bodyAdditive, researchAdditive,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
            CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
            CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
            CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
            AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
            using cocycle.2⟩ : bodyAdditive.Cocycle))
      (by
        intro left right hsame
        rcases hsame with ⟨primitive, hprimitive⟩
        exact ⟨primitive, by
          simpa [bodyAdditive, researchAdditive,
            SemanticRepairAdditiveH1SameClass,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
            CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
            CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
            CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
            AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
            using hprimitive.symm⟩)
  let bodyToResearch :
      bodyAdditive.H1 -> SemanticRepairAdditiveH1Class researchAdditive :=
    Quotient.map
      (fun cocycle =>
        (⟨cocycle.1, by
          simpa [bodyAdditive, researchAdditive,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
            CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
            CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
            CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
            AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
            using cocycle.2⟩ : SemanticRepairAdditiveH1Cocycle researchAdditive))
      (by
        intro left right hsame
        rcases hsame with ⟨primitive, hprimitive⟩
        exact ⟨primitive, by
          simpa [bodyAdditive, researchAdditive,
            SemanticRepairAdditiveH1SameClass,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
            CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
            CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
            CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
            CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
            CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
            AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
            using hprimitive.symm⟩)
  let h1Transport :
      SemanticRepairAdditiveH1Class researchAdditive ≃ bodyAdditive.H1 :=
    { toFun := researchToBody
      invFun := bodyToResearch
      left_inv := by
        intro h1
        refine Quotient.inductionOn h1 ?_
        intro cocycle
        rfl
      right_inv := by
        intro h1
        refine Quotient.inductionOn h1 ?_
        intro cocycle
        rfl }
  let researchComparison :=
    (toResearchCochainRealization boundary canonical bodyRealization).toH1Comparison
  refine
    { toCoverRelativeH1 := ?_
      fromCoverRelativeH1 := ?_
      h1Equiv := ?_
      sameClass_iff_coverRelative := ?_
      zero_iff_coverRelativeZero := ?_ }
  · simpa [researchComparison, toResearchCochainRealization,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
      using (bodyPackage.toCoverRelativeH1 ∘ h1Transport)
  · simpa [researchComparison, toResearchCochainRealization,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
      using (h1Transport.symm ∘ bodyPackage.fromCoverRelativeH1)
  · simpa [researchComparison, toResearchCochainRealization,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
      using h1Transport.trans bodyPackage.h1Equiv
  · intro left right hleft hright
    let bodyLeft :
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          K boundary.primitive).Cocycle :=
      ⟨left, by
        simpa [
          CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
          CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
          CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
          CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
          CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
          AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
          using hleft⟩
    let bodyRight :
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          K boundary.primitive).Cocycle :=
      ⟨right, by
        simpa [
          CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
          CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
          CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
          CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
          CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
          AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
          using hright⟩
    have hbody :=
      bodyPackage.sameClass_iff_coverRelative bodyLeft bodyRight
    constructor
    · rintro ⟨primitive, hprimitive⟩
      have hbodyClass :
          (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
            K boundary.primitive).Cohomologous bodyLeft bodyRight :=
        ⟨primitive, hprimitive.symm⟩
      have hcover := hbody.1 hbodyClass
      simpa [researchComparison, bodyLeft, bodyRight,
        toResearchCochainRealization] using hcover
    · intro hcover
      have hbodyCover :
          (K.CechCoboundarySetoidSucc 0).r
            (bodyRealization.toH1Comparison.toCoverRelativeCocycle bodyLeft)
            (bodyRealization.toH1Comparison.toCoverRelativeCocycle bodyRight) := by
        simpa [researchComparison, bodyLeft, bodyRight,
          toResearchCochainRealization] using hcover
      rcases hbody.2 hbodyCover with ⟨primitive, hprimitive⟩
      exact ⟨primitive, hprimitive.symm⟩
  · have hResidual :
        h1Transport (semanticRepairAdditiveResidualClass researchAdditive) =
          bodyAdditive.residualClass := by
      rfl
    have hZero :
        h1Transport (semanticRepairAdditiveZeroClass researchAdditive) =
          bodyAdditive.zeroClass := by
      rfl
    constructor
    · intro hresearchZero
      have hbodyZero : bodyAdditive.H1Zero := by
        change bodyAdditive.residualClass = bodyAdditive.zeroClass
        rw [← hResidual, ← hZero, hresearchZero]
      have hcover := bodyPackage.zero_iff_coverRelativeZero.1 hbodyZero
      simpa [researchComparison, toResearchCochainRealization,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
        CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
        CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using hcover
    · intro hcover
      have hbodyCover : bodyRealization.toH1Comparison.CoverRelativeResidualH1Zero := by
        simpa [researchComparison, toResearchCochainRealization,
          CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
          CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
          CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
          CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
          CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
          CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
          CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
          AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
          using hcover
      have hbodyZero := bodyPackage.zero_iff_coverRelativeZero.2 hbodyCover
      change semanticRepairAdditiveResidualClass researchAdditive =
        semanticRepairAdditiveZeroClass researchAdditive
      apply h1Transport.injective
      simpa [hResidual, hZero] using hbodyZero

/-- Convert body conjunct 8 by retaining its displayed boundary primitive. -/
def toResearchResidualBoundary
    (boundary :
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient semanticSite K)
    (canonical :
      CoverRelativeCechGeneratedCanonicalH1Envelope
        boundary.toGeneratedCoefficient)
    (body :
      AAT.AG.SemanticRepair.GeneratedResidualBoundarySurfaceBody
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          K boundary.primitive)) :
    canonical.residualBoundary := by
  rcases body with ⟨primitive, hprimitive⟩
  refine ⟨primitive, ?_⟩
  simpa [
    CoverRelativeCechGeneratedCanonicalH1Envelope.residualBoundary,
    CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
    AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using
      hprimitive

/-- Convert body conjunct 9 by retaining both its cocycle and same-class data. -/
def toResearchSemanticH1Zero
    (boundary :
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient semanticSite K)
    (canonical :
      CoverRelativeCechGeneratedCanonicalH1Envelope
        boundary.toGeneratedCoefficient)
    (body :
      AAT.AG.SemanticRepair.GeneratedSemanticH1ZeroBody
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          K boundary.primitive)) :
    SemanticRepairH1Zero canonical.toEnvelope := by
  refine ⟨?_, ?_⟩
  · simpa [
      SemanticRepairSheafH1.CechZ1,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.GeneratedSemanticH1ZeroBody,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using
        body.1
  · rcases body.2 with ⟨primitive, hprimitive⟩
    refine ⟨primitive, ?_⟩
    simpa [
      SemanticRepairSheafH1.H1SameClass,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      coverRelativeCechGeneratedCanonicalCohomologous,
      AAT.AG.SemanticRepair.SemanticRepairAdditiveH1Surface.Cohomologous,
      AAT.AG.SemanticRepair.GeneratedSemanticH1ZeroBody,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using
        hprimitive

/-- Convert body conjunct 10 through the represented quotient relation. -/
def toResearchAdditiveH1Zero
    (boundary :
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient semanticSite K)
    (canonical :
      CoverRelativeCechGeneratedCanonicalH1Envelope
        boundary.toGeneratedCoefficient)
    (body :
      (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
        K boundary.primitive).H1Zero) :
    SemanticRepairAdditiveH1Zero canonical.toAdditiveCechH1Data := by
  have bodySameClass := Quotient.exact body
  rcases bodySameClass with ⟨primitive, hprimitive⟩
  apply Quotient.sound
  refine ⟨primitive, ?_⟩
  simpa [
    CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
    CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
    CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
    CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
    CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
    CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
    CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
    coverRelativeCechGeneratedCanonicalCohomologous,
    SemanticRepairAdditiveH1SameClass,
    AAT.AG.SemanticRepair.SemanticRepairAdditiveH1Surface.H1Zero,
    AAT.AG.SemanticRepair.SemanticRepairAdditiveH1Surface.Cohomologous,
    AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using
      hprimitive.symm

end GroundedPacketBridge
end CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
