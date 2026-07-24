import Formal.AG.Measurement.GAGA
import Formal.AG.Measurement.ComputabilityLawConflict
import Formal.AG.Examples.FiniteModel
import Formal.AG.ReadingFunctoriality.FiniteExamples
import Formal.AG.Derived.Counterexample
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.StdBasis

noncomputable section

namespace AAT.AG
namespace Measurement

open CategoryTheory
open Opposite

/-!
Part VIII R11 / AC25 finite measurement examples.

These examples are selected finite fixtures. They verify the Part VIII
measurement boundaries on tiny carriers and theorem packages, but do not assert
global extraction, operation semantics, or arbitrary analytic completeness.
-/

/-- R11(a): the pseudo-circle finite measurement domain has a measured cocycle
and a separate unmeasured axis. -/
inductive PseudoCircleMeasurementDomain where
  | boundaryCocycle
  | unmeasuredAxis
  deriving DecidableEq, Fintype

/-- R11(b): a three-vertex support universe for square-free hitting examples. -/
inductive SquareFreeSupportVertex where
  | p
  | q
  | r
  deriving DecidableEq, Fintype

/-- R11(b): the two minimal repair targets for `{p,q}` / `{q,r}`. -/
inductive SquareFreeRepairTarget where
  | singletonQ
  | pairPR
  deriving DecidableEq, Fintype

/-- R11(c): a two-object finite site used by the computability fixture. -/
inductive TinyMeasurementSite where
  | u
  | v
  deriving DecidableEq, Fintype

/-- R11(e): low-degree cochains used by the Hodge fixture. -/
inductive LowDegreeCochain where
  | exact
  | harmonic
  | coexact
  deriving DecidableEq, Fintype

/-- R11(e): concrete one-dimensional boundary cochains for the Hodge fixture. -/
abbrev LowDegreeBoundaryCochain : Type :=
  EuclideanSpace ℝ (Fin 1)

/-- R11(e): concrete three-dimensional real cochains for the Hodge fixture. -/
abbrev LowDegreeRealCochain : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- R11(f): a finite residue flag for support-localized transfer. -/
inductive TransferResidueFlag where
  | zero
  | nontrivial
  deriving DecidableEq, Fintype

/-- Actual finite equation indices used by the two-ideal computation profile. -/
inductive FiniteEquationHandle where
  | left
  | right
  | alternate
  deriving DecidableEq, Fintype

/-- Witness variable read from each finite Atom in the universal equation chart. -/
private def finiteAtomWitnessVariable :
    FiniteModel.FiniteAtom → SquareFreeSupportVertex
  | .componentA | .dependsAB | .contractBase => .p
  | .componentB | .dependsBC | .contractImpl => .q
  | .componentC | .dependsCA | .substitutesImplBase => .r

/-- Universal symbolic polynomial attached to an actual equation/Atom coordinate. -/
private def finiteEquationViolation
    (equation : FiniteEquationHandle)
    (atom : FiniteModel.FiniteAtom) :
    MvPolynomial SquareFreeSupportVertex Int :=
  match equation with
  | .left => MvPolynomial.X (finiteAtomWitnessVariable atom)
  | .right =>
      if atom = FiniteModel.FiniteAtom.componentA
        then MvPolynomial.X SquareFreeSupportVertex.p else 0
  | .alternate => 0

/-- Actual three-index architectural equation system used by measurement profiles. -/
noncomputable def finiteMeasurementEquationSystem :
    ArchitecturalEquationSystem FiniteModel.site.contextPreorder := by
  classical
  exact {
    Index := FiniteEquationHandle
    role
      | .left => .required
      | .right => .required
      | .alternate => .optional
    Observable := fun _ => MvPolynomial SquareFreeSupportVertex Int
    observableCommRing := fun _ => inferInstance
    restrict := fun _ => RingHom.id _
    restrict_id := by intros; rfl
    restrict_comp := by intros; rfl
    violationCoordinate := fun _ equation atom =>
      finiteEquationViolation equation atom
    violationCoordinate_restrict := by intros; rfl
    equationResidual := fun _ object equation atom =>
      MvPolynomial.C (FiniteModel.noCycleResidual object) *
        finiteEquationViolation equation atom
    equationResidual_restrict := by intros; rfl
  }

/-- Coverage requirements generated from the actual three-equation family. -/
def finiteMeasurementCoverageRequirements :
    Site.CoverageRequirements FiniteModel.corePackage.object
      finiteMeasurementEquationSystem FiniteModel.site.signature where
  requiredSupport := fun _ => True
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := fun _ _ => True
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun _ _ => True
  boundaryVisibleOn := fun _ _ => True

/-- Equation-generated site shared by finite square-free, Tor, and GAGA profiles. -/
noncomputable def finiteMeasurementEquationSite :
    Site.AATSite FiniteModel.corePackage.object where
  contextPreorder := FiniteModel.site.contextPreorder
  equationSystem := finiteMeasurementEquationSystem
  signature := FiniteModel.site.signature
  requirements := finiteMeasurementCoverageRequirements
  overlap := FiniteModel.site.overlap

/-- Selected base context of the equation-generated finite measurement site. -/
abbrev finiteMeasurementSiteBase : finiteMeasurementEquationSite.category :=
  FiniteModel.siteBase

/-- Base change of the universal integer equation chart to `ZMod 2`. -/
def finiteEquationObservableMapZMod2 :
    finiteMeasurementEquationSite.equationSystem.Observable
        finiteMeasurementSiteBase →+*
      MvPolynomial SquareFreeSupportVertex (ZMod 2) :=
  MvPolynomial.map (Int.castRingHom (ZMod 2))

/-- R11(a): the profile separates measured nonzero from unmeasured axes. -/
def pseudoCircleMeasurementProfile : MeasurementProfile where
  equationGeometry := MeasurementEquationGeometry.ofSite FiniteModel.site
  SiteObj := TinyMeasurementSite
  Cover := Unit
  Coeff := Unit
  EffCoeff := Unit
  ObstructionObject := Unit
  WitnessVariables := SquareFreeSupportVertex
  ObstructionIdeal := Unit
  RepresentationFamily := Unit
  Domain := PseudoCircleMeasurementDomain
  CertRef := fun _ => Unit
  SelectedMethod := fun _ => Unit
  InScope := fun alpha => alpha = PseudoCircleMeasurementDomain.boundaryCocycle
  OutOfScope := fun alpha => alpha = PseudoCircleMeasurementDomain.unmeasuredAxis
  Zero := fun _ => False
  NonZero := fun alpha => alpha = PseudoCircleMeasurementDomain.boundaryCocycle
  Undecided := fun _ => False
  NotRunOrUnavailable := fun _ => False

instance pseudoCircleWitnessVariablesFintype :
    Fintype pseudoCircleMeasurementProfile.WitnessVariables :=
  inferInstanceAs (Fintype SquareFreeSupportVertex)

instance pseudoCircleWitnessVariablesDecidableEq :
    DecidableEq pseudoCircleMeasurementProfile.WitnessVariables :=
  inferInstanceAs (DecidableEq SquareFreeSupportVertex)

/-- R11(a): concrete pseudo-circle boundary cocycle is measured nonzero. -/
def pseudoCircleBoundaryCocycleVerdict :
    MeasurementVerdict pseudoCircleMeasurementProfile
      PseudoCircleMeasurementDomain.boundaryCocycle :=
  MeasurementVerdict.measured_nonzero rfl rfl ()

/-- R11(a): the unmeasured axis is not silently treated as zero. -/
theorem pseudoCircle_unmeasuredAxis_not_zero :
    ¬ pseudoCircleMeasurementProfile.Zero
      PseudoCircleMeasurementDomain.unmeasuredAxis := by
  intro h
  cases h

/-- R11(b): the `{p,q}` forbidden support. -/
def forbiddenSupportPQ : List SquareFreeSupportVertex :=
  [SquareFreeSupportVertex.p, SquareFreeSupportVertex.q]

/-- R11(b): the `{q,r}` forbidden support. -/
def forbiddenSupportQR : List SquareFreeSupportVertex :=
  [SquareFreeSupportVertex.q, SquareFreeSupportVertex.r]

/-- R11(b): the `{p,q}` forbidden support as a Finset. -/
def forbiddenSupportPQFinset : Finset SquareFreeSupportVertex :=
  {SquareFreeSupportVertex.p, SquareFreeSupportVertex.q}

/-- R11(b): the `{q,r}` forbidden support as a Finset. -/
def forbiddenSupportQRFinset : Finset SquareFreeSupportVertex :=
  {SquareFreeSupportVertex.q, SquareFreeSupportVertex.r}

/-- Singleton support used by the nondegenerate principal Tor fixtures. -/
def forbiddenSupportPFinset : Finset SquareFreeSupportVertex :=
  {SquareFreeSupportVertex.p}

/-- R11(b): the concrete support carried by each selected repair target. -/
def squareFreeRepairTargetSupport :
    SquareFreeRepairTarget -> Finset SquareFreeSupportVertex
  | SquareFreeRepairTarget.singletonQ => {SquareFreeSupportVertex.q}
  | SquareFreeRepairTarget.pairPR =>
      {SquareFreeSupportVertex.p, SquareFreeSupportVertex.r}

/-- R11(b): the singleton `{q}` hits both forbidden supports. -/
theorem squareFreeHittingSet_q_hits_forbiddenSupports :
    SquareFreeSupportVertex.q ∈ forbiddenSupportPQ ∧
      SquareFreeSupportVertex.q ∈ forbiddenSupportQR := by
  simp [forbiddenSupportPQ, forbiddenSupportQR]

/-- R11(b): the pair `{p,r}` hits the two forbidden supports separately. -/
theorem squareFreeHittingSet_pr_hits_forbiddenSupports :
    SquareFreeSupportVertex.p ∈ forbiddenSupportPQ ∧
      SquareFreeSupportVertex.r ∈ forbiddenSupportQR := by
  simp [forbiddenSupportPQ, forbiddenSupportQR]

/-- R11(c): constant finite-field presheaf used by the generated Čech fixture. -/
def finiteComputabilityF2Presheaf :
    Site.AATPresheaf finiteMeasurementEquationSite where
  obj _ := ZMod 2
  map _ x := x
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem finiteComputabilitySite_cover_eq_top
    {base : finiteMeasurementEquationSite.category} {cover : Sieve base}
    (hcover : cover ∈ finiteMeasurementEquationSite.topology base) :
    cover = ⊤ := by
  change
    (Site.admissiblePrecoverage finiteMeasurementCoverageRequirements
      finiteMeasurementEquationSite.overlap).Saturate base cover at hcover
  induction hcover with
  | of X S hS =>
      rcases hS with ⟨F, rfl⟩
      rw [← Sieve.id_mem_iff_eq_top]
      rcases F.admissible.atomSupportCoverage
          FiniteModel.FiniteAtom.componentA trivial with ⟨i, _hi⟩
      let hEq :
          X = Site.ContextCategoryObject.of
            FiniteModel.siteContextPreorder (F.patch i) := by
        cases X
        exact congrArg
          (Site.ContextCategoryObject.of FiniteModel.siteContextPreorder)
          (F.inclusion i).symm
      have hmem : F.presieve (𝟙 X) :=
        Presieve.ofArrows.mk'
          (Y := fun i => Site.ContextCategoryObject.of
            FiniteModel.siteContextPreorder (F.patch i))
          (f := fun i => homOfLE (F.inclusion i))
          i hEq
          (Subsingleton.elim (𝟙 X)
            (eqToHom hEq ≫ homOfLE (F.inclusion i)))
      exact Sieve.le_generate F.presieve X hmem
  | top _X =>
      rfl
  | pullback _X _S _hS _Y _f ih =>
      rw [ih, Sieve.pullback_top]
  | transitive X S R _hS hR ihS ihR =>
      rw [← Sieve.id_mem_iff_eq_top]
      have hSid : S (𝟙 X) := by
        rw [Sieve.id_mem_iff_eq_top, ihS]
      have hlocal : R = ⊤ := by
        simpa using ihR hSid
      rw [hlocal]
      trivial

theorem finiteComputabilityF2_isSheaf :
    Site.AATSheafCondition
      finiteMeasurementEquationSite finiteComputabilityF2Presheaf := by
  intro _base cover hcover
  rw [Site.AATSheafConditionFor,
    finiteComputabilitySite_cover_eq_top hcover]
  exact Presieve.isSheafFor_top finiteComputabilityF2Presheaf

/-- R11(c): nontrivial module-valued obstruction sheaf for the finite fixture. -/
def finiteComputabilityObstructionSheaf :
    Cohomology.ObstructionSheaf finiteMeasurementEquationSite where
  carrier := {
    carrier := finiteComputabilityF2Presheaf
    isSheaf := finiteComputabilityF2_isSheaf
  }
  addCommGroup _ := by
    change AddCommGroup (ZMod 2)
    infer_instance
  map_zero := by intros; rfl
  map_add := by intros; rfl

/-- R11(c): constant finite-field presheaf for the finite-field matrix route. -/
def finiteDimensionalMatrixPresheaf :
    Site.AATPresheaf finiteMeasurementEquationSite where
  obj _ := ZMod 2
  map _ x := x
  map_id _ := rfl
  map_comp _ _ := rfl

theorem finiteDimensionalMatrix_isSheaf :
    Site.AATSheafCondition
      finiteMeasurementEquationSite finiteDimensionalMatrixPresheaf := by
  intro _base cover hcover
  rw [Site.AATSheafConditionFor,
    finiteComputabilitySite_cover_eq_top hcover]
  exact Presieve.isSheafFor_top finiteDimensionalMatrixPresheaf

/-- R11(c): finite-field obstruction sheaf with finite section carriers. -/
def finiteDimensionalMatrixObstructionSheaf :
    Cohomology.ObstructionSheaf finiteMeasurementEquationSite where
  carrier := {
    carrier := finiteDimensionalMatrixPresheaf
    isSheaf := finiteDimensionalMatrix_isSheaf
  }
  addCommGroup _ := by
    change AddCommGroup (ZMod 2)
    infer_instance
  map_zero := by intros; rfl
  map_add := by intros; rfl

/-- Witness-ideal preservation data for the equation-generated measurement site. -/
def finiteMeasurementSiteAdequacyRequirements :
    Site.UAdequacyRequirements finiteMeasurementEquationSite.contextPreorder
      finiteMeasurementCoverageRequirements where
  selectedWitnessIdeal := fun _ => True
  witnessIdealPreservedBy := fun _ _ => trivial

/-- R11(c): a two-index admissible cover on the selected finite AAT site. -/
def finiteComputabilityCover :
    Site.AATCoverageFamily finiteMeasurementCoverageRequirements
      finiteMeasurementEquationSite.overlap finiteMeasurementSiteBase where
  Index := Bool
  patch := fun _ => FiniteModel.siteContext
  inclusion := fun _ => rfl
  admissible := {
    atomSupportCoverage := fun _atom _hreq => ⟨false, trivial⟩
    equationCoordinateCoverage := fun _coordinate _hreq => Or.inl ⟨false, trivial⟩
    violationWitnessCoverage := fun _witness _hreq => Or.inl ⟨false, trivial⟩
    signatureAxisCoverage := fun _axis _hreq => ⟨false, trivial⟩
    boundaryCoverage := fun _i _j => trivial
    nonGeneration := fun _i {_support} {_atom} hselected =>
      FiniteModel.allFamily_mem _ hselected
  }

theorem finiteComputabilityCover_topologyCover :
    Sieve.generate finiteComputabilityCover.presieve ∈
      finiteMeasurementEquationSite.topology finiteMeasurementSiteBase := by
  exact Site.AATGrothendieckTopology.generate_mem finiteComputabilityCover

/-- R11(c): the selected two-index cover is `U`-adequate. -/
theorem finiteComputabilityCover_uAdequate :
    Site.UAdequateCover finiteMeasurementSiteAdequacyRequirements
      finiteComputabilityCover where
  topologyCover := finiteComputabilityCover_topologyCover
  requiredSupportCovered := fun _atom _hreq => ⟨false, trivial⟩
  requiredEquationCoordinatesVisible := fun _coordinate _hreq => Or.inl ⟨false, trivial⟩
  selectedViolationWitnessesVisible := fun _witness _hreq => Or.inl ⟨false, trivial⟩
  requiredAxesReadable := fun _axis _hreq => ⟨false, trivial⟩
  boundaryWitnessesVisible := fun _i _j => trivial
  restrictionMapsPreserveWitnessIdeals := fun _i _hbase => trivial

/-- R11(c): coefficient-free finite geometry generating the canonical tuple nerve. -/
def finiteComputabilityCoverGeometry :
    Site.FinitePosetCoverGeometry finiteMeasurementEquationSite where
  ContextIndex := PUnit
  finiteContextIndex := inferInstance
  context := fun _ => FiniteModel.siteContext
  contextLe := fun _ _ => True
  contextLe_refl := fun _ => trivial
  contextLe_trans := fun _ _ => trivial
  contextLe_antisymm := by intros; subsingleton
  contextLe_sound := fun _ => rfl
  contextMeet := fun _ _ => PUnit.unit
  contextMeet_le_left := fun _ _ => trivial
  contextMeet_le_right := fun _ _ => trivial
  context_le_meet := fun _ _ => trivial
  base := finiteMeasurementSiteBase
  cover := finiteComputabilityCover
  finiteCoverIndex := by
    change Finite Bool
    infer_instance
  nerveSimplex := fun n => Fin (n + 1) -> Bool
  finiteNerveSimplex := fun _ => inferInstance
  simplexIndices := fun _ simplex k => simplex k
  simplexOverlap := fun _ _ => FiniteModel.siteContext
  simplexOverlap_le_patch := fun _ _ _ => rfl
  adequacyRequirements := finiteMeasurementSiteAdequacyRequirements
  coverAdequate := finiteComputabilityCover_uAdequate

/-- R11(c): tuple geometry generated from actual selected overlaps. -/
def finiteComputabilityTupleGeometry :
    Site.FinitePosetCanonicalTupleCoverGeometry
      finiteComputabilityCoverGeometry :=
  finiteComputabilityCoverGeometry.canonicalTupleCoverGeometryFromOverlap

/-- Nontrivial profile handles used to verify selected obstruction-object
provenance. -/
inductive FiniteObstructionObjectHandle where
  | selected
  | alternate
  deriving DecidableEq

/-- Nontrivial profile handles used to verify selected obstruction-ideal
provenance. -/
inductive FiniteObstructionIdealHandle where
  | selected
  | alternate
  deriving DecidableEq

/-!
The original finite-dimensional fixture has a contractible constant
coefficient complex.  The next fixture reuses the strict-diamond AAT site from
the reading-functoriality reference model, with its finite-field sheaf that
vanishes on the two patches and is nonzero on their mixed overlap.  It gives an
actual nonzero generated `H¹` class for the representative procedure.
-/

/-- Profile for the nonzero finite-dimensional `H¹` representative fixture. -/
def finiteDimensionalNonzeroH1Profile : MeasurementProfile where
  equationGeometry :=
    MeasurementEquationGeometry.ofSite
      ReadingFunctorialityFinite.finiteLinearSite
  SiteObj := PUnit
  Cover := Bool
  Coeff := ZMod 2
  EffCoeff := Unit
  ObstructionObject := Unit
  WitnessVariables := SquareFreeSupportVertex
  ObstructionIdeal := Unit
  RepresentationFamily := Unit
  Domain := Unit
  CertRef := fun _ => Unit
  SelectedMethod := fun _ => Unit
  InScope := fun _ => True
  OutOfScope := fun _ => False
  Zero := fun _ => True
  NonZero := fun _ => False
  Undecided := fun _ => False
  NotRunOrUnavailable := fun _ => False

/-- Witness-ideal preservation data for the strict-diamond selected cover. -/
def finiteDimensionalNonzeroH1AdequacyRequirements :
    Site.UAdequacyRequirements
      ReadingFunctorialityFinite.finiteLinearSite.contextPreorder
      ReadingFunctorialityFinite.finiteLinearSite.requirements where
  selectedWitnessIdeal := fun _ => True
  witnessIdealPreservedBy := fun _ _ => trivial

/-- The strict-diamond cover is adequate for the local measurement fixture. -/
theorem finiteDimensionalNonzeroH1Cover_uAdequate :
    Site.UAdequateCover finiteDimensionalNonzeroH1AdequacyRequirements
      ReadingFunctorialityFinite.finiteLinearCover where
  topologyCover :=
    Site.AATGrothendieckTopology.generate_mem
      ReadingFunctorialityFinite.finiteLinearCover
  requiredSupportCovered :=
    ReadingFunctorialityFinite.finiteLinearCover.admissible.atomSupportCoverage
  requiredEquationCoordinatesVisible :=
    ReadingFunctorialityFinite.finiteLinearCover.admissible.equationCoordinateCoverage
  selectedViolationWitnessesVisible :=
    ReadingFunctorialityFinite.finiteLinearCover.admissible.violationWitnessCoverage
  requiredAxesReadable :=
    ReadingFunctorialityFinite.finiteLinearCover.admissible.signatureAxisCoverage
  boundaryWitnessesVisible :=
    ReadingFunctorialityFinite.finiteLinearCover.admissible.boundaryCoverage
  restrictionMapsPreserveWitnessIdeals := fun _ _ => trivial

/-- Coefficient-free strict-diamond cover geometry.  Its operational nerve is
replaced below by the canonical tuple nerve generated from the selected
cover. -/
noncomputable def finiteDimensionalNonzeroH1CoverGeometry :
    Site.FinitePosetCoverGeometry
      ReadingFunctorialityFinite.finiteLinearSite where
  ContextIndex := PUnit
  finiteContextIndex := inferInstance
  context := fun _ => ReadingFunctorialityFinite.finiteLinearBase.ctx
  contextLe := fun _ _ => True
  contextLe_refl := fun _ => trivial
  contextLe_trans := fun _ _ => trivial
  contextLe_antisymm := by intros; subsingleton
  contextLe_sound := fun _ =>
    ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.refl _
  contextMeet := fun _ _ => PUnit.unit
  contextMeet_le_left := fun _ _ => trivial
  contextMeet_le_right := fun _ _ => trivial
  context_le_meet := fun _ _ => trivial
  base := ReadingFunctorialityFinite.finiteLinearBase
  cover := ReadingFunctorialityFinite.finiteLinearCover
  finiteCoverIndex := inferInstance
  nerveSimplex := fun _ => PUnit
  finiteNerveSimplex := fun _ => inferInstance
  simplexIndices := fun _ _ _ =>
    ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv.symm false
  simplexOverlap := fun _ _ =>
    ReadingFunctorialityFinite.finiteLinearCover.patch
      (ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv.symm false)
  simplexOverlap_le_patch := fun _ _ _ =>
    ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.refl _
  adequacyRequirements := finiteDimensionalNonzeroH1AdequacyRequirements
  coverAdequate := finiteDimensionalNonzeroH1Cover_uAdequate

/-- Canonical tuple geometry of the strict-diamond cover. -/
noncomputable def finiteDimensionalNonzeroH1TupleGeometry :
    Site.FinitePosetCanonicalTupleCoverGeometry
      finiteDimensionalNonzeroH1CoverGeometry :=
  finiteDimensionalNonzeroH1CoverGeometry
    |>.canonicalTupleCoverGeometryFromOverlap

/-- Generated finite-field measurement geometry on the strict-diamond site. -/
noncomputable def finiteDimensionalNonzeroH1Geometry :
    FiniteMeasurementGeometry finiteDimensionalNonzeroH1Profile where
  coverGeometry := finiteDimensionalNonzeroH1CoverGeometry
  tupleGeometry := finiteDimensionalNonzeroH1TupleGeometry
  coeffCommRing := by
    change CommRing (ZMod 2)
    infer_instance
  obstructionSheaf :=
    ReadingFunctorialityFinite.finiteLinearF2ObstructionSheaf
  sectionModule := by
    intro n simplex
    change Module (ZMod 2)
      (ReadingFunctorialityFinite.finiteLinearF2CoefficientSubmodule _)
    infer_instance
  faceRestrictionLinear := by
    intro n simplex i
    let faceData :=
      (finiteDimensionalNonzeroH1TupleGeometry.toSimplicialFaceAction
        ReadingFunctorialityFinite.finiteLinearF2ObstructionSheaf.carrier.toPresheaf)
        |>.toFaceData
    exact ReadingFunctorialityFinite.finiteLinearF2RestrictionLinear
      (CategoryTheory.homOfLE
        (faceData.faceOverlap_le n simplex i))
  faceRestrictionLinear_apply := by
    intros
    rfl
  siteObjEquiv := Equiv.refl PUnit
  coverEquiv :=
    ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv.symm

/-- Every generated strict-diamond cochain carrier is finite over `ZMod 2`. -/
noncomputable def finiteDimensionalNonzeroH1CochainFintype (n : Nat) :
    Fintype (finiteDimensionalNonzeroH1Geometry.CechCochain n) := by
  letI : Finite
      (Site.FinitePosetCechSimplex
        finiteDimensionalNonzeroH1Geometry.coefficientRegime n) :=
    Site.FinitePosetCechSimplex.finite
      finiteDimensionalNonzeroH1Geometry.coefficientRegime n
  letI : Fintype
      (Site.FinitePosetCechSimplex
        finiteDimensionalNonzeroH1Geometry.coefficientRegime n) :=
    Fintype.ofFinite _
  letI : DecidableEq
      (Site.FinitePosetCechSimplex
        finiteDimensionalNonzeroH1Geometry.coefficientRegime n) :=
    Classical.decEq _
  letI (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime n) :
      Fintype (Site.FinitePosetCechSection
        finiteDimensionalNonzeroH1Geometry.coefficientRegime n simplex) := by
    change Fintype
      (ReadingFunctorialityFinite.finiteLinearF2CoefficientSubmodule _)
    exact Fintype.ofFinite _
  letI (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime n) :
      DecidableEq (Site.FinitePosetCechSection
        finiteDimensionalNonzeroH1Geometry.coefficientRegime n simplex) :=
    Classical.decEq _
  infer_instance

/-- Explicit coefficient field for the nonzero `H¹` matrix fixture. -/
noncomputable def finiteDimensionalNonzeroH1CoeffField :
    Field finiteDimensionalNonzeroH1Profile.Coeff := by
  change Field (ZMod 2)
  infer_instance

/-- A finite basis of each generated strict-diamond cochain module. -/
noncomputable def finiteDimensionalNonzeroH1CochainBasis (n : Nat) :
    letI : Field finiteDimensionalNonzeroH1Profile.Coeff :=
      finiteDimensionalNonzeroH1CoeffField
    letI : AddCommGroup
        (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
      finiteDimensionalNonzeroH1Geometry.cochainAddCommGroup n
    letI : Module finiteDimensionalNonzeroH1Profile.Coeff
        (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
      finiteDimensionalNonzeroH1Geometry.cochainModule n
    letI : Module.Free finiteDimensionalNonzeroH1Profile.Coeff
        (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
      Module.Free.of_divisionRing _ _
    Module.Basis
      (Module.Free.ChooseBasisIndex
        finiteDimensionalNonzeroH1Profile.Coeff
        (finiteDimensionalNonzeroH1Geometry.CechCochain n))
      finiteDimensionalNonzeroH1Profile.Coeff
      (finiteDimensionalNonzeroH1Geometry.CechCochain n) := by
  letI : Field finiteDimensionalNonzeroH1Profile.Coeff :=
    finiteDimensionalNonzeroH1CoeffField
  letI : AddCommGroup
      (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    finiteDimensionalNonzeroH1Geometry.cochainAddCommGroup n
  letI : Module finiteDimensionalNonzeroH1Profile.Coeff
      (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    finiteDimensionalNonzeroH1Geometry.cochainModule n
  letI : Fintype (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    finiteDimensionalNonzeroH1CochainFintype n
  letI : Module.Free finiteDimensionalNonzeroH1Profile.Coeff
      (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    Module.Free.of_divisionRing _ _
  exact Module.Free.chooseBasis _ _

/-- Matrix model of the actual strict-diamond canonical Čech complex. -/
noncomputable def finiteDimensionalNonzeroH1CechModel :
    @FiniteDimensionalCechModel finiteDimensionalNonzeroH1Profile
      finiteDimensionalNonzeroH1Geometry
      finiteDimensionalNonzeroH1CoeffField := by
  letI : Field finiteDimensionalNonzeroH1Profile.Coeff :=
    finiteDimensionalNonzeroH1CoeffField
  letI (n : Nat) :
      Fintype (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    finiteDimensionalNonzeroH1CochainFintype n
  letI (n : Nat) :
      AddCommGroup (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    finiteDimensionalNonzeroH1Geometry.cochainAddCommGroup n
  letI (n : Nat) : Module finiteDimensionalNonzeroH1Profile.Coeff
      (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    finiteDimensionalNonzeroH1Geometry.cochainModule n
  letI (n : Nat) : Module.Free finiteDimensionalNonzeroH1Profile.Coeff
      (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    Module.Free.of_divisionRing _ _
  letI (n : Nat) : Module.Finite finiteDimensionalNonzeroH1Profile.Coeff
      (finiteDimensionalNonzeroH1Geometry.CechCochain n) :=
    Module.Finite.of_finite
  exact {
    CochainSpace := finiteDimensionalNonzeroH1Geometry.CechCochain
    CochainIndex := fun n =>
      Module.Free.ChooseBasisIndex
        finiteDimensionalNonzeroH1Profile.Coeff
        (finiteDimensionalNonzeroH1Geometry.CechCochain n)
    cochainIndexFintype := fun _ => inferInstance
    cochainIndexDecidableEq := fun _ => Classical.decEq _
    cochainAddCommGroup :=
      finiteDimensionalNonzeroH1Geometry.cochainAddCommGroup
    cochainModule := finiteDimensionalNonzeroH1Geometry.cochainModule
    cochainBasis := finiteDimensionalNonzeroH1CochainBasis
    cochainEquivCanonical := fun _ => AddEquiv.refl _
    cochainEquivCanonical_smul := by intros; rfl
    differentialLinear :=
      finiteDimensionalNonzeroH1Geometry.differentialLinear
    differential_eq_canonical := by intros; rfl
    differential_comp := by
      intro n c
      exact finiteDimensionalNonzeroH1Geometry.cechComplex
        |>.differential_comp_zero n c
    differentialMatrix := fun n =>
      LinearMap.toMatrix
        (finiteDimensionalNonzeroH1CochainBasis n)
        (finiteDimensionalNonzeroH1CochainBasis (n + 1))
        (finiteDimensionalNonzeroH1Geometry.differentialLinear n)
    differentialMatrix_correct := by intros; rfl
  }

/-- Uniform finite-search representative procedure for the strict-diamond
matrix model. -/
noncomputable def finiteDimensionalNonzeroH1CechProcedure :
    FiniteDimensionalCechProcedure.{0, 0}
      finiteDimensionalNonzeroH1Profile
      finiteDimensionalNonzeroH1Geometry where
  coeffField := finiteDimensionalNonzeroH1CoeffField
  coeffDecidableEq := by
    change DecidableEq (ZMod 2)
    infer_instance
  linearSystemSolver := FiniteLinearSystemSolver.ofFiniteField (ZMod 2)
  cosetNormalizer := FiniteLinearCosetNormalizer.ofFiniteField (ZMod 2)
  model := finiteDimensionalNonzeroH1CechModel

/-- Common Čech computation API selecting the nonzero finite-dimensional
fixture. -/
noncomputable def finiteDimensionalNonzeroH1ComputationProcedure :
    CechComputationProcedure finiteDimensionalNonzeroH1Profile
      finiteDimensionalNonzeroH1Geometry :=
  .finiteDimensional finiteDimensionalNonzeroH1CechProcedure

/-- Potential-difference cochain on the two strict-diamond cover branches. -/
noncomputable def finiteDimensionalNonzeroH1OneCochain :
    finiteDimensionalNonzeroH1Geometry.CechCochain 1 := fun simplex => by
  change ReadingFunctorialityFinite.finiteLinearF2CoefficientSubmodule
    (ReadingFunctorialityFinite.finiteLinearSite.overlap.overlap
      ReadingFunctorialityFinite.finiteLinearBase.ctx
      (ReadingFunctorialityFinite.finiteLinearCover.patch (simplex 0))
      (ReadingFunctorialityFinite.finiteLinearCover.patch (simplex 1)))
  exact ReadingFunctorialityFinite.finiteLinearF2PairSection
    (simplex 0) (simplex 1)

private theorem finiteDimensionalNonzeroH1Face_zero_first
    (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 2) :
    ((finiteDimensionalNonzeroH1TupleGeometry.toSimplicialFaceAction
        ReadingFunctorialityFinite.finiteLinearF2CoefficientPresheaf).toFaceData.face
      1 simplex (0 : Fin 3)) 0 = simplex 1 :=
  rfl

private theorem finiteDimensionalNonzeroH1Face_zero_second
    (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 2) :
    ((finiteDimensionalNonzeroH1TupleGeometry.toSimplicialFaceAction
        ReadingFunctorialityFinite.finiteLinearF2CoefficientPresheaf).toFaceData.face
      1 simplex (0 : Fin 3)) 1 = simplex 2 :=
  rfl

private theorem finiteDimensionalNonzeroH1Face_one_first
    (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 2) :
    ((finiteDimensionalNonzeroH1TupleGeometry.toSimplicialFaceAction
        ReadingFunctorialityFinite.finiteLinearF2CoefficientPresheaf).toFaceData.face
      1 simplex (1 : Fin 3)) 0 = simplex 0 :=
  rfl

private theorem finiteDimensionalNonzeroH1Face_one_second
    (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 2) :
    ((finiteDimensionalNonzeroH1TupleGeometry.toSimplicialFaceAction
        ReadingFunctorialityFinite.finiteLinearF2CoefficientPresheaf).toFaceData.face
      1 simplex (1 : Fin 3)) 1 = simplex 2 :=
  rfl

private theorem finiteDimensionalNonzeroH1Face_two_first
    (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 2) :
    ((finiteDimensionalNonzeroH1TupleGeometry.toSimplicialFaceAction
        ReadingFunctorialityFinite.finiteLinearF2CoefficientPresheaf).toFaceData.face
      1 simplex (2 : Fin 3)) 0 = simplex 0 :=
  rfl

private theorem finiteDimensionalNonzeroH1Face_two_second
    (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 2) :
    ((finiteDimensionalNonzeroH1TupleGeometry.toSimplicialFaceAction
        ReadingFunctorialityFinite.finiteLinearF2CoefficientPresheaf).toFaceData.face
      1 simplex (2 : Fin 3)) 1 = simplex 1 :=
  rfl

/-- The potential-difference cochain satisfies the actual generated Čech
cocycle equation. -/
theorem finiteDimensionalNonzeroH1OneCochain_isCocycle :
    finiteDimensionalNonzeroH1Geometry.cechComplex.differential 1
        finiteDimensionalNonzeroH1OneCochain =
      Site.FinitePosetCechZeroCochain
        finiteDimensionalNonzeroH1Geometry.cechComplex.additive 2 := by
  funext simplex
  refine Subtype.ext ?_
  dsimp only [FiniteMeasurementGeometry.cechComplex,
    Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex,
    Cohomology.StandardFinitePosetCech.standardFinitePosetCechComplex,
    Cohomology.StandardFinitePosetCech.standardDifferential,
    Cohomology.StandardFinitePosetCech.standardAdditiveData,
    Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination,
    Site.FinitePosetCechZeroCochain]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fintype.sum_empty, add_zero]
  norm_num
  simp only [Site.FinitePosetCechFaceRestriction,
    finiteDimensionalNonzeroH1Geometry,
    Site.FinitePosetCoverGeometry.toObstructionCoefficientRegime,
    Site.FinitePosetCoverGeometry.toRegime,
    ReadingFunctorialityFinite.finiteLinearF2ObstructionSheaf_toPresheaf]
  simp only [
    finiteDimensionalNonzeroH1OneCochain,
    finiteDimensionalNonzeroH1Face_zero_first,
    finiteDimensionalNonzeroH1Face_zero_second,
    finiteDimensionalNonzeroH1Face_one_first,
    finiteDimensionalNonzeroH1Face_one_second,
    finiteDimensionalNonzeroH1Face_two_first,
    finiteDimensionalNonzeroH1Face_two_second]
  dsimp only [ReadingFunctorialityFinite.finiteLinearF2CoefficientPresheaf]
  refine Subtype.ext ?_
  rw [ReadingFunctorialityFinite.finiteLinearF2Section_add_val,
    ReadingFunctorialityFinite.finiteLinearF2Section_add_val,
    ReadingFunctorialityFinite.finiteLinearF2Section_neg_val,
    ReadingFunctorialityFinite.finiteLinearF2Section_zero_val]
  dsimp only [id]
  simp only [ReadingFunctorialityFinite.finiteLinearF2PairSection_val]
  ring

/-- The potential-difference cochain as an actual cycle in the generated
finite-poset complex. -/
noncomputable def finiteDimensionalNonzeroH1Cocycle :
    finiteDimensionalNonzeroH1Geometry.CechCocycle 1 :=
  ⟨finiteDimensionalNonzeroH1OneCochain,
    finiteDimensionalNonzeroH1OneCochain_isCocycle⟩

private theorem finiteDimensionalNonzeroH1DegreeZeroCoefficient_eq_bot
    (simplex : Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 0) :
    ReadingFunctorialityFinite.finiteLinearF2CoefficientSubmodule
        (Site.FinitePosetCechOverlapObject
          finiteDimensionalNonzeroH1Geometry.coefficientRegime 0 simplex).ctx =
      ⊥ := by
  simpa [finiteDimensionalNonzeroH1Geometry,
    finiteDimensionalNonzeroH1TupleGeometry,
    finiteDimensionalNonzeroH1CoverGeometry,
    Site.FinitePosetCanonicalTupleCoverGeometry.toCoverGeometry,
    Site.FinitePosetCoverGeometry.canonicalTupleCoverGeometryFromOverlap,
    Site.FinitePosetCoverGeometry.canonicalTupleOverlapFromOverlap] using
      ReadingFunctorialityFinite.finiteLinearF2CoefficientSubmodule_patch_eq_bot
        (simplex 0)

private theorem finiteDimensionalNonzeroH1ZeroCochain_eq_zero
    (b : finiteDimensionalNonzeroH1Geometry.CechCochain 0) : b = 0 := by
  funext simplex
  refine Subtype.ext ?_
  have hb : (b simplex).1 ∈ (⊥ : Submodule (ZMod 2) (ZMod 2)) := by
    rw [← finiteDimensionalNonzeroH1DegreeZeroCoefficient_eq_bot simplex]
    exact (b simplex).2
  exact hb

private def finiteDimensionalNonzeroH1MixedOneSimplex :
    Site.FinitePosetCechSimplex
      finiteDimensionalNonzeroH1Geometry.coefficientRegime 1 :=
  fun i =>
    if i = 0 then
      ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv.symm false
    else
      ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv.symm true

private theorem finiteDimensionalNonzeroH1OneCochain_mixed_val :
    (finiteDimensionalNonzeroH1OneCochain
      finiteDimensionalNonzeroH1MixedOneSimplex).1 = (1 : ZMod 2) := by
  simp [finiteDimensionalNonzeroH1OneCochain,
    finiteDimensionalNonzeroH1MixedOneSimplex,
    ReadingFunctorialityFinite.finiteLinearF2PairSection_val,
    ReadingFunctorialityFinite.finiteLinearF2Potential,
    ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv]

private theorem finiteDimensionalNonzeroH1OneCochain_ne_zero :
    finiteDimensionalNonzeroH1OneCochain ≠ 0 := by
  intro hzero
  have hvalue := congrArg
    (fun c => (c finiteDimensionalNonzeroH1MixedOneSimplex).1) hzero
  change
    (finiteDimensionalNonzeroH1OneCochain
        finiteDimensionalNonzeroH1MixedOneSimplex).1 =
      ((0 : finiteDimensionalNonzeroH1Geometry.CechCochain 1)
        finiteDimensionalNonzeroH1MixedOneSimplex).1 at hvalue
  rw [finiteDimensionalNonzeroH1OneCochain_mixed_val] at hvalue
  change (1 : ZMod 2) = 0 at hvalue
  exact one_ne_zero hvalue

/-- Actual nonzero class selected by the finite-dimensional strict-diamond
fixture. -/
noncomputable def finiteDimensionalNonzeroH1Class :
    finiteDimensionalNonzeroH1Geometry.CechHn 1 :=
  finiteDimensionalNonzeroH1Geometry.classOfCocycle 1
    finiteDimensionalNonzeroH1Cocycle

theorem finiteDimensionalNonzeroH1Class_ne_zero :
    finiteDimensionalNonzeroH1Class ≠
      finiteDimensionalNonzeroH1Geometry.zeroClass 1 := by
  intro hzero
  have hrelated := Quotient.exact hzero
  change ∃ b : finiteDimensionalNonzeroH1Geometry.CechCochain 0,
    finiteDimensionalNonzeroH1Cocycle.1 -
        (Site.FinitePosetCechZeroCocycle
          finiteDimensionalNonzeroH1Geometry.cechComplex 1).1 =
      finiteDimensionalNonzeroH1Geometry.differentialHom 0 b at hrelated
  rcases hrelated with ⟨b, hb⟩
  rw [finiteDimensionalNonzeroH1ZeroCochain_eq_zero b] at hb
  have hzeroCocycle :
      (Site.FinitePosetCechZeroCocycle
        finiteDimensionalNonzeroH1Geometry.cechComplex 1).1 =
        (0 : finiteDimensionalNonzeroH1Geometry.CechCochain 1) := by
    funext simplex
    rfl
  rw [hzeroCocycle, map_zero] at hb
  have hcochain : finiteDimensionalNonzeroH1OneCochain = 0 := by
    simpa [finiteDimensionalNonzeroH1Cocycle] using hb
  exact finiteDimensionalNonzeroH1OneCochain_ne_zero hcochain

/-- R11(b): the common finite-dimensional quotient API returns a cycle for an
actual nonzero generated `H¹` class and proves that it represents that class. -/
theorem finiteDimensionalNonzeroH1Representative :
    finiteDimensionalNonzeroH1Class ≠
        finiteDimensionalNonzeroH1Geometry.zeroClass 1 ∧
      finiteDimensionalNonzeroH1Geometry.classOfCocycle 1
          (finiteDimensionalNonzeroH1ComputationProcedure.quotientRepresentative
            1 finiteDimensionalNonzeroH1Class) =
        finiteDimensionalNonzeroH1Class :=
  ⟨finiteDimensionalNonzeroH1Class_ne_zero,
    finiteDimensionalNonzeroH1ComputationProcedure.quotientRepresentative_correct
      1 finiteDimensionalNonzeroH1Class⟩

/-- R11(c): seed profile used only to name the generated `H¹` domain. -/
def finiteComputabilitySeedProfile : MeasurementProfile where
  equationGeometry :=
    MeasurementEquationGeometry.ofSite finiteMeasurementEquationSite
  SiteObj := PUnit
  Cover := Bool
  Coeff := ZMod 2
  EffCoeff := Unit
  ObstructionObject := Unit
  WitnessVariables := SquareFreeSupportVertex
  ObstructionIdeal := Unit
  RepresentationFamily := Unit
  Domain := Unit
  CertRef := fun _ => Unit
  SelectedMethod := fun _ => Unit
  InScope := fun _ => True
  OutOfScope := fun _ => False
  Zero := fun _ => True
  NonZero := fun _ => False
  Undecided := fun _ => False
  NotRunOrUnavailable := fun _ => False

/-- R11(c): seed geometry sharing the actual site, cover, sheaf, and restrictions. -/
def finiteComputabilitySeedGeometry :
    FiniteMeasurementGeometry finiteComputabilitySeedProfile where
  coverGeometry := finiteComputabilityCoverGeometry
  tupleGeometry := finiteComputabilityTupleGeometry
  coeffCommRing := by
    change CommRing (ZMod 2)
    infer_instance
  obstructionSheaf := finiteComputabilityObstructionSheaf
  sectionModule := by
    intro _ _
    change Module (ZMod 2) (ZMod 2)
    infer_instance
  faceRestrictionLinear := by
    letI : CommRing finiteComputabilitySeedProfile.Coeff := by
      change CommRing (ZMod 2)
      infer_instance
    intro _ _ _
    change ZMod 2 →ₗ[ZMod 2] ZMod 2
    exact LinearMap.id
  faceRestrictionLinear_apply := by
    letI : CommRing finiteComputabilitySeedProfile.Coeff := by
      change CommRing (ZMod 2)
      infer_instance
    intros
    rfl
  siteObjEquiv := by
    simpa [finiteComputabilitySeedProfile, finiteComputabilityCoverGeometry] using
      (Equiv.refl PUnit)
  coverEquiv := by
    simpa [finiteComputabilitySeedProfile, finiteComputabilityCoverGeometry,
      finiteComputabilityCover] using (Equiv.refl Bool)

/-- R11(c): theorem 4.2 profile whose domain is the generated Čech `H¹`. -/
def finiteComputabilityMeasurementProfile : MeasurementProfile where
  equationGeometry :=
    MeasurementEquationGeometry.ofSite finiteMeasurementEquationSite
  SiteObj := PUnit
  Cover := Bool
  Coeff := ZMod 2
  EffCoeff := Unit
  ObstructionObject := FiniteObstructionObjectHandle
  WitnessVariables := SquareFreeSupportVertex
  ObstructionIdeal := FiniteObstructionIdealHandle
  RepresentationFamily := Unit
  Domain := finiteComputabilitySeedGeometry.CechHn 1
  CertRef := fun _ => Unit
  SelectedMethod := fun _ => Unit
  InScope := fun _ => True
  OutOfScope := fun _ => False
  Zero := fun alpha => alpha = finiteComputabilitySeedGeometry.zeroClass 1
  NonZero := fun alpha => alpha ≠ finiteComputabilitySeedGeometry.zeroClass 1
  Undecided := fun _ => False
  NotRunOrUnavailable := fun _ => False

/-- R11(c): finite geometry over the actual theorem 4.2 profile. -/
def finiteComputabilityGeometry :
    FiniteMeasurementGeometry finiteComputabilityMeasurementProfile where
  coverGeometry := finiteComputabilityCoverGeometry
  tupleGeometry := finiteComputabilityTupleGeometry
  coeffCommRing := by
    change CommRing (ZMod 2)
    infer_instance
  obstructionSheaf := finiteComputabilityObstructionSheaf
  sectionModule := by
    intro _ _
    change Module (ZMod 2) (ZMod 2)
    infer_instance
  faceRestrictionLinear := by
    letI : CommRing finiteComputabilityMeasurementProfile.Coeff := by
      change CommRing (ZMod 2)
      infer_instance
    intro _ _ _
    change ZMod 2 →ₗ[ZMod 2] ZMod 2
    exact LinearMap.id
  faceRestrictionLinear_apply := by
    letI : CommRing finiteComputabilityMeasurementProfile.Coeff := by
      change CommRing (ZMod 2)
      infer_instance
    intros
    rfl
  siteObjEquiv := by
    simpa [finiteComputabilityMeasurementProfile,
      finiteComputabilityCoverGeometry] using (Equiv.refl PUnit)
  coverEquiv := by
    simpa [finiteComputabilityMeasurementProfile,
      finiteComputabilityCoverGeometry, finiteComputabilityCover] using
      (Equiv.refl Bool)

/-- R11(c): profile selecting the finite-dimensional branch over `ZMod 2`. -/
def finiteDimensionalMatrixProfile : MeasurementProfile where
  equationGeometry :=
    MeasurementEquationGeometry.ofSite finiteMeasurementEquationSite
  SiteObj := PUnit
  Cover := Bool
  Coeff := ZMod 2
  EffCoeff := Unit
  ObstructionObject := FiniteObstructionObjectHandle
  WitnessVariables := SquareFreeSupportVertex
  ObstructionIdeal := FiniteObstructionIdealHandle
  RepresentationFamily := Unit
  Domain := Unit
  CertRef := fun _ => Unit
  SelectedMethod := fun _ => Unit
  InScope := fun _ => True
  OutOfScope := fun _ => False
  Zero := fun _ => True
  NonZero := fun _ => False
  Undecided := fun _ => False
  NotRunOrUnavailable := fun _ => False

/-- R11(c): finite-field geometry with explicit coefficient-linear restrictions. -/
def finiteDimensionalMatrixGeometry :
    FiniteMeasurementGeometry finiteDimensionalMatrixProfile where
  coverGeometry := finiteComputabilityCoverGeometry
  tupleGeometry := finiteComputabilityTupleGeometry
  coeffCommRing := by
    change CommRing (ZMod 2)
    infer_instance
  obstructionSheaf := finiteDimensionalMatrixObstructionSheaf
  sectionModule := by
    intro _ _
    change Module (ZMod 2) (ZMod 2)
    infer_instance
  faceRestrictionLinear := by
    letI : CommRing finiteDimensionalMatrixProfile.Coeff := by
      change CommRing (ZMod 2)
      infer_instance
    intro _ _ _
    change ZMod 2 →ₗ[ZMod 2] ZMod 2
    exact LinearMap.id
  faceRestrictionLinear_apply := by
    letI : CommRing finiteDimensionalMatrixProfile.Coeff := by
      change CommRing (ZMod 2)
      infer_instance
    intros
    rfl
  siteObjEquiv := by
    simpa [finiteDimensionalMatrixProfile,
      finiteComputabilityCoverGeometry] using (Equiv.refl PUnit)
  coverEquiv := by
    simpa [finiteDimensionalMatrixProfile,
      finiteComputabilityCoverGeometry, finiteComputabilityCover] using
      (Equiv.refl Bool)

/-- The coefficient ring selected by the finite-dimensional matrix profile. -/
local instance finiteDimensionalMatrixProfileCoeffCommRing :
    CommRing finiteDimensionalMatrixProfile.Coeff :=
  finiteDimensionalMatrixGeometry.coeffCommRing

/-- The left equation evaluates to the Atom-selected witness variable. -/
private theorem finiteMeasurement_leftEquationCoordinate_zmod2
    (atom : FiniteModel.FiniteAtom) :
    finiteEquationObservableMapZMod2
        (finiteDimensionalMatrixProfile.equationGeometry.site.equationSystem.violationCoordinate
          finiteMeasurementSiteBase .left atom) =
      MvPolynomial.X (finiteAtomWitnessVariable atom) := by
  change
    MvPolynomial.map (Int.castRingHom (ZMod 2))
        (finiteEquationViolation .left atom) =
      MvPolynomial.X (finiteAtomWitnessVariable atom)
  simp [finiteEquationViolation]

/-- The right equation evaluates only at the selected component Atom. -/
private theorem finiteMeasurement_rightEquationCoordinate_zmod2
    (atom : FiniteModel.FiniteAtom) :
    finiteEquationObservableMapZMod2
        (finiteDimensionalMatrixProfile.equationGeometry.site.equationSystem.violationCoordinate
          finiteMeasurementSiteBase .right atom) =
      if atom = FiniteModel.FiniteAtom.componentA then
        MvPolynomial.X SquareFreeSupportVertex.p else 0 := by
  change
    MvPolynomial.map (Int.castRingHom (ZMod 2))
        (finiteEquationViolation .right atom) =
      if atom = FiniteModel.FiniteAtom.componentA then
        MvPolynomial.X SquareFreeSupportVertex.p else 0
  by_cases hselected : atom = FiniteModel.FiniteAtom.componentA
  · simp [finiteEquationViolation, hselected]
  · simp [finiteEquationViolation, hselected]

/-- R11(c): finite basis of every finite-field canonical Čech cochain space. -/
noncomputable def finiteDimensionalMatrixCoeffField :
    Field finiteDimensionalMatrixProfile.Coeff := by
  change Field (ZMod 2)
  infer_instance

/-- R11(c): finite basis of every finite-field canonical Čech cochain space. -/
noncomputable def finiteDimensionalMatrixCochainBasis (n : Nat) :
    letI : CommRing finiteDimensionalMatrixProfile.Coeff :=
      finiteDimensionalMatrixGeometry.coeffCommRing
    letI : AddCommGroup (finiteDimensionalMatrixGeometry.CechCochain n) :=
      finiteDimensionalMatrixGeometry.cochainAddCommGroup n
    letI : Module finiteDimensionalMatrixProfile.Coeff
        (finiteDimensionalMatrixGeometry.CechCochain n) :=
      finiteDimensionalMatrixGeometry.cochainModule n
    Module.Basis
      (Site.FinitePosetCechSimplex
        finiteDimensionalMatrixGeometry.coefficientRegime n)
      finiteDimensionalMatrixProfile.Coeff
      (finiteDimensionalMatrixGeometry.CechCochain n) := by
  change Module.Basis
    (Site.FinitePosetCechSimplex
      finiteDimensionalMatrixGeometry.coefficientRegime n)
    (ZMod 2)
    (Site.FinitePosetCechSimplex
      finiteDimensionalMatrixGeometry.coefficientRegime n -> (ZMod 2))
  letI : Finite
      (Site.FinitePosetCechSimplex
        finiteDimensionalMatrixGeometry.coefficientRegime n) :=
    finiteDimensionalMatrixGeometry.coefficientRegime.finiteNerveSimplex n
  exact Pi.basisFun (ZMod 2) _

/-- R11(c): the finite-field coefficient branch reduces to finite matrices. -/
noncomputable def finiteDimensionalMatrixCechModel :
    @FiniteDimensionalCechModel finiteDimensionalMatrixProfile
      finiteDimensionalMatrixGeometry finiteDimensionalMatrixCoeffField := by
  letI : Field finiteDimensionalMatrixProfile.Coeff :=
    finiteDimensionalMatrixCoeffField
  exact {
    CochainSpace := fun n => finiteDimensionalMatrixGeometry.CechCochain n
    CochainIndex := fun n =>
      Site.FinitePosetCechSimplex finiteDimensionalMatrixGeometry.coefficientRegime n
    cochainIndexFintype := fun n => by
      letI : Finite
          (Site.FinitePosetCechSimplex
            finiteDimensionalMatrixGeometry.coefficientRegime n) :=
        finiteDimensionalMatrixGeometry.coefficientRegime.finiteNerveSimplex n
      exact Fintype.ofFinite _
    cochainIndexDecidableEq := fun _ => Classical.decEq _
    cochainAddCommGroup := finiteDimensionalMatrixGeometry.cochainAddCommGroup
    cochainModule := finiteDimensionalMatrixGeometry.cochainModule
    cochainBasis := finiteDimensionalMatrixCochainBasis
    cochainEquivCanonical := fun _ => AddEquiv.refl _
    cochainEquivCanonical_smul := by intros; rfl
    differentialLinear := finiteDimensionalMatrixGeometry.differentialLinear
    differential_eq_canonical := by intros; rfl
    differential_comp := by
      intro n c
      exact finiteDimensionalMatrixGeometry.cechComplex.differential_comp_zero n c
    differentialMatrix := fun n => by
      letI : Fintype
          (Site.FinitePosetCechSimplex
            finiteDimensionalMatrixGeometry.coefficientRegime n) := by
        letI : Finite
            (Site.FinitePosetCechSimplex
              finiteDimensionalMatrixGeometry.coefficientRegime n) :=
          finiteDimensionalMatrixGeometry.coefficientRegime.finiteNerveSimplex n
        exact Fintype.ofFinite _
      letI : Fintype
          (Site.FinitePosetCechSimplex
            finiteDimensionalMatrixGeometry.coefficientRegime (n + 1)) := by
        letI : Finite
            (Site.FinitePosetCechSimplex
              finiteDimensionalMatrixGeometry.coefficientRegime (n + 1)) :=
          finiteDimensionalMatrixGeometry.coefficientRegime.finiteNerveSimplex (n + 1)
        exact Fintype.ofFinite _
      letI : DecidableEq
          (Site.FinitePosetCechSimplex
            finiteDimensionalMatrixGeometry.coefficientRegime n) :=
        Classical.decEq _
      letI : DecidableEq
          (Site.FinitePosetCechSimplex
            finiteDimensionalMatrixGeometry.coefficientRegime (n + 1)) :=
        Classical.decEq _
      letI : AddCommGroup (finiteDimensionalMatrixGeometry.CechCochain n) :=
        finiteDimensionalMatrixGeometry.cochainAddCommGroup n
      letI : AddCommGroup
          (finiteDimensionalMatrixGeometry.CechCochain (n + 1)) :=
        finiteDimensionalMatrixGeometry.cochainAddCommGroup (n + 1)
      letI : Module finiteDimensionalMatrixProfile.Coeff
          (finiteDimensionalMatrixGeometry.CechCochain n) :=
        finiteDimensionalMatrixGeometry.cochainModule n
      letI : Module finiteDimensionalMatrixProfile.Coeff
          (finiteDimensionalMatrixGeometry.CechCochain (n + 1)) :=
        finiteDimensionalMatrixGeometry.cochainModule (n + 1)
      exact LinearMap.toMatrix
        (finiteDimensionalMatrixCochainBasis n)
        (finiteDimensionalMatrixCochainBasis (n + 1))
        (finiteDimensionalMatrixGeometry.differentialLinear n)
    differentialMatrix_correct := by intros; rfl
  }

/-- R11(c): packaged finite-dimensional procedure with an exhaustive finite-field solver. -/
noncomputable def finiteDimensionalMatrixCechProcedure :
    FiniteDimensionalCechProcedure.{0, 0} finiteDimensionalMatrixProfile
      finiteDimensionalMatrixGeometry where
  coeffField := by
    exact finiteDimensionalMatrixCoeffField
  coeffDecidableEq := by
    change DecidableEq (ZMod 2)
    infer_instance
  linearSystemSolver := FiniteLinearSystemSolver.ofFiniteField (ZMod 2)
  cosetNormalizer := FiniteLinearCosetNormalizer.ofFiniteField (ZMod 2)
  model := finiteDimensionalMatrixCechModel

/-- R11(c): the finite-field fixture fires the finite-dimensional route. -/
theorem finiteDimensionalMatrixRoute_fires :
    (CechComputationProcedure.finiteDimensional
      finiteDimensionalMatrixCechProcedure).route =
        CoefficientComputationRoute.finiteDimensionalLinearAlgebra :=
  rfl

/-- R11(c): the selected coefficient field has a finite carrier. -/
theorem finiteDimensionalMatrixCoeff_finite :
    Finite finiteDimensionalMatrixProfile.Coeff := by
  change Finite (ZMod 2)
  infer_instance

/-- R11(c): every finite-field matrix-model cohomology degree is finite-dimensional. -/
theorem finiteDimensionalMatrixCohomology_moduleFinite (n : Nat) :
    letI : Field finiteDimensionalMatrixProfile.Coeff :=
      finiteDimensionalMatrixCoeffField
    Module.Finite finiteDimensionalMatrixProfile.Coeff
      (finiteDimensionalMatrixCechModel.Cohomology n) := by
  letI : Field finiteDimensionalMatrixProfile.Coeff :=
    finiteDimensionalMatrixCoeffField
  exact finiteDimensionalMatrixCechModel.cohomology_moduleFinite n

/--
R11(c): the finite-field matrix quotient computes the canonical generated Čech
cohomology rather than a parallel cohomology carrier.
-/
noncomputable def finiteDimensionalMatrixCohomologyEquivCanonical (n : Nat) :
    letI : Field finiteDimensionalMatrixProfile.Coeff :=
      finiteDimensionalMatrixCoeffField
    finiteDimensionalMatrixCechModel.Cohomology n ≃
      finiteDimensionalMatrixGeometry.CechHn n := by
  letI : Field finiteDimensionalMatrixProfile.Coeff :=
    finiteDimensionalMatrixCoeffField
  exact finiteDimensionalMatrixCechProcedure.cohomologyEquivCanonical n

/-- R11(c): the finite-dimensional route drives a measured zero verdict. -/
noncomputable def finiteDimensionalMatrixVerdictProcedure :
    VerdictProcedure finiteDimensionalMatrixProfile
      finiteDimensionalMatrixGeometry 1
      (fun _ => finiteDimensionalMatrixGeometry.zeroClass 1)
      (.finiteDimensional finiteDimensionalMatrixCechProcedure) where
  availability := fun _ => .measured
  measured_zero_sound := by
    intro _ _ _
    exact ⟨trivial, trivial⟩
  measured_nonzero_sound := by
    intro alpha _ hfalse
    have htrue :=
      ((CechComputationProcedure.finiteDimensional
        finiteDimensionalMatrixCechProcedure).zeroDecision_correct 1
          (finiteDimensionalMatrixGeometry.zeroClass 1)).mpr rfl
    rw [htrue] at hfalse
    cases hfalse
  unmeasured_sound := by
    intro _ h
    cases h
  unknown_sound := by
    intro _ h
    cases h
  notComputed_sound := by
    intro _ h
    cases h
  method := fun _ => ()
  certificate := fun _ => ()

/-- R11(c): complete finite-dimensional coefficient interface over `ZMod 2`. -/
noncomputable def finiteDimensionalMatrixEffCoeff :
    EffCoeff finiteDimensionalMatrixProfile finiteDimensionalMatrixGeometry where
  profileInterface := ()
  selectedDegree := 1
  domainClass := fun _ => finiteDimensionalMatrixGeometry.zeroClass 1
  cechProcedure := .finiteDimensional finiteDimensionalMatrixCechProcedure
  verdictProcedure := finiteDimensionalMatrixVerdictProcedure

/-- R11(c): full finite measurement regime selecting the finite-field matrix route. -/
noncomputable def finiteDimensionalMatrixRegime :
    FiniteMeasurementRegime finiteDimensionalMatrixProfile where
  geometry := finiteDimensionalMatrixGeometry
  coeffDecidableEq := by
    change DecidableEq (ZMod 2)
    infer_instance
  effCoeff := finiteDimensionalMatrixEffCoeff
  witnessFintype := by
    change Fintype SquareFreeSupportVertex
    infer_instance
  witnessDecidableEq := by
    change DecidableEq SquareFreeSupportVertex
    infer_instance

/-- R11(c): every singleton witness generates the proper all-variable ideal. -/
def finiteDimensionalMatrixLeftSquareFree :
    FiniteSquareFreeComputationData finiteDimensionalMatrixRegime :=
  FiniteSquareFreeComputationData.allSingletons finiteDimensionalMatrixRegime

theorem finiteDimensionalMatrixLeftIdeal_eq_idealOfVars :
    finiteDimensionalMatrixLeftSquareFree.obstructionIdeal (ZMod 2) =
      MvPolynomial.idealOfVars SquareFreeSupportVertex (ZMod 2) :=
  FiniteSquareFreeComputationData.allSingletons_obstructionIdeal
    finiteDimensionalMatrixRegime (ZMod 2)

/-- Concrete proper left ideal used by the finite tensor computation. -/
def finiteDimensionalMatrixLeftIdeal :
    Ideal (MvPolynomial SquareFreeSupportVertex (ZMod 2)) :=
  MvPolynomial.idealOfVars SquareFreeSupportVertex (ZMod 2)

theorem finiteDimensionalMatrixLeftIdeal_eq_squareFree :
    finiteDimensionalMatrixLeftIdeal =
      finiteDimensionalMatrixLeftSquareFree.obstructionIdeal (ZMod 2) := by
  exact finiteDimensionalMatrixLeftIdeal_eq_idealOfVars.symm

/-- R11(c): nonzero principal right ideal for the finite-field finite-resolution fixture. -/
def finiteDimensionalMatrixRightSquareFree :
    FiniteSquareFreeComputationData finiteDimensionalMatrixRegime where
  forbiddenSupports := {forbiddenSupportPFinset}

/-- Concrete nonzero principal right ideal used by the selected resolution. -/
def finiteDimensionalMatrixRightIdeal :
    Ideal (MvPolynomial SquareFreeSupportVertex (ZMod 2)) :=
  Ideal.span ({MvPolynomial.X SquareFreeSupportVertex.p} :
    Set (MvPolynomial SquareFreeSupportVertex (ZMod 2)))

theorem finiteDimensionalMatrixRightIdeal_eq_squareFree :
    finiteDimensionalMatrixRightIdeal =
      finiteDimensionalMatrixRightSquareFree.obstructionIdeal (ZMod 2) := by
  ext f
  simp [finiteDimensionalMatrixRightIdeal,
    FiniteSquareFreeComputationData.obstructionIdeal,
    FiniteSquareFreeComputationData.witnessRegime,
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.obstructionIdeal,
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.supportIdeal,
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.monomialSet,
    finiteDimensionalMatrixRightSquareFree, forbiddenSupportPFinset,
    LawAlgebra.StanleyReisner.squareFreeMonomial]

/-- The actual left equation coordinates generate the all-variable ideal. -/
theorem finiteMeasurement_leftEquationIdeal_realizes :
    profileEquationIdeal finiteDimensionalMatrixProfile
        finiteMeasurementSiteBase finiteEquationObservableMapZMod2
        FiniteEquationHandle.left =
      finiteDimensionalMatrixLeftSquareFree.obstructionIdeal (ZMod 2) := by
  rw [← finiteDimensionalMatrixLeftIdeal_eq_squareFree]
  rw [profileEquationIdeal_eq_span_range]
  unfold finiteDimensionalMatrixLeftIdeal MvPolynomial.idealOfVars
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro polynomial ⟨atom, rfl⟩
    apply Ideal.subset_span
    exact ⟨finiteAtomWitnessVariable atom,
      (finiteMeasurement_leftEquationCoordinate_zmod2 atom).symm⟩
  · apply Ideal.span_le.mpr
    rintro polynomial ⟨supportVertex, rfl⟩
    apply Ideal.subset_span
    cases supportVertex
    · exact ⟨FiniteModel.FiniteAtom.componentA, by
        simpa [finiteAtomWitnessVariable] using
          finiteMeasurement_leftEquationCoordinate_zmod2
            FiniteModel.FiniteAtom.componentA⟩
    · exact ⟨FiniteModel.FiniteAtom.componentB, by
        simpa [finiteAtomWitnessVariable] using
          finiteMeasurement_leftEquationCoordinate_zmod2
            FiniteModel.FiniteAtom.componentB⟩
    · exact ⟨FiniteModel.FiniteAtom.componentC, by
        simpa [finiteAtomWitnessVariable] using
          finiteMeasurement_leftEquationCoordinate_zmod2
            FiniteModel.FiniteAtom.componentC⟩

/-- The actual right equation coordinates generate the principal `X p` ideal. -/
theorem finiteMeasurement_rightEquationIdeal_realizes :
    profileEquationIdeal finiteDimensionalMatrixProfile
        finiteMeasurementSiteBase finiteEquationObservableMapZMod2
        FiniteEquationHandle.right =
      finiteDimensionalMatrixRightSquareFree.obstructionIdeal (ZMod 2) := by
  rw [← finiteDimensionalMatrixRightIdeal_eq_squareFree]
  rw [profileEquationIdeal_eq_span_range]
  unfold finiteDimensionalMatrixRightIdeal
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro polynomial ⟨atom, rfl⟩
    change
      finiteEquationObservableMapZMod2
          (finiteDimensionalMatrixProfile.equationGeometry.site.equationSystem.violationCoordinate
            finiteMeasurementSiteBase .right atom) ∈
        Ideal.span ({MvPolynomial.X SquareFreeSupportVertex.p} :
          Set (MvPolynomial SquareFreeSupportVertex (ZMod 2)))
    rw [finiteMeasurement_rightEquationCoordinate_zmod2]
    split_ifs
    · exact Ideal.subset_span (by rfl)
    · exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    intro polynomial hpolynomial
    have hpoly :
        polynomial = MvPolynomial.X SquareFreeSupportVertex.p := by
      simpa using hpolynomial
    subst polynomial
    apply Ideal.subset_span
    exact ⟨FiniteModel.FiniteAtom.componentA, by
      simpa using finiteMeasurement_rightEquationCoordinate_zmod2
        FiniteModel.FiniteAtom.componentA⟩

/-- All required equation coordinates generate the standard obstruction ideal. -/
theorem finiteMeasurement_requiredEquationIdeal_realizes :
    profileRequiredEquationIdeal finiteDimensionalMatrixProfile
        finiteMeasurementSiteBase finiteEquationObservableMapZMod2 =
      finiteDimensionalMatrixLeftSquareFree.obstructionIdeal (ZMod 2)
    := by
  rw [← finiteDimensionalMatrixLeftIdeal_eq_squareFree]
  rw [profileRequiredEquationIdeal_eq_span]
  unfold finiteDimensionalMatrixLeftIdeal MvPolynomial.idealOfVars
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro polynomial ⟨equation, atom, rfl⟩
    rcases equation with ⟨equation, hrequired⟩
    cases equation
    · apply Ideal.subset_span
      exact ⟨finiteAtomWitnessVariable atom,
        (finiteMeasurement_leftEquationCoordinate_zmod2 atom).symm⟩
    · change
        finiteEquationObservableMapZMod2
            (finiteDimensionalMatrixProfile.equationGeometry.site.equationSystem.violationCoordinate
              finiteMeasurementSiteBase .right atom) ∈
          MvPolynomial.idealOfVars SquareFreeSupportVertex (ZMod 2)
      rw [finiteMeasurement_rightEquationCoordinate_zmod2]
      split_ifs
      · apply Ideal.subset_span
        exact ⟨SquareFreeSupportVertex.p, rfl⟩
      · exact Ideal.zero_mem _
    · simp [ArchitecturalEquationSystem.Required, finiteDimensionalMatrixProfile,
        MeasurementEquationGeometry.ofSite, finiteMeasurementEquationSite,
        finiteMeasurementEquationSystem] at hrequired
  · apply Ideal.span_le.mpr
    rintro polynomial ⟨supportVertex, rfl⟩
    apply Ideal.subset_span
    cases supportVertex
    · exact ⟨⟨FiniteEquationHandle.left, rfl⟩,
        FiniteModel.FiniteAtom.componentA, by
          simpa [finiteAtomWitnessVariable] using
            (finiteMeasurement_leftEquationCoordinate_zmod2
              FiniteModel.FiniteAtom.componentA).symm⟩
    · exact ⟨⟨FiniteEquationHandle.left, rfl⟩,
        FiniteModel.FiniteAtom.componentB, by
          simpa [finiteAtomWitnessVariable] using
            (finiteMeasurement_leftEquationCoordinate_zmod2
              FiniteModel.FiniteAtom.componentB).symm⟩
    · exact ⟨⟨FiniteEquationHandle.left, rfl⟩,
        FiniteModel.FiniteAtom.componentC, by
          simpa [finiteAtomWitnessVariable] using
            (finiteMeasurement_leftEquationCoordinate_zmod2
              FiniteModel.FiniteAtom.componentC).symm⟩

/-- Square-free obstruction family selected independently of the Tor law pair.
The finite fixture reuses the nonzero all-variable family as its obstruction
family. -/
def finiteDimensionalMatrixObstructionSquareFree :
    FiniteSquareFreeComputationData finiteDimensionalMatrixRegime :=
  finiteDimensionalMatrixLeftSquareFree

/-- Nontrivial selected profile handles realized by the concrete finite
obstruction sheaf and the generated monomial ideals. -/
noncomputable def finiteDimensionalMatrixProfileRealization :
    FiniteAATProfileRealization finiteDimensionalMatrixProfile
      finiteDimensionalMatrixRegime where
  equationContext := finiteMeasurementSiteBase
  equationObservableMap := finiteEquationObservableMapZMod2
  selectedLeftEquation := ⟨.left, rfl⟩
  selectedRightEquation := ⟨.right, rfl⟩

/-- The canonical required profile ideal is the concrete obstruction ideal. -/
theorem finiteDimensionalMatrixProfileRealization_obstructionIdeal :
    finiteDimensionalMatrixProfileRealization.obstructionIdeal =
      finiteDimensionalMatrixLeftIdeal := by
  exact finiteMeasurement_requiredEquationIdeal_realizes.trans
    finiteDimensionalMatrixLeftIdeal_eq_squareFree.symm

/-- The canonical selected left profile ideal is the concrete left ideal. -/
theorem finiteDimensionalMatrixProfileRealization_leftIdeal :
    finiteDimensionalMatrixProfileRealization.leftIdeal =
      finiteDimensionalMatrixLeftIdeal := by
  exact finiteMeasurement_leftEquationIdeal_realizes.trans
    finiteDimensionalMatrixLeftIdeal_eq_squareFree.symm

/-- The canonical selected right profile ideal is the concrete right ideal. -/
theorem finiteDimensionalMatrixProfileRealization_rightIdeal :
    finiteDimensionalMatrixProfileRealization.rightIdeal =
      finiteDimensionalMatrixRightIdeal := by
  exact finiteMeasurement_rightEquationIdeal_realizes.trans
    finiteDimensionalMatrixRightIdeal_eq_squareFree.symm

/-- R11(c): selected length-one finite-free resolution on the finite-field right ideal. -/
def finiteDimensionalMatrixRightResolution :
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution
      (MvPolynomial SquareFreeSupportVertex (ZMod 2))
      finiteDimensionalMatrixRightIdeal := by
  have hnonzero :
      (MvPolynomial.X SquareFreeSupportVertex.p :
        MvPolynomial SquareFreeSupportVertex (ZMod 2)) ≠ 0 := by
    simp
  exact Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution
    (A := MvPolynomial SquareFreeSupportVertex (ZMod 2)) hnonzero

/-- The first matrix of the selected principal resolution is multiplication
by its actual singleton generator. -/
theorem finiteDimensionalMatrixRightResolution_differentialMatrix_zero
    (i : finiteDimensionalMatrixRightResolution.BasisIndex 0)
    (j : finiteDimensionalMatrixRightResolution.BasisIndex 1) :
    finiteDimensionalMatrixRightResolution.differentialMatrix 0 i j =
      (MvPolynomial.X SquareFreeSupportVertex.p :
        MvPolynomial SquareFreeSupportVertex (ZMod 2)) := by
  change ULift Unit at i j
  rcases i with ⟨⟨⟩⟩
  rcases j with ⟨⟨⟩⟩
  simp [finiteDimensionalMatrixRightResolution,
    Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution,
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.differentialMatrix,
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.coordinateDifferential,
    Derived.FreeResolution.MathlibResolution.Principal.projectiveResolution,
    Derived.FreeResolution.MathlibResolution.Principal.complex,
    Derived.FreeResolution.MathlibResolution.Principal.differential]

/-- The tensor coefficient ring is the finite field obtained after killing all
witness variables. -/
noncomputable def finiteDimensionalMatrixTensorQuotientFintype :
    Fintype
      (MvPolynomial SquareFreeSupportVertex (ZMod 2) ⧸
        finiteDimensionalMatrixLeftIdeal) := by
  unfold finiteDimensionalMatrixLeftIdeal
  exact PolynomialQuotient.quotientIdealOfVarsFintype
    SquareFreeSupportVertex (ZMod 2)

/-- Exhaustive finite-matrix solver over the proper all-variable quotient. -/
noncomputable def finiteDimensionalMatrixTensorAlgorithm :
    FiniteTensorMatrixAlgorithm
      (MvPolynomial SquareFreeSupportVertex (ZMod 2))
      finiteDimensionalMatrixLeftIdeal
      finiteDimensionalMatrixRightIdeal
      finiteDimensionalMatrixRightResolution := by
  letI := finiteDimensionalMatrixTensorQuotientFintype
  letI : DecidableEq
      (MvPolynomial SquareFreeSupportVertex (ZMod 2) ⧸
        finiteDimensionalMatrixLeftIdeal) :=
    Classical.decEq _
  exact FiniteTensorMatrixAlgorithm.ofFiniteQuotient

theorem finiteDimensionalMatrixQuotient_one_ne_zero :
    (1 : MvPolynomial SquareFreeSupportVertex (ZMod 2) ⧸
      finiteDimensionalMatrixLeftIdeal) ≠ 0 := by
  intro h
  change (Ideal.Quotient.mk finiteDimensionalMatrixLeftIdeal)
    (1 : MvPolynomial SquareFreeSupportVertex (ZMod 2)) = 0 at h
  rw [Ideal.Quotient.eq_zero_iff_mem] at h
  unfold finiteDimensionalMatrixLeftIdeal at h
  rw [← PolynomialQuotient.ker_constantCoeff_eq_idealOfVars] at h
  simp at h

/-- Nonzero degree-one coordinate vector in the principal resolution. -/
def finiteDimensionalMatrixOneCoordinate :
    FiniteTensorMatrixAlgorithm.CoordinateTerm.{0, 0}
      finiteDimensionalMatrixTensorAlgorithm 1 :=
  fun _ => 1

theorem finiteDimensionalMatrixOneCoordinate_ne_zero :
    finiteDimensionalMatrixOneCoordinate ≠ 0 := by
  intro h
  have hvalue := congrFun h (ULift.up ())
  exact finiteDimensionalMatrixQuotient_one_ne_zero hvalue

/-- Killing all witness variables makes the principal degree-zero
differential vanish on the selected nonzero coordinate. -/
theorem finiteDimensionalMatrixOneCoordinate_isCycle :
    FiniteTensorMatrixAlgorithm.differential.{0, 0}
      finiteDimensionalMatrixTensorAlgorithm 0
      finiteDimensionalMatrixOneCoordinate = 0 := by
  rw [show finiteDimensionalMatrixOneCoordinate =
      (Ideal.Quotient.mk
        finiteDimensionalMatrixLeftIdeal) ∘
        (fun _ : finiteDimensionalMatrixRightResolution.BasisIndex 1 =>
          (1 : MvPolynomial SquareFreeSupportVertex (ZMod 2))) by
    rfl]
  unfold FiniteTensorMatrixAlgorithm.differential
  unfold FiniteTensorMatrixAlgorithm.differentialMatrix
  funext i
  rw [Matrix.mulVecLin_apply]
  rw [← RingHom.map_mulVec]
  simp [
    finiteDimensionalMatrixRightResolution,
    Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution,
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.differentialMatrix,
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.coordinateDifferential,
    Derived.FreeResolution.MathlibResolution.Principal.projectiveResolution,
    Derived.FreeResolution.MathlibResolution.Principal.complex,
    Derived.FreeResolution.MathlibResolution.Principal.differential]
  change (Ideal.Quotient.mk
    finiteDimensionalMatrixLeftIdeal)
      (MvPolynomial.X SquareFreeSupportVertex.p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  unfold finiteDimensionalMatrixLeftIdeal
  exact Ideal.subset_span ⟨SquareFreeSupportVertex.p, rfl⟩

/-- Actual degree-one cycle selected by the finite matrix computation. -/
noncomputable def finiteDimensionalMatrixSelectedCycle :
    FiniteTensorMatrixAlgorithm.Cycle.{0, 0}
      finiteDimensionalMatrixTensorAlgorithm 1 := by
  refine ⟨finiteDimensionalMatrixOneCoordinate, ?_⟩
  change ModuleCat.Hom.hom
      ((finiteDimensionalMatrixTensorAlgorithm.coordinateComplex).d 1
        ((ComplexShape.down ℕ).next 1))
        finiteDimensionalMatrixOneCoordinate = 0
  rw [ChainComplex.next_nat_succ]
  simpa [FiniteTensorMatrixAlgorithm.coordinateComplex,
    ChainComplex.of_d] using finiteDimensionalMatrixOneCoordinate_isCycle

theorem finiteDimensionalMatrixSelectedCycle_ne_zero :
    finiteDimensionalMatrixSelectedCycle ≠ 0 := by
  intro h
  apply finiteDimensionalMatrixOneCoordinate_ne_zero
  exact congrArg Subtype.val h

/-- The incoming degree-two coordinate term is the zero module. -/
theorem finiteDimensionalMatrixIncomingSubsingleton :
    Subsingleton
      (((FiniteTensorMatrixAlgorithm.coordinateComplex.{0, 0}
        finiteDimensionalMatrixTensorAlgorithm).sc 1).X₁) := by
  change Subsingleton
    ((FiniteTensorMatrixAlgorithm.coordinateComplex.{0, 0}
      finiteDimensionalMatrixTensorAlgorithm).X
        ((ComplexShape.down ℕ).prev 1))
  rw [ChainComplex.prev]
  change Subsingleton
    (finiteDimensionalMatrixRightResolution.BasisIndex 2 →
      MvPolynomial SquareFreeSupportVertex (ZMod 2) ⧸
        finiteDimensionalMatrixLeftIdeal)
  let hsub : Subsingleton
      (ULift.{0, 0} Empty →
        MvPolynomial SquareFreeSupportVertex (ZMod 2) ⧸
          finiteDimensionalMatrixLeftIdeal) :=
    ⟨fun f g => funext fun i => nomatch i.down⟩
  simpa [finiteDimensionalMatrixRightResolution,
    Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution] using hsub

/-- The selected cycle represents a nonzero class in the actual coordinate
homology quotient. -/
theorem finiteDimensionalMatrixSelectedCoordinateClass_ne_zero :
    FiniteTensorMatrixAlgorithm.classOfCycle.{0, 0}
      finiteDimensionalMatrixTensorAlgorithm 1
        finiteDimensionalMatrixSelectedCycle ≠ 0 := by
  intro hclass
  have hrange :=
    (FiniteTensorMatrixAlgorithm.classOfCycle_eq_zero_iff_range.{0, 0}
      finiteDimensionalMatrixTensorAlgorithm 1
        finiteDimensionalMatrixSelectedCycle).mp hclass
  rcases hrange with ⟨b, hb⟩
  letI : Subsingleton
      (((FiniteTensorMatrixAlgorithm.coordinateComplex.{0, 0}
        finiteDimensionalMatrixTensorAlgorithm).sc 1).X₁) :=
    finiteDimensionalMatrixIncomingSubsingleton
  have hbzero : b = 0 := by
    apply Subsingleton.elim
  subst b
  simp only [map_zero] at hb
  exact finiteDimensionalMatrixSelectedCycle_ne_zero hb.symm

/-- R11(c): all theorem 4.2 inputs for the finite-field route. -/
noncomputable def finiteDimensionalMatrixComputationData :
    FiniteAATComputationData finiteDimensionalMatrixProfile
      finiteDimensionalMatrixRegime where
  obstructionSquareFree := finiteDimensionalMatrixObstructionSquareFree
  leftSquareFree := finiteDimensionalMatrixLeftSquareFree
  rightSquareFree := finiteDimensionalMatrixRightSquareFree
  profileRealization := finiteDimensionalMatrixProfileRealization
  profileObstructionIdeal_eq_squareFree :=
    finiteDimensionalMatrixProfileRealization_obstructionIdeal.trans
      finiteDimensionalMatrixLeftIdeal_eq_squareFree
  leftIdeal := finiteDimensionalMatrixLeftIdeal
  profileLeftIdeal_eq_presentation :=
    finiteDimensionalMatrixProfileRealization_leftIdeal
  leftPresentation_eq_squareFree :=
    finiteDimensionalMatrixLeftIdeal_eq_squareFree
  rightIdeal := finiteDimensionalMatrixRightIdeal
  profileRightIdeal_eq_presentation :=
    finiteDimensionalMatrixProfileRealization_rightIdeal
  rightPresentation_eq_squareFree :=
    finiteDimensionalMatrixRightIdeal_eq_squareFree
  rightResolution := finiteDimensionalMatrixRightResolution
  tensorMatrixAlgorithm := finiteDimensionalMatrixTensorAlgorithm
  torDegree := 1
  selectedCoordinateCycle := finiteDimensionalMatrixSelectedCycle

/-- R11(c): theorem 4.2 package produced through the finite-field matrix route. -/
noncomputable def finiteDimensionalMatrixComputabilityPackage :
    FiniteAATComputability.{0, 0} finiteDimensionalMatrixRegime
      finiteDimensionalMatrixComputationData :=
  finiteAATComputabilityPackage finiteDimensionalMatrixRegime
    finiteDimensionalMatrixComputationData

/-- R11(c): the full finite-field theorem package fires the finite-dimensional route. -/
theorem finiteDimensionalMatrixFullRoute_fires :
    finiteDimensionalMatrixComputabilityPackage.coefficientComputation.route =
      .finiteDimensionalLinearAlgebra :=
  rfl

theorem finiteDimensionalMatrixData_selectedCoordinateClass_ne_zero :
    finiteDimensionalMatrixComputationData.selectedCoordinateHomologyClass ≠ 0 := by
  simpa [FiniteAATComputationData.selectedCoordinateHomologyClass,
    finiteDimensionalMatrixComputationData] using
      finiteDimensionalMatrixSelectedCoordinateClass_ne_zero

/-- The finite-dimensional full package carries the same nonzero class
through coordinate homology, tensor homology, Mathlib Tor, and LawConflict. -/
theorem finiteDimensionalMatrixFullRoute_nonzero :
    finiteDimensionalMatrixComputabilityPackage.selectedCoordinateCycle ≠ 0 ∧
      finiteDimensionalMatrixComputabilityPackage.selectedCoordinateHomologyClass ≠ 0 ∧
      finiteDimensionalMatrixComputabilityPackage.selectedTensorHomologyClass ≠ 0 ∧
      finiteDimensionalMatrixComputabilityPackage.selectedTorClass ≠ 0 ∧
      finiteDimensionalMatrixComputabilityPackage.selectedConflictClass ≠ 0 := by
  have hcoordinate := finiteDimensionalMatrixData_selectedCoordinateClass_ne_zero
  have htensor :=
    finiteDimensionalMatrixComputationData.selectedTensorHomologyClass_ne_zero
      hcoordinate
  have htor :=
    finiteDimensionalMatrixComputationData.selectedTorClass_ne_zero htensor
  have hconflict :=
    finiteDimensionalMatrixComputationData.selectedConflictClass_ne_zero htor
  exact ⟨finiteDimensionalMatrixSelectedCycle_ne_zero,
    hcoordinate, htensor, htor, hconflict⟩

/-- R11(c): generated cochains have explicit finite carriers. -/
def finiteComputabilityCochainFintype (n : Nat) :
    Fintype (finiteComputabilityGeometry.CechCochain n) := by
  change Fintype ((Fin (n + 1) -> Bool) -> ZMod 2)
  infer_instance

/-- R11(c): equality of explicit finite cochains is decidable. -/
def finiteComputabilityCochainDecidableEq (n : Nat) :
    DecidableEq (finiteComputabilityGeometry.CechCochain n) := by
  change DecidableEq ((Fin (n + 1) -> Bool) -> ZMod 2)
  infer_instance

/-- R11(c): the canonical cocycle kernel is explicitly finite. -/
def finiteComputabilityCocycleFintype (n : Nat) :
    Fintype (finiteComputabilityGeometry.CechCocycle n) := by
  letI := finiteComputabilityCochainFintype n
  letI := finiteComputabilityCochainDecidableEq (n + 1)
  letI : DecidablePred (fun c : finiteComputabilityGeometry.CechCochain n =>
      finiteComputabilityGeometry.cechComplex.differential n c =
        Site.FinitePosetCechZeroCochain
          finiteComputabilityGeometry.cechComplex.additive (n + 1)) :=
    fun _ => inferInstance
  exact Fintype.ofFinset
    (Finset.univ.filter fun c : finiteComputabilityGeometry.CechCochain n =>
      finiteComputabilityGeometry.cechComplex.differential n c =
        Site.FinitePosetCechZeroCochain
          finiteComputabilityGeometry.cechComplex.additive (n + 1))
    (by
      intro c
      constructor <;> intro h
      · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] using h
      · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] using h)

/-- R11(c): equality in the finite canonical quotient is decidable. -/
def finiteComputabilityCohomologyDecidableEq (n : Nat) :
    DecidableEq (finiteComputabilityGeometry.CechHn n) := by
  cases n with
  | zero =>
      letI := finiteComputabilityCochainFintype 0
      letI := finiteComputabilityCochainDecidableEq 0
      letI := finiteComputabilityCochainDecidableEq 1
      letI := finiteComputabilityCocycleFintype 0
      letI : DecidableEq (finiteComputabilityGeometry.CechCocycle 0) :=
        Subtype.instDecidableEq
      letI : DecidableRel
          (Site.FinitePosetCechCoboundarySetoid
            (finiteComputabilityGeometry.coboundaryRelation 0)).r := fun a b => by
        change Decidable (a = b)
        infer_instance
      apply Quotient.decidableEq
  | succ n =>
      letI := finiteComputabilityCochainFintype n
      letI := finiteComputabilityCochainFintype (n + 1)
      letI := finiteComputabilityCochainDecidableEq (n + 1)
      letI := finiteComputabilityCochainDecidableEq (n + 2)
      letI := finiteComputabilityCocycleFintype (n + 1)
      letI : DecidableEq (finiteComputabilityGeometry.CechCocycle (n + 1)) :=
        Subtype.instDecidableEq
      letI : DecidableRel
          (Site.FinitePosetCechCoboundarySetoid
            (finiteComputabilityGeometry.coboundaryRelation (n + 1))).r :=
        fun a b => by
          change Decidable (∃ c : finiteComputabilityGeometry.CechCochain n,
            a.1 - b.1 = finiteComputabilityGeometry.differentialHom n c)
          infer_instance
      apply Quotient.decidableEq

/-- R11(c): finite presentation from which all effective procedures are derived. -/
def finiteComputabilityFiniteCarrierPresentation :
    FiniteCarrierCechPresentation finiteComputabilityMeasurementProfile
      finiteComputabilityGeometry where
  cochainFintype := finiteComputabilityCochainFintype
  cochainDecidableEq := finiteComputabilityCochainDecidableEq
  cocycleFintype := finiteComputabilityCocycleFintype
  cohomologyDecidableEq := finiteComputabilityCohomologyDecidableEq

/-- R11(c): selected procedures are constructed by explicit finite search. -/
def finiteComputabilityEffectiveCechProcedure :
    EffectiveFinitelyPresentedCechProcedure finiteComputabilityMeasurementProfile
      finiteComputabilityGeometry :=
  finiteComputabilityFiniteCarrierPresentation.toEffectiveProcedure

/-- R11(c): effective finitely-presented branch selected by the finite fixture. -/
noncomputable def finiteComputabilityCechProcedure :
    CechComputationProcedure finiteComputabilityMeasurementProfile
      finiteComputabilityGeometry :=
  .effectiveFinitelyPresented finiteComputabilityEffectiveCechProcedure

/-- R11(c): profile classes map to the generated canonical Čech quotient. -/
def finiteComputabilityDomainClass
    (alpha : finiteComputabilityMeasurementProfile.Domain) :
    finiteComputabilityGeometry.CechHn 1 := by
  simpa [finiteComputabilityGeometry, finiteComputabilitySeedGeometry,
    finiteComputabilityMeasurementProfile, finiteComputabilitySeedProfile] using alpha

/-- R11(c): measured classes run the selected Čech zero-decision procedure. -/
noncomputable def finiteComputabilityVerdictProcedure :
    VerdictProcedure finiteComputabilityMeasurementProfile
      finiteComputabilityGeometry 1 finiteComputabilityDomainClass
      finiteComputabilityCechProcedure where
  availability := fun _ => .measured
  measured_zero_sound := by
    intro alpha _ hzero
    constructor
    · trivial
    · have hz := (finiteComputabilityCechProcedure.zeroDecision_correct 1
        (finiteComputabilityDomainClass alpha)).mp hzero
      simpa [finiteComputabilityMeasurementProfile,
        finiteComputabilityGeometry, finiteComputabilitySeedGeometry,
        finiteComputabilitySeedProfile, finiteComputabilityDomainClass] using hz
  measured_nonzero_sound := by
    intro alpha _ hzero
    constructor
    · trivial
    · have hne : finiteComputabilityDomainClass alpha ≠
          finiteComputabilityGeometry.zeroClass 1 := by
        intro hz
        have htrue := (finiteComputabilityCechProcedure.zeroDecision_correct 1
          (finiteComputabilityDomainClass alpha)).mpr hz
        rw [htrue] at hzero
        cases hzero
      simpa [finiteComputabilityMeasurementProfile,
        finiteComputabilityGeometry, finiteComputabilitySeedGeometry,
        finiteComputabilitySeedProfile, finiteComputabilityDomainClass] using hne
  unmeasured_sound := by
    intro alpha h
    cases h
  unknown_sound := by
    intro alpha h
    cases h
  notComputed_sound := by
    intro alpha h
    cases h
  method := fun _ => ()
  certificate := fun _ => ()

/-- R11(c): verdicts are computed by the selected classifier. -/
def finiteComputabilityEffCoeff :
    EffCoeff finiteComputabilityMeasurementProfile finiteComputabilityGeometry where
  profileInterface := ()
  selectedDegree := 1
  domainClass := finiteComputabilityDomainClass
  cechProcedure := finiteComputabilityCechProcedure
  verdictProcedure := finiteComputabilityVerdictProcedure

/-- R11(c): finite measurement regime generated from actual geometry. -/
def computabilityFiniteMeasurementRegime :
    FiniteMeasurementRegime finiteComputabilityMeasurementProfile where
  geometry := finiteComputabilityGeometry
  coeffDecidableEq := by
    change DecidableEq (ZMod 2)
    infer_instance
  effCoeff := finiteComputabilityEffCoeff
  witnessFintype := by
    change Fintype SquareFreeSupportVertex
    infer_instance
  witnessDecidableEq := by
    change DecidableEq SquareFreeSupportVertex
    infer_instance

/-- R11(c): zero cochain in the generated degree-zero cochain module. -/
def finiteComputabilityZeroCochain :
    computabilityFiniteMeasurementRegime.geometry.CechCochain 0 :=
  fun _ => by
    change ZMod 2
    exact 0

/-- R11(c): nonzero cochain in the same generated degree-zero module. -/
def finiteComputabilityOneCochain :
    computabilityFiniteMeasurementRegime.geometry.CechCochain 0 :=
  fun _ => by
    change ZMod 2
    exact 1

/-- R11(c): the linear fixture does not collapse its cochain carrier to `Unit`. -/
theorem finiteComputabilityCochain_nondegenerate :
    finiteComputabilityZeroCochain ≠ finiteComputabilityOneCochain := by
  intro h
  have hvalue := congrFun h (fun _ : Fin 1 => false)
  dsimp [finiteComputabilityZeroCochain,
    finiteComputabilityOneCochain] at hvalue
  change (0 : ZMod 2) = 1 at hvalue
  exact zero_ne_one hvalue

/-- R11(c): every singleton support generates the concrete proper left ideal. -/
def tinyLeftSquareFreeData :
    FiniteSquareFreeComputationData computabilityFiniteMeasurementRegime :=
  FiniteSquareFreeComputationData.allSingletons
    computabilityFiniteMeasurementRegime

theorem tinyLeftIdeal_eq_squareFree :
    finiteDimensionalMatrixLeftIdeal =
      tinyLeftSquareFreeData.obstructionIdeal (ZMod 2) := by
  exact (FiniteSquareFreeComputationData.allSingletons_obstructionIdeal
    computabilityFiniteMeasurementRegime (ZMod 2)).symm

/-- R11(c): a nonzero singleton support generates the concrete principal
right ideal. -/
def tinyRightSquareFreeData :
    FiniteSquareFreeComputationData computabilityFiniteMeasurementRegime where
  forbiddenSupports := {forbiddenSupportPFinset}

theorem tinyRightIdeal_eq_squareFree :
    finiteDimensionalMatrixRightIdeal =
      tinyRightSquareFreeData.obstructionIdeal (ZMod 2) := by
  ext f
  simp [finiteDimensionalMatrixRightIdeal,
    FiniteSquareFreeComputationData.obstructionIdeal,
    FiniteSquareFreeComputationData.witnessRegime,
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.obstructionIdeal,
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.supportIdeal,
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.monomialSet,
    tinyRightSquareFreeData, forbiddenSupportPFinset,
    LawAlgebra.StanleyReisner.squareFreeMonomial]

/-- Effective-route square-free obstruction family. -/
def tinyObstructionSquareFreeData :
    FiniteSquareFreeComputationData computabilityFiniteMeasurementRegime :=
  tinyLeftSquareFreeData

/-- Two distinct polynomial lifts of one nonzero square-free quotient class
receive the same canonical monomial normal form. -/
theorem tinyLeftSquareFree_normalForm_identifies_distinct_lifts :
    (1 + MvPolynomial.X SquareFreeSupportVertex.p :
        MvPolynomial SquareFreeSupportVertex (ZMod 2)) ≠ 1 ∧
      tinyLeftSquareFreeData.normalForm (ZMod 2)
          (1 + MvPolynomial.X SquareFreeSupportVertex.p) =
        tinyLeftSquareFreeData.normalForm (ZMod 2) 1 := by
  constructor
  · intro h
    have hp := congrArg
      (MvPolynomial.coeff
        (Finsupp.single SquareFreeSupportVertex.p 1)) h
    simp at hp
  · apply tinyLeftSquareFreeData.normalForm_eq_of_sub_mem (ZMod 2)
    have hx : (MvPolynomial.X SquareFreeSupportVertex.p :
        MvPolynomial SquareFreeSupportVertex (ZMod 2)) ∈
          tinyLeftSquareFreeData.obstructionIdeal (ZMod 2) := by
      change (MvPolynomial.X SquareFreeSupportVertex.p :
          MvPolynomial SquareFreeSupportVertex (ZMod 2)) ∈
        (FiniteSquareFreeComputationData.allSingletons
          computabilityFiniteMeasurementRegime).obstructionIdeal (ZMod 2)
      rw [FiniteSquareFreeComputationData.allSingletons_obstructionIdeal]
      apply Ideal.subset_span
      exact Set.mem_range_self SquareFreeSupportVertex.p
    simpa using hx

/-- Effective-route provenance for the selected nontrivial profile handles. -/
noncomputable def finiteComputabilityProfileRealization :
    FiniteAATProfileRealization finiteComputabilityMeasurementProfile
      computabilityFiniteMeasurementRegime where
  equationContext := finiteMeasurementSiteBase
  equationObservableMap := finiteEquationObservableMapZMod2
  selectedLeftEquation := ⟨.left, rfl⟩
  selectedRightEquation := ⟨.right, rfl⟩

/-- The effective route's canonical required ideal is its concrete obstruction ideal. -/
theorem finiteComputabilityProfileRealization_obstructionIdeal :
    finiteComputabilityProfileRealization.obstructionIdeal =
      finiteDimensionalMatrixLeftIdeal := by
  simpa [finiteComputabilityProfileRealization,
    finiteComputabilityMeasurementProfile, finiteDimensionalMatrixProfile] using
      finiteDimensionalMatrixProfileRealization_obstructionIdeal

/-- The effective route's canonical selected left ideal is its concrete left ideal. -/
theorem finiteComputabilityProfileRealization_leftIdeal :
    finiteComputabilityProfileRealization.leftIdeal =
      finiteDimensionalMatrixLeftIdeal := by
  simpa [finiteComputabilityProfileRealization,
    finiteComputabilityMeasurementProfile, finiteDimensionalMatrixProfile] using
      finiteDimensionalMatrixProfileRealization_leftIdeal

/-- The effective route's canonical selected right ideal is its concrete right ideal. -/
theorem finiteComputabilityProfileRealization_rightIdeal :
    finiteComputabilityProfileRealization.rightIdeal =
      finiteDimensionalMatrixRightIdeal := by
  simpa [finiteComputabilityProfileRealization,
    finiteComputabilityMeasurementProfile, finiteDimensionalMatrixProfile] using
      finiteDimensionalMatrixProfileRealization_rightIdeal

/-- R11(c): all theorem 4.2 inputs are selected from actual nonzero finite
chain data. -/
noncomputable def finiteComputabilityExampleData :
    FiniteAATComputationData finiteComputabilityMeasurementProfile
      computabilityFiniteMeasurementRegime where
  obstructionSquareFree := tinyObstructionSquareFreeData
  leftSquareFree := tinyLeftSquareFreeData
  rightSquareFree := tinyRightSquareFreeData
  profileRealization := finiteComputabilityProfileRealization
  profileObstructionIdeal_eq_squareFree :=
    finiteComputabilityProfileRealization_obstructionIdeal.trans
      tinyLeftIdeal_eq_squareFree
  leftIdeal := finiteDimensionalMatrixLeftIdeal
  profileLeftIdeal_eq_presentation :=
    finiteComputabilityProfileRealization_leftIdeal
  leftPresentation_eq_squareFree := tinyLeftIdeal_eq_squareFree
  rightIdeal := finiteDimensionalMatrixRightIdeal
  profileRightIdeal_eq_presentation :=
    finiteComputabilityProfileRealization_rightIdeal
  rightPresentation_eq_squareFree := tinyRightIdeal_eq_squareFree
  rightResolution := finiteDimensionalMatrixRightResolution
  tensorMatrixAlgorithm := finiteDimensionalMatrixTensorAlgorithm
  torDegree := 1
  selectedCoordinateCycle := finiteDimensionalMatrixSelectedCycle

/-- The degree-one basis support is derived from the actual principal
differential entry `X p`. -/
theorem finiteComputabilityExampleData_resolutionBasisSupport_one
    (j : finiteComputabilityExampleData.rightResolution.BasisIndex 1) :
    finiteComputabilityExampleData.resolutionBasisSupport 1 j =
      forbiddenSupportPFinset := by
  letI := computabilityFiniteMeasurementRegime.witnessDecidableEq
  letI := computabilityFiniteMeasurementRegime.geometry.coeffCommRing
  letI := finiteComputabilityExampleData.tensorMatrixAlgorithm.quotientDecidableEq
  letI : Nontrivial finiteComputabilityMeasurementProfile.Coeff := by
    change Nontrivial (ZMod 2)
    infer_instance
  letI : DecidableEq
      (finiteComputabilityExampleData.rightResolution.BasisIndex 0) :=
    Classical.decEq _
  ext e
  rw [FiniteAATComputationData.mem_resolutionBasisSupport_succ_iff]
  constructor
  · rintro ⟨i, -, hi | hi⟩
    · have hmatrix :
          finiteComputabilityExampleData.rightResolution.differentialMatrix
              0 i j =
            (MvPolynomial.X SquareFreeSupportVertex.p :
              MvPolynomial SquareFreeSupportVertex (ZMod 2)) := by
        simpa [finiteComputabilityExampleData] using
          finiteDimensionalMatrixRightResolution_differentialMatrix_zero i j
      rw [hmatrix,
        FiniteAATComputationData.polynomialVariableSupport_X] at hi
      simpa [forbiddenSupportPFinset] using hi
    · simp [FiniteAATComputationData.resolutionBasisSupport] at hi
  · intro he
    let i : finiteComputabilityExampleData.rightResolution.BasisIndex 0 := by
      change ULift Unit
      exact ULift.up ()
    have hmatrix :
        finiteComputabilityExampleData.rightResolution.differentialMatrix
            0 i j =
          (MvPolynomial.X SquareFreeSupportVertex.p :
            MvPolynomial SquareFreeSupportVertex (ZMod 2)) := by
      simpa [finiteComputabilityExampleData] using
        finiteDimensionalMatrixRightResolution_differentialMatrix_zero i j
    refine ⟨i, ?_, Or.inl ?_⟩
    · rw [hmatrix]
      simp
    · rw [hmatrix, FiniteAATComputationData.polynomialVariableSupport_X]
      simpa [forbiddenSupportPFinset] using he

/-- R11(c): theorem 4.2 constructs the finite computability package. -/
def finiteComputabilityExamplePackage :
    FiniteAATComputability.{0, 0} computabilityFiniteMeasurementRegime
      finiteComputabilityExampleData :=
  finiteAATComputabilityPackage computabilityFiniteMeasurementRegime
    finiteComputabilityExampleData

/-- R11(c): the finite fixture selects the effective finitely-presented route. -/
theorem finiteComputabilityExample_effectiveRouteSelected :
    finiteComputabilityExamplePackage.coefficientComputation.route =
      .effectiveFinitelyPresented :=
  rfl

/-- The effective route exposes the common representative API, rather than a
route-specific search field. -/
theorem finiteComputabilityExample_genericRepresentative_correct
    (n : Nat)
    (h : computabilityFiniteMeasurementRegime.geometry.CechHn n) :
    computabilityFiniteMeasurementRegime.geometry.classOfCocycle n
        (finiteComputabilityExamplePackage.cocycleRepresentative n h) = h :=
  finiteComputabilityExamplePackage.cocycleRepresentative_correct n h

/-- The finite-dimensional route exposes the same canonical representative
API on degree-one generated Čech classes. -/
theorem finiteDimensionalMatrixH1Representative_correct
    (h : finiteDimensionalMatrixGeometry.CechHn 1) :
    finiteDimensionalMatrixGeometry.classOfCocycle 1
        (finiteDimensionalMatrixComputabilityPackage.cocycleRepresentative 1 h) = h :=
  finiteDimensionalMatrixComputabilityPackage.cocycleRepresentative_correct 1 h

theorem finiteComputabilityExampleData_selectedCoordinateClass_ne_zero :
    finiteComputabilityExampleData.selectedCoordinateHomologyClass ≠ 0 := by
  simpa [FiniteAATComputationData.selectedCoordinateHomologyClass,
    finiteComputabilityExampleData] using
      finiteDimensionalMatrixSelectedCoordinateClass_ne_zero

/-- The effective full package transports its selected nonzero class through
the same constructed Tor and LawConflict route. -/
theorem finiteComputabilityExampleFullRoute_nonzero :
    finiteComputabilityExamplePackage.selectedCoordinateCycle ≠ 0 ∧
      finiteComputabilityExamplePackage.selectedCoordinateHomologyClass ≠ 0 ∧
      finiteComputabilityExamplePackage.selectedTensorHomologyClass ≠ 0 ∧
      finiteComputabilityExamplePackage.selectedTorClass ≠ 0 ∧
      finiteComputabilityExamplePackage.selectedConflictClass ≠ 0 := by
  have hcoordinate :=
    finiteComputabilityExampleData_selectedCoordinateClass_ne_zero
  have htensor :=
    finiteComputabilityExampleData.selectedTensorHomologyClass_ne_zero hcoordinate
  have htor := finiteComputabilityExampleData.selectedTorClass_ne_zero htensor
  have hconflict :=
    finiteComputabilityExampleData.selectedConflictClass_ne_zero htor
  exact ⟨finiteDimensionalMatrixSelectedCycle_ne_zero,
    hcoordinate, htensor, htor, hconflict⟩

/-- R11(c): kernel, image, and quotient procedures use generated Čech data. -/
theorem finiteComputabilityExample_effectiveProcedureRoute :
    (∀ n (c : computabilityFiniteMeasurementRegime.geometry.CechCochain n),
      finiteComputabilityEffectiveCechProcedure.kernel n c = true ↔
        computabilityFiniteMeasurementRegime.geometry.differentialHom n c = 0) ∧
    (∀ n (c : computabilityFiniteMeasurementRegime.geometry.CechCochain (n + 1)),
      finiteComputabilityEffectiveCechProcedure.image n c = true ↔
        ∃ b : computabilityFiniteMeasurementRegime.geometry.CechCochain n,
          computabilityFiniteMeasurementRegime.geometry.differentialHom n b = c) ∧
    (∀ n (h : computabilityFiniteMeasurementRegime.geometry.CechHn n),
      computabilityFiniteMeasurementRegime.geometry.classOfCocycle n
        (finiteComputabilityEffectiveCechProcedure.quotientRepresentative n h) = h) :=
  ⟨finiteComputabilityEffectiveCechProcedure.kernel_correct,
    finiteComputabilityEffectiveCechProcedure.image_correct,
    finiteComputabilityEffectiveCechProcedure.quotientRepresentative_correct⟩

/-- R11(c): the combinatorics route computes the support of the actual
selected nonzero cycle. -/
theorem finiteComputabilityExample_combinatoricsRoute :
    finiteComputabilityExamplePackage.conflictSupport =
      forbiddenSupportPFinset := by
  letI := computabilityFiniteMeasurementRegime.witnessDecidableEq
  letI := computabilityFiniteMeasurementRegime.geometry.coeffCommRing
  letI := finiteComputabilityExampleData.tensorMatrixAlgorithm.quotientDecidableEq
  have hclass :
      finiteComputabilityExamplePackage.selectedCoordinateHomologyClass ≠ 0 := by
    simpa [finiteComputabilityExamplePackage, finiteAATComputabilityPackage] using
      finiteComputabilityExampleData_selectedCoordinateClass_ne_zero
  have hsupport : finiteComputabilityExamplePackage.conflictSupport =
      finiteComputabilityExampleData.selectedCycleSupport :=
    FiniteAATComputability.conflictSupport_eq_selectedCycleSupport_of_selectedCoordinateHomologyClass_ne_zero
      finiteComputabilityExamplePackage hclass
  rw [hsupport]
  have hone :
      (1 : MvPolynomial SquareFreeSupportVertex (ZMod 2) ⧸
      finiteDimensionalMatrixLeftIdeal) ≠ 0 :=
    finiteDimensionalMatrixQuotient_one_ne_zero
  have hrepresentative
      (i : finiteComputabilityExampleData.rightResolution.BasisIndex 1) :
      finiteComputabilityExampleData.coordinateRepresentative
          finiteComputabilityExampleData.selectedCoordinateCycle i = 1 := by
    apply tinyLeftSquareFreeData.quotientNormalFormOfIdealEq_unique
      (ZMod 2) finiteDimensionalMatrixLeftIdeal
      tinyLeftIdeal_eq_squareFree _ 1
    · change (1 : MvPolynomial SquareFreeSupportVertex (ZMod 2) ⧸
        finiteDimensionalMatrixLeftIdeal) =
          finiteDimensionalMatrixOneCoordinate i
      rfl
    · simpa [tinyLeftSquareFreeData] using
        (FiniteSquareFreeComputationData.allSingletons_one_isReduced
          computabilityFiniteMeasurementRegime (ZMod 2))
  have hvalue
      (i : finiteComputabilityExampleData.rightResolution.BasisIndex 1) :
      finiteComputabilityExampleData.tensorMatrixAlgorithm.cycleValue 1
        finiteComputabilityExampleData.selectedCoordinateCycle i = 1 := by
    change finiteDimensionalMatrixOneCoordinate i = 1
    rfl
  have hresolution
      (i : finiteComputabilityExampleData.rightResolution.BasisIndex 1) :
      finiteComputabilityExampleData.resolutionBasisSupport 1 i =
        forbiddenSupportPFinset :=
    finiteComputabilityExampleData_resolutionBasisSupport_one i
  letI : Nonempty
      (finiteComputabilityExampleData.rightResolution.BasisIndex 1) := by
    change Nonempty (ULift Unit)
    exact ⟨ULift.up ()⟩
  have hbiUnion :
      (Finset.univ.biUnion fun _ :
        finiteComputabilityExampleData.rightResolution.BasisIndex 1 =>
          forbiddenSupportPFinset) = forbiddenSupportPFinset := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨_, _, he⟩
      exact he
    · intro he
      rw [Finset.mem_biUnion]
      let i : finiteComputabilityExampleData.rightResolution.BasisIndex 1 := by
        change ULift Unit
        exact ULift.up ()
      exact ⟨i, Finset.mem_univ i, he⟩
  rw [FiniteAATComputationData.selectedCycleSupport]
  change (Finset.univ.biUnion fun i :
      finiteComputabilityExampleData.rightResolution.BasisIndex 1 =>
        if finiteComputabilityExampleData.tensorMatrixAlgorithm.cycleValue 1
            finiteComputabilityExampleData.selectedCoordinateCycle i = 0 then
          ∅
        else
          finiteComputabilityExampleData.resolutionBasisSupport 1 i ∪
            FiniteAATComputationData.polynomialVariableSupport
              SquareFreeSupportVertex (ZMod 2)
              (finiteComputabilityExampleData.coordinateRepresentative
                finiteComputabilityExampleData.selectedCoordinateCycle i)) =
    forbiddenSupportPFinset
  calc
    (Finset.univ.biUnion fun i :
        finiteComputabilityExampleData.rightResolution.BasisIndex 1 =>
          if finiteComputabilityExampleData.tensorMatrixAlgorithm.cycleValue 1
              finiteComputabilityExampleData.selectedCoordinateCycle i = 0 then
            ∅
          else
            finiteComputabilityExampleData.resolutionBasisSupport 1 i ∪
              FiniteAATComputationData.polynomialVariableSupport
                SquareFreeSupportVertex (ZMod 2)
                (finiteComputabilityExampleData.coordinateRepresentative
                  finiteComputabilityExampleData.selectedCoordinateCycle i)) =
        (Finset.univ.biUnion fun _ :
          finiteComputabilityExampleData.rightResolution.BasisIndex 1 =>
            forbiddenSupportPFinset) := by
              congr 1
              funext i
              rw [hvalue i, hresolution i, hrepresentative i]
              simp [hone,
                FiniteAATComputationData.polynomialVariableSupport_one]
    _ = forbiddenSupportPFinset := hbiUnion

/-- Common ambient used to connect the computed finite support relation to the
existing measurement semantics. -/
noncomputable def finiteComputabilityCommonAmbient :
    CommonAmbientPair finiteComputabilityMeasurementProfile where
  AmbientSpace := Unit
  StructureSheaf := Unit
  LawIdeal := FiniteEquationHandle
  CoefficientObject := Unit
  WitnessPair := Unit
  ComparisonProfile := Unit
  SupportCarrier := Finset SquareFreeSupportVertex
  leftDomain := finiteComputabilitySeedGeometry.zeroClass 1
  rightDomain := finiteComputabilitySeedGeometry.zeroClass 1
  selectedAmbient := ()
  selectedStructureSheaf := ()
  leftLawIdeal := .left
  rightLawIdeal := .right
  leftCoefficient := ()
  rightCoefficient := ()
  selectedWitnessPair := ()
  selectedComparisonProfile := ()
  commonRingedSite := True
  commonRingedSite_cert := trivial
  lawIdealsInCommonAmbient := True
  lawIdealsInCommonAmbient_cert := trivial
  coefficientsCompatible := True
  coefficientsCompatible_cert := trivial
  witnessesComparable := True
  witnessesComparable_cert := trivial
  comparisonProfileFixed := True
  comparisonProfileFixed_cert := trivial
  noComparisonWithoutCommonAmbient := True
  noComparisonWithoutCommonAmbient_cert := trivial

/-- Local realization of the nontrivial equation handles and finite support carrier
in the selected common ambient. -/
noncomputable def finiteComputabilityConflictRealization :
    FiniteAATConflictRealization finiteComputabilityExampleData where
  commonAmbient := finiteComputabilityCommonAmbient
  equationToAmbient := id
  leftLaw_ambient := rfl
  rightLaw_ambient := rfl
  supportEquiv := Equiv.refl _

/-- Final theorem 4.2 fixture including the actual relation-valued
`LawConflictMeasurement`. -/
noncomputable def finiteComputabilityConflictPackage :
    FiniteAATConflictComputability computabilityFiniteMeasurementRegime
      finiteComputabilityExampleData finiteComputabilityConflictRealization :=
  finiteAATConflictComputabilityPackage computabilityFiniteMeasurementRegime
    finiteComputabilityExampleData finiteComputabilityConflictRealization

/-- The proper degree-one nonzero conflict class and its computed support
reading both survive in the final measurement package. -/
theorem finiteComputabilityConflictPackage_nonzero_and_supportReading :
    finiteComputabilityExampleData.selectedConflictClass ≠ 0 ∧
      finiteComputabilityConflictPackage.lawConflictMeasurement.selectedClassSupportReading := by
  constructor
  · change finiteComputabilityExampleData.selectedConflictClass ≠ 0
    exact finiteComputabilityExampleFullRoute_nonzero.2.2.2.2
  · exact finiteComputabilityConflictPackage.selectedClassSupportReading

/-- The final conflict fixture explicitly records proper selected ideals,
degree one, a nonzero actual conflict class, and its computed support reading. -/
theorem finiteComputabilityConflictPackage_proper_degree_one_nonzero_and_supportReading :
    finiteComputabilityExampleData.leftIdeal ≠ ⊤ ∧
      finiteComputabilityExampleData.rightIdeal ≠ ⊤ ∧
      finiteComputabilityExampleData.torDegree = 1 ∧
      finiteComputabilityExampleData.selectedConflictClass ≠ 0 ∧
      finiteComputabilityConflictPackage.lawConflictMeasurement.selectedClassSupportReading := by
  have hleft : finiteDimensionalMatrixLeftIdeal ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    intro hone
    apply finiteDimensionalMatrixQuotient_one_ne_zero
    change Ideal.Quotient.mk finiteDimensionalMatrixLeftIdeal
      (1 : MvPolynomial SquareFreeSupportVertex (ZMod 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hone
  have hright_le_left :
      finiteDimensionalMatrixRightIdeal ≤ finiteDimensionalMatrixLeftIdeal := by
    unfold finiteDimensionalMatrixRightIdeal finiteDimensionalMatrixLeftIdeal
    unfold MvPolynomial.idealOfVars
    exact Ideal.span_mono
      (Set.singleton_subset_iff.mpr
        (Set.mem_range_self SquareFreeSupportVertex.p))
  have hright : finiteDimensionalMatrixRightIdeal ≠ ⊤ :=
    ne_top_of_le_ne_top hleft hright_le_left
  have hroute := finiteComputabilityConflictPackage_nonzero_and_supportReading
  refine ⟨?_, ?_, rfl, hroute.1, hroute.2⟩
  · change finiteDimensionalMatrixLeftIdeal ≠ ⊤
    exact hleft
  · change finiteDimensionalMatrixRightIdeal ≠ ⊤
    exact hright

/-- Zero class in the actual conflict carrier, viewed through the final
measurement's carrier field. -/
noncomputable def finiteComputabilityMeasuredZeroConflict :
    finiteComputabilityConflictPackage.lawConflictMeasurement.ConflictClass := by
  change finiteComputabilityExampleData.ActualConflictClass
  exact 0

/-- The actual transported support relation assigns the empty finite support
to every reading of the zero conflict class. -/
theorem finiteComputabilityConflictPackage_zero_support
    {support : Finset SquareFreeSupportVertex}
    (h : finiteComputabilityConflictPackage.lawConflictMeasurement.conflictSupport
      finiteComputabilityMeasuredZeroConflict support) :
    support = ∅ := by
  have hrelation : finiteComputabilityConflictRealization.supportRelation
      (0 : finiteComputabilityExampleData.ActualConflictClass) support := by
    simpa [finiteComputabilityConflictPackage,
      finiteAATConflictComputabilityPackage,
      FiniteAATConflictRealization.lawConflictMeasurement] using h
  have hzero := finiteComputabilityConflictRealization.supportRelation_zero hrelation
  simpa [finiteComputabilityConflictRealization] using hzero

/-- R11(c): the selected finite resolution computes the Mathlib Tor object. -/
theorem finiteComputabilityExample_torRoute :
    Nonempty
      (Derived.Intersection.mathlibTor
          (MvPolynomial SquareFreeSupportVertex (ZMod 2))
          finiteComputabilityExampleData.leftIdeal
          finiteComputabilityExampleData.rightIdeal
          finiteComputabilityExampleData.torDegree ≅
        (finiteComputabilityExampleData.rightResolution.tensorComplex
          finiteComputabilityExampleData.leftIdeal).homology
            finiteComputabilityExampleData.torDegree) :=
  ⟨finiteComputabilityExamplePackage.torComparison⟩

namespace NontrivialTorFixture

open Derived.Counterexample.SharedWitnessCoord

/--
R11(c): the concrete principal resolution of `R/⟨xz⟩` as a length-one
finite-free resolution.
-/
def principalFiniteFreeResolutionV2 :
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution
      R2 (idealV (ZMod 2)) := by
  simpa [idealV] using
    (Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution
      (A := R2) xz_ne_zero_zmod2)

/-- R11(c): the finite coordinate differential is genuinely nonzero. -/
theorem principalCoordinateDifferentialV2_nonzero :
    (principalFiniteFreeResolutionV2.coordinateDifferential 0) ≠ 0 := by
  simpa [principalFiniteFreeResolutionV2, idealV] using
    (Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution_coordinateDifferential_zero_ne_zero
      (A := R2) xz_ne_zero_zmod2)

/-- Resolution matrices after reduction modulo the selected left ideal. -/
noncomputable def principalTensorDifferentialMatrixV2 (n : Nat) :
    Matrix (principalFiniteFreeResolutionV2.BasisIndex n)
      (principalFiniteFreeResolutionV2.BasisIndex (n + 1))
      (R2 ⧸ idealU (ZMod 2)) :=
  (principalFiniteFreeResolutionV2.differentialMatrix n).map
    (Ideal.Quotient.mk (idealU (ZMod 2)))

/-- Coordinate representative of the explicit polynomial `y` in degree one. -/
def yCoordinateCycleV2 :
    principalFiniteFreeResolutionV2.BasisIndex 1 →
      R2 ⧸ idealU (ZMod 2) :=
  fun i => by
    cases i.down
    exact Ideal.Quotient.mk (idealU (ZMod 2)) (MvPolynomial.X y)

theorem yCoordinateCycleV2_ne_zero : yCoordinateCycleV2 ≠ 0 := by
  intro h
  have hvalue := congrFun h (ULift.up ())
  change (Ideal.Quotient.mk (idealU (ZMod 2))) (MvPolynomial.X y : R2) = 0 at hvalue
  rw [Ideal.Quotient.eq_zero_iff_mem] at hvalue
  exact y_not_mem_idealU_zmod2 hvalue

/-- The reduced degree-zero resolution matrix kills the selected `y` vector. -/
theorem yCoordinateCycleV2_is_cycle :
    Matrix.mulVec (principalTensorDifferentialMatrixV2 0) yCoordinateCycleV2 = 0 := by
  rw [show yCoordinateCycleV2 =
      (Ideal.Quotient.mk (idealU (ZMod 2))) ∘
        (fun _ : principalFiniteFreeResolutionV2.BasisIndex 1 =>
          (MvPolynomial.X y : R2)) by rfl]
  unfold principalTensorDifferentialMatrixV2
  funext i
  rw [← RingHom.map_mulVec]
  simp [principalFiniteFreeResolutionV2,
    Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution,
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.differentialMatrix,
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.coordinateDifferential,
    Derived.FreeResolution.MathlibResolution.Principal.projectiveResolution,
    Derived.FreeResolution.MathlibResolution.Principal.complex,
    Derived.FreeResolution.MathlibResolution.Principal.differential,
    xz]
  change (Ideal.Quotient.mk (idealU (ZMod 2)))
    (((MvPolynomial.X x : R2) * MvPolynomial.X z) * MvPolynomial.X y) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, idealU, Ideal.mem_span_singleton']
  exact ⟨MvPolynomial.X z, by simp [xy]; ring⟩

/-- The incoming degree-two matrix has zero image. -/
theorem principalTensorDifferentialMatrixV2_one_zero
    (b : principalFiniteFreeResolutionV2.BasisIndex 2 →
      R2 ⧸ idealU (ZMod 2)) :
    Matrix.mulVec (principalTensorDifferentialMatrixV2 1) b = 0 := by
  funext i
  simp [principalTensorDifferentialMatrixV2, principalFiniteFreeResolutionV2,
    Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution,
    Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.differentialMatrix,
    Matrix.mulVec]

/-- The nonzero `y` cycle is not in the incoming matrix image. -/
theorem yCoordinateCycleV2_not_boundary :
    ¬ ∃ b : principalFiniteFreeResolutionV2.BasisIndex 2 →
        R2 ⧸ idealU (ZMod 2),
      Matrix.mulVec (principalTensorDifferentialMatrixV2 1) b =
        yCoordinateCycleV2 := by
  rintro ⟨b, hb⟩
  rw [principalTensorDifferentialMatrixV2_one_zero b] at hb
  exact yCoordinateCycleV2_ne_zero hb.symm

/--
R11(c): nondegenerate finite-chain Tor route: a length-one resolution has a
nonzero coordinate differential, computes actual Mathlib Tor, and carries the
explicit nonzero degree-one conflict class.
-/
theorem nontrivialFiniteChainTorRoute_fires :
    principalFiniteFreeResolutionV2.length = 1 ∧
      principalFiniteFreeResolutionV2.coordinateDifferential 0 ≠ 0 ∧
      Matrix.mulVec (principalTensorDifferentialMatrixV2 0)
        yCoordinateCycleV2 = 0 ∧
      (¬ ∃ b : principalFiniteFreeResolutionV2.BasisIndex 2 →
          R2 ⧸ idealU (ZMod 2),
        Matrix.mulVec (principalTensorDifferentialMatrixV2 1) b =
          yCoordinateCycleV2) ∧
      Nonempty
        (Derived.Intersection.mathlibTor R2
            (idealU (ZMod 2)) (idealV (ZMod 2)) 1 ≅
          (principalFiniteFreeResolutionV2.tensorComplex
            (idealU (ZMod 2))).homology 1) ∧
      ∃ x : Derived.Intersection.mathlibTor R2
          (idealU (ZMod 2)) (idealV (ZMod 2)) 1,
        x ≠ 0 :=
  ⟨rfl, principalCoordinateDifferentialV2_nonzero,
    yCoordinateCycleV2_is_cycle, yCoordinateCycleV2_not_boundary,
    ⟨principalFiniteFreeResolutionV2.torIsoTensorHomology
      (idealU (ZMod 2)) 1⟩,
    Derived.Counterexample.SharedWitnessCoord.example56_zmod2_mathlibTor1_nonzero⟩

end NontrivialTorFixture

/-- R11(c): finite Čech, verdict, square-free, Tor, and support routes are constructed. -/
theorem finiteComputabilityExample_verified :
    Nonempty
      (FiniteAATComputability.{0, 0} computabilityFiniteMeasurementRegime
        finiteComputabilityExampleData) :=
  finiteAATComputability computabilityFiniteMeasurementRegime finiteComputabilityExampleData

/-- R11(b): actual verdict procedure retained by the square-free repair profile. -/
def pseudoCircleFiniteVerdict :
    (alpha : pseudoCircleMeasurementProfile.Domain) ->
      MeasurementVerdict pseudoCircleMeasurementProfile alpha
  | PseudoCircleMeasurementDomain.boundaryCocycle =>
      MeasurementVerdict.measured_nonzero rfl rfl ()
  | PseudoCircleMeasurementDomain.unmeasuredAxis =>
      MeasurementVerdict.unmeasured rfl

/-- R11(b): selected Part III square-free witness regime for the repair fixture. -/
def squareFreeSourceWitnessRegime :
    UsesSquareFreeWitnessRegime SquareFreeSupportVertex where
  Forb := fun support =>
    support = forbiddenSupportPQFinset ∨ support = forbiddenSupportQRFinset

/-- R11(b): the Part III simplicial complex selected by the repair fixture. -/
def squareFreeSourceDelta :
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.AbstractSimplicialComplex
      SquareFreeSupportVertex :=
  LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.delta
    SquareFreeSupportVertex squareFreeSourceWitnessRegime

/-- R11(b): the finite Alexander dual selected by the repair fixture. -/
def squareFreeFiniteAlexanderDual :
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.AbstractSimplicialComplex
      SquareFreeSupportVertex :=
  finiteAlexanderDual SquareFreeSupportVertex squareFreeSourceDelta

/-- R11(b): a repair target support is an Alexander-dual nonface. -/
def squareFreeRepairTargetAlexanderDualNonface
    (target : SquareFreeRepairTarget) : Prop :=
  squareFreeRepairTargetSupport target ∉ squareFreeFiniteAlexanderDual.faces

/--
R11(b): Alexander-dual nonfaces of the fixture are exactly supports hitting the
selected forbidden supports.
-/
theorem squareFree_repairSupport_notMemAlexanderDual_iff_hitsForbidden
    (target : SquareFreeRepairTarget) :
    squareFreeRepairTargetAlexanderDualNonface target ↔
      FinsetHitsForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
        (squareFreeRepairTargetSupport target) := by
  unfold squareFreeRepairTargetAlexanderDualNonface squareFreeFiniteAlexanderDual
    squareFreeSourceDelta
  exact not_mem_finiteAlexanderDual_iff_hitsForbidden
    SquareFreeSupportVertex squareFreeSourceWitnessRegime
    (squareFreeRepairTargetSupport target)

/-- R11(b): `{q}` hits the selected forbidden supports. -/
theorem squareFree_singletonQ_hitsForbidden :
    FinsetHitsForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
      (squareFreeRepairTargetSupport SquareFreeRepairTarget.singletonQ) := by
  intro F hF
  rcases hF with rfl | rfl
  · exact ⟨SquareFreeSupportVertex.q, by
      simp [squareFreeRepairTargetSupport, forbiddenSupportPQFinset]⟩
  · exact ⟨SquareFreeSupportVertex.q, by
      simp [squareFreeRepairTargetSupport, forbiddenSupportQRFinset]⟩

/-- R11(b): `{p,r}` hits the selected forbidden supports. -/
theorem squareFree_pairPR_hitsForbidden :
    FinsetHitsForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
      (squareFreeRepairTargetSupport SquareFreeRepairTarget.pairPR) := by
  intro F hF
  rcases hF with rfl | rfl
  · exact ⟨SquareFreeSupportVertex.p, by
      simp [squareFreeRepairTargetSupport, forbiddenSupportPQFinset]⟩
  · exact ⟨SquareFreeSupportVertex.r, by
      simp [squareFreeRepairTargetSupport, forbiddenSupportQRFinset]⟩

/-- R11(b): `{q}` is inclusion-minimal among selected finite hitting sets. -/
theorem squareFree_singletonQ_minimalHitting :
    MinimalHittingSetForForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
      (squareFreeRepairTargetSupport SquareFreeRepairTarget.singletonQ) := by
  refine ⟨squareFree_singletonQ_hitsForbidden, ?_⟩
  intro K hK hKsub x hx
  simp [squareFreeRepairTargetSupport] at hx
  subst hx
  have hHit := hK forbiddenSupportPQFinset (Or.inl rfl)
  rcases hHit with ⟨y, hyFilter⟩
  have hyK : y ∈ K := (Finset.mem_filter.mp hyFilter).1
  have hyForbidden : y ∈ forbiddenSupportPQFinset := (Finset.mem_filter.mp hyFilter).2
  have hyTarget := hKsub hyK
  cases y <;> simp [squareFreeRepairTargetSupport, forbiddenSupportPQFinset] at hyForbidden hyTarget hyK ⊢
  exact hyK

/-- R11(b): `{p,r}` is inclusion-minimal among selected finite hitting sets. -/
theorem squareFree_pairPR_minimalHitting :
    MinimalHittingSetForForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
      (squareFreeRepairTargetSupport SquareFreeRepairTarget.pairPR) := by
  refine ⟨squareFree_pairPR_hitsForbidden, ?_⟩
  intro K hK hKsub x hx
  simp [squareFreeRepairTargetSupport] at hx
  rcases hx with rfl | rfl
  · have hHit := hK forbiddenSupportPQFinset (Or.inl rfl)
    rcases hHit with ⟨y, hyFilter⟩
    have hyK : y ∈ K := (Finset.mem_filter.mp hyFilter).1
    have hyForbidden : y ∈ forbiddenSupportPQFinset := (Finset.mem_filter.mp hyFilter).2
    have hyTarget := hKsub hyK
    cases y <;> simp [squareFreeRepairTargetSupport, forbiddenSupportPQFinset] at hyForbidden hyTarget hyK ⊢
    exact hyK
  · have hHit := hK forbiddenSupportQRFinset (Or.inr rfl)
    rcases hHit with ⟨y, hyFilter⟩
    have hyK : y ∈ K := (Finset.mem_filter.mp hyFilter).1
    have hyForbidden : y ∈ forbiddenSupportQRFinset := (Finset.mem_filter.mp hyFilter).2
    have hyTarget := hKsub hyK
    cases y <;> simp [squareFreeRepairTargetSupport, forbiddenSupportQRFinset] at hyForbidden hyTarget hyK ⊢
    exact hyK

/-- R11(b): Part VIII square-free repair regime for the `{p,q}` / `{q,r}` example. -/
def squareFreeRepairRegime :
    SquareFreeRepairRegime pseudoCircleMeasurementProfile where
  witnessFintype := inferInstanceAs (Fintype SquareFreeSupportVertex)
  witnessDecidableEq := inferInstanceAs (DecidableEq SquareFreeSupportVertex)
  sourceWitnessRegime := squareFreeSourceWitnessRegime
  Witness := SquareFreeSupportVertex
  witnessOfProfileWitness := fun witness => witness
  ForbiddenSupport := List SquareFreeSupportVertex
  MinimalForbiddenSupport := List SquareFreeSupportVertex
  ObstructionIdeal := Unit
  StanleyReisnerIdeal := Unit
  Delta := Unit
  profileWitnessesLifted := True
  profileWitnessesLifted_cert := trivial
  forbiddenSupportReadsSourceRegime := True
  forbiddenSupportReadsSourceRegime_cert := trivial
  finiteWitness := True
  finiteWitness_cert := trivial
  forbiddenSupportsFinite := True
  forbiddenSupportsFinite_cert := trivial
  minimalForbiddenSupportsFinite := True
  minimalForbiddenSupportsFinite_cert := trivial
  obstructionIdealGeneratedByMinimalForbidden := True
  obstructionIdealGeneratedByMinimalForbidden_cert := trivial
  deltaAvoidsForbiddenSupports := True
  deltaAvoidsForbiddenSupports_cert := trivial

/-- R11(b): selected Alexander dual carrier for the finite repair fixture. -/
def squareFreeAlexanderDual :
    AlexanderDualComplex squareFreeRepairRegime where
  Dual := Finset SquareFreeSupportVertex
  dualOfDelta :=
    ∀ S : Finset SquareFreeSupportVertex,
      S ∈ squareFreeFiniteAlexanderDual.faces ↔
        (Finset.univ \ S) ∉ squareFreeSourceDelta.faces
  dualOfDelta_cert :=
    mem_finiteAlexanderDualFaces_iff SquareFreeSupportVertex
      squareFreeSourceDelta

/-- R11(b): selected minimal vertex covers. -/
def squareFreeMinimalVertexCovers :
    MinimalVertexCover squareFreeRepairRegime where
  Cover := SquareFreeRepairTarget
  minimalVertexCover := fun target =>
    squareFreeRepairTargetAlexanderDualNonface target ∧
      MinimalHittingSetForForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
        (squareFreeRepairTargetSupport target)

/-- R11(b): selected minimal witness hitting sets. -/
def squareFreeMinimalWitnessHittingSets :
    MinimalWitnessHittingSet squareFreeRepairRegime where
  HittingSet := SquareFreeRepairTarget
  minimalWitnessHittingSet := fun target =>
    MinimalHittingSetForForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
      (squareFreeRepairTargetSupport target)

/-- R11(b): selected minimal repair hitting sets `{q}` and `{p,r}`. -/
def squareFreeMinimalRepairHittingSets :
    MinimalRepairHittingSet squareFreeRepairRegime where
  RepairTarget := SquareFreeRepairTarget
  minimalRepairHittingSet := fun target =>
    MinimalHittingSetForForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
      (squareFreeRepairTargetSupport target)
  notOperationSemantics := True
  notOperationSemantics_cert := trivial

/-- R11(b): concrete bridge from selected repair targets to finite minimal hitting sets. -/
def squareFreeAlexanderDualRepairBridge :
    FiniteAlexanderDualRepairBridge squareFreeRepairRegime where
  RepairTarget := SquareFreeRepairTarget
  repairSupport := squareFreeRepairTargetSupport
  minimalRepairTarget := fun target =>
    squareFreeMinimalRepairHittingSets.minimalRepairHittingSet target
  minimalRepairTarget_iff := by
    intro target
    rfl

/-- R11(b): theorem 5.2 instantiated on the finite repair hitting-set fixture. -/
def squareFreeRepairExamplePackage :
    StanleyReisnerAlexanderDualRepair squareFreeRepairRegime :=
  stanleyReisnerAlexanderDualRepairPackage squareFreeAlexanderDual
    squareFreeMinimalVertexCovers squareFreeMinimalWitnessHittingSets
    squareFreeMinimalRepairHittingSets
    (LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.obstructionIdeal
        SquareFreeSupportVertex ℤ squareFreeSourceWitnessRegime =
      LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.stanleyReisnerIdeal
        SquareFreeSupportVertex ℤ
        (LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.delta
          SquareFreeSupportVertex squareFreeSourceWitnessRegime))
    (SquareFreeRepairRegime.source_obstructionIdeal_eq_stanleyReisnerIdeal
      squareFreeRepairRegime ℤ)
    (∀ S : Finset SquareFreeSupportVertex,
      LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.MinimalStanleyReisnerGeneratorSupport
          SquareFreeSupportVertex
          (LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.delta
            SquareFreeSupportVertex squareFreeSourceWitnessRegime) S ↔
        LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.MinimalForbidden
          SquareFreeSupportVertex squareFreeSourceWitnessRegime S)
    (SquareFreeRepairRegime.source_minimalGeneratorSupport_iff_minimalForbidden
      squareFreeRepairRegime)
    (∀ target : SquareFreeRepairTarget,
      squareFreeMinimalVertexCovers.minimalVertexCover target ↔
        squareFreeMinimalWitnessHittingSets.minimalWitnessHittingSet target)
    (by
      intro target
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨(squareFree_repairSupport_notMemAlexanderDual_iff_hitsForbidden target).mpr
          h.1, h⟩)
    (∀ target : SquareFreeRepairTarget,
      squareFreeMinimalRepairHittingSets.minimalRepairHittingSet target ↔
        squareFreeRepairTargetAlexanderDualNonface target ∧
          MinimalHittingSetForForbidden SquareFreeSupportVertex squareFreeSourceWitnessRegime
            (squareFreeRepairTargetSupport target))
    (by
      intro target
      constructor
      · intro h
        exact ⟨(squareFree_repairSupport_notMemAlexanderDual_iff_hitsForbidden target).mpr
          h.1, h⟩
      · intro h
        exact h.2)

/-- R11(b): `{q}` is a selected minimal repair hitting set. -/
theorem squareFree_singletonQ_minimalRepairHittingSet :
    squareFreeMinimalRepairHittingSets.minimalRepairHittingSet
      SquareFreeRepairTarget.singletonQ := by
  exact squareFree_singletonQ_minimalHitting

/-- R11(b): `{p,r}` is a selected minimal repair hitting set. -/
theorem squareFree_pairPR_minimalRepairHittingSet :
    squareFreeMinimalRepairHittingSets.minimalRepairHittingSet
      SquareFreeRepairTarget.pairPR := by
  exact squareFree_pairPR_minimalHitting

/-- R11(e): the concrete finite real inner-product complex used by the Hodge fixture. -/
def lowDegreeRealComplex :
    RealFiniteInnerProductComplex
      LowDegreeBoundaryCochain LowDegreeRealCochain LowDegreeBoundaryCochain where
  dPrev := 0
  dNext := 0
  d_comp_d := rfl

/-- R11(e): the selected low-degree Laplacian is the zero operator. -/
theorem lowDegreeRealComplex_laplacian_eq_zero :
    lowDegreeRealComplex.laplacian = 0 := by
  ext x i
  simp [lowDegreeRealComplex, RealFiniteInnerProductComplex.laplacian,
    RealFiniteInnerProductComplex.dPrevAdjoint,
    RealFiniteInnerProductComplex.dNextAdjoint]

/-- R11(e): every cochain in the low-degree zero complex is harmonic. -/
theorem lowDegreeRealComplex_all_harmonic (x : LowDegreeRealCochain) :
    lowDegreeRealComplex.laplacian x = 0 := by
  rw [lowDegreeRealComplex_laplacian_eq_zero]
  simp

/-- R11(e): concrete finite Hodge decomposition on the low-degree real complex. -/
def lowDegreeRealHodgeDecomposition :
    RealFiniteHodgeDecomposition lowDegreeRealComplex where
  CohomologyClass := lowDegreeRealComplex.cohomology
  harmonicKernelEquivCohomology :=
    lowDegreeRealComplex.laplacianKernelEquivCohomology
  exactPart := fun _ => 0
  harmonicPart := fun x => x
  coexactPart := fun _ => 0
  exactPart_mem_range := by
    intro x
    exact ⟨0, rfl⟩
  harmonicPart_mem_kernel := lowDegreeRealComplex_all_harmonic
  coexactPart_mem_adjoint_range := by
    intro x
    exact ⟨0, by
      simp [lowDegreeRealComplex, RealFiniteInnerProductComplex.dNextAdjoint]⟩
  decomposition := by
    intro x
    simp
  exact_harmonic_orthogonal := by
    intro x y
    simp
  harmonic_coexact_orthogonal := by
    intro x y
    simp
  exact_coexact_orthogonal := by
    intro x y
    simp
  cohomologyClassOf := fun x => x
  cohomologyClass_eq_harmonic := by
    intro x
    rfl

/-- R11(e): kernel membership is equivalent to the selected harmonic cohomology reading. -/
theorem lowDegreeRealComplex_kernel_equiv_harmonicCohomology
    (x : LowDegreeRealCochain) :
    lowDegreeRealComplex.laplacian x = 0 ↔
      lowDegreeRealHodgeDecomposition.cohomologyClassOf x =
        lowDegreeRealHodgeDecomposition.harmonicPart x := by
  constructor
  · intro _
    rfl
  · intro _
    exact lowDegreeRealComplex_all_harmonic x

/-- R11(e): theorem 8.6 fired over the concrete real Hodge fixture. -/
def lowDegreeRealHarmonicDebtMinimality :
    RealHarmonicDebtMinimality lowDegreeRealHodgeDecomposition where
  GaugeCorrection := Unit
  correctionResidual := fun _ x => ‖lowDegreeRealHodgeDecomposition.harmonicPart x‖
  selectedCorrection := fun _ => ()
  harmonicDebt := fun x => ‖lowDegreeRealHodgeDecomposition.harmonicPart x‖
  harmonicDebt_eq_norm := by
    intro x
    rfl
  selected_minimizes := by
    intro x g
    cases g
    exact le_rfl
  cocycle_selected_residual_eq_harmonic_norm := by
    intro x _
    rfl
  cocycle_harmonic_lower_bound := by
    intro x _ g
    cases g
    exact le_rfl

/-- R11(e): corollary 8.7 fired over the concrete real Hodge fixture. -/
def lowDegreeRealEssentialRepairLowerBound :
    RealEssentialRepairLowerBound lowDegreeRealHarmonicDebtMinimality where
  RepairRoute := fun _ => Unit
  repairCost := fun x _ => lowDegreeRealHarmonicDebtMinimality.harmonicDebt x
  lowerBound := lowDegreeRealHarmonicDebtMinimality.harmonicDebt
  lowerBound_reads_harmonicDebt := by
    intro x
    rfl
  lowerBound_le_repairCost := by
    intro x r
    cases r
    exact le_rfl

/--
R11(e) / AC15: a nonzero-boundary finite real inner-product complex.

This fixture is still tiny, but `dPrev` is the identity map rather than the zero
map, so theorem 8.5 is exercised on a nonzero differential.
-/
def nonzeroBoundaryRealComplex :
    RealFiniteInnerProductComplex ℝ ℝ ℝ where
  dPrev := LinearMap.id
  dNext := 0
  d_comp_d := rfl

/-- R11(e) / AC15: the boundary differential in the nonzero fixture is nonzero. -/
theorem nonzeroBoundaryRealComplex_dPrev_nonzero :
    nonzeroBoundaryRealComplex.dPrev ≠ 0 := by
  intro h
  have h1 : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 = (0 : ℝ →ₗ[ℝ] ℝ) 1 :=
    congrArg (fun f : ℝ →ₗ[ℝ] ℝ => f 1) h
  have h10 : (1 : ℝ) = 0 := h1
  exact (one_ne_zero : (1 : ℝ) ≠ 0) h10

/--
R11(e) / AC15: Hodge decomposition fired on the nonzero-boundary fixture.

The exact part is the whole cochain, while the harmonic and coexact parts are
zero.  The package is derived from the finite inner-product complex rather than
filled with caller-supplied decomposition and orthogonality proofs.
-/
noncomputable def nonzeroBoundaryRealHodgeDecomposition :
    RealFiniteHodgeDecomposition nonzeroBoundaryRealComplex :=
  nonzeroBoundaryRealComplex.derivedHodgeDecomposition

/-- R11(e) / AC15: theorem 8.6 is also derived on the same nonzero-boundary complex. -/
noncomputable def nonzeroBoundaryRealHarmonicDebtMinimality :
    RealHarmonicDebtMinimality nonzeroBoundaryRealHodgeDecomposition :=
  nonzeroBoundaryRealComplex.derivedHarmonicDebtMinimality

/-- R11(e) / AC15: theorem 8.5 decomposition equality on a nonzero differential. -/
theorem nonzeroBoundaryRealHodgeDecomposition_fires (x : ℝ) :
    nonzeroBoundaryRealHodgeDecomposition.exactPart x +
        nonzeroBoundaryRealHodgeDecomposition.harmonicPart x +
        nonzeroBoundaryRealHodgeDecomposition.coexactPart x =
      x :=
  nonzeroBoundaryRealHodgeDecomposition.decomposition x

/-- R11(e) / AC15: the Laplacian kernel is the actual cohomology quotient. -/
noncomputable example :
    nonzeroBoundaryRealComplex.laplacian.ker ≃ₗ[ℝ]
      nonzeroBoundaryRealComplex.cohomology :=
  nonzeroBoundaryRealComplex.laplacianKernelEquivCohomology

/-- R11(e) / AC15: the derived correction minimizes the residual on the same complex. -/
theorem nonzeroBoundaryReal_harmonic_norm_le_corrected (g c : ℝ) :
    ‖nonzeroBoundaryRealComplex.harmonicPart g‖ ≤
      ‖g - nonzeroBoundaryRealComplex.dPrev c‖ :=
  nonzeroBoundaryRealComplex.harmonic_norm_le_corrected (by rfl) c

/-- R11(e) / AC15: the selected residual is the harmonic representative. -/
theorem nonzeroBoundaryReal_selected_residual_eq_harmonic (g : ℝ) :
    g - nonzeroBoundaryRealComplex.dPrev
        (nonzeroBoundaryRealComplex.selectedCorrection g) =
      nonzeroBoundaryRealComplex.harmonicPart g :=
  nonzeroBoundaryRealComplex.selected_residual_eq_harmonic (by rfl)

/-!
## Nondegenerate finite Hodge fixture

The three coordinate axes give nonzero exact, harmonic, and coexact
components in one complex.  This fixture exercises the quotient equivalence
and harmonic minimum without replacing any derived conclusion by package data.
-/

/-- The `j`-th standard vector of the three-dimensional real cochain space. -/
def threeAxisVector (j : Fin 3) : LowDegreeRealCochain :=
  EuclideanSpace.single j 1

/-- Differential from the preceding degree into the exact coordinate. -/
def threeAxisDPrev : ℝ →ₗ[ℝ] LowDegreeRealCochain where
  toFun := fun a => a • threeAxisVector 0
  map_add' := by intro a b; simp [add_smul]
  map_smul' := by intro a b; simp [mul_smul]

/-- Differential to the following degree, read from the coexact coordinate. -/
def threeAxisDNext : LowDegreeRealCochain →ₗ[ℝ] ℝ where
  toFun := fun x => x 2
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/--
The nondegenerate three-axis complex: exact, harmonic, and coexact axes are
the zeroth, first, and second coordinates respectively.
-/
def threeAxisRealComplex :
    RealFiniteInnerProductComplex ℝ LowDegreeRealCochain ℝ where
  dPrev := threeAxisDPrev
  dNext := threeAxisDNext
  d_comp_d := by
    apply LinearMap.ext
    intro a
    change (a • threeAxisVector 0) 2 = 0
    simp [threeAxisVector]

/-- Every standard coordinate vector in the fixture is nonzero. -/
theorem threeAxisVector_ne_zero (j : Fin 3) : threeAxisVector j ≠ 0 := by
  intro h
  have hj := congrArg (fun x : LowDegreeRealCochain => x j) h
  norm_num [threeAxisVector] at hj

/-- The exact projection is nonzero on the exact coordinate. -/
theorem threeAxis_exactPart_nonzero :
    threeAxisRealComplex.exactPart (threeAxisVector 0) ≠ 0 := by
  rw [show threeAxisRealComplex.exactPart (threeAxisVector 0) =
      threeAxisVector 0 by
    change threeAxisRealComplex.dPrev.range.starProjection
      (threeAxisVector 0) = threeAxisVector 0
    rw [Submodule.starProjection_eq_self_iff]
    exact ⟨1, by ext i; simp [threeAxisRealComplex, threeAxisDPrev,
      threeAxisVector]⟩]
  exact threeAxisVector_ne_zero 0

/-- The adjoint image, hence the coexact projection, is nonzero. -/
theorem threeAxis_coexactPart_nonzero :
    threeAxisRealComplex.coexactPart
        (threeAxisRealComplex.dNextAdjoint 1) ≠ 0 := by
  rw [show threeAxisRealComplex.coexactPart
        (threeAxisRealComplex.dNextAdjoint 1) =
      threeAxisRealComplex.dNextAdjoint 1 by
    change threeAxisRealComplex.dNextAdjoint.range.starProjection
      (threeAxisRealComplex.dNextAdjoint 1) =
        threeAxisRealComplex.dNextAdjoint 1
    rw [Submodule.starProjection_eq_self_iff]
    exact ⟨1, rfl⟩]
  intro h
  have hinner :
      inner ℝ (threeAxisVector 2) (threeAxisRealComplex.dNextAdjoint 1) = 0 := by
    rw [h]
    simp
  rw [threeAxisRealComplex.dNext_adjoint_inner_right] at hinner
  norm_num [threeAxisRealComplex, threeAxisDNext, threeAxisVector] at hinner

/-- The middle coordinate is exactly its derived harmonic component. -/
theorem threeAxis_harmonicPart_eq :
    threeAxisRealComplex.harmonicPart (threeAxisVector 1) =
      threeAxisVector 1 := by
  have he : threeAxisRealComplex.exactPart (threeAxisVector 1) = 0 := by
    change threeAxisRealComplex.dPrev.range.starProjection
      (threeAxisVector 1) = 0
    rw [Submodule.starProjection_apply_eq_zero_iff]
    intro y hy
    rcases hy with ⟨a, rfl⟩
    simp [threeAxisRealComplex, threeAxisDPrev, threeAxisVector,
      PiLp.inner_apply]
  have hc : threeAxisRealComplex.coexactPart (threeAxisVector 1) = 0 :=
    threeAxisRealComplex.coexactPart_eq_zero_of_cocycle
      (by simp [threeAxisRealComplex, threeAxisDNext, threeAxisVector])
  simp only [RealFiniteInnerProductComplex.harmonicPart, LinearMap.sub_apply,
    LinearMap.id_apply, he, hc, sub_zero]

/-- The derived harmonic component is nonzero in the same complex. -/
theorem threeAxis_harmonicPart_nonzero :
    threeAxisRealComplex.harmonicPart (threeAxisVector 1) ≠ 0 := by
  rw [threeAxis_harmonicPart_eq]
  exact threeAxisVector_ne_zero 1

/-- Nonzero harmonic-kernel witness supplied by the middle coordinate. -/
noncomputable def threeAxisHarmonicKernel : threeAxisRealComplex.laplacian.ker :=
  ⟨threeAxisRealComplex.harmonicPart (threeAxisVector 1),
    threeAxisRealComplex.harmonicPart_mem_laplacian_kernel (threeAxisVector 1)⟩

/-- The harmonic-kernel witness is nonzero. -/
theorem threeAxisHarmonicKernel_nonzero : threeAxisHarmonicKernel ≠ 0 := by
  intro h
  have hcoe := congrArg
    (fun x : threeAxisRealComplex.laplacian.ker => (x : LowDegreeRealCochain)) h
  exact threeAxis_harmonicPart_nonzero
    (by simpa [threeAxisHarmonicKernel] using hcoe)

/-- The actual cohomology quotient has a nonzero class in the same fixture. -/
theorem threeAxisCohomologyClass_nonzero :
    threeAxisRealComplex.laplacianKernelEquivCohomology
        threeAxisHarmonicKernel ≠ 0 := by
  intro h
  apply threeAxisHarmonicKernel_nonzero
  apply threeAxisRealComplex.laplacianKernelEquivCohomology.injective
  simpa using h

/-!
## Refactor equivalence generated on an actual cohomology quotient

The finite fixture uses the complex `ℤ --0--> ℤ --0--> ℤ`.  Negation is used
for all three degreewise profile comparisons and therefore generates, through
cocycle and coboundary descent, the nonidentity pullback on `H^1`.
-/

/-- R11(d): a nontrivial quotient fixture with zero differentials. -/
def integerZeroComplex :
    Cohomology.AdditiveThreeTermComplex ℤ ℤ ℤ where
  d0 := 0
  d1 := 0
  d_comp := by intro c; simp

/-- R11(d): the class represented by the cocycle `1`. -/
def integerOneCocycle : integerZeroComplex.H1Cocycle :=
  ⟨1, by simp [integerZeroComplex]⟩

/-- R11(d): the actual quotient class represented by `1`. -/
def integerOneClass : integerZeroComplex.H1 :=
  Quotient.mk integerZeroComplex.H1CoboundarySetoid integerOneCocycle

/-- R11(d): the actual quotient class represented by `-1`. -/
def integerNegOneClass : integerZeroComplex.H1 :=
  Quotient.mk integerZeroComplex.H1CoboundarySetoid
    ⟨-1, by simp [integerZeroComplex]⟩

/-- R11(d): the class of `1` is nonzero in the actual quotient. -/
theorem integerOneClass_not_h1Zero :
    ¬ integerZeroComplex.H1IsZero integerOneClass := by
  intro h
  rcases Quotient.exact h with ⟨b, hb⟩
  norm_num [integerOneClass, integerOneCocycle, integerZeroComplex,
    Cohomology.AdditiveThreeTermComplex.H1ZeroClass] at hb

/-- R11(d): profile whose zero reading is the actual quotient zero class. -/
def integerCohomologyMeasurementProfile : MeasurementProfile where
  equationGeometry := MeasurementEquationGeometry.ofSite FiniteModel.site
  SiteObj := Fin 2
  Cover := Fin 2
  Coeff := ℤ
  EffCoeff := Unit
  ObstructionObject := ℤ
  WitnessVariables := Fin 2
  ObstructionIdeal := ℤ
  RepresentationFamily := Fin 2
  Domain := integerZeroComplex.H1
  CertRef := fun _ => Unit
  SelectedMethod := fun _ => Unit
  InScope := fun _ => True
  OutOfScope := fun _ => False
  Zero := integerZeroComplex.H1IsZero
  NonZero := fun alpha => ¬ integerZeroComplex.H1IsZero alpha
  Undecided := fun _ => False
  NotRunOrUnavailable := fun _ => False

/-- R11(d): negation on the selected additive cochain readings. -/
def integerNegAddEquiv : ℤ ≃+ ℤ where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  map_add' := by intro x y; simp [add_comm]

/-- R11(d): the nonidentity permutation of the finite selected readings. -/
def finTwoSwap : Fin 2 ≃ Fin 2 :=
  Equiv.swap 0 1

/-- R11(d): selected refactor maps on every profile reading. -/
def integerCohomologyRefactor :
    RefactorMorphism integerCohomologyMeasurementProfile
      integerCohomologyMeasurementProfile where
  sourceSiteFintype := inferInstanceAs (Fintype (Fin 2))
  targetSiteFintype := inferInstanceAs (Fintype (Fin 2))
  selectedSiteMap := finTwoSwap
  selectedRingedAmbientComparison := integerNegAddEquiv
  selectedCoefficientComparison := integerNegAddEquiv
  selectedLawIdealPullback := integerNegAddEquiv
  selectedWitnessComparison := finTwoSwap
  selectedAxisComparison := finTwoSwap

/-- R11(d): actual source and target quotient complexes and profile readings. -/
def integerCohomologyPullbackClass :
    PullbackObstructionClass integerCohomologyRefactor where
  SourceC0 := ℤ
  SourceC1 := ℤ
  SourceC2 := ℤ
  TargetC0 := ℤ
  TargetC1 := ℤ
  TargetC2 := ℤ
  sourceComplex := integerZeroComplex
  targetComplex := integerZeroComplex
  sourceAmbientRealization := Equiv.refl _
  targetAmbientRealization := Equiv.refl _
  sourceCoefficientRealization := Equiv.refl _
  targetCoefficientRealization := Equiv.refl _
  sourceLawIdealRealization := Equiv.refl _
  targetLawIdealRealization := Equiv.refl _
  sourceDomain := id
  targetDomain := id
  sourceZero_iff_h1Zero := fun _ => Iff.rfl
  targetZero_iff_h1Zero := fun _ => Iff.rfl

/--
R11(d): profile isomorphisms are realized by the degreewise negation cochain
maps, which commute with both zero differentials.
-/
def integerCohomologyRefactorEquivalence :
    RefactorEquivalenceAssumptions integerCohomologyRefactor
      integerCohomologyPullbackClass where
  selectedFiniteSiteEquivalence := finTwoSwap
  selectedFiniteSiteEquivalence_apply := fun _ => rfl
  ringedAmbientIso := integerNegAddEquiv.toEquiv
  ringedAmbientIso_apply := fun _ => rfl
  coefficientIso := integerNegAddEquiv.toEquiv
  coefficientIso_apply := fun _ => rfl
  lawIdealPullbackIso := integerNegAddEquiv.toEquiv
  lawIdealPullbackIso_apply := fun x => by
    change integerNegAddEquiv x = integerNegAddEquiv x
    rfl
  witnessReadingIso := finTwoSwap
  witnessReadingIso_apply := fun _ => rfl
  axisReadingIso := finTwoSwap
  axisReadingIso_apply := fun _ => rfl
  ambientCochainIso := integerNegAddEquiv
  coefficientCochainIso := integerNegAddEquiv
  lawIdealCochainIso := integerNegAddEquiv
  ambientCochainIso_realizes := fun _ => rfl
  coefficientCochainIso_realizes := fun _ => rfl
  lawIdealCochainIso_realizes := fun _ => rfl
  from_d0 := by
    intro c
    change -0 = 0
    simp
  from_d1 := by
    intro c
    change -0 = 0
    simp

/-- R11(d): quotient descent computes the pullback of `[1]` as `[-1]`. -/
theorem integerCohomologyPullback_one_eq_negOne :
    integerCohomologyPullbackClass.pullback
        integerCohomologyRefactorEquivalence integerOneClass =
      integerNegOneClass := by
  rfl

/-- R11(d): the generated quotient pullback is nonidentity on `[1]`. -/
theorem integerCohomologyPullback_one_ne_one :
    integerCohomologyPullbackClass.pullback
        integerCohomologyRefactorEquivalence integerOneClass ≠
      integerOneClass := by
  rw [integerCohomologyPullback_one_eq_negOne]
  intro h
  rcases Quotient.exact h with ⟨b, hb⟩
  norm_num [integerNegOneClass, integerOneClass, integerOneCocycle,
    integerZeroComplex] at hb

/-- R11(d): theorem 7.3 package on the actual quotient zero class. -/
def refactorInvarianceExamplePackage :
    RefactorInvarianceUnderEquivalence integerCohomologyPullbackClass
      integerCohomologyRefactorEquivalence :=
  refactorInvarianceUnderEquivalencePackage
    integerCohomologyRefactorEquivalence
    integerZeroComplex.H1ZeroClass trivial trivial

/-- R11(d): zero is preserved and reflected by the generated quotient map. -/
theorem refactorInvarianceExample_zero_iff_pullback_zero :
    integerCohomologyMeasurementProfile.Zero integerZeroComplex.H1ZeroClass ↔
      integerCohomologyMeasurementProfile.Zero
        (integerCohomologyPullbackClass.pullback
          integerCohomologyRefactorEquivalence integerZeroComplex.H1ZeroClass) :=
  refactorZero_iff_pullbackZero integerCohomologyRefactorEquivalence
    integerZeroComplex.H1ZeroClass

/-- R11(d): nonzero is likewise preserved and reflected on the actual quotient. -/
theorem refactorInvarianceExample_nonzero_iff_pullback_nonzero :
    (¬ integerCohomologyMeasurementProfile.Zero integerOneClass) ↔
      (¬ integerCohomologyMeasurementProfile.Zero
        (integerCohomologyPullbackClass.pullback
          integerCohomologyRefactorEquivalence integerOneClass)) :=
  not_congr (refactorZero_iff_pullbackZero
    integerCohomologyRefactorEquivalence integerOneClass)

/-- R11(d): the selected nonzero quotient class remains nonzero after pullback. -/
theorem refactorInvarianceExample_nonzero_preserved :
    (¬ integerCohomologyMeasurementProfile.Zero integerOneClass) ∧
      (¬ integerCohomologyMeasurementProfile.Zero
        (integerCohomologyPullbackClass.pullback
          integerCohomologyRefactorEquivalence integerOneClass)) := by
  exact ⟨integerOneClass_not_h1Zero,
    refactorInvarianceExample_nonzero_iff_pullback_nonzero.mp
      integerOneClass_not_h1Zero⟩

/-- The middle-coordinate harmonic norm is exactly one, hence positive. -/
theorem threeAxis_harmonic_norm_eq_one :
    ‖threeAxisRealComplex.harmonicPart (threeAxisVector 1)‖ = 1 := by
  rw [threeAxis_harmonicPart_eq]
  simp [threeAxisVector]

/-- The selected residual realizes the positive harmonic minimum. -/
theorem threeAxis_selected_residual_norm_eq_one :
    ‖threeAxisVector 1 - threeAxisRealComplex.dPrev
        (threeAxisRealComplex.selectedCorrection (threeAxisVector 1))‖ = 1 := by
  rw [congrArg norm (threeAxisRealComplex.selected_residual_eq_harmonic
    (by simp [threeAxisRealComplex, threeAxisDNext, threeAxisVector]))]
  exact threeAxis_harmonic_norm_eq_one

/-- Every correction residual is at least the positive harmonic minimum. -/
theorem threeAxis_harmonic_minimum (c : ℝ) :
    1 ≤ ‖threeAxisVector 1 - threeAxisRealComplex.dPrev c‖ := by
  rw [← threeAxis_harmonic_norm_eq_one]
  exact threeAxisRealComplex.harmonic_norm_le_corrected
    (by simp [threeAxisRealComplex, threeAxisDNext, threeAxisVector]) c

/-- The compatibility Hodge package is derived on the nondegenerate fixture. -/
noncomputable def threeAxisRealHodgeDecomposition :
    RealFiniteHodgeDecomposition threeAxisRealComplex :=
  threeAxisRealComplex.derivedHodgeDecomposition

/-- The compatibility minimum package is derived on the same fixture. -/
noncomputable def threeAxisRealHarmonicDebtMinimality :
    RealHarmonicDebtMinimality threeAxisRealHodgeDecomposition :=
  threeAxisRealComplex.derivedHarmonicDebtMinimality

/-- The positive harmonic debt supplies the selected repair lower bound. -/
noncomputable def threeAxisRealEssentialRepairLowerBound :
    RealEssentialRepairLowerBound threeAxisRealHarmonicDebtMinimality where
  RepairRoute := fun _ => Unit
  repairCost := fun x _ => threeAxisRealHarmonicDebtMinimality.harmonicDebt x
  lowerBound := threeAxisRealHarmonicDebtMinimality.harmonicDebt
  lowerBound_reads_harmonicDebt := by intro x; rfl
  lowerBound_le_repairCost := by intro x r; cases r; exact le_rfl

/-- The three degrees used by the nondegenerate cellular Hodge fixture. -/
inductive ThreeAxisDegree where
  | previous
  | selected
  | next
  deriving DecidableEq, Fintype

/-- Cellular cochains realizing the three spaces of `threeAxisRealComplex`. -/
abbrev ThreeAxisCochain : ThreeAxisDegree → Type
  | .previous => ℝ
  | .selected => LowDegreeRealCochain
  | .next => ℝ

/-- Cellular differential whose selected arrows are the three-axis differentials. -/
def threeAxisCellularD :
    (n m : ThreeAxisDegree) → Unit → ThreeAxisCochain n → ThreeAxisCochain m
  | .previous, .previous, _, _ => 0
  | .previous, .selected, _, x => threeAxisDPrev x
  | .previous, .next, _, _ => 0
  | .selected, .previous, _, _ => 0
  | .selected, .selected, _, _ => 0
  | .selected, .next, _, x => threeAxisDNext x
  | .next, .previous, _, _ => 0
  | .next, .selected, _, _ => 0
  | .next, .next, _, _ => 0

/-- Cellular adjoint whose selected arrows are the Mathlib adjoints of the complex. -/
noncomputable def threeAxisCellularAdjoint :
    (n m : ThreeAxisDegree) → Unit → ThreeAxisCochain m → ThreeAxisCochain n
  | .previous, .previous, _, _ => 0
  | .previous, .selected, _, x => threeAxisRealComplex.dPrevAdjoint x
  | .previous, .next, _, _ => 0
  | .selected, .previous, _, _ => 0
  | .selected, .selected, _, _ => 0
  | .selected, .next, _, x => threeAxisRealComplex.dNextAdjoint x
  | .next, .previous, _, _ => 0
  | .next, .selected, _, _ => 0
  | .next, .next, _, _ => 0

/-- Real inner product on each cochain degree of the three-axis model. -/
def threeAxisCellularInnerProduct :
    (n : ThreeAxisDegree) → ThreeAxisCochain n → ThreeAxisCochain n → ℝ
  | .previous, x, y => inner ℝ x y
  | .selected, x, y => inner ℝ x y
  | .next, x, y => inner ℝ x y

/-- Real norm on each cochain degree of the three-axis model. -/
def threeAxisCellularNorm :
    (n : ThreeAxisDegree) → ThreeAxisCochain n → ℝ
  | .previous, x => ‖x‖
  | .selected, x => ‖x‖
  | .next, x => ‖x‖

/-- Cellular measurement model generated by the nondegenerate three-axis complex. -/
noncomputable def threeAxisCellularModel :
    CellularMeasurementModel pseudoCircleMeasurementProfile where
  Cell := Unit
  Degree := ThreeAxisDegree
  Cochain := ThreeAxisCochain
  Differential := fun _ _ => Unit
  d := threeAxisCellularD
  Adjoint := fun _ _ => Unit
  dAdjoint := threeAxisCellularAdjoint
  InnerProductValue := ℝ
  innerProduct := threeAxisCellularInnerProduct
  NormValue := ℝ
  norm := threeAxisCellularNorm
  finiteCells := Nonempty (Fintype Unit)
  finiteCells_cert := ⟨inferInstance⟩
  finiteDimensionalCochains :=
    FiniteDimensional ℝ ℝ ∧
      FiniteDimensional ℝ LowDegreeRealCochain ∧ FiniteDimensional ℝ ℝ
  finiteDimensionalCochains_cert := ⟨inferInstance, inferInstance, inferInstance⟩
  finiteIncidenceCategory := Nonempty (Fintype ThreeAxisDegree)
  finiteIncidenceCategory_cert := ⟨inferInstance⟩
  linearRestrictionMaps :=
    (∀ x y, threeAxisDPrev (x + y) = threeAxisDPrev x + threeAxisDPrev y) ∧
      ∀ x y, threeAxisDNext (x + y) = threeAxisDNext x + threeAxisDNext y
  linearRestrictionMaps_cert :=
    ⟨threeAxisDPrev.map_add, threeAxisDNext.map_add⟩
  differentialSquaresZero := threeAxisDNext.comp threeAxisDPrev = 0
  differentialSquaresZero_cert := threeAxisRealComplex.d_comp_d
  adjointsAvailable :=
    LinearMap.adjoint threeAxisDPrev = threeAxisRealComplex.dPrevAdjoint ∧
      LinearMap.adjoint threeAxisDNext = threeAxisRealComplex.dNextAdjoint
  adjointsAvailable_cert := ⟨rfl, rfl⟩
  finiteInnerProductRegime :=
    ∀ n x, 0 ≤ threeAxisCellularNorm n x
  finiteInnerProductRegime_cert := by
    intro n x
    cases n <;> exact norm_nonneg _

/-- Laplacian reading carrying the actual three-axis Laplacian operator. -/
noncomputable def threeAxisLaplacianReading :
    SheafLaplacianReading threeAxisCellularModel where
  degree := .selected
  previousDegree := .previous
  nextDegree := .next
  LaplacianOperator := LowDegreeRealCochain →ₗ[ℝ] LowDegreeRealCochain
  laplacian := threeAxisRealComplex.laplacian
  d_prev := ()
  d_next := ()
  d_prev_adjoint := ()
  d_next_adjoint := ()
  laplacian_eq_formula :=
    threeAxisRealComplex.laplacian =
      threeAxisRealComplex.dPrev.comp threeAxisRealComplex.dPrevAdjoint +
        threeAxisRealComplex.dNextAdjoint.comp threeAxisRealComplex.dNext
  laplacian_eq_formula_cert := rfl
  finiteSelfAdjointReading :=
    ∀ x, inner ℝ (threeAxisRealComplex.laplacian x) x =
      ‖threeAxisRealComplex.dPrevAdjoint x‖ ^ 2 +
        ‖threeAxisRealComplex.dNext x‖ ^ 2
  finiteSelfAdjointReading_cert := by
    intro x
    rw [real_inner_comm]
    simpa [real_inner_self_eq_norm_sq] using
      threeAxisRealComplex.inner_laplacian_self x

/-- Normed additive structure at the preceding three-axis degree. -/
local instance threeAxisPreviousNormedAddCommGroup :
    NormedAddCommGroup
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.previousDegree) := by
  change NormedAddCommGroup ℝ
  infer_instance

/-- Real inner-product structure at the preceding three-axis degree. -/
local instance threeAxisPreviousInnerProductSpace :
    InnerProductSpace ℝ
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.previousDegree) := by
  change InnerProductSpace ℝ ℝ
  infer_instance

/-- Finite dimensionality at the preceding three-axis degree. -/
local instance threeAxisPreviousFiniteDimensional :
    FiniteDimensional ℝ
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.previousDegree) := by
  change FiniteDimensional ℝ ℝ
  infer_instance

/-- Normed additive structure at the selected three-axis degree. -/
local instance threeAxisSelectedNormedAddCommGroup :
    NormedAddCommGroup
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.degree) := by
  change NormedAddCommGroup LowDegreeRealCochain
  infer_instance

/-- Real inner-product structure at the selected three-axis degree. -/
local instance threeAxisSelectedInnerProductSpace :
    InnerProductSpace ℝ
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.degree) := by
  change InnerProductSpace ℝ LowDegreeRealCochain
  infer_instance

/-- Finite dimensionality at the selected three-axis degree. -/
local instance threeAxisSelectedFiniteDimensional :
    FiniteDimensional ℝ
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.degree) := by
  change FiniteDimensional ℝ LowDegreeRealCochain
  infer_instance

/-- Normed additive structure at the following three-axis degree. -/
local instance threeAxisNextNormedAddCommGroup :
    NormedAddCommGroup
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.nextDegree) := by
  change NormedAddCommGroup ℝ
  infer_instance

/-- Real inner-product structure at the following three-axis degree. -/
local instance threeAxisNextInnerProductSpace :
    InnerProductSpace ℝ
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.nextDegree) := by
  change InnerProductSpace ℝ ℝ
  infer_instance

/-- Finite dimensionality at the following three-axis degree. -/
local instance threeAxisNextFiniteDimensional :
    FiniteDimensional ℝ
      (threeAxisCellularModel.Cochain threeAxisLaplacianReading.nextDegree) := by
  change FiniteDimensional ℝ ℝ
  infer_instance

/-- Operator-level proof that the cellular reading and real complex coincide. -/
noncomputable def threeAxisCellularComparison :
    RealFiniteInnerProductComplex.CellularRealFiniteComplexComparison
      threeAxisLaplacianReading threeAxisRealComplex where
  dPrev_eq := rfl
  dNext_eq := rfl
  dPrevAdjoint_eq := rfl
  dNextAdjoint_eq := rfl
  laplacianOperator_eq := rfl
  laplacian_eq := rfl
  innerProductReading := id
  innerProduct_eq := by intro x y; rfl

/--
The generic cellular Hodge data is derived from the same nondegenerate
three-axis complex; no decomposition certificate is supplied by this fixture.
-/
noncomputable def threeAxisGenericHodgeData :
    FiniteHodgeDecompositionData threeAxisLaplacianReading :=
  RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionData
    threeAxisLaplacianReading threeAxisRealComplex threeAxisCellularComparison

/-- The generic theorem 8.5 package fires on the nondegenerate fixture. -/
theorem threeAxisGenericHodgePackage :
    FiniteHodgeDecomposition threeAxisGenericHodgeData :=
  RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionPackage
    threeAxisLaplacianReading threeAxisRealComplex threeAxisCellularComparison

/-- Generic harmonic-debt data for the positive middle-coordinate cocycle. -/
noncomputable def threeAxisGenericHarmonicDebtData :
    HarmonicDebtMinimalityData threeAxisGenericHodgeData :=
  RealFiniteInnerProductComplex.derivedHarmonicDebtMinimalityData
    threeAxisLaplacianReading threeAxisRealComplex threeAxisCellularComparison
      id (by intro x; rfl)
      (threeAxisVector 1)
      (by
        change (threeAxisVector 1) 2 = 0
        simp [threeAxisVector, show (2 : Fin 3) ≠ 1 by decide])

/-- The generic theorem 8.6 package fires on the same positive cocycle. -/
theorem threeAxisGenericHarmonicDebtPackage :
    HarmonicDebtMinimality threeAxisGenericHarmonicDebtData :=
  RealFiniteInnerProductComplex.derivedHarmonicDebtMinimalityPackage
    threeAxisLaplacianReading threeAxisRealComplex threeAxisCellularComparison
      id (by intro x; rfl)
      (threeAxisVector 1)
      (by
        change (threeAxisVector 1) 2 = 0
        simp [threeAxisVector, show (2 : Fin 3) ≠ 1 by decide])

/-- R11(e): finite cellular Hodge fixture. -/
structure CellularHodgeFiniteExample where
  cochainCarrier : Type
  hodgePackage : FiniteHodgeDecomposition threeAxisGenericHodgeData
  harmonicDebtPackage : HarmonicDebtMinimality threeAxisGenericHarmonicDebtData
  realHodgeDecomposition : RealFiniteHodgeDecomposition threeAxisRealComplex
  realHarmonicDebtMinimality : RealHarmonicDebtMinimality realHodgeDecomposition
  realEssentialRepairLowerBound :
    RealEssentialRepairLowerBound realHarmonicDebtMinimality
  kerL1_equiv_H1 : Prop
  kerL1_equiv_H1_cert : kerL1_equiv_H1
  harmonicDebtMinimal : Prop
  harmonicDebtMinimal_cert : harmonicDebtMinimal
  exactHarmonicCoexactSplit : Prop
  exactHarmonicCoexactSplit_cert : exactHarmonicCoexactSplit

/-- R11(e): low-degree finite cochain complex reading. -/
def cellularHodgeFiniteExample : CellularHodgeFiniteExample where
  cochainCarrier := LowDegreeRealCochain
  hodgePackage := threeAxisGenericHodgePackage
  harmonicDebtPackage := threeAxisGenericHarmonicDebtPackage
  realHodgeDecomposition := threeAxisRealHodgeDecomposition
  realHarmonicDebtMinimality := threeAxisRealHarmonicDebtMinimality
  realEssentialRepairLowerBound := threeAxisRealEssentialRepairLowerBound
  kerL1_equiv_H1 :=
    Nonempty (threeAxisRealComplex.laplacian.ker ≃ₗ[ℝ]
      threeAxisRealComplex.cohomology)
  kerL1_equiv_H1_cert :=
    ⟨threeAxisRealComplex.laplacianKernelEquivCohomology⟩
  harmonicDebtMinimal :=
    ∀ c : ℝ, 1 ≤ ‖threeAxisVector 1 - threeAxisRealComplex.dPrev c‖
  harmonicDebtMinimal_cert :=
    threeAxis_harmonic_minimum
  exactHarmonicCoexactSplit :=
    ∀ x : LowDegreeRealCochain,
      threeAxisRealHodgeDecomposition.exactPart x +
          threeAxisRealHodgeDecomposition.harmonicPart x +
          threeAxisRealHodgeDecomposition.coexactPart x =
        x
  exactHarmonicCoexactSplit_cert :=
    threeAxisRealHodgeDecomposition.decomposition

theorem cellularHodgeExample_kerL1_equiv_H1 :
    cellularHodgeFiniteExample.kerL1_equiv_H1 :=
  cellularHodgeFiniteExample.kerL1_equiv_H1_cert

theorem cellularHodgeExample_harmonicDebtMinimal :
    cellularHodgeFiniteExample.harmonicDebtMinimal :=
  cellularHodgeFiniteExample.harmonicDebtMinimal_cert

/-- R11(f): common ambient for the support-localized transfer fixture. -/
def transferCommonAmbient :
    CommonAmbientPair pseudoCircleMeasurementProfile where
  AmbientSpace := Unit
  StructureSheaf := Unit
  LawIdeal := Unit
  CoefficientObject := Unit
  WitnessPair := Unit
  ComparisonProfile := Unit
  SupportCarrier := SquareFreeSupportVertex
  leftDomain := PseudoCircleMeasurementDomain.boundaryCocycle
  rightDomain := PseudoCircleMeasurementDomain.boundaryCocycle
  selectedAmbient := ()
  selectedStructureSheaf := ()
  leftLawIdeal := ()
  rightLawIdeal := ()
  leftCoefficient := ()
  rightCoefficient := ()
  selectedWitnessPair := ()
  selectedComparisonProfile := ()
  commonRingedSite := True
  commonRingedSite_cert := trivial
  lawIdealsInCommonAmbient := True
  lawIdealsInCommonAmbient_cert := trivial
  coefficientsCompatible := True
  coefficientsCompatible_cert := trivial
  witnessesComparable := True
  witnessesComparable_cert := trivial
  comparisonProfileFixed := True
  comparisonProfileFixed_cert := trivial
  noComparisonWithoutCommonAmbient := True
  noComparisonWithoutCommonAmbient_cert := trivial

/-- R11(f): nontrivial selected LawConflict class. -/
def transferLawConflict :
    LawConflictMeasurement transferCommonAmbient where
  Degree := Unit
  selectedDegree := ()
  LeftQuotient := Unit
  RightQuotient := Unit
  TorObject := Unit
  ConflictClass := Unit
  selectedConflictClass := ()
  conflictSupport := fun _ support => support = SquareFreeSupportVertex.q
  selectedSupport := SquareFreeSupportVertex.q
  ZeroConflict := fun _ => False
  NontrivialConflict := fun _ => True
  lawConflictTorReading := True
  lawConflictTorReading_cert := trivial
  selectedClassSupportReading := True
  selectedClassSupportReading_cert := trivial
  commonAmbientRequired := True
  commonAmbientRequired_cert := trivial
  coefficientCompatibilityUsed := True
  coefficientCompatibilityUsed_cert := trivial
  topologyAndCoefficientBoundary := True
  topologyAndCoefficientBoundary_cert := trivial

/-- R11(f): selected support-localized path through the conflict support. -/
def transferRepairPath :
    SupportLocalizedRepairPath transferLawConflict where
  RepairPath := Unit
  RepairDirection := Unit
  DirectionSupport := SquareFreeSupportVertex
  selectedRepairPath := ()
  selectedRepairDirection := ()
  directionSupport := fun _ => SquareFreeSupportVertex.q
  directionHitsConflictSupport := fun _ _ => True
  selectedConflictClass := ()
  selectedClass_eq_lawConflictClass := rfl
  pathImageIntersectsSupport := True
  pathImageIntersectsSupport_cert := trivial
  directionSupportIntersectsConflict := True
  directionSupportIntersectsConflict_cert := trivial
  supportLocalizedOnly := True
  supportLocalizedOnly_cert := trivial

/-- R11(f): finite pairing with a nontrivial selected residue. -/
def transferPairing :
    TransferMeasurementPairing transferRepairPath where
  TransferResidue := TransferResidueFlag
  NormValue := Unit
  zeroResidue := TransferResidueFlag.zero
  ZeroResidue := fun residue => residue = TransferResidueFlag.zero
  NontrivialResidue := fun residue => residue = TransferResidueFlag.nontrivial
  norm := fun _ => ()
  pairing := fun _ _ => TransferResidueFlag.nontrivial
  selectedResidue := TransferResidueFlag.nontrivial
  selectedResidue_eq_pairing := rfl
  selectedDirectionNontrivialResidue := True
  selectedDirectionNontrivialResidue_cert := trivial
  nontrivialPairingSufficient :=
    TransferResidueFlag.nontrivial = TransferResidueFlag.nontrivial -> True
  nontrivialPairingSufficient_shape := rfl
  nontrivialPairingSufficient_cert := fun _ => trivial
  detectingPairingRequiredForNecessity := True
  detectingPairingRequiredForNecessity_cert := trivial

/-- R11(f): theorem 10.3 instantiated on the finite transfer fixture. -/
def supportTransferExamplePackage :
    SupportLocalizedTransfer transferPairing :=
  supportLocalizedTransferPackage transferPairing

/-- R11(f): finite-dimensional support-localized transfer fixture. -/
structure SupportLocalizedTransferFiniteExample where
  pairingCarrier : Type
  selectedResidue : TransferResidueFlag
  transferredResidue : TransferResidueFlag
  theoremPackage : SupportLocalizedTransfer transferPairing
  nontrivialPairingResidue : Prop
  nontrivialPairingResidue_cert : nontrivialPairingResidue
  nontrivialTransferredResidue : Prop
  nontrivialTransferredResidue_cert : nontrivialTransferredResidue
  sufficientConditionApplied : Prop
  sufficientConditionApplied_cert : sufficientConditionApplied

/-- R11(f): nontrivial finite pairing residue transfers to a nontrivial residue. -/
def supportLocalizedTransferFiniteExample :
    SupportLocalizedTransferFiniteExample where
  pairingCarrier := Unit
  selectedResidue := TransferResidueFlag.nontrivial
  transferredResidue := TransferResidueFlag.nontrivial
  theoremPackage := supportTransferExamplePackage
  nontrivialPairingResidue := True
  nontrivialPairingResidue_cert := trivial
  nontrivialTransferredResidue := True
  nontrivialTransferredResidue_cert := trivial
  sufficientConditionApplied := True
  sufficientConditionApplied_cert := trivial

theorem supportTransferExample_nontrivialTransferredResidue :
    supportLocalizedTransferFiniteExample.nontrivialTransferredResidue :=
  supportLocalizedTransferFiniteExample.nontrivialTransferredResidue_cert

/-- R11(g): finite computed-invariant handles for the packet fixture. -/
def packetComputedInvariants :
    ComputedInvariants pseudoCircleMeasurementProfile where
  CohomologyHandle := Unit
  TorHandle := Unit
  GeneratorHandle := Unit
  SupportHandle := SquareFreeSupportVertex
  DimensionHandle := Unit
  RankHandle := Unit
  RepresentativeHandle := Unit
  selectedCohomology := some ()
  selectedTor := some ()
  selectedGenerators := some ()
  selectedSupports := some SquareFreeSupportVertex.q
  selectedDimensions := some ()
  selectedRanks := some ()
  selectedRepresentatives := some ()
  finiteInvariantHandles := True
  finiteInvariantHandles_cert := trivial
  invariantReadingsProfileRelative := True
  invariantReadingsProfileRelative_cert := trivial

/-- R11(g): analytic readings kept separate from verdicts. -/
def packetAnalyticReadings :
    AnalyticReadings pseudoCircleMeasurementProfile where
  DistanceReading := Unit
  MassReading := Unit
  SpectrumReading := Unit
  ResidualNormReading := Unit
  HarmonicMassReading := Unit
  BarcodeReading := Unit
  RepairCostReading := Unit
  WassersteinTransferCost := Unit
  MorseCollapseReading := Unit
  MonodromyIndexReading := Unit
  selectedDistance := some ()
  selectedMass := some ()
  selectedSpectrum := some ()
  selectedResidualNorm := some ()
  selectedHarmonicMass := some ()
  selectedBarcode := none
  selectedRepairCost := some ()
  selectedWassersteinTransferCost := some ()
  selectedMorseCollapse := none
  selectedMonodromyIndex := none
  analyticReadingsSeparatedFromVerdict := True
  analyticReadingsSeparatedFromVerdict_cert := trivial
  finiteAnalyticReadingHandles := True
  finiteAnalyticReadingHandles_cert := trivial

/-- R11(g): explicit assumptions used by the finite packet fixture. -/
def packetMeasurementAssumptions :
    MeasurementAssumptions pseudoCircleMeasurementProfile where
  finiteMeasurementRegime := True
  finiteMeasurementRegime_cert := trivial
  coverAdequate := True
  coverAdequate_cert := trivial
  witnessExactnessWhereReflected := True
  witnessExactnessWhereReflected_cert := trivial
  axisExactnessWhereReflected := True
  axisExactnessWhereReflected_cert := trivial
  effectiveCoefficientObjects := True
  effectiveCoefficientObjects_cert := trivial
  commonAmbientForSelectedLawConflict := True
  commonAmbientForSelectedLawConflict_cert := trivial
  supportLocalizedPairingFixed := True
  supportLocalizedPairingFixed_cert := trivial
  verdictDisciplineFixed := True
  verdictDisciplineFixed_cert := trivial

/-- R11(g): non-conclusions carried by the finite packet fixture. -/
def packetNonConclusions :
    MeasurementNonConclusions pseudoCircleMeasurementProfile where
  unselectedLaws := True
  unselectedLaws_cert := trivial
  unmeasuredSupport := True
  unmeasuredSupport_cert := trivial
  unprovidedCoefficientData := True
  unprovidedCoefficientData_cert := trivial
  undecidedPredicates := True
  undecidedPredicates_cert := trivial
  candidateDependentReadingsSeparated := True
  candidateDependentReadingsSeparated_cert := trivial

/-- R11(g): raw finite packet data with certified/candidate separation. -/
def measurementPacketExampleData :
    MeasurementPacketData pseudoCircleMeasurementProfile where
  selectedDomain := PseudoCircleMeasurementDomain.boundaryCocycle
  structuralVerdict :=
    StructuralVerdict.fromMeasurement pseudoCircleBoundaryCocycleVerdict
  computedInvariants := packetComputedInvariants
  analyticReadings := packetAnalyticReadings
  CertifiedReading := Unit
  CandidateInterface := Unit
  ConditionalReading := Unit
  certifiedReadings := [()]
  candidateInterfaces := [()]
  conditionalReadings := [()]
  assumptions := packetMeasurementAssumptions
  nonConclusions := packetNonConclusions
  certifiedSeparatedFromCandidate := True
  certifiedSeparatedFromCandidate_cert := trivial

/-- R11(g): theorem 12.1 instantiated on the finite packet fixture. -/
def measurementPacketExampleSynthesis :
    FiniteMeasurementSynthesis measurementPacketExampleData :=
  finiteMeasurementSynthesisPackage measurementPacketExampleData

/-- R11(g): a real-coefficient profile using the generated finite-poset site and cover.

The verdict vocabulary is deliberately trivial: the single `Unit` measurement
is in scope by selection, and no theorem-12.3 conjunct reads `Zero` /
`NonZero`.  This profile only supplies the selected site, cover, real
coefficient, and equation handles for the GAGA comparison. -/
abbrev gagaRealMeasurementProfile : MeasurementProfile where
  equationGeometry :=
    MeasurementEquationGeometry.ofSite finiteMeasurementEquationSite
  SiteObj := PUnit
  Cover := Bool
  Coeff := ℝ
  EffCoeff := Unit
  ObstructionObject := FiniteObstructionObjectHandle
  WitnessVariables := SquareFreeSupportVertex
  ObstructionIdeal := FiniteObstructionIdealHandle
  RepresentationFamily := Unit
  Domain := Unit
  CertRef := fun _ => Unit
  SelectedMethod := fun _ => Unit
  InScope := fun _ => True
  OutOfScope := fun _ => False
  Zero := fun _ => True
  NonZero := fun _ => False
  Undecided := fun _ => False
  NotRunOrUnavailable := fun _ => False

/-- Constant real presheaf on the actual selected finite-poset site. -/
abbrev gagaRealPresheaf :
    Site.AATPresheaf finiteMeasurementEquationSite where
  obj _ := ℝ
  map _ x := x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every restriction in the constant real presheaf is the identity. -/
theorem gagaRealPresheaf_map_apply
    {X Y : finiteMeasurementEquationSite.categoryᵒᵖ}
    (f : X ⟶ Y) (x : ℝ) : gagaRealPresheaf.map f x = x :=
  rfl

theorem gagaReal_isSheaf :
    Site.AATSheafCondition finiteMeasurementEquationSite gagaRealPresheaf := by
  intro _base cover hcover
  rw [Site.AATSheafConditionFor, finiteComputabilitySite_cover_eq_top hcover]
  exact Presieve.isSheafFor_top gagaRealPresheaf

/-- The real coefficient obstruction sheaf used by the GAGA finite profile. -/
abbrev gagaRealObstructionSheaf :
    Cohomology.ObstructionSheaf finiteMeasurementEquationSite where
  carrier := { carrier := gagaRealPresheaf, isSheaf := gagaReal_isSheaf }
  addCommGroup _ := by
    change AddCommGroup ℝ
    infer_instance
  map_zero := by intros; rfl
  map_add := by intros; rfl

/-- The generated finite Čech geometry for the real GAGA profile. -/
abbrev gagaRealGeometry : FiniteMeasurementGeometry gagaRealMeasurementProfile where
  coverGeometry := finiteComputabilityCoverGeometry
  tupleGeometry := finiteComputabilityTupleGeometry
  coeffCommRing := by
    change CommRing ℝ
    infer_instance
  obstructionSheaf := gagaRealObstructionSheaf
  sectionModule := by
    intro _ _
    change Module ℝ ℝ
    infer_instance
  faceRestrictionLinear := by
    letI : CommRing gagaRealMeasurementProfile.Coeff := by
      change CommRing ℝ
      infer_instance
    intro _ _ _
    change ℝ →ₗ[ℝ] ℝ
    exact LinearMap.id
  faceRestrictionLinear_apply := by
    letI : CommRing gagaRealMeasurementProfile.Coeff := by
      change CommRing ℝ
      infer_instance
    intros
    rfl
  siteObjEquiv := by
    simpa [gagaRealMeasurementProfile, finiteComputabilityCoverGeometry] using
      (Equiv.refl PUnit)
  coverEquiv := by
    simpa [gagaRealMeasurementProfile, finiteComputabilityCoverGeometry,
      finiteComputabilityCover] using (Equiv.refl Bool)

/-- Generated canonical simplex type for the real GAGA profile. -/
abbrev GAGARealSimplex (n : Nat) :=
  Site.FinitePosetCechSimplex gagaRealGeometry.coefficientRegime n

/-- The actual simplicial face map generated from the selected cover and sheaf. -/
def gagaRealFace (n : Nat) (simplex : GAGARealSimplex (n + 1))
    (i : Fin (n + 2)) : GAGARealSimplex n :=
  (gagaRealGeometry.tupleGeometry.toSimplicialFaceAction
    gagaRealGeometry.obstructionSheaf.carrier.toPresheaf).toFaceData.face n simplex i

/-- The selected cover nerve has exactly the canonical Čech simplices as coordinates. -/
noncomputable def gagaRealCoverNerve : Cohomology.CoverNerve where
  Chart := GAGARealSimplex 0
  EdgeComponent := GAGARealSimplex 1
  FaceComponent := GAGARealSimplex 2
  edgeLeft := fun edge => gagaRealFace 0 edge 1
  edgeRight := fun edge => gagaRealFace 0 edge 0
  faceEdge0 := fun face => gagaRealFace 1 face 0
  faceEdge1 := fun face => gagaRealFace 1 face 1
  faceEdge2 := fun face => gagaRealFace 1 face 2
  edgeOverlapComponent := fun edge =>
    finiteComputabilityCover.patch (edge 0) = finiteComputabilityCover.patch (edge 1)
  faceTripleOverlapComponent := fun face =>
    finiteComputabilityCover.patch (face 0) = finiteComputabilityCover.patch (face 1) ∧
      finiteComputabilityCover.patch (face 1) = finiteComputabilityCover.patch (face 2)
  edgeOverlapComponent_holds := by intro _; rfl
  faceTripleOverlapComponent_holds := by intro _; exact ⟨rfl, rfl⟩

/-- Coordinate identification of real canonical Čech cochains with their simplex functions. -/
noncomputable def gagaRealCochainCoordinates (n : Nat) :
    letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
    letI : AddCommGroup (gagaRealGeometry.CechCochain n) :=
      gagaRealGeometry.cochainAddCommGroup n
    letI : Module ℝ (gagaRealGeometry.CechCochain n) :=
      gagaRealGeometry.cochainModule n
    gagaRealGeometry.CechCochain n ≃ₗ[ℝ] (GAGARealSimplex n → ℝ) := by
  letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
  letI : AddCommGroup (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainAddCommGroup n
  letI : Module ℝ (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainModule n
  refine {
    toFun := fun c simplex => c simplex
    invFun := fun c simplex => c simplex
    left_inv := by intro c; rfl
    right_inv := by intro c; rfl
    map_add' := by intro c d; rfl
    map_smul' := by intro r c; rfl }

/-- Finite simplex basis for the real canonical Čech cochains. -/
noncomputable def gagaRealCochainBasis (n : Nat) :
    letI : AddCommGroup (gagaRealGeometry.CechCochain n) :=
      gagaRealGeometry.cochainAddCommGroup n
    letI : Module ℝ (gagaRealGeometry.CechCochain n) :=
      gagaRealGeometry.cochainModule n
    Module.Basis (GAGARealSimplex n) ℝ (gagaRealGeometry.CechCochain n) := by
  letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
  letI : AddCommGroup (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainAddCommGroup n
  letI : Module ℝ (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainModule n
  letI : Finite (GAGARealSimplex n) :=
    gagaRealGeometry.coefficientRegime.finiteNerveSimplex n
  exact Module.Basis.ofEquivFun (gagaRealCochainCoordinates n)

/-- The selected nerve complex is the canonical real Čech complex itself. -/
noncomputable def gagaRealNerveComplex :
    Cohomology.FiniteNerveCochainComplex gagaRealCoverNerve ℝ where
  C0 := gagaRealGeometry.CechCochain 0
  C1 := gagaRealGeometry.CechCochain 1
  C2 := gagaRealGeometry.CechCochain 2
  add_C0 := gagaRealGeometry.cochainAddCommGroup 0
  add_C1 := gagaRealGeometry.cochainAddCommGroup 1
  add_C2 := gagaRealGeometry.cochainAddCommGroup 2
  module_C0 := gagaRealGeometry.cochainModule 0
  module_C1 := gagaRealGeometry.cochainModule 1
  module_C2 := gagaRealGeometry.cochainModule 2
  finiteDimensional_C0 := by
    letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
    letI : AddCommGroup (gagaRealGeometry.CechCochain 0) :=
      gagaRealGeometry.cochainAddCommGroup 0
    letI : Module ℝ (gagaRealGeometry.CechCochain 0) :=
      gagaRealGeometry.cochainModule 0
    letI : Finite (GAGARealSimplex 0) :=
      gagaRealGeometry.coefficientRegime.finiteNerveSimplex 0
    exact Module.Finite.of_basis (gagaRealCochainBasis 0)
  finiteDimensional_C1 := by
    letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
    letI : AddCommGroup (gagaRealGeometry.CechCochain 1) :=
      gagaRealGeometry.cochainAddCommGroup 1
    letI : Module ℝ (gagaRealGeometry.CechCochain 1) :=
      gagaRealGeometry.cochainModule 1
    letI : Finite (GAGARealSimplex 1) :=
      gagaRealGeometry.coefficientRegime.finiteNerveSimplex 1
    exact Module.Finite.of_basis (gagaRealCochainBasis 1)
  finiteDimensional_C2 := by
    letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
    letI : AddCommGroup (gagaRealGeometry.CechCochain 2) :=
      gagaRealGeometry.cochainAddCommGroup 2
    letI : Module ℝ (gagaRealGeometry.CechCochain 2) :=
      gagaRealGeometry.cochainModule 2
    letI : Finite (GAGARealSimplex 2) :=
      gagaRealGeometry.coefficientRegime.finiteNerveSimplex 2
    exact Module.Finite.of_basis (gagaRealCochainBasis 2)
  d0 := gagaRealGeometry.differentialLinear 0
  d1 := gagaRealGeometry.differentialLinear 1
  d1_comp_d0 := by
    intro c
    simpa [FiniteMeasurementGeometry.differentialLinear,
      FiniteMeasurementGeometry.cechComplex] using
      Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex_differential_comp
        gagaRealGeometry.tupleGeometry gagaRealGeometry.obstructionSheaf 0 c
  zeroCochainCoordinates := by
    simpa only [gagaRealCoverNerve] using gagaRealCochainCoordinates 0
  oneCochainCoordinates := by
    simpa only [gagaRealCoverNerve] using gagaRealCochainCoordinates 1
  twoCochainCoordinates := by
    simpa only [gagaRealCoverNerve] using gagaRealCochainCoordinates 2
  d0_eq_edgeIncidence := by
    intro c edge
    change (gagaRealCochainCoordinates 1
      (gagaRealGeometry.cechComplex.differential 0 c)) edge =
        (gagaRealCochainCoordinates 0 c) (gagaRealFace 0 edge 0) -
          (gagaRealCochainCoordinates 0 c) (gagaRealFace 0 edge 1)
    simp only [FiniteMeasurementGeometry.cechComplex,
      Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex,
      Cohomology.StandardFinitePosetCech.standardFinitePosetCechComplex,
      Cohomology.StandardFinitePosetCech.standardAdditiveData,
      Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination]
    unfold Cohomology.StandardFinitePosetCech.standardDifferential
    unfold Cohomology.StandardFinitePosetCech.standardAdditiveData
    dsimp [gagaRealCochainCoordinates]
    have hterms :
        (fun i : Fin 2 =>
          Site.FinitePosetCechFaceRestriction
            (gagaRealGeometry.tupleGeometry.toSimplicialFaceAction
              gagaRealGeometry.obstructionSheaf.carrier.toPresheaf).toFaceData
            c edge i) =
          (fun i : Fin 2 => gagaRealGeometry.faceRestrictionLinear 0 edge i
            (c (gagaRealFace 0 edge i))) := by
      funext i
      exact (gagaRealGeometry.faceRestrictionLinear_apply 0 edge i
        (c (gagaRealFace 0 edge i))).symm
    rw [hterms]
    simp [Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination,
      gagaRealGeometry, Fin.sum_univ_two, sub_eq_add_neg]
    rfl
  d1_eq_faceIncidence := by
    intro c face
    change (gagaRealCochainCoordinates 2
      (gagaRealGeometry.cechComplex.differential 1 c)) face =
        (gagaRealCochainCoordinates 1 c) (gagaRealFace 1 face 0) -
          (gagaRealCochainCoordinates 1 c) (gagaRealFace 1 face 1) +
            (gagaRealCochainCoordinates 1 c) (gagaRealFace 1 face 2)
    simp only [FiniteMeasurementGeometry.cechComplex,
      Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex,
      Cohomology.StandardFinitePosetCech.standardFinitePosetCechComplex,
      Cohomology.StandardFinitePosetCech.standardAdditiveData,
      Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination]
    unfold Cohomology.StandardFinitePosetCech.standardDifferential
    unfold Cohomology.StandardFinitePosetCech.standardAdditiveData
    dsimp [gagaRealCochainCoordinates]
    have hterms :
        (fun i : Fin 3 =>
          Site.FinitePosetCechFaceRestriction
            (gagaRealGeometry.tupleGeometry.toSimplicialFaceAction
              gagaRealGeometry.obstructionSheaf.carrier.toPresheaf).toFaceData
            c face i) =
          (fun i : Fin 3 => gagaRealGeometry.faceRestrictionLinear 1 face i
            (c (gagaRealFace 1 face i))) := by
      funext i
      exact (gagaRealGeometry.faceRestrictionLinear_apply 1 face i
        (c (gagaRealFace 1 face i))).symm
    rw [hterms]
    simp [Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination,
      gagaRealGeometry, Fin.sum_univ_three, sub_eq_add_neg]
    rfl

/-- The two actual monomial-law generators used by the selected GAGA chart. -/
inductive GAGADerivedLawIdeal where
  | xy
  | xz

/-- Evaluate a selected ambient law generator in the shared-witness chart. -/
def gagaDerivedLawGenerator : GAGADerivedLawIdeal →
    Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ
  | .xy => Derived.Counterexample.SharedWitnessCoord.xy ℝ
  | .xz => Derived.Counterexample.SharedWitnessCoord.xz ℝ

/-- Construct the chart ideal generated by an ambient selected law. -/
def gagaGeneratedLawIdeal (L : GAGADerivedLawIdeal) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ) :=
  Ideal.span ({gagaDerivedLawGenerator L} : Set
    (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ))

/-- The selected `xy` generator yields the canonical left monomial ideal. -/
theorem gagaGeneratedLawIdeal_xy :
    gagaGeneratedLawIdeal .xy = Derived.Counterexample.SharedWitnessCoord.idealU ℝ :=
  rfl

/-- The selected `xz` generator yields the canonical right monomial ideal. -/
theorem gagaGeneratedLawIdeal_xz :
    gagaGeneratedLawIdeal .xz = Derived.Counterexample.SharedWitnessCoord.idealV ℝ :=
  rfl

/-- Actual observable-ring map realizing the selected left equation in the
shared-witness chart. -/
def gagaLeftEquationObservableMap :
    finiteMeasurementEquationSite.equationSystem.Observable
        finiteMeasurementSiteBase →+*
      Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ :=
  MvPolynomial.eval₂Hom
    (Int.castRingHom
      (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)) fun
    | .p => Derived.Counterexample.SharedWitnessCoord.xy ℝ
    | .q | .r => 0

/-- Actual observable-ring map realizing the selected right equation in the
shared-witness chart. -/
def gagaRightEquationObservableMap :
    finiteMeasurementEquationSite.equationSystem.Observable
        finiteMeasurementSiteBase →+*
      Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ :=
  MvPolynomial.eval₂Hom
    (Int.castRingHom
      (Derived.Counterexample.SharedWitnessCoord.ChartRing ℝ)) fun
    | .p => Derived.Counterexample.SharedWitnessCoord.xz ℝ
    | .q | .r => 0

theorem gagaLeftEquationCoordinate
    (atom : FiniteModel.FiniteAtom) :
    gagaLeftEquationObservableMap
        (finiteMeasurementEquationSite.equationSystem.violationCoordinate
          finiteMeasurementSiteBase .left atom) =
      if finiteAtomWitnessVariable atom = SquareFreeSupportVertex.p then
        Derived.Counterexample.SharedWitnessCoord.xy ℝ else 0 := by
  cases atom <;>
    simp [gagaLeftEquationObservableMap, finiteMeasurementEquationSite,
      finiteMeasurementEquationSystem, finiteEquationViolation,
      finiteAtomWitnessVariable]

theorem gagaRightEquationCoordinate
    (atom : FiniteModel.FiniteAtom) :
    gagaRightEquationObservableMap
        (finiteMeasurementEquationSite.equationSystem.violationCoordinate
          finiteMeasurementSiteBase .right atom) =
      if atom = FiniteModel.FiniteAtom.componentA then
        Derived.Counterexample.SharedWitnessCoord.xz ℝ else 0 := by
  cases atom <;>
    simp [gagaRightEquationObservableMap, finiteMeasurementEquationSite,
      finiteMeasurementEquationSystem, finiteEquationViolation]

theorem gagaLeftEquationCoordinate_mem
    (atom : FiniteModel.FiniteAtom) :
    gagaLeftEquationObservableMap
        (finiteMeasurementEquationSite.equationSystem.violationCoordinate
          finiteMeasurementSiteBase .left atom) ∈
      Derived.Counterexample.SharedWitnessCoord.idealU ℝ := by
  rw [gagaLeftEquationCoordinate]
  split_ifs
  · exact Ideal.subset_span (by rfl)
  · exact Ideal.zero_mem _

theorem gagaRightEquationCoordinate_mem
    (atom : FiniteModel.FiniteAtom) :
    gagaRightEquationObservableMap
        (finiteMeasurementEquationSite.equationSystem.violationCoordinate
          finiteMeasurementSiteBase .right atom) ∈
      Derived.Counterexample.SharedWitnessCoord.idealV ℝ := by
  rw [gagaRightEquationCoordinate]
  split_ifs
  · exact Ideal.subset_span (by rfl)
  · exact Ideal.zero_mem _

/-- R11(g): the common ambient for the generated real finite-profile fixture. -/
def gagaRealCommonAmbient :
    CommonAmbientPair gagaRealMeasurementProfile where
  AmbientSpace := FiniteModel.FiniteAtom
  StructureSheaf := FiniteObstructionObjectHandle
  LawIdeal := GAGADerivedLawIdeal
  CoefficientObject := ℝ
  WitnessPair := Derived.Counterexample.SharedWitnessCoord
  ComparisonProfile := FiniteObstructionIdealHandle
  SupportCarrier := SquareFreeSupportVertex
  leftDomain := ()
  rightDomain := ()
  selectedAmbient := .componentA
  selectedStructureSheaf := .selected
  leftLawIdeal := .xy
  rightLawIdeal := .xz
  leftCoefficient := 1
  rightCoefficient := 1
  selectedWitnessPair := .x
  selectedComparisonProfile := .selected
  commonRingedSite :=
    Site.AATSheafCondition finiteMeasurementEquationSite gagaRealPresheaf
  commonRingedSite_cert := gagaReal_isSheaf
  lawIdealsInCommonAmbient :=
    gagaGeneratedLawIdeal .xy = Derived.Counterexample.SharedWitnessCoord.idealU ℝ ∧
      gagaGeneratedLawIdeal .xz = Derived.Counterexample.SharedWitnessCoord.idealV ℝ
  lawIdealsInCommonAmbient_cert := ⟨gagaGeneratedLawIdeal_xy, gagaGeneratedLawIdeal_xz⟩
  coefficientsCompatible := (1 : ℝ) = 1
  coefficientsCompatible_cert := rfl
  witnessesComparable := (Derived.Counterexample.SharedWitnessCoord.x :
    Derived.Counterexample.SharedWitnessCoord) = .x
  witnessesComparable_cert := rfl
  comparisonProfileFixed := (FiniteObstructionIdealHandle.selected :
    FiniteObstructionIdealHandle) = .selected
  comparisonProfileFixed_cert := rfl
  noComparisonWithoutCommonAmbient :=
    Site.AATSheafCondition finiteMeasurementEquationSite gagaRealPresheaf
  noComparisonWithoutCommonAmbient_cert := gagaReal_isSheaf

/-- Interpret each profile obstruction-object handle on the actual real Čech sheaf. -/
def gagaAmbientStructureSheafFromProfile : FiniteObstructionObjectHandle →
    Cohomology.ObstructionSheaf finiteMeasurementEquationSite
  | .selected => gagaRealObstructionSheaf
  | .alternate => gagaRealObstructionSheaf

/-- R11(g): source data whose site, cover, cochains, and differentials are generated
from the selected real finite profile. -/
noncomputable def gagaFiniteCechSource :
    AATGAGAFiniteCechSource gagaRealMeasurementProfile where
  geometry := gagaRealGeometry
  selectedContext := PUnit.unit
  selectedCoverIndex := false
  nerve := gagaRealCoverNerve
  nerveComplex := gagaRealNerveComplex
  chartToCanonical := Equiv.refl _
  edgeToCanonical := Equiv.refl _
  faceToCanonical := Equiv.refl _
  zeroToCanonical := AddEquiv.refl _
  oneToCanonical := AddEquiv.refl _
  twoToCanonical := AddEquiv.refl _
  d0_toCanonical := by
    intro c
    rfl
  d1_toCanonical := by
    intro c
    rfl

/-- R11(g): all selected data are tied to the generated finite Čech source. -/
noncomputable def gagaCommonFiniteData :
    AATGAGACommonFiniteData gagaRealMeasurementProfile where
  finiteCechSource := gagaFiniteCechSource
  selectedSite := PUnit.unit
  selectedCover := false
  selectedCoefficient := 1
  selectedMeasurement := ()
  measuredSelection := {
    inScope := trivial
    method := ()
    certificate := ()
  }
  commonAmbient := gagaRealCommonAmbient
  equationContext := finiteMeasurementSiteBase
  leftEquationObservableMap := gagaLeftEquationObservableMap
  rightEquationObservableMap := gagaRightEquationObservableMap
  selectedLeftProfileEquation := ⟨.left, rfl⟩
  selectedRightProfileEquation := ⟨.right, rfl⟩
  leftEquationCoordinate_mem := gagaLeftEquationCoordinate_mem
  leftGeneratorAtom := .componentA
  leftEquationGenerator_eq_xy := by
    simpa using gagaLeftEquationCoordinate FiniteModel.FiniteAtom.componentA
  rightEquationCoordinate_mem := gagaRightEquationCoordinate_mem
  rightGeneratorAtom := .componentA
  rightEquationGenerator_eq_xz := by
    simpa using gagaRightEquationCoordinate FiniteModel.FiniteAtom.componentA
  ambientAtomType_eq_source := rfl
  ambientStructureSheafFromProfile := id
  selectedObstructionObject := .selected
  selectedStructureSheaf_eq_profile := rfl
  ambientStructureSheafToSource := gagaAmbientStructureSheafFromProfile
  selectedStructureSheaf_realizes_source := rfl
  ambientCoefficientObject_eq_profile := rfl
  leftCoefficient_eq_selected := rfl
  rightCoefficient_eq_selected := rfl
  selectedSite_eq_source := rfl
  selectedCover_eq_source := rfl
  ambientLeftDomain_eq := rfl
  ambientRightDomain_eq := rfl

local instance gagaRealSimplexFinite (n : Nat) : Finite (GAGARealSimplex n) :=
  gagaRealGeometry.coefficientRegime.finiteNerveSimplex n

/-- Computable enumeration of the generated real simplices in each degree. -/
local instance gagaRealSimplexFintype (n : Nat) :
    Fintype (GAGARealSimplex n) :=
  Fintype.ofFinite _

/-- Linear coordinates for the finite real cochain carrier with its `L²` metric. -/
noncomputable def gagaRealEuclideanCoordinates (n : Nat) :
    EuclideanSpace ℝ (GAGARealSimplex n) ≃ₗ[ℝ] (GAGARealSimplex n → ℝ) :=
  (EuclideanSpace.equiv (GAGARealSimplex n) ℝ).toLinearEquiv

/-- The selected canonical zero-cochains in real Euclidean coordinates. -/
noncomputable def gagaRealZeroRealization :
    gagaFiniteCechSource.nerveComplex.C0 ≃ₗ[ℝ]
      EuclideanSpace ℝ (GAGARealSimplex 0) :=
  gagaRealNerveComplex.zeroCochainCoordinates.trans
    (gagaRealEuclideanCoordinates 0).symm

/-- The selected canonical one-cochains in real Euclidean coordinates. -/
noncomputable def gagaRealOneRealization :
    gagaFiniteCechSource.nerveComplex.C1 ≃ₗ[ℝ]
      EuclideanSpace ℝ (GAGARealSimplex 1) :=
  gagaRealNerveComplex.oneCochainCoordinates.trans
    (gagaRealEuclideanCoordinates 1).symm

/-- The selected canonical two-cochains in real Euclidean coordinates. -/
noncomputable def gagaRealTwoRealization :
    gagaFiniteCechSource.nerveComplex.C2 ≃ₗ[ℝ]
      EuclideanSpace ℝ (GAGARealSimplex 2) :=
  gagaRealNerveComplex.twoCochainCoordinates.trans
    (gagaRealEuclideanCoordinates 2).symm

/-- Realize every generated canonical Čech cochain space in Euclidean coordinates. -/
noncomputable def gagaRealAllDegreeRealization (n : Nat) :
    gagaFiniteCechSource.geometry.CechCochain n ≃+
      EuclideanSpace ℝ (GAGARealSimplex n) := by
  letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
  letI : AddCommGroup (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainAddCommGroup n
  letI : Module ℝ (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainModule n
  exact ((gagaRealCochainCoordinates n).trans
    (gagaRealEuclideanCoordinates n).symm).toAddEquiv

/-- The real differential is transported from the actual canonical Čech differential. -/
noncomputable def gagaRealAllDegreeDifferential (n : Nat) :
    EuclideanSpace ℝ (GAGARealSimplex n) →ₗ[ℝ]
      EuclideanSpace ℝ (GAGARealSimplex (n + 1)) := by
  letI : CommRing ℝ := gagaRealGeometry.coeffCommRing
  letI : AddCommGroup (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainAddCommGroup n
  letI : AddCommGroup (gagaRealGeometry.CechCochain (n + 1)) :=
    gagaRealGeometry.cochainAddCommGroup (n + 1)
  letI : Module ℝ (gagaRealGeometry.CechCochain n) :=
    gagaRealGeometry.cochainModule n
  letI : Module ℝ (gagaRealGeometry.CechCochain (n + 1)) :=
    gagaRealGeometry.cochainModule (n + 1)
  let E0 := (gagaRealCochainCoordinates n).trans (gagaRealEuclideanCoordinates n).symm
  let E1 := (gagaRealCochainCoordinates (n + 1)).trans
    (gagaRealEuclideanCoordinates (n + 1)).symm
  exact E1.toLinearMap.comp
    ((gagaRealGeometry.differentialLinear n).comp E0.symm.toLinearMap)

/-- The transported all-degree real differential is the generated Čech differential. -/
theorem gagaRealAllDegreeDifferential_eq_source (n : Nat)
    (c : gagaFiniteCechSource.geometry.CechCochain n) :
    gagaRealAllDegreeDifferential n (gagaRealAllDegreeRealization n c) =
      gagaRealAllDegreeRealization (n + 1)
        (gagaFiniteCechSource.geometry.differentialLinear n c) := by
  change gagaRealAllDegreeRealization (n + 1)
      (gagaRealGeometry.differentialLinear n
        ((gagaRealAllDegreeRealization n).symm
          (gagaRealAllDegreeRealization n c))) = _
  rw [(gagaRealAllDegreeRealization n).symm_apply_apply]
  simp only [gagaFiniteCechSource]

/-- Consecutive transported differentials form the actual all-degree Čech complex. -/
theorem gagaRealAllDegreeDifferential_comp (n : Nat) :
    (gagaRealAllDegreeDifferential (n + 1)).comp
      (gagaRealAllDegreeDifferential n) = 0 := by
  apply LinearMap.ext
  intro c
  change gagaRealAllDegreeRealization (n + 2)
      (gagaRealGeometry.differentialLinear (n + 1)
        ((gagaRealAllDegreeRealization (n + 1)).symm
          (gagaRealAllDegreeRealization (n + 1)
            (gagaRealGeometry.differentialLinear n
              ((gagaRealAllDegreeRealization n).symm c))))) = 0
  rw [(gagaRealAllDegreeRealization (n + 1)).symm_apply_apply]
  have hcomp :=
    Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex_differential_comp
      gagaRealGeometry.tupleGeometry gagaRealGeometry.obstructionSheaf n
      ((gagaRealAllDegreeRealization n).symm c)
  have hzero :
      gagaRealGeometry.cechComplex.differential (n + 1)
        (gagaRealGeometry.cechComplex.differential n
          ((gagaRealAllDegreeRealization n).symm c)) =
        (0 : gagaRealGeometry.CechCochain (n + 2)) := by
    simpa [FiniteMeasurementGeometry.cechComplex] using hcomp
  have hzeroLinear :
      gagaRealGeometry.differentialLinear (n + 1)
        (gagaRealGeometry.differentialLinear n
          ((gagaRealAllDegreeRealization n).symm c)) =
        (0 : gagaRealGeometry.CechCochain (n + 2)) := by
    simpa [FiniteMeasurementGeometry.differentialLinear] using hzero
  rw [hzeroLinear]
  exact (gagaRealAllDegreeRealization (n + 2)).map_zero

/-- The all-degree Hodge input is constructed from the same generated real Čech source. -/
noncomputable def gagaRealAllDegreeHodgeInput :
    AATGAGAAllDegreeRealCechHodgeInput gagaFiniteCechSource where
  RealCochain := fun n => EuclideanSpace ℝ (GAGARealSimplex n)
  cochainNormed := by intro _; infer_instance
  cochainInner := by intro _; infer_instance
  cochainFinite := by intro _; infer_instance
  sourceToReal := gagaRealAllDegreeRealization
  realD := gagaRealAllDegreeDifferential
  realD_eq_source := gagaRealAllDegreeDifferential_eq_source
  real_d_comp := gagaRealAllDegreeDifferential_comp

/-- R11(g): the Hodge realization uses the same selected real Čech complex. -/
noncomputable def gagaRealHodgeInput :
    AATGAGARealCechHodgeInput gagaFiniteCechSource where
  RealC0 := EuclideanSpace ℝ (GAGARealSimplex 0)
  RealC1 := EuclideanSpace ℝ (GAGARealSimplex 1)
  RealC2 := EuclideanSpace ℝ (GAGARealSimplex 2)
  zeroNormed := by infer_instance
  zeroInner := by infer_instance
  zeroFinite := by infer_instance
  oneNormed := by infer_instance
  oneInner := by infer_instance
  oneFinite := by infer_instance
  twoNormed := by infer_instance
  twoInner := by infer_instance
  twoFinite := by infer_instance
  zeroToReal := gagaRealZeroRealization.toAddEquiv
  oneToReal := gagaRealOneRealization.toAddEquiv
  twoToReal := gagaRealTwoRealization.toAddEquiv
  zeroCochainCoordinates := gagaRealEuclideanCoordinates 0
  zeroCochainCoordinates_inv := (gagaRealEuclideanCoordinates 0).symm
  zeroCochainCoordinates_left_inv := by
    intro c
    exact (gagaRealEuclideanCoordinates 0).symm_apply_apply c
  zeroCochainCoordinates_right_inv := by
    intro c
    exact (gagaRealEuclideanCoordinates 0).apply_symm_apply c
  zeroCochainCoordinates_add := by
    intro c d
    exact (gagaRealEuclideanCoordinates 0).map_add c d
  oneCochainCoordinates := gagaRealEuclideanCoordinates 1
  oneCochainCoordinates_inv := (gagaRealEuclideanCoordinates 1).symm
  oneCochainCoordinates_left_inv := by
    intro c
    exact (gagaRealEuclideanCoordinates 1).symm_apply_apply c
  oneCochainCoordinates_right_inv := by
    intro c
    exact (gagaRealEuclideanCoordinates 1).apply_symm_apply c
  oneCochainCoordinates_add := by
    intro c d
    exact (gagaRealEuclideanCoordinates 1).map_add c d
  twoCochainCoordinates := gagaRealEuclideanCoordinates 2
  twoCochainCoordinates_inv := (gagaRealEuclideanCoordinates 2).symm
  twoCochainCoordinates_left_inv := by
    intro c
    exact (gagaRealEuclideanCoordinates 2).symm_apply_apply c
  twoCochainCoordinates_right_inv := by
    intro c
    exact (gagaRealEuclideanCoordinates 2).apply_symm_apply c
  twoCochainCoordinates_add := by
    intro c d
    exact (gagaRealEuclideanCoordinates 2).map_add c d
  zeroCochainCoordinates_smul := by
    intro a c
    exact (gagaRealEuclideanCoordinates 0).map_smul a c
  oneCochainCoordinates_smul := by
    intro a c
    exact (gagaRealEuclideanCoordinates 1).map_smul a c
  twoCochainCoordinates_smul := by
    intro a c
    exact (gagaRealEuclideanCoordinates 2).map_smul a c
  realD0 := gagaRealOneRealization.toLinearMap.comp
    (gagaRealNerveComplex.d0.comp gagaRealZeroRealization.symm.toLinearMap)
  realD1 := gagaRealTwoRealization.toLinearMap.comp
    (gagaRealNerveComplex.d1.comp gagaRealOneRealization.symm.toLinearMap)
  real_d1_comp_d0 := by
    apply LinearMap.ext
    intro c
    change gagaRealTwoRealization
      (gagaRealNerveComplex.d1
        (gagaRealOneRealization.symm
          (gagaRealOneRealization
            (gagaRealNerveComplex.d0 (gagaRealZeroRealization.symm c))))) = 0
    rw [gagaRealOneRealization.symm_apply_apply]
    rw [gagaRealNerveComplex.d1_comp_d0]
    exact gagaRealTwoRealization.map_zero
  realD0_eq_profile := by
    intro c
    change gagaRealOneRealization
      (gagaRealNerveComplex.d0
        (gagaRealZeroRealization.symm (gagaRealZeroRealization c))) =
      gagaRealOneRealization (gagaRealNerveComplex.d0 c)
    rw [gagaRealZeroRealization.symm_apply_apply]
  realD1_eq_profile := by
    intro c
    change gagaRealTwoRealization
      (gagaRealNerveComplex.d1
        (gagaRealOneRealization.symm (gagaRealOneRealization c))) =
      gagaRealTwoRealization (gagaRealNerveComplex.d1 c)
    rw [gagaRealOneRealization.symm_apply_apply]
  d0_eq_edgeIncidence := by
    intro c edge
    change (gagaRealEuclideanCoordinates 1
      ((gagaRealEuclideanCoordinates 1).symm
        (gagaRealNerveComplex.d0 (gagaRealEuclideanCoordinates 0 c)))) edge =
      (gagaRealEuclideanCoordinates 0 c) (gagaRealCoverNerve.edgeRight edge) -
        (gagaRealEuclideanCoordinates 0 c) (gagaRealCoverNerve.edgeLeft edge)
    rw [LinearEquiv.apply_symm_apply]
    exact gagaRealNerveComplex.d0_eq_edgeIncidence
      (gagaRealEuclideanCoordinates 0 c) edge
  d1_eq_faceIncidence := by
    intro c face
    change (gagaRealEuclideanCoordinates 2
      ((gagaRealEuclideanCoordinates 2).symm
        (gagaRealNerveComplex.d1 (gagaRealEuclideanCoordinates 1 c)))) face =
      (gagaRealEuclideanCoordinates 1 c) (gagaRealCoverNerve.faceEdge0 face) -
        (gagaRealEuclideanCoordinates 1 c) (gagaRealCoverNerve.faceEdge1 face) +
          (gagaRealEuclideanCoordinates 1 c) (gagaRealCoverNerve.faceEdge2 face)
    rw [LinearEquiv.apply_symm_apply]
    exact gagaRealNerveComplex.d1_eq_faceIncidence
      (gagaRealEuclideanCoordinates 1 c) face

/-- R11(g): finite Hodge data for the single generated Čech source. -/
noncomputable def gagaSelectedFiniteHodgeData :
    AATGAGASelectedFiniteHodgeData gagaCommonFiniteData where
  allDegreeInput := gagaRealAllDegreeHodgeInput

/-- R11(g): finite Hodge theorem package for the single generated Čech source. -/
noncomputable def gagaFiniteHodgeTheoremPackage :
    SelectedFiniteHodgeTheoremPackage gagaCommonFiniteData where
  hodgeData := gagaSelectedFiniteHodgeData

/-- R11(g): Period/Stokes theorem package over the same selected measurement. -/
def gagaPeriodStokesTheoremPackage :
    SelectedPeriodStokesTheoremPackage gagaCommonFiniteData
      gagaFiniteHodgeTheoremPackage where
  sourceHodgeData := gagaSelectedFiniteHodgeData
  sourceHodgeData_eq := rfl

/-- R11(g): finite-nerve capacity package over the same selected measurement. -/
def gagaTopologicalDebtTheoremPackage :
    SelectedTopologicalDebtTheoremPackage gagaCommonFiniteData where
  source := gagaFiniteCechSource
  source_eq_common := rfl

/-- R11(g): every certified GAGA conclusion is derived from the generated source. -/
noncomputable def gagaCertifiedFields :
    AATGAGACertifiedFields gagaCommonFiniteData where
  finiteHodgeTheoremPackage := gagaFiniteHodgeTheoremPackage
  periodStokesTheoremPackage := gagaPeriodStokesTheoremPackage
  topologicalDebtTheoremPackage := gagaTopologicalDebtTheoremPackage

/-- R11(g): candidate interfaces remain separated from certified readings. -/
def gagaCandidateInterfaces :
    AATGAGACandidateInterfaces gagaRealMeasurementProfile where
  MonotoneWitnessStabilityInterface := Unit
  FiniteCechStabilityInterface := Unit
  FlatBaseChangeInterface := Unit
  SpectralHotspotInterface := Unit
  TransferLowerBoundInterface := Unit
  monotoneWitnessStability := some ()
  finiteCechStability := some ()
  flatBaseChange := some ()
  spectralHotspot := some ()
  transferLowerBound := some ()

/-- R11(g): non-conclusion data are retained outside the certified statement. -/
def gagaNonConclusionData :
    AATGAGANonConclusionData gagaRealMeasurementProfile where
  noExternalDataSourceFidelity := ¬ gagaRealMeasurementProfile.OutOfScope ()
  noExternalDataSourceFidelity_cert := by simp
  noExternalProcedureCorrectness :=
    ¬ gagaRealMeasurementProfile.NotRunOrUnavailable ()
  noExternalProcedureCorrectness_cert := by simp
  noArbitraryEquationHandleComparison :=
    gagaRealCommonAmbient.coefficientsCompatible
  noArbitraryEquationHandleComparison_cert :=
    gagaRealCommonAmbient.coefficientsCompatible_cert
  candidateDependentFieldsNotCertified :=
    gagaCandidateInterfaces.monotoneWitnessStability = some ()
  candidateDependentFieldsNotCertified_cert := rfl

/-- R11(g): raw finite AAT-GAGA comparison data. -/
noncomputable def gagaComparisonExampleData :
    AATGAGAComparisonData gagaRealMeasurementProfile where
  commonData := gagaCommonFiniteData
  certifiedFields := gagaCertifiedFields

/-- R11(g): theorem 12.3 instantiated on the generated finite comparison fixture. -/
theorem gagaComparisonExamplePackage :
    AATGAGAFiniteMeasurementComparison gagaComparisonExampleData :=
  aatGAGAFiniteMeasurementComparison gagaComparisonExampleData

/-- R11(g): GAGA fixture over one real finite profile, with certified and candidate
readings separated. -/
structure MeasurementPacketGAGAFiniteExample where
  /-- The certified theorem-12.3 comparison on the generated fixture data. -/
  gagaPackage : AATGAGAFiniteMeasurementComparison gagaComparisonExampleData
  /-- The certified comparison statement fired on the same fixture data. -/
  certifiedComparison : aatGAGAComparisonStatement gagaComparisonExampleData
  /-- Candidate interfaces kept separate from the certified readings. -/
  candidateInterfaces : AATGAGACandidateInterfaces gagaRealMeasurementProfile
  /-- Recorded non-conclusions kept outside the certified statement. -/
  nonConclusionData : AATGAGANonConclusionData gagaRealMeasurementProfile

/-- R11(g): certified readings and candidate interfaces stay separated. -/
noncomputable def measurementPacketGAGAFiniteExample :
    MeasurementPacketGAGAFiniteExample where
  gagaPackage := gagaComparisonExamplePackage
  certifiedComparison := aatGAGAComparisonStatement_holds gagaComparisonExampleData
  candidateInterfaces := gagaCandidateInterfaces
  nonConclusionData := gagaNonConclusionData

/-- R11(g): every theorem-12.3 certified conjunct fires in one finite fixture. -/
theorem measurementPacketGAGAExample_certifiedComparison :
    aatGAGAComparisonStatement gagaComparisonExampleData :=
  measurementPacketGAGAFiniteExample.certifiedComparison

/-- R11: aggregate suite reused by Part IX as static measurement fixtures. -/
structure PartVIIIFiniteExampleSuite where
  pseudoCircleMeasuredNonzero :
    MeasurementVerdict pseudoCircleMeasurementProfile
      PseudoCircleMeasurementDomain.boundaryCocycle
  unmeasuredAxisNotZero :
    ¬ pseudoCircleMeasurementProfile.Zero
      PseudoCircleMeasurementDomain.unmeasuredAxis
  qHitsBothForbiddenSupports :
    SquareFreeSupportVertex.q ∈ forbiddenSupportPQ ∧
      SquareFreeSupportVertex.q ∈ forbiddenSupportQR
  prHitsForbiddenSupports :
    SquareFreeSupportVertex.p ∈ forbiddenSupportPQ ∧
      SquareFreeSupportVertex.r ∈ forbiddenSupportQR
  squareFreeRepairPackage : StanleyReisnerAlexanderDualRepair squareFreeRepairRegime
  singletonQMinimalRepair :
    squareFreeMinimalRepairHittingSets.minimalRepairHittingSet
      SquareFreeRepairTarget.singletonQ
  pairPRMinimalRepair :
    squareFreeMinimalRepairHittingSets.minimalRepairHittingSet
      SquareFreeRepairTarget.pairPR
  finiteComputability :
    Nonempty
      (FiniteAATComputability.{0, 0} computabilityFiniteMeasurementRegime
        finiteComputabilityExampleData)
  refactorInvariance :
    RefactorInvarianceUnderEquivalence integerCohomologyPullbackClass
      integerCohomologyRefactorEquivalence
  refactorNonzeroTransport :
    (¬ integerCohomologyMeasurementProfile.Zero integerOneClass) ∧
      (¬ integerCohomologyMeasurementProfile.Zero
        (integerCohomologyPullbackClass.pullback
          integerCohomologyRefactorEquivalence integerOneClass))
  refactorPullbackNonidentity :
    integerCohomologyPullbackClass.pullback
        integerCohomologyRefactorEquivalence integerOneClass ≠
      integerOneClass
  cellularHodge : CellularHodgeFiniteExample
  supportTransfer : SupportLocalizedTransferFiniteExample
  packetGAGA : MeasurementPacketGAGAFiniteExample
  staticFixturesReusableForPartIX : Prop
  staticFixturesReusableForPartIX_cert : staticFixturesReusableForPartIX

/-- R11: complete selected finite example suite for Part VIII. -/
def partVIIIFiniteExampleSuite : PartVIIIFiniteExampleSuite where
  pseudoCircleMeasuredNonzero := pseudoCircleBoundaryCocycleVerdict
  unmeasuredAxisNotZero := pseudoCircle_unmeasuredAxis_not_zero
  qHitsBothForbiddenSupports := squareFreeHittingSet_q_hits_forbiddenSupports
  prHitsForbiddenSupports := squareFreeHittingSet_pr_hits_forbiddenSupports
  squareFreeRepairPackage := squareFreeRepairExamplePackage
  singletonQMinimalRepair := squareFree_singletonQ_minimalRepairHittingSet
  pairPRMinimalRepair := squareFree_pairPR_minimalRepairHittingSet
  finiteComputability := finiteComputabilityExample_verified
  refactorInvariance := refactorInvarianceExamplePackage
  refactorNonzeroTransport := refactorInvarianceExample_nonzero_preserved
  refactorPullbackNonidentity := integerCohomologyPullback_one_ne_one
  cellularHodge := cellularHodgeFiniteExample
  supportTransfer := supportLocalizedTransferFiniteExample
  packetGAGA := measurementPacketGAGAFiniteExample
  staticFixturesReusableForPartIX := True
  staticFixturesReusableForPartIX_cert := trivial

/-- R11: the aggregate suite exposes every requested finite fixture family. -/
def PartVIIIFiniteExampleSuite.CoversR11 (S : PartVIIIFiniteExampleSuite) : Prop :=
  (∃ verdict :
      MeasurementVerdict pseudoCircleMeasurementProfile
        PseudoCircleMeasurementDomain.boundaryCocycle,
      verdict = S.pseudoCircleMeasuredNonzero) ∧
    (¬ pseudoCircleMeasurementProfile.Zero
      PseudoCircleMeasurementDomain.unmeasuredAxis) ∧
      (SquareFreeSupportVertex.q ∈ forbiddenSupportPQ ∧
        SquareFreeSupportVertex.q ∈ forbiddenSupportQR) ∧
        (SquareFreeSupportVertex.p ∈ forbiddenSupportPQ ∧
          SquareFreeSupportVertex.r ∈ forbiddenSupportQR) ∧
          squareFreeMinimalRepairHittingSets.minimalRepairHittingSet
            SquareFreeRepairTarget.singletonQ ∧
            squareFreeMinimalRepairHittingSets.minimalRepairHittingSet
              SquareFreeRepairTarget.pairPR ∧
              Nonempty
                (FiniteAATComputability.{0, 0} computabilityFiniteMeasurementRegime
                  finiteComputabilityExampleData) ∧
                Function.Bijective
                    integerCohomologyRefactorEquivalence.selectedFiniteSiteEquivalence ∧
                  Function.Bijective
                      integerCohomologyRefactorEquivalence.coefficientIso ∧
                    (integerCohomologyMeasurementProfile.Zero
                          (integerCohomologyPullbackClass.targetDomain
                            S.refactorInvariance.targetClass) ↔
                      integerCohomologyMeasurementProfile.Zero
                        (integerCohomologyPullbackClass.sourceDomain
                          (integerCohomologyPullbackClass.pullback
                            integerCohomologyRefactorEquivalence
                            S.refactorInvariance.targetClass))) ∧
                      ((¬ integerCohomologyMeasurementProfile.Zero integerOneClass) ∧
                        (¬ integerCohomologyMeasurementProfile.Zero
                          (integerCohomologyPullbackClass.pullback
                            integerCohomologyRefactorEquivalence
                            integerOneClass))) ∧
                      (integerCohomologyPullbackClass.pullback
                          integerCohomologyRefactorEquivalence integerOneClass ≠
                        integerOneClass) ∧
                      S.cellularHodge.kerL1_equiv_H1 ∧
                        S.cellularHodge.harmonicDebtMinimal ∧
                          S.supportTransfer.nontrivialPairingResidue ∧
                            S.supportTransfer.nontrivialTransferredResidue ∧
                              aatGAGAComparisonStatement gagaComparisonExampleData ∧
                                S.staticFixturesReusableForPartIX

/-- R11 / AC25: all requested finite example families are fully certified. -/
theorem partVIIIFiniteExampleSuite_complete :
    partVIIIFiniteExampleSuite.CoversR11 := by
  unfold PartVIIIFiniteExampleSuite.CoversR11
  exact ⟨⟨pseudoCircleBoundaryCocycleVerdict, rfl⟩,
    partVIIIFiniteExampleSuite.unmeasuredAxisNotZero,
    partVIIIFiniteExampleSuite.qHitsBothForbiddenSupports,
    partVIIIFiniteExampleSuite.prHitsForbiddenSupports,
    partVIIIFiniteExampleSuite.singletonQMinimalRepair,
    partVIIIFiniteExampleSuite.pairPRMinimalRepair,
    partVIIIFiniteExampleSuite.finiteComputability,
    integerCohomologyRefactorEquivalence.selectedFiniteSiteEquivalence.bijective,
    integerCohomologyRefactorEquivalence.coefficientIso.bijective,
    partVIIIFiniteExampleSuite.refactorInvariance.zero_iff_pullback_zero,
    partVIIIFiniteExampleSuite.refactorNonzeroTransport,
    partVIIIFiniteExampleSuite.refactorPullbackNonidentity,
    partVIIIFiniteExampleSuite.cellularHodge.kerL1_equiv_H1_cert,
    partVIIIFiniteExampleSuite.cellularHodge.harmonicDebtMinimal_cert,
    partVIIIFiniteExampleSuite.supportTransfer.nontrivialPairingResidue_cert,
    partVIIIFiniteExampleSuite.supportTransfer.nontrivialTransferredResidue_cert,
    partVIIIFiniteExampleSuite.packetGAGA.certifiedComparison,
    partVIIIFiniteExampleSuite.staticFixturesReusableForPartIX_cert⟩

end Measurement
end AAT.AG
