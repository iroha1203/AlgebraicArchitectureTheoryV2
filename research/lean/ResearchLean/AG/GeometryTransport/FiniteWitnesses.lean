import ResearchLean.AG.GeometryTransport.Supply
import ResearchLean.AG.GeometryTransport.Components
import Formal.AG.LawAlgebra.RawPresheafFiniteExample
import Formal.AG.ReadingFunctoriality.FiniteExamples

/-!
# Finite witnesses for geometry transport

The positive fixture uses the reviewed two-patch `FiniteModel` site and the
nonzero, nonidentity raw restriction system from
`RawPresheafFiniteExample`.  A concrete Atom involution gives a genuinely
nonidentity exact doctrine hom, so canonical `HGeom` and the resulting lift
fire away from the identity route.
-/

namespace AAT.AG.GeometryTransport

universe u

open CategoryTheory
open AtomFoundation

namespace FiniteGeometryWitness

/-- The reviewed finite two-patch geometry equipped with its actual raw
restriction system. -/
noncomputable def package : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := FiniteModel.twoPatchCorePackage
  geometry := FiniteModel.twoPatchSelectedGeometryReading
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := LawAlgebra.FiniteExamples.RawPresheaf.system

/-- The finite witness has an actual selected context. -/
theorem site_nonempty : Nonempty package.site.category :=
  ⟨FiniteModel.twoPatchBase⟩

/-- Its selected two-branch family is an actual covering sieve. -/
theorem has_topology_cover :
    Sieve.generate FiniteModel.twoPatchCover.presieve ∈
      package.site.topology FiniteModel.twoPatchBase :=
  FiniteModel.twoPatchCover_topologyCover

/-- The coefficient ring is nonzero. -/
theorem coefficient_nontrivial : (2 : package.Coefficient) ≠ 0 := by
  change (2 : Int) ≠ 0
  norm_num

/-- The raw system contains the concrete nonzero structural relation
`X² - 1`. -/
theorem raw_relation_nonzero :
    ((package.raw.relationFamily
      LawAlgebra.FiniteExamples.RawPresheaf.left).polynomial ()) ≠ 0 :=
  LawAlgebra.FiniteExamples.RawPresheaf.relation_polynomial_ne_zero

/-- The raw restriction along the selected left-to-base arrow is genuinely
nonidentity on the coordinate generator. -/
theorem raw_restriction_fires :
    (package.raw.restrictionStable
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).restriction.polynomialMap
        (MvPolynomial.X ()) = -(MvPolynomial.X ()) :=
  LawAlgebra.FiniteExamples.RawPresheaf.leftToBase_polynomialMap_X

/-- Swap the two visible finite components and fix every other Atom. -/
def swapAtom : FiniteModel.carrier.Atom → FiniteModel.carrier.Atom
  | .componentA => .componentB
  | .componentB => .componentA
  | atom => atom

/-- Swapping the two visible components twice fixes every Atom. -/
@[simp] theorem swapAtom_involutive (atom : FiniteModel.carrier.Atom) :
    swapAtom (swapAtom atom) = atom := by
  cases atom <;> rfl

/-- The selected swap as an Atom equivalence. -/
def swapEquiv : FiniteModel.carrier.Atom ≃ FiniteModel.carrier.Atom where
  toFun := swapAtom
  invFun := swapAtom
  left_inv := swapAtom_involutive
  right_inv := swapAtom_involutive

/-- A nonidentity exact endomorphism of the finite extraction doctrine. -/
def exactSwap : ExactDoctrineHom package.core.reading.doctrine
    package.core.reading.doctrine where
  sourceMap := _root_.id
  atomEquiv := swapEquiv
  normalize_eq _ := rfl
  extraction_iff source atom := by
    change FiniteModel.extractionDoctrine.extracts source atom ↔
      FiniteModel.extractionDoctrine.extracts source (swapEquiv atom)
    cases source with
    | all =>
        simp [ExtractionDoctrine.extracts_iff,
          FiniteModel.extractionDoctrine]
    | withoutComponentC =>
        rw [FiniteModel.extractionDoctrine_extracts_iff_selected,
          FiniteModel.extractionDoctrine_extracts_iff_selected]
        cases atom <;> simp [swapEquiv, swapAtom]

/-- The finite exact direction is not the identity on primitive Atoms. -/
theorem exactSwap_nonidentity : exactSwap.atomEquiv.toFun ≠ _root_.id := by
  intro h
  have hA := congrFun h FiniteModel.FiniteAtom.componentA
  exact FiniteModel.FiniteAtom.noConfusion hA

/-- The low-level realization condition is inhabited on a nondegenerate,
nonidentity finite input. -/
noncomputable def positiveHGeom :
    HGeom package (transportAlongHom package.core exactSwap) :=
  canonicalHGeom package exactSwap

/-- The positive finite geometry lift produced from `HGeom`. -/
noncomputable def positiveLift :
    GeometryTotalHom package
      (pushGeometryPackage package (transportAlongHom package.core exactSwap)) :=
  geometryLiftOfHGeom package (transportAlongHom package.core exactSwap)
    positiveHGeom

/-- The positive lift lies over a genuinely nonidentity core-package hom. -/
theorem positiveLift_base_nonidentity_atom :
    positiveLift.base.upper.atomEquiv.toFun ≠ _root_.id := by
  simpa [positiveLift, exactSwap, transportAlongHom, transportAlongUpper] using
    exactSwap_nonidentity

end FiniteGeometryWitness

namespace NegativeGeometryWitness

open AAT.AG.ReadingFunctorialityFinite

/-- The full-context source contains a singleton support which reads only
`componentA`.  Its image under the selected core hom keeps the same context
but sends the Atom to `componentB`, where no support reads it. -/
def obstructionContext : Site.ArchCtx exactSourceCore.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom => atom = FiniteModel.FiniteAtom.componentA
    supportReads_objectFamily := by
      intro _support atom h
      subst atom
      rw [exactSourceCore.object_family_mem_iff_extracts]
      change True ∧ True ∧ True ∧ True
      simp
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- Nonvacuous coverage requirements for the obstruction fixture. -/
def requirements : Site.CoverageRequirements exactSourceCore.object
    exactSourceCore.equationSystem exactSourceCore.algebra.signatureReading where
  requiredSupport atom := atom = FiniteModel.FiniteAtom.componentA
  requiredEquationCoordinate _ := False
  selectedViolationWitness _ := False
  requiredAxis _ := False
  supportVisibleOn _ atom := atom = FiniteModel.FiniteAtom.componentA
  equationCoordinateVisibleOn _ _ := False
  violationWitnessVisibleOn _ _ := False
  axisReadableOn _ _ := False
  boundaryVisibleOn _ _ := True

/-- Pullbacks on the full restriction-context preorder are its canonical
componentwise products. -/
noncomputable def overlap :
    Site.ContextOverlapPullback exactSourceCore.contextPreorder :=
  Site.meetOverlapPullback exactSourceCore.contextPreorder
    Site.productContextFiniteMeet

/-- Selected nondegenerate geometry on the negative source core. -/
noncomputable def selectedGeometry :
    Site.SelectedGeometryReading exactSourceCore where
  requirements := requirements
  overlap := overlap

/-- The selected site underlying the negative and firing fixtures. -/
noncomputable abbrev site := selectedGeometry.toAATSite

/-- One semantic raw coordinate on every obstruction-site context. -/
def coordFamily (W : site.category) : LawAlgebra.CoordinateFamily W.ctx where
  Coord := Unit
  label := fun _ => LawAlgebra.CoordinateLabel.semantic
  LocalData := fun _ => Unit

/-- The nonzero raw relation `X² - X`. -/
noncomputable def relationFamily (W : site.category) :
    LawAlgebra.StructuralRelationFamily (coordFamily W) Int where
  Relation := Unit
  polynomial := fun _ => MvPolynomial.X () ^ 2 - MvPolynomial.X ()

/-- Every selected restriction keeps the raw coordinate. -/
noncomputable def coordinateRestriction {X Y : site.category} (w : X ⟶ Y) :
    LawAlgebra.TypedCoordinateRestriction (coordFamily X) (coordFamily Y) Int
      (site.contextPreorder.morphism (leOfHom w)) where
  variableImage := fun _ => MvPolynomial.X ()

/-- The obstruction fixture's coordinate restriction is the identity ring hom. -/
theorem coordinateRestriction_polynomialMap {X Y : site.category} (w : X ⟶ Y) :
    (coordinateRestriction w).polynomialMap =
      RingHom.id (LawAlgebra.FreeTypedCommAlg (coordFamily X) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    change (coordinateRestriction w).polynomialMap (MvPolynomial.C value) =
      MvPolynomial.C value
    exact LawAlgebra.TypedCoordinateRestriction.polynomialMap_C _ _
  · intro coordinate
    cases coordinate
    rw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- The nonzero obstruction relation is stable under identity coordinate restriction. -/
noncomputable def restrictionStable {X Y : site.category} (w : X ⟶ Y) :
    LawAlgebra.RestrictionStableStructuralRelations
      (relationFamily X) (relationFamily Y)
      (site.contextPreorder.morphism (leOfHom w)) where
  restriction := coordinateRestriction w
  maps_JStruct := by
    intro polynomial hpolynomial
    have hid : (coordinateRestriction w).polynomialMap polynomial = polynomial := by
      rw [coordinateRestriction_polynomialMap]
      rfl
    rw [hid]
    exact hpolynomial

/-- A coherent nonempty raw restriction system on the obstruction site. -/
noncomputable def raw : LawAlgebra.RawAmbientRestrictionSystem site Int where
  coordFamily := coordFamily
  relationFamily := relationFamily
  restrictionStable := restrictionStable
  identity_polynomialMap W := coordinateRestriction_polynomialMap (𝟙 W)
  composition_polynomialMap f g := by
    change (coordinateRestriction (f ≫ g)).polynomialMap =
      ((coordinateRestriction f).polynomialMap).comp
        ((coordinateRestriction g).polynomialMap)
    rw [coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

/-- The finite, nondegenerate source geometry used by the no-lift witness. -/
noncomputable def package : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := exactSourceCore
  geometry := selectedGeometry
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := raw

/-- The source site is inhabited by the obstruction context. -/
def base : package.site.category := ⟨obstructionContext⟩

/-- A genuine singleton admissible cover discharging the selected support
requirement. -/
noncomputable def cover : Site.AATCoverageFamily requirements overlap base where
  Index := PUnit
  patch _ := obstructionContext
  inclusion _ := exactSourceCore.contextPreorder.refl obstructionContext
  admissible := {
    atomSupportCoverage := by
      intro atom h
      exact ⟨PUnit.unit, h⟩
    equationCoordinateCoverage := by
      intro _ h
      exact False.elim h
    violationWitnessCoverage := by
      intro _ h
      exact False.elim h
    signatureAxisCoverage := by
      intro _ h
      exact False.elim h
    boundaryCoverage := by intros; trivial
    nonGeneration := Site.AdmissibleCover.nonGenerating_from_inclusions
  }

/-- The concrete singleton family generates an actual source covering sieve. -/
theorem cover_mem_topology :
    Sieve.generate cover.presieve ∈ package.site.topology base :=
  Site.AATGrothendieckTopology.generate_mem cover

/-- The negative fixture's integer coefficient ring is nonzero. -/
theorem coefficient_nontrivial : (2 : package.Coefficient) ≠ 0 := by
  change (2 : Int) ≠ 0
  norm_num

/-- The obstruction fixture carries the concrete nonzero relation `X² - X`. -/
theorem raw_relation_nonzero :
    (package.raw.relationFamily base).polynomial () ≠ 0 := by
  change (MvPolynomial.X () ^ 2 - MvPolynomial.X () :
    MvPolynomial Unit Int) ≠ 0
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => 2)) hzero
  norm_num at heval

/-- Exact lower doctrine map paired with the public nonidentity exact core
change from the Formal finite fixture. -/
noncomputable def doctrineHom : ExactDoctrineHom exactSourceCore.reading.doctrine
    exactTargetCore.reading.doctrine where
  sourceMap := _root_.id
  atomEquiv := nonidentityExactCoreChange.atomEquiv
  normalize_eq _ := rfl
  extraction_iff source atom := by
    cases source
    cases atom <;> rfl

/-- The non-tautological core-package hom whose context functor is the
identity while its Atom equivalence swaps the visible components. -/
noncomputable def coreHom : PackageTotalHom exactSourceCore exactTargetCore where
  base := {
    doctrineHom := doctrineHom
    source_eq := rfl
  }
  upper := nonidentityExactCoreChange
  atomEquiv_eq := rfl

/-- The selected core hom is genuinely nonidentity on primitive Atoms. -/
theorem coreHom_nonidentity_atom : coreHom.upper.atomEquiv.toFun ≠ _root_.id :=
  nonidentityExactCoreChange_fires

/-- The core-stage witness lies over exactly the selected exact doctrine hom. -/
@[simp] theorem coreHom_base_doctrineHom :
    coreHom.base.doctrineHom = doctrineHom :=
  rfl

/-- The negative core hom is not the identity/tautological total hom. -/
theorem coreHom_ne_identity :
    coreHom ≠ PackageTotalHom.id exactSourceCore := by
  intro h
  apply coreHom_nonidentity_atom
  have hfun := congrArg (fun f : PackageTotalHom exactSourceCore exactTargetCore =>
    f.upper.atomEquiv.toFun) h
  simpa [PackageTotalHom.id, SignedExactCoreReadingHom.refl] using hfun

/-- The non-tautological core hom leaves the obstruction context fixed, so its
image still does not read `componentB`. -/
theorem coreHom_context_does_not_read_componentB :
    ¬ ((coreContextFunctor coreHom).obj base).ctx.minimal.supportReads
      PUnit.unit FiniteModel.FiniteAtom.componentB := by
  intro h
  exact FiniteModel.FiniteAtom.noConfusion h

/-- In contrast, the G-101 tautological hom for the same exact doctrine map
conjugates readability and therefore reads `componentB`. -/
theorem tautological_context_reads_componentB :
    ((coreContextFunctor (transportAlongHom exactSourceCore doctrineHom)).obj
      base).ctx.minimal.supportReads
        (transportCoreSupportEquiv exactSourceCore.reading doctrineHom
          base PUnit.unit)
        FiniteModel.FiniteAtom.componentB := by
  simpa [transportAlongHom, transportAlongUpper] using
    (transportCoreSupportEquiv_reads_iff exactSourceCore.reading doctrineHom
      base PUnit.unit FiniteModel.FiniteAtom.componentA).2 rfl

/-- A concrete inequality separates the selected core hom from the
tautological transport route on an actual realization value. -/
theorem coreHom_ne_tautological_context_action :
    (((coreContextFunctor coreHom).obj base).ctx.minimal.supportReads
        PUnit.unit FiniteModel.FiniteAtom.componentB) ≠
      (((coreContextFunctor
        (transportAlongHom exactSourceCore doctrineHom)).obj base).ctx.minimal.supportReads
          (transportCoreSupportEquiv exactSourceCore.reading doctrineHom
            base PUnit.unit) FiniteModel.FiniteAtom.componentB) := by
  intro h
  apply coreHom_context_does_not_read_componentB
  rw [h]
  exact tautological_context_reads_componentB

/-- A target-independent semantic profile of a core-package hom: whether the
image context contains some support reading the image of a source Atom. -/
def coreSupportReadProfile {Q : AATCorePackage FiniteModel.carrier}
    (f : PackageTotalHom exactSourceCore Q) :
    Site.ContextCategoryObject exactSourceCore.contextPreorder →
      FiniteModel.carrier.Atom → Prop :=
  fun W atom => ∃ support : ((coreContextFunctor f).obj W).ctx.Support,
    ((coreContextFunctor f).obj W).ctx.minimal.supportReads support
      (f.upper.atomEquiv atom)

/-- The selected non-tautological lift loses the component-A read profile. -/
theorem coreHom_profile_componentA_false :
    ¬ coreSupportReadProfile coreHom base
      FiniteModel.FiniteAtom.componentA := by
  rintro ⟨support, hread⟩
  cases support
  exact coreHom_context_does_not_read_componentB hread

/-- The canonical lift retains the transported component-A read profile. -/
theorem tautological_profile_componentA_true :
    coreSupportReadProfile
      (transportAlongHom exactSourceCore doctrineHom) base
        FiniteModel.FiniteAtom.componentA := by
  exact ⟨transportCoreSupportEquiv exactSourceCore.reading doctrineHom
    base PUnit.unit, tautological_context_reads_componentB⟩

/-- The selected core hom and the canonical hom have different common
realization-read profiles. -/
theorem coreHom_profile_ne_tautological :
    coreSupportReadProfile coreHom ≠
      coreSupportReadProfile
        (transportAlongHom exactSourceCore doctrineHom) := by
  intro h
  apply coreHom_profile_componentA_false
  rw [h]
  exact tautological_profile_componentA_true

/-- A core-stage lift route over the fixed exact doctrine map.  Keeping the
target in the package makes selected and canonical lifts directly comparable
in one type. -/
structure CoreLiftRoute where
  /-- The core package reached by this selected lift route. -/
  target : AATCorePackage FiniteModel.carrier
  /-- The actual G-101 total morphism from the fixed negative source. -/
  hom : PackageTotalHom exactSourceCore target
  /-- Proof that the route lies over the selected exact doctrine hom. -/
  lower_eq : HEq hom.base.doctrineHom doctrineHom

namespace CoreLiftRoute

/-- The target-independent readability projection of a lift route. -/
def supportProfile (route : CoreLiftRoute) :
    Site.ContextCategoryObject exactSourceCore.contextPreorder →
      FiniteModel.carrier.Atom → Prop :=
  coreSupportReadProfile route.hom

end CoreLiftRoute

/-- The realization-incompatible selected core lift as a common route. -/
noncomputable def selectedCoreLiftRoute : CoreLiftRoute where
  target := exactTargetCore
  hom := coreHom
  lower_eq := HEq.rfl

/-- The G-101 canonical core lift over the same exact doctrine map. -/
noncomputable def tautologicalCoreLiftRoute : CoreLiftRoute where
  target := transportAlong exactSourceCore doctrineHom
  hom := transportAlongHom exactSourceCore doctrineHom
  lower_eq := HEq.rfl

/-- The selected core lift is not the G-101 tautological lift over the same
exact doctrine map.  Their common route profiles differ on an actual
readability value, so the proof does not use target-type inequality. -/
theorem coreHom_ne_tautological :
    selectedCoreLiftRoute ≠ tautologicalCoreLiftRoute := by
  intro h
  apply coreHom_profile_ne_tautological
  simpa [selectedCoreLiftRoute, tautologicalCoreLiftRoute,
    CoreLiftRoute.supportProfile] using
    congrArg CoreLiftRoute.supportProfile h

/-- G-108 (v)(e): the selected core-stage lift exists and lies over exactly
the fixed nonidentity exact doctrine hom.  This conclusion records the lower
map rather than merely the inhabitation of an unrelated hom type. -/
theorem core_stage_lift_exists :
    ∃ f : PackageTotalHom exactSourceCore exactTargetCore,
      f.base.doctrineHom = doctrineHom :=
  ⟨coreHom, coreHom_base_doctrineHom⟩

/-- No low-level realization supply exists for the negative core hom. -/
theorem not_hGeom : ¬ Nonempty (HGeom package coreHom) := by
  rintro ⟨H⟩
  have hread := H.supportReads base PUnit.unit
    FiniteModel.FiniteAtom.componentA rfl
  change FiniteModel.FiniteAtom.componentB =
    FiniteModel.FiniteAtom.componentA at hread
  exact FiniteModel.FiniteAtom.noConfusion hread

/-- Assemble an arbitrary geometry package over the fixed negative target
core from the existing Formal component types. -/
noncomputable def targetPackage
    (geometry : Site.SelectedGeometryReading exactTargetCore)
    (k : Type) [CommRing k]
    (targetRaw : LawAlgebra.RawAmbientRestrictionSystem
      geometry.toAATSite k) : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := exactTargetCore
  geometry := geometry
  Coefficient := k
  coefficientCommRing := inferInstance
  raw := targetRaw

/-- No geometry hom over `coreHom` exists to any target package over the
fixed target core, regardless of its coverage, overlap, coefficients, or raw
system. -/
theorem no_geomReadHom_to_any_target
    (geometry : Site.SelectedGeometryReading exactTargetCore)
    (k : Type) [CommRing k]
    (targetRaw : LawAlgebra.RawAmbientRestrictionSystem
      geometry.toAATSite k) :
    ¬ Nonempty (GeomReadHom package
      (targetPackage geometry k targetRaw) coreHom) := by
  rintro ⟨F⟩
  exact not_hGeom ⟨hGeomOfGeomReadHom F⟩

/-- Equivalent total-category form of the negative witness. -/
theorem no_geometryLift_to_any_target
    (geometry : Site.SelectedGeometryReading exactTargetCore)
    (k : Type) [CommRing k]
    (targetRaw : LawAlgebra.RawAmbientRestrictionSystem
      geometry.toAATSite k) :
    ¬ ∃ lift : GeometryTotalHom package (targetPackage geometry k targetRaw),
      lift.base = coreHom := by
  rintro ⟨lift, hbase⟩
  exact not_hGeom (hGeom_necessary lift hbase)

/-- The target geometry class is nonempty: free non-realization transport
constructs a concrete candidate even though no realization-compatible hom to
it exists. -/
noncomputable def targetCandidate : GeometryPackage.{0, 0} FiniteModel.carrier :=
  pushGeometryPackage package coreHom

/-- The freely pushed candidate lies over the fixed negative target core. -/
theorem targetCandidate_core : targetCandidate.core = exactTargetCore :=
  rfl

/-- The target package class is inhabited independently of geometry-lift existence. -/
theorem target_candidate_class_nonempty :
    Nonempty {K : GeometryPackage.{0, 0} FiniteModel.carrier //
      K.core = exactTargetCore} :=
  ⟨⟨targetCandidate, targetCandidate_core⟩⟩

/-! ### Negative coverage instance -/

/-- Target requirements selecting no coverage obligations. -/
def emptyTargetRequirements : Site.CoverageRequirements exactTargetCore.object
    exactTargetCore.equationSystem exactTargetCore.algebra.signatureReading where
  requiredSupport := fun _ => False
  requiredEquationCoordinate := fun _ => False
  selectedViolationWitness := fun _ => False
  requiredAxis := fun _ => False
  supportVisibleOn := fun _ _ => False
  equationCoordinateVisibleOn := fun _ _ => False
  violationWitnessVisibleOn := fun _ _ => False
  axisReadableOn := fun _ _ => False
  boundaryVisibleOn := fun _ _ => False

/-- Canonical target overlap used by the coverage-negative fixture. -/
noncomputable def emptyTargetOverlap :
    Site.ContextOverlapPullback exactTargetCore.contextPreorder :=
  Site.meetOverlapPullback exactTargetCore.contextPreorder
    Site.productContextFiniteMeet

/-- Selected target geometry with no required support. -/
noncomputable def emptyTargetGeometry : Site.SelectedGeometryReading exactTargetCore where
  requirements := emptyTargetRequirements
  overlap := emptyTargetOverlap

/-- Reindexed raw system over the coverage-negative target geometry. -/
noncomputable def emptyTargetRaw : LawAlgebra.RawAmbientRestrictionSystem
    emptyTargetGeometry.toAATSite Int :=
  rawReindexCore selectedGeometry emptyTargetGeometry coreHom raw

/-- Target package used solely to refute universal coverage preservation. -/
noncomputable def emptyCoverageTarget : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := exactTargetCore
  geometry := emptyTargetGeometry
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := emptyTargetRaw

/-- `CoverageTransport` has a concrete negative instance: the required source
component is sent to a target with no required support. -/
theorem no_coverageTransport_to_emptyTarget :
    ¬ CoverageTransport package emptyCoverageTarget coreHom := by
  intro T
  have htarget := T.requiredSupport FiniteModel.FiniteAtom.componentA rfl
  exact htarget

/-! ### Literal cover-family and raw-value firing -/

/-- The companion source context reads only component B. -/
def componentBContext : Site.ArchCtx exactSourceCore.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom => atom = FiniteModel.FiniteAtom.componentB
    supportReads_objectFamily := by
      intro _support atom h
      subst atom
      rw [exactSourceCore.object_family_mem_iff_extracts]
      change True ∧ True ∧ True ∧ True
      simp
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- The A-readable and B-readable contexts are actual distinct site objects. -/
theorem obstructionContext_ne_componentBContext :
    obstructionContext ≠ componentBContext := by
  intro h
  have hprofile := congrArg
    (fun W : Site.ArchCtx exactSourceCore.object =>
      ∃ support : W.Support,
        W.minimal.supportReads support FiniteModel.FiniteAtom.componentA) h
  have hsource : ∃ support : obstructionContext.Support,
      obstructionContext.minimal.supportReads support
        FiniteModel.FiniteAtom.componentA := ⟨PUnit.unit, rfl⟩
  have htarget : ¬ ∃ support : componentBContext.Support,
      componentBContext.minimal.supportReads support
        FiniteModel.FiniteAtom.componentA := by
    rintro ⟨support, hread⟩
    cases support
    exact FiniteModel.FiniteAtom.noConfusion hread
  apply htarget
  exact Eq.mp hprofile hsource

/-- Context-dependent raw relations with a common principal ideal. -/
noncomputable def signedRelationFamily (W : site.category) :
    LawAlgebra.StructuralRelationFamily (coordFamily W) Int := by
  classical
  exact {
    Relation := Unit
    polynomial := fun _ =>
      if W.ctx = obstructionContext then MvPolynomial.X () else -(MvPolynomial.X ())
  }

/-- Every signed relation ideal contains the common generator `X`. -/
theorem signedRelationFamily_X_mem (W : site.category) :
    MvPolynomial.X () ∈ (signedRelationFamily W).JStruct := by
  classical
  by_cases hW : W.ctx = obstructionContext
  · simpa [signedRelationFamily, hW] using
      (signedRelationFamily W).polynomial_mem_JStruct ()
  · have hneg := (signedRelationFamily W).JStruct.neg_mem
      ((signedRelationFamily W).polynomial_mem_JStruct ())
    simpa [signedRelationFamily, hW] using hneg

/-- Identity coordinate restriction preserves the signed principal ideals. -/
noncomputable def signedRestrictionStable {X Y : site.category} (w : X ⟶ Y) :
    LawAlgebra.RestrictionStableStructuralRelations
      (signedRelationFamily X) (signedRelationFamily Y)
      (site.contextPreorder.morphism (leOfHom w)) where
  restriction := coordinateRestriction w
  maps_JStruct := by
    classical
    intro polynomial hpolynomial
    have hid : (coordinateRestriction w).polynomialMap polynomial = polynomial := by
      rw [coordinateRestriction_polynomialMap]
      rfl
    rw [hid]
    rw [LawAlgebra.StructuralRelationFamily.JStruct] at hpolynomial ⊢
    apply (Ideal.span_le.mpr ?_) hpolynomial
    rintro targetPolynomial ⟨relation, rfl⟩
    cases relation
    by_cases hY : Y.ctx = obstructionContext
    · simpa [signedRelationFamily, hY] using signedRelationFamily_X_mem X
    · exact by
        simpa [signedRelationFamily, hY] using
          (signedRelationFamily X).JStruct.neg_mem
            (signedRelationFamily_X_mem X)

/-- Coherent raw system whose displayed relation detects context reindexing. -/
noncomputable def signedRaw :
    LawAlgebra.RawAmbientRestrictionSystem site Int where
  coordFamily := coordFamily
  relationFamily := signedRelationFamily
  restrictionStable := signedRestrictionStable
  identity_polynomialMap W := coordinateRestriction_polynomialMap (𝟙 W)
  composition_polynomialMap f g := by
    change (coordinateRestriction (f ≫ g)).polynomialMap =
      ((coordinateRestriction f).polynomialMap).comp
        ((coordinateRestriction g).polynomialMap)
    rw [coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

/-- Source package for literal cover-family and raw-value firing. -/
noncomputable def firingPackage : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := exactSourceCore
  geometry := selectedGeometry
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := signedRaw

/-- The B-readable source context as a site object. -/
def componentBBase : firingPackage.site.category := ⟨componentBContext⟩

/-- The A-readable source base, definitionally shared with the existing cover. -/
def componentABase : firingPackage.site.category := ⟨obstructionContext⟩

/-- The existing singleton cover regarded over the firing package. -/
noncomputable def firingCover : Site.AATCoverageFamily
    firingPackage.geometry.requirements firingPackage.geometry.overlap componentABase :=
  cover

/-- The actual source cover patch reads component A. -/
theorem firingCover_patch_reads_componentA :
    ∃ support : (firingCover.patch PUnit.unit).Support,
      (firingCover.patch PUnit.unit).minimal.supportReads support
        FiniteModel.FiniteAtom.componentA :=
  ⟨PUnit.unit, rfl⟩

/-- Canonical identity-coefficient target for the nonidentity Atom swap. -/
noncomputable abbrev firingTarget := geomTransportAlong firingPackage doctrineHom

/-- The target's fixed A-readable semantic reference is the image of the
B-readable source context, because the exact Atom map swaps A and B. -/
noncomputable def targetComponentAReference : firingTarget.site.category :=
  contextForward (transportAlongHom firingPackage.core doctrineHom) componentBBase

/-- The target reference really reads component A after the Atom swap. -/
theorem targetComponentAReference_reads_componentA :
    ∃ support : targetComponentAReference.ctx.Support,
      targetComponentAReference.ctx.minimal.supportReads support
        FiniteModel.FiniteAtom.componentA := by
  refine ⟨transportCoreSupportEquiv firingPackage.core.reading doctrineHom
    componentBBase PUnit.unit, ?_⟩
  simpa [targetComponentAReference, firingPackage, doctrineHom,
    componentBBase, componentBContext] using
    (transportCoreSupportEquiv_reads_iff firingPackage.core.reading doctrineHom
      componentBBase PUnit.unit FiniteModel.FiniteAtom.componentB).2 rfl

/-- The actual source cover transported by the canonical context functor. -/
noncomputable def transportedFiringCover :=
  pushAATCoverageFamily firingPackage doctrineHom firingCover

/-- The actual transported cover patch reads component B. -/
theorem transportedFiringCover_patch_reads_componentB :
    ∃ support : (transportedFiringCover.patch PUnit.unit).Support,
      (transportedFiringCover.patch PUnit.unit).minimal.supportReads support
        FiniteModel.FiniteAtom.componentB := by
  refine ⟨transportCoreSupportEquiv firingPackage.core.reading doctrineHom
    componentABase PUnit.unit, ?_⟩
  simpa [transportedFiringCover, firingCover, componentABase, firingPackage,
    doctrineHom, obstructionContext] using
    (transportCoreSupportEquiv_reads_iff firingPackage.core.reading doctrineHom
      componentABase PUnit.unit FiniteModel.FiniteAtom.componentA).2 rfl

/-- The actual transported cover patch no longer reads component A. -/
theorem transportedFiringCover_patch_not_reads_componentA :
    ¬ ∃ support : (transportedFiringCover.patch PUnit.unit).Support,
      (transportedFiringCover.patch PUnit.unit).minimal.supportReads support
        FiniteModel.FiniteAtom.componentA := by
  rintro ⟨support, hread⟩
  obtain ⟨sourceSupport, rfl⟩ :=
    (transportCoreSupportEquiv firingPackage.core.reading doctrineHom
      componentABase).surjective support
  have hsource :=
    (transportCoreSupportEquiv_reads_iff firingPackage.core.reading doctrineHom
      componentABase sourceSupport FiniteModel.FiniteAtom.componentB).mp (by
        simpa [transportedFiringCover, firingCover, componentABase,
          firingPackage, doctrineHom, obstructionContext] using hread)
  change FiniteModel.FiniteAtom.componentB =
    FiniteModel.FiniteAtom.componentA at hsource
  exact FiniteModel.FiniteAtom.noConfusion hsource

/-- The common Atom-indexed read profile of the actual source and transported
cover patches changes from A-readable to non-A-readable. -/
theorem firingCover_patch_readProfile_changes :
    (∃ support : (firingCover.patch PUnit.unit).Support,
      (firingCover.patch PUnit.unit).minimal.supportReads support
        FiniteModel.FiniteAtom.componentA) ∧
    ¬ (∃ support : (transportedFiringCover.patch PUnit.unit).Support,
      (transportedFiringCover.patch PUnit.unit).minimal.supportReads support
        FiniteModel.FiniteAtom.componentA) :=
  ⟨firingCover_patch_reads_componentA,
    transportedFiringCover_patch_not_reads_componentA⟩

/-- The actual transported cover patch differs from the target A-readable
reference patch; this is a cover-family datum inequality, not a requirement
predicate comparison. -/
theorem transportedFiringCover_patch_ne_targetComponentAReference :
    transportedFiringCover.patch PUnit.unit ≠ targetComponentAReference.ctx := by
  change coreContextMap (transportAlongHom firingPackage.core doctrineHom)
      obstructionContext ≠
    coreContextMap (transportAlongHom firingPackage.core doctrineHom)
      componentBContext
  intro h
  exact obstructionContext_ne_componentBContext
    (canonicalCoreContextMap_injective firingPackage doctrineHom h)

/-- The source A-readable slot carries `X`. -/
theorem signedRaw_source_A_value :
    (firingPackage.raw.relationFamily componentABase).polynomial () =
      MvPolynomial.X () := by
  simp [firingPackage, signedRaw, signedRelationFamily, componentABase]

/-- At the target A-readable slot, canonical inverse-context reindexing
recovers the source B-readable value `-X`; the coefficient map is identity. -/
theorem signedRaw_target_A_value :
    (firingTarget.raw.relationFamily targetComponentAReference).polynomial () =
      -(MvPolynomial.X ()) := by
  change MvPolynomial.map (RingHom.id Int)
      ((signedRelationFamily
        ((contextInverse (G := firingPackage) (H := firingTarget)
          (transportAlongHom firingPackage.core doctrineHom)).obj
          targetComponentAReference)).polynomial ()) = -(MvPolynomial.X ())
  rw [show
    (contextInverse (G := firingPackage) (H := firingTarget)
      (transportAlongHom firingPackage.core doctrineHom)).obj
        targetComponentAReference = componentBBase by
      exact canonicalContextRetraction_eq firingPackage doctrineHom componentBBase]
  have hBA : componentBContext ≠ obstructionContext :=
    obstructionContext_ne_componentBContext.symm
  simp [signedRelationFamily, componentBBase, hBA]

/-- Identity-coefficient canonical reindexing changes an actual raw relation
value on the fixed A-readable semantic slot. -/
theorem signedRaw_value_changes :
    (firingPackage.raw.relationFamily componentABase).polynomial () ≠
      (firingTarget.raw.relationFamily targetComponentAReference).polynomial () := by
  rw [signedRaw_source_A_value, signedRaw_target_A_value]
  intro h
  have heval := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => 1)) h
  norm_num at heval

/-! ### Concrete nonidentity coefficient action in one core fiber -/

/-- Asymmetric coefficient ring used by the fiber-isomorphism example. -/
abbrev PairCoefficient := Int × Int

/-- The first coefficient idempotent marks the source presentation. -/
noncomputable def pairRelationFamily (W : site.category) :
    LawAlgebra.StructuralRelationFamily (coordFamily W) PairCoefficient where
  Relation := Unit
  polynomial := fun _ =>
    MvPolynomial.C ((1 : Int), (0 : Int)) * MvPolynomial.X ()

/-- Identity coordinate restriction for the pair-coefficient presentation. -/
noncomputable def pairCoordinateRestriction {X Y : site.category} (w : X ⟶ Y) :
    LawAlgebra.TypedCoordinateRestriction (coordFamily X) (coordFamily Y)
      PairCoefficient (site.contextPreorder.morphism (leOfHom w)) where
  variableImage := fun _ => MvPolynomial.X ()

/-- Pair-coordinate restriction acts identically on the free algebra. -/
theorem pairCoordinateRestriction_polynomialMap {X Y : site.category}
    (w : X ⟶ Y) :
    (pairCoordinateRestriction w).polynomialMap =
      RingHom.id (LawAlgebra.FreeTypedCommAlg (coordFamily X) PairCoefficient) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    change (pairCoordinateRestriction w).polynomialMap (MvPolynomial.C value) =
      MvPolynomial.C value
    exact LawAlgebra.TypedCoordinateRestriction.polynomialMap_C _ _
  · intro coordinate
    cases coordinate
    rw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- Pair relations are stable under every selected restriction. -/
noncomputable def pairRestrictionStable {X Y : site.category} (w : X ⟶ Y) :
    LawAlgebra.RestrictionStableStructuralRelations
      (pairRelationFamily X) (pairRelationFamily Y)
      (site.contextPreorder.morphism (leOfHom w)) where
  restriction := pairCoordinateRestriction w
  maps_JStruct := by
    intro polynomial hpolynomial
    have hid : (pairCoordinateRestriction w).polynomialMap polynomial =
        polynomial := by
      rw [pairCoordinateRestriction_polynomialMap]
      rfl
    rw [hid]
    exact hpolynomial

/-- Coherent pair-coefficient raw system. -/
noncomputable def pairRaw :
    LawAlgebra.RawAmbientRestrictionSystem site PairCoefficient where
  coordFamily := coordFamily
  relationFamily := pairRelationFamily
  restrictionStable := pairRestrictionStable
  identity_polynomialMap W := pairCoordinateRestriction_polynomialMap (𝟙 W)
  composition_polynomialMap f g := by
    change (pairCoordinateRestriction (f ≫ g)).polynomialMap =
      ((pairCoordinateRestriction f).polynomialMap).comp
        ((pairCoordinateRestriction g).polynomialMap)
    rw [pairCoordinateRestriction_polynomialMap,
      pairCoordinateRestriction_polynomialMap,
      pairCoordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

/-- Source package for the concrete coefficient fiber action. -/
noncomputable def pairPackage : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := exactSourceCore
  geometry := selectedGeometry
  Coefficient := PairCoefficient
  coefficientCommRing := inferInstance
  raw := pairRaw

/-- Swap the two coefficient factors. -/
def pairSwap : PairCoefficient →+* PairCoefficient :=
  (RingEquiv.prodComm : Int × Int ≃+* Int × Int).toRingHom

/-- The coefficient swap is an involution. -/
theorem pairSwap_involutive (x : PairCoefficient) : pairSwap (pairSwap x) = x := by
  rcases x with ⟨x, y⟩
  rfl

/-- Ring-hom form of coefficient-swap involutivity. -/
theorem pairSwap_comp : pairSwap.comp pairSwap = RingHom.id PairCoefficient := by
  ext x <;> rfl

/-- Same-core package obtained by the nonidentity coefficient automorphism. -/
noncomputable def pairFiberTarget : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := pairPackage.core
  geometry := pairPackage.geometry
  Coefficient := PairCoefficient
  coefficientCommRing := inferInstance
  raw := pairPackage.raw.baseChange pairSwap

/-- Forward fiber hom carrying the coefficient swap. -/
noncomputable def pairFiberForwardGeometry :
    GeomReadHom pairPackage pairFiberTarget
      (PackageTotalHom.id pairPackage.core) where
  coverage := {
    requiredSupport := fun _ => _root_.id
    requiredEquationCoordinate := fun _ => _root_.id
    selectedViolationWitness := fun _ => _root_.id
    requiredAxis := fun _ => _root_.id
    supportVisibleOn := fun _ _ => _root_.id
    equationCoordinateVisibleOn := fun _ _ => _root_.id
    violationWitnessVisibleOn := fun _ _ => _root_.id
    axisReadableOn := fun _ _ => _root_.id
    boundaryVisibleOn := fun _ _ => _root_.id
  }
  overlap := { overlapIso := fun _ _ _ => Iso.refl _ }
  coefficientHom := pairSwap
  raw_eq := by
    change pairPackage.raw.baseChange pairSwap =
      rawTransport (G := pairPackage) (H := pairPackage)
        (PackageTotalHom.id pairPackage.core) pairSwap
    simp [rawTransport]
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Reverse fiber hom, using the same involutive coefficient swap. -/
noncomputable def pairFiberInverseGeometry :
    GeomReadHom pairFiberTarget pairPackage
      (PackageTotalHom.id pairPackage.core) where
  coverage := {
    requiredSupport := fun _ => _root_.id
    requiredEquationCoordinate := fun _ => _root_.id
    selectedViolationWitness := fun _ => _root_.id
    requiredAxis := fun _ => _root_.id
    supportVisibleOn := fun _ _ => _root_.id
    equationCoordinateVisibleOn := fun _ _ => _root_.id
    violationWitnessVisibleOn := fun _ _ => _root_.id
    axisReadableOn := fun _ _ => _root_.id
    boundaryVisibleOn := fun _ _ => _root_.id
  }
  overlap := { overlapIso := fun _ _ _ => Iso.refl _ }
  coefficientHom := pairSwap
  raw_eq := by
    change pairPackage.raw =
      rawReindex (G := pairPackage) (H := pairPackage)
        (PackageTotalHom.id pairPackage.core)
        ((pairPackage.raw.baseChange pairSwap).baseChange pairSwap)
    rw [rawReindex_id]
    rw [← LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
    rw [pairSwap_comp]
    exact (LawAlgebra.RawAmbientRestrictionSystem.baseChange_id pairPackage.raw).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Forward total hom of the concrete coefficient fiber action. -/
noncomputable def pairFiberForward : GeometryTotalHom pairPackage pairFiberTarget where
  base := PackageTotalHom.id pairPackage.core
  geometry := pairFiberForwardGeometry

/-- Reverse total hom of the concrete coefficient fiber action. -/
noncomputable def pairFiberInverse : GeometryTotalHom pairFiberTarget pairPackage where
  base := PackageTotalHom.id pairPackage.core
  geometry := pairFiberInverseGeometry

/-- The two concrete coefficient-swap homs form an isomorphism. -/
noncomputable def pairCategoricalIso : pairPackage ≅ pairFiberTarget where
  hom := pairFiberForward
  inv := pairFiberInverse
  hom_inv_id := by
    apply GeometryTotalHom.ext
    · exact Category.comp_id
        (self := AAT.AG.AtomFoundation.PackageTotalHom.packageTotalCategory
          FiniteModel.carrier)
        (PackageTotalHom.id pairPackage.core)
    · apply heq_of_eq
      apply GeomReadHom.ext
      · exact pairSwap_comp
      · rfl
      · rfl
      · rfl
  inv_hom_id := by
    apply GeometryTotalHom.ext
    · exact Category.comp_id
        (self := AAT.AG.AtomFoundation.PackageTotalHom.packageTotalCategory
          FiniteModel.carrier)
        (PackageTotalHom.id pairPackage.core)
    · apply heq_of_eq
      apply GeomReadHom.ext
      · exact pairSwap_comp
      · rfl
      · rfl
      · rfl

/-- Concrete inner-fiber isomorphism with nonidentity coefficient action. -/
noncomputable def pairConcreteFiberIso :
    GeometryFiberInnerIso pairPackage pairFiberTarget rfl where
  iso := pairCategoricalIso
  hom_base_eq := rfl
  inv_base_eq := rfl

/-- The concrete fiber coefficient equivalence swaps the two idempotents. -/
theorem pairConcreteFiberIso_coefficient_fires :
    pairConcreteFiberIso.coefficientEquiv ((1 : Int), (0 : Int)) =
      ((0 : Int), (1 : Int)) := by
  rfl

end NegativeGeometryWitness

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
