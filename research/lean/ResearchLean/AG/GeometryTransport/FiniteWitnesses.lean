import ResearchLean.AG.GeometryTransport.Supply
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

theorem cover_mem_topology :
    Sieve.generate cover.presieve ∈ package.site.topology base :=
  Site.AATGrothendieckTopology.generate_mem cover

theorem coefficient_nontrivial : (2 : package.Coefficient) ≠ 0 := by
  change (2 : Int) ≠ 0
  norm_num

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

theorem coreHom_profile_componentA_false :
    ¬ coreSupportReadProfile coreHom base
      FiniteModel.FiniteAtom.componentA := by
  rintro ⟨support, hread⟩
  cases support
  exact coreHom_context_does_not_read_componentB hread

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
  target : AATCorePackage FiniteModel.carrier
  hom : PackageTotalHom exactSourceCore target
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

/-- The core-stage arrow itself is an inhabited lift over its exact lower
doctrine map. -/
theorem core_stage_lift_exists :
    Nonempty (PackageTotalHom exactSourceCore exactTargetCore) :=
  ⟨coreHom⟩

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

theorem targetCandidate_core : targetCandidate.core = exactTargetCore :=
  rfl

theorem target_candidate_class_nonempty :
    Nonempty {K : GeometryPackage.{0, 0} FiniteModel.carrier //
      K.core = exactTargetCore} :=
  ⟨⟨targetCandidate, targetCandidate_core⟩⟩

/-! ### Nontrivial component transport firing -/

/-- Asymmetric coefficient ring used to make raw base change observable
without changing the coefficient type. -/
abbrev PairCoefficient := Int × Int

noncomputable def pairRelationFamily (W : site.category) :
    LawAlgebra.StructuralRelationFamily (coordFamily W) PairCoefficient where
  Relation := Unit
  polynomial := fun _ =>
    MvPolynomial.C ((1 : Int), (0 : Int)) * MvPolynomial.X ()

noncomputable def pairCoordinateRestriction {X Y : site.category} (w : X ⟶ Y) :
    LawAlgebra.TypedCoordinateRestriction (coordFamily X) (coordFamily Y)
      PairCoefficient (site.contextPreorder.morphism (leOfHom w)) where
  variableImage := fun _ => MvPolynomial.X ()

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

/-- Nontrivial source package for simultaneous site and raw firing. -/
noncomputable def pairPackage : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := exactSourceCore
  geometry := selectedGeometry
  Coefficient := PairCoefficient
  coefficientCommRing := inferInstance
  raw := pairRaw

/-- Swap the two coefficient factors. -/
def pairSwap : PairCoefficient →+* PairCoefficient :=
  (RingEquiv.prodComm : Int × Int ≃+* Int × Int).toRingHom

/-- Non-realization component transport along the nonidentity core hom and
nonidentity coefficient automorphism. -/
noncomputable def changedPackage : GeometryPackage.{0, 0} FiniteModel.carrier :=
  pushGeometryPackageWithCoefficient pairPackage coreHom PairCoefficient pairSwap

def pairBase : pairPackage.site.category := ⟨obstructionContext⟩

/-- The pushed site genuinely changes the selected required-support value. -/
theorem source_not_requires_componentB :
    ¬ pairPackage.geometry.requirements.requiredSupport
      FiniteModel.FiniteAtom.componentB := by
  intro h
  exact FiniteModel.FiniteAtom.noConfusion h

theorem target_requires_componentB :
    changedPackage.geometry.requirements.requiredSupport
      FiniteModel.FiniteAtom.componentB := by
  exact ⟨FiniteModel.FiniteAtom.componentA, rfl, rfl⟩

/-- The source raw relation carries the first coefficient idempotent. -/
theorem pairRaw_source_value :
    (pairPackage.raw.relationFamily pairBase).polynomial () =
      MvPolynomial.C ((1 : Int), (0 : Int)) * MvPolynomial.X () :=
  rfl

/-- After transport, the same relation carries the swapped coefficient. -/
theorem pairRaw_target_value :
    (changedPackage.raw.relationFamily
      (contextForward coreHom pairBase)).polynomial () =
      MvPolynomial.C ((0 : Int), (1 : Int)) * MvPolynomial.X () := by
  change MvPolynomial.map pairSwap
      (MvPolynomial.C ((1 : Int), (0 : Int)) * MvPolynomial.X ()) =
    MvPolynomial.C ((0 : Int), (1 : Int)) * MvPolynomial.X ()
  have hswap : pairSwap ((1 : Int), (0 : Int)) =
      ((0 : Int), (1 : Int)) := rfl
  rw [map_mul]
  erw [MvPolynomial.map_C]
  rw [hswap, MvPolynomial.map_X]
  rfl

/-- Raw transport changes an actual polynomial value, not merely an index
type. -/
theorem pairRaw_value_changes :
    (pairPackage.raw.relationFamily pairBase).polynomial () ≠
      (changedPackage.raw.relationFamily
        (contextForward coreHom pairBase)).polynomial () := by
  rw [pairRaw_source_value, pairRaw_target_value]
  intro h
  have heval := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id PairCoefficient)
      (fun _ : Unit => ((1 : Int), (1 : Int)))) h
  norm_num at heval

end NegativeGeometryWitness

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
