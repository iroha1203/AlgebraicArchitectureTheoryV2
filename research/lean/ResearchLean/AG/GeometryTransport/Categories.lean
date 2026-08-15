import ResearchLean.AG.GeometryTransport.Basic

/-!
# The geometry-stage total category

This module implements the seven-part G-108 geometry-hom contract and forms
the total category over the G-101 core-package category.

## Implementation notes

Coverage data are transported by the fixed forward index maps, while overlap
objects are compared by isomorphism in the target thin context category.
Coefficient transport is a forward `RingHom`; the raw compatibility field is
the equality with coefficient base change followed by inverse-context
reindexing.  The three realization comparison families are computational data,
and their reading preservation and naturality laws are separate propositions.
Opcartesianity is not a field of a geometry morphism.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

/-- Forward preservation of all coverage-requirement predicates. -/
structure CoverageTransport {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (f : PackageTotalHom G.core H.core) : Prop where
  requiredSupport : ∀ atom,
    G.geometry.requirements.requiredSupport atom →
      H.geometry.requirements.requiredSupport (f.upper.atomEquiv atom)
  requiredEquationCoordinate : ∀ coordinate,
    G.geometry.requirements.requiredEquationCoordinate coordinate →
      H.geometry.requirements.requiredEquationCoordinate
        (requiredCoordinateMap f coordinate)
  selectedViolationWitness : ∀ coordinate,
    G.geometry.requirements.selectedViolationWitness coordinate →
      H.geometry.requirements.selectedViolationWitness
        (equationCoordinateMap f coordinate)
  requiredAxis : ∀ axis,
    G.geometry.requirements.requiredAxis axis →
      H.geometry.requirements.requiredAxis (f.upper.axisMap axis)
  supportVisibleOn : ∀ W atom,
    G.geometry.requirements.supportVisibleOn W atom →
      H.geometry.requirements.supportVisibleOn
        (contextMap f W) (f.upper.atomEquiv atom)
  equationCoordinateVisibleOn : ∀ W coordinate,
    G.geometry.requirements.equationCoordinateVisibleOn W coordinate →
      H.geometry.requirements.equationCoordinateVisibleOn
        (contextMap f W) (requiredCoordinateMap f coordinate)
  violationWitnessVisibleOn : ∀ W coordinate,
    G.geometry.requirements.violationWitnessVisibleOn W coordinate →
      H.geometry.requirements.violationWitnessVisibleOn
        (contextMap f W) (equationCoordinateMap f coordinate)
  axisReadableOn : ∀ W axis,
    G.geometry.requirements.axisReadableOn W axis →
      H.geometry.requirements.axisReadableOn
        (contextMap f W) (f.upper.axisMap axis)
  boundaryVisibleOn : ∀ W V,
    G.geometry.requirements.boundaryVisibleOn W V →
      H.geometry.requirements.boundaryVisibleOn
        (contextMap f W) (contextMap f V)

namespace CoverageTransport

/-- Coverage preservation for the identity core morphism. -/
def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    CoverageTransport G G (PackageTotalHom.id G.core) where
  requiredSupport _ := _root_.id
  requiredEquationCoordinate _ := _root_.id
  selectedViolationWitness _ := _root_.id
  requiredAxis _ := _root_.id
  supportVisibleOn _ _ := _root_.id
  equationCoordinateVisibleOn _ _ := _root_.id
  violationWitnessVisibleOn _ _ := _root_.id
  axisReadableOn _ _ := _root_.id
  boundaryVisibleOn _ _ := _root_.id

/-- Coverage preservation composes along the fixed component index maps. -/
def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    {g : PackageTotalHom H.core K.core}
    (F : CoverageTransport G H f) (T : CoverageTransport H K g) :
    CoverageTransport G K (PackageTotalHom.comp f g) where
  requiredSupport atom h := T.requiredSupport _ (F.requiredSupport atom h)
  requiredEquationCoordinate coordinate h := by
    simpa [requiredCoordinateMap] using
      T.requiredEquationCoordinate (requiredCoordinateMap f coordinate)
        (F.requiredEquationCoordinate coordinate h)
  selectedViolationWitness coordinate h := by
    simpa [equationCoordinateMap] using
      T.selectedViolationWitness (equationCoordinateMap f coordinate)
        (F.selectedViolationWitness coordinate h)
  requiredAxis axis h := T.requiredAxis _ (F.requiredAxis axis h)
  supportVisibleOn W atom h :=
    T.supportVisibleOn (contextMap f W) _ (F.supportVisibleOn W atom h)
  equationCoordinateVisibleOn W coordinate h := by
    simpa [requiredCoordinateMap] using
      T.equationCoordinateVisibleOn (contextMap f W)
        (requiredCoordinateMap f coordinate)
        (F.equationCoordinateVisibleOn W coordinate h)
  violationWitnessVisibleOn W coordinate h := by
    simpa [equationCoordinateMap] using
      T.violationWitnessVisibleOn (contextMap f W)
        (equationCoordinateMap f coordinate)
        (F.violationWitnessVisibleOn W coordinate h)
  axisReadableOn W axis h :=
    T.axisReadableOn (contextMap f W) _ (F.axisReadableOn W axis h)
  boundaryVisibleOn W V h :=
    T.boundaryVisibleOn (contextMap f W) (contextMap f V)
      (F.boundaryVisibleOn W V h)

end CoverageTransport

/-- Isomorphism comparison for selected overlap objects. -/
structure OverlapTransport {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (f : PackageTotalHom G.core H.core) where
  overlapIso : ∀ base left right,
    contextForward f
        ⟨G.geometry.overlap.overlap
          (contextBackwardMap f base)
          (contextBackwardMap f left)
          (contextBackwardMap f right)⟩ ≅
      ⟨H.geometry.overlap.overlap
        base left right⟩

namespace OverlapTransport

/-- Overlap comparison for the identity core morphism. -/
def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    OverlapTransport G G (PackageTotalHom.id G.core) where
  overlapIso _ _ _ := Iso.refl _

/-- Overlap comparisons compose by functorial image and transitivity of isomorphisms. -/
def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    {g : PackageTotalHom H.core K.core}
    (F : OverlapTransport G H f) (T : OverlapTransport H K g) :
    OverlapTransport G K (PackageTotalHom.comp f g) where
  overlapIso base left right :=
    ((contextFunctor g).mapIso
      (F.overlapIso
        (contextBackwardMap g base)
        (contextBackwardMap g left)
        (contextBackwardMap g right))).trans
      (T.overlapIso base left right)

/-- The overlap comparison commutes with the left projection. -/
theorem left_comm {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    (T : OverlapTransport G H f)
    {base left right : Site.ArchCtx H.core.object}
    (hl : H.core.contextPreorder.le left base)
    (hr : H.core.contextPreorder.le right base) :
    (T.overlapIso base left right).hom ≫
        homOfLE (H.geometry.overlap.overlap_le_left
          hl hr) =
      (contextFunctor f).map
          (homOfLE (G.geometry.overlap.overlap_le_left
            ((contextInverse f).map (homOfLE hl)).le
            ((contextInverse f).map (homOfLE hr)).le)) ≫
        (f.upper.equationTransport.contextEquivalence.counitIso.hom.app
          ⟨left⟩) := by
  apply Subsingleton.elim

/-- The overlap comparison commutes with the right projection. -/
theorem right_comm {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    (T : OverlapTransport G H f)
    {base left right : Site.ArchCtx H.core.object}
    (hl : H.core.contextPreorder.le left base)
    (hr : H.core.contextPreorder.le right base) :
    (T.overlapIso base left right).hom ≫
        homOfLE (H.geometry.overlap.overlap_le_right
          hl hr) =
      (contextFunctor f).map
          (homOfLE (G.geometry.overlap.overlap_le_right
            ((contextInverse f).map (homOfLE hl)).le
            ((contextInverse f).map (homOfLE hr)).le)) ≫
        (f.upper.equationTransport.contextEquivalence.counitIso.hom.app
          ⟨right⟩) := by
  apply Subsingleton.elim

/-- The overlap comparison commutes with the projection to the common base. -/
theorem base_comm {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    (T : OverlapTransport G H f)
    {base left right : Site.ArchCtx H.core.object}
    (hl : H.core.contextPreorder.le left base)
    (hr : H.core.contextPreorder.le right base) :
    (T.overlapIso base left right).hom ≫
        homOfLE (H.geometry.overlap.overlap_le_base
          hl hr) =
      (contextFunctor f).map
          (homOfLE (G.geometry.overlap.overlap_le_base
            ((contextInverse f).map (homOfLE hl)).le
            ((contextInverse f).map (homOfLE hr)).le)) ≫
        (f.upper.equationTransport.contextEquivalence.counitIso.hom.app
          ⟨base⟩) := by
  apply Subsingleton.elim

/-- The transported source overlap retains the universal lifting property:
the target-selected lift factors through the inverse comparison isomorphism. -/
theorem lift_preserved {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    (T : OverlapTransport G H f)
    {base left right X : Site.ArchCtx H.core.object}
    (hl : H.core.contextPreorder.le left base)
    (hr : H.core.contextPreorder.le right base)
    (hXl : H.core.contextPreorder.le X left)
    (hXr : H.core.contextPreorder.le X right) :
    H.core.contextPreorder.le X
      (contextMap f
        (G.geometry.overlap.overlap
          (contextBackwardMap f base)
          (contextBackwardMap f left)
          (contextBackwardMap f right))) := by
  exact H.core.contextPreorder.trans
    (H.geometry.overlap.overlap_lift hl hr hXl hXr)
    (T.overlapIso base left right).inv.le

end OverlapTransport

/-- Coverage-preservation proofs are propositionally unique. -/
instance coverageTransportSubsingleton {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (f : PackageTotalHom G.core H.core) :
    Subsingleton (CoverageTransport G H f) :=
  ⟨fun _ _ => by rfl⟩

/-- Overlap comparisons are unique in the selected thin context category. -/
instance overlapTransportSubsingleton {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (f : PackageTotalHom G.core H.core) :
    Subsingleton (OverlapTransport G H f) := by
  constructor
  intro F T
  cases F with
  | mk Fiso =>
      cases T with
      | mk Tiso =>
          congr
          funext base left right
          exact Subsingleton.elim _ _

/-- The selected context morphism underlying a source category arrow. -/
abbrev sourceContextMorphism {U : AtomCarrier.{u}}
    {G : GeometryPackage.{u, v} U}
    {W V : G.site.category} (w : W ⟶ V) :=
  G.core.contextPreorder.morphism (leOfHom w)

/-- The selected target context morphism underlying the mapped arrow. -/
abbrev targetContextMorphism {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    {W V : G.site.category} (w : W ⟶ V) :=
  H.core.contextPreorder.morphism
    (leOfHom ((contextFunctor f).map w))

/--
Low-level realization transport supply along a core-package morphism.

This structure contains only the three local-carrier comparison families,
their reading laws, their naturality, and the mapped non-generation law.  It
does not mention a geometry lift, coverage transport, coefficients, or raw
systems, so it is not a disguised `GeomReadHom` certificate.
-/
structure RealizationTransportSupply {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) (f : PackageTotalHom P Q) where
  supportComp : ∀ W : Site.ContextCategoryObject P.contextPreorder,
    W.ctx.Support → ((coreContextFunctor f).obj W).ctx.Support
  axisComp : ∀ W : Site.ContextCategoryObject P.contextPreorder,
    W.ctx.Axis → ((coreContextFunctor f).obj W).ctx.Axis
  observableComp : ∀ W : Site.ContextCategoryObject P.contextPreorder,
    W.ctx.Observable → ((coreContextFunctor f).obj W).ctx.Observable
  supportReads : ∀ (W : Site.ContextCategoryObject P.contextPreorder) support atom,
    W.ctx.minimal.supportReads support atom →
      ((coreContextFunctor f).obj W).ctx.minimal.supportReads
        (supportComp W support) (f.upper.atomEquiv atom)
  axisReads : ∀ (W : Site.ContextCategoryObject P.contextPreorder) axis,
    W.ctx.minimal.axisReads axis →
      ((coreContextFunctor f).obj W).ctx.minimal.axisReads (axisComp W axis)
  observableReads : ∀ (W : Site.ContextCategoryObject P.contextPreorder) observable,
    W.ctx.minimal.observableReads observable →
      ((coreContextFunctor f).obj W).ctx.minimal.observableReads
        (observableComp W observable)
  support_naturality : ∀ {W V : Site.ContextCategoryObject P.contextPreorder}
      (w : W ⟶ V) support,
    (Q.contextPreorder.morphism
      (leOfHom ((coreContextFunctor f).map w))).supportMap
        (supportComp W support) =
      supportComp V
        ((P.contextPreorder.morphism (leOfHom w)).supportMap support)
  axis_naturality : ∀ {W V : Site.ContextCategoryObject P.contextPreorder}
      (w : W ⟶ V) axis,
    (Q.contextPreorder.morphism
      (leOfHom ((coreContextFunctor f).map w))).axisMap
        (axisComp W axis) =
      axisComp V ((P.contextPreorder.morphism (leOfHom w)).axisMap axis)
  observable_naturality : ∀ {W V : Site.ContextCategoryObject P.contextPreorder}
      (w : W ⟶ V) observable,
    (Q.contextPreorder.morphism
      (leOfHom ((coreContextFunctor f).map w))).observableRestrict
        (observableComp V observable) =
      observableComp W
        ((P.contextPreorder.morphism (leOfHom w)).observableRestrict observable)
  mappedNonGeneration : ∀ {W V : Site.ContextCategoryObject P.contextPreorder}
      (w : W ⟶ V),
    Site.SupportMapNonGenerating
      ((coreContextFunctor f).obj W).ctx ((coreContextFunctor f).obj V).ctx
      (Q.contextPreorder.morphism
        (leOfHom ((coreContextFunctor f).map w))).supportMap

/-- G-108's named realization hypothesis for a geometry package over `P`. -/
abbrev HGeom {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    {Q : AATCorePackage U} (f : PackageTotalHom G.core Q) :=
  RealizationTransportSupply G.core Q f

/--
A geometry-stage morphism over one G-101 core-package morphism.

The compatibility propositions implement the fixed G-108 hom contract.  The
only computational fields are the coefficient map, overlap comparison, and
the three context-indexed realization comparison families.
-/
structure GeomReadHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (baseHom : PackageTotalHom G.core H.core) where
  coverage : CoverageTransport G H baseHom
  overlap : OverlapTransport G H baseHom
  coefficientHom : G.Coefficient →+* H.Coefficient
  raw_eq : H.raw = rawTransport baseHom coefficientHom
  supportComp : ∀ W : G.site.category,
    W.ctx.Support → (contextForward baseHom W).ctx.Support
  axisComp : ∀ W : G.site.category,
    W.ctx.Axis → (contextForward baseHom W).ctx.Axis
  observableComp : ∀ W : G.site.category,
    W.ctx.Observable → (contextForward baseHom W).ctx.Observable
  supportReads : ∀ (W : G.site.category) support atom,
    W.ctx.minimal.supportReads support atom →
      (contextForward baseHom W).ctx.minimal.supportReads
        (supportComp W support) (baseHom.upper.atomEquiv atom)
  axisReads : ∀ (W : G.site.category) axis,
    W.ctx.minimal.axisReads axis →
      (contextForward baseHom W).ctx.minimal.axisReads (axisComp W axis)
  observableReads : ∀ (W : G.site.category) observable,
    W.ctx.minimal.observableReads observable →
      (contextForward baseHom W).ctx.minimal.observableReads
        (observableComp W observable)
  support_naturality : ∀ {W V : G.site.category} (w : W ⟶ V) support,
    (targetContextMorphism (f := baseHom) w).supportMap (supportComp W support) =
      supportComp V ((sourceContextMorphism w).supportMap support)
  axis_naturality : ∀ {W V : G.site.category} (w : W ⟶ V) axis,
    (targetContextMorphism (f := baseHom) w).axisMap (axisComp W axis) =
      axisComp V ((sourceContextMorphism w).axisMap axis)
  observable_naturality : ∀ {W V : G.site.category} (w : W ⟶ V) observable,
    (targetContextMorphism (f := baseHom) w).observableRestrict
        (observableComp V observable) =
      observableComp W
        ((sourceContextMorphism w).observableRestrict observable)

namespace GeomReadHom

/-- Identity geometry morphism. -/
noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    GeomReadHom G G (PackageTotalHom.id G.core) where
  coverage := CoverageTransport.id G
  overlap := OverlapTransport.id G
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := rawTransport_id G |>.symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Composition of geometry morphisms over composition in the core total category. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    {g : PackageTotalHom H.core K.core}
    (F : GeomReadHom G H f) (T : GeomReadHom H K g) :
    GeomReadHom G K (PackageTotalHom.comp f g) where
  coverage := F.coverage.comp T.coverage
  overlap := F.overlap.comp T.overlap
  coefficientHom := T.coefficientHom.comp F.coefficientHom
  raw_eq := by
    calc
      K.raw = rawTransport g T.coefficientHom := T.raw_eq
      _ = rawReindex g (H.raw.baseChange T.coefficientHom) := rfl
      _ = rawReindex g
          ((rawTransport f F.coefficientHom).baseChange T.coefficientHom) := by
            rw [F.raw_eq]
      _ = rawTransport (PackageTotalHom.comp f g)
          (T.coefficientHom.comp F.coefficientHom) :=
            (rawTransport_comp f g F.coefficientHom T.coefficientHom).symm
  supportComp W support := T.supportComp (contextForward f W) (F.supportComp W support)
  axisComp W axis := T.axisComp (contextForward f W) (F.axisComp W axis)
  observableComp W observable :=
    T.observableComp (contextForward f W) (F.observableComp W observable)
  supportReads W support atom h :=
    T.supportReads (contextForward f W) _ _ (F.supportReads W support atom h)
  axisReads W axis h :=
    T.axisReads (contextForward f W) _ (F.axisReads W axis h)
  observableReads W observable h :=
    T.observableReads (contextForward f W) _ (F.observableReads W observable h)
  support_naturality {W V} w support := by
    rw [T.support_naturality ((contextFunctor f).map w), F.support_naturality w]
  axis_naturality {W V} w axis := by
    rw [T.axis_naturality ((contextFunctor f).map w), F.axis_naturality w]
  observable_naturality {W V} w observable := by
    rw [T.observable_naturality ((contextFunctor f).map w),
      F.observable_naturality w]

/-- Geometry homs are determined by their computational comparison data. -/
@[ext (iff := false)] theorem ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {F T : GeomReadHom G H baseHom}
    (hcoefficient : F.coefficientHom = T.coefficientHom)
    (hsupport : HEq F.supportComp T.supportComp)
    (haxis : HEq F.axisComp T.axisComp)
    (hobservable : HEq F.observableComp T.observableComp) : F = T := by
  have hcoverage : F.coverage = T.coverage := Subsingleton.elim _ _
  have hoverlap : F.overlap = T.overlap := Subsingleton.elim _ _
  cases F
  cases T
  cases hcoverage
  cases hoverlap
  cases hcoefficient
  cases hsupport
  cases haxis
  cases hobservable
  rfl

end GeomReadHom

/-- A morphism in the geometry-stage total category. -/
structure GeometryTotalHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  base : PackageTotalHom G.core H.core
  geometry : GeomReadHom G H base

namespace GeometryTotalHom

/-- Total identity morphism. -/
noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    GeometryTotalHom G G where
  base := PackageTotalHom.id G.core
  geometry := GeomReadHom.id G

/-- Total composition. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (F : GeometryTotalHom G H) (T : GeometryTotalHom H K) :
    GeometryTotalHom G K where
  base := PackageTotalHom.comp F.base T.base
  geometry := F.geometry.comp T.geometry

/-- Total homs are determined by their base and geometry components. -/
@[ext (iff := false)] theorem ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {F T : GeometryTotalHom G H}
    (hbase : F.base = T.base)
    (hgeometry : HEq F.geometry T.geometry) : F = T := by
  cases F
  cases T
  cases hbase
  cases hgeometry
  rfl

end GeometryTotalHom

/-- The object type `GeomRead_U` of the geometry-stage total category. -/
abbrev GeomReadCategory (U : AtomCarrier.{u}) := GeometryPackage.{u, v} U

/-- Geometry packages and contract-preserving morphisms form `GeomRead_U`. -/
noncomputable instance geometryTotalCategory (U : AtomCarrier.{u}) :
    Category (GeomReadCategory.{u, v} U) where
  Hom := GeometryTotalHom
  id := GeometryTotalHom.id
  comp := GeometryTotalHom.comp
  id_comp := by
    intro G H F
    apply GeometryTotalHom.ext
    · apply PackageTotalHom.ext
      · apply ExtInstHom.ext
        apply ExactDoctrineHom.ext
        · rfl
        · apply Equiv.ext
          intro atom
          rfl
      · exact PackageTotalHom.upper_id_comp F.base.upper
    · apply heq_of_eq
      apply GeomReadHom.ext <;> rfl
  comp_id := by
    intro G H F
    apply GeometryTotalHom.ext
    · apply PackageTotalHom.ext
      · apply ExtInstHom.ext
        apply ExactDoctrineHom.ext
        · rfl
        · apply Equiv.ext
          intro atom
          rfl
      · exact PackageTotalHom.upper_comp_id F.base.upper
    · apply heq_of_eq
      apply GeomReadHom.ext <;> rfl
  assoc := by
    intro G H K L F T S
    apply GeometryTotalHom.ext
    · apply PackageTotalHom.ext
      · apply ExtInstHom.ext
        apply ExactDoctrineHom.ext
        · rfl
        · apply Equiv.ext
          intro atom
          rfl
      · exact PackageTotalHom.upper_comp_assoc
          F.base.upper T.base.upper S.base.upper
    · apply heq_of_eq
      apply GeomReadHom.ext <;> rfl

/-- Forget the geometry-stage data and retain the underlying G-101 package. -/
noncomputable def geometryProjection (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ AATCorePackage U where
  obj G := G.core
  map F := F.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection maps a total geometry hom to its actual core morphism. -/
@[simp] theorem geometryProjection_map {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U} (F : G ⟶ H) :
    (geometryProjection U).map F = (show GeometryTotalHom G H from F).base := by
  rfl

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
