import ResearchLean.AG.ObstructionDiagnosticBridge.PointGeneratorAtomInput
import ResearchLean.AG.ObstructionDiagnosticBridge.FiniteContextSupport
import Formal.AG.Site.Geometry
import Formal.Util.AssertStandardAxioms

/-!
# Context support on the combined point/generator carrier

This module lifts the Cycle 12 point-support site to the Cycle 15 carrier that
contains both the eight selected geometric points and the four primitive Law
occurrences.  An open context reads exactly its geometric point Atoms and keeps
every selected generator Atom available.  Its open support is still derived
only from readable point Atoms, so Law occurrences do not manufacture geometry.

## Implementation notes

This is the context, coverage, and site part of Issue #4791 paper design section
10.  Reusing the point-only `AtomCarrier` was rejected because it would erase
the primitive-generator provenance established in Cycle 15.  Giving generator
Atoms artificial points was also rejected because observation must not create
geometric structure.  Instead, the sum carrier is retained and generator Atoms
are readable in every selected open context; this makes the coarse and fine
families cover the full 12-Atom input while `contextSupport` remains the
interior of the genuinely readable point set.
-/

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace AAT.AG.ObstructionDiagnosticBridge
namespace CombinedAtomContextSupport

open SelectedFiniteGeometry PointGeneratorAtomInput

/-- An open context on the Cycle 15 object reads its points and all generators. -/
def openContext (W : Opens Space) : Site.ArchCtx PointGeneratorAtomInput.object where
  minimal := {
    Support := Unit
    Axis := Unit
    Observable := Unit
    supportReads := fun _ atom =>
      match atom with
      | .inl point => point ∈ W
      | .inr _ => True
    supportReads_objectFamily := by simp [PointGeneratorAtomInput.object]
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := Unit
  extension := ()

/-- Point-reading API for selected open contexts.

The simp normal form reduces a point-Atom reading to geometric membership.
-/
@[simp]
theorem openContext_reads_point (W : Opens Space) (point : Point) :
    (openContext W).minimal.supportReads ()
      (PointGeneratorAtomInput.pointAtom point) ↔ point ∈ W :=
  Iff.rfl

/-- Generator-reading API for selected open contexts.

The simp normal form reduces a generator-Atom reading to `True`.
-/
@[simp]
theorem openContext_reads_generator (W : Opens Space)
    (generator : PrimitiveGenerator PointAtomLawInput.laws) :
    (openContext W).minimal.supportReads ()
      (PointGeneratorAtomInput.generatorAtom generator) :=
  trivial

/-- Negative fixture: a valid context that reads points but no generators.

This context is not used by the selected covers.  It witnesses that generator
coverage below is not automatic merely because an Atom is in the object family.
-/
def generatorSilentContext (W : Opens Space) :
    Site.ArchCtx PointGeneratorAtomInput.object where
  minimal := {
    Support := Unit
    Axis := Unit
    Observable := Unit
    supportReads := fun _ atom =>
      match atom with
      | .inl point => point ∈ W
      | .inr _ => False
    supportReads_objectFamily := by simp [PointGeneratorAtomInput.object]
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := Unit
  extension := ()

/-- Point set read by an arbitrary combined-carrier context. -/
def readablePointSet (W : Site.ArchCtx PointGeneratorAtomInput.object) : Set Space :=
  {x | ∃ support : W.Support,
    W.minimal.supportReads support (PointGeneratorAtomInput.pointAtom x)}

/-- Geometric support derived only from readable point Atoms. -/
def contextSupport (W : Site.ArchCtx PointGeneratorAtomInput.object) : Opens Space :=
  Opens.interior (readablePointSet W)

/-- Restriction morphisms make the combined context's readable point set monotone. -/
theorem readablePointSet_mono {W V : Site.ArchCtx PointGeneratorAtomInput.object}
    (f : Site.ContextMorphism W V) (hf : f.IsRestriction) :
    readablePointSet W ⊆ readablePointSet V := by
  rintro x ⟨support, hsupport⟩
  exact ⟨f.supportMap support, hf.1 hsupport⟩

/-- Restriction morphisms induce inclusion of derived geometric supports. -/
theorem contextSupport_mono {W V : Site.ArchCtx PointGeneratorAtomInput.object}
    (f : Site.ContextMorphism W V) (hf : f.IsRestriction) :
    contextSupport W ≤ contextSupport V :=
  interior_mono (readablePointSet_mono f hf)

/-- Canonical thin category of actual restrictions on the combined object. -/
noncomputable abbrev contextPreorder :=
  Site.contextMorphismPreorderCategory PointGeneratorAtomInput.object

/-- Combined-carrier point support as a functor to open sets. -/
def supportFunctor : Site.ContextCategoryObject contextPreorder ⥤ Opens Space where
  obj W := contextSupport W.ctx
  map f := by
    apply homOfLE
    exact contextSupport_mono
      (contextPreorder.morphism (leOfHom f))
      (contextPreorder.morphism_isRestriction (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Open-context support normalizes to the selected open set.

The simp normal form replaces derived support by its geometric open.
-/
@[simp]
theorem contextSupport_openContext (W : Opens Space) :
    contextSupport (openContext W) = W := by
  ext x
  change x ∈ interior (readablePointSet (openContext W)) ↔ x ∈ W
  rw [show readablePointSet (openContext W) = (W : Set Space) by
    ext y
    constructor
    · rintro ⟨_support, hsupport⟩
      exact hsupport
    · intro hy
      exact ⟨(), hy⟩]
  rw [W.isOpen.interior_eq]
  rfl

/-- Product contexts read precisely the intersection of their point sets. -/
theorem readablePointSet_product
    (W V : Site.ArchCtx PointGeneratorAtomInput.object) :
    readablePointSet (Site.productContext W V) =
      readablePointSet W ∩ readablePointSet V := by
  ext x
  constructor
  · rintro ⟨⟨left, right⟩, hleft, hright⟩
    exact ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
  · rintro ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
    exact ⟨⟨left, right⟩, hleft, hright⟩

/-- Product-context support is intersection on the combined object.

The simp normal form replaces product support by the meet of factor supports.
-/
@[simp]
theorem contextSupport_product
    (W V : Site.ArchCtx PointGeneratorAtomInput.object) :
    contextSupport (Site.productContext W V) =
      contextSupport W ⊓ contextSupport V := by
  ext x
  change x ∈ interior
      (readablePointSet (Site.productContext W V)) ↔
    x ∈ interior (readablePointSet W) ∧ x ∈ interior (readablePointSet V)
  rw [readablePointSet_product, interior_inter]
  rfl

/-- Product support of selected open contexts is their open intersection.

The simp normal form replaces the combined construction by the open-set meet.
-/
@[simp]
theorem contextSupport_product_openContext (W V : Opens Space) :
    contextSupport (Site.productContext (openContext W) (openContext V)) = W ⊓ V := by
  rw [contextSupport_product, contextSupport_openContext, contextSupport_openContext]

/-- Inclusion of opens induces a combined-context morphism. -/
def openContextMorphism {W V : Opens Space} (_h : W ≤ V) :
    Site.ContextMorphism (openContext W) (openContext V) where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- The open-context morphism is an actual restriction on both Atom summands. -/
theorem openContextMorphism_isRestriction {W V : Opens Space} (h : W ≤ V) :
    (openContextMorphism h).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hatom
    cases atom with
    | inl point => exact h hatom
    | inr generator => trivial
  · intro axis haxis
    exact haxis
  · intro observable hobservable
    exact hobservable
  · intro support atom hatom
    trivial

/-- Inclusion of opens is represented in the combined context preorder. -/
theorem openContext_le {W V : Opens Space} (h : W ≤ V) :
    contextPreorder.le (openContext W) (openContext V) :=
  ⟨openContextMorphism h, openContextMorphism_isRestriction h⟩

/-- Empty equation component; Cycle 16 changes Atom provenance, not equations. -/
def equationSystem : ArchitecturalEquationSystem contextPreorder where
  Index := Empty
  role := Empty.elim
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ index => nomatch index
  violationCoordinate_restrict := by intros; contradiction
  equationResidual := fun _ _ index => nomatch index
  equationResidual_restrict := by intros; contradiction

/-- Empty signature component; full Atom coverage is carried by support visibility. -/
def signature : ArchitectureSignature PointGeneratorAtomInput.carrier where
  Axis := Empty
  Coordinate := Empty.elim
  selected := Empty.elim
  coordinate := fun _ axis => nomatch axis

/-- Coverage requires every selected point or generator Atom to be visible.

Point visibility is derived from `contextSupport`; every selected primitive
generator remains visible in each open context.  The remaining coordinate
requirements are empty as in the predecessor point-support site.
-/
def coverageRequirements :
    Site.CoverageRequirements PointGeneratorAtomInput.object equationSystem signature where
  requiredSupport := fun _ => True
  requiredEquationCoordinate := fun coordinate => nomatch coordinate.1.1
  selectedViolationWitness := fun coordinate => nomatch coordinate.1
  requiredAxis := Empty.elim
  supportVisibleOn := fun W atom =>
    match atom with
    | .inl point => point ∈ contextSupport W
    | .inr generator => ∃ support : W.Support,
        W.minimal.supportReads support
          (PointGeneratorAtomInput.generatorAtom generator)
  equationCoordinateVisibleOn := fun _ coordinate => nomatch coordinate.1.1
  violationWitnessVisibleOn := fun _ coordinate => nomatch coordinate.1
  axisReadableOn := fun _ axis => nomatch axis
  boundaryVisibleOn := fun _ _ => True

/-- Product contexts supply overlap objects for the combined site. -/
noncomputable def overlap : Site.ContextOverlapPullback contextPreorder :=
  Site.meetOverlapPullback contextPreorder Site.productContextFiniteMeet

/-- AAT site on the actual combined point/generator architecture object. -/
noncomputable def site : Site.AATSite PointGeneratorAtomInput.object where
  contextPreorder := contextPreorder
  equationSystem := equationSystem
  signature := signature
  requirements := coverageRequirements
  overlap := overlap

/-- Full-space base context on the combined object. -/
def baseContext : Site.ArchCtx PointGeneratorAtomInput.object := openContext ⊤

/-- Coarse three-patch family on the combined object. -/
def coarseCoverageFamily : Site.CoverageFamily contextPreorder where
  base := baseContext
  Index := CoarseChart
  patch chart := openContext (coarsePatch chart)
  inclusion _chart := openContext_le le_top

/-- Fine four-patch family on the combined object. -/
def fineCoverageFamily : Site.CoverageFamily contextPreorder where
  base := baseContext
  Index := FineChart
  patch chart := openContext (finePatch chart)
  inclusion _chart := openContext_le le_top

/-- The coarse family covers all point and generator Atoms. -/
theorem coarseCoverageFamily_admissible :
    Site.AdmissibleCover coverageRequirements overlap coarseCoverageFamily := by
  refine {
    atomSupportCoverage := ?_
    equationCoordinateCoverage := ?_
    violationWitnessCoverage := ?_
    signatureAxisCoverage := ?_
    boundaryCoverage := ?_
    nonGeneration := ?_
  }
  · intro atom hatom
    cases atom with
    | inl point =>
        obtain ⟨chart, hx⟩ := coarse_cover point
        exact ⟨chart, by
          simpa [coverageRequirements, coarseCoverageFamily] using hx⟩
    | inr generator =>
        exact ⟨.c0, ⟨(), openContext_reads_generator _ generator⟩⟩
  · intro coordinate
    exact Empty.elim coordinate.1.1
  · intro coordinate
    exact Empty.elim coordinate.1
  · intro axis
    exact Empty.elim axis
  · intros
    trivial
  · intro chart
    exact coarseCoverageFamily.inclusion_nonGenerating chart

/-- The fine family covers all point and generator Atoms. -/
theorem fineCoverageFamily_admissible :
    Site.AdmissibleCover coverageRequirements overlap fineCoverageFamily := by
  refine {
    atomSupportCoverage := ?_
    equationCoordinateCoverage := ?_
    violationWitnessCoverage := ?_
    signatureAxisCoverage := ?_
    boundaryCoverage := ?_
    nonGeneration := ?_
  }
  · intro atom hatom
    cases atom with
    | inl point =>
        obtain ⟨chart, hx⟩ := fine_cover point
        exact ⟨chart, by
          simpa [coverageRequirements, fineCoverageFamily] using hx⟩
    | inr generator =>
        exact ⟨.a0, ⟨(), openContext_reads_generator _ generator⟩⟩
  · intro coordinate
    exact Empty.elim coordinate.1.1
  · intro coordinate
    exact Empty.elim coordinate.1
  · intro axis
    exact Empty.elim axis
  · intros
    trivial
  · intro chart
    exact fineCoverageFamily.inclusion_nonGenerating chart

/-- Coarse chart supports normalize to their geometric patches.

The simp normal form exposes the selected coarse open.
-/
@[simp]
theorem supportFunctor_coarse_patch (chart : CoarseChart) :
    supportFunctor.obj
        (Site.ContextCategoryObject.of contextPreorder
          (coarseCoverageFamily.patch chart)) = coarsePatch chart := by
  exact contextSupport_openContext _

/-- Fine chart supports normalize to their geometric patches.

The simp normal form exposes the selected fine open.
-/
@[simp]
theorem supportFunctor_fine_patch (chart : FineChart) :
    supportFunctor.obj
        (Site.ContextCategoryObject.of contextPreorder
          (fineCoverageFamily.patch chart)) = finePatch chart := by
  exact contextSupport_openContext _

/-- Any combined-site admissible family maps to a pointwise open cover. -/
theorem admissible_support_covers
    {F : Site.CoverageFamily contextPreorder}
    (hF : Site.AdmissibleCover coverageRequirements overlap F)
    (x : Space) :
    ∃ i : F.Index,
      x ∈ supportFunctor.obj
        (Site.ContextCategoryObject.of contextPreorder (F.patch i)) := by
  obtain ⟨i, hi⟩ := hF.atomSupportCoverage (.inl x) trivial
  exact ⟨i, hi⟩

/-- Admissibility exposes an actual patch reading for every generator Atom. -/
theorem admissible_generator_reading
    {F : Site.CoverageFamily contextPreorder}
    (hF : Site.AdmissibleCover coverageRequirements overlap F)
    (generator : PrimitiveGenerator PointAtomLawInput.laws) :
    ∃ i : F.Index, ∃ support : (F.patch i).Support,
      (F.patch i).minimal.supportReads support
        (PointGeneratorAtomInput.generatorAtom generator) := by
  simpa [coverageRequirements] using
    hF.atomSupportCoverage (.inr generator) trivial

/-- A context with no generator readings fails generator visibility. -/
theorem generatorSilentContext_not_generator_visible (W : Opens Space)
    (generator : PrimitiveGenerator PointAtomLawInput.laws) :
    ¬ coverageRequirements.supportVisibleOn (generatorSilentContext W)
      (PointGeneratorAtomInput.generatorAtom generator) := by
  simp [coverageRequirements, generatorSilentContext,
    PointGeneratorAtomInput.generatorAtom]

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.CombinedAtomContextSupport

end CombinedAtomContextSupport
end AAT.AG.ObstructionDiagnosticBridge
