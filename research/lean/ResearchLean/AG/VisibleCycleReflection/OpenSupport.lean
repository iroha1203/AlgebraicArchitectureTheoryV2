import ResearchLean.AG.VisibleCycleReflection.AtomInput
import Formal.AG.Site.Geometry
import Formal.Util.AssertStandardAxioms

/-!
# G-132: AAT site from arbitrary topological and primitive-generator input

## Implementation notes

This generalizes G-125's combined-Atom site without its eight-point geometry
or four-generator presentation. Supports are interiors of readable point sets.
The coverage requires point visibility in these derived opens, and generator
readability independently. Products preserve intersections, and input open
covers are proved admissible using their pointwise coverage and nonempty index.
-/

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace AAT.AG.VisibleCycleReflection
namespace OpenSupport

open CanonicalResolution ObstructionDiagnosticBridge

universe u

variable {Source X : Type u} {laws : FiniteLawFamily Source}
variable (P : GeneratorPresentation laws) [TopologicalSpace X]

/-- A: an open reads its geometric point Atoms and every primitive generator. -/
def openContext (W : Opens X) : Site.ArchCtx (architectureObject X P) where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom =>
      match atom with
      | .inl point => point ∈ W
      | .inr _ => True
    supportReads_objectFamily := by simp [architectureObject]
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- A: point readings in the open context are exactly geometric membership. -/
@[simp]
theorem openContext_reads_point (W : Opens X) (point : X) :
    ((openContext P) W).minimal.supportReads PUnit.unit
      (.inl point) ↔ point ∈ W :=
  Iff.rfl

/-- A: each declared generator is readable in every constructed open context. -/
@[simp]
theorem openContext_reads_generator (W : Opens X)
    (generator : PrimitiveGenerator laws) :
    ((openContext P) W).minimal.supportReads PUnit.unit
      (.inr generator) :=
  trivial

/-- A: a negative visibility fixture reads points while omitting all generators. -/
def generatorSilentContext (W : Opens X) :
    Site.ArchCtx (architectureObject X P) where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom =>
      match atom with
      | .inl point => point ∈ W
      | .inr _ => False
    supportReads_objectFamily := by simp [architectureObject]
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- A: extract the geometrically readable point set of an arbitrary context. -/
def readablePointSet (W : Site.ArchCtx (architectureObject X P)) : Set X :=
  {x | ∃ support : W.Support,
    W.minimal.supportReads support (.inl x)}

/-- A: the open support is the interior of the actual readable point set. -/
def contextSupport (W : Site.ArchCtx (architectureObject X P)) : Opens X :=
  Opens.interior ((readablePointSet P) W)

omit [TopologicalSpace X] in
/-- A: restriction maps preserve readable point membership. -/
theorem readablePointSet_mono {W V : Site.ArchCtx (architectureObject X P)}
    (f : Site.ContextMorphism W V) (hf : f.IsRestriction) :
    (readablePointSet P) W ⊆ (readablePointSet P) V := by
  rintro x ⟨support, hsupport⟩
  exact ⟨f.supportMap support, hf.1 hsupport⟩

/-- A: restrictions induce inclusions of derived open supports. -/
theorem contextSupport_mono {W V : Site.ArchCtx (architectureObject X P)}
    (f : Site.ContextMorphism W V) (hf : f.IsRestriction) :
    (contextSupport P) W ≤ (contextSupport P) V :=
  interior_mono ((readablePointSet_mono P) f hf)

/-- A: the canonical thin category of actual context restrictions. -/
noncomputable abbrev contextPreorder :=
  Site.contextMorphismPreorderCategory (architectureObject X P)

/-- A: send actual context restrictions to inclusions of their open supports. -/
def supportFunctor : Site.ContextCategoryObject (contextPreorder (X := X) P) ⥤ Opens X where
  obj W := (contextSupport P) W.ctx
  map f := by
    apply homOfLE
    exact (contextSupport_mono P)
      ((contextPreorder (X := X) P).morphism (leOfHom f))
      ((contextPreorder (X := X) P).morphism_isRestriction (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- A: the support of a constructed open context is exactly its input open. -/
@[simp]
theorem contextSupport_openContext (W : Opens X) :
    (contextSupport P) ((openContext P) W) = W := by
  ext x
  change x ∈ interior ((readablePointSet P) ((openContext P) W)) ↔ x ∈ W
  rw [show (readablePointSet P) ((openContext P) W) = (W : Set X) by
    ext y
    constructor
    · rintro ⟨_support, hsupport⟩
      exact hsupport
    · intro hy
      exact ⟨PUnit.unit, hy⟩]
  rw [W.isOpen.interior_eq]
  rfl

omit [TopologicalSpace X] in
/-- A: product contexts read the intersection of the two point sets. -/
theorem readablePointSet_product
    (W V : Site.ArchCtx (architectureObject X P)) :
    (readablePointSet P) (Site.productContext W V) =
      (readablePointSet P) W ∩ (readablePointSet P) V := by
  ext x
  constructor
  · rintro ⟨⟨left, right⟩, hleft, hright⟩
    exact ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
  · rintro ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
    exact ⟨⟨left, right⟩, hleft, hright⟩

/-- A: support preserves products as actual intersections of opens. -/
@[simp]
theorem contextSupport_product
    (W V : Site.ArchCtx (architectureObject X P)) :
    (contextSupport P) (Site.productContext W V) =
      (contextSupport P) W ⊓ (contextSupport P) V := by
  ext x
  change x ∈ interior
      ((readablePointSet P) (Site.productContext W V)) ↔
    x ∈ interior ((readablePointSet P) W) ∧ x ∈ interior ((readablePointSet P) V)
  rw [(readablePointSet_product P), interior_inter]
  rfl

/-- A: products of constructed open contexts have the given open intersection. -/
@[simp]
theorem contextSupport_product_openContext (W V : Opens X) :
    (contextSupport P) (Site.productContext ((openContext P) W) ((openContext P) V)) = W ⊓ V := by
  rw [(contextSupport_product P), (contextSupport_openContext P), (contextSupport_openContext P)]

/-- A: an inclusion of opens gives an actual context morphism. -/
def openContextMorphism {W V : Opens X} (_h : W ≤ V) :
    Site.ContextMorphism ((openContext P) W) ((openContext P) V) where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- A: the open inclusion preserves readings and does not generate Atoms. -/
theorem openContextMorphism_isRestriction {W V : Opens X} (h : W ≤ V) :
    ((openContextMorphism P) h).IsRestriction := by
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

/-- A: open inclusion is a morphism in the canonical context preorder. -/
theorem openContext_le {W V : Opens X} (h : W ≤ V) :
    (contextPreorder (X := X) P).le ((openContext P) W) ((openContext P) V) :=
  ⟨(openContextMorphism P) h, (openContextMorphism_isRestriction P) h⟩

/-- A: the point/generator coverage uses no additional equation coordinates. -/
def equationSystem : ArchitecturalEquationSystem (contextPreorder (X := X) P) where
  Index := PEmpty
  role := PEmpty.elim
  Observable := fun _ => ULift.{u} Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id (ULift.{u} Int)
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ index => nomatch index
  violationCoordinate_restrict := by intros; contradiction
  equationResidual := fun _ _ index => nomatch index
  equationResidual_restrict := by intros; contradiction

/-- A: point/generator support requirements use no additional signature axes. -/
def signature : ArchitectureSignature (atomCarrier X laws) where
  Axis := PEmpty
  Coordinate := PEmpty.elim
  selected := PEmpty.elim
  coordinate := fun _ axis => nomatch axis

/-- A: admissibility requires actual open point visibility and generator readability. -/
def coverageRequirements :
    Site.CoverageRequirements (architectureObject X P) (equationSystem (X := X) P) (signature (X := X) (laws := laws)) where
  requiredSupport := fun _ => True
  requiredEquationCoordinate := fun coordinate => nomatch coordinate.1.1
  selectedViolationWitness := fun coordinate => nomatch coordinate.1
  requiredAxis := PEmpty.elim
  supportVisibleOn := fun W atom =>
    match atom with
    | .inl point => point ∈ (contextSupport P) W
    | .inr generator => ∃ support : W.Support,
        W.minimal.supportReads support
          (.inr generator)
  equationCoordinateVisibleOn := fun _ coordinate => nomatch coordinate.1.1
  violationWitnessVisibleOn := fun _ coordinate => nomatch coordinate.1
  axisReadableOn := fun _ axis => nomatch axis
  boundaryVisibleOn := fun _ _ => True

/-- A: actual product contexts supply overlap pullbacks. -/
noncomputable def overlap : Site.ContextOverlapPullback (contextPreorder (X := X) P) :=
  Site.meetOverlapPullback (contextPreorder (X := X) P) Site.productContextFiniteMeet

/-- A: assemble the AAT site from the supplied primitive relation and point supports. -/
noncomputable def site : Site.AATSite (architectureObject X P) where
  contextPreorder := (contextPreorder (X := X) P)
  equationSystem := (equationSystem (X := X) P)
  signature := (signature (X := X) (laws := laws))
  requirements := (coverageRequirements (X := X) P)
  overlap := (overlap (X := X) P)

/-- A: an admissible family covers every geometric point by an actual open support. -/
theorem admissible_support_covers
    {F : Site.CoverageFamily (contextPreorder (X := X) P)}
    (hF : Site.AdmissibleCover (coverageRequirements (X := X) P) (overlap (X := X) P) F)
    (x : X) :
    ∃ i : F.Index,
      x ∈ (supportFunctor (X := X) P).obj
        (Site.ContextCategoryObject.of (contextPreorder (X := X) P) (F.patch i)) := by
  obtain ⟨i, hi⟩ := hF.atomSupportCoverage (.inl x) trivial
  exact ⟨i, hi⟩

/-- A: admissibility exposes a patch reading for every primitive generator. -/
theorem admissible_generator_reading
    {F : Site.CoverageFamily (contextPreorder (X := X) P)}
    (hF : Site.AdmissibleCover (coverageRequirements (X := X) P) (overlap (X := X) P) F)
    (generator : PrimitiveGenerator laws) :
    ∃ i : F.Index, ∃ support : (F.patch i).Support,
      (F.patch i).minimal.supportReads support
        (.inr generator) := by
  simpa [coverageRequirements] using
    hF.atomSupportCoverage (.inr generator) trivial

/-- A: the negative visibility fixture fails the generator requirement. -/
theorem generatorSilentContext_not_generator_visible (W : Opens X)
    (generator : PrimitiveGenerator laws) :
    ¬ (coverageRequirements (X := X) P).supportVisibleOn ((generatorSilentContext P) W)
      (.inr generator) := by
  simp [coverageRequirements, generatorSilentContext]

/-- A's open cover family, generated from the given charts. -/
def coverageFamily {I : Type u} (patch : I → Opens X) :
    Site.CoverageFamily ((contextPreorder (X := X) P)) where
  base := (openContext P) ⊤
  Index := I
  patch i := (openContext P) (patch i)
  inclusion _ := (openContext_le P) le_top

/-- A's admissibility is derived from point coverage and a nonempty chart index. -/
theorem coverageFamily_admissible {I : Type u} [Nonempty I]
    (patch : I → Opens X) (hcovers : ∀ x : X, ∃ i, x ∈ patch i) :
    Site.AdmissibleCover ((coverageRequirements (X := X) P)) ((overlap (X := X) P)) (coverageFamily P patch) := by
  refine {
    atomSupportCoverage := ?_
    equationCoordinateCoverage := ?_
    violationWitnessCoverage := ?_
    signatureAxisCoverage := ?_
    boundaryCoverage := ?_
    nonGeneration := ?_
  }
  · intro atom _hatom
    cases atom with
    | inl point =>
        obtain ⟨i, hx⟩ := hcovers point
        exact ⟨i, by simpa [coverageRequirements, coverageFamily] using hx⟩
    | inr generator =>
        exact ⟨Classical.arbitrary I, ⟨PUnit.unit, openContext_reads_generator P _ generator⟩⟩
  · intro coordinate
    exact PEmpty.elim coordinate.1.1
  · intro coordinate
    exact PEmpty.elim coordinate.1
  · intro axis
    exact PEmpty.elim axis
  · intros
    trivial
  · intro i
    exact (coverageFamily P patch).inclusion_nonGenerating i

end OpenSupport
end AAT.AG.VisibleCycleReflection

#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.OpenSupport
