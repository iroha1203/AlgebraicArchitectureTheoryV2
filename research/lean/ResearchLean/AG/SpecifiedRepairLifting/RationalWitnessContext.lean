import ResearchLean.AG.SpecifiedRepairLifting.RationalWitnessGeometry
import Formal.AG.Site.Geometry
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # W1の三点と一生成元からの実contextとsite

Implementation notes: 原始Atomは三幾何点と一生成元の直和。
開支持は点Atomの読み取り集合の内部から生成し、生成元Atomは幾何を増やさない。
元のAAT admissible topologyを用い、空の被覆だけの位相に置換しない。
既存G-125のcombined-context構成の証明経路をこの固定原始入力に適用する。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Set TopologicalSpace
namespace AAT.AG.SpecifiedRepairLifting.RationalWitnessContext
open RationalWitnessGeometry ObstructionDiagnosticBridge
/-- 三幾何点と一生成元を保持する原始carrier。 -/
def carrier : AtomCarrier where
  AtomKind := Unit
  Axis := Unit
  Subject := Unit
  Predicate := Unit
  Payload := Unit
  Atom := Point ⊕ Unit
  kind := fun _ => ()
  axis := fun _ => ()
  subject := fun _ => ()
  predicate := fun _ => ()
  payload := fun _ => ()
/-- 固定された全四Atomのarchitecture object。 -/
def object : ArchitectureObject carrier where
  configuration := {
    family := ⟨fun _ => True⟩
    relation := fun _ _ => False
    identification := fun _ _ => False
  }
  StructureMaps := Unit
  SelectedQuantities := Unit
  structureMaps := ()
  selectedQuantities := ()
/-- An open context on the W1 object reads its points and all generators. -/
def openContext (W : Opens Space) : Site.ArchCtx object where
  minimal := {
    Support := Unit
    Axis := Unit
    Observable := Unit
    supportReads := fun _ atom =>
      match atom with
      | .inl point => point ∈ W
      | .inr _ => True
    supportReads_objectFamily := by simp [object]
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
      (Sum.inl point) ↔ point ∈ W :=
  Iff.rfl

/-- Generator-reading API for selected open contexts.

The simp normal form reduces a generator-Atom reading to `True`.
-/
@[simp]
theorem openContext_reads_generator (W : Opens Space)
    (generator : Unit) :
    (openContext W).minimal.supportReads ()
      (Sum.inr generator) :=
  trivial

/-- Point set read by an arbitrary W1-carrier context. -/
def readablePointSet (W : Site.ArchCtx object) : Set Space :=
  {x | ∃ support : W.Support,
    W.minimal.supportReads support (Sum.inl x)}

/-- Geometric support derived only from readable point Atoms. -/
def contextSupport (W : Site.ArchCtx object) : Opens Space :=
  Opens.interior (readablePointSet W)

/-- Restriction morphisms make the W1 context's readable point set monotone. -/
theorem readablePointSet_mono {W V : Site.ArchCtx object}
    (f : Site.ContextMorphism W V) (hf : f.IsRestriction) :
    readablePointSet W ⊆ readablePointSet V := by
  rintro x ⟨support, hsupport⟩
  exact ⟨f.supportMap support, hf.1 hsupport⟩

/-- Restriction morphisms induce inclusion of derived geometric supports. -/
theorem contextSupport_mono {W V : Site.ArchCtx object}
    (f : Site.ContextMorphism W V) (hf : f.IsRestriction) :
    contextSupport W ≤ contextSupport V :=
  interior_mono (readablePointSet_mono f hf)

/-- Canonical thin category of actual restrictions on the W1 object. -/
noncomputable abbrev contextPreorder :=
  Site.contextMorphismPreorderCategory object

/-- W1-carrier point support as a functor to open sets. -/
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
    (W V : Site.ArchCtx object) :
    readablePointSet (Site.productContext W V) =
      readablePointSet W ∩ readablePointSet V := by
  ext x
  constructor
  · rintro ⟨⟨left, right⟩, hleft, hright⟩
    exact ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
  · rintro ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
    exact ⟨⟨left, right⟩, hleft, hright⟩

/-- Product-context support is intersection on the W1 object.

The simp normal form replaces product support by the meet of factor supports.
-/
@[simp]
theorem contextSupport_product
    (W V : Site.ArchCtx object) :
    contextSupport (Site.productContext W V) =
      contextSupport W ⊓ contextSupport V := by
  ext x
  change x ∈ interior
      (readablePointSet (Site.productContext W V)) ↔
    x ∈ interior (readablePointSet W) ∧ x ∈ interior (readablePointSet V)
  rw [readablePointSet_product, interior_inter]
  rfl

/-- Product support of selected open contexts is their open intersection.

The simp normal form replaces the W1 construction by the open-set meet.
-/
@[simp]
theorem contextSupport_product_openContext (W V : Opens Space) :
    contextSupport (Site.productContext (openContext W) (openContext V)) = W ⊓ V := by
  rw [contextSupport_product, contextSupport_openContext, contextSupport_openContext]

/-- Inclusion of opens induces a W1-context morphism. -/
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

/-- Inclusion of opens is represented in the W1 context preorder. -/
theorem openContext_le {W V : Opens Space} (h : W ≤ V) :
    contextPreorder.le (openContext W) (openContext V) :=
  ⟨openContextMorphism h, openContextMorphism_isRestriction h⟩

/-- Empty equation component; W1 changes Atom provenance, not equations. -/
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
def signature : ArchitectureSignature carrier where
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
    Site.CoverageRequirements object equationSystem signature where
  requiredSupport := fun _ => True
  requiredEquationCoordinate := fun coordinate => nomatch coordinate.1.1
  selectedViolationWitness := fun coordinate => nomatch coordinate.1
  requiredAxis := Empty.elim
  supportVisibleOn := fun W atom =>
    match atom with
    | .inl point => point ∈ contextSupport W
    | .inr generator => ∃ support : W.Support,
        W.minimal.supportReads support
          (Sum.inr generator)
  equationCoordinateVisibleOn := fun _ coordinate => nomatch coordinate.1.1
  violationWitnessVisibleOn := fun _ coordinate => nomatch coordinate.1
  axisReadableOn := fun _ axis => nomatch axis
  boundaryVisibleOn := fun _ _ => True

/-- Product contexts supply overlap objects for the W1 site. -/
noncomputable def overlap : Site.ContextOverlapPullback contextPreorder :=
  Site.meetOverlapPullback contextPreorder Site.productContextFiniteMeet

/-- AAT site on the actual W1 point/generator architecture object. -/
noncomputable def site : Site.AATSite object where
  contextPreorder := contextPreorder
  equationSystem := equationSystem
  signature := signature
  requirements := coverageRequirements
  overlap := overlap

/-- Full-space base context on the W1 object. -/
def baseContext : Site.ArchCtx object := openContext ⊤


/-- 固定された二chartによる実被覆family。 -/
def coverageFamily : Site.CoverageFamily contextPreorder where
  base := baseContext
  Index := Bool
  patch i := openContext (patch i)
  inclusion _ := openContext_le le_top
/-- 実coverageの点可視性は同じ開patchの点membership。 -/
theorem coverageFamily_support_point (i : Bool) (x : Space) :
    coverageRequirements.supportVisibleOn (coverageFamily.patch i) (Sum.inl x) ↔ x ∈ patch i := by
  change x ∈ contextSupport (openContext (patch i)) ↔ _
  rw [contextSupport_openContext]
/-- 二chartは全幾何点と一生成元を実際に被覆する。 -/
theorem coverageFamily_admissible :
    Site.AdmissibleCover coverageRequirements overlap coverageFamily := by
  refine {
    atomSupportCoverage := ?_
    equationCoordinateCoverage := ?_
    violationWitnessCoverage := ?_
    signatureAxisCoverage := ?_
    boundaryCoverage := ?_
    nonGeneration := ?_
  }
  · intro atom _
    cases atom with
    | inl point =>
        obtain ⟨i,hi⟩ := patches_cover point
        exact ⟨i,(coverageFamily_support_point i point).mpr hi⟩
    | inr generator => exact ⟨false,⟨(),openContext_reads_generator _ generator⟩⟩
  · intro coordinate
    exact Empty.elim coordinate.1.1
  · intro coordinate
    exact Empty.elim coordinate.1
  · intro axis
    exact Empty.elim axis
  · intros
    trivial
  · intro i
    exact coverageFamily.inclusion_nonGenerating i
/-- Product contexts form pullbacks in the W1 thin context category. -/
def contextPullbackCone {X Y Z : site.category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PullbackCone f g :=
  PullbackCone.mk
    (homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx))
    (homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx))
    (Subsingleton.elim _ _)

/-- Universal property of the W1 product-context pullback cone. -/
def contextPullbackConeIsLimit {X Y Z : site.category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (contextPullbackCone f g) :=
  PullbackCone.IsLimit.mk _
    (fun s => homOfLE
      (Site.productContextFiniteMeet.le_meet (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

/-- Local pullback instance used by the generated-topology sheaf criterion. -/
noncomputable local instance contextHasPullback
    {X Y Z : site.category} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  ⟨⟨⟨contextPullbackCone f g, contextPullbackConeIsLimit f g⟩⟩⟩

/-- The support image of a W1 context pullback is open intersection. -/
def supportMapPullbackConeIsLimit {X Y Z : site.category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit
      (PullbackCone.mk
        (supportFunctor.map (contextPullbackCone f g).fst)
        (supportFunctor.map (contextPullbackCone f g).snd)
        (Subsingleton.elim _ _) :
        PullbackCone (supportFunctor.map f) (supportFunctor.map g)) :=
  PullbackCone.IsLimit.mk _
    (fun s => homOfLE (by
      rw [show supportFunctor.obj (contextPullbackCone f g).pt =
          supportFunctor.obj X ⊓ supportFunctor.obj Y by
        exact contextSupport_product X.ctx Y.ctx]
      exact le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

/-- The W1 support functor preserves context pullbacks. -/
theorem supportFunctor_preservesPullback
    {X Y Z : site.category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) supportFunctor :=
  preservesLimit_of_preserves_limit_cone
    (contextPullbackConeIsLimit f g)
    ((PullbackCone.isLimitMapConeEquiv
      (contextPullbackCone f g) supportFunctor).symm
      (supportMapPullbackConeIsLimit f g))

/-- Pullback of a W1 admissible family maps to an open cover. -/
theorem mapped_pullback_mem_open_topology
    {X Y : site.category} (f : Y ⟶ X)
    (F : Site.AATCoverageFamily coverageRequirements overlap X) :
    Sieve.generate
        (((Sieve.generate F.presieve).pullback f).arrows.map supportFunctor) ∈
      Opens.grothendieckTopology Space (supportFunctor.obj Y) := by
  intro x hx
  obtain ⟨i, hi⟩ := F.admissible.atomSupportCoverage (.inl x) trivial
  let patchObject := Site.ContextCategoryObject.of contextPreorder (F.patch i)
  let Q := Site.ContextCategoryObject.of contextPreorder
    (Site.productContext Y.ctx (F.patch i))
  let q : Q ⟶ Y :=
    homOfLE (Site.productContextFiniteMeet.meet_le_left Y.ctx (F.patch i))
  let qpatch : Q ⟶ patchObject :=
    homOfLE (Site.productContextFiniteMeet.meet_le_right Y.ctx (F.patch i))
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed hinclusion qpatch
    convert hcomp using 1
  refine ⟨supportFunctor.obj Q, supportFunctor.map q, ?_, ?_⟩
  · exact Sieve.le_generate _ _ (Presieve.map.of hq)
  · change x ∈ contextSupport (Site.productContext Y.ctx (F.patch i))
    rw [contextSupport_product]
    exact ⟨hx, hi⟩

/-- The actual W1-site support functor is continuous. -/
theorem supportFunctor_isContinuous :
    Functor.IsContinuous supportFunctor site.topology
      (Opens.grothendieckTopology Space) where
  op_comp_isSheaf_of_types := by
    rintro ⟨G, hG⟩
    rw [isSheaf_iff_isSheaf_of_type] at hG
    rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
    rw [Precoverage.isSheaf_toGrothendieck_iff]
    intro X Y f R hR
    rcases hR with ⟨F, rfl⟩
    letI : supportFunctor.PreservesPairwisePullbacks
        ((Sieve.generate F.presieve).pullback f).arrows := {
      preservesLimit := by
        intro R Y left right hleft hright
        exact supportFunctor_preservesPullback left right
    }
    letI : ((Sieve.generate F.presieve).pullback f).arrows.HasPairwisePullbacks :=
      ⟨by
        intro Y Z left hleft right hright
        exact contextHasPullback left right⟩
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    apply (Presieve.isSheafFor_iff_generate _).mpr
    exact hG _ (mapped_pullback_mem_open_topology f F)

/-- W1 Atom input satisfying the generic G-125 open-support contract. -/
def contextOpenSupport : ContextOpenSupport site where
  space := TopCat.of Space
  support := supportFunctor
  continuous := supportFunctor_isContinuous


end AAT.AG.SpecifiedRepairLifting.RationalWitnessContext

#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.carrier
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.object
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.openContext
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.openContext_reads_point
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.openContext_reads_generator
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.readablePointSet
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextSupport
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.readablePointSet_mono
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextSupport_mono
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextPreorder
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.supportFunctor
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextSupport_openContext
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.readablePointSet_product
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextSupport_product
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextSupport_product_openContext
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.openContextMorphism
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.openContextMorphism_isRestriction
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.openContext_le
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.equationSystem
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.signature
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.coverageRequirements
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.overlap
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.site
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.baseContext
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.coverageFamily
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.coverageFamily_support_point
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.coverageFamily_admissible
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextPullbackCone
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextPullbackConeIsLimit
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextHasPullback
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.supportMapPullbackConeIsLimit
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.supportFunctor_preservesPullback
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.mapped_pullback_mem_open_topology
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.supportFunctor_isContinuous
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessContext.contextOpenSupport
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.RationalWitnessContext
