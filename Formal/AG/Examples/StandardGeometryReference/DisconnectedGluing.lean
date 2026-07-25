import Formal.AG.Examples.StandardGeometryReference.EquationGeometry

/-!
# Standard geometry reference: a separating gluing instance

SD8 (Issue #3800).  This module builds the instance that SD5 and SD6 do not
reach: a context-indexed chart cover whose compatibility is produced by the
Čech route `EquationContextChartProducer.ofRefinement` and whose universal
sections are **not** context independent, so that
`EquationContextChartProducer.ofContextIndependentSections` cannot produce it
and the glued section of Definition 5.2A is none of the sections it glues.

## Why the reference model cannot host this, on the Čech route

`EquationObservableRealization.violationSection_natural` propagates the
universal section along every context morphism, so `violationSection` is
constant on each connected component of the context category.  Two contexts can
therefore carry different universal sections only when no zigzag joins them,
and `EquationContextChartRefinement` then forces their charts to be disjoint:
the refinement family over their overlap is indexed by the contexts refining
both, which is empty.  For the glued section to differ from *every* universal
section, at least two of those pairwise disjoint unions of charts must be
nonempty, and the charts jointly cover; the represented Scheme is then
disconnected.

That argument is about the Čech route only.  Issue #3800 records the correction
that disconnectedness is one sufficient condition and not a necessary one: a
compatibility producer supplied directly, without
`EquationContextChartRefinement`, could instead live on a connected ambient
whose restriction to the chart overlap is not injective.  This module does not
build that variant.  The reference ambient supports neither route: the
coordinate ring of `Spec ℤ[x]` is an integral domain, so restriction to any
nonempty open is injective.

## What is built here

The ambient is replaced, not the theory.  The selected structural relation is
`X² - X`, so the raw quotient is `ℤ[e]/(e² - e)` and the represented Scheme is
`Spec` of it, the disjoint union of `D(e)` and `D(1 - e)`.  Two contexts outside
the selected two-patch family own those two principal opens and every remaining
context owns `D(0) = ⊥`.  The two owning contexts are isolated in
`referenceContextPreorder`, so the equation system may — and does — give them
different symbolic coordinates: `0` on one and `1` on the other.

The selected coverage requirements differ from the reference ones in exactly
two clauses: the signature axis is readable only on the base patch and the
boundary is visible only there.  Together they force every admissible family to
contain the identity of its base, so the generated topology is bottom, the
sheafification unit is invertible at every context, and the canonical section
ring is the raw quotient itself.  No second sheaf-condition argument is
introduced.

## Implementation notes

* The atlas is the one-chart identity atlas of the base context.  A two-chart
  atlas with disjoint images was rejected: `ArchitectureOverlapPresentation`
  compares `architectureChartSpec` of the selected pair context with the actual
  pullback, and for disjoint charts that pullback is empty while the pair
  context's Spec is not.  Disconnectedness therefore has to live in the section
  ring, not in the atlas.
* Every context restriction of the selected raw system is the identity
  polynomial map.  A nonidentity restriction was not needed: what this fixture
  separates is compatibility production, and the sign twist of the existing
  finite fixtures would only obscure the two symbolic values.
* Non-degeneracy is proved by identifying the glued section as `2 * (1 - e)`
  through the uniqueness clause of the gluing, and then separating it from both
  universal sections by the two integer evaluations of the raw quotient.
  Deriving non-degeneracy from a cardinality or emptiness argument about the
  charts was rejected because it would not exhibit the glued section.
* The symbolic value carried by the second component is `2`, not `1`.  A unit
  there would put a unit into `realizationIdeal` and collapse the
  equation-generated realization, which would make the section side of Theorem
  5.2C hold only over the empty test scheme.  `realizationIdeal_ne_top` records
  that the selected value avoids this.
* What this fixture exercises, and what it does not.  Distinct contexts own
  disjoint opens, so every pairwise overlap of distinct contexts is empty and
  `EquationContextChartRefinement` is discharged by `bot_le`; the Čech
  transport of `violation_compatible_of_refinement` is never used on a nonempty
  overlap.  What is separated is the *hypothesis* of the two producers, not the
  reach of Čech refinement.  For the same reason the context-transition
  localizations are identities or maps of zero rings, and the atlas-overlap
  localization inverts only `1`.  Non-degenerate localizations and non-empty
  chart overlaps are carried by SD5 and SD6.
* The selected coverage requirements make the generated topology bottom, so
  this fixture exercises no admissible cover, no sheaf condition and no
  sheafification content of the AAT site.  Those are carried by SD0--SD6, whose
  site has a genuine two-patch cover of its base.
-/

noncomputable section

namespace AAT.AG.Examples.StandardGeometryReferenceModels

namespace DisconnectedGluing

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

/-! ## The two isolated owning contexts -/

/-- The context owning the first component of the disconnected ambient. -/
def componentAContext : Site.ArchCtx AAT.AG.FiniteModel.object where
  minimal :=
    (AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.base).minimal
  Extension := Bool
  extension := false

/-- The context owning the second component of the disconnected ambient. -/
def componentBContext : Site.ArchCtx AAT.AG.FiniteModel.object where
  minimal :=
    (AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.base).minimal
  Extension := Bool
  extension := true

/-- Neither owning context is one of the four selected two-patch contexts. -/
theorem componentContext_ne_twoPatchContext
    {W : Site.ArchCtx AAT.AG.FiniteModel.object}
    (hW : W.Extension = Bool)
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    W ≠ AAT.AG.FiniteModel.twoPatchContext i := by
  intro h
  have he : Bool = AAT.AG.FiniteModel.TwoPatchContextIndex :=
    hW.symm.trans (congrArg Site.ArchitectureContext.Extension h)
  have hcard := Fintype.card_congr (Equiv.cast he)
  simp only [Fintype.card_bool] at hcard
  have hfour :
      Fintype.card AAT.AG.FiniteModel.TwoPatchContextIndex = 4 := by decide
  omega

/-- The first owning context is none of the selected two-patch contexts. -/
theorem componentAContext_ne_twoPatchContext
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    componentAContext ≠ AAT.AG.FiniteModel.twoPatchContext i :=
  componentContext_ne_twoPatchContext (W := componentAContext) rfl i

/-- The second owning context is none of the selected two-patch contexts. -/
theorem componentBContext_ne_twoPatchContext
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    componentBContext ≠ AAT.AG.FiniteModel.twoPatchContext i :=
  componentContext_ne_twoPatchContext (W := componentBContext) rfl i

/-- The two owning contexts are distinct. -/
theorem componentAContext_ne_componentBContext :
    componentAContext ≠ componentBContext := by
  intro h
  have hext := congrArg
    (fun W : Site.ArchCtx AAT.AG.FiniteModel.object =>
      (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) h
  injection hext with _ hvalue
  have hfalse : (false : Bool) = true := hvalue
  exact Bool.noConfusion hfalse

/-- The context-category object owning the first component. -/
def componentA : referenceSite.category :=
  Site.ContextCategoryObject.of referenceContextPreorder componentAContext

/-- The context-category object owning the second component. -/
def componentB : referenceSite.category :=
  Site.ContextCategoryObject.of referenceContextPreorder componentBContext

/-- The first owning object is none of the four selected two-patch objects. -/
theorem componentA_ne_context
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    componentA ≠ context i := fun h =>
  componentAContext_ne_twoPatchContext i
    (congrArg Site.ContextCategoryObject.ctx h)

/-- The second owning object is none of the four selected two-patch objects. -/
theorem componentB_ne_context
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    componentB ≠ context i := fun h =>
  componentBContext_ne_twoPatchContext i
    (congrArg Site.ContextCategoryObject.ctx h)

/-- The two owning objects are distinct. -/
theorem componentA_ne_componentB : componentA ≠ componentB := fun h =>
  componentAContext_ne_componentBContext
    (congrArg Site.ContextCategoryObject.ctx h)

/--
The two owning objects are isolated from each other and from the selected
two-patch family: a context morphism out of or into either of them exists only
as its identity.
-/
theorem eq_of_hom_component
    {W V : referenceSite.category} (f : W ⟶ V)
    (h : W = componentA ∨ W = componentB ∨ V = componentA ∨ V = componentB) :
    W = V := by
  have hle : referenceContextPreorder.le W.ctx V.ctx := CategoryTheory.leOfHom f
  rcases (referenceContextPreorder_le_iff W.ctx V.ctx).mp hle with heq | ⟨i, j, hi, hj, _⟩
  · cases W
    cases V
    exact congrArg (fun c => (⟨c⟩ : referenceSite.category)) heq
  · exfalso
    rcases h with rfl | rfl | rfl | rfl
    · exact componentAContext_ne_twoPatchContext i hi
    · exact componentBContext_ne_twoPatchContext i hi
    · exact componentAContext_ne_twoPatchContext j hj
    · exact componentBContext_ne_twoPatchContext j hj

/-! ## The equation system carrying two symbolic values -/

/--
The symbolic value owned by a context: `1` on the second component and `0`
everywhere else.

The two owning contexts are isolated, so this assignment is compatible with
every context restriction while still taking two values.
-/
noncomputable def symbolicValue (W : referenceSite.category) : Int :=
  if W = componentB then 2 else 0

/-- The second component owns the symbolic value `2`.

The value is a non-unit on purpose.  A unit there would make the generated
`realizationIdeal` the whole ring and the equation-generated realization empty,
which would make the section side of Theorem 5.2C vacuous
(`realizationIdeal_ne_top`).

As a simp rule, it normalizes the fixture symbol to its integer value. -/
@[simp] theorem symbolicValue_componentB : symbolicValue componentB = 2 := by
  rw [symbolicValue, if_pos rfl]

/-- The first component owns the symbolic value `0`.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem symbolicValue_componentA : symbolicValue componentA = 0 := by
  rw [symbolicValue, if_neg componentA_ne_componentB]

/-- Every selected two-patch context owns the symbolic value `0`.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem symbolicValue_context
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    symbolicValue (context i) = 0 := by
  rw [symbolicValue, if_neg (fun h => componentB_ne_context i h.symm)]

/-- The symbolic value is constant along every context restriction. -/
theorem symbolicValue_hom {source target : referenceSite.category}
    (f : source ⟶ target) :
    symbolicValue target = symbolicValue source := by
  have hle : referenceContextPreorder.le source.ctx target.ctx :=
    CategoryTheory.leOfHom f
  rcases (referenceContextPreorder_le_iff source.ctx target.ctx).mp hle with
    heq | ⟨i, j, hi, hj, _⟩
  · have hst : source = target := by
      cases source
      cases target
      exact congrArg (fun c => (⟨c⟩ : referenceSite.category)) heq
    rw [hst]
  · have hs : source = context i := by
      cases source
      exact congrArg (fun c => (⟨c⟩ : referenceSite.category)) hi
    have ht : target = context j := by
      cases target
      exact congrArg (fun c => (⟨c⟩ : referenceSite.category)) hj
    rw [hs, ht, symbolicValue_context, symbolicValue_context]

/--
SD8: the equation system whose symbolic coordinate depends on the context.

One required equation, integer observables, identity restriction, and the
two-valued symbolic coordinate.  Object-dependent residuals are zero, so each
generated equalizer relation is the universal section itself; this is why the
symbolic value has to be a non-unit for `realizationIdeal` to stay proper
(`realizationIdeal_ne_top`).  A nonzero residual would only shift the same
constraint onto the difference.
-/
noncomputable def disconnectedEquationSystem :
    ArchitecturalEquationSystem referenceSite.contextPreorder where
  Index := PUnit
  role := fun _ => EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun W _ _ => symbolicValue W
  violationCoordinate_restrict := by
    intro source target f _ _
    exact symbolicValue_hom f
  equationResidual := fun _ _ _ _ => 0
  equationResidual_restrict := by intros; rfl

/-- Its single equation is required. -/
theorem disconnectedEquationSystem_required
    (index : disconnectedEquationSystem.Index) :
    disconnectedEquationSystem.Required index := rfl

/-! ## The selected site and its bottom topology -/

/--
SD8: coverage requirements that read the signature axis only on the base patch.

The atom-support clauses are the reference ones.  The axis and boundary clauses
are the only changes: together they force every admissible family to be based
at the base patch and to contain that patch, hence to contain the identity.
The generated topology is then bottom, which is what makes the canonical
section ring computable as the raw quotient.  The equation-coordinate and
violation-witness clauses are unconstrained because this fixture selects the
topology, not the coverage content.
-/
def disconnectedCoverageRequirements :
    Site.CoverageRequirements
      referenceCorePackage.object
      disconnectedEquationSystem
      referenceSite.signature where
  requiredSupport := referenceCoverageRequirements.requiredSupport
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := referenceCoverageRequirements.supportVisibleOn
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.base
  boundaryVisibleOn := fun _ base =>
    base = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.base

/-- SD8: the selected site, differing from `referenceSite` only in its equation
system and coverage requirements. -/
noncomputable def disconnectedSite :
    Site.AATSite referenceCorePackage.object :=
  { referenceSite with
    equationSystem := disconnectedEquationSystem
    requirements := disconnectedCoverageRequirements }

/-- The selected site keeps the reference context preorder.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem disconnectedSite_contextPreorder :
    disconnectedSite.contextPreorder = referenceContextPreorder :=
  rfl

/-- The selected site keeps the reference overlap package.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem disconnectedSite_overlap :
    disconnectedSite.overlap = referenceOverlap :=
  rfl

/-- The selected site carries the two-valued equation system.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem disconnectedSite_equationSystem :
    disconnectedSite.equationSystem = disconnectedEquationSystem :=
  rfl

private theorem admissible_base_eq
    {X : disconnectedSite.category}
    (F : Site.AATCoverageFamily disconnectedCoverageRequirements
      referenceOverlap X) :
    X.ctx = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.base := by
  rcases F.admissible.signatureAxisCoverage PUnit.unit trivial with ⟨i, _⟩
  have hboundary := F.admissible.boundaryCoverage i i
  simpa [disconnectedCoverageRequirements] using hboundary

private theorem admissible_has_base_patch
    {X : disconnectedSite.category}
    (F : Site.AATCoverageFamily disconnectedCoverageRequirements
      referenceOverlap X) :
    ∃ i : F.Index, F.patch i =
      AAT.AG.FiniteModel.twoPatchContext
        AAT.AG.FiniteModel.TwoPatchContextIndex.base := by
  rcases F.admissible.signatureAxisCoverage PUnit.unit trivial with ⟨i, hi⟩
  exact ⟨i, by simpa [disconnectedCoverageRequirements] using hi⟩

private theorem admissible_presieve_identity
    {X : disconnectedSite.category}
    (F : Site.AATCoverageFamily disconnectedCoverageRequirements
      referenceOverlap X) :
    F.presieve (𝟙 X) := by
  rcases admissible_has_base_patch F with ⟨i, hi⟩
  have hctx : X.ctx = F.patch i := (admissible_base_eq F).trans hi.symm
  have hobj : X = Site.ContextCategoryObject.of
      disconnectedSite.contextPreorder (F.patch i) := by
    cases X
    simp only [Site.ContextCategoryObject.of] at hctx ⊢
    congr
  exact Presieve.ofArrows.mk' i hobj (Subsingleton.elim _ _)

private theorem admissible_generate_eq_top
    {X : disconnectedSite.category}
    (F : Site.AATCoverageFamily disconnectedCoverageRequirements
      referenceOverlap X) :
    Sieve.generate F.presieve = ⊤ :=
  Sieve.generate_of_contains_isSplitEpi (𝟙 X)
    (admissible_presieve_identity F)

/-- SD8: every admissible family contains its identity, so the generated
topology is bottom. -/
theorem disconnectedSite_topology_eq_bot : disconnectedSite.topology = ⊥ := by
  rw [Site.AATSite.topology_eq, Site.AATGrothendieckTopology,
    Precoverage.toGrothendieck_eq_sInf]
  apply le_antisymm
  · apply sInf_le
    intro X S hS
    rw [GrothendieckTopology.bot_covering]
    rcases hS with ⟨F, rfl⟩
    exact admissible_generate_eq_top F
  · exact bot_le

/-- SD8: bottom-topology sheafification on the selected site. -/
noncomputable instance disconnectedHasSheafify :
    HasSheafify disconnectedSite.topology (AATCommAlgCat Int) := by
  rw [disconnectedSite_topology_eq_bot]
  exact HasSheafify.mk' _ _
    (sheafBotEquivalence (AATCommAlgCat Int)).symm.toAdjunction

/-! ## The raw system whose quotient is `ℤ[e]/(e² - e)` -/

/-- SD8: one semantic coordinate on every context. -/
def disconnectedCoordFamily (W : disconnectedSite.category) :
    CoordinateFamily W.ctx where
  Coord := Unit
  label := fun _ => CoordinateLabel.semantic
  LocalData := fun _ => Unit

/-- SD8: the selected structural equation `X² - X`, whose quotient is generated
by an idempotent. -/
def disconnectedRelationFamily (W : disconnectedSite.category) :
    StructuralRelationFamily (disconnectedCoordFamily W) Int where
  Relation := Unit
  polynomial := fun _ => MvPolynomial.X () ^ 2 - MvPolynomial.X ()

/-- SD8: every context restriction keeps the selected coordinate. -/
def disconnectedCoordinateRestriction
    {X Y : disconnectedSite.category} (f : X ⟶ Y) :
    TypedCoordinateRestriction
      (disconnectedCoordFamily X) (disconnectedCoordFamily Y) Int
      (disconnectedSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) where
  variableImage := fun _ => MvPolynomial.X ()

/-- The selected restriction acts as the identity on polynomials. -/
theorem disconnectedCoordinateRestriction_polynomialMap
    {X Y : disconnectedSite.category} (f : X ⟶ Y) :
    (disconnectedCoordinateRestriction f).polynomialMap =
      RingHom.id (FreeTypedCommAlg (disconnectedCoordFamily X) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro i
    cases i
    rw [TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- SD8: the structural ideal is preserved because the restriction is the
identity. -/
def disconnectedRestrictionStable
    {X Y : disconnectedSite.category} (f : X ⟶ Y) :
    RestrictionStableStructuralRelations
      (disconnectedRelationFamily X) (disconnectedRelationFamily Y)
      (disconnectedSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) where
  restriction := disconnectedCoordinateRestriction f
  maps_JStruct := by
    intro p hp
    have hid : (disconnectedCoordinateRestriction f).polynomialMap p = p := by
      rw [disconnectedCoordinateRestriction_polynomialMap]
      rfl
    rw [hid]
    exact hp

/-- SD8: the selected raw restriction system with the idempotent relation. -/
def disconnectedRaw : RawAmbientRestrictionSystem disconnectedSite Int where
  coordFamily := disconnectedCoordFamily
  relationFamily := disconnectedRelationFamily
  restrictionStable := disconnectedRestrictionStable
  identity_polynomialMap := fun W =>
    disconnectedCoordinateRestriction_polynomialMap (𝟙 W)
  composition_polynomialMap := by
    intro X Y Z f g
    show (disconnectedCoordinateRestriction (f ≫ g)).polynomialMap =
      ((disconnectedCoordinateRestriction f).polynomialMap).comp
        ((disconnectedCoordinateRestriction g).polynomialMap)
    rw [disconnectedCoordinateRestriction_polynomialMap,
      disconnectedCoordinateRestriction_polynomialMap,
      disconnectedCoordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

/-- Every descended context restriction of the selected raw system is the
identity. -/
theorem disconnectedRaw_quotientDesc
    {X Y : disconnectedSite.category} (f : X ⟶ Y)
    (p : FreeTypedCommAlg (disconnectedCoordFamily Y) Int) :
    (disconnectedRaw.restrictionStable f).quotientDesc
        ((disconnectedRaw.relationFamily Y).quotientMap p) =
      (disconnectedRaw.relationFamily X).quotientMap p := by
  rw [RestrictionStableStructuralRelations.quotientDesc_mk]
  have hid : (disconnectedCoordinateRestriction f).polynomialMap p = p := by
    rw [disconnectedCoordinateRestriction_polynomialMap]
    rfl
  exact congrArg (disconnectedRaw.relationFamily X).quotientMap hid

/-! ## The disconnected represented Scheme -/

/-- The base context of the selected site. -/
def baseObject : disconnectedSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.base

/-- SD8: bottom-topology sheafification is invertible at every context, so the
canonical section ring is the raw quotient. -/
theorem canonical_component_isIso (W : disconnectedSite.category) :
    IsIso (disconnectedRaw.toRingedSite.canonical.app (op W)) := by
  have hsheaf : Presheaf.IsSheaf disconnectedSite.topology
      disconnectedRaw.toPresheaf := by
    rw [disconnectedSite_topology_eq_bot]
    exact Presheaf.isSheaf_bot _
  haveI : IsIso (CategoryTheory.toSheafify disconnectedSite.topology
      disconnectedRaw.toPresheaf) :=
    CategoryTheory.isIso_toSheafify
      (J := disconnectedSite.topology) hsheaf
  change IsIso ((CategoryTheory.toSheafify disconnectedSite.topology
    disconnectedRaw.toPresheaf).app (op W))
  infer_instance

/-- SD8: the represented Scheme, `Spec (ℤ[e]/(e² - e))`.

This is the existing single-chart constructor at the base context.  A two-chart
atlas with disjoint images cannot be used instead: `ArchitectureOverlapPresentation`
compares `architectureChartSpec` of the selected pair context with the actual
pullback of the two chart maps, and that pullback is empty for disjoint charts
while the pair context's Spec is not.  Disconnectedness therefore lives in the
section ring, not in the atlas. -/
noncomputable def disconnectedScheme :
    StandardArchitectureScheme disconnectedRaw :=
  StandardArchitectureScheme.singleAffine disconnectedRaw baseObject

/-- Its ambient is the canonical base chart Spec.

As a simp rule, it normalizes the fixture Scheme to the canonical
section-ring Spec. -/
@[simp] theorem disconnectedScheme_underlying :
    disconnectedScheme.underlying =
      architectureChartSpec disconnectedRaw baseObject :=
  rfl

/-- The ambient is affine. -/
instance disconnectedScheme_isAffine :
    IsAffine disconnectedScheme.underlying := by
  change IsAffine (AlgebraicGeometry.Spec
    (SheafifiedSectionRing disconnectedRaw baseObject))
  infer_instance

/-! ## The idempotent that disconnects the ambient -/

/-- The class of the selected coordinate in the raw quotient at the base context. -/
noncomputable def rawIdempotent : disconnectedRaw.rawAlgebra baseObject :=
  (disconnectedRaw.relationFamily baseObject).quotientMap (MvPolynomial.X ())

/-- The selected coordinate class is idempotent, by the structural relation. -/
theorem rawIdempotent_mul_self :
    rawIdempotent * rawIdempotent = rawIdempotent := by
  have hzero :
      (disconnectedRaw.relationFamily baseObject).quotientMap
        (MvPolynomial.X () ^ 2 - MvPolynomial.X ()) = 0 :=
    (disconnectedRaw.relationFamily baseObject).quotientMap_polynomial_eq_zero ()
  rw [map_sub, map_pow] at hzero
  have hsq : rawIdempotent ^ 2 = rawIdempotent := sub_eq_zero.mp hzero
  calc rawIdempotent * rawIdempotent = rawIdempotent ^ 2 := (sq _).symm
    _ = rawIdempotent := hsq

/-- Evaluation of the free algebra at `0`. -/
noncomputable def rawEvalZero :
    FreeTypedCommAlg (disconnectedCoordFamily baseObject) Int →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => 0)

/-- Evaluation of the free algebra at `1`. -/
noncomputable def rawEvalOne :
    FreeTypedCommAlg (disconnectedCoordFamily baseObject) Int →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => 1)

private theorem jstruct_le_ker_rawEvalZero :
    (disconnectedRaw.relationFamily baseObject).JStruct ≤
      RingHom.ker rawEvalZero := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  show rawEvalZero (MvPolynomial.X () ^ 2 - MvPolynomial.X ()) = 0
  simp [rawEvalZero]

private theorem jstruct_le_ker_rawEvalOne :
    (disconnectedRaw.relationFamily baseObject).JStruct ≤
      RingHom.ker rawEvalOne := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  show rawEvalOne (MvPolynomial.X () ^ 2 - MvPolynomial.X ()) = 0
  simp [rawEvalOne]

/-- The evaluation at `0` descended to the raw quotient. -/
noncomputable def quotientEvalZero :
    disconnectedRaw.rawAlgebra baseObject →+* Int :=
  Ideal.Quotient.lift (disconnectedRaw.relationFamily baseObject).JStruct
    rawEvalZero (fun _ hp => jstruct_le_ker_rawEvalZero hp)

/-- The evaluation at `1` descended to the raw quotient. -/
noncomputable def quotientEvalOne :
    disconnectedRaw.rawAlgebra baseObject →+* Int :=
  Ideal.Quotient.lift (disconnectedRaw.relationFamily baseObject).JStruct
    rawEvalOne (fun _ hp => jstruct_le_ker_rawEvalOne hp)

/-- The evaluation at `0` sends the selected coordinate class to `0`.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem quotientEvalZero_rawIdempotent :
    quotientEvalZero rawIdempotent = 0 := by
  show rawEvalZero (MvPolynomial.X ()) = 0
  simp [rawEvalZero]

/-- The evaluation at `1` sends the selected coordinate class to `1`.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem quotientEvalOne_rawIdempotent :
    quotientEvalOne rawIdempotent = 1 := by
  show rawEvalOne (MvPolynomial.X ()) = 1
  simp [rawEvalOne]

/-- The selected coordinate class is not `0`. -/
theorem rawIdempotent_ne_zero : rawIdempotent ≠ 0 := by
  intro h
  have := congrArg quotientEvalOne h
  rw [quotientEvalOne_rawIdempotent, map_zero] at this
  exact one_ne_zero this

/-- The selected coordinate class is not `1`. -/
theorem rawIdempotent_ne_one : rawIdempotent ≠ 1 := by
  intro h
  have := congrArg quotientEvalZero h
  rw [quotientEvalZero_rawIdempotent, map_one] at this
  exact zero_ne_one this

/-- The canonical sheafification component at the base context, as a ring map. -/
noncomputable def canonicalBaseHom :
    disconnectedRaw.rawAlgebra baseObject →+*
      SheafifiedSectionRing disconnectedRaw baseObject :=
  ((disconnectedRaw.toRingedSite.canonical.app (op baseObject)).right).hom

/-- The canonical component at the base context is injective. -/
theorem canonicalBaseHom_injective : Function.Injective canonicalBaseHom := by
  letI := canonical_component_isIso baseObject
  intro x y h
  have hx := congrArg (fun q => q.right x)
    (IsIso.hom_inv_id (disconnectedRaw.toRingedSite.canonical.app (op baseObject)))
  have hy := congrArg (fun q => q.right y)
    (IsIso.hom_inv_id (disconnectedRaw.toRingedSite.canonical.app (op baseObject)))
  calc
    x = (inv (disconnectedRaw.toRingedSite.canonical.app (op baseObject))).right
        ((disconnectedRaw.toRingedSite.canonical.app (op baseObject)).right x) := by
      simpa only [Under.comp_right, Under.id_right, CommRingCat.comp_apply,
        CommRingCat.id_apply] using hx.symm
    _ = (inv (disconnectedRaw.toRingedSite.canonical.app (op baseObject))).right
        ((disconnectedRaw.toRingedSite.canonical.app (op baseObject)).right y) := by
      exact congrArg _ h
    _ = y := by
      simpa only [Under.comp_right, Under.id_right, CommRingCat.comp_apply,
        CommRingCat.id_apply] using hy

/-- The raw quotient at the base context, read as global sections of the ambient. -/
noncomputable def rawToGlobal :
    disconnectedRaw.rawAlgebra baseObject →+*
      Γ(disconnectedScheme.underlying, ⊤) :=
  ((AlgebraicGeometry.Scheme.ΓSpecIso
    (SheafifiedSectionRing disconnectedRaw baseObject)).inv).hom.comp
      canonicalBaseHom

/-- Reading the raw quotient as global sections is injective. -/
theorem rawToGlobal_injective : Function.Injective rawToGlobal := by
  intro x y h
  apply canonicalBaseHom_injective
  have hxy :
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing disconnectedRaw baseObject)).inv
          (canonicalBaseHom x) =
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing disconnectedRaw baseObject)).inv
          (canonicalBaseHom y) := h
  have hcancel := congrArg
    (fun z => (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing disconnectedRaw baseObject)).hom z) hxy
  simpa only [Iso.inv_hom_id_apply] using hcancel

/-- The canonical section ring map at the base context is invertible. -/
instance canonicalBaseRight_isIso :
    IsIso ((disconnectedRaw.toRingedSite.canonical.app (op baseObject)).right) := by
  letI := canonical_component_isIso baseObject
  exact inferInstanceAs (IsIso ((Under.forget _).map
    (disconnectedRaw.toRingedSite.canonical.app (op baseObject))))

/-- Global sections of the ambient, read back in the raw quotient. -/
noncomputable def globalToRaw :
    Γ(disconnectedScheme.underlying, ⊤) →+*
      disconnectedRaw.rawAlgebra baseObject :=
  (CommRingCat.Hom.hom
      (inv ((disconnectedRaw.toRingedSite.canonical.app
        (op baseObject)).right))).comp
    (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing disconnectedRaw baseObject)).hom)

/-- Reading a raw class as a global section and back is the identity.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem globalToRaw_rawToGlobal
    (x : disconnectedRaw.rawAlgebra baseObject) :
    globalToRaw (rawToGlobal x) = x := by
  show (inv ((disconnectedRaw.toRingedSite.canonical.app
        (op baseObject)).right))
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing disconnectedRaw baseObject)).hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing disconnectedRaw baseObject)).inv
          (canonicalBaseHom x))) = x
  rw [Iso.inv_hom_id_apply]
  have hcancel := congrArg (fun q => q x)
    (IsIso.hom_inv_id
      ((disconnectedRaw.toRingedSite.canonical.app (op baseObject)).right))
  simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using hcancel

/-- Evaluation of a global section at the first component. -/
noncomputable def globalEvalZero :
    Γ(disconnectedScheme.underlying, ⊤) →+* Int :=
  quotientEvalZero.comp globalToRaw

/-- Evaluation of a global section at the second component. -/
noncomputable def globalEvalOne :
    Γ(disconnectedScheme.underlying, ⊤) →+* Int :=
  quotientEvalOne.comp globalToRaw

/-- SD8: the idempotent global section whose two principal opens are the
components of the ambient. -/
noncomputable def idempotentSection : Γ(disconnectedScheme.underlying, ⊤) :=
  rawToGlobal rawIdempotent

/-- The selected global section is idempotent. -/
theorem idempotentSection_mul_self :
    idempotentSection * idempotentSection = idempotentSection := by
  rw [idempotentSection, ← map_mul, rawIdempotent_mul_self]

/-- The selected global section is neither `0` nor `1`. -/
theorem idempotentSection_ne_zero : idempotentSection ≠ 0 := by
  intro h
  apply rawIdempotent_ne_zero
  apply rawToGlobal_injective
  rw [map_zero]
  exact h

/-- The complement of the selected global section is nontrivial too. -/
theorem idempotentSection_ne_one : idempotentSection ≠ 1 := by
  intro h
  apply rawIdempotent_ne_one
  apply rawToGlobal_injective
  rw [map_one]
  exact h

/-- The first component evaluates the idempotent to `0`.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem globalEvalZero_idempotentSection :
    globalEvalZero idempotentSection = 0 := by
  show quotientEvalZero (globalToRaw (rawToGlobal rawIdempotent)) = 0
  rw [globalToRaw_rawToGlobal, quotientEvalZero_rawIdempotent]

/-- The second component evaluates the idempotent to `1`.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem globalEvalOne_idempotentSection :
    globalEvalOne idempotentSection = 1 := by
  show quotientEvalOne (globalToRaw (rawToGlobal rawIdempotent)) = 1
  rw [globalToRaw_rawToGlobal, quotientEvalOne_rawIdempotent]

/-- The ambient global sections are nontrivial. -/
instance globalSections_nontrivial :
    Nontrivial Γ(disconnectedScheme.underlying, ⊤) := by
  refine ⟨⟨rawToGlobal 0, rawToGlobal 1, ?_⟩⟩
  intro h
  have h01 : (0 : disconnectedRaw.rawAlgebra baseObject) = 1 :=
    rawToGlobal_injective h
  have := congrArg quotientEvalZero h01
  rw [map_zero, map_one] at this
  exact zero_ne_one this

/-! ## The realization -/

/--
SD8: the selected architecture reading over the disconnected ambient.

Its readings over a test scheme are the actual morphisms into the represented
Scheme.  This choice is deliberate and is not where the content of SD8 lies:
because the equation system's observable ring is `Int`, the evaluation
component of an `EquationArchitecturePoint` is already forced by initiality of
`Int`, so *any* reading with the same observables produces the same
`sectionMap`, and hence the same universal sections.  What SD8 separates is
compatibility production, which depends only on those universal sections and on
the selected cover.  The nondegenerate representability of a coordinate reading
is carried by SD1--SD6 over `Spec ℤ[x]`; repeating it here would not change a
single statement below.
-/
noncomputable def disconnectedReading :
    EquationArchitectureReading.{0, 0} disconnectedSite.equationSystem where
  Reading T := T ⟶ disconnectedScheme.underlying
  pullback f r := f ≫ r
  object := fun _ => AAT.AG.FiniteModel.acyclicObject
  pullback_id := fun r => Category.id_comp r
  pullback_comp := fun f g r => (Category.assoc g f r).symm
  residual_pullback := by
    intro T T' f r W i a e
    show (f.appTop.hom.comp e) 0 = f.appTop (e 0)
    simp

/-- The generated point functor of the selected reading is the functor of
points of the represented Scheme; the evaluation component is forced by
initiality of `Int`. -/
noncomputable def disconnectedRepresentingEquiv
    (T : AlgebraicGeometry.Scheme.{0}) :
    (T ⟶ disconnectedScheme.underlying) ≃
      EquationArchitecturePoint disconnectedReading T where
  toFun s :=
    { reading := s
      evaluation := fun _ => Int.castRingHom _
      evaluation_natural := by
        intro source target f x
        rfl }
  invFun p := p.reading
  left_inv _ := rfl
  right_inv p := by
    refine EquationArchitecturePoint.ext rfl ?_
    intro W x
    exact congrArg (fun q => q x)
      (RingHom.ext_int (Int.castRingHom Γ(T, ⊤)) (p.evaluation W))

/-- The representing equivalence commutes with pullback of test schemes. -/
theorem disconnectedRepresentingEquiv_natural
    {T T' : AlgebraicGeometry.Scheme.{0}}
    (s : T ⟶ disconnectedScheme.underlying) (f : T' ⟶ T) :
    disconnectedRepresentingEquiv T' (f ≫ s) =
      EquationArchitecturePoint.pullback f
        (disconnectedRepresentingEquiv T s) := by
  refine EquationArchitecturePoint.ext rfl ?_
  intro W x
  exact congrArg (fun q => q x)
    (RingHom.ext_int (Int.castRingHom Γ(T', ⊤))
      (f.appTop.hom.comp (Int.castRingHom Γ(T, ⊤))))

/-- SD8: the equation-observable realization on the disconnected ambient. -/
noncomputable def disconnectedRealization :
    EquationObservableRealization disconnectedRaw disconnectedScheme
      disconnectedSite.equationSystem :=
  EquationObservableRealization.ofRepresentingEquiv
    disconnectedReading disconnectedRepresentingEquiv

/-- The selected realization is valid. -/
theorem disconnectedRealization_valid :
    IsEquationObservableRealization disconnectedRealization :=
  EquationObservableRealization.ofRepresentingEquiv_valid
    disconnectedReading disconnectedRepresentingEquiv
    disconnectedRepresentingEquiv_natural

/-- The universal section of a context is the integer cast of its symbolic
value. -/
theorem violationSection_eq_symbolicValue
    (W : disconnectedSite.category)
    (i : disconnectedSite.equationSystem.Index) (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.violationSection W i a =
      ((symbolicValue W : Int) : Γ(disconnectedScheme.underlying, ⊤)) :=
  rfl

/-- The first component's universal section is `0`.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem violationSection_componentA
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.violationSection componentA i a = 0 := by
  rw [violationSection_eq_symbolicValue, symbolicValue_componentA]
  exact Int.cast_zero

/-- The second component's universal section is `2`.

As a simp rule, it normalizes the fixture universal section to its value. -/
@[simp] theorem violationSection_componentB
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.violationSection componentB i a = 2 := by
  rw [violationSection_eq_symbolicValue, symbolicValue_componentB]
  exact Int.cast_two

/--
SD8, first separating fact: the universal sections are **not** context
independent, so `EquationContextChartProducer.ofContextIndependentSections`
cannot be applied to any cover of this realization.

The quantified statement is the negation of that constructor's `hconst`
hypothesis; the two are kept in agreement by hand, not by a shared named
predicate.
-/
theorem violationSection_not_context_independent :
    ¬ ∀ (W V : disconnectedSite.category)
        (i : disconnectedSite.equationSystem.Index)
        (a : AAT.AG.FiniteModel.carrier.Atom),
        disconnectedRealization.violationSection W i a =
          disconnectedRealization.violationSection V i a := by
  intro h
  have h02 := h componentA componentB PUnit.unit
    AAT.AG.FiniteModel.FiniteAtom.componentA
  rw [violationSection_componentA, violationSection_componentB] at h02
  have hint := congrArg globalEvalZero h02
  rw [map_zero, map_ofNat] at hint
  exact absurd hint (by decide)

/-! ## The separating context chart cover -/

/-- The chart generator owned by a context: the idempotent on the first
component, its complement on the second, and `0` on every other context. -/
noncomputable def chartGenerator (W : disconnectedSite.category) :
    Γ(disconnectedScheme.underlying, ⊤) :=
  if W = componentA then idempotentSection
  else if W = componentB then 1 - idempotentSection
  else 0

/-- The first component owns the idempotent.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem chartGenerator_componentA :
    chartGenerator componentA = idempotentSection := by
  rw [chartGenerator, if_pos rfl]

/-- The second component owns the complementary idempotent.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem chartGenerator_componentB :
    chartGenerator componentB = 1 - idempotentSection := by
  rw [chartGenerator, if_neg (Ne.symm componentA_ne_componentB), if_pos rfl]

/-- Every other context owns the zero generator. -/
theorem chartGenerator_eq_zero
    {W : disconnectedSite.category}
    (hA : W ≠ componentA) (hB : W ≠ componentB) :
    chartGenerator W = 0 := by
  rw [chartGenerator, if_neg hA, if_neg hB]

/-- Distinct contexts own generators with zero product: the two components are
complementary idempotents and every other generator vanishes. -/
theorem chartGenerator_mul_eq_zero
    {W V : disconnectedSite.category} (hWV : W ≠ V) :
    chartGenerator W * chartGenerator V = 0 := by
  by_cases hWA : W = componentA
  · subst hWA
    by_cases hVB : V = componentB
    · subst hVB
      rw [chartGenerator_componentA, chartGenerator_componentB, mul_sub,
        mul_one, idempotentSection_mul_self, sub_self]
    · rw [chartGenerator_eq_zero (Ne.symm hWV) hVB, mul_zero]
  · by_cases hWB : W = componentB
    · subst hWB
      by_cases hVA : V = componentA
      · subst hVA
        rw [chartGenerator_componentA, chartGenerator_componentB, sub_mul,
          one_mul, idempotentSection_mul_self, sub_self]
      · rw [chartGenerator_eq_zero hVA (Ne.symm hWV), mul_zero]
    · rw [chartGenerator_eq_zero hWA hWB, zero_mul]

/-- The open owned by a context. -/
noncomputable def chartOpen (W : disconnectedSite.category) :
    disconnectedScheme.underlying.Opens :=
  disconnectedScheme.underlying.basicOpen (chartGenerator W)

/-- Every owned open is affine, the ambient being affine. -/
theorem chartOpen_isAffineOpen (W : disconnectedSite.category) :
    AlgebraicGeometry.IsAffineOpen (chartOpen W) :=
  (isAffineOpen_top disconnectedScheme.underlying).basicOpen _

/-- Distinct contexts own disjoint opens. -/
theorem chartOpen_disjoint
    {W V : disconnectedSite.category} (hWV : W ≠ V) :
    chartOpen W ⊓ chartOpen V = ⊥ := by
  rw [chartOpen, chartOpen, ← AlgebraicGeometry.Scheme.basicOpen_mul,
    chartGenerator_mul_eq_zero hWV]
  exact disconnectedScheme.underlying.basicOpen_zero ⊤

/-- Context restriction preserves the owned open: every morphism touching an
owning context is an identity, and all remaining contexts own `⊥`. -/
theorem chartOpen_mono
    {source target : disconnectedSite.category} (f : source ⟶ target) :
    chartOpen source ≤ chartOpen target := by
  by_cases hst : source = target
  · rw [hst]
  · have hsA : source ≠ componentA := by
      intro h
      exact hst (eq_of_hom_component f (Or.inl h))
    have hsB : source ≠ componentB := by
      intro h
      exact hst (eq_of_hom_component f (Or.inr (Or.inl h)))
    rw [chartOpen, chartGenerator_eq_zero hsA hsB,
      disconnectedScheme.underlying.basicOpen_zero ⊤]
    exact bot_le

/-- The two components jointly cover the ambient: in every stalk the idempotent
is a unit or its complement is. -/
theorem chartOpen_iSup_eq_top :
    (⨆ W : disconnectedSite.category, chartOpen W) = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _
  have hxtop : x ∈ (⊤ : disconnectedScheme.underlying.Opens) := trivial
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      (disconnectedScheme.underlying.presheaf.germ ⊤ x hxtop
        idempotentSection) with hu | hu
  · refine TopologicalSpace.Opens.mem_iSup.mpr ⟨componentA, ?_⟩
    rw [chartOpen, chartGenerator_componentA]
    exact (AlgebraicGeometry.Scheme.mem_basicOpen _ idempotentSection
      x hxtop).mpr hu
  · refine TopologicalSpace.Opens.mem_iSup.mpr ⟨componentB, ?_⟩
    rw [chartOpen, chartGenerator_componentB]
    refine (AlgebraicGeometry.Scheme.mem_basicOpen _ (1 - idempotentSection)
      x hxtop).mpr ?_
    rwa [map_sub, map_one]

/-- SD8: the context-indexed chart cover of the disconnected ambient. -/
noncomputable def disconnectedContextCharts :
    EquationObservableRealization.EquationContextCharts
      (X := disconnectedScheme) :=
  EquationContextChartCover.ofMonotoneOpens disconnectedSite
    disconnectedScheme.underlying chartOpen
    (fun f => chartOpen_mono f)
    chartOpen_isAffineOpen chartOpen_iSup_eq_top

/-- The image open of a selected chart is the open its context owns.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem contextChartOpen_disconnected (W : disconnectedSite.category) :
    EquationObservableRealization.contextChartOpen
        disconnectedContextCharts W =
      chartOpen W := by
  have h : EquationObservableRealization.contextChartOpen
        disconnectedContextCharts W =
      AlgebraicGeometry.Scheme.Hom.opensRange (chartOpen W).ι ⊓ ⊤ := rfl
  rw [h, AlgebraicGeometry.Scheme.Opens.opensRange_ι, inf_top_eq]

/--
SD8, second separating fact: the selected cover satisfies the Čech refinement
condition.

Distinct contexts own disjoint opens, so every pairwise overlap of distinct
contexts is empty, and the overlap of a context with itself is covered by that
context.
-/
theorem disconnectedContextChartRefinement :
    EquationObservableRealization.EquationContextChartRefinement
      (X := disconnectedScheme) disconnectedContextCharts := by
  constructor
  intro W V
  by_cases hWV : W = V
  · subst hWV
    refine le_trans inf_le_left (le_iSup_of_le ⟨W, ⟨𝟙 W, 𝟙 W⟩⟩ ?_)
    exact le_rfl
  · rw [contextChartOpen_disconnected, contextChartOpen_disconnected,
      chartOpen_disjoint hWV]
    exact bot_le

/-- SD8: the compatibility producer obtained by the Čech route. -/
theorem disconnectedContextChartProducer :
    EquationObservableRealization.EquationContextChartProducer
      disconnectedRealization disconnectedContextCharts :=
  EquationObservableRealization.EquationContextChartProducer.ofRefinement
    disconnectedRealization disconnectedContextCharts
    disconnectedContextChartRefinement

/-! ## The glued section is none of the sections it glues -/

/-- Restriction of a global section to the open owned by a context. -/
private noncomputable abbrev resChart (W : disconnectedSite.category)
    (s : Γ(disconnectedScheme.underlying, ⊤)) :
    Γ(disconnectedScheme.underlying, chartOpen W) :=
  disconnectedScheme.underlying.presheaf.map
    (homOfLE (le_top : chartOpen W ≤ ⊤)).op s

/-- Restriction to an owned open preserves `0`. -/
private theorem resChart_zero (W : disconnectedSite.category) :
    resChart W 0 = 0 :=
  map_zero _

/-- Restriction to an owned open preserves `1`. -/
private theorem resChart_one (W : disconnectedSite.category) :
    resChart W 1 = 1 :=
  map_one _

/-- Restriction to an owned open preserves `2`. -/
private theorem resChart_two (W : disconnectedSite.category) :
    resChart W 2 = 2 :=
  map_ofNat _ 2

/-- Restriction to an owned open preserves products. -/
private theorem resChart_mul (W : disconnectedSite.category)
    (x y : Γ(disconnectedScheme.underlying, ⊤)) :
    resChart W (x * y) = resChart W x * resChart W y :=
  map_mul _ x y

/-- A context's own generator restricts to a unit on the open it owns. -/
private theorem resChart_generator_isUnit (W : disconnectedSite.category) :
    IsUnit (resChart W (chartGenerator W)) :=
  disconnectedScheme.underlying.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen
    (chartGenerator W)

/-- On the open owned by a context, every other context's generator vanishes. -/
private theorem resChart_eq_zero_of_ne
    {W V : disconnectedSite.category} (hWV : W ≠ V) :
    resChart W (chartGenerator V) = 0 := by
  refine (resChart_generator_isUnit W).mul_left_cancel ?_
  rw [mul_zero, ← map_mul, chartGenerator_mul_eq_zero hWV, map_zero]

/-- The second component's generator is idempotent. -/
private theorem chartGenerator_componentB_mul_self :
    chartGenerator componentB * chartGenerator componentB =
      chartGenerator componentB := by
  rw [chartGenerator_componentB]
  calc (1 - idempotentSection) * (1 - idempotentSection)
      = 1 - idempotentSection - idempotentSection +
          idempotentSection * idempotentSection := by ring
    _ = 1 - idempotentSection - idempotentSection + idempotentSection := by
        rw [idempotentSection_mul_self]
    _ = 1 - idempotentSection := by ring

/-- On the open it owns, the second component's generator restricts to `1`. -/
private theorem resChart_componentB_self :
    resChart componentB (chartGenerator componentB) = 1 := by
  refine (resChart_generator_isUnit componentB).mul_left_cancel ?_
  rw [mul_one, ← map_mul, chartGenerator_componentB_mul_self]

/-- Every context outside the two components owns an open with a trivial
section ring: its own generator is `0`, and `0` restricts to a unit there. -/
private theorem chartOpen_subsingleton
    {W : disconnectedSite.category}
    (hA : W ≠ componentA) (hB : W ≠ componentB) :
    Subsingleton Γ(disconnectedScheme.underlying, chartOpen W) := by
  have hu := resChart_generator_isUnit W
  rw [chartGenerator_eq_zero hA hB, resChart_zero] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

/-- Every context's universal section outside the second component is `0`. -/
theorem violationSection_eq_zero_of_ne
    {W : disconnectedSite.category} (hB : W ≠ componentB)
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.violationSection W i a = 0 := by
  rw [violationSection_eq_symbolicValue, symbolicValue, if_neg hB]
  exact Int.cast_zero

/-- On every owned open, the complementary idempotent agrees with that
context's own universal section. -/
private theorem resChart_complement
    (W : disconnectedSite.category)
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    resChart W (2 * (1 - idempotentSection)) =
      resChart W (disconnectedRealization.violationSection W i a) := by
  by_cases hA : W = componentA
  · subst hA
    rw [violationSection_componentA, resChart_zero, resChart_mul,
      ← chartGenerator_componentB,
      resChart_eq_zero_of_ne componentA_ne_componentB, mul_zero]
  · by_cases hB : W = componentB
    · subst hB
      rw [violationSection_componentB, resChart_mul,
        ← chartGenerator_componentB, resChart_componentB_self, mul_one,
        resChart_two]
    · haveI := chartOpen_subsingleton hA hB
      exact Subsingleton.elim _ _

/-- Restriction to a smaller open of an equality of restrictions. -/
private theorem resChart_of_contextChart
    {W : disconnectedSite.category}
    {s t : Γ(disconnectedScheme.underlying, ⊤)}
    (h : disconnectedScheme.underlying.presheaf.map
        (homOfLE (le_top :
          EquationObservableRealization.contextChartOpen
            disconnectedContextCharts W ≤ ⊤)).op s =
      disconnectedScheme.underlying.presheaf.map (homOfLE le_top).op t) :
    resChart W s = resChart W t := by
  have hle : chartOpen W ≤
      EquationObservableRealization.contextChartOpen
        disconnectedContextCharts W :=
    le_of_eq (contextChartOpen_disconnected W).symm
  have hmap := congrArg
    (disconnectedScheme.underlying.presheaf.map (homOfLE hle).op) h
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp] using hmap

/--
SD8, third separating fact: the glued section of Definition 5.2A is
`2 * (1 - e)`.

It is pinned down by the uniqueness clause of the gluing: on the open owned by
the first component it agrees with that component's universal section `0`, on
the open owned by the second component it agrees with `2`, and every remaining
owned open has a trivial section ring.
-/
theorem gluedViolationSection_eq_complement
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.gluedViolationSection
        disconnectedContextCharts disconnectedContextChartProducer i a =
      2 * (1 - idempotentSection) := by
  refine TopCat.Sheaf.eq_of_locally_eq'
    disconnectedScheme.underlying.sheaf chartOpen ⊤
    (fun _ => homOfLE le_top) (le_of_eq chartOpen_iSup_eq_top.symm) _ _ ?_
  intro W
  have hglued := disconnectedRealization.gluedViolationSection_on_open
    disconnectedContextCharts disconnectedContextChartProducer i a W
  rw [disconnectedRealization.contextChartOpenViolation_eq_restrict
    disconnectedContextCharts W i a] at hglued
  exact (resChart_of_contextChart hglued).trans
    (resChart_complement W i a).symm

/--
SD8, main theorem: the glued section is **none** of the universal sections it
glues.

Together with `violationSection_not_context_independent` and
`disconnectedContextChartRefinement` this separates the two compatibility
producers of Definition 5.2A: the Čech route fires on this cover, the
context-independence route cannot, and the section the Čech route produces is
new.
-/
theorem gluedViolationSection_ne_violationSection
    (W : disconnectedSite.category)
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.gluedViolationSection
        disconnectedContextCharts disconnectedContextChartProducer i a ≠
      disconnectedRealization.violationSection W i a := by
  rw [gluedViolationSection_eq_complement]
  by_cases hB : W = componentB
  · subst hB
    rw [violationSection_componentB]
    intro h
    have hint := congrArg globalEvalOne h
    rw [map_mul, map_sub, map_one, globalEvalOne_idempotentSection,
      map_ofNat] at hint
    omega
  · rw [violationSection_eq_zero_of_ne hB]
    intro h
    have hint := congrArg globalEvalZero h
    rw [map_mul, map_sub, map_one, globalEvalZero_idempotentSection,
      map_ofNat, map_zero] at hint
    omega

/-- The two owned components jointly exhaust the ambient. -/
theorem chartOpen_sup_eq_top :
    chartOpen componentA ⊔ chartOpen componentB = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← chartOpen_iSup_eq_top]
  refine iSup_le fun W => ?_
  by_cases hA : W = componentA
  · subst hA
    exact le_sup_left
  · by_cases hB : W = componentB
    · subst hB
      exact le_sup_right
    · rw [chartOpen, chartGenerator_eq_zero hA hB,
        disconnectedScheme.underlying.basicOpen_zero ⊤]
      exact bot_le

/-- A context owning the whole ambient would make the gluing return its own
universal section. -/
private theorem glued_eq_violationSection_of_chartOpen_eq_top
    {W : disconnectedSite.category} (htop : chartOpen W = ⊤)
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.gluedViolationSection
        disconnectedContextCharts disconnectedContextChartProducer i a =
      disconnectedRealization.violationSection W i a := by
  refine TopCat.Sheaf.eq_of_locally_eq'
    disconnectedScheme.underlying.sheaf (fun _ : Unit => chartOpen W) ⊤
    (fun _ => homOfLE le_top)
    (le_iSup_of_le () (le_of_eq htop.symm)) _ _ ?_
  intro _
  have hglued := disconnectedRealization.gluedViolationSection_on_open
    disconnectedContextCharts disconnectedContextChartProducer i a W
  rw [disconnectedRealization.contextChartOpenViolation_eq_restrict
    disconnectedContextCharts W i a] at hglued
  exact resChart_of_contextChart hglued

/-- SD8: the first component is a nonempty open.

If it were empty the second component would own the whole ambient, and the
gluing would then return that component's own universal section, contradicting
`gluedViolationSection_ne_violationSection`. -/
theorem chartOpen_componentA_ne_bot : chartOpen componentA ≠ ⊥ := by
  intro hbot
  have htop : chartOpen componentB = ⊤ := by
    rw [← chartOpen_sup_eq_top, hbot, bot_sup_eq]
  exact gluedViolationSection_ne_violationSection componentB PUnit.unit
    AAT.AG.FiniteModel.FiniteAtom.componentA
    (glued_eq_violationSection_of_chartOpen_eq_top htop _ _)

/-- SD8: the second component is a nonempty open. -/
theorem chartOpen_componentB_ne_bot : chartOpen componentB ≠ ⊥ := by
  intro hbot
  have htop : chartOpen componentA = ⊤ := by
    rw [← chartOpen_sup_eq_top, hbot, sup_bot_eq]
  exact gluedViolationSection_ne_violationSection componentA PUnit.unit
    AAT.AG.FiniteModel.FiniteAtom.componentA
    (glued_eq_violationSection_of_chartOpen_eq_top htop _ _)

/--
SD8: the represented Scheme is disconnected in the sense the fixture needs: the
two owned opens are nonempty, disjoint, and jointly the whole ambient.
-/
theorem ambient_disconnected :
    chartOpen componentA ≠ ⊥ ∧ chartOpen componentB ≠ ⊥ ∧
      chartOpen componentA ⊓ chartOpen componentB = ⊥ ∧
      chartOpen componentA ⊔ chartOpen componentB = ⊤ :=
  ⟨chartOpen_componentA_ne_bot, chartOpen_componentB_ne_bot,
    chartOpen_disjoint componentA_ne_componentB, chartOpen_sup_eq_top⟩

/-! ## The generated realization is not the empty one -/

/-- Every object-dependent residual of this equation system vanishes.

As a simp rule, it normalizes the left-hand fixture expression to the
right-hand concrete expression. -/
@[simp] theorem ambientResidualSection_eq_zero
    (W : disconnectedSite.category)
    (i : disconnectedSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    disconnectedRealization.ambientResidualSection W i a = 0 := by
  show disconnectedRealization.sectionMap W 0 = 0
  exact map_zero _

/-- The parity of a global section read at the first component. -/
noncomputable def globalParity :
    Γ(disconnectedScheme.underlying, ⊤) →+* ZMod 2 :=
  (Int.castRingHom (ZMod 2)).comp globalEvalZero

/-- Every generated equalizer relation is even. -/
theorem globalParity_realizationRelation
    (g : EquationObservableRealization.GeneratorIndex
      disconnectedSite.equationSystem) :
    globalParity (disconnectedRealization.realizationRelation g) = 0 := by
  show globalParity
      (disconnectedRealization.violationSection g.1 g.2.1 g.2.2 -
        disconnectedRealization.ambientResidualSection g.1 g.2.1 g.2.2) = 0
  rw [ambientResidualSection_eq_zero, sub_zero]
  by_cases hB : g.1 = componentB
  · rw [hB, violationSection_componentB, map_ofNat]
    decide
  · rw [violationSection_eq_zero_of_ne hB, map_zero]

/--
SD8: the generated realization ideal is a proper ideal.

This is what keeps the section side of Theorem 5.2C from being vacuous.  A
symbolic value that is a unit — `1`, say — would put a unit in the generated
ideal and collapse the equation-generated realization; the selected value `2`
does not.
-/
theorem realizationIdeal_ne_top :
    disconnectedRealization.realizationIdeal ≠ ⊤ := by
  intro htop
  have hle : disconnectedRealization.realizationIdeal ≤
      RingHom.ker globalParity := by
    rw [EquationObservableRealization.realizationIdeal]
    refine Ideal.span_le.mpr ?_
    rintro x ⟨g, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    exact globalParity_realizationRelation g
  have hone : (1 : Γ(disconnectedScheme.underlying, ⊤)) ∈
      disconnectedRealization.realizationIdeal := by
    rw [htop]
    trivial
  have := hle hone
  rw [RingHom.mem_ker, map_one] at this
  exact one_ne_zero this

/--
SD8: the caller-side chart identity of the pre-equation-system route fails on
this fixture.

This is the strictness witness for `EquationContextChartProducer`: the producer
field holds here (`disconnectedContextChartProducer`) while the identity that
the earlier route demanded does not.
-/
theorem chartAgreement_fails :
    ¬ ∀ (W V : disconnectedSite.category)
        (i : disconnectedSite.equationSystem.Index)
        (a : AAT.AG.FiniteModel.carrier.Atom),
        (disconnectedContextCharts.chartMap W).appTop
            (disconnectedRealization.violationSection V i a) =
          disconnectedRealization.contextChartEvaluation
            disconnectedContextCharts W
            (disconnectedSite.equationSystem.violationCoordinate W i a) := by
  intro h
  exact violationSection_not_context_independent
    (fun W V i a =>
      disconnectedRealization.violationSection_const_of_chartAgreement
        disconnectedContextCharts h W V i a)

/-! ## Theorem 5.2C on the separating cover -/

/-- The image open of a selected chart is the open its context owns. -/
theorem chartImage_eq (W : disconnectedSite.category) :
    (chartOpen W).ι ''ᵁ ⊤ = chartOpen W :=
  AlgebraicGeometry.Scheme.Opens.ι_image_top _

/-- The generator of the source chart, read on the target chart.

The context morphism is taken only to fix the implicit source and target; the
generator itself depends on those two contexts and not on the morphism, which
is unique in a thin category. -/
noncomputable def transitionGenerator
    {source target : disconnectedSite.category} (_f : source ⟶ target) :
    Γ(disconnectedScheme.underlying, (chartOpen target).ι ''ᵁ ⊤) :=
  disconnectedScheme.underlying.presheaf.map
    (homOfLE (le_top : (chartOpen target).ι ''ᵁ ⊤ ≤ ⊤)).op
    (chartGenerator source)

/-- The source chart is exactly the principal open of that generator. -/
theorem transitionGenerator_basicOpen_eq
    {source target : disconnectedSite.category} (f : source ⟶ target) :
    (chartOpen source).ι ''ᵁ ⊤ =
      disconnectedScheme.underlying.basicOpen (transitionGenerator f) := by
  rw [chartImage_eq, transitionGenerator,
    disconnectedScheme.underlying.basicOpen_res (chartGenerator source) _,
    chartImage_eq]
  exact (inf_eq_right.mpr (chartOpen_mono f)).symm

/-- SD8: the context-transition localization of the separating cover.

Every transition is the inclusion of one principal open into another, so the
affine basic-open criterion applies uniformly; no transition is assumed
invertible. -/
noncomputable def disconnectedContextChartLocalization :
    EquationObservableRealization.EquationContextChartLocalization
      disconnectedContextCharts where
  submonoid f := Submonoid.powers (transitionGenerator f)
  isLocalization := by
    intro source target f
    have haffine :
        AlgebraicGeometry.IsAffineOpen ((chartOpen target).ι ''ᵁ ⊤) := by
      rw [chartImage_eq]
      exact chartOpen_isAffineOpen target
    show @IsLocalization _ _ (Submonoid.powers (transitionGenerator f))
      Γ(disconnectedScheme.underlying, (chartOpen source).ι ''ᵁ ⊤) _
      (RingHom.toAlgebra
        (disconnectedScheme.underlying.homOfLE
          (chartOpen_mono f)).appTop.hom)
    rw [congrArg CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.homOfLE_appTop (chartOpen_mono f))]
    exact haffine.isLocalization_of_eq_basicOpen
      (transitionGenerator f) _ (transitionGenerator_basicOpen_eq f)

/-- SD8: the complete chart producer on the separating cover. -/
noncomputable def disconnectedSchemeChartProducer :
    EquationObservableRealization.EquationSchemeChartProducer
      disconnectedRealization disconnectedContextCharts where
  coordinate := disconnectedContextChartProducer
  localization := disconnectedContextChartLocalization

/-- Every chart of the one-chart atlas is the identity, so every atlas-overlap
projection is an isomorphism. -/
theorem atlasOverlap_fst_isIso
    (j l : disconnectedScheme.atlas.Index) :
    IsIso (pullback.fst (disconnectedScheme.atlas.chart j).map
      (disconnectedScheme.atlas.chart l).map) := by
  show IsIso (pullback.fst
    (𝟙 (architectureChartSpec disconnectedRaw baseObject))
    (𝟙 (architectureChartSpec disconnectedRaw baseObject)))
  have hcomp :=
    (IsPullback.of_id_fst
      (f := 𝟙 (architectureChartSpec disconnectedRaw baseObject))
        ).isoPullback_hom_fst
  haveI : IsIso
      ((IsPullback.of_id_fst
        (f := 𝟙 (architectureChartSpec disconnectedRaw baseObject))
          ).isoPullback.hom ≫
        pullback.fst
          (𝟙 (architectureChartSpec disconnectedRaw baseObject))
          (𝟙 (architectureChartSpec disconnectedRaw baseObject))) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (IsPullback.of_id_fst
      (f := 𝟙 (architectureChartSpec disconnectedRaw baseObject))
        ).isoPullback.hom
    (pullback.fst
      (𝟙 (architectureChartSpec disconnectedRaw baseObject))
      (𝟙 (architectureChartSpec disconnectedRaw baseObject)))

/-- SD8: the atlas-overlap localization, discharged by invertibility of the
projections of the one-chart atlas. -/
noncomputable def disconnectedAmbientChartLocalization :
    EquationObservableRealization.EquationAmbientChartLocalization
      (raw := disconnectedRaw) (X := disconnectedScheme) where
  submonoid _ _ := Submonoid.powers 1
  isLocalization := by
    intro j l
    letI : Algebra
        Γ((disconnectedScheme.atlas.chart j).domain, ⊤)
        Γ(disconnectedScheme.atlas.actualOverlap disconnectedRaw j l, ⊤) :=
      (pullback.fst (disconnectedScheme.atlas.chart j).map
        (disconnectedScheme.atlas.chart l).map).appTop.hom.toAlgebra
    haveI := atlasOverlap_fst_isIso j l
    exact IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso
        (pullback.fst (disconnectedScheme.atlas.chart j).map
          (disconnectedScheme.atlas.chart l).map).appTop)

/--
SD8, fourth fact: Theorem 5.2C's chart correspondence fires on the separating
cover.

Every clause of `EquationContextWitnessChartRealized` is discharged: context
chart generation, context-transition base change through the principal-open
localizations, atlas-overlap base change, atlas-chart generation, and overlap
agreement.  Unlike SD6, none of this is routed through context independence of
the universal sections, which fails here.
-/
theorem disconnectedEquationContextWitnessChartRealized
    (i : disconnectedSite.equationSystem.Index) :
    disconnectedRealization.EquationContextWitnessChartRealized
      disconnectedContextCharts disconnectedContextChartProducer i :=
  disconnectedRealization.equationContextWitnessChartRealized
    disconnectedContextCharts disconnectedSchemeChartProducer
    disconnectedAmbientChartLocalization i

/--
SD8: Part III, Theorem 5.2C fires on the separating cover.

The same statement as SD5 and SD6, on the cover whose compatibility comes from
the Čech route while the universal sections are context dependent.
-/
theorem disconnectedLawfulnessIdealFactorizationChartCorrespondence
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ disconnectedRealization.realizationScheme) :
    ((disconnectedRealization.EquationLawfulAlong
          disconnectedContextCharts s ↔
        (disconnectedRealization.equationGeneratedIdealSheaf
          disconnectedContextCharts
          disconnectedContextChartProducer).comap s = ⊥) ∧
      ((disconnectedRealization.equationGeneratedIdealSheaf
          disconnectedContextCharts
          disconnectedContextChartProducer).comap s = ⊥ ↔
        Nonempty
          (disconnectedRealization.FactorsThroughEquationGeneratedLawfulClosedSubscheme
            disconnectedContextCharts
            disconnectedContextChartProducer
            s))) ∧
      ∀ i : disconnectedSite.equationSystem.RequiredIndex,
        disconnectedRealization.EquationContextWitnessChartRealized
          disconnectedContextCharts
          disconnectedContextChartProducer
          i.1 :=
  disconnectedRealization.lawfulnessIdealFactorizationChartCorrespondence
    disconnectedRealization_valid
    disconnectedContextCharts
    disconnectedSchemeChartProducer
    disconnectedAmbientChartLocalization
    s

end DisconnectedGluing

end AAT.AG.Examples.StandardGeometryReferenceModels
