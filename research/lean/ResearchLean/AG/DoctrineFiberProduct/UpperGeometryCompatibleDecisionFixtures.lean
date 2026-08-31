import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSolutionEquivalence
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCochains
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRawCochainImages
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleDecisionNoGo
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Witnesses
import ResearchLean.AG.CrossStageCoherence.ComparisonDescentInstances

/-!
# Revision-7 compatible decision fixtures for G-115

This module constructs the named positive packet over the active reverse
refinement context.  The source core has four symmetric signature axes inside
the actual selected target fiber.  Its horizontal edge and two authored
automorphisms are concrete adjacent transpositions; no nonidentity proof,
generated comparator, solution, or cochain is stored in the problem input.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open UpperGeometryCompatibleProblemInputData

set_option maxHeartbeats 4000000

namespace UpperDecisionWitness

/-!
## Implementation notes

The distinguished context gives Support, Axis, and Observable the same four
concrete values.  A pointed preorder sends every distinct-context meet to a
Support/Axis-empty bottom whose observable is unique.  This is the smallest
finite-meet site on which adjacent permutations act on all three real local
carriers while remaining natural on every readable arrow.

Using the former `PUnit` carriers was rejected because it made every local
action identity.  Counting only `base.upper.axisMap` was also rejected because
it would replace the fixed local-carrier obligation by a core-only witness.
For the Cartesian-generated comparator, concrete values are therefore pulled
back through the reviewed realization-exact carrier equivalences; its full
factorization then proves the actual generated local maps send the inverse
image of one to the inverse image of two.
-/

/-! ## A four-axis core in the actual active reverse target fiber -/

/-- The reviewed active reverse context is the decision context. -/
noncomputable abbrev context : ActiveRefinementBCContext FiniteModel.carrier :=
  activeReverseContext

/-- The distinguished local context whose three geometry carriers expose the
four decision values. -/
def decisionContext
    (A : ArchitectureObject FiniteModel.carrier) : Site.ArchCtx A where
  minimal := {
    Support := Fin 4
    Axis := Fin 4
    Observable := Fin 4
    supportReads := fun _ _ => False
    supportReads_objectFamily := fun h => False.elim h
    axisReads := fun _ => True
    observableReads := fun _ => True }
  Extension := PUnit
  extension := PUnit.unit

/-- A Support/Axis-empty bottom context. It supplies meets without imposing
maps out of the distinguished finite Support and Axis carriers; its unique
observable keeps the contravariant restriction total. -/
def bottomContext
    (A : ArchitectureObject FiniteModel.carrier) : Site.ArchCtx A where
  minimal := {
    Support := PEmpty
    Axis := PEmpty
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := fun h => False.elim h
    axisReads := fun _ => False
    observableReads := fun _ => True }
  Extension := PUnit
  extension := PUnit.unit

/-- The unique readable restriction from the bottom context. -/
def bottomContextMorphism
    (A : ArchitectureObject FiniteModel.carrier) (W : Site.ArchCtx A) :
    Site.ContextMorphism (bottomContext A) W where
  supportMap := PEmpty.elim
  axisMap := PEmpty.elim
  observableRestrict := fun _ => PUnit.unit

/-- The bottom restriction satisfies the selected restriction role. -/
theorem bottomContextMorphism_isRestriction
    (A : ArchitectureObject FiniteModel.carrier) (W : Site.ArchCtx A) :
    (bottomContextMorphism A W).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support
    exact PEmpty.elim support
  · intro axis
    exact PEmpty.elim axis
  · intro observable _
    trivial
  · intro support
    exact PEmpty.elim support

/-- The selected readable morphism and its restriction proof for the pointed
preorder. -/
noncomputable def decisionReadableMorphism
    (A : ArchitectureObject FiniteModel.carrier) {W V : Site.ArchCtx A}
    (h : W = V ∨ W = bottomContext A) :
    Site.ContextMorphism W V := by
  classical
  by_cases hEq : W = V
  · subst V
    exact Site.identityContextMorphism W
  · have hBottom : W = bottomContext A := h.resolve_left hEq
    subst W
    exact bottomContextMorphism A V

/-- The selected pointed-preorder morphism is always a restriction. -/
theorem decisionReadableMorphism_isRestriction
    (A : ArchitectureObject FiniteModel.carrier) {W V : Site.ArchCtx A}
    (h : W = V ∨ W = bottomContext A) :
    (decisionReadableMorphism A h).IsRestriction := by
  classical
  by_cases hEq : W = V
  · subst V
    simpa [decisionReadableMorphism] using
      (show (Site.identityContextMorphism W).IsRestriction from
        ⟨fun value => value, fun value => value,
          fun value => value, fun h => W.supportReads_objectFamily h⟩)
  · have hBottom : W = bottomContext A := h.resolve_left hEq
    subst W
    simpa [decisionReadableMorphism, hEq] using
      bottomContextMorphism_isRestriction A V

/-- A pointed finite-meet context preorder: distinct contexts meet at bottom.
This makes the distinguished carrier permutation natural rather than hiding it
behind a core-only map. -/
noncomputable def decisionContextPreorder
    (A : ArchitectureObject FiniteModel.carrier) :
    Site.ContextPreorderCategory A where
  le W V := W = V ∨ W = bottomContext A
  refl W := Or.inl rfl
  trans := by
    intro W V X hWV hVX
    rcases hWV with hWV | hW
    · subst V
      exact hVX
    · exact Or.inr hW
  readableMorphism h := decisionReadableMorphism A h
  readableMorphism_isRestriction h :=
    decisionReadableMorphism_isRestriction A h

/-- The concrete meet operation for the pointed context preorder. -/
noncomputable def decisionContextMeet
    (A : ArchitectureObject FiniteModel.carrier)
    (W V : Site.ArchCtx A) : Site.ArchCtx A := by
  classical
  exact if W = V then W else bottomContext A

/-- Binary meets for the pointed context preorder. -/
noncomputable def decisionContextFiniteMeet
    (A : ArchitectureObject FiniteModel.carrier) :
    Site.ContextFiniteMeet (decisionContextPreorder A) where
  meet := decisionContextMeet A
  meet_le_left := by
    intro W V
    by_cases h : W = V
    · simp [decisionContextMeet, h, decisionContextPreorder]
    · simp [decisionContextMeet, h, decisionContextPreorder]
  meet_le_right := by
    intro W V
    by_cases h : W = V
    · subst V
      simp [decisionContextMeet, decisionContextPreorder]
    · simp [decisionContextMeet, h, decisionContextPreorder]
  le_meet := by
    intro X W V hXW hXV
    by_cases hWV : W = V
    · subst V
      simpa [decisionContextMeet] using hXW
    · simp only [decisionContextMeet, hWV, if_false]
      rcases hXW with hXW | hX
      · rcases hXV with hXV | hX
        · exact False.elim (hWV (hXW.symm.trans hXV))
        · exact Or.inr hX
      · exact Or.inr hX

/-- Nonempty target equation system; all residuals are zero. -/
noncomputable def equationSystem
    (A : ArchitectureObject FiniteModel.carrier) :
    ArchitecturalEquationSystem (decisionContextPreorder A) where
  Index := PUnit
  role _ := EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => 0
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ _ _ _ => 0
  equationResidual_restrict := by intros; rfl

/-- Sound nonempty equation reading on the all-admitting active target. -/
noncomputable def equationReading
    (A : ArchitectureObject FiniteModel.carrier) : EquationReading A where
  contextPreorder := decisionContextPreorder A
  equationSystem := equationSystem A
  circuits := { code := fun _ => .reject }
  circuitSound := by
    intro _index _object _datum _hmatches haccepts _hequation
    simp at haccepts

/-- Active-target reading with four symmetric signature axes. -/
noncomputable def reading : CoreReading FiniteModel.carrier where
  doctrine := activeReverseTargetPoint.doctrine
  source := activeReverseTargetPoint.source
  family_listFinite := ⟨FiniteModel.FiniteAtom.all,
    fun atom _ => FiniteModel.FiniteAtom.mem_all atom⟩
  composition := FiniteModel.compositionReading
  objectReading := FiniteModel.objectReading
  equationReading := equationReading _
  invariantReading := FiniteModel.invariantFamily
  signatureReading := FiniteCrossStageWitness.signature
  operationReading := FiniteModel.operationReading

/-- Four-axis core generated in the actual target fiber. -/
noncomputable def core : AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem reading

/-- The decision core is an actual object of the selected active target fiber. -/
noncomputable def coreObject : CoreFiber activeReverseTargetPoint :=
  ⟨core, rfl⟩

/-- A signature permutation as a self-map of the decision core. -/
noncomputable def corePermutationTotal (permutation : Equiv.Perm (Fin 4)) :
    PackageTotalHom core core where
  base := ExtInstHom.id (packagePoint core)
  upper :=
    { SignedExactCoreReadingHom.refl core with
      axisMap := permutation
      coordinateEquiv := fun _ => permutation
      axis_selected_iff := fun _ => Iff.rfl
      coordinate_eq := by intro object axis; rfl }
  atomEquiv_eq := rfl

/-- Core permutation total homs compose as the corresponding permutations. -/
theorem corePermutationTotal_comp (first second : Equiv.Perm (Fin 4)) :
    (corePermutationTotal first).comp (corePermutationTotal second) =
      corePermutationTotal (first.trans second) := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

/-- The identity permutation gives the identity core total hom. -/
theorem corePermutationTotal_refl :
    corePermutationTotal (Equiv.refl (Fin 4)) = PackageTotalHom.id core := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

/-! ## Selected geometry and coefficient-trivial automorphisms -/

/-- The three axes used by the decision fixture; the fourth axis witnesses a
genuine nonselected direction. -/
def SelectedAxis (axis : Fin 4) : Prop := axis ≠ (3 : Fin 4)

/-- Axis zero is selected. -/
theorem selectedAxis_zero : SelectedAxis (0 : Fin 4) := by
  simp [SelectedAxis]

/-- Axis three is genuinely excluded from the selection. -/
theorem not_selectedAxis_three : ¬ SelectedAxis (3 : Fin 4) := by
  simp [SelectedAxis]

/-- Coverage requirements selecting exactly the three decision axes. -/
def requirements : Site.CoverageRequirements core.object
    core.equationSystem core.algebra.signatureReading where
  requiredSupport := fun _ => False
  requiredEquationCoordinate := fun _ => False
  selectedViolationWitness := fun _ => False
  requiredAxis := fun axis => SelectedAxis axis
  supportVisibleOn := fun _ _ => True
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun _ axis => SelectedAxis axis
  boundaryVisibleOn := fun _ _ => True

/-- Selected geometry on the pointed finite-meet decision site. -/
noncomputable def geometry : Site.SelectedGeometryReading core where
  requirements := requirements
  overlap := Site.meetOverlapPullback core.contextPreorder
    (decisionContextFiniteMeet core.object)

/-- One-coordinate local polynomial family at every decision context. -/
def coordFamily (W : geometry.toAATSite.category) :
    LawAlgebra.CoordinateFamily W.ctx where
  Coord := Unit
  label := fun _ => LawAlgebra.CoordinateLabel.semantic
  LocalData := fun _ => Unit

/-- The nonzero quadratic-minus-linear raw relation at every context. -/
noncomputable def relationFamily (W : geometry.toAATSite.category) :
    LawAlgebra.StructuralRelationFamily (coordFamily W) Int where
  Relation := Unit
  polynomial := fun _ => MvPolynomial.X () ^ 2 - MvPolynomial.X ()

/-- Identity restriction of the unique raw coordinate. -/
noncomputable def coordinateRestriction
    {X Y : geometry.toAATSite.category} (w : X ⟶ Y) :
    LawAlgebra.TypedCoordinateRestriction (coordFamily X) (coordFamily Y) Int
      (geometry.toAATSite.contextPreorder.morphism (leOfHom w)) where
  variableImage := fun _ => MvPolynomial.X ()

/-- Coordinate restriction commutes with the raw polynomial. -/
theorem coordinateRestriction_polynomialMap
    {X Y : geometry.toAATSite.category} (w : X ⟶ Y) :
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

/-- The raw relation family is stable under all context restrictions. -/
noncomputable def restrictionStable
    {X Y : geometry.toAATSite.category} (w : X ⟶ Y) :
    LawAlgebra.RestrictionStableStructuralRelations
      (relationFamily X) (relationFamily Y)
      (geometry.toAATSite.contextPreorder.morphism (leOfHom w)) where
  restriction := coordinateRestriction w
  maps_JStruct := by
    intro polynomial hpolynomial
    have identity : (coordinateRestriction w).polynomialMap polynomial =
        polynomial := by
      rw [coordinateRestriction_polynomialMap]
      rfl
    rw [identity]
    exact hpolynomial

/-- Raw ambient restriction system used by the decision geometry. -/
noncomputable def raw :
    LawAlgebra.RawAmbientRestrictionSystem geometry.toAATSite Int where
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

/-- Complete geometry package for the positive decision fixture. -/
noncomputable def package : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := core
  geometry := geometry
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := raw

/-- Distinguished four-valued local context. -/
noncomputable abbrev baseContext : Site.ArchCtx core.object :=
  decisionContext core.object

/-- The selected site contains the distinguished context. -/
theorem site_nonempty : Nonempty package.site.category :=
  ⟨⟨baseContext⟩⟩

/-- The distinguished context belongs to the top cover. -/
theorem has_actual_cover :
    (⊤ : Sieve (⟨baseContext⟩ : package.site.category)) ∈
      package.site.topology ⟨baseContext⟩ :=
  package.site.top_mem _

/-- The coefficient ring is nontrivial at the chosen concrete value. -/
theorem coefficient_nontrivial : (2 : package.Coefficient) ≠ 0 := by
  change (2 : Int) ≠ 0
  norm_num

/-- The named quadratic raw relation is not zero. -/
theorem raw_relation_nonzero :
    ((package.raw.relationFamily
      (⟨baseContext⟩ : package.site.category)).polynomial ()) ≠ 0 := by
  change (MvPolynomial.X () ^ 2 - MvPolynomial.X () :
    MvPolynomial Unit Int) ≠ 0
  intro equality
  have evaluated := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (2 : Int))) equality
  norm_num at evaluated

/-- Core permutations leave the constant raw restriction system unchanged. -/
theorem rawReindex_corePermutation (permutation : Equiv.Perm (Fin 4))
    (system : LawAlgebra.RawAmbientRestrictionSystem package.site
      package.Coefficient) :
    rawReindex (G := package) (H := package)
      (corePermutationTotal permutation) system = system := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext
  · rfl
  · rfl
  · rfl

/-- Component equalities determine dependent geometry homs heterogeneously. -/
theorem geometryHom_heq_of_base_eq
    {f g : PackageTotalHom package.core package.core}
    (F : GeomReadHom package package f)
    (T : GeomReadHom package package g)
    (baseEquality : f = g)
    (coefficientEquality : F.coefficientHom = T.coefficientHom)
    (supportEquality : HEq F.supportComp T.supportComp)
    (axisEquality : HEq F.axisComp T.axisComp)
    (observableEquality : HEq F.observableComp T.observableComp) :
    HEq F T := by
  cases baseEquality
  exact heq_of_eq (GeomReadHom.ext coefficientEquality supportEquality
    axisEquality observableEquality)

/-- The distinguished local support permutation, extended by identity away
from the decision context. -/
noncomputable def localSupportPermutation (permutation : Equiv.Perm (Fin 4))
    (W : package.site.category) : W.ctx.Support → W.ctx.Support := by
  classical
  by_cases hW : W.ctx = baseContext
  · exact fun support =>
      cast (congrArg (fun X : Site.ArchCtx core.object => X.Support) hW.symm)
        (permutation
          (cast (congrArg (fun X : Site.ArchCtx core.object => X.Support) hW)
            support))
  · exact _root_.id

/-- The distinguished local axis permutation, extended by identity away from
the decision context. -/
noncomputable def localAxisPermutation (permutation : Equiv.Perm (Fin 4))
    (W : package.site.category) : W.ctx.Axis → W.ctx.Axis := by
  classical
  by_cases hW : W.ctx = baseContext
  · exact fun axis =>
      cast (congrArg (fun X : Site.ArchCtx core.object => X.Axis) hW.symm)
        (permutation
          (cast (congrArg (fun X : Site.ArchCtx core.object => X.Axis) hW) axis))
  · exact _root_.id

/-- The distinguished local observable permutation, extended by identity away
from the decision context. -/
noncomputable def localObservablePermutation (permutation : Equiv.Perm (Fin 4))
    (W : package.site.category) : W.ctx.Observable → W.ctx.Observable := by
  classical
  by_cases hW : W.ctx = baseContext
  · exact fun observable =>
      cast (congrArg (fun X : Site.ArchCtx core.object => X.Observable) hW.symm)
        (permutation
          (cast (congrArg (fun X : Site.ArchCtx core.object => X.Observable) hW)
            observable))
  · exact _root_.id

/-- At the distinguished context, the local support action is the requested
finite permutation. -/
@[simp] theorem localSupportPermutation_base
    (permutation : Equiv.Perm (Fin 4)) (support : Fin 4) :
    localSupportPermutation permutation
      (⟨baseContext⟩ : package.site.category) support = permutation support := by
  simp [localSupportPermutation, baseContext, decisionContext]

/-- At the distinguished context, the local axis action is the requested
finite permutation. -/
@[simp] theorem localAxisPermutation_base
    (permutation : Equiv.Perm (Fin 4)) (axis : Fin 4) :
    localAxisPermutation permutation
      (⟨baseContext⟩ : package.site.category) axis = permutation axis := by
  simp [localAxisPermutation, baseContext, decisionContext]

/-- At the distinguished context, the local observable action is the requested
finite permutation. -/
@[simp] theorem localObservablePermutation_base
    (permutation : Equiv.Perm (Fin 4)) (observable : Fin 4) :
    localObservablePermutation permutation
      (⟨baseContext⟩ : package.site.category) observable =
        permutation observable := by
  simp [localObservablePermutation, baseContext, decisionContext]

/-- Every selected endomorphism in the pointed thin context category exposes
the identity context morphism. -/
theorem sourceContextMorphism_self
    (W : package.site.category) (w : W ⟶ W) :
    sourceContextMorphism w = Site.identityContextMorphism W.ctx := by
  change (decisionContextPreorder core.object).morphism (leOfHom w) = _
  simp [Site.ContextPreorderCategory.morphism, decisionContextPreorder,
    decisionReadableMorphism]

/-- Full geometry action of a decision-axis permutation, including all three
actual local carrier maps. -/
noncomputable def geometryPermutationHom
    (permutation : Equiv.Perm (Fin 4))
    (preservesSelected : ∀ axis, SelectedAxis axis →
      SelectedAxis (permutation axis)) :
    GeomReadHom package package (corePermutationTotal permutation) where
  coverage := {
    requiredSupport := fun _ h => False.elim h
    requiredEquationCoordinate := fun _ h => False.elim h
    selectedViolationWitness := fun _ h => False.elim h
    requiredAxis := preservesSelected
    supportVisibleOn := fun _ _ _ => trivial
    equationCoordinateVisibleOn := fun _ _ _ => trivial
    violationWitnessVisibleOn := fun _ _ _ => trivial
    axisReadableOn := fun _ axis readable => preservesSelected axis readable
    boundaryVisibleOn := fun _ _ _ => trivial }
  overlap := { overlapIso := fun _ _ _ => Iso.refl _ }
  coefficientHom := RingHom.id package.Coefficient
  raw_eq := by
    unfold rawTransport
    rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_id]
    exact (rawReindex_corePermutation permutation package.raw).symm
  supportComp W := localSupportPermutation permutation W
  axisComp W := localAxisPermutation permutation W
  observableComp W := localObservablePermutation permutation W
  supportReads W support _ h := by
    classical
    change W.ctx.minimal.supportReads
      (localSupportPermutation permutation W support) _
    by_cases hW : W.ctx = baseContext
    · cases W with
      | mk Wctx =>
          dsimp at hW ⊢
          subst Wctx
          exact False.elim h
    · simpa [localSupportPermutation, hW] using h
  axisReads W axis h := by
    classical
    change W.ctx.minimal.axisReads (localAxisPermutation permutation W axis)
    by_cases hW : W.ctx = baseContext
    · cases W with
      | mk Wctx =>
          dsimp at hW ⊢
          subst Wctx
          trivial
    · simpa [localAxisPermutation, hW] using h
  observableReads W observable h := by
    classical
    change W.ctx.minimal.observableReads
      (localObservablePermutation permutation W observable)
    by_cases hW : W.ctx = baseContext
    · cases W with
      | mk Wctx =>
          dsimp at hW ⊢
          subst Wctx
          trivial
    · simpa [localObservablePermutation, hW] using h
  support_naturality := by
    intro W V w support
    have hwv := leOfHom w
    change (decisionContextPreorder core.object).le W.ctx V.ctx at hwv
    rcases hwv with hwv | hbottom
    · have hWV : W = V := by
        cases W
        cases V
        simp_all
      subst V
      have ht : (@targetContextMorphism _ package package
          (corePermutationTotal permutation) W W w) =
          sourceContextMorphism w := by rfl
      rw [ht, sourceContextMorphism_self W w]
      rfl
    · have hW : W =
          (⟨bottomContext core.object⟩ : package.site.category) := by
        cases W
        simp_all
      subst W
      exact PEmpty.elim support
  axis_naturality := by
    intro W V w axis
    have hwv := leOfHom w
    change (decisionContextPreorder core.object).le W.ctx V.ctx at hwv
    rcases hwv with hwv | hbottom
    · have hWV : W = V := by
        cases W
        cases V
        simp_all
      subst V
      have ht : (@targetContextMorphism _ package package
          (corePermutationTotal permutation) W W w) =
          sourceContextMorphism w := by rfl
      rw [ht, sourceContextMorphism_self W w]
      rfl
    · have hW : W =
          (⟨bottomContext core.object⟩ : package.site.category) := by
        cases W
        simp_all
      subst W
      exact PEmpty.elim axis
  observable_naturality := by
    intro W V w observable
    have hwv := leOfHom w
    change (decisionContextPreorder core.object).le W.ctx V.ctx at hwv
    rcases hwv with hwv | hbottom
    · have hWV : W = V := by
        cases W
        cases V
        simp_all
      subst V
      have ht : (@targetContextMorphism _ package package
          (corePermutationTotal permutation) W W w) =
          sourceContextMorphism w := by rfl
      rw [ht, sourceContextMorphism_self W w]
      rfl
    · have hW : W =
          (⟨bottomContext core.object⟩ : package.site.category) := by
        cases W
        simp_all
      subst W
      change PUnit.unit = PUnit.unit
      rfl

/-- Adjacent transposition used by the horizontal edge. -/
noncomputable def swap01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1

/-- Adjacent transposition used by the authored comparator. -/
noncomputable def swap12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

/-- The horizontal transposition preserves selected axes. -/
theorem swap01_preserves :
    ∀ axis, SelectedAxis axis → SelectedAxis (swap01 axis) := by
  intro axis selected
  fin_cases axis <;> simp_all [SelectedAxis, swap01]
  all_goals decide

/-- The comparator transposition preserves selected axes. -/
theorem swap12_preserves :
    ∀ axis, SelectedAxis axis → SelectedAxis (swap12 axis) := by
  intro axis selected
  fin_cases axis <;> simp_all [SelectedAxis, swap12]
  all_goals decide

/-- Full geometry endomorphism induced by the horizontal transposition. -/
noncomputable def swap01Total : GeometryTotalHom package package where
  base := corePermutationTotal swap01
  geometry := geometryPermutationHom swap01 swap01_preserves

/-- Full geometry endomorphism induced by the comparator transposition. -/
noncomputable def swap12Total : GeometryTotalHom package package where
  base := corePermutationTotal swap12
  geometry := geometryPermutationHom swap12 swap12_preserves

/-- The horizontal transposition is involutive. -/
theorem swap01_square : swap01.trans swap01 = Equiv.refl (Fin 4) := by
  apply Equiv.ext
  intro axis
  fin_cases axis <;> rfl

/-- The comparator transposition is involutive. -/
theorem swap12_square : swap12.trans swap12 = Equiv.refl (Fin 4) := by
  apply Equiv.ext
  intro axis
  fin_cases axis <;> rfl

/-- The full horizontal geometry action squares to the identity. -/
theorem swap01Total_square :
    swap01Total.comp swap01Total = GeometryTotalHom.id package := by
  have baseSquare :
      (swap01Total.comp swap01Total).base =
        (GeometryTotalHom.id package).base := by
    change (corePermutationTotal swap01).comp (corePermutationTotal swap01) =
      PackageTotalHom.id core
    rw [corePermutationTotal_comp, swap01_square]
    exact corePermutationTotal_refl
  apply GeometryTotalHom.ext
  · exact baseSquare
  · apply geometryHom_heq_of_base_eq _ _ baseSquare
    · exact RingHom.id_comp _
    · apply heq_of_eq
      funext W support
      change localSupportPermutation swap01 W
          (localSupportPermutation swap01 W support) = support
      classical
      by_cases hW : W.ctx = baseContext
      · cases W with
        | mk Wctx =>
            dsimp at hW ⊢
            subst Wctx
            simpa only [localSupportPermutation_base] using
              congrArg (fun e : Equiv.Perm (Fin 4) => e support) swap01_square
      · simp [localSupportPermutation, hW]
    · apply heq_of_eq
      funext W axis
      change localAxisPermutation swap01 W
          (localAxisPermutation swap01 W axis) = axis
      classical
      by_cases hW : W.ctx = baseContext
      · cases W with
        | mk Wctx =>
            dsimp at hW ⊢
            subst Wctx
            simpa only [localAxisPermutation_base] using
              congrArg (fun e : Equiv.Perm (Fin 4) => e axis) swap01_square
      · simp [localAxisPermutation, hW]
    · apply heq_of_eq
      funext W observable
      change localObservablePermutation swap01 W
          (localObservablePermutation swap01 W observable) = observable
      classical
      by_cases hW : W.ctx = baseContext
      · cases W with
        | mk Wctx =>
            dsimp at hW ⊢
            subst Wctx
            simpa only [localObservablePermutation_base] using
              congrArg (fun e : Equiv.Perm (Fin 4) => e observable) swap01_square
      · simp [localObservablePermutation, hW]

/-- The full comparator geometry action squares to the identity. -/
theorem swap12Total_square :
    swap12Total.comp swap12Total = GeometryTotalHom.id package := by
  have baseSquare :
      (swap12Total.comp swap12Total).base =
        (GeometryTotalHom.id package).base := by
    change (corePermutationTotal swap12).comp (corePermutationTotal swap12) =
      PackageTotalHom.id core
    rw [corePermutationTotal_comp, swap12_square]
    exact corePermutationTotal_refl
  apply GeometryTotalHom.ext
  · exact baseSquare
  · apply geometryHom_heq_of_base_eq _ _ baseSquare
    · exact RingHom.id_comp _
    · apply heq_of_eq
      funext W support
      change localSupportPermutation swap12 W
          (localSupportPermutation swap12 W support) = support
      classical
      by_cases hW : W.ctx = baseContext
      · cases W with
        | mk Wctx =>
            dsimp at hW ⊢
            subst Wctx
            simpa only [localSupportPermutation_base] using
              congrArg (fun e : Equiv.Perm (Fin 4) => e support) swap12_square
      · simp [localSupportPermutation, hW]
    · apply heq_of_eq
      funext W axis
      change localAxisPermutation swap12 W
          (localAxisPermutation swap12 W axis) = axis
      classical
      by_cases hW : W.ctx = baseContext
      · cases W with
        | mk Wctx =>
            dsimp at hW ⊢
            subst Wctx
            simpa only [localAxisPermutation_base] using
              congrArg (fun e : Equiv.Perm (Fin 4) => e axis) swap12_square
      · simp [localAxisPermutation, hW]
    · apply heq_of_eq
      funext W observable
      change localObservablePermutation swap12 W
          (localObservablePermutation swap12 W observable) = observable
      classical
      by_cases hW : W.ctx = baseContext
      · cases W with
        | mk Wctx =>
            dsimp at hW ⊢
            subst Wctx
            simpa only [localObservablePermutation_base] using
              congrArg (fun e : Equiv.Perm (Fin 4) => e observable) swap12_square
      · simp [localObservablePermutation, hW]

/-- Geometry automorphism for the horizontal transposition. -/
noncomputable def swap01Iso : Aut package where
  hom := swap01Total
  inv := swap01Total
  hom_inv_id := swap01Total_square
  inv_hom_id := swap01Total_square

/-- Geometry automorphism for the comparator transposition. -/
noncomputable def swap12Iso : Aut package where
  hom := swap12Total
  inv := swap12Total
  hom_inv_id := swap12Total_square
  inv_hom_id := swap12Total_square

/-- Composite-fiber automorphism carried by the horizontal edge. -/
noncomputable def compositeSwap01 : CompositeFiberAut package :=
  ⟨swap01Iso, rfl⟩

/-- Composite-fiber automorphism carried by the authored comparator. -/
noncomputable def compositeSwap12 : CompositeFiberAut package :=
  ⟨swap12Iso, rfl⟩

/-- The horizontal geometry action is nonidentity. -/
theorem swap01Total_ne_id :
    swap01Total ≠ GeometryTotalHom.id package := by
  intro equality
  have axisEquality := congrArg
    (fun total : GeometryTotalHom package package =>
      total.base.upper.axisMap (0 : Fin 4)) equality
  change (1 : Fin 4) = 0 at axisEquality
  exact (by decide : (1 : Fin 4) ≠ 0) axisEquality

/-- The horizontal composite-fiber automorphism is nontrivial. -/
theorem compositeSwap01_ne_one : compositeSwap01 ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism : CompositeFiberAut package =>
      (CompositeFiberAut.hom automorphism).base.upper.axisMap (0 : Fin 4))
    equality
  change (1 : Fin 4) = 0 at axisEquality
  exact (by decide : (1 : Fin 4) ≠ 0) axisEquality

/-- The authored comparator automorphism is nontrivial. -/
theorem compositeSwap12_ne_one : compositeSwap12 ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism : CompositeFiberAut package =>
      (CompositeFiberAut.hom automorphism).base.upper.axisMap (1 : Fin 4))
    equality
  change (2 : Fin 4) = 1 at axisEquality
  exact (by decide : (2 : Fin 4) ≠ 1) axisEquality

/-! ## One-vertex source presentation and actual core-fiber diagram -/

/-- The unique nonidentity edge of the decision presentation. -/
inductive DecisionEdge
  | twist
  deriving DecidableEq, Fintype

/-- The unique comparison two-cell of the decision presentation. -/
inductive DecisionCell
  | comparison
  deriving DecidableEq, Fintype

/-- Empty path at the unique decision vertex. -/
def nilPath : PresentedPath (fun _ _ : PUnit => DecisionEdge)
    PUnit.unit PUnit.unit :=
  .nil PUnit.unit

/-- One-edge path carrying the horizontal transposition. -/
def twistPath : PresentedPath (fun _ _ : PUnit => DecisionEdge)
    PUnit.unit PUnit.unit :=
  .cons .twist (.nil PUnit.unit)

/-- Root-connected one-vertex finite presentation with one edge and cell. -/
abbrev presentation : FiniteTransportPresentation where
  Vertex := PUnit
  vertexFintype := inferInstance
  Edge := fun _ _ => DecisionEdge
  edgeFintype := fun _ _ => inferInstance
  TwoCell := DecisionCell
  twoCellFintype := inferInstance
  twoSource := fun _ => PUnit.unit
  twoTarget := fun _ => PUnit.unit
  twoLeft := fun _ => nilPath
  twoRight := fun _ => twistPath
  ThreeCell := PEmpty
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell
  threeTarget := fun cell => nomatch cell
  threeStart := fun cell => nomatch cell
  threeFinish := fun cell => nomatch cell
  threeLeft := fun cell => nomatch cell
  threeRight := fun cell => nomatch cell

/-- Independent strong-cartesian qualification of the horizontal geometry
edge. -/
theorem swap01_geometryStrong :
    (geometryProjection FiniteModel.carrier).IsStronglyCocartesian
      swap01Total.base swap01Total := by
  letI : (geometryProjection FiniteModel.carrier).IsHomLift
      swap01Total.base swap01Iso.hom := by
    change (geometryProjection FiniteModel.carrier).IsHomLift
      ((geometryProjection FiniteModel.carrier).map swap01Iso.hom)
      swap01Iso.hom
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_iso
    (geometryProjection FiniteModel.carrier) swap01Total.base swap01Iso

/-- Independent strong-cartesian qualification of the horizontal core edge. -/
theorem swap01_coreStrong :
    (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      swap01Total.base.base swap01Total.base := by
  letI : (packageProjection FiniteModel.carrier).IsHomLift
      swap01Total.base.base
      (compositeFiberPushforward package compositeSwap01).1.hom := by
    change (packageProjection FiniteModel.carrier).IsHomLift
      ((packageProjection FiniteModel.carrier).map
        (compositeFiberPushforward package compositeSwap01).1.hom)
      (compositeFiberPushforward package compositeSwap01).1.hom
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_iso
    (packageProjection FiniteModel.carrier) swap01Total.base.base
      (compositeFiberPushforward package compositeSwap01).1

/-- Strong finite lift data generated by the horizontal automorphism. -/
noncomputable abbrev liftData :
    TwoLayerLiftData presentation FiniteModel.carrier where
  geometry _ := package
  edgeLift _ := swap01Total
  edgeGeometryStrong _ := swap01_geometryStrong
  edgeCoreStrong _ := swap01_coreStrong

/-- Every generated path lift lies over its pointed core base. -/
theorem pathLift_pointed_base
    {i j : presentation.Vertex} (path : presentation.Path i j) :
    (liftData.pathLift path).base.base = ExtInstHom.id (packagePoint core) := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      change swap01Total.base.base.comp
        (liftData.pathLift tail).base.base = _
      rw [inductionHypothesis]
      rfl

/-- Core-fiber path map extracted from the strong lift. -/
noncomputable def corePathMap
    {i j : presentation.Vertex} (path : presentation.Path i j) :
    coreObject ⟶ coreObject := by
  letI : (packageProjection FiniteModel.carrier).IsHomLift
      (𝟙 activeReverseTargetPoint) (liftData.pathLift path).base :=
    CategoryTheory.IsHomLift.of_commsq
      (packageProjection FiniteModel.carrier)
      (𝟙 activeReverseTargetPoint) (liftData.pathLift path).base
      coreObject.2 coreObject.2 (by
        simpa only [coreObject] using pathLift_pointed_base path)
  exact ⟨(liftData.pathLift path).base, inferInstance⟩

/-- Actual one-object source fiber diagram generated by path composition. -/
noncomputable def sourceFiberDiagram :
    PresentedPathCategory presentation ⥤ CoreFiber activeReverseTargetPoint where
  obj _ := coreObject
  map path := corePathMap path
  map_id vertex := by
    apply Subtype.ext
    rfl
  map_comp first second := by
    apply Subtype.ext
    simpa only [corePathMap] using congrArg
      (fun hom => hom.base) (liftData.pathLift_append first second)

/-- Fixed source geometry at the unique presentation vertex. -/
noncomputable abbrev sourceGeometry (_ : presentation.Vertex) :
    FixedCoefficientGeometryAt core Int where
  geometry := geometry
  raw := raw

/-- Certificate-free authored two-layer transport with its single comparator. -/
noncomputable def sourceTransport : FixedCoefficientTwoLayerTransportOver
    presentation sourceFiberDiagram Int sourceGeometry where
  edgeLift _ := swap01Total
  edge_base edge := by
    cases edge
    rfl
  edgeGeometryStrong _ := swap01_geometryStrong
  edgeCoreStrong _ := swap01_coreStrong
  twoCellBase cell := by
    cases cell
    rfl
  comparator _ := compositeSwap12
  edge_coefficient_id edge := by
    cases edge
    rfl
  comparator_coefficient_id cell := by
    cases cell
    rfl

/-- Complete named compatible problem data over the active reverse context. -/
noncomputable def problemData : UpperGeometryCompatibleProblemInputData
    context presentation (CommRingCat.of Int) where
  root := PUnit.unit
  rootPath := fun _ => .nil PUnit.unit
  sourceFiberDiagram := sourceFiberDiagram
  sourceGeometry := sourceGeometry
  sourceTransport := sourceTransport

/-- Named finite compatible upper-refinement problem. -/
noncomputable def problem : UpperGeometryCompatibleProblemInput context where
  presentation := presentation
  coefficient := CommRingCat.of Int
  data := problemData

/-- The theorem-generated solution of the named problem. -/
noncomputable def solution :
    GeometryCompatibleUpperRefinementBCSolution problem.data :=
  problem.data.generatedGeometryCompatibleUpperRefinementBCSolution

/-- The canonical companion solution over the same named problem data. -/
noncomputable def canonicalCompanionSolution :
    CanonicalUpperRefinementBCSolution problem.data :=
  problem.data.canonicalCompanionUpperRefinementBCSolution

/-! ## Concrete horizontal and two-cell firing -/

/-- The card-named active reverse refinement moves a concrete Atom and is
therefore genuinely lax rather than an exact identity fixture. -/
theorem active_refinement_fires :
    (context.configuration.pulledRefinementAt context.source).doctrineHom.atomMap
        FiniteModel.FiniteAtom.componentA ≠
      FiniteModel.FiniteAtom.componentA :=
  activeReverse_pulledRefinement_atom_nonidentity

/-- The active refinement context is outside the exact comparison image. -/
theorem context_outside_exact_image :
    ¬ ∃ exact : ExactDoctrineHom FiniteModel.extractionDoctrine
        refinementTargetDoctrine,
      (doctrineToRefinement FiniteModel.carrier).map exact =
        context.configuration.refinement := by
  simpa [context, activeReverseContext, activeReverseConfiguration] using
    activeReverse_outside_exact_image

/-- Every presentation vertex is connected to the chosen root. -/
theorem problem_root_connected (i : problem.presentation.Vertex) :
    Nonempty (problem.presentation.Path problem.data.root i) :=
  ⟨problem.data.rootPath i⟩

/-- The horizontal edge also fires on the core signature axis. -/
theorem source_edge_axis_fires :
    (sourceTransport.edgeLift (i := PUnit.unit) (j := PUnit.unit)
      DecisionEdge.twist).base.upper.axisMap (0 : Fin 4) =
      (1 : Fin 4) := rfl

/-- The horizontal source edge moves an actual local support value. -/
theorem source_edge_local_support_fires :
    (sourceTransport.edgeLift (i := PUnit.unit) (j := PUnit.unit)
      DecisionEdge.twist).geometry.supportComp
        (⟨baseContext⟩ : package.site.category) (0 : Fin 4) = (1 : Fin 4) := by
  simp [sourceTransport, swap01Total, geometryPermutationHom,
    localSupportPermutation_base, swap01]

/-- The horizontal source edge moves an actual local axis value. -/
theorem source_edge_local_axis_fires :
    (sourceTransport.edgeLift (i := PUnit.unit) (j := PUnit.unit)
      DecisionEdge.twist).geometry.axisComp
        (⟨baseContext⟩ : package.site.category) (0 : Fin 4) = (1 : Fin 4) := by
  simp [sourceTransport, swap01Total, geometryPermutationHom,
    localAxisPermutation_base, swap01]

/-- The horizontal source edge moves an actual local observable value. -/
theorem source_edge_local_observable_fires :
    (sourceTransport.edgeLift (i := PUnit.unit) (j := PUnit.unit)
      DecisionEdge.twist).geometry.observableComp
        (⟨baseContext⟩ : package.site.category) (0 : Fin 4) = (1 : Fin 4) := by
  simp [sourceTransport, swap01Total, geometryPermutationHom,
    localObservablePermutation_base, swap01]

/-- The full horizontal edge is not the identity geometry hom. -/
theorem source_edge_ne_identity :
    sourceTransport.edgeLift (i := PUnit.unit) (j := PUnit.unit)
      DecisionEdge.twist ≠ GeometryTotalHom.id package :=
  swap01Total_ne_id

/-- The authored comparator also fires on the core signature axis. -/
theorem authored_comparator_axis_fires :
    (CompositeFiberAut.hom
      (sourceTransport.comparator DecisionCell.comparison)).base.upper.axisMap
        (1 : Fin 4) = (2 : Fin 4) := rfl

/-- The authored two-cell comparator moves an actual local support value. -/
theorem authored_comparator_local_support_fires :
    (CompositeFiberAut.hom
      (sourceTransport.comparator DecisionCell.comparison)).geometry.supportComp
        (⟨baseContext⟩ : package.site.category) (1 : Fin 4) = (2 : Fin 4) := by
  simp [sourceTransport, compositeSwap12, CompositeFiberAut.hom,
    swap12Iso, swap12Total,
    geometryPermutationHom, localSupportPermutation_base, swap12]

/-- The authored two-cell comparator moves an actual local axis value. -/
theorem authored_comparator_local_axis_fires :
    (CompositeFiberAut.hom
      (sourceTransport.comparator DecisionCell.comparison)).geometry.axisComp
        (⟨baseContext⟩ : package.site.category) (1 : Fin 4) = (2 : Fin 4) := by
  simp [sourceTransport, compositeSwap12, CompositeFiberAut.hom,
    swap12Iso, swap12Total,
    geometryPermutationHom, localAxisPermutation_base, swap12]

/-- The authored two-cell comparator moves an actual local observable value. -/
theorem authored_comparator_local_observable_fires :
    (CompositeFiberAut.hom
      (sourceTransport.comparator DecisionCell.comparison)).geometry.observableComp
        (⟨baseContext⟩ : package.site.category) (1 : Fin 4) = (2 : Fin 4) := by
  simp [sourceTransport, compositeSwap12, CompositeFiberAut.hom,
    swap12Iso, swap12Total,
    geometryPermutationHom, localObservablePermutation_base, swap12]

/-- The authored comparator is a nontrivial composite-fiber automorphism. -/
theorem authored_comparator_ne_one :
    sourceTransport.comparator DecisionCell.comparison ≠ 1 :=
  compositeSwap12_ne_one

/-- Total support-carrier map of a refinement geometry morphism. -/
noncomputable def refinementSupportSigmaMap
    {G H : GeometryPackage FiniteModel.carrier}
    (F : RefinementGeometryHom G H) :
    (Σ W : G.site.category, W.ctx.Support) →
      (Σ W : H.site.category, W.ctx.Support)
  | ⟨W, support⟩ =>
      ⟨refinementGeometryContextForward F.base W,
        F.geometry.supportComp W support⟩

/-- Total support-carrier maps respect refinement-geometry composition. -/
theorem refinementSupportSigmaMap_comp
    {G H K : GeometryPackage FiniteModel.carrier}
    (F : RefinementGeometryHom G H) (T : RefinementGeometryHom H K)
    (value : Σ W : G.site.category, W.ctx.Support) :
    refinementSupportSigmaMap (F.comp T) value =
      refinementSupportSigmaMap T (refinementSupportSigmaMap F value) := by
  rfl

/-- Total axis-carrier map of a refinement geometry morphism. -/
noncomputable def refinementAxisSigmaMap
    {G H : GeometryPackage FiniteModel.carrier}
    (F : RefinementGeometryHom G H) :
    (Σ W : G.site.category, W.ctx.Axis) →
      (Σ W : H.site.category, W.ctx.Axis)
  | ⟨W, axis⟩ =>
      ⟨refinementGeometryContextForward F.base W,
        F.geometry.axisComp W axis⟩

/-- Total axis-carrier maps respect refinement-geometry composition. -/
theorem refinementAxisSigmaMap_comp
    {G H K : GeometryPackage FiniteModel.carrier}
    (F : RefinementGeometryHom G H) (T : RefinementGeometryHom H K)
    (value : Σ W : G.site.category, W.ctx.Axis) :
    refinementAxisSigmaMap (F.comp T) value =
      refinementAxisSigmaMap T (refinementAxisSigmaMap F value) := by
  rfl

/-- Total observable-carrier map of a refinement geometry morphism. -/
noncomputable def refinementObservableSigmaMap
    {G H : GeometryPackage FiniteModel.carrier}
    (F : RefinementGeometryHom G H) :
    (Σ W : G.site.category, W.ctx.Observable) →
      (Σ W : H.site.category, W.ctx.Observable)
  | ⟨W, observable⟩ =>
      ⟨refinementGeometryContextForward F.base W,
        F.geometry.observableComp W observable⟩

/-- Total observable-carrier maps respect refinement-geometry composition. -/
theorem refinementObservableSigmaMap_comp
    {G H K : GeometryPackage FiniteModel.carrier}
    (F : RefinementGeometryHom G H) (T : RefinementGeometryHom H K)
    (value : Σ W : G.site.category, W.ctx.Observable) :
    refinementObservableSigmaMap (F.comp T) value =
      refinementObservableSigmaMap T
        (refinementObservableSigmaMap F value) := by
  rfl

/-- The route realization equivalence at the unique decision vertex. -/
noncomputable abbrev generatedBaseRealizationExact :=
  problem.data.generatedBaseRouteRealizationExactAt PUnit.unit

/-- The literal base-route support map is the realization-exact forward
supply used to construct that route. -/
theorem generatedBaseRouteLeg_supportComp_eq_homSupply
    (W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category)
    (support : W.ctx.Support) :
    (problem.data.generatedBaseRouteLegAt PUnit.unit).geometry.supportComp
        W support =
      generatedBaseRealizationExact.homSupply.supportComp W support := by
  rfl

/-- The literal base-route axis map is the realization-exact forward supply. -/
theorem generatedBaseRouteLeg_axisComp_eq_homSupply
    (W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category)
    (axis : W.ctx.Axis) :
    (problem.data.generatedBaseRouteLegAt PUnit.unit).geometry.axisComp W axis =
      generatedBaseRealizationExact.homSupply.axisComp W axis := by
  rfl

/-- The literal base-route observable map is the realization-exact forward
supply. -/
theorem generatedBaseRouteLeg_observableComp_eq_homSupply
    (W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category)
    (observable : W.ctx.Observable) :
    (problem.data.generatedBaseRouteLegAt PUnit.unit).geometry.observableComp
        W observable =
      generatedBaseRealizationExact.homSupply.observableComp W observable := by
  rfl

/-- On total support carriers, the literal route leg is the reviewed
realization-exact equivalence. -/
theorem generatedBaseRoute_supportSigmaMap_eq :
    refinementSupportSigmaMap
        (problem.data.generatedBaseRouteLegAt PUnit.unit) =
      generatedBaseRealizationExact.supportSigmaEquiv := by
  have hupper :=
    problem.data.generatedBaseRouteUpperEquivalenceAt_forward_eq PUnit.unit
  cases hupper
  funext value
  rcases value with ⟨W, support⟩
  apply Sigma.ext
  · rfl
  · exact heq_of_eq
      (generatedBaseRouteLeg_supportComp_eq_homSupply W support)

/-- On total axis carriers, the literal route leg is the reviewed
realization-exact equivalence. -/
theorem generatedBaseRoute_axisSigmaMap_eq :
    refinementAxisSigmaMap
        (problem.data.generatedBaseRouteLegAt PUnit.unit) =
      generatedBaseRealizationExact.axisSigmaEquiv := by
  have hupper :=
    problem.data.generatedBaseRouteUpperEquivalenceAt_forward_eq PUnit.unit
  cases hupper
  funext value
  rcases value with ⟨W, axis⟩
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (generatedBaseRouteLeg_axisComp_eq_homSupply W axis)

/-- On total observable carriers, the literal route leg is the reviewed
realization-exact equivalence. -/
theorem generatedBaseRoute_observableSigmaMap_eq :
    refinementObservableSigmaMap
        (problem.data.generatedBaseRouteLegAt PUnit.unit) =
      generatedBaseRealizationExact.observableSigmaEquiv := by
  have hupper :=
    problem.data.generatedBaseRouteUpperEquivalenceAt_forward_eq PUnit.unit
  cases hupper
  funext value
  rcases value with ⟨W, observable⟩
  apply Sigma.ext
  · rfl
  · exact heq_of_eq
      (generatedBaseRouteLeg_observableComp_eq_homSupply W observable)

/-- The generated support value corresponding to a concrete source value. -/
noncomputable def generatedBaseSupportValue (support : Fin 4) :
    Σ W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category,
      W.ctx.Support :=
  (generatedBaseRealizationExact.supportSigmaEquiv).symm
    ⟨(⟨baseContext⟩ : package.site.category), support⟩

/-- The generated axis value corresponding to a concrete source value. -/
noncomputable def generatedBaseAxisValue (axis : Fin 4) :
    Σ W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category,
      W.ctx.Axis :=
  (generatedBaseRealizationExact.axisSigmaEquiv).symm
    ⟨(⟨baseContext⟩ : package.site.category), axis⟩

/-- The generated observable value corresponding to a concrete source value. -/
noncomputable def generatedBaseObservableValue (observable : Fin 4) :
    Σ W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category,
      W.ctx.Observable :=
  (generatedBaseRealizationExact.observableSigmaEquiv).symm
    ⟨(⟨baseContext⟩ : package.site.category), observable⟩

/-- The literal generated route leg sends the generated support value back to
its named concrete source value. -/
theorem generatedBaseRoute_support_value (support : Fin 4) :
    refinementSupportSigmaMap
        (problem.data.generatedBaseRouteLegAt PUnit.unit)
        (generatedBaseSupportValue support) =
      ⟨(⟨baseContext⟩ : package.site.category), support⟩ := by
  change
    (⟨refinementGeometryContextForward
        (problem.data.generatedBaseRouteLegAt PUnit.unit).base
        (generatedBaseSupportValue support).1,
      (problem.data.generatedBaseRouteLegAt PUnit.unit).geometry.supportComp
        (generatedBaseSupportValue support).1
        (generatedBaseSupportValue support).2⟩ :
      Σ W : package.site.category, W.ctx.Support) = _
  rw [generatedBaseRouteLeg_supportComp_eq_homSupply]
  change
    (⟨(upperCoreContextFunctor
        (problem.data.generatedBaseRouteLegAt PUnit.unit).base.upper).obj
        (generatedBaseSupportValue support).1,
      generatedBaseRealizationExact.homSupply.supportComp
        (generatedBaseSupportValue support).1
        (generatedBaseSupportValue support).2⟩ :
      Σ W : package.site.category, W.ctx.Support) = _
  have hupper :=
    problem.data.generatedBaseRouteUpperEquivalenceAt_forward_eq PUnit.unit
  cases hupper
  exact Equiv.apply_symm_apply generatedBaseRealizationExact.supportSigmaEquiv
    (⟨(⟨baseContext⟩ : package.site.category), support⟩)

/-- The literal generated route leg sends the generated axis value back to
its named concrete source value. -/
theorem generatedBaseRoute_axis_value (axis : Fin 4) :
    refinementAxisSigmaMap
        (problem.data.generatedBaseRouteLegAt PUnit.unit)
        (generatedBaseAxisValue axis) =
      ⟨(⟨baseContext⟩ : package.site.category), axis⟩ := by
  rw [generatedBaseRoute_axisSigmaMap_eq]
  exact Equiv.apply_symm_apply generatedBaseRealizationExact.axisSigmaEquiv
    (⟨(⟨baseContext⟩ : package.site.category), axis⟩)

/-- The literal generated route leg sends the generated observable value back
to its named concrete source value. -/
theorem generatedBaseRoute_observable_value (observable : Fin 4) :
    refinementObservableSigmaMap
        (problem.data.generatedBaseRouteLegAt PUnit.unit)
        (generatedBaseObservableValue observable) =
      ⟨(⟨baseContext⟩ : package.site.category), observable⟩ := by
  rw [generatedBaseRoute_observableSigmaMap_eq]
  exact Equiv.apply_symm_apply
    generatedBaseRealizationExact.observableSigmaEquiv
    (⟨(⟨baseContext⟩ : package.site.category), observable⟩)

/-- The authored comparator sends the named total support value one to two. -/
theorem authoredComparator_support_value :
    refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (sourceTransport.comparator DecisionCell.comparison)))
        ⟨(⟨baseContext⟩ : package.site.category), (1 : Fin 4)⟩ =
      ⟨(⟨baseContext⟩ : package.site.category), (2 : Fin 4)⟩ := by
  apply Sigma.ext
  · rfl
  · exact heq_of_eq authored_comparator_local_support_fires

/-- The authored comparator sends the named total axis value one to two. -/
theorem authoredComparator_axis_value :
    refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (sourceTransport.comparator DecisionCell.comparison)))
        ⟨(⟨baseContext⟩ : package.site.category), (1 : Fin 4)⟩ =
      ⟨(⟨baseContext⟩ : package.site.category), (2 : Fin 4)⟩ := by
  apply Sigma.ext
  · rfl
  · exact heq_of_eq authored_comparator_local_axis_fires

/-- The authored comparator sends the named total observable value one to
two. -/
theorem authoredComparator_observable_value :
    refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (sourceTransport.comparator DecisionCell.comparison)))
        ⟨(⟨baseContext⟩ : package.site.category), (1 : Fin 4)⟩ =
      ⟨(⟨baseContext⟩ : package.site.category), (2 : Fin 4)⟩ := by
  apply Sigma.ext
  · rfl
  · exact heq_of_eq authored_comparator_local_observable_fires

/-- The Cartesian-generated comparator itself sends the generated local
support value corresponding to one to the value corresponding to two. -/
theorem generated_base_comparator_local_support_fires :
    refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteComparator
              DecisionCell.comparison)))
        (generatedBaseSupportValue (1 : Fin 4)) =
      generatedBaseSupportValue (2 : Fin 4) := by
  apply generatedBaseRealizationExact.supportSigmaEquiv.injective
  rw [← generatedBaseRoute_supportSigmaMap_eq]
  rw [← refinementSupportSigmaMap_comp]
  have hfac :=
    problem.data.generatedBaseRouteComparator_fac DecisionCell.comparison
  change
    ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
      (CompositeFiberAut.hom
        (problem.data.generatedBaseRouteComparator
          DecisionCell.comparison))).comp
        (problem.data.generatedBaseRouteLegAt PUnit.unit) =
      (problem.data.generatedBaseRouteLegAt PUnit.unit).comp
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (sourceTransport.comparator DecisionCell.comparison))) at hfac
  rw [hfac]
  rw [refinementSupportSigmaMap_comp]
  rw [generatedBaseRoute_support_value]
  rw [authoredComparator_support_value]
  rw [generatedBaseRoute_support_value]

/-- The Cartesian-generated comparator moves an actual generated support
value, not merely a core signature coordinate. -/
theorem generated_base_comparator_local_support_ne_input :
    refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteComparator
              DecisionCell.comparison)))
        (generatedBaseSupportValue (1 : Fin 4)) ≠
      generatedBaseSupportValue (1 : Fin 4) := by
  rw [generated_base_comparator_local_support_fires]
  intro equality
  have imageEquality := congrArg
    generatedBaseRealizationExact.supportSigmaEquiv equality
  have pairEquality :
      (⟨(⟨baseContext⟩ : package.site.category), (2 : Fin 4)⟩ :
        Σ W : package.site.category, W.ctx.Support) =
      ⟨(⟨baseContext⟩ : package.site.category), (1 : Fin 4)⟩ := by
    simpa only [generatedBaseSupportValue, Equiv.apply_symm_apply] using
      imageEquality
  have concreteEquality : (2 : Fin 4) = (1 : Fin 4) :=
    eq_of_heq (Sigma.ext_iff.mp pairEquality).2
  exact (by decide : (2 : Fin 4) ≠ 1) concreteEquality

/-- The Cartesian-generated comparator itself sends the generated local axis
value corresponding to one to the value corresponding to two. -/
theorem generated_base_comparator_local_axis_fires :
    refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteComparator
              DecisionCell.comparison)))
        (generatedBaseAxisValue (1 : Fin 4)) =
      generatedBaseAxisValue (2 : Fin 4) := by
  apply generatedBaseRealizationExact.axisSigmaEquiv.injective
  rw [← generatedBaseRoute_axisSigmaMap_eq]
  rw [← refinementAxisSigmaMap_comp]
  have hfac :=
    problem.data.generatedBaseRouteComparator_fac DecisionCell.comparison
  change
    ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
      (CompositeFiberAut.hom
        (problem.data.generatedBaseRouteComparator
          DecisionCell.comparison))).comp
        (problem.data.generatedBaseRouteLegAt PUnit.unit) =
      (problem.data.generatedBaseRouteLegAt PUnit.unit).comp
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (sourceTransport.comparator DecisionCell.comparison))) at hfac
  rw [hfac]
  rw [refinementAxisSigmaMap_comp]
  rw [generatedBaseRoute_axis_value]
  rw [authoredComparator_axis_value]
  rw [generatedBaseRoute_axis_value]

/-- The Cartesian-generated comparator moves an actual generated axis value,
not merely a core signature coordinate. -/
theorem generated_base_comparator_local_axis_ne_input :
    refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteComparator
              DecisionCell.comparison)))
        (generatedBaseAxisValue (1 : Fin 4)) ≠
      generatedBaseAxisValue (1 : Fin 4) := by
  rw [generated_base_comparator_local_axis_fires]
  intro equality
  have imageEquality := congrArg
    generatedBaseRealizationExact.axisSigmaEquiv equality
  have pairEquality :
      (⟨(⟨baseContext⟩ : package.site.category), (2 : Fin 4)⟩ :
        Σ W : package.site.category, W.ctx.Axis) =
      ⟨(⟨baseContext⟩ : package.site.category), (1 : Fin 4)⟩ := by
    simpa only [generatedBaseAxisValue, Equiv.apply_symm_apply] using
      imageEquality
  have concreteEquality : (2 : Fin 4) = (1 : Fin 4) :=
    eq_of_heq (Sigma.ext_iff.mp pairEquality).2
  exact (by decide : (2 : Fin 4) ≠ 1) concreteEquality

/-- The Cartesian-generated comparator sends the generated local observable
value corresponding to one to the value corresponding to two. -/
theorem generated_base_comparator_local_observable_fires :
    refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteComparator
              DecisionCell.comparison)))
        (generatedBaseObservableValue (1 : Fin 4)) =
      generatedBaseObservableValue (2 : Fin 4) := by
  apply generatedBaseRealizationExact.observableSigmaEquiv.injective
  rw [← generatedBaseRoute_observableSigmaMap_eq]
  rw [← refinementObservableSigmaMap_comp]
  have hfac :=
    problem.data.generatedBaseRouteComparator_fac DecisionCell.comparison
  change
    ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
      (CompositeFiberAut.hom
        (problem.data.generatedBaseRouteComparator
          DecisionCell.comparison))).comp
        (problem.data.generatedBaseRouteLegAt PUnit.unit) =
      (problem.data.generatedBaseRouteLegAt PUnit.unit).comp
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (sourceTransport.comparator DecisionCell.comparison))) at hfac
  rw [hfac]
  rw [refinementObservableSigmaMap_comp]
  rw [generatedBaseRoute_observable_value]
  rw [authoredComparator_observable_value]
  rw [generatedBaseRoute_observable_value]

/-- The Cartesian-generated comparator moves an actual generated observable
value, not merely a core signature coordinate. -/
theorem generated_base_comparator_local_observable_ne_input :
    refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteComparator
              DecisionCell.comparison)))
        (generatedBaseObservableValue (1 : Fin 4)) ≠
      generatedBaseObservableValue (1 : Fin 4) := by
  rw [generated_base_comparator_local_observable_fires]
  intro equality
  have imageEquality := congrArg
    generatedBaseRealizationExact.observableSigmaEquiv equality
  have pairEquality :
      (⟨(⟨baseContext⟩ : package.site.category), (2 : Fin 4)⟩ :
        Σ W : package.site.category, W.ctx.Observable) =
      ⟨(⟨baseContext⟩ : package.site.category), (1 : Fin 4)⟩ := by
    simpa only [generatedBaseObservableValue, Equiv.apply_symm_apply] using
      imageEquality
  have concreteEquality : (2 : Fin 4) = (1 : Fin 4) :=
    eq_of_heq (Sigma.ext_iff.mp pairEquality).2
  exact (by decide : (2 : Fin 4) ≠ 1) concreteEquality

/-- The generated comparator's core signature axis evaluation, retained as an
independent route-level check alongside the local carrier evaluations. -/
theorem generated_base_comparator_axis_fires :
    (CompositeFiberAut.hom
      (problem.data.generatedBaseRouteComparator DecisionCell.comparison)).base.upper.axisMap
        (1 : Fin 4) = (2 : Fin 4) := by
  have factorization :=
    problem.data.generatedBaseRouteComparator_fac DecisionCell.comparison
  have axisEquality := congrArg
    (fun hom : RefinementGeometryHom
        (problem.data.generatedBaseRouteGeometryAt PUnit.unit)
        (problem.data.sourceGeometry PUnit.unit).package =>
      hom.base.upper.axisMap (1 : Fin 4)) factorization
  simpa [problem, problemData, sourceTransport, sourceGeometry,
    sourceFiberDiagram, corePathMap, liftData,
    UpperGeometryCompatibleProblemInputData.generatedBaseRouteComparator,
    UpperGeometryCompatibleProblemInputData.generatedBaseGeometryComparatorCandidateAt,
    RefinementGeometryHom.comp, RefinementPackageHom.comp] using axisEquality

/-- The generated pullback of the horizontal automorphism fires on axis zero. -/
theorem generated_base_swap01_axis_fires :
    (CompositeFiberAut.hom
      (problem.data.generatedBaseCompositeFiberAutAt PUnit.unit
        compositeSwap01)).base.upper.axisMap (0 : Fin 4) =
      (1 : Fin 4) := by
  have factorization := problem.data.generatedBaseCompositeFiberAutAt_fac
    PUnit.unit compositeSwap01
  have axisEquality := congrArg
    (fun hom : RefinementGeometryHom
        (problem.data.generatedBaseRouteGeometryAt PUnit.unit)
        (problem.data.sourceGeometry PUnit.unit).package =>
      hom.base.upper.axisMap (0 : Fin 4)) factorization
  simpa [problem, problemData, sourceTransport, sourceGeometry,
    sourceFiberDiagram, corePathMap, liftData,
    UpperGeometryCompatibleProblemInputData.generatedBaseGeometryComparatorCandidateAt,
    RefinementGeometryHom.comp, RefinementPackageHom.comp] using axisEquality

/-- The generated pullback of the comparator automorphism fires on axis one. -/
theorem generated_base_swap12_axis_fires :
    (CompositeFiberAut.hom
      (problem.data.generatedBaseCompositeFiberAutAt PUnit.unit
        compositeSwap12)).base.upper.axisMap (1 : Fin 4) =
      (2 : Fin 4) := by
  simpa [UpperGeometryCompatibleProblemInputData.generatedBaseRouteComparator,
    problem, problemData, sourceTransport] using
    generated_base_comparator_axis_fires

/-- The Cartesian-generated comparator is nontrivial. -/
theorem generated_base_comparator_ne_one :
    problem.data.generatedBaseRouteComparator DecisionCell.comparison ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism =>
      (CompositeFiberAut.hom automorphism).base.upper.axisMap (1 : Fin 4))
    equality
  change (CompositeFiberAut.hom
      (problem.data.generatedBaseRouteComparator DecisionCell.comparison)).base.upper.axisMap
        (1 : Fin 4) = (1 : Fin 4) at axisEquality
  rw [generated_base_comparator_axis_fires] at axisEquality
  exact (by decide : (2 : Fin 4) ≠ 1) axisEquality

/-- Underlying two-layer transport data used to derive raw cochains. -/
noncomputable abbrev sourceData : TwoLayerTransportData
    presentation FiniteModel.carrier :=
  sourceTransport.toTwoLayerTransportData

/-- The empty source path lifts to the identity. -/
theorem sourceData_pathLift_nil :
    sourceData.lift.pathLift (presentation.twoLeft DecisionCell.comparison) =
      GeometryTotalHom.id package := by
  rfl

/-- The twist source path lifts to the horizontal automorphism. -/
theorem sourceData_pathLift_twist :
    sourceData.lift.pathLift (presentation.twoRight DecisionCell.comparison) =
      swap01Total := by
  change swap01Total.comp (GeometryTotalHom.id package) = swap01Total
  exact @Category.comp_id
    (GeomReadCategory.{0, 0} FiniteModel.carrier)
    (geometryTotalCategory FiniteModel.carrier)
    package package swap01Total

/-- The empty upper path lift is the identity automorphism. -/
theorem sourceData_upperPathLift_nil :
    upperReselectedPathLift sourceData.lift 1
        (presentation.twoLeft DecisionCell.comparison) =
      GeometryTotalHom.id package := by
  rfl

/-- The twist upper path lift is the horizontal automorphism. -/
theorem sourceData_upperPathLift_twist :
    upperReselectedPathLift sourceData.lift 1
        (presentation.twoRight DecisionCell.comparison) = swap01Total := by
  change (swap01Total.comp (CompositeFiberAut.hom 1)).comp
      (GeometryTotalHom.id package) = swap01Total
  change (swap01Total.comp (GeometryTotalHom.id package)).comp
      (GeometryTotalHom.id package) = swap01Total
  calc
    (swap01Total.comp (GeometryTotalHom.id package)).comp
        (GeometryTotalHom.id package) =
        swap01Total.comp (GeometryTotalHom.id package) :=
      @Category.comp_id
        (GeomReadCategory.{0, 0} FiniteModel.carrier)
        (geometryTotalCategory FiniteModel.carrier)
        package package (swap01Total.comp (GeometryTotalHom.id package))
    _ = swap01Total :=
      @Category.comp_id
        (GeomReadCategory.{0, 0} FiniteModel.carrier)
        (geometryTotalCategory FiniteModel.carrier)
        package package swap01Total

/-- The canonical source comparator normalizes to the horizontal automorphism. -/
theorem sourceData_canonicalComparator_eq_swap01 :
    upperCanonicalTwoCellComparator sourceData 1 DecisionCell.comparison =
      compositeSwap01 := by
  let leftLift := upperReselectedPathLift sourceData.lift 1
    (presentation.twoLeft DecisionCell.comparison)
  letI : (crossStageProjection.{0, 0} FiniteModel.carrier).IsStronglyCocartesian
      leftLift.base.base leftLift :=
    (upperReselectLiftData sourceData.lift 1).pathLift_compositeStrong
      (presentation.twoLeft DecisionCell.comparison)
  apply CompositeFiberAut.ext_of_strong_fac leftLift
  calc
    leftLift.comp (CompositeFiberAut.hom
        (upperCanonicalTwoCellComparator sourceData 1 DecisionCell.comparison)) =
        upperReselectedPathLift sourceData.lift 1
          (presentation.twoRight DecisionCell.comparison) :=
      upperCanonicalTwoCellComparator_fac sourceData 1 DecisionCell.comparison
    _ = leftLift.comp (CompositeFiberAut.hom compositeSwap01) := by
      dsimp only [leftLift]
      rw [sourceData_upperPathLift_nil, sourceData_upperPathLift_twist]
      exact (@Category.id_comp
        (GeomReadCategory.{0, 0} FiniteModel.carrier)
        (geometryTotalCategory FiniteModel.carrier)
        package package swap01Total).symm

/-- The horizontal composite automorphism is its own inverse. -/
theorem compositeSwap01_inv : compositeSwap01⁻¹ = compositeSwap01 := by
  apply Subtype.ext
  apply Iso.ext
  rfl

/-- The derived source raw cochain fires on the concrete signature axis. -/
theorem source_raw_cochain_axis_fires :
    (CompositeFiberAut.hom
      (problem.data.compatibleSourceRawDefectCochain
        DecisionCell.comparison)).base.upper.axisMap (0 : Fin 4) =
      (2 : Fin 4) := by
  rw [UpperGeometryCompatibleProblemInputData.compatibleSourceRawDefectCochain_apply]
  unfold upperRawTwoCellDefect
  change (CompositeFiberAut.hom
      (sourceData.comparator DecisionCell.comparison *
        (upperCanonicalTwoCellComparator sourceData 1
          DecisionCell.comparison)⁻¹)).base.upper.axisMap (0 : Fin 4) =
    (2 : Fin 4)
  rw [sourceData_canonicalComparator_eq_swap01]
  rw [compositeSwap01_inv, compositeFiberAut_hom_mul]
  change (swap01Total.comp swap12Total).base.upper.axisMap (0 : Fin 4) =
    (2 : Fin 4)
  rfl

/-- The derived source raw cochain is the product of the two adjacent swaps. -/
theorem source_raw_cochain_eq :
    problem.data.compatibleSourceRawDefectCochain DecisionCell.comparison =
      compositeSwap12 * compositeSwap01⁻¹ := by
  rw [UpperGeometryCompatibleProblemInputData.compatibleSourceRawDefectCochain_apply]
  unfold upperRawTwoCellDefect
  change sourceData.comparator DecisionCell.comparison *
      (upperCanonicalTwoCellComparator sourceData 1
        DecisionCell.comparison)⁻¹ = _
  rw [sourceData_canonicalComparator_eq_swap01]
  rfl

/-- The derived source raw cochain is nontrivial. -/
theorem source_raw_cochain_ne_one :
    problem.data.compatibleSourceRawDefectCochain DecisionCell.comparison ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism =>
      (CompositeFiberAut.hom automorphism).base.upper.axisMap (0 : Fin 4))
    equality
  change (CompositeFiberAut.hom
      (problem.data.compatibleSourceRawDefectCochain
        DecisionCell.comparison)).base.upper.axisMap (0 : Fin 4) =
    (0 : Fin 4) at axisEquality
  rw [source_raw_cochain_axis_fires] at axisEquality
  exact (by decide : (2 : Fin 4) ≠ 0) axisEquality

/-- The generated base-route raw cochain fires on the concrete signature axis. -/
theorem generated_base_raw_cochain_axis_fires :
    (CompositeFiberAut.hom
      (problem.data.generatedBaseRouteRawDefectCochain
        DecisionCell.comparison)).base.upper.axisMap (0 : Fin 4) =
      (2 : Fin 4) := by
  rw [problem.data.generatedBaseRouteRawDefectCochain_eq_image]
  rw [source_raw_cochain_eq]
  rw [compositeSwap01_inv, map_mul, compositeFiberAut_hom_mul]
  change (CompositeFiberAut.hom
      (problem.data.generatedBaseCompositeFiberAutAt PUnit.unit
        compositeSwap12)).base.upper.axisMap
      ((CompositeFiberAut.hom
        (problem.data.generatedBaseCompositeFiberAutAt PUnit.unit
          compositeSwap01)).base.upper.axisMap (0 : Fin 4)) = (2 : Fin 4)
  rw [generated_base_swap01_axis_fires,
    generated_base_swap12_axis_fires]

/-- The generated base-route raw cochain is nontrivial. -/
theorem generated_base_raw_cochain_ne_one :
    problem.data.generatedBaseRouteRawDefectCochain
      DecisionCell.comparison ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism =>
      (CompositeFiberAut.hom automorphism).base.upper.axisMap (0 : Fin 4))
    equality
  change (CompositeFiberAut.hom
      (problem.data.generatedBaseRouteRawDefectCochain
        DecisionCell.comparison)).base.upper.axisMap (0 : Fin 4) =
    (0 : Fin 4) at axisEquality
  rw [generated_base_raw_cochain_axis_fires] at axisEquality
  exact (by decide : (2 : Fin 4) ≠ 0) axisEquality

/-- The horizontal source edge fixes coefficients. -/
theorem source_edge_coefficient_id :
    (sourceTransport.edgeLift (i := PUnit.unit) (j := PUnit.unit)
      DecisionEdge.twist).geometry.coefficientHom = RingHom.id Int :=
  sourceTransport.edge_coefficient_id DecisionEdge.twist

/-- The authored comparator fixes coefficients. -/
theorem authored_comparator_coefficient_id :
    (CompositeFiberAut.hom
      (sourceTransport.comparator DecisionCell.comparison)).geometry.coefficientHom =
      RingHom.id Int :=
  sourceTransport.comparator_coefficient_id DecisionCell.comparison

/-- The Cartesian-generated comparator fixes coefficients. -/
theorem generated_base_comparator_coefficient_id :
    (CompositeFiberAut.hom
      (problem.data.generatedBaseRouteFixedComparator
        DecisionCell.comparison)).geometry.coefficientHom = RingHom.id Int :=
  problem.data.generatedBaseRouteFixedComparator_coefficient_id
    DecisionCell.comparison

/-- The canonical companion maps to the generated solution under the existing
same-problem equivalence. -/
theorem canonical_companion_maps_to_solution :
    problem.data.canonicalGeneratedUpperRefinementBCSolutionEquiv
        canonicalCompanionSolution = solution :=
  problem.data.canonicalGeneratedUpperRefinementBCSolutionEquiv_companion

/-- The generic support-carrier conservativity theorem specializes to the
named generated solution. -/
theorem solution_support_carrier_conservative
    (W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category)
    (support : W.ctx.Support) :
    HEq ((solution.component PUnit.unit).geometry.supportComp W support) support :=
  problem.data.generatedGeometryCompatibleSolution_supportComp_heq
    PUnit.unit W support

/-- The generic axis-carrier conservativity theorem specializes to the named
generated solution. -/
theorem solution_axis_carrier_conservative
    (W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category)
    (axis : W.ctx.Axis) :
    HEq ((solution.component PUnit.unit).geometry.axisComp W axis) axis :=
  problem.data.generatedGeometryCompatibleSolution_axisComp_heq
    PUnit.unit W axis

/-- The generic observable-carrier conservativity theorem specializes to the
named generated solution. -/
theorem solution_observable_carrier_conservative
    (W : (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category)
    (observable : W.ctx.Observable) :
    HEq ((solution.component PUnit.unit).geometry.observableComp W observable)
      observable :=
  problem.data.generatedGeometryCompatibleSolution_observableComp_heq
    PUnit.unit W observable

/-- The generated solution's actual edge-naturality field specializes to the
named horizontal edge. -/
theorem solution_edge_naturality_fires :
    (problem.data.generatedBaseRouteGeometryEdge DecisionEdge.twist).comp
        (solution.component PUnit.unit) =
      (solution.component PUnit.unit).comp
        (problem.data.generatedPulledRouteGeometryEdge DecisionEdge.twist) :=
  solution.edge_naturality DecisionEdge.twist

/-- The generated solution's actual comparator-intertwining field specializes
to the named comparison cell. -/
theorem solution_comparator_intertwining_fires :
    (CompositeFiberAut.hom
      (problem.data.generatedBaseRouteComparator
        DecisionCell.comparison)).comp (solution.component PUnit.unit) =
      (solution.component PUnit.unit).comp
        (CompositeFiberAut.hom
          (problem.data.generatedPulledRouteComparator
            DecisionCell.comparison)) :=
  solution.comparator_intertwining DecisionCell.comparison

end UpperDecisionWitness

/-! ## Card-named decision artifacts -/

/-- Card-named active context for the positive decision fixture. -/
noncomputable abbrev upperDecisionContext :
    ActiveRefinementBCContext FiniteModel.carrier :=
  UpperDecisionWitness.context

/-- Card-named finite compatible decision problem. -/
noncomputable def upperDecisionProblem :
    UpperGeometryCompatibleProblemInput upperDecisionContext :=
  UpperDecisionWitness.problem

/-- Card-named theorem-generated decision solution. -/
noncomputable def upperDecisionSolution :
    UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution
      upperDecisionProblem.data :=
  upperDecisionProblem.data.generatedGeometryCompatibleUpperRefinementBCSolution

/-- Card-named canonical companion over the same decision problem. -/
noncomputable def upperDecisionCanonicalCompanionSolution :
    UpperGeometryCompatibleProblemInputData.CanonicalUpperRefinementBCSolution
      upperDecisionProblem.data :=
  upperDecisionProblem.data.canonicalCompanionUpperRefinementBCSolution

/-- The card-named companion maps to the card-named generated solution. -/
theorem upperDecisionCanonicalCompanion_maps_to_generated :
    upperDecisionProblem.data.canonicalGeneratedUpperRefinementBCSolutionEquiv
        upperDecisionCanonicalCompanionSolution = upperDecisionSolution :=
  upperDecisionProblem.data.canonicalGeneratedUpperRefinementBCSolutionEquiv_companion

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
