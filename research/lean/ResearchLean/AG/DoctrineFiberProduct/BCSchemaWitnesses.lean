import ResearchLean.AG.DoctrineFiberProduct.BCSchema
import ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses

/-!
# Finite witnesses for the Beck--Chevalley input schema

The witnesses exercise a nonempty G-106 combinatorial diagram, valid and
invalid compatible-point tables, positive and negative BC condition values,
and the boundary between generated pullback squares and a concrete commutative
square that is not a pullback.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open CategoryTheory.Limits
open AtomFoundation
open TransportCoherence

/-- Executable equality for the concrete finite Atom carrier. -/
local instance finiteBCModelCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- One concrete label reused in every finite diagnostic cell dimension. -/
inductive FiniteBCDiagnosticCell : Type
  | cell
deriving DecidableEq

/-- The concrete diagnostic label family is a singleton finite type. -/
instance finiteBCDiagnosticCellFintype : Fintype FiniteBCDiagnosticCell where
  elems := {FiniteBCDiagnosticCell.cell}
  complete := by intro value; cases value; simp

/-! ## A nonempty finite G-106 diagnostic presentation -/

/-- One-vertex, one-edge, one-2-cell diagnostic skeleton. -/
def finiteBCDiagnosticTwoPresentation : FiniteTransportTwoPresentation.{0} where
  Vertex := FiniteBCDiagnosticCell
  vertexFintype := inferInstance
  Edge := fun _ _ => FiniteBCDiagnosticCell
  edgeFintype := fun _ _ => inferInstance
  TwoCell := FiniteBCDiagnosticCell
  twoCellFintype := inferInstance
  twoSource := fun _ => FiniteBCDiagnosticCell.cell
  twoTarget := fun _ => FiniteBCDiagnosticCell.cell
  twoLeft := fun _ => .nil FiniteBCDiagnosticCell.cell
  twoRight := fun _ => .cons FiniteBCDiagnosticCell.cell
    (.nil FiniteBCDiagnosticCell.cell)

/-- Empty path in the concrete diagnostic skeleton. -/
def finiteBCDiagnosticEmptyPath :
    finiteBCDiagnosticTwoPresentation.Path
      FiniteBCDiagnosticCell.cell FiniteBCDiagnosticCell.cell :=
  .nil FiniteBCDiagnosticCell.cell

/-- Single-edge path in the concrete diagnostic skeleton. -/
def finiteBCDiagnosticEdgePath :
    finiteBCDiagnosticTwoPresentation.Path
      FiniteBCDiagnosticCell.cell FiniteBCDiagnosticCell.cell :=
  .cons FiniteBCDiagnosticCell.cell (.nil FiniteBCDiagnosticCell.cell)

/-- Nonempty forward rewrite used by the concrete diagnostic 3-cell. -/
def finiteBCDiagnosticFace : WhiskeredFace
    finiteBCDiagnosticTwoPresentation
      FiniteBCDiagnosticCell.cell FiniteBCDiagnosticCell.cell where
  cell := FiniteBCDiagnosticCell.cell
  incoming := .nil FiniteBCDiagnosticCell.cell
  outgoing := .nil FiniteBCDiagnosticCell.cell
  orientation := .forward

/--
One-vertex G-106 geometry with nonempty edge, 2-cell, 3-cell, and oriented-face
families.  The 3-cell compares the same one-face rewrite on both sides; it is a
schema-coverage witness, not a nonvanishing claim.
-/
def finiteBCDiagnosticGeometry : FiniteTransportPresentation.{0} where
  toFiniteTransportTwoPresentation := finiteBCDiagnosticTwoPresentation
  ThreeCell := FiniteBCDiagnosticCell
  threeCellFintype := inferInstance
  threeSource := fun _ => FiniteBCDiagnosticCell.cell
  threeTarget := fun _ => FiniteBCDiagnosticCell.cell
  threeStart := fun _ => finiteBCDiagnosticFace.before
  threeFinish := fun _ => finiteBCDiagnosticFace.after
  threeLeft := fun _ =>
    .cons finiteBCDiagnosticFace.asStep (.nil finiteBCDiagnosticFace.after)
  threeRight := fun _ =>
    .cons finiteBCDiagnosticFace.asStep (.nil finiteBCDiagnosticFace.after)

/-- Fully enumerated finite diagnostic code for the concrete G-106 geometry. -/
def finiteBCDiagnosticPresentation : FiniteDiagnosticPresentation.{0} where
  geometry := finiteBCDiagnosticGeometry
  vertexDecidableEq := by
    change DecidableEq FiniteBCDiagnosticCell
    infer_instance
  edgeDecidableEq := by
    intro source target
    change DecidableEq FiniteBCDiagnosticCell
    infer_instance
  twoCellDecidableEq := by
    change DecidableEq FiniteBCDiagnosticCell
    infer_instance
  threeCellDecidableEq := by
    change DecidableEq FiniteBCDiagnosticCell
    infer_instance
  vertices := [FiniteBCDiagnosticCell.cell]
  vertices_nodup := by simp
  vertices_complete := by intro vertex; cases vertex; simp
  edges := fun _ _ => [FiniteBCDiagnosticCell.cell]
  edges_nodup := by intro; simp
  edges_complete := by intro source target edge; cases edge; simp
  twoCells := [FiniteBCDiagnosticCell.cell]
  twoCells_nodup := by simp
  twoCells_complete := by intro value; cases value; simp
  threeCells := [FiniteBCDiagnosticCell.cell]
  threeCells_nodup := by simp
  threeCells_complete := by intro value; cases value; simp

/-- Identity package lift assigned to the concrete diagnostic edge. -/
noncomputable def finiteBCDiagnosticLiftData :
    AdmissibleLiftData finiteBCDiagnosticGeometry FiniteModel.carrier where
  package := fun _ => FiniteModel.corePackage
  edgeLift := fun _ => PackageTotalHom.id FiniteModel.corePackage
  edgeStrong := by
    intro source target edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 (packagePoint FiniteModel.corePackage))
        (Iso.refl FiniteModel.corePackage).hom :=
      CategoryTheory.IsHomLift.id rfl
    simpa using
      (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
        (packageProjection FiniteModel.carrier)
        (𝟙 (packagePoint FiniteModel.corePackage))
        (Iso.refl FiniteModel.corePackage))

/-- Concrete pre-base-change interpretation with identity authored comparator. -/
noncomputable def finiteBCDiagnosticTransportData :
    AdmissibleTransportData finiteBCDiagnosticGeometry FiniteModel.carrier where
  lift := finiteBCDiagnosticLiftData
  twoCellBase := by
    intro value
    cases value
    change (PackageTotalHom.id FiniteModel.corePackage).base =
      ((PackageTotalHom.id FiniteModel.corePackage).comp
        (PackageTotalHom.id FiniteModel.corePackage)).base
    rw [show (PackageTotalHom.id FiniteModel.corePackage).comp
        (PackageTotalHom.id FiniteModel.corePackage) =
      PackageTotalHom.id FiniteModel.corePackage by
        exact (@Category.comp_id
          (AATCorePackage FiniteModel.carrier)
          (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
          FiniteModel.corePackage FiniteModel.corePackage
          (PackageTotalHom.id FiniteModel.corePackage))]
  comparator := fun _ => 1

/-- The diagnostic vertex projection sees the concrete vertex. -/
theorem finiteBCDiagnostic_vertices_nonempty :
    finiteBCDiagnosticPresentation.vertices.length = 1 := by
  simp [finiteBCDiagnosticPresentation]

/-- The diagnostic 2-cell serialization is genuinely nonempty. -/
theorem finiteBCDiagnostic_twoCells_nonempty :
    (diagnosticTwoLeftPaths finiteBCDiagnosticPresentation).length = 1 := by
  simp [diagnosticTwoLeftPaths, finiteBCDiagnosticPresentation]

/-- The diagnostic 3-cell serialization contains a genuine oriented face. -/
theorem finiteBCDiagnostic_threeFaces_nonempty :
    (diagnosticFaces finiteBCDiagnosticPresentation).length = 2 := by
  simp [diagnosticFaces, diagnosticThreeLeftPastings,
    diagnosticThreeRightPastings, finiteBCDiagnosticPresentation,
    finiteBCDiagnosticGeometry, diagnosticPastingValue]

/-! ## Valid and invalid BC point tables -/

/-- Constant two-leg cospan used by the positive BC schema instance. -/
def finiteConstantBCCospan : CartCospanPresentation FiniteModel.carrier where
  firstSource := finiteTwoSourceInstance
  secondSource := finiteTwoSourceInstance
  base := finiteOneSourceInstance
  first := finiteConstantPresentation
  second := finiteConstantPresentation

/-- Compatible point table for the constant cospan. -/
def finiteConstantCompatiblePointCode : CompatiblePointCode where
  sourcePoints := fun _ => 0
  basePoint := 0
  images := fun _ => 0

/-- The concrete point table agrees with both selected cospan legs. -/
theorem finiteConstantCompatiblePointCode_wellFormed :
    finiteConstantCompatiblePointCode.WellFormed finiteConstantBCCospan := by
  simp [CompatiblePointCode.WellFormed, finiteConstantCompatiblePointCode,
    finiteConstantBCCospan, finiteTwoSourceInstance, finiteOneSourceInstance,
    finiteTwoSourceZero, finiteOneSourceZero, finiteConstantPresentation,
    finiteConstantSourceMap]

/-- Valid raw BC code with noninvertible cospan legs and nonempty diagnostic cells. -/
noncomputable def finiteConstantBCRawCode : BCRawCode FiniteModel.carrier where
  cospan := finiteConstantBCCospan
  compatiblePoints := finiteConstantCompatiblePointCode
  diagnostic := finiteBCDiagnosticPresentation

/-- The concrete constant BC raw code is well formed. -/
theorem finiteConstantBCRawCode_wellFormed : finiteConstantBCRawCode.WellFormed :=
  finiteConstantCompatiblePointCode_wellFormed

/-- Validated concrete BC presentation. -/
noncomputable def finiteConstantBCPresentation : BCPresentation FiniteModel.carrier :=
  ⟨finiteConstantBCRawCode, finiteConstantBCRawCode_wellFormed⟩

/--
The concrete G-106 package interpretation inhabits the separate dependent
semantic layer; it is not an authored BC-presentation field.
-/
noncomputable def finiteConstantBCDiagnosticInterpretation :
    BCDiagnosticInterpretation FiniteModel.carrier
      (toSemanticBC finiteConstantBCPresentation) where
  data := by
    simpa [toSemanticBC, finiteConstantBCPresentation, finiteConstantBCRawCode,
      finiteBCDiagnosticPresentation] using finiteBCDiagnosticTransportData

/-- The BC validator accepts the concrete valid raw code. -/
theorem finiteConstantBCRawCode_check_true :
    finiteConstantBCRawCode.checkWellFormed = true :=
  (BCRawCode.checkWellFormed_eq_true_iff finiteConstantBCRawCode).mpr
    finiteConstantBCRawCode_wellFormed

/-- Both generated pullback legs expose the four-source pullback code. -/
theorem finiteConstantBC_generated_leg_source_cards :
    readBCProjection (.cart .top .sourceCard) finiteConstantBCPresentation =
        ULift.up 4 ∧
      readBCProjection (.cart .left .sourceCard) finiteConstantBCPresentation =
        ULift.up 4 := by
  constructor <;>
    simpa [readBCProjection, bcCartPresentation, finiteConstantBCPresentation,
      finiteConstantBCRawCode, finiteConstantBCCospan,
      pullbackFstPresentation, pullbackSndPresentation,
      pullbackInstanceCode] using congrArg ULift.up
        finiteConstantPullback_sourceCard

/-- Malformed compatible-point table whose authored base index is out of range. -/
def finiteBadBCCompatiblePointCode : CompatiblePointCode where
  sourcePoints := fun _ => 0
  basePoint := 1
  images := fun _ => 0

/-- Raw BC code carrying the malformed compatible-point table. -/
noncomputable def finiteBadBCRawCode : BCRawCode FiniteModel.carrier where
  cospan := finiteConstantBCCospan
  compatiblePoints := finiteBadBCCompatiblePointCode
  diagnostic := finiteBCDiagnosticPresentation

/-- The malformed point table fails BC validation. -/
theorem finiteBadBCRawCode_not_wellFormed : ¬ finiteBadBCRawCode.WellFormed := by
  intro hwellFormed
  have hbase := hwellFormed.2.2.1
  norm_num [finiteBadBCRawCode, finiteBadBCCompatiblePointCode,
    finiteConstantBCCospan, finiteOneSourceInstance, finiteOneSourceZero] at hbase

/-- The Boolean BC validator rejects the same malformed raw code. -/
theorem finiteBadBCRawCode_check_false :
    finiteBadBCRawCode.checkWellFormed = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact finiteBadBCRawCode_not_wellFormed
    ((BCRawCode.checkWellFormed_eq_true_iff finiteBadBCRawCode).mp htrue)

/-! ## Positive and negative BC condition instances -/

/-- The first-leg Atom condition accepts a noninvertible constant cospan leg. -/
theorem finiteConstantBC_firstAtom_check :
    evalBCCondition (.allCells (.cart .bottom .atomMapIdentity))
      finiteConstantBCPresentation = true := by
  rw [evalBCCondition_firstAtomMapIdentity_eq_true_iff]
  exact AtomPermutationCode.toEquiv_refl

/-- All three nonempty diagnostic-geometry universals fire on the concrete code. -/
theorem finiteConstantBC_diagnostic_structure_check :
    evalBCCondition
      (.conjunction (.allCells .diagnosticTwoCellEndpointsInRange)
        (.conjunction (.allCells .diagnosticThreeCellEndpointsInRange)
          (.allCells .diagnosticFaceReferencesInRange)))
      finiteConstantBCPresentation = true := by
  rfl

/-- Cospan with a nonidentity Atom permutation on its first leg. -/
noncomputable def finiteSwapBCCospan : CartCospanPresentation FiniteModel.carrier where
  firstSource := finiteTwoSourceInstance
  secondSource := finiteTwoSourceInstance
  base := finiteTwoSourceInstance
  first := finiteSwapPresentation
  second := idTypedPresentation finiteTwoSourceInstance

/-- The same all-zero point table is compatible with the swap cospan. -/
theorem finiteConstantCompatiblePointCode_swap_wellFormed :
    finiteConstantCompatiblePointCode.WellFormed finiteSwapBCCospan := by
  simp [CompatiblePointCode.WellFormed, finiteConstantCompatiblePointCode,
    finiteSwapBCCospan, finiteTwoSourceInstance, finiteTwoSourceZero,
    finiteSwapPresentation, idTypedPresentation]

/-- Validated BC presentation with a genuinely nonidentity first Atom component. -/
noncomputable def finiteSwapBCPresentation : BCPresentation FiniteModel.carrier :=
  ⟨{ cospan := finiteSwapBCCospan
     compatiblePoints := finiteConstantCompatiblePointCode
     diagnostic := finiteBCDiagnosticPresentation },
    finiteConstantCompatiblePointCode_swap_wellFormed⟩

/-- The first-leg Atom condition rejects the concrete swap table. -/
theorem finiteSwapBC_firstAtom_check_false :
    evalBCCondition (.allCells (.cart .bottom .atomMapIdentity))
      finiteSwapBCPresentation = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  have hid :=
    (evalBCCondition_firstAtomMapIdentity_eq_true_iff
      finiteSwapBCPresentation).mp htrue
  change finiteSwapPermutationCode.toEquiv =
    Equiv.refl FiniteModel.FiniteAtom at hid
  have hcomponent := congrArg
    (fun equiv : Equiv.Perm FiniteModel.FiniteAtom =>
      equiv FiniteModel.FiniteAtom.componentC) hid
  change finiteSwapPermutationCode.toEquiv FiniteModel.FiniteAtom.componentC =
    FiniteModel.FiniteAtom.componentC at hcomponent
  rw [finiteSwapPermutationCode_componentC] at hcomponent
  simp at hcomponent

/-- Canonical positive realization witness for the concrete pullback square. -/
noncomputable def finiteConstantRealizableSquare :
    RealizableSquare FiniteModel.carrier :=
  realizableSquareOf finiteConstantBCPresentation

/-- The semantic first-leg predicate fires on the concrete constant square. -/
theorem finiteConstantRealizableSquare_firstLegIdentity :
    FirstLegIdentityAtomComponent finiteConstantRealizableSquare :=
  (evalBCCondition_firstAtomMapIdentity_bridge
    finiteConstantBCPresentation).mp finiteConstantBC_firstAtom_check

/-- The same semantic predicate fails on the concrete swap square. -/
theorem finiteSwapRealizableSquare_not_firstLegIdentity :
    ¬ FirstLegIdentityAtomComponent
      (realizableSquareOf finiteSwapBCPresentation) := by
  intro hidentity
  have htrue := (evalBCCondition_firstAtomMapIdentity_bridge
    finiteSwapBCPresentation).mpr hidentity
  rw [finiteSwapBC_firstAtom_check_false] at htrue
  contradiction

/-! ## A commutative semantic square outside the generated pullback image -/

/-- Constant endomorphism of the two-source instance, distinct from identity. -/
def finiteTwoCollapsePresentation :
    CartPresentationBetween finiteTwoSourceInstance finiteTwoSourceInstance where
  sourceMap := fun _ => finiteTwoSourceZero
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- The decoded collapse endomorphism is not the categorical identity. -/
theorem finiteTwoCollapseSemantic_ne_id :
    (toSemanticCart finiteTwoCollapsePresentation.toPresentation).hom ≠
      𝟙 finiteTwoSourceInstance.toSemantic := by
  intro equality
  have hmap := congrArg
    (fun hom : finiteTwoSourceInstance.toSemantic ⟶
        finiteTwoSourceInstance.toSemantic =>
      hom.doctrineHom.sourceMap finiteTwoSourceOne) equality
  change finiteTwoSourceZero = finiteTwoSourceOne at hmap
  have hdown := congrArg
    (fun source : (finiteAllDoctrineCode 2).Source => source.down.val) hmap
  norm_num [finiteTwoSourceZero, finiteTwoSourceOne,
    finiteAllDoctrineCode] at hdown

/-- Composing the collapse endomorphism with the constant map changes nothing. -/
theorem finiteTwoCollapse_comp_finiteConstant :
    (toSemanticCart finiteTwoCollapsePresentation.toPresentation).hom ≫
        (toSemanticCart finiteConstantPresentation.toPresentation).hom =
      (toSemanticCart finiteConstantPresentation.toPresentation).hom := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · rfl

/-- Concrete commutative square whose two projections are the constant map. -/
noncomputable def finiteNonPullbackSquare : ExtInstSquare FiniteModel.carrier where
  northwest := finiteTwoSourceInstance.toSemantic
  northeast := finiteOneSourceInstance.toSemantic
  southwest := finiteOneSourceInstance.toSemantic
  southeast := finiteOneSourceInstance.toSemantic
  top := (toSemanticCart finiteConstantPresentation.toPresentation).hom
  left := (toSemanticCart finiteConstantPresentation.toPresentation).hom
  right := 𝟙 finiteOneSourceInstance.toSemantic
  bottom := 𝟙 finiteOneSourceInstance.toSemantic
  commutes := by simp

/-- The concrete commutative square is not a categorical pullback. -/
theorem finiteNonPullbackSquare_not_isPullback :
    ¬ IsPullback finiteNonPullbackSquare.left finiteNonPullbackSquare.top
      finiteNonPullbackSquare.bottom finiteNonPullbackSquare.right := by
  intro hpullback
  have hequal := hpullback.hom_ext
    (k := (toSemanticCart finiteTwoCollapsePresentation.toPresentation).hom)
    (l := 𝟙 finiteTwoSourceInstance.toSemantic)
    (by
      change (toSemanticCart finiteTwoCollapsePresentation.toPresentation).hom ≫
          (toSemanticCart finiteConstantPresentation.toPresentation).hom =
        (𝟙 finiteTwoSourceInstance.toSemantic) ≫
          (toSemanticCart finiteConstantPresentation.toPresentation).hom
      rw [finiteTwoCollapse_comp_finiteConstant, Category.id_comp])
    (by
      change (toSemanticCart finiteTwoCollapsePresentation.toPresentation).hom ≫
          (toSemanticCart finiteConstantPresentation.toPresentation).hom =
        (𝟙 finiteTwoSourceInstance.toSemantic) ≫
          (toSemanticCart finiteConstantPresentation.toPresentation).hom
      rw [finiteTwoCollapse_comp_finiteConstant, Category.id_comp])
  exact finiteTwoCollapseSemantic_ne_id hequal

/-- Semantic BC input carrying the concrete non-pullback square. -/
noncomputable def finiteNonPullbackBCInput : BCSemanticInput FiniteModel.carrier where
  square := finiteNonPullbackSquare
  compatiblePoints := compatiblePointSemanticInputOfSquare finiteNonPullbackSquare
  diagnostic := finiteBCDiagnosticGeometry

/-- No validated finite BC presentation realizes the concrete non-pullback input. -/
theorem finiteNonPullbackBCInput_not_presented :
    ¬ ∃ presentation : BCPresentation FiniteModel.carrier,
      toSemanticBC presentation = finiteNonPullbackBCInput := by
  rintro ⟨presentation, equality⟩
  have hpullback := (toSemanticBC_sound presentation).1
  have htarget :
      (fun input : BCSemanticInput FiniteModel.carrier =>
        IsPullback input.square.left input.square.top
          input.square.bottom input.square.right) finiteNonPullbackBCInput := by
    rw [← equality]
    exact hpullback
  exact finiteNonPullbackSquare_not_isPullback (by
    simpa [finiteNonPullbackBCInput] using htarget)

/-- No realization certificate can package the same non-pullback semantic input. -/
theorem finiteNonPullbackBCInput_has_no_realizableSquare :
    ¬ ∃ square : RealizableSquare FiniteModel.carrier,
      square.semantic = finiteNonPullbackBCInput := by
  rintro ⟨square, equality⟩
  apply finiteNonPullbackBCInput_not_presented
  exact ⟨square.presentation, square.realization_eq.trans equality⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
