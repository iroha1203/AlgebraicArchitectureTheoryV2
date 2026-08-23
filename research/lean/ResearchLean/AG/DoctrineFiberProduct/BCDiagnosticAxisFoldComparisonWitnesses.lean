import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparison
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredFactorizationComparisonWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses
import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Strict and lax finite witnesses for the diagnostic axis-fold comparison

The lax fixture uses the reviewed G-106 double diamond.  Both parallel edges
are identity lifts of one three-axis package, while its two authored faces use
identity and an adjacent axis swap.  Thus no edge reselection can make both
faces coherent, and the nonidentity face internally generates a noninvertible
axis fold.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u₁ v₁

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## A decoded three-axis package and its diagnostic swap -/

/-- Preserve the three-axis signature while landing at the decoded BC point. -/
noncomputable def finiteAxisFoldSupportPackage :
    AATCorePackage FiniteModel.carrier :=
  transportAlong finiteWitnessSourcePackage finiteModelDoctrineFromFixture

/-- The package lies at the finite authored-support point. -/
theorem finiteAxisFoldSupportPackage_point :
    (packageProjection FiniteModel.carrier).obj finiteAxisFoldSupportPackage =
      finiteAuthoredSupportInstance.toSemantic := by
  rfl

/-- A permutation of the decoded package's three signature axes. -/
noncomputable def finiteAxisFoldPermutationUpper
    (permutation : Equiv.Perm (Fin 3)) :
    SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage :=
  { SignedExactCoreReadingHom.refl finiteAxisFoldSupportPackage with
    axisMap := permutation
    coordinateEquiv := by
      intro axis
      change Fin 3 ≃ Fin 3
      exact permutation
    axis_selected_iff := fun _ => Iff.rfl
    coordinate_eq := by intro object axis; rfl }

/-- A signature permutation as a total morphism over identity. -/
noncomputable def finiteAxisFoldPermutationTotal
    (permutation : Equiv.Perm (Fin 3)) :
    PackageTotalHom finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage where
  base := ExtInstHom.id (packagePoint finiteAxisFoldSupportPackage)
  upper := finiteAxisFoldPermutationUpper permutation
  atomEquiv_eq := rfl

/-- Total morphism composition follows permutation composition. -/
theorem finiteAxisFoldPermutationTotal_comp
    (first second : Equiv.Perm (Fin 3)) :
    (finiteAxisFoldPermutationTotal first).comp
        (finiteAxisFoldPermutationTotal second) =
      finiteAxisFoldPermutationTotal (first.trans second) := by
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

/-- The identity permutation is the package identity. -/
theorem finiteAxisFoldPermutationTotal_refl :
    finiteAxisFoldPermutationTotal (Equiv.refl (Fin 3)) =
      PackageTotalHom.id finiteAxisFoldSupportPackage := by
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

/-- The adjacent swap as a total morphism over identity. -/
noncomputable def finiteAxisFoldSwapTotal :
    PackageTotalHom finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage :=
  finiteAxisFoldPermutationTotal (Equiv.swap (0 : Fin 3) 1)

/-- The adjacent swap squares to the package identity. -/
theorem finiteAxisFoldSwapTotal_square :
    finiteAxisFoldSwapTotal.comp finiteAxisFoldSwapTotal =
      PackageTotalHom.id finiteAxisFoldSupportPackage := by
  rw [finiteAxisFoldSwapTotal, finiteAxisFoldPermutationTotal_comp]
  rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 0 1) =
      Equiv.refl (Fin 3) by
    apply Equiv.ext
    intro axis
    fin_cases axis <;> rfl]
  exact finiteAxisFoldPermutationTotal_refl

/-- The adjacent swap as a package-fiber automorphism. -/
noncomputable def finiteAxisFoldSwap :
    PackageFiberAut finiteAxisFoldSupportPackage :=
  ⟨{
    hom := finiteAxisFoldSwapTotal
    inv := finiteAxisFoldSwapTotal
    hom_inv_id := finiteAxisFoldSwapTotal_square
    inv_hom_id := finiteAxisFoldSwapTotal_square }, rfl⟩

/-- Its moved zero axis generates a noninvertible fold. -/
noncomputable def finiteAxisFoldSwapWitness :
    PackageFiberAut.AxisFoldWitness finiteAxisFoldSwap where
  source := (0 : Fin 3)
  axisDecidableEq := Classical.decEq _
  moved := by
    change (Equiv.swap (0 : Fin 3) 1) 0 ≠ 0
    decide
  objectMap_eq := rfl

theorem finiteAxisFoldSwap_available :
    PackageFiberAut.AxisFoldAvailable finiteAxisFoldSwap :=
  ⟨finiteAxisFoldSwapWitness⟩

theorem finiteAxisFoldSwap_generated_not_isIso :
    ¬ IsIso
      (show finiteAxisFoldSupportPackage ⟶ finiteAxisFoldSupportPackage from
        PackageFiberAut.generatedAxisFoldTotal finiteAxisFoldSwap) :=
  PackageFiberAut.generatedAxisFoldTotal_not_isIso finiteAxisFoldSwap
    finiteAxisFoldSwap_available

/-! ## Double-diamond authored datum -/

/-- Fully enumerated double-diamond diagnostic code. -/
noncomputable def finiteAxisFoldDiagnosticPresentation :
    FiniteDiagnosticPresentation.{0} where
  geometry := doubleDiamondPresentation PUnit
  vertexDecidableEq := Classical.decEq _
  edgeDecidableEq := fun _ _ => Classical.decEq _
  twoCellDecidableEq := Classical.decEq _
  threeCellDecidableEq := Classical.decEq _
  vertices := Finset.univ.toList
  vertices_nodup := Finset.nodup_toList _
  vertices_complete := fun vertex => Finset.mem_toList.mpr (Finset.mem_univ vertex)
  edges := fun _ _ => Finset.univ.toList
  edges_nodup := fun _ _ => Finset.nodup_toList _
  edges_complete := fun _ _ edge => Finset.mem_toList.mpr (Finset.mem_univ edge)
  twoCells := Finset.univ.toList
  twoCells_nodup := Finset.nodup_toList _
  twoCells_complete := fun cell => Finset.mem_toList.mpr (Finset.mem_univ cell)
  threeCells := Finset.univ.toList
  threeCells_nodup := Finset.nodup_toList _
  threeCells_complete := fun cell => Finset.mem_toList.mpr (Finset.mem_univ cell)

/-- Identity BC square carrying the double-diamond diagnostic. -/
noncomputable def finiteAxisFoldBCPresentation : BCPresentation FiniteModel.carrier :=
  bcPresentationOfCospan finiteAuthoredSupportCospan
    finiteAxisFoldDiagnosticPresentation

noncomputable def finiteAxisFoldSquare : RealizableSquare FiniteModel.carrier :=
  realizableSquareOf finiteAxisFoldBCPresentation

/-- Identity lift on every double-diamond edge. -/
noncomputable def finiteAxisFoldLiftData :
    AdmissibleLiftData (doubleDiamondPresentation PUnit) FiniteModel.carrier where
  package := fun _ => finiteAxisFoldSupportPackage
  edgeLift := fun _ => PackageTotalHom.id finiteAxisFoldSupportPackage
  edgeStrong := by
    intro vertexSource vertexTarget edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 (packagePoint finiteAxisFoldSupportPackage))
        (Iso.refl finiteAxisFoldSupportPackage).hom :=
      CategoryTheory.IsHomLift.id rfl
    simpa using
      (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
        (packageProjection FiniteModel.carrier)
        (𝟙 (packagePoint finiteAxisFoldSupportPackage))
        (Iso.refl finiteAxisFoldSupportPackage))

/-- Identity and swap comparators on the two faces of the same diamond. -/
noncomputable def finiteAxisFoldTransportData :
    AdmissibleTransportData (doubleDiamondPresentation PUnit)
      FiniteModel.carrier where
  lift := finiteAxisFoldLiftData
  twoCellBase := by
    intro cell
    cases cell <;> rfl
  comparator
    | .first => 1
    | .second => finiteAxisFoldSwap

/-- The two authored comparators are genuinely distinct. -/
theorem finiteAxisFold_comparators_ne :
    finiteAxisFoldTransportData.comparator .first ≠
      finiteAxisFoldTransportData.comparator .second := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
  change (0 : Fin 3) = 1 at axisEquality
  exact Fin.zero_ne_one axisEquality

/-- No edge reselection makes both double-diamond faces coherent. -/
theorem finiteAxisFold_not_coherentizable :
    ¬ Coherentizable finiteAxisFoldTransportData := by
  rintro ⟨reselection, coherent⟩
  exact finiteAxisFold_comparators_ne
    (doubleDiamond_comparator_eq_of_coherentAt
      finiteAxisFoldTransportData reselection coherent)

/-- Interpret the double diamond on the decoded identity BC square. -/
noncomputable def finiteAxisFoldInterpretation :
    BCDiagnosticInterpretation FiniteModel.carrier
      finiteAxisFoldSquare.semantic where
  data := by
    simpa [finiteAxisFoldSquare, realizableSquareOf,
      finiteAxisFoldBCPresentation, bcPresentationOfCospan,
      toSemanticBC, finiteAxisFoldDiagnosticPresentation] using
        finiteAxisFoldTransportData

/-- Every double-diamond target is the southwest point of the identity square. -/
theorem finiteAxisFold_endpoint_eq
    (cell : finiteAxisFoldSquare.semantic.diagnostic.TwoCell) :
    (packageProjection FiniteModel.carrier).obj
        (finiteAxisFoldInterpretation.data.lift.package
          (finiteAxisFoldSquare.semantic.diagnostic.twoTarget cell)) =
      finiteAxisFoldSquare.semantic.square.southwest := by
  cases cell <;> rfl

/-- The lax authored datum has two genuine support components. -/
noncomputable def finiteAxisFoldBCDatumSquare :
    AuthoredBCDatumSquare FiniteModel.carrier :=
  AuthoredBCDatumSquare.ofInterpretation finiteAxisFoldSquare
    finiteAxisFoldInterpretation finiteAxisFold_endpoint_eq

theorem finiteAxisFoldSupport_nonempty :
    Nonempty finiteAxisFoldBCDatumSquare.context.Category :=
  ⟨Discrete.mk DoubleDiamondTwoCell.second⟩

/-- The canonical comparator of the two identity path lifts is identity. -/
theorem finiteAxisFold_canonicalComparator_second_eq_one :
    canonicalTwoCellComparator finiteAxisFoldTransportData 1
        DoubleDiamondTwoCell.second = 1 := by
  let left := reselectedPathLift finiteAxisFoldTransportData.lift 1
    ((doubleDiamondPresentation PUnit).twoLeft DoubleDiamondTwoCell.second)
  letI : (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      left.base left :=
    reselectedPathLift_isStronglyCocartesian
      finiteAxisFoldTransportData.lift 1
      ((doubleDiamondPresentation PUnit).twoLeft DoubleDiamondTwoCell.second)
  apply PackageFiberAut.ext_of_strong_fac left
  rw [canonicalTwoCellComparator_fac]
  simp [left, finiteAxisFoldTransportData, finiteAxisFoldLiftData,
    reselectedPathLift, reselectLiftData, AdmissibleLiftData.pathLift,
    singleDiskLeftPath,
    singleDiskRightPath, doubleDiamondPresentation,
    doubleDiamondTwoPresentation]
  rw [show PackageFiberAut.hom
      (1 : PackageFiberAut finiteAxisFoldSupportPackage) =
    PackageTotalHom.id finiteAxisFoldSupportPackage by rfl]
  exact (@Category.comp_id
    (AATCorePackage FiniteModel.carrier)
    (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
    finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage
    ((PackageTotalHom.id finiteAxisFoldSupportPackage).comp
      (PackageTotalHom.id finiteAxisFoldSupportPackage))).symm

/-- The initial raw defect on the second face is the adjacent swap. -/
theorem finiteAxisFold_initialRawDefect_second :
    initialRawDefectCochain finiteAxisFoldTransportData
        DoubleDiamondTwoCell.second =
      finiteAxisFoldSwap := by
  rw [initialRawDefectCochain, rawDefectCochain, rawTwoCellDefect,
    finiteAxisFold_canonicalComparator_second_eq_one]
  simp [finiteAxisFoldTransportData]

/-- The lax input reconstructs exactly the reviewed double-diamond datum. -/
theorem finiteAxisFold_toTransportData :
    finiteAxisFoldBCDatumSquare.toTransportData =
      finiteAxisFoldTransportData := by
  rfl

/-- Hence the generated fold is available at the nonidentity support face. -/
theorem finiteAxisFold_initialRawDefect_second_available :
    PackageFiberAut.AxisFoldAvailable
      (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
        DoubleDiamondTwoCell.second) := by
  rw [finiteAxisFold_toTransportData, finiteAxisFold_initialRawDefect_second]
  exact finiteAxisFoldSwap_available

/-- A functor naturally isomorphic to identity reflects isomorphisms. -/
theorem isIso_of_map_isIso_of_natIso_id
    {C : Type u₁} [Category.{v₁} C] (functor : C ⥤ C)
    (unitor : functor ≅ 𝟭 C) {source target : C}
    (hom : source ⟶ target) [IsIso (functor.map hom)] : IsIso hom := by
  letI : IsIso (unitor.hom.app source ≫ hom) := by
    change IsIso (unitor.hom.app source ≫ (𝟭 C).map hom)
    rw [← unitor.hom.naturality hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (unitor.hom.app source) hom

/-- The transported fold at the nonidentity face remains noninvertible. -/
theorem finiteAxisFold_viaBaseFold_second_not_isIso :
    ¬ IsIso
      (authoredViaBaseDiagnosticAxisFoldComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)) := by
  intro isIso
  letI : IsIso
      (authoredViaBaseDiagnosticAxisFoldComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)) := isIso
  let fold := authoredDiagnosticAxisFoldDecodedComponent
    finiteAxisFoldBCDatumSquare DoubleDiamondTwoCell.second
  let transported :=
    (coreFiberTransportFunctor
      (𝟙 finiteAuthoredSupportInstance.toSemantic)).map fold
  let reindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (idTypedPresentation finiteAuthoredSupportInstance))).map transported
  letI : IsIso reindexed := by
    change IsIso
      (authoredViaBaseDiagnosticAxisFoldComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second))
    infer_instance
  letI : IsIso transported :=
    isIso_of_map_isIso_of_natIso_id
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (idTypedPresentation finiteAuthoredSupportInstance)))
      (selectedCoreFiberReindexUnitor finiteAuthoredSupportInstance).symm
      transported
  letI : IsIso fold :=
    isIso_of_map_isIso_of_natIso_id
      (coreFiberTransportFunctor
        (𝟙 finiteAuthoredSupportInstance.toSemantic))
      (coreFiberUnitor finiteAuthoredSupportInstance.toSemantic) fold
  letI : IsIso fold.1 := by
    change IsIso
      (CategoryTheory.Functor.Fiber.fiberInclusion.map fold)
    infer_instance
  have fold_val_eq :
      fold.1 = PackageFiberAut.generatedAxisFoldTotal finiteAxisFoldSwap := by
    dsimp [fold, authoredDiagnosticAxisFoldDecodedComponent,
      authoredDiagnosticAxisFoldComponent, authoredDiagnosticAxisFoldTotal]
    change PackageFiberAut.generatedAxisFoldTotal
        (initialRawDefectCochain finiteAxisFoldTransportData
          DoubleDiamondTwoCell.second) =
      PackageFiberAut.generatedAxisFoldTotal finiteAxisFoldSwap
    rw [finiteAxisFold_initialRawDefect_second]
  apply finiteAxisFoldSwap_generated_not_isIso
  rw [← fold_val_eq]
  infer_instance

/-- The generated lax component differs from the canonical mate. -/
theorem finiteAxisFoldComparison_second_ne_canonical :
    authoredDiagnosticAxisFoldComparisonComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second) := by
  intro equality
  rw [authoredDiagnosticAxisFoldComparisonComponent_eq_canonical_comp_fold]
    at equality
  have fold_eq_id :
      authoredViaBaseDiagnosticAxisFoldComponent finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second) =
        𝟙 ((authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj
          (Discrete.mk DoubleDiamondTwoCell.second)) := by
    apply (cancel_epi
      ((authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second))).1
    simpa using equality
  apply finiteAxisFold_viaBaseFold_second_not_isIso
  rw [fold_eq_id]
  infer_instance

/-- The concrete lax double diamond refutes the generated relation. -/
theorem finiteAxisFoldBCDatumSquare_not_mateCoherent :
    ¬ DiagnosticAxisFoldMateCoherentRel FiniteModel.carrier
      finiteAxisFoldBCDatumSquare := by
  apply AuthoredSupportComparison.not_agrees_of_app_ne
    (Discrete.mk DoubleDiamondTwoCell.second)
  exact finiteAxisFoldComparison_second_ne_canonical

/-! ## Strict positive control -/

/-- The existing strict authored square fires the same generated relation. -/
theorem finiteAuthoredBCDatumSquare_diagnosticAxisFoldMateCoherent :
    DiagnosticAxisFoldMateCoherentRel FiniteModel.carrier
      finiteAuthoredBCDatumSquare := by
  apply diagnosticAxisFoldMateCoherentRel_of_initialRawDefect_eq_identity
  simpa [finiteAuthoredFactorization_toTransportData] using
    finiteAuthoredFactorization_initialRawDefect_eq_identity

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
