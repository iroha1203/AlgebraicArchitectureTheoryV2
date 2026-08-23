import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFold
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses

/-!
# Orbit witnesses for the pairwise diagnostic axis fold

The fixed double diamond has two faces with the same endpoint and the same
boundary paths.  Their pairwise raw-defect quotient cancels the common
canonical comparator at every edge coordinate and leaves the authored adjacent
swap.  The resulting cochain-indexed comparison therefore remains noncanonical
throughout the actual G-106 reselection orbit.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u₁ v₁

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finitePairwiseAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Both double-diamond faces have the same generated path comparator. -/
theorem finiteAxisFold_canonicalComparator_faces_eq
    (reselection : EdgeReselection finiteAxisFoldTransportData.lift) :
    canonicalTwoCellComparator finiteAxisFoldTransportData reselection
        DoubleDiamondTwoCell.first =
      canonicalTwoCellComparator finiteAxisFoldTransportData reselection
        DoubleDiamondTwoCell.second := by
  let left := reselectedPathLift finiteAxisFoldTransportData.lift reselection
    ((doubleDiamondPresentation PUnit).twoLeft DoubleDiamondTwoCell.first)
  letI : (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      left.base left :=
    reselectedPathLift_isStronglyCocartesian
      finiteAxisFoldTransportData.lift reselection
      ((doubleDiamondPresentation PUnit).twoLeft DoubleDiamondTwoCell.first)
  apply PackageFiberAut.ext_of_strong_fac left
  calc
    left.comp (PackageFiberAut.hom
        (canonicalTwoCellComparator finiteAxisFoldTransportData reselection
          DoubleDiamondTwoCell.first)) =
      reselectedPathLift finiteAxisFoldTransportData.lift reselection
        ((doubleDiamondPresentation PUnit).twoRight
          DoubleDiamondTwoCell.first) :=
      canonicalTwoCellComparator_fac finiteAxisFoldTransportData reselection
        DoubleDiamondTwoCell.first
    _ = reselectedPathLift finiteAxisFoldTransportData.lift reselection
        ((doubleDiamondPresentation PUnit).twoRight
          DoubleDiamondTwoCell.second) := rfl
    _ = left.comp (PackageFiberAut.hom
        (canonicalTwoCellComparator finiteAxisFoldTransportData reselection
          DoubleDiamondTwoCell.second)) :=
      (canonicalTwoCellComparator_fac finiteAxisFoldTransportData reselection
        DoubleDiamondTwoCell.second).symm

/-- The double-diamond pairwise quotient cancels reselection at every coordinate. -/
theorem finiteAxisFold_pairwiseRawDefect_eq_swap
    (reselection : EdgeReselection finiteAxisFoldTransportData.lift) :
    PackageFiberAut.pairwiseRawDefect finiteAxisFoldTransportData
        (rawDefectCochain finiteAxisFoldTransportData reselection)
        DoubleDiamondTwoCell.first DoubleDiamondTwoCell.second rfl =
      finiteAxisFoldSwap := by
  rw [PackageFiberAut.pairwiseRawDefect]
  simp only [rawDefectCochain, rawTwoCellDefect]
  rw [← finiteAxisFold_canonicalComparator_faces_eq reselection]
  have cast_eq :
      PackageFiberAut.castTarget finiteAxisFoldTransportData
          (first := DoubleDiamondTwoCell.first)
          (second := DoubleDiamondTwoCell.second) rfl
          (finiteAxisFoldTransportData.comparator DoubleDiamondTwoCell.first *
            (canonicalTwoCellComparator finiteAxisFoldTransportData reselection
              DoubleDiamondTwoCell.first)⁻¹) =
        (canonicalTwoCellComparator finiteAxisFoldTransportData reselection
          DoubleDiamondTwoCell.first)⁻¹ := by
    simp [PackageFiberAut.castTarget, finiteAxisFoldTransportData]
  rw [cast_eq]
  simp [finiteAxisFoldTransportData, mul_assoc]

/-- The pairwise quotient is independent of the chosen reselection coordinate. -/
theorem finiteAxisFold_pairwiseRawDefect_reselection_invariant
    (first second : EdgeReselection finiteAxisFoldTransportData.lift) :
    PackageFiberAut.pairwiseRawDefect finiteAxisFoldTransportData
        (rawDefectCochain finiteAxisFoldTransportData first)
        DoubleDiamondTwoCell.first DoubleDiamondTwoCell.second rfl =
      PackageFiberAut.pairwiseRawDefect finiteAxisFoldTransportData
        (rawDefectCochain finiteAxisFoldTransportData second)
        DoubleDiamondTwoCell.first DoubleDiamondTwoCell.second rfl := by
  rw [finiteAxisFold_pairwiseRawDefect_eq_swap,
    finiteAxisFold_pairwiseRawDefect_eq_swap]

/--
The concrete authored faces retain the same pairwise quotient after replacing
their common generated canonical comparator.
-/
theorem finiteAxisFold_pairwise_commonCanonical_replacement_invariant
    (firstCanonical secondCanonical :
      PackageFiberAut finiteAxisFoldSupportPackage) :
    (finiteAxisFoldSwap * firstCanonical⁻¹) *
        ((1 : PackageFiberAut finiteAxisFoldSupportPackage) *
          firstCanonical⁻¹)⁻¹ =
      (finiteAxisFoldSwap * secondCanonical⁻¹) *
        ((1 : PackageFiberAut finiteAxisFoldSupportPackage) *
          secondCanonical⁻¹)⁻¹ := by
  exact PackageFiberAut.commonCanonicalPairwiseQuotient_replacement_invariant
    (1 : PackageFiberAut finiteAxisFoldSupportPackage)
    finiteAxisFoldSwap firstCanonical secondCanonical

/-- Every edge coordinate supplies the same moved-axis pairwise witness. -/
noncomputable def finiteAxisFold_pairwiseWitness
    (reselection : EdgeReselection finiteAxisFoldTransportData.lift) :
    PackageFiberAut.PairwiseAxisFoldWitnessAt finiteAxisFoldTransportData
      (rawDefectCochain finiteAxisFoldTransportData reselection)
      DoubleDiamondTwoCell.second where
  first := DoubleDiamondTwoCell.first
  package_eq := rfl
  fold := by
    rw [finiteAxisFold_pairwiseRawDefect_eq_swap reselection]
    exact finiteAxisFoldSwapWitness

/-- Pairwise fold availability holds throughout the actual reselection orbit. -/
theorem finiteAxisFold_pairwiseAvailable
    (reselection : EdgeReselection finiteAxisFoldTransportData.lift) :
    PackageFiberAut.PairwiseAxisFoldAvailableAt finiteAxisFoldTransportData
      (rawDefectCochain finiteAxisFoldTransportData reselection)
      DoubleDiamondTwoCell.second :=
  ⟨finiteAxisFold_pairwiseWitness reselection⟩

/-- The source pairwise fold is noninvertible at every edge coordinate. -/
theorem finiteAxisFold_generatedPairwise_not_isIso
    (reselection : EdgeReselection finiteAxisFoldTransportData.lift) :
    ¬ IsIso
      (show finiteAxisFoldSupportPackage ⟶ finiteAxisFoldSupportPackage from
        PackageFiberAut.generatedPairwiseAxisFoldTotalAt
          finiteAxisFoldTransportData
          (rawDefectCochain finiteAxisFoldTransportData reselection)
          DoubleDiamondTwoCell.second) :=
  PackageFiberAut.generatedPairwiseAxisFoldTotalAt_not_isIso
    finiteAxisFoldTransportData
    (rawDefectCochain finiteAxisFoldTransportData reselection)
    DoubleDiamondTwoCell.second
    (finiteAxisFold_pairwiseAvailable reselection)

/-- The authored input exposes the same pairwise availability at every coordinate. -/
theorem finiteAxisFold_input_pairwiseAvailable
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    PackageFiberAut.PairwiseAxisFoldAvailableAt
      finiteAxisFoldBCDatumSquare.toTransportData
      (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection)
      DoubleDiamondTwoCell.second := by
  simpa only [finiteAxisFold_toTransportData] using
    finiteAxisFold_pairwiseAvailable reselection

/-- A functor naturally isomorphic to identity reflects isomorphisms. -/
private theorem isIso_of_map_isIso_of_natIso_id_pairwise
    {C : Type u₁} [Category.{v₁} C] (functor : C ⥤ C)
    (unitor : functor ≅ 𝟭 C) {source target : C}
    (hom : source ⟶ target) [IsIso (functor.map hom)] : IsIso hom := by
  letI : IsIso (unitor.hom.app source ≫ hom) := by
    change IsIso (unitor.hom.app source ≫ (𝟭 C).map hom)
    rw [← unitor.hom.naturality hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (unitor.hom.app source) hom

/-- The via-base pairwise fold remains noninvertible at every coordinate. -/
theorem finiteAxisFold_viaBasePairwise_not_isIso
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    ¬ IsIso
      (authoredViaBasePairwiseAxisFoldComponentAtCochain
        finiteAxisFoldBCDatumSquare
        (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
          reselection)
        (Discrete.mk DoubleDiamondTwoCell.second)) := by
  intro isIso
  let cochain := rawDefectCochain
    finiteAxisFoldBCDatumSquare.toTransportData reselection
  letI : IsIso
      (authoredViaBasePairwiseAxisFoldComponentAtCochain
        finiteAxisFoldBCDatumSquare cochain
        (Discrete.mk DoubleDiamondTwoCell.second)) := isIso
  let fold := authoredPairwiseAxisFoldDecodedComponent
    finiteAxisFoldBCDatumSquare cochain DoubleDiamondTwoCell.second
  let transported :=
    (coreFiberTransportFunctor
      (𝟙 finiteAuthoredSupportInstance.toSemantic)).map fold
  let reindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (idTypedPresentation finiteAuthoredSupportInstance))).map transported
  letI : IsIso reindexed := by
    change IsIso
      (authoredViaBasePairwiseAxisFoldComponentAtCochain
        finiteAxisFoldBCDatumSquare cochain
        (Discrete.mk DoubleDiamondTwoCell.second))
    infer_instance
  letI : IsIso transported :=
    isIso_of_map_isIso_of_natIso_id_pairwise
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (idTypedPresentation finiteAuthoredSupportInstance)))
      (selectedCoreFiberReindexUnitor finiteAuthoredSupportInstance).symm
      transported
  letI : IsIso fold :=
    isIso_of_map_isIso_of_natIso_id_pairwise
      (coreFiberTransportFunctor
        (𝟙 finiteAuthoredSupportInstance.toSemantic))
      (coreFiberUnitor finiteAuthoredSupportInstance.toSemantic) fold
  letI : IsIso fold.1 := by
    change IsIso (CategoryTheory.Functor.Fiber.fiberInclusion.map fold)
    infer_instance
  have fold_heq : HEq fold.1
      (PackageFiberAut.generatedPairwiseAxisFoldTotalAt
        finiteAxisFoldBCDatumSquare.toTransportData cochain
        DoubleDiamondTwoCell.second) := by
    simpa only [fold] using
      (authoredPairwiseAxisFoldDecodedComponent_val_heq
        finiteAxisFoldBCDatumSquare cochain DoubleDiamondTwoCell.second)
  have fold_eq : fold.1 =
      PackageFiberAut.generatedPairwiseAxisFoldTotalAt
        finiteAxisFoldBCDatumSquare.toTransportData cochain
        DoubleDiamondTwoCell.second :=
    eq_of_heq fold_heq
  apply PackageFiberAut.generatedPairwiseAxisFoldTotalAt_not_isIso
    finiteAxisFoldBCDatumSquare.toTransportData cochain
    DoubleDiamondTwoCell.second
    (finiteAxisFold_input_pairwiseAvailable reselection)
  rw [← fold_eq]
  infer_instance

/-- Every orbit-coordinate component differs from the canonical mate. -/
theorem finiteAxisFold_pairwiseComparison_ne_canonical
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    authoredPairwiseAxisFoldComparisonComponentAtCochain
        finiteAxisFoldBCDatumSquare
        (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
          reselection)
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second) := by
  intro equality
  rw [authoredPairwiseAxisFoldComparisonComponentAtCochain_eq_canonical_comp_fold]
    at equality
  have fold_eq_id :
      authoredViaBasePairwiseAxisFoldComponentAtCochain
          finiteAxisFoldBCDatumSquare
          (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
            reselection)
          (Discrete.mk DoubleDiamondTwoCell.second) =
        𝟙 ((authoredSupportViaBaseRoute
          finiteAxisFoldBCDatumSquare.context).obj
          (Discrete.mk DoubleDiamondTwoCell.second)) := by
    apply (cancel_epi
      ((authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second))).1
    simpa using equality
  apply finiteAxisFold_viaBasePairwise_not_isIso reselection
  rw [fold_eq_id]
  infer_instance

/-- The cochain-indexed relative relation fails at every edge coordinate. -/
theorem finiteAxisFold_pairwise_not_mateCoherent
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    ¬ PairwiseAxisFoldMateCoherentAtCochain finiteAxisFoldBCDatumSquare
      (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
        reselection) := by
  apply AuthoredSupportComparison.not_agrees_of_app_ne
    (Discrete.mk DoubleDiamondTwoCell.second)
  exact finiteAxisFold_pairwiseComparison_ne_canonical reselection

/-- The relative mismatch is nonvanishing on the full G-106 orbit. -/
theorem finiteAxisFold_pairwise_not_mateCoherent_on_orbit
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (inOrbit : InReselectionOrbit
      finiteAxisFoldBCDatumSquare.toTransportData cochain) :
    ¬ PairwiseAxisFoldMateCoherentAtCochain
      finiteAxisFoldBCDatumSquare cochain := by
  rcases inOrbit with ⟨reselection, rfl⟩
  exact finiteAxisFold_pairwise_not_mateCoherent reselection

/-- The named initial-cochain relation fails on the fixed lax datum. -/
theorem finiteAxisFoldBCDatumSquare_not_pairwiseMateCoherent :
    ¬ MateCoherentRel FiniteModel.carrier
      finiteAxisFoldBCDatumSquare := by
  exact finiteAxisFold_pairwise_not_mateCoherent
    (1 : EdgeReselection finiteAxisFoldBCDatumSquare.toTransportData.lift)

/-! ## Strict positive control -/

/-- A singleton strict cochain has no moved pairwise quotient. -/
theorem finiteAuthored_pairwiseUnavailable
    (cochain : DefectCochain finiteAuthoredBCDatumSquare.toTransportData)
    (supportCell :
      finiteAuthoredBCDatumSquare.context.square.semantic.diagnostic.TwoCell) :
    ¬ PackageFiberAut.PairwiseAxisFoldAvailableAt
      finiteAuthoredBCDatumSquare.toTransportData cochain supportCell := by
  rintro ⟨witness⟩
  rcases witness with ⟨first, package_eq, fold⟩
  cases first
  cases supportCell
  have package_eq_rfl : package_eq = rfl := Subsingleton.elim _ _
  rw [package_eq_rfl] at fold
  have quotient_one :
      PackageFiberAut.pairwiseRawDefect
          finiteAuthoredBCDatumSquare.toTransportData cochain
          FiniteBCDiagnosticCell.cell FiniteBCDiagnosticCell.cell rfl = 1 := by
    simp [PackageFiberAut.pairwiseRawDefect, PackageFiberAut.castTarget]
  rw [quotient_one] at fold
  exact PackageFiberAut.not_axisFoldAvailable_one ⟨fold⟩

/-- The strict finite datum fires the same named pairwise relation. -/
theorem finiteAuthoredBCDatumSquare_pairwiseMateCoherent :
    MateCoherentRel FiniteModel.carrier
      finiteAuthoredBCDatumSquare := by
  apply pairwiseAxisFoldMateCoherentAtCochain_of_unavailable
  intro supportCell
  exact finiteAuthored_pairwiseUnavailable
    (initialRawDefectCochain finiteAuthoredBCDatumSquare.toTransportData)
    supportCell

/-! ## Nontriviality of the concrete reselection orbit -/

/-- Reselect only the right edge by the adjacent swap. -/
noncomputable def finiteAxisFoldSecondFaceReselection :
    EdgeReselection finiteAxisFoldTransportData.lift :=
  fun _ _ edge =>
    match edge with
    | .left => 1
    | .right => finiteAxisFoldSwap

/-- The explicit right-edge reselection makes the second face coherent. -/
theorem finiteAxisFold_secondFace_coherent :
    (reselectedPathLift finiteAxisFoldTransportData.lift
        finiteAxisFoldSecondFaceReselection
        ((doubleDiamondPresentation PUnit).twoLeft
          DoubleDiamondTwoCell.second)).comp
      (PackageFiberAut.hom
        (finiteAxisFoldTransportData.comparator
          DoubleDiamondTwoCell.second)) =
    reselectedPathLift finiteAxisFoldTransportData.lift
      finiteAxisFoldSecondFaceReselection
      ((doubleDiamondPresentation PUnit).twoRight
        DoubleDiamondTwoCell.second) := by
  simp only [doubleDiamondPresentation, doubleDiamondTwoPresentation,
    singleDiskLeftPath, singleDiskRightPath]
  rw [reselectedPathLift_singleEdge, reselectedPathLift_singleEdge]
  simp [reselectedEdgeLift, finiteAxisFoldSecondFaceReselection,
    finiteAxisFoldTransportData, finiteAxisFoldLiftData]
  rw [show PackageFiberAut.hom
      (1 : PackageFiberAut finiteAxisFoldSupportPackage) =
    PackageTotalHom.id finiteAxisFoldSupportPackage by rfl]
  rw [show (PackageTotalHom.id finiteAxisFoldSupportPackage).comp
        (PackageTotalHom.id finiteAxisFoldSupportPackage) =
      PackageTotalHom.id finiteAxisFoldSupportPackage from
    @Category.comp_id
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage
      (PackageTotalHom.id finiteAxisFoldSupportPackage)]

/-- The second authored comparator equals the generated comparator after reselection. -/
theorem finiteAxisFold_secondComparator_eq_canonical :
    finiteAxisFoldTransportData.comparator DoubleDiamondTwoCell.second =
      canonicalTwoCellComparator finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection DoubleDiamondTwoCell.second := by
  let left := reselectedPathLift finiteAxisFoldTransportData.lift
    finiteAxisFoldSecondFaceReselection
    ((doubleDiamondPresentation PUnit).twoLeft DoubleDiamondTwoCell.second)
  letI : (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      left.base left :=
    reselectedPathLift_isStronglyCocartesian finiteAxisFoldTransportData.lift
      finiteAxisFoldSecondFaceReselection
      ((doubleDiamondPresentation PUnit).twoLeft DoubleDiamondTwoCell.second)
  apply PackageFiberAut.ext_of_strong_fac left
  exact finiteAxisFold_secondFace_coherent.trans
    (canonicalTwoCellComparator_fac finiteAxisFoldTransportData
      finiteAxisFoldSecondFaceReselection DoubleDiamondTwoCell.second).symm

/-- The shifted raw defect on the second face is identity. -/
theorem finiteAxisFold_shiftedRawDefect_second_eq_one :
    rawTwoCellDefect finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection DoubleDiamondTwoCell.second = 1 :=
  (rawTwoCellDefect_eq_one_iff finiteAxisFoldTransportData
    finiteAxisFoldSecondFaceReselection DoubleDiamondTwoCell.second).2
      finiteAxisFold_secondComparator_eq_canonical

/-- The adjacent swap is not the identity automorphism. -/
theorem finiteAxisFoldSwap_ne_one :
    finiteAxisFoldSwap ≠ (1 : PackageFiberAut finiteAxisFoldSupportPackage) := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
  change (1 : Fin 3) = 0 at axisEquality
  exact Fin.zero_ne_one axisEquality.symm

/-- The explicit reselection produces a raw cochain different from the initial one. -/
theorem finiteAxisFold_shiftedCochain_ne_initial :
    rawDefectCochain finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection ≠
      initialRawDefectCochain finiteAxisFoldTransportData := by
  intro equality
  have secondEquality := congrFun equality DoubleDiamondTwoCell.second
  change rawTwoCellDefect finiteAxisFoldTransportData
      finiteAxisFoldSecondFaceReselection DoubleDiamondTwoCell.second =
    rawTwoCellDefect finiteAxisFoldTransportData 1
      DoubleDiamondTwoCell.second at secondEquality
  rw [finiteAxisFold_shiftedRawDefect_second_eq_one] at secondEquality
  have initialSecond := finiteAxisFold_initialRawDefect_second
  change rawTwoCellDefect finiteAxisFoldTransportData 1
      DoubleDiamondTwoCell.second = finiteAxisFoldSwap at initialSecond
  rw [initialSecond] at secondEquality
  exact finiteAxisFoldSwap_ne_one secondEquality.symm

/-- The fixed lax raw-cochain orbit has at least two distinct points. -/
theorem finiteAxisFold_reselectionOrbit_nontrivial :
    ∃ cochain : DefectCochain finiteAxisFoldTransportData,
      InReselectionOrbit finiteAxisFoldTransportData cochain ∧
        cochain ≠
          initialRawDefectCochain finiteAxisFoldTransportData := by
  exact ⟨rawDefectCochain finiteAxisFoldTransportData
      finiteAxisFoldSecondFaceReselection,
    ⟨finiteAxisFoldSecondFaceReselection, rfl⟩,
    finiteAxisFold_shiftedCochain_ne_initial⟩

/-- The same nontrivial orbit is exposed by the authored BC input. -/
theorem finiteAxisFold_input_reselectionOrbit_nontrivial :
    ∃ cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData,
      InReselectionOrbit finiteAxisFoldBCDatumSquare.toTransportData cochain ∧
        cochain ≠
          initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData := by
  simpa only [finiteAxisFold_toTransportData] using
    finiteAxisFold_reselectionOrbit_nontrivial

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
