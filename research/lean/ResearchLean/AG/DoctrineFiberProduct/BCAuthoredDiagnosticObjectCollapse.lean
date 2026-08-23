import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredObjectCollapse

/-!
# Diagnostic generation of the fixed object-collapse factor

The reviewed finite authored support has a noninvertible exact object erasure.
This module makes that factor an output of the existing G-106 raw diagnostic:
an identity raw component selects identity, while a nonidentity raw component
selects the object erasure.  The selected factor is then transported along the
actual bottom and right legs and inserted as an endomorphism of the public
authored via-base route.

Implementation notes: the branch condition is equality of the supplied raw
cochain component with the identity automorphism, so it directly consumes the
authored diagnostic rather than accepting a collapse or firing certificate.
The construction is intentionally fixed to the reviewed finite support: a
generic `AATCorePackage` has no canonical auxiliary-reading erasure.  The
earlier axis-fold alternative is not used because it is an authored twist and
the fixed target requires a genuine non-twist factor.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u₁ v₁

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteDiagnosticObjectCollapseAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Select identity on a vanishing raw component and the reviewed object
erasure on a nonvanishing component. -/
noncomputable def finiteDiagnosticObjectCollapseTotalAtCochain
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) :
    PackageTotalHom finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage := by
  classical
  exact if cochain cell = 1 then
    PackageTotalHom.id finiteAxisFoldSupportPackage
  else finiteAxisFoldEraseTotal

/-- The identity diagnostic selects the identity total factor. -/
theorem finiteDiagnosticObjectCollapseTotalAtCochain_eq_id
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) (vanishes : cochain cell = 1) :
    finiteDiagnosticObjectCollapseTotalAtCochain cochain cell =
      PackageTotalHom.id finiteAxisFoldSupportPackage := by
  simp [finiteDiagnosticObjectCollapseTotalAtCochain, vanishes]

/-- Every nonidentity diagnostic component selects the exact object erasure. -/
theorem finiteDiagnosticObjectCollapseTotalAtCochain_eq_erase
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) (fires : cochain cell ≠ 1) :
    finiteDiagnosticObjectCollapseTotalAtCochain cochain cell =
      finiteAxisFoldEraseTotal := by
  simp [finiteDiagnosticObjectCollapseTotalAtCochain, fires]

/-- A firing diagnostic component generates a noninvertible exact factor. -/
theorem finiteDiagnosticObjectCollapseTotalAtCochain_not_isIso
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) (fires : cochain cell ≠ 1) :
    ¬ IsIso (show finiteAxisFoldSupportPackage ⟶ finiteAxisFoldSupportPackage from
      finiteDiagnosticObjectCollapseTotalAtCochain cochain cell) := by
  rw [finiteDiagnosticObjectCollapseTotalAtCochain_eq_erase cochain cell fires]
  exact finiteAxisFoldEraseTotal_not_isIso

/-- Both diagnostic branches lie over the identity base map. -/
theorem finiteDiagnosticObjectCollapseTotalAtCochain_base
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) :
    (finiteDiagnosticObjectCollapseTotalAtCochain cochain cell).base =
      ExtInstHom.id (packagePoint finiteAxisFoldSupportPackage) := by
  classical
  unfold finiteDiagnosticObjectCollapseTotalAtCochain
  split <;> rfl

/-- The selected total factor lies over the southwest identity. -/
theorem finiteDiagnosticObjectCollapseTotalAtCochain_isHomLift
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) :
    (packageProjection FiniteModel.carrier).IsHomLift
      (𝟙 finiteAxisFoldBCDatumSquare.context.square.semantic.square.southwest)
      (finiteDiagnosticObjectCollapseTotalAtCochain cochain cell) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection FiniteModel.carrier)
    (𝟙 finiteAxisFoldBCDatumSquare.context.square.semantic.square.southwest)
    (finiteDiagnosticObjectCollapseTotalAtCochain cochain cell)
    (finiteAxisFoldBCDatumSquare.context.endpoint_eq cell)
    (finiteAxisFoldBCDatumSquare.context.endpoint_eq cell)
  rw [packageProjection_map,
    finiteDiagnosticObjectCollapseTotalAtCochain_base]
  rw [Category.comp_id]
  exact Category.id_comp _

/-- The generated factor as a southwest-fiber endomorphism. -/
noncomputable def finiteDiagnosticObjectCollapseComponentAtCochain
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) :
    finiteAxisFoldBCDatumSquare.context.supportObject cell ⟶
      finiteAxisFoldBCDatumSquare.context.supportObject cell :=
  ⟨finiteDiagnosticObjectCollapseTotalAtCochain cochain cell,
    finiteDiagnosticObjectCollapseTotalAtCochain_isHomLift cochain cell⟩

/-- Transport the generated non-twist factor to the public via-base route. -/
noncomputable def finiteViaBaseDiagnosticObjectCollapseComponentAtCochain
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : finiteAxisFoldBCDatumSquare.context.Category) :
    (authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj cell ⟶
      (authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj cell :=
  (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (bcRightPresentation finiteAxisFoldBCPresentation))).map
    ((coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcBottomPresentation finiteAxisFoldBCPresentation))).map
      (finiteDiagnosticObjectCollapseComponentAtCochain cochain cell.as))

/-- The identity diagnostic remains identity after transport to the via-base
route. -/
theorem finiteViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cochain_eq : cochain =
      identityDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : finiteAxisFoldBCDatumSquare.context.Category) :
    finiteViaBaseDiagnosticObjectCollapseComponentAtCochain cochain cell =
      𝟙 ((authoredSupportViaBaseRoute
        finiteAxisFoldBCDatumSquare.context).obj cell) := by
  have component_eq :
      finiteDiagnosticObjectCollapseComponentAtCochain cochain cell.as =
        𝟙 (finiteAxisFoldBCDatumSquare.context.supportObject cell.as) := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply finiteDiagnosticObjectCollapseTotalAtCochain_eq_id
    rw [congrFun cochain_eq cell.as]
    rfl
  unfold finiteViaBaseDiagnosticObjectCollapseComponentAtCochain
  rw [component_eq]
  let bottom := coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcBottomPresentation finiteAxisFoldBCPresentation))
  let right := selectedCoreFiberReindexFunctor
    (typedRealizableHom
      (bcRightPresentation finiteAxisFoldBCPresentation))
  calc
    right.map (bottom.map
        (𝟙 (finiteAxisFoldBCDatumSquare.context.supportObject cell.as))) =
      right.map (𝟙 (bottom.obj
        (finiteAxisFoldBCDatumSquare.context.supportObject cell.as))) := by
        exact congrArg right.map (bottom.map_id _)
    _ = 𝟙 (right.obj (bottom.obj
        (finiteAxisFoldBCDatumSquare.context.supportObject cell.as))) :=
      right.map_id _

/-- The fixed initial diagnostic fires the object-collapse branch at its second
face. -/
theorem finiteInitialDiagnosticObjectCollapse_second_eq_erase :
    finiteDiagnosticObjectCollapseTotalAtCochain
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        DoubleDiamondTwoCell.second = finiteAxisFoldEraseTotal := by
  apply finiteDiagnosticObjectCollapseTotalAtCochain_eq_erase
  rw [finiteAxisFold_toTransportData,
    finiteAxisFold_initialRawDefect_second]
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
  change (1 : Fin 3) = 0 at axisEquality
  exact Fin.zero_ne_one axisEquality.symm

/-- The initial diagnostic therefore generates a genuine non-twist
noninvertible factor. -/
theorem finiteInitialDiagnosticObjectCollapse_second_not_isIso :
    ¬ IsIso (show finiteAxisFoldSupportPackage ⟶ finiteAxisFoldSupportPackage from
      finiteDiagnosticObjectCollapseTotalAtCochain
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        DoubleDiamondTwoCell.second) := by
  rw [finiteInitialDiagnosticObjectCollapse_second_eq_erase]
  exact finiteAxisFoldEraseTotal_not_isIso

/-- A functor naturally isomorphic to identity reflects equality with
identity. -/
private theorem diagnosticObjectCollapse_eq_id_of_map_eq_id_of_natIso_id
    {C : Type u₁} [Category.{v₁} C] (functor : C ⥤ C)
    (unitor : functor ≅ (𝟭 C : C ⥤ C)) {object : C}
    (hom : object ⟶ object)
    (mapped_eq : functor.map hom = 𝟙 (functor.obj object)) :
    hom = 𝟙 object := by
  apply (cancel_epi (unitor.hom.app object)).1
  calc
    unitor.hom.app object ≫ hom =
        functor.map hom ≫ unitor.hom.app object :=
      (unitor.hom.naturality hom).symm
    _ = 𝟙 (functor.obj object) ≫ unitor.hom.app object := by
      rw [mapped_eq]
    _ = unitor.hom.app object ≫ 𝟙 object := by simp

/-- A generated non-twist factor remains nonidentity on the public via-base
route whenever its raw diagnostic component fires. -/
theorem finiteViaBaseDiagnosticObjectCollapseComponentAtCochain_ne_id
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) (fires : cochain cell ≠ 1) :
    finiteViaBaseDiagnosticObjectCollapseComponentAtCochain
        cochain (Discrete.mk cell) ≠
      𝟙 ((authoredSupportViaBaseRoute
        finiteAxisFoldBCDatumSquare.context).obj
          (Discrete.mk cell)) := by
  intro viaBase_eq
  let factor := finiteDiagnosticObjectCollapseComponentAtCochain
    cochain cell
  let transported :=
    (coreFiberTransportFunctor
      (𝟙 finiteAuthoredSupportInstance.toSemantic)).map factor
  let reindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (idTypedPresentation finiteAuthoredSupportInstance))).map transported
  have reindexed_eq : reindexed = 𝟙 _ := by
    change finiteViaBaseDiagnosticObjectCollapseComponentAtCochain
        cochain (Discrete.mk cell) = 𝟙 _
    exact viaBase_eq
  have transported_eq : transported = 𝟙 _ :=
    diagnosticObjectCollapse_eq_id_of_map_eq_id_of_natIso_id
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (idTypedPresentation finiteAuthoredSupportInstance)))
      (selectedCoreFiberReindexUnitor finiteAuthoredSupportInstance).symm
      transported reindexed_eq
  have factor_eq : factor = 𝟙 _ :=
    diagnosticObjectCollapse_eq_id_of_map_eq_id_of_natIso_id
      (coreFiberTransportFunctor
        (𝟙 finiteAuthoredSupportInstance.toSemantic))
      (coreFiberUnitor finiteAuthoredSupportInstance.toSemantic)
      factor transported_eq
  have total_eq := congrArg (fun component => component.1) factor_eq
  change finiteDiagnosticObjectCollapseTotalAtCochain
      cochain cell =
    PackageTotalHom.id finiteAxisFoldSupportPackage at total_eq
  rw [finiteDiagnosticObjectCollapseTotalAtCochain_eq_erase
    cochain cell fires] at total_eq
  have objectMap_eq := congrArg
    (fun total : PackageTotalHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage => total.upper.objectMap) total_eq
  change finiteAxisFoldEraseObject = _root_.id at objectMap_eq
  apply finiteAxisFoldEraseObject_not_injective
  intro first second equality
  simpa only [objectMap_eq, id_eq] using equality

/-- The initial firing face is the concrete specialization of the general
via-base nonidentity theorem. -/
theorem finiteViaBaseInitialDiagnosticObjectCollapse_second_ne_id :
    finiteViaBaseDiagnosticObjectCollapseComponentAtCochain
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      𝟙 ((authoredSupportViaBaseRoute
        finiteAxisFoldBCDatumSquare.context).obj
          (Discrete.mk DoubleDiamondTwoCell.second)) := by
  apply finiteViaBaseDiagnosticObjectCollapseComponentAtCochain_ne_id
  rw [finiteAxisFold_toTransportData,
    finiteAxisFold_initialRawDefect_second]
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
  change (1 : Fin 3) = 0 at axisEquality
  exact Fin.zero_ne_one axisEquality.symm

/-- Bridge the generated object-collapse factor into the public direct and
via-base authored-support routes. -/
noncomputable def finiteDiagnosticObjectCollapseComparisonAtCochain
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData) :
    authoredSupportDirectRoute finiteAxisFoldBCDatumSquare.context ⟶
      authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context :=
  authoredComparisonOfComponents (fun cell =>
    (authoredSupportCanonicalMate
      finiteAxisFoldBCDatumSquare.context).app cell ≫
      finiteViaBaseDiagnosticObjectCollapseComponentAtCochain cochain cell)

/-- The public comparison exposes the diagnostic-selected non-twist factor in
canonical-then-factor order. -/
@[simp]
theorem finiteDiagnosticObjectCollapseComparisonAtCochain_app
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : finiteAxisFoldBCDatumSquare.context.Category) :
    (finiteDiagnosticObjectCollapseComparisonAtCochain cochain).app cell =
      (authoredSupportCanonicalMate
        finiteAxisFoldBCDatumSquare.context).app cell ≫
        finiteViaBaseDiagnosticObjectCollapseComponentAtCochain cochain cell :=
  rfl

/-- A firing component makes the generated public comparison differ from the
canonical mate at that component. -/
theorem finiteDiagnosticObjectCollapseComparisonAtCochain_app_ne_canonical
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit) (fires : cochain cell ≠ 1) :
    (finiteDiagnosticObjectCollapseComparisonAtCochain cochain).app
        (Discrete.mk cell) ≠
      (authoredSupportCanonicalMate
        finiteAxisFoldBCDatumSquare.context).app (Discrete.mk cell) := by
  intro equality
  have factor_eq :
      finiteViaBaseDiagnosticObjectCollapseComponentAtCochain
          cochain (Discrete.mk cell) = 𝟙 _ := by
    apply (cancel_epi
      ((authoredSupportCanonicalMate
        finiteAxisFoldBCDatumSquare.context).app (Discrete.mk cell))).1
    simpa using equality
  exact finiteViaBaseDiagnosticObjectCollapseComponentAtCochain_ne_id
    cochain cell fires factor_eq

/-- Identity raw data makes the generated non-twist comparison canonical. -/
theorem finiteDiagnosticObjectCollapseComparisonAtCochain_identity_eq_canonical :
    finiteDiagnosticObjectCollapseComparisonAtCochain
        (identityDefectCochain
          finiteAxisFoldBCDatumSquare.toTransportData) =
      authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context := by
  apply CategoryTheory.NatTrans.ext
  apply funext
  intro cell
  rw [finiteDiagnosticObjectCollapseComparisonAtCochain_app,
    finiteViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id
      (identityDefectCochain
        finiteAxisFoldBCDatumSquare.toTransportData) rfl cell]
  simp

/-- Relative canonicity of the diagnostic-generated object-collapse comparison
at a supplied raw cochain. -/
def FiniteDiagnosticObjectCollapseMateCoherentAtCochain
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData) : Prop :=
  AuthoredSupportComparison.Agrees
    (finiteDiagnosticObjectCollapseComparisonAtCochain cochain)
    (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context)

/-- Positive predicate instance at the independent identity cochain. -/
theorem finiteDiagnosticObjectCollapse_identity_mateCoherent :
    FiniteDiagnosticObjectCollapseMateCoherentAtCochain
      (identityDefectCochain
        finiteAxisFoldBCDatumSquare.toTransportData) :=
  finiteDiagnosticObjectCollapseComparisonAtCochain_identity_eq_canonical

/-- The non-twist comparison mismatch survives the full genuine G-106
reselection orbit. -/
theorem finiteDiagnosticObjectCollapse_not_mateCoherent_on_orbit
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (inOrbit : InReselectionOrbit
      finiteAxisFoldBCDatumSquare.toTransportData cochain) :
    ¬ FiniteDiagnosticObjectCollapseMateCoherentAtCochain cochain := by
  rcases inOrbit with ⟨reselection, rfl⟩
  have cochain_ne :
      rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection ≠
        identityDefectCochain finiteAxisFoldBCDatumSquare.toTransportData := by
    intro equality
    apply finiteAxisFold_not_coherentizable
    exact ⟨reselection,
      (coherentAt_iff_rawDefectCochain_eq_identity
        finiteAxisFoldBCDatumSquare.toTransportData reselection).2 equality⟩
  have fires : ∃ cell,
      rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
        reselection cell ≠ 1 := by
    by_contra none
    apply cochain_ne
    funext cell
    by_contra component_ne
    exact none ⟨cell, component_ne⟩
  rcases fires with ⟨cell, fires⟩
  apply AuthoredSupportComparison.not_agrees_of_app_ne (Discrete.mk cell)
  exact finiteDiagnosticObjectCollapseComparisonAtCochain_app_ne_canonical
    (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection)
    cell fires

/-- The initial authored diagnostic generates the named public comparison. -/
noncomputable def finiteGeneratedDiagnosticObjectCollapseComparison :
    authoredSupportDirectRoute finiteAxisFoldBCDatumSquare.context ⟶
      authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context :=
  finiteDiagnosticObjectCollapseComparisonAtCochain
    (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)

/-- The generated public comparison is genuinely noncanonical at the firing
face. -/
theorem finiteGeneratedDiagnosticObjectCollapseComparison_second_ne_canonical :
    finiteGeneratedDiagnosticObjectCollapseComparison.app
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      (authoredSupportCanonicalMate
        finiteAxisFoldBCDatumSquare.context).app
          (Discrete.mk DoubleDiamondTwoCell.second) := by
  intro equality
  exact finiteDiagnosticObjectCollapseComparisonAtCochain_app_ne_canonical
    (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    DoubleDiamondTwoCell.second (by
      rw [finiteAxisFold_toTransportData,
        finiteAxisFold_initialRawDefect_second]
      intro swap_eq
      have axisEquality := congrArg
        (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
          (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) swap_eq
      change (1 : Fin 3) = 0 at axisEquality
      exact Fin.zero_ne_one axisEquality.symm) equality

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
