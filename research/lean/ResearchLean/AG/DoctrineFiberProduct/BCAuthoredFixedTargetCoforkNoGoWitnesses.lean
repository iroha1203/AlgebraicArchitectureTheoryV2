import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredFixedTargetQuotientNoGo

/-!
# Finite Cofork nonexistence at the authored fixed target

The fixed lax double-diamond residual has a stronger obstruction than the
conditional return-map barrier.  Its adjacent transposition fixes signature
axis `2` while acting there by a nonidentity coordinate equivalence.  Every
exact-core morphism carries an equivalence on that coordinate, so no arrow out
of the support object can coequalize the residual with identity.

The identity-like transport and reindex functors preserve this nonexistence.
Consequently no standard `Cofork` of the transported residual and identity
exists on the authored via-base route.  This rules out the attempted generated
Cofork construction for the reviewed finite datum; it is not a global
nonexistence theorem for quotient categories with weaker morphisms.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory CategoryTheory.Limits
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteCoforkNoGoAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- A functor naturally isomorphic to identity preserves nonexistence of a
coequalizing arrow for an endomorphism. -/
private theorem no_coequalizing_arrow_map_of_natIso_id
    {C : Type u} [Category.{v} C] (functor : C ⥤ C)
    (unitor : functor ≅ 𝟭 C) {X : C} (action : X ⟶ X)
    (noArrow : ∀ {Q : C} (π : X ⟶ Q), action ≫ π = π → False) :
    ∀ {Q : C} (π : functor.obj X ⟶ Q),
      functor.map action ≫ π = π → False := by
  intro Q π condition
  apply noArrow (unitor.inv.app X ≫ π)
  calc
    action ≫ (unitor.inv.app X ≫ π) =
        (action ≫ unitor.inv.app X) ≫ π := by simp
    _ = (unitor.inv.app X ≫ functor.map action) ≫ π := by
      rw [show action ≫ unitor.inv.app X =
          unitor.inv.app X ≫ functor.map action by
        simpa using unitor.inv.naturality action]
    _ = unitor.inv.app X ≫ (functor.map action ≫ π) := by simp
    _ = unitor.inv.app X ≫ π := by rw [condition]

/--
No exact-core arrow out of the finite support object coequalizes its actual
G-106 raw residual with identity.  The contradiction occurs on the residual's
fixed axis `2`, where its coordinate action is the nontrivial adjacent swap.
-/
theorem finiteAxisFold_initialRawDefect_no_coequalizing_arrow
    {Q : CoreFiber finiteAuthoredSupportInstance.toSemantic}
    (π : finiteAxisFoldBCDatumSquare.context.supportObject
        DoubleDiamondTwoCell.second ⟶ Q)
    (condition :
      authoredInitialRawDefectComponent finiteAxisFoldBCDatumSquare
          DoubleDiamondTwoCell.second ≫ π = π) : False := by
  have initial_eq :
      initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
          DoubleDiamondTwoCell.second = finiteAxisFoldSwap := by
    simpa only [finiteAxisFold_toTransportData] using
      finiteAxisFold_initialRawDefect_second
  have raw_total_eq :
      (authoredInitialRawDefectComponent finiteAxisFoldBCDatumSquare
          DoubleDiamondTwoCell.second).1 = finiteAxisFoldSwapTotal := by
    change PackageFiberAut.hom
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
          DoubleDiamondTwoCell.second) = finiteAxisFoldSwapTotal
    rw [initial_eq]
    rfl
  have coordinate_heq : HEq
      ((authoredInitialRawDefectComponent finiteAxisFoldBCDatumSquare
          DoubleDiamondTwoCell.second ≫ π).1.upper.coordinateEquiv (2 : Fin 3))
      (π.1.upper.coordinateEquiv (2 : Fin 3)) := by
    rw [condition]
  change HEq
      (((authoredInitialRawDefectComponent finiteAxisFoldBCDatumSquare
          DoubleDiamondTwoCell.second).1.comp π.1).upper.coordinateEquiv
        (2 : Fin 3))
      (π.1.upper.coordinateEquiv (2 : Fin 3)) at coordinate_heq
  rw [raw_total_eq] at coordinate_heq
  change HEq
      ((Equiv.swap (0 : Fin 3) 1).trans
        (π.1.upper.coordinateEquiv (2 : Fin 3)))
      (π.1.upper.coordinateEquiv (2 : Fin 3)) at coordinate_heq
  have coordinate_eq := eq_of_heq coordinate_heq
  have point_eq := congrArg (fun equivalence => equivalence (0 : Fin 3))
    coordinate_eq
  simp at point_eq

/--
There is no standard Cofork of the fixed transported residual and identity.
Thus the Cycle 48 conditional Cofork theorem is vacuous on this exact finite
target, and the proposed generated-Cofork route cannot supply K2 here.
-/
theorem finiteAxisFold_viaBaseRawDefect_no_cofork :
    ¬ Nonempty (Cofork
      (authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second))
      (𝟙 ((authoredSupportViaBaseRoute
        finiteAxisFoldBCDatumSquare.context).obj
          (Discrete.mk DoubleDiamondTwoCell.second)))) := by
  rintro ⟨cofork⟩
  let support := finiteAxisFoldBCDatumSquare.context.supportObject
    DoubleDiamondTwoCell.second
  let raw := authoredInitialRawDefectComponent finiteAxisFoldBCDatumSquare
    DoubleDiamondTwoCell.second
  let transport := coreFiberTransportFunctor
    (𝟙 finiteAuthoredSupportInstance.toSemantic)
  let reindex := selectedCoreFiberReindexFunctor
    (typedRealizableHom
      (idTypedPresentation finiteAuthoredSupportInstance))
  have noSupport : ∀ {Q} (π : support ⟶ Q), raw ≫ π = π → False := by
    intro Q π condition
    exact finiteAxisFold_initialRawDefect_no_coequalizing_arrow π condition
  have noTransport : ∀ {Q} (π : transport.obj support ⟶ Q),
      transport.map raw ≫ π = π → False :=
    no_coequalizing_arrow_map_of_natIso_id transport
      (coreFiberUnitor finiteAuthoredSupportInstance.toSemantic)
      raw noSupport
  have noReindex : ∀ {Q} (π : reindex.obj (transport.obj support) ⟶ Q),
      reindex.map (transport.map raw) ≫ π = π → False :=
    no_coequalizing_arrow_map_of_natIso_id reindex
      (selectedCoreFiberReindexUnitor finiteAuthoredSupportInstance).symm
      (transport.map raw) noTransport
  apply noReindex cofork.π
  change reindex.map (transport.map raw) ≫ cofork.π = cofork.π
  simpa using cofork.condition

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
