import ResearchLean.AG.DoctrineFiberProduct.FiniteModelRealizationULift

/-!
# Finite witnesses for the realization-compatible universe lift

This module instantiates the decoder-level bridge on the noninvertible
selective-two arrow followed by its finite-code support bridge.  The resulting
realized arrow is the exact prefix of the already reviewed generated arrow to
`FiniteModel.corePackage`, and its canonical universe lift still identifies
two distinct source cells.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- Executable Atom equality on the universe-zero finite carrier. -/
local instance finiteModelRealizationWitnessAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom :=
  finiteModelRealizationULiftAtomDecidableEq

/-- The selective-two arrow composed with the exact finite-code support bridge. -/
def finiteSelectiveTwoToSupportPresentation :
    CartPresentationBetween finiteSelectiveTwoInstance
      finitePortfolioSupportInstance :=
  compPresentation finiteSelectiveTwoToOnePresentation
    finiteSelectiveOneToSupportPresentation

/-- The exact realized prefix ending at the finite-code support endpoint. -/
def finiteSelectiveTwoToSupportInput : RealizableHom FiniteModel.carrier :=
  realizableHomOf finiteSelectiveTwoToSupportPresentation.toPresentation

/-- The realized prefix hom is the categorical composite of its two code legs. -/
theorem finiteSelectiveTwoToSupportInput_hom :
    finiteSelectiveTwoToSupportInput.semantic.hom =
      finiteSelectiveTwoInput.semantic.hom ≫
        finiteSelectiveOneToSupportInput.semantic.hom := by
  exact toSemanticCart_compPresentation_hom
    finiteSelectiveTwoToOnePresentation finiteSelectiveOneToSupportPresentation

/-- Appending the reviewed code-to-fixture bridge gives the generated core arrow. -/
theorem finiteSelectiveTwoToSupportInput_comp_core :
    finiteSelectiveTwoToSupportInput.semantic.hom ≫
        finitePortfolioSupportToCoreHom =
      finiteSelectiveTwoGeneratedLiftInput.hom := by
  rw [finiteSelectiveTwoToSupportInput_hom]
  rfl

/-- The two selected low source cells remain distinct in the composite presentation. -/
theorem finiteSelectiveTwoToSupport_source_points_ne :
    finiteSelectiveTwoPoint ≠ finiteSelectiveTwoOther := by
  intro equality
  have hdown : (0 : Fin 2) = 1 := by
    simpa [finiteSelectiveTwoPoint, finiteSelectiveTwoOther,
      finiteSelectiveDoctrineCode] using congrArg ULift.down equality
  have hne : (0 : Fin 2) ≠ 1 := by decide
  exact hne hdown

/-- The realized support-prefix arrow still identifies the two distinct source cells. -/
theorem finiteSelectiveTwoToSupport_sourceMap_eq :
    finiteSelectiveTwoToSupportInput.semantic.hom.doctrineHom.sourceMap
        finiteSelectiveTwoPoint =
      finiteSelectiveTwoToSupportInput.semantic.hom.doctrineHom.sourceMap
        finiteSelectiveTwoOther := by
  rfl

/-- The realized support-prefix arrow is genuinely noninvertible. -/
theorem finiteSelectiveTwoToSupportInput_not_isIso :
    ¬ IsIso finiteSelectiveTwoToSupportInput.semantic.hom := by
  intro hiso
  letI : IsIso finiteSelectiveTwoToSupportInput.semantic.hom := hiso
  exact finiteSelectiveTwoToSupport_source_points_ne
    (extInstHom_sourceMap_injective_of_isIso
      finiteSelectiveTwoToSupportInput.semantic.hom
      finiteSelectiveTwoToSupport_sourceMap_eq)

/-- Rebase the concrete realized prefix to an arbitrary universe. -/
def finiteSelectiveTwoToSupportLiftedInput :
    RealizableHom finiteModelLiftCarrier.{u} :=
  finiteModelLiftRealizableHom.{u} finiteSelectiveTwoToSupportInput

/-- The concrete semantic-input bridge is generated from the realized prefix. -/
def finiteSelectiveTwoToSupportSemanticIso :
    CartSemanticInputIso
      (finiteModelLiftSemanticInput.{u}
        finiteSelectiveTwoToSupportInput.semantic)
      finiteSelectiveTwoToSupportLiftedInput.{u}.semantic :=
  finiteModelLiftRealizableHomSemanticIso.{u}
    finiteSelectiveTwoToSupportInput

/-- The source isomorphism sends the first nested lift to the rebased first cell. -/
@[simp]
theorem finiteSelectiveTwoToSupportSemanticIso_source_first :
    finiteSelectiveTwoToSupportSemanticIso.{u}.sourceIso.hom.doctrineHom.sourceMap
        (ULift.up finiteSelectiveTwoPoint) =
      finiteSourceRebaseEquiv.{0, u} 2 finiteSelectiveTwoPoint :=
  rfl

/-- The source isomorphism sends the second nested lift to the rebased second cell. -/
@[simp]
theorem finiteSelectiveTwoToSupportSemanticIso_source_other :
    finiteSelectiveTwoToSupportSemanticIso.{u}.sourceIso.hom.doctrineHom.sourceMap
        (ULift.up finiteSelectiveTwoOther) =
      finiteSourceRebaseEquiv.{0, u} 2 finiteSelectiveTwoOther :=
  rfl

/-- The generated source and target isomorphisms make the concrete lower square commute. -/
theorem finiteSelectiveTwoToSupportSemanticIso_hom_comm :
    finiteSelectiveTwoToSupportSemanticIso.{u}.sourceIso.hom ≫
        finiteSelectiveTwoToSupportLiftedInput.{u}.semantic.hom =
      (finiteModelLiftSemanticInput.{u}
          finiteSelectiveTwoToSupportInput.semantic).hom ≫
        finiteSelectiveTwoToSupportSemanticIso.{u}.targetIso.hom :=
  finiteSelectiveTwoToSupportSemanticIso.{u}.hom_comm

/-- The two rebased source cells remain distinct at every target universe. -/
theorem finiteSelectiveTwoToSupport_lifted_source_points_ne :
    finiteSourceRebaseEquiv.{0, u} 2 finiteSelectiveTwoPoint ≠
      finiteSourceRebaseEquiv.{0, u} 2 finiteSelectiveTwoOther := by
  exact (finiteSourceRebaseEquiv.{0, u} 2).injective.ne
    finiteSelectiveTwoToSupport_source_points_ne

/-- The lifted realized arrow identifies the two rebased source cells. -/
theorem finiteSelectiveTwoToSupport_lifted_sourceMap_eq :
    finiteSelectiveTwoToSupportLiftedInput.{u}.semantic.hom.doctrineHom.sourceMap
        (finiteSourceRebaseEquiv.{0, u} 2 finiteSelectiveTwoPoint) =
      finiteSelectiveTwoToSupportLiftedInput.{u}.semantic.hom.doctrineHom.sourceMap
        (finiteSourceRebaseEquiv.{0, u} 2 finiteSelectiveTwoOther) := by
  rfl

/-- The canonically lifted realized prefix remains genuinely noninvertible. -/
theorem finiteSelectiveTwoToSupportLiftedInput_not_isIso :
    ¬ IsIso finiteSelectiveTwoToSupportLiftedInput.{u}.semantic.hom := by
  intro hiso
  letI : IsIso finiteSelectiveTwoToSupportLiftedInput.{u}.semantic.hom := hiso
  exact finiteSelectiveTwoToSupport_lifted_source_points_ne.{u}
    (extInstHom_sourceMap_injective_of_isIso
      finiteSelectiveTwoToSupportLiftedInput.{u}.semantic.hom
      finiteSelectiveTwoToSupport_lifted_sourceMap_eq.{u})

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
