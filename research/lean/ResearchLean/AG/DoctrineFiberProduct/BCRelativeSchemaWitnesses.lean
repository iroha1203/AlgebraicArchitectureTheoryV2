import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchema
import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchemaWitnesses

/-!
# Finite witnesses for authored-support relative signatures

The main witness transports the reviewed finite core package to a decoded
finite-code instance, builds an identity BC cospan on that instance, and places
one nonempty G-106 diagnostic 2-cell over the square's southwest vertex.  It
therefore exercises the endpoint-incidence field rather than leaving support
empty.  The raw identity comparator is then read back as the component of the
generated discrete natural transformation.

A separate two-element function witness gives positive and negative instances
of the comparison-agreement predicate.  It tests the equality predicate itself;
the K2 strict/lax `MateCoherentRel` pair remains a later theorem obligation.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

/-- Executable equality for the concrete finite Atom carrier. -/
local instance finiteBCRelativeCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## A nonempty authored support over a finite-code square -/

/-- The finite-code point corresponding to the reviewed package's selected source. -/
def finiteAuthoredSupportInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteModelDoctrineCode
  point := ULift.up (1 : Fin 2)

/-- Transport the reviewed package to the exact decoded finite-code doctrine. -/
noncomputable def finiteAuthoredSupportPackage :
    AATCorePackage FiniteModel.carrier :=
  transportAlong FiniteModel.corePackage finiteModelDoctrineFromFixture

/-- The transported package lands at the selected finite-code point. -/
theorem finiteAuthoredSupportPackage_point :
    (packageProjection FiniteModel.carrier).obj finiteAuthoredSupportPackage =
      finiteAuthoredSupportInstance.toSemantic := by
  rfl

/-- Identity cospan on the decoded instance used to generate the BC square. -/
def finiteAuthoredSupportCospan :
    CartCospanPresentation FiniteModel.carrier where
  firstSource := finiteAuthoredSupportInstance
  secondSource := finiteAuthoredSupportInstance
  base := finiteAuthoredSupportInstance
  first := idTypedPresentation finiteAuthoredSupportInstance
  second := idTypedPresentation finiteAuthoredSupportInstance

/-- Generated finite-code BC presentation with one nonempty diagnostic cell. -/
def finiteAuthoredSupportBCPresentation : BCPresentation FiniteModel.carrier :=
  bcPresentationOfCospan finiteAuthoredSupportCospan
    finiteBCDiagnosticPresentation

/-- Canonical realization provenance for the generated identity square. -/
noncomputable def finiteAuthoredSupportSquare :
    RealizableSquare FiniteModel.carrier :=
  realizableSquareOf finiteAuthoredSupportBCPresentation

/-- Identity package lift on every edge of the singleton diagnostic geometry. -/
noncomputable def finiteAuthoredSupportLiftData :
    AdmissibleLiftData finiteBCDiagnosticGeometry FiniteModel.carrier where
  package := fun _ => finiteAuthoredSupportPackage
  edgeLift := fun _ => PackageTotalHom.id finiteAuthoredSupportPackage
  edgeStrong := by
    intro source target edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 (packagePoint finiteAuthoredSupportPackage))
        (Iso.refl finiteAuthoredSupportPackage).hom :=
      CategoryTheory.IsHomLift.id rfl
    simpa using
      (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
        (packageProjection FiniteModel.carrier)
        (𝟙 (packagePoint finiteAuthoredSupportPackage))
        (Iso.refl finiteAuthoredSupportPackage))

/-- G-106 datum with the identity authored comparator on the nonempty cell. -/
noncomputable def finiteAuthoredSupportTransportData :
    AdmissibleTransportData finiteBCDiagnosticGeometry FiniteModel.carrier where
  lift := finiteAuthoredSupportLiftData
  twoCellBase := by
    intro face
    cases face
    change (PackageTotalHom.id finiteAuthoredSupportPackage).base =
      ((PackageTotalHom.id finiteAuthoredSupportPackage).comp
        (PackageTotalHom.id finiteAuthoredSupportPackage)).base
    rw [show (PackageTotalHom.id finiteAuthoredSupportPackage).comp
        (PackageTotalHom.id finiteAuthoredSupportPackage) =
      PackageTotalHom.id finiteAuthoredSupportPackage by
        exact @Category.comp_id
          (AATCorePackage FiniteModel.carrier)
          (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
          finiteAuthoredSupportPackage finiteAuthoredSupportPackage
          (PackageTotalHom.id finiteAuthoredSupportPackage)]
  comparator := fun _ => 1

/-- The concrete G-106 datum interpreted on the generated square diagnostic. -/
noncomputable def finiteAuthoredSupportInterpretation :
    BCDiagnosticInterpretation FiniteModel.carrier
      finiteAuthoredSupportSquare.semantic where
  data := by
    simpa [finiteAuthoredSupportSquare, realizableSquareOf,
      finiteAuthoredSupportBCPresentation, bcPresentationOfCospan,
      toSemanticBC, finiteBCDiagnosticPresentation] using
        finiteAuthoredSupportTransportData

/-- Every concrete authored endpoint is exactly the square's southwest vertex. -/
theorem finiteAuthoredSupport_endpoint_eq
    (face : finiteAuthoredSupportSquare.semantic.diagnostic.TwoCell) :
    (packageProjection FiniteModel.carrier).obj
        (finiteAuthoredSupportInterpretation.data.lift.package
          (finiteAuthoredSupportSquare.semantic.diagnostic.twoTarget face)) =
      finiteAuthoredSupportSquare.semantic.square.southwest := by
  cases face
  rfl

/-- The nonempty finite authored-datum square inhabits the F0b2b domain. -/
noncomputable def finiteAuthoredBCDatumSquare :
    AuthoredBCDatumSquare FiniteModel.carrier :=
  AuthoredBCDatumSquare.ofInterpretation finiteAuthoredSupportSquare
    finiteAuthoredSupportInterpretation finiteAuthoredSupport_endpoint_eq

/-- The fixed discrete support contains the concrete diagnostic 2-cell. -/
theorem finiteAuthoredSupport_nonempty :
    Nonempty finiteAuthoredBCDatumSquare.context.Category :=
  ⟨Discrete.mk FiniteBCDiagnosticCell.cell⟩

/-- The raw comparator field is the actual endpoint natural-family component. -/
theorem finiteAuthoredEndpointAutomorphism_component :
    (finiteAuthoredBCDatumSquare.endpointAutomorphism.app
        (Discrete.mk FiniteBCDiagnosticCell.cell)).1 =
      PackageTotalHom.id finiteAuthoredSupportPackage := by
  rfl

/-- The all-identity raw table generates the identity support endotransformation. -/
theorem finiteAuthoredEndpointAutomorphism_eq_identity :
    finiteAuthoredBCDatumSquare.endpointAutomorphism =
      𝟙 finiteAuthoredBCDatumSquare.context.supportFunctor := by
  ext support
  rcases support with ⟨face⟩
  cases face
  rfl

/-! ## Positive and negative agreement instances -/

/-- One tagged Boolean object for a direct equality-predicate instance pair. -/
def finiteAgreementFunctor : Discrete PUnit ⥤ Type :=
  Discrete.functor (fun _ => Bool)

/-- Identity component family on the tagged Boolean object. -/
def finiteAgreementIdentity : finiteAgreementFunctor ⟶ finiteAgreementFunctor :=
  Discrete.natTrans (fun _ => id)

/-- Nonidentity Boolean-negation component on the same domain and codomain. -/
def finiteAgreementNegation : finiteAgreementFunctor ⟶ finiteAgreementFunctor :=
  Discrete.natTrans (fun _ => Bool.not)

/-- The agreement predicate has a concrete positive instance. -/
theorem finiteAgreement_positive :
    AuthoredSupportComparison.Agrees
      finiteAgreementIdentity finiteAgreementIdentity :=
  AuthoredSupportComparison.agrees_self finiteAgreementIdentity

/-- The agreement predicate has a concrete negative instance. -/
theorem finiteAgreement_negative :
    ¬ AuthoredSupportComparison.Agrees
      finiteAgreementIdentity finiteAgreementNegation := by
  apply AuthoredSupportComparison.not_agrees_of_app_ne
    (Discrete.mk PUnit.unit)
  intro hequality
  have hfalse := congrArg (fun function : Bool → Bool => function false) hequality
  exact Bool.noConfusion hfalse

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
