import ResearchLean.AG.RealizationReconstruction.AATClosedFamilySignature
import ResearchLean.AG.RealizationReconstruction.CSAATIndependentPackageCategories
import ResearchLean.AG.RealizationReconstruction.CSAATGeometryAxisVarianceCounterexample
import ResearchLean.AG.RealizationReconstruction.MandatoryCExplicitExactGeometryObstruction
import Formal.Util.AssertStandardAxioms

/-!
# One closed family of decoder-independent realization categories

The four mandatory parameter branches already share the independently defined
`ClosedFamilyParameter`.  This module equips every one of its fibers with the
corresponding decoder-independent morphism type: explicit exact geometry on
the fixed mandatory-C object, all original-cell geometry morphisms for G-122,
and the independent named-operation package morphisms for both CS models.

The construction includes the fixed uniform flip and arbitrary noninvertible
CS morphisms.  It does not yet define the final uniform data condition
`D_Theta`: the four branch laws remain the previously constructed laws, and
their comparison with one common final preservation interface is a subsequent
obligation.  No presentation, decoder image, splitting, or retract condition
occurs in the object or morphism types below.

## Implementation notes

The category is indexed by the already closed parameter instead of taking four
completed categories as fields of a certificate.  Dependent elimination on
the parameter recovers the original object and morphism types definitionally.
In particular, the CS branches retain arbitrary carrier maps rather than being
coerced into the equivalence-valued exact-geometry interface.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v

/-- Decoder-independent morphisms in the tagged-operation fiber. -/
def TaggedFamilyRealizationHom :
    FamilyRealization.{u, v} (ClosedFamilyParameter.taggedOperation :
      ClosedFamilyParameter.{u, v}) →
      FamilyRealization.{u, v} .taggedOperation →
        Type (max (u + 1) (v + 1))
  | .taggedOperation, .taggedOperation =>
      ULift.{max (u + 1) (v + 1)}
        (ExplicitExactGeometryHom taggedOperationGeometryPackage
          taggedOperationGeometryPackage)

/-- Decoder-independent morphisms in one original G-122 input fiber. -/
def G122FamilyRealizationHom (input : G122FamilyInput.{u, v}) :
    FamilyRealization.{u, v} (.g122 input) →
      FamilyRealization.{u, v} (.g122 input) →
      Type (max (u + 1) (v + 1))
  | .g122 source, .g122 target =>
      ULift.{v + 1}
        (G122CellInput.G122OriginalCellGeometryHom input source target)

/-- Decoder-independent morphisms in one lens parameter fiber. -/
def LensFamilyRealizationHom (input : LensFamilyInput.{u}) :
    FamilyRealization.{u, v} (.lens input) →
      FamilyRealization.{u, v} (.lens input) →
        Type (max (u + 1) (v + 1))
  | .lens source, .lens target =>
      ULift.{max (u + 1) (v + 1)}
        (LensAATIndependentGeneratedPackageHom input source target)

/-- Decoder-independent morphisms in one protocol parameter fiber. -/
def ProtocolFamilyRealizationHom (input : ProtocolFamilyInput.{u}) :
    FamilyRealization.{u, v} (.protocol input) →
      FamilyRealization.{u, v} (.protocol input) →
        Type (max (u + 1) (v + 1))
  | .protocol source, .protocol target =>
      ULift.{max (u + 1) (v + 1)}
        (ProtocolAATIndependentGeneratedPackageHom input source target)

/-- Decoder-independent morphisms in one fixed closed-family fiber. -/
def ClosedFamilyRealizationHom {theta : ClosedFamilyParameter.{u, v}} :
    FamilyRealization.{u, v} theta → FamilyRealization.{u, v} theta →
      Type (max (u + 1) (v + 1)) :=
  match theta with
  | .taggedOperation => TaggedFamilyRealizationHom
  | .g122 input => G122FamilyRealizationHom input
  | .lens input => LensFamilyRealizationHom input
  | .protocol input => ProtocolFamilyRealizationHom input

/-- Identity morphism in each closed-family fiber. -/
noncomputable def ClosedFamilyRealizationHom.id :
    {theta : ClosedFamilyParameter.{u, v}} →
      (X : FamilyRealization theta) → ClosedFamilyRealizationHom X X
  | .taggedOperation, .taggedOperation =>
      ULift.up (ExplicitExactGeometryHom.id taggedOperationGeometryPackage)
  | .g122 input, .g122 X =>
      ULift.up (G122CellInput.G122OriginalCellGeometryHom.id input X)
  | .lens _, .lens X =>
      ULift.up (LensAATIndependentGeneratedPackageHom.id X)
  | .protocol _, .protocol X =>
      ULift.up (ProtocolAATIndependentGeneratedPackageHom.id X)

/-- Composition uses the independently proved composition of the selected
branch and never changes the common parameter. -/
noncomputable def ClosedFamilyRealizationHom.comp :
    {theta : ClosedFamilyParameter.{u, v}} →
      {X Y Z : FamilyRealization theta} →
      ClosedFamilyRealizationHom X Y → ClosedFamilyRealizationHom Y Z →
        ClosedFamilyRealizationHom X Z
  | .taggedOperation, .taggedOperation, .taggedOperation, .taggedOperation,
      first, second =>
      ULift.up (ExplicitExactGeometryHom.comp first.down second.down)
  | .g122 input, .g122 _, .g122 _, .g122 _, first, second =>
      ULift.up (G122CellInput.G122OriginalCellGeometryHom.comp input
        first.down second.down)
  | .lens _, .lens _, .lens _, .lens _, first, second =>
      ULift.up (LensAATIndependentGeneratedPackageHom.comp first.down second.down)
  | .protocol _, .protocol _, .protocol _, .protocol _, first, second =>
      ULift.up (ProtocolAATIndependentGeneratedPackageHom.comp
        first.down second.down)

/-- Every fixed parameter has one category of independently quantified
realizations and all morphisms admitted by its branch law. -/
noncomputable instance closedFamilyRealizationCategory
    (theta : ClosedFamilyParameter.{u, v}) : Category (FamilyRealization theta) where
  Hom := ClosedFamilyRealizationHom
  id := ClosedFamilyRealizationHom.id
  comp := ClosedFamilyRealizationHom.comp
  id_comp := by
    intro X Y f
    cases theta with
    | taggedOperation =>
        cases X
        cases Y
        apply ULift.ext
        exact ExplicitExactGeometryHom.id_comp f.down
    | g122 input =>
        cases X with
        | g122 source =>
          cases Y with
          | g122 target =>
            apply ULift.ext
            exact G122CellInput.G122OriginalCellGeometryHom.id_comp input f.down
    | lens input =>
        cases X with
        | lens source =>
          cases Y with
          | lens target =>
            apply ULift.ext
            apply LensAATIndependentGeneratedPackageHom.ext
            rfl
    | protocol input =>
        cases X with
        | protocol source =>
          cases Y with
          | protocol target =>
            apply ULift.ext
            apply ProtocolAATIndependentGeneratedPackageHom.ext
            rfl
  comp_id := by
    intro X Y f
    cases theta with
    | taggedOperation =>
        cases X
        cases Y
        apply ULift.ext
        exact ExplicitExactGeometryHom.comp_id f.down
    | g122 input =>
        cases X with
        | g122 source =>
          cases Y with
          | g122 target =>
            apply ULift.ext
            exact G122CellInput.G122OriginalCellGeometryHom.comp_id input f.down
    | lens input =>
        cases X with
        | lens source =>
          cases Y with
          | lens target =>
            apply ULift.ext
            apply LensAATIndependentGeneratedPackageHom.ext
            rfl
    | protocol input =>
        cases X with
        | protocol source =>
          cases Y with
          | protocol target =>
            apply ULift.ext
            apply ProtocolAATIndependentGeneratedPackageHom.ext
            rfl
  assoc := by
    intro W X Y Z f g h
    cases theta with
    | taggedOperation =>
        cases W
        cases X
        cases Y
        cases Z
        apply ULift.ext
        exact ExplicitExactGeometryHom.comp_assoc f.down g.down h.down
    | g122 input =>
        cases W with
        | g122 first =>
          cases X with
          | g122 second =>
            cases Y with
            | g122 third =>
              cases Z with
              | g122 fourth =>
                apply ULift.ext
                exact G122CellInput.G122OriginalCellGeometryHom.comp_assoc
                  input f.down g.down h.down
    | lens input =>
        cases W with
        | lens first =>
          cases X with
          | lens second =>
            cases Y with
            | lens third =>
              cases Z with
              | lens fourth =>
                apply ULift.ext
                apply LensAATIndependentGeneratedPackageHom.ext
                rfl
    | protocol input =>
        cases W with
        | protocol first =>
          cases X with
          | protocol second =>
            cases Y with
            | protocol third =>
              cases Z with
              | protocol fourth =>
                apply ULift.ext
                apply ProtocolAATIndependentGeneratedPackageHom.ext
                rfl

/-- Every mandatory-C source-choice morphism, hence the fixed uniform flip,
is an actual endomorphism in the tagged fiber of the closed declaration. -/
noncomputable def closedFamilyTaggedSourceChoice
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    (FamilyRealization.taggedOperation :
      FamilyRealization (ClosedFamilyParameter.taggedOperation :
          ClosedFamilyParameter.{0, 0})) ⟶ .taggedOperation :=
  ULift.up (taggedSourceChoiceExplicitExactGeometryHom choice)

/-- The constant-true member in the closed tagged fiber has exactly the fixed
mandatory uniform-flip base map. -/
theorem closedFamilyTaggedUniformFlip_base :
    (closedFamilyTaggedSourceChoice (fun _ => true)).down.base =
      taggedUniformFlipTotal :=
  taggedSourceChoiceExplicitExactGeometryHom_uniformFlip_base

/-- Every independently specified lens morphism enters the lens fiber without
an invertibility or presentation-membership premise. -/
def closedFamilyLensHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    (FamilyRealization.lens X : FamilyRealization (.lens input)) ⟶
      FamilyRealization.lens Y :=
  ULift.up (LensAATIndependentGeneratedPackageHom.ofSemanticHom f)

/-- Every independently specified protocol natural transformation enters the
protocol fiber without an invertibility or presentation-membership premise. -/
def closedFamilyProtocolHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (f : X ⟶ Y) :
    (FamilyRealization.protocol X : FamilyRealization (.protocol input)) ⟶
      FamilyRealization.protocol Y :=
  ULift.up (ProtocolAATIndependentGeneratedPackageHom.ofSemanticHom f)

/-- The fixed empty-to-unit lens map is retained by the closed declaration. -/
def closedFamilyAxisVarianceHom :
    (FamilyRealization.lens axisVarianceEmptyLens :
        FamilyRealization (.lens axisVarianceLensInput)) ⟶
      FamilyRealization.lens axisVarianceUnitLens :=
  ULift.up
    (LensAATIndependentGeneratedPackageHom.ofForwardMorphism axisVarianceForward)

/-- The retained fixed lens map is genuinely non-surjective on states. -/
theorem closedFamilyAxisVarianceHom_not_surjective :
    ¬ Function.Surjective closedFamilyAxisVarianceHom.down.stateMap := by
  intro surjective
  exact PEmpty.elim (surjective PUnit.unit).choose

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
