import ResearchLean.AG.LocalSemanticReconstruction.G124ComparisonTransport
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: the complete comparison groups of arbitrary independent
lens and protocol morphisms are transported through the universe lift and
the one common main local reader, with both endpoint automorphisms evaluated
in that same Hom. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
attribute [local instance] uliftCategory
universe u
namespace CSComparisonMain
/-- All comparison-preserving endpoint automorphisms of an arbitrary lens
semantic morphism transport to the same common main local Hom. -/
noncomputable def lensComparisonMainMulEquiv
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup f ≃*
      GeneratedArrowComparisonSubgroup
        ((reading (Parameter.lens input : Parameter.{u, u})).map
          (ULift.up f)) :=
  (generatedArrowComparisonMulEquivOfFullyFaithful
    (CategoryTheory.ULiftHom.up
      (C := LensRealization input.View input.reference))
    (CategoryTheory.ULiftHom.equiv
      (C := LensRealization input.View input.reference)).fullyFaithfulFunctor f).trans
    (G124ComparisonTransport.comparisonMulEquiv
      (Parameter.lens input : Parameter.{u, u}) (ULift.up f))

/-- All comparison-preserving endpoint automorphisms of an arbitrary
protocol semantic morphism transport to the same main local Hom. -/
noncomputable def protocolComparisonMainMulEquiv
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation} (f : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup f ≃*
      GeneratedArrowComparisonSubgroup
        ((reading (Parameter.protocol input : Parameter.{u, u})).map
          (ULift.up f)) :=
  (generatedArrowComparisonMulEquivOfFullyFaithful
    (CategoryTheory.ULiftHom.up
      (C := ProtocolRealization input.schema input.observation))
    (CategoryTheory.ULiftHom.equiv
      (C := ProtocolRealization input.schema input.observation)).fullyFaithfulFunctor f).trans
    (G124ComparisonTransport.comparisonMulEquiv
      (Parameter.protocol input : Parameter.{u, u}) (ULift.up f))

/-- Each source endpoint of the full lens comparison group is read through
the same main functor. -/
theorem lensComparisonMain_source_hom
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup f) :
    (lensComparisonMainMulEquiv input f pair).1.1.hom =
      (reading (Parameter.lens input : Parameter.{u, u})).map
        (ULift.up pair.1.1.hom) := rfl

/-- Each target endpoint of the full lens comparison group is read through
the same main functor. -/
theorem lensComparisonMain_target_hom
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup f) :
    (lensComparisonMainMulEquiv input f pair).1.2.hom =
      (reading (Parameter.lens input : Parameter.{u, u})).map
        (ULift.up pair.1.2.hom) := rfl

/-- Each source endpoint of the full protocol comparison group is read
through the same main functor. -/
theorem protocolComparisonMain_source_hom
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation} (f : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup f) :
    (protocolComparisonMainMulEquiv input f pair).1.1.hom =
      (reading (Parameter.protocol input : Parameter.{u, u})).map
        (ULift.up pair.1.1.hom) := rfl

/-- Each target endpoint of the full protocol comparison group is read
through the same main functor. -/
theorem protocolComparisonMain_target_hom
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation} (f : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup f) :
    (protocolComparisonMainMulEquiv input f pair).1.2.hom =
      (reading (Parameter.protocol input : Parameter.{u, u})).map
        (ULift.up pair.1.2.hom) := rfl


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSComparisonMain

end CSComparisonMain
end AAT.AG.LocalSemanticReconstruction
