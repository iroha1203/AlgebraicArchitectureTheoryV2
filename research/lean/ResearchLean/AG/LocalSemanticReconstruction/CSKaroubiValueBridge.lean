import ResearchLean.AG.LocalSemanticReconstruction.CSFiniteDecoderValueBridge
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: arbitrary Karoubi and Karoubi Arrow morphisms have their
original finite semantic value tables assembled back to the very same
common main local Hom, including the finite decoder restriction. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory CategoryTheory.Idempotents RealizationReconstruction IndependentAATPrimitiveReconstruction
open FiniteApplicationHomDecoders
namespace CSKaroubiValueBridge
universe u

theorem lens_karoubi_value_iff_main_point
    (input : LensFamilyInput.{u})
    {p q : Karoubi LensPresentation} (arrow : p ⟶ q)
    (state : ((LensRealization.lensKaroubiReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj p).Fiber)
    (output : ((LensRealization.lensKaroubiReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj q).Fiber) :
    LensSemanticFiniteDetermination.readLensHomAt
      ((LensRealization.lensKaroubiReconstructionEquivalence
        (V := input.View) (v₀ := input.reference)).functor.obj p)
      ((LensRealization.lensKaroubiReconstructionEquivalence
        (V := input.View) (v₀ := input.reference)).functor.obj q)
      ((LensRealization.lensKaroubiReconstructionEquivalence
        (V := input.View) (v₀ := input.reference)).functor.map arrow) state = output ↔
      decodeLensPoint input
        (ULiftHom.objUp ((LensRealization.lensKaroubiReconstructionEquivalence
          (V := input.View) (v₀ := input.reference)).functor.obj p))
        (ULiftHom.objUp ((LensRealization.lensKaroubiReconstructionEquivalence
          (V := input.View) (v₀ := input.reference)).functor.obj q))
        state.1 output.1
        (localHomTable (.lens input)
          ((lensKaroubiEquivalence input).functor.map arrow)) = true := by
  exact CSFiniteValueQueryBridge.lens_value_iff_primitive_point input
    ((LensRealization.lensKaroubiReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj p)
    ((LensRealization.lensKaroubiReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj q)
    ((LensRealization.lensKaroubiReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.map arrow) state output


theorem lens_karoubi_arrow_value_iff_main_point
    (input : LensFamilyInput.{u})
    (presentation : Karoubi (Arrow LensPresentation))
    (state : ((LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj presentation).left.Fiber)
    (output : ((LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj presentation).right.Fiber) :
    let semantic := (LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj presentation
    LensSemanticFiniteDetermination.readLensHomAt semantic.left semantic.right
        semantic.hom state = output ↔
      decodeLensPoint input (ULiftHom.objUp semantic.left)
        (ULiftHom.objUp semantic.right) state.1 output.1
        (localHomTable (.lens input)
          ((lensKaroubiArrowEquivalence input).functor.obj presentation).hom) = true := by
  exact CSFiniteValueQueryBridge.lens_value_iff_primitive_point input
    _ _ _ state output


theorem protocol_karoubi_value_iff_main_point
    (input : ProtocolFamilyInput.{u})
    {p q : Karoubi (ProtocolPresentation input.schema input.observation)}
    (arrow : p ⟶ q)
    (vertex : input.schema.Vertex)
    (state : ((ProtocolPresentation.protocolKaroubiReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor.obj p).State vertex)
    (output : ((ProtocolPresentation.protocolKaroubiReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor.obj q).State vertex) :
    let R := (ProtocolPresentation.protocolKaroubiReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor
    ProtocolObservedFiniteDetermination.readProtocolHomAt
      (R.obj p) (R.obj q) (R.map arrow) ⟨vertex,state⟩ = ⟨vertex,output⟩ ↔
      decodeProtocolPoint input (ULiftHom.objUp (R.obj p))
        (ULiftHom.objUp (R.obj q)) vertex state output
        (localHomTable (.protocol input)
          ((protocolKaroubiEquivalence input).functor.map arrow)) = true := by
  exact CSFiniteValueQueryBridge.protocol_value_iff_primitive_point input
    _ _ _ vertex state output


theorem protocol_karoubi_arrow_value_iff_main_point
    (input : ProtocolFamilyInput.{u})
    (presentation : Karoubi (Arrow
      (ProtocolPresentation input.schema input.observation)))
    (vertex : input.schema.Vertex)
    (state : ((ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor.obj presentation).left.State vertex)
    (output : ((ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor.obj presentation).right.State vertex) :
    let semantic := (ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor.obj presentation
    ProtocolObservedFiniteDetermination.readProtocolHomAt
      semantic.left semantic.right semantic.hom ⟨vertex,state⟩ = ⟨vertex,output⟩ ↔
      decodeProtocolPoint input (ULiftHom.objUp semantic.left)
        (ULiftHom.objUp semantic.right) vertex state output
        (localHomTable (.protocol input)
          ((protocolKaroubiArrowEquivalence input).functor.obj presentation).hom) = true := by
  exact CSFiniteValueQueryBridge.protocol_value_iff_primitive_point input
    _ _ _ vertex state output


/-- The entire primitive Hom of an arbitrary Karoubi-reconstructed lens
arrow equals the reading of the extension of its original finite value table. -/
theorem lens_karoubi_assemble_restricted_values
    (input : LensFamilyInput.{u})
    {p q : Karoubi LensPresentation} (arrow : p ⟶ q)
    [Fintype ((LensRealization.lensKaroubiReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj p).Fiber] :
    let R := (LensRealization.lensKaroubiReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor
    let X := R.obj p
    let Y := R.obj q
    let f := R.map arrow
    (lensKaroubiEquivalence input).functor.map arrow =
      (reading (Parameter.lens input : Parameter.{u, u})).map
        (ULift.up (LensSemanticFiniteDetermination.assembleTable X Y
          (FiniteReading.restrict (LensSemanticFiniteDetermination.readLensHomAt X Y)
            (LensSemanticFiniteDetermination.fullFiber X) f))) := by
  dsimp only
  rw [CSFiniteValueQueryBridge.lens_assemble_restricted_values]
  rfl

/-- The entire primitive Hom of an arbitrary Karoubi-reconstructed protocol
arrow equals the reading of the extension of its coherent finite table. -/
theorem protocol_karoubi_assemble_restricted_values
    (input : ProtocolFamilyInput.{u})
    {p q : Karoubi (ProtocolPresentation input.schema input.observation)}
    (arrow : p ⟶ q)
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint
      ((ProtocolPresentation.protocolKaroubiReconstructionEquivalence
        (S := input.schema) (O := input.observation)).functor.obj p))]
    [DecidableEq input.schema.Vertex] :
    let R := (ProtocolPresentation.protocolKaroubiReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor
    let P := R.obj p
    let Q := R.obj q
    let f := R.map arrow
    (protocolKaroubiEquivalence input).functor.map arrow =
      (reading (Parameter.protocol input : Parameter.{u, u})).map
        (ULift.up (ProtocolObservedFiniteDetermination.assembleTable P Q
          (FiniteReading.restrict (ProtocolObservedFiniteDetermination.readProtocolHomAt P Q)
            (ProtocolObservedFiniteDetermination.fullInput P) f)
          (ProtocolObservedFiniteDetermination.read_table_coherent P Q f))) := by
  dsimp only
  rw [CSFiniteValueQueryBridge.protocol_assemble_restricted_values]
  rfl


/-- A Karoubi Arrow lens object's local arrow is exactly the main reading
of the extension of its complete semantic fiber table. -/
theorem lens_karoubi_arrow_assemble_restricted_values
    (input : LensFamilyInput.{u})
    (presentation : Karoubi (Arrow LensPresentation))
    [Fintype ((LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj presentation).left.Fiber] :
    let semantic := (LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj presentation
    ((lensKaroubiArrowEquivalence input).functor.obj presentation).hom =
      (reading (Parameter.lens input : Parameter.{u, u})).map
        (ULift.up (LensSemanticFiniteDetermination.assembleTable
          semantic.left semantic.right
          (FiniteReading.restrict
            (LensSemanticFiniteDetermination.readLensHomAt semantic.left semantic.right)
            (LensSemanticFiniteDetermination.fullFiber semantic.left) semantic.hom))) := by
  dsimp only
  rw [CSFiniteValueQueryBridge.lens_assemble_restricted_values]
  rfl

/-- A Karoubi Arrow protocol object's local arrow is exactly the main
reading of the extension of its coherent complete vertex table. -/
theorem protocol_karoubi_arrow_assemble_restricted_values
    (input : ProtocolFamilyInput.{u})
    (presentation : Karoubi (Arrow
      (ProtocolPresentation input.schema input.observation)))
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint
      ((ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
        (S := input.schema) (O := input.observation)).functor.obj presentation).left)]
    [DecidableEq input.schema.Vertex] :
    let semantic := (ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor.obj presentation
    ((protocolKaroubiArrowEquivalence input).functor.obj presentation).hom =
      (reading (Parameter.protocol input : Parameter.{u, u})).map
        (ULift.up (ProtocolObservedFiniteDetermination.assembleTable
          semantic.left semantic.right
          (FiniteReading.restrict
            (ProtocolObservedFiniteDetermination.readProtocolHomAt
              semantic.left semantic.right)
            (ProtocolObservedFiniteDetermination.fullInput semantic.left) semantic.hom)
          (ProtocolObservedFiniteDetermination.read_table_coherent
            semantic.left semantic.right semantic.hom))) := by
  dsimp only
  rw [CSFiniteValueQueryBridge.protocol_assemble_restricted_values]
  rfl
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSKaroubiValueBridge

end CSKaroubiValueBridge
end AAT.AG.LocalSemanticReconstruction
