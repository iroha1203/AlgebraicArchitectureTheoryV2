import ResearchLean.AG.LocalSemanticReconstruction.CSKaroubiValueBridge
import ResearchLean.AG.LocalSemanticReconstruction.CSComparisonMain
import ResearchLean.AG.LocalSemanticReconstruction.CSChangeProgramLocal
import Formal.Util.AssertStandardAxioms

/-! Design IV-4/E2: the original semantic family retains its Karoubi Arrow
square and complete comparison groups in the common main reading. -/
namespace AAT.AG.LocalSemanticReconstruction.G124MainTheorem
open CategoryTheory CategoryTheory.Idempotents
open RealizationReconstruction IndependentAATPrimitiveReconstruction
open CSProgramLocal
universe u
set_option maxHeartbeats 800000

/-- For one lens input, arbitrary Karoubi Arrow squares are assembled from
the original finite value tables in main N, and every semantic comparison
group is transported bijectively to that same main N. -/
theorem lens_arrow_and_comparison
    (input : LensFamilyInput.{u})
    {p q : Karoubi (Arrow LensPresentation)} (square : p ⟶ q)
    [Fintype ((LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj p).left.Fiber]
    [Fintype ((LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor.obj p).right.Fiber]
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    (let R := (LensRealization.lensKaroubiArrowReconstructionEquivalence
      (V := input.View) (v₀ := input.reference)).functor
     let source := R.obj p
     let target := R.obj q
     let g := R.map square
     ((lensKaroubiArrowEquivalence input).functor.map square).left =
       (reading (Parameter.lens input : Parameter.{u, u})).map
         (ULift.up (LensSemanticFiniteDetermination.assembleTable
           source.left target.left
           (FiniteReading.restrict
             (LensSemanticFiniteDetermination.readLensHomAt source.left target.left)
             (LensSemanticFiniteDetermination.fullFiber source.left) g.left))) ∧
     ((lensKaroubiArrowEquivalence input).functor.map square).right =
       (reading (Parameter.lens input : Parameter.{u, u})).map
         (ULift.up (LensSemanticFiniteDetermination.assembleTable
           source.right target.right
           (FiniteReading.restrict
             (LensSemanticFiniteDetermination.readLensHomAt source.right target.right)
             (LensSemanticFiniteDetermination.fullFiber source.right) g.right)))) ∧
    Function.Bijective (CSComparisonMain.lensComparisonMainMulEquiv input f) := by
  exact ⟨CSKaroubiValueBridge.lens_karoubi_arrow_square_assemble_restricted_values
      input square,
    (CSComparisonMain.lensComparisonMainMulEquiv input f).bijective⟩

/-- The protocol Arrow square retains vertex, edge and observation table
coherence, while arbitrary semantic comparisons transport to main N. -/
theorem protocol_arrow_and_comparison
    (input : ProtocolFamilyInput.{u})
    {p q : Karoubi (Arrow
      (ProtocolPresentation input.schema input.observation))} (square : p ⟶ q)
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint
      ((ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
        (S := input.schema) (O := input.observation)).functor.obj p).left)]
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint
      ((ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
        (S := input.schema) (O := input.observation)).functor.obj p).right)]
    [DecidableEq input.schema.Vertex]
    {X Y : ProtocolRealization input.schema input.observation} (f : X ⟶ Y) :
    (let R := (ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
      (S := input.schema) (O := input.observation)).functor
     let source := R.obj p
     let target := R.obj q
     let g := R.map square
     ((protocolKaroubiArrowEquivalence input).functor.map square).left =
       (reading (Parameter.protocol input : Parameter.{u, u})).map
         (ULift.up (ProtocolObservedFiniteDetermination.assembleTable
           source.left target.left
           (FiniteReading.restrict
             (ProtocolObservedFiniteDetermination.readProtocolHomAt source.left target.left)
             (ProtocolObservedFiniteDetermination.fullInput source.left) g.left)
           (ProtocolObservedFiniteDetermination.read_table_coherent
             source.left target.left g.left))) ∧
     ((protocolKaroubiArrowEquivalence input).functor.map square).right =
       (reading (Parameter.protocol input : Parameter.{u, u})).map
         (ULift.up (ProtocolObservedFiniteDetermination.assembleTable
           source.right target.right
           (FiniteReading.restrict
             (ProtocolObservedFiniteDetermination.readProtocolHomAt source.right target.right)
             (ProtocolObservedFiniteDetermination.fullInput source.right) g.right)
           (ProtocolObservedFiniteDetermination.read_table_coherent
             source.right target.right g.right)))) ∧
    Function.Bijective (CSComparisonMain.protocolComparisonMainMulEquiv input f) := by
  exact ⟨CSKaroubiValueBridge.protocol_karoubi_arrow_square_assemble_restricted_values
      input square,
    (CSComparisonMain.protocolComparisonMainMulEquiv input f).bijective⟩

/-- The original finite lens program has both its exact rejection criterion
and, on success, point readback through the local Hom of the common N. -/
theorem lens_program_main_point_and_rejection
    {V K : Type u} (reference : V) [Fintype K] [DecidableEq K]
    {visible : Equiv.Perm V}
    (table : {hidden // hidden ∈ LensFiniteDetermination.fullReferenceFiber (K := K)} → K) :
    ((LensFiniteDetermination.effectivenessProgram
      (V := V) (K := K) (reference := reference) (visible := visible)).extend? table =
      none ↔ ¬ LensFiniteDetermination.TableCoherent table) ∧
    (∀ (change : FixedFLensConnection.LensInvertibleChange
        (LensRealization.product V K reference)
        (LensRealization.product V K reference) visible),
      (LensFiniteDetermination.effectivenessProgram
        (V := V) (K := K) (reference := reference) (visible := visible)).extend? table =
          some change →
      ∀ state output : K,
        FiniteApplicationHomDecoders.decodeLensPoint ⟨V,reference⟩
          (ULiftHom.objUp (LensRealization.product V K reference))
          (ULiftHom.objUp (LensRealization.product V K reference))
          (visible reference,state) (visible reference,output)
          (localHomTable (.lens ⟨V,reference⟩)
            (CSComponentLocalGroup.lensChangeLocalSemidirectMulEquiv reference
              (⊤ : Subgroup (Equiv.Perm V))
              (lensChangeToFullGroup reference change)).left.hom) = true ↔
          table ⟨state, Finset.mem_univ _⟩ = output) := by
  exact ⟨CSProgramLocal.lens_effectivenessProgram_reject_iff reference table,
    fun change success state output =>
      CSProgramLocal.lens_effectivenessProgram_main_point
        reference table change success state output⟩

/-- The original finite protocol program rejects precisely incoherent
tables and reads a successful output at the visible-reindexed vertex. -/
theorem protocol_program_main_point_and_rejection
    {F : FixedFDirectedMultigraph.{u,u}}
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    {K : Type u} [Fintype K] [DecidableEq K]
    {visible : FixedFGraphAutomorphism F}
    (S : F.Vertex → Prop) [DecidablePred S]
    (retains : InducedComponent.RetainsFullConnectivity F S)
    (table : {vertex // vertex ∈ ProtocolFiniteDetermination.readingVertices F S} →
      Equiv.Perm K) :
    ((ProtocolFiniteDetermination.effectivenessProgram
      (F := F) (K := K) (automorphism := visible) S retains).extend? table = none ↔
        ¬ ProtocolFiniteDetermination.TableCoherent F S K table) ∧
    (∀ (change : FixedFProtocolConnection.ProtocolInvertibleChange F K visible),
      (ProtocolFiniteDetermination.effectivenessProgram
        (F := F) (K := K) (automorphism := visible) S retains).extend? table =
          some change →
      ∀ (vertex : F.Vertex)
        (selected : vertex ∈ ProtocolFiniteDetermination.readingVertices F S)
        (state output : K),
        FiniteApplicationHomDecoders.decodeProtocolPoint
          (CSProtocolKernelLocal.fixedProtocolInput F)
          (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
          (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
          (visible.vertex vertex) state output
          (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
            (CSComponentLocalGroup.protocolChangeLocalSemidirectMulEquiv
              (⊤ : Subgroup (FixedFGraphAutomorphism F))
              (protocolChangeToFullGroup change)).left.hom) = true ↔
        (table ⟨vertex,selected⟩) state = output) := by
  exact ⟨CSProgramLocal.protocol_effectivenessProgram_reject_iff S retains table,
    fun change success vertex selected state output =>
      CSProgramLocal.protocol_effectivenessProgram_main_point
        S retains table change success vertex selected state output⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124MainTheorem

end AAT.AG.LocalSemanticReconstruction.G124MainTheorem
