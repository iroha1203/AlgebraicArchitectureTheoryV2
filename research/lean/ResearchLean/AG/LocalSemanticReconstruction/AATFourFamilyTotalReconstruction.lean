import ResearchLean.AG.LocalSemanticReconstruction.AATFourFamilyBranchReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# One total reconstruction category for the four mandatory G-124 families

The four Cycle 78 fibers are totalized as one indexed-sum category.  An object
is a family parameter together with an object in that fiber.  A morphism has a
constructor only when source and target belong to the same fiber, so no
cross-family morphism is introduced.

The total reading, Hom assembler, both inverse laws, object realization, and
category equivalence are defined once on this total category.  Fiber inclusions
then identify the restriction of the total reading with every accepted branch
reading and carry the tagged, G-122, lens, and protocol connections through the
same surface.

This is a discrete Grothendieck-style totalization, not another case dispatcher.
It does not turn the accepted full G-122 coordinates into primitive local
syntax.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open CategoryTheory.Idempotents
open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open AtomFoundation DoctrineFiberProduct GeometryTransport TransportCoherence
open FullGeometryNormalization
open LocalReconstructionEquivalence

local instance aatTotalFiniteAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

attribute [local instance] uliftCategory

/-- An object of an indexed family of categories, retaining its family index. -/
structure IndexedTotalObject (Fiber : AATBranchParameter → Type 1) where
  /-- The selected family. -/
  parameter : AATBranchParameter
  /-- The object inside the selected family. -/
  object : Fiber parameter

/-- A Hom in the indexed total category exists only inside one family fiber. -/
inductive IndexedTotalHom
    (Fiber : AATBranchParameter → Type 1)
    [∀ parameter, Category.{1} (Fiber parameter)] :
    IndexedTotalObject Fiber → IndexedTotalObject Fiber → Type 1
  | mk {parameter : AATBranchParameter} {X Y : Fiber parameter}
      (hom : X ⟶ Y) :
      IndexedTotalHom Fiber ⟨parameter, X⟩ ⟨parameter, Y⟩

namespace IndexedTotalHom

variable {Fiber : AATBranchParameter → Type 1}
  [∀ parameter, Category.{1} (Fiber parameter)]

/-- Identity stays inside the selected fiber. -/
def id (X : IndexedTotalObject Fiber) : IndexedTotalHom Fiber X X := by
  rcases X with ⟨parameter, X⟩
  exact .mk (𝟙 X)

/-- Composition is the componentwise composition in the common fiber. -/
def comp {X Y Z : IndexedTotalObject Fiber}
    (first : IndexedTotalHom Fiber X Y)
    (second : IndexedTotalHom Fiber Y Z) : IndexedTotalHom Fiber X Z := by
  cases first with
  | mk first =>
      cases second with
      | mk second => exact .mk (first ≫ second)

/-- The indexed total Hom constructor is injective on its fiber Hom. -/
theorem mk_injective {parameter : AATBranchParameter}
    {X Y : Fiber parameter} :
    Function.Injective
      (IndexedTotalHom.mk (Fiber := Fiber) (X := X) (Y := Y)) := by
  intro first second equality
  cases equality
  rfl

end IndexedTotalHom

noncomputable instance indexedTotalCategory
    (Fiber : AATBranchParameter → Type 1)
    [∀ parameter, Category.{1} (Fiber parameter)] :
    Category.{1} (IndexedTotalObject Fiber) where
  Hom := IndexedTotalHom Fiber
  id := IndexedTotalHom.id
  comp := IndexedTotalHom.comp
  id_comp := by
    intro X Y morphism
    cases morphism with
    | mk morphism =>
        change IndexedTotalHom.mk ((𝟙 _) ≫ morphism) =
          IndexedTotalHom.mk morphism
        exact congrArg IndexedTotalHom.mk (Category.id_comp morphism)
  comp_id := by
    intro X Y morphism
    cases morphism with
    | mk morphism =>
        change IndexedTotalHom.mk (morphism ≫ 𝟙 _) =
          IndexedTotalHom.mk morphism
        exact congrArg IndexedTotalHom.mk (Category.comp_id morphism)
  assoc := by
    intro W X Y Z first second third
    cases first with
    | mk first =>
        cases second with
        | mk second =>
            cases third with
            | mk third =>
                change IndexedTotalHom.mk ((first ≫ second) ≫ third) =
                  IndexedTotalHom.mk (first ≫ second ≫ third)
                exact congrArg IndexedTotalHom.mk
                  (Category.assoc first second third)

/-- The single total global category containing all four admitted fibers. -/
abbrev AATTotalGlobal := IndexedTotalObject AATBranchGlobal

/-- The single total local-model category containing all four local fibers. -/
abbrev AATTotalLocal := IndexedTotalObject AATBranchLocal

/-- The branch readings assemble into one functor on the total categories. -/
noncomputable def aatTotalReading : AATTotalGlobal ⥤ AATTotalLocal where
  obj total := ⟨total.parameter,
    (aatBranchReading total.parameter).obj total.object⟩
  map {X Y} morphism := by
    cases morphism with
    | mk morphism => exact .mk ((aatBranchReading _).map morphism)
  map_id X := by
    rcases X with ⟨parameter, X⟩
    change IndexedTotalHom.mk ((aatBranchReading parameter).map (𝟙 X)) =
      IndexedTotalHom.mk (𝟙 ((aatBranchReading parameter).obj X))
    exact congrArg IndexedTotalHom.mk
      ((aatBranchReading parameter).map_id X)
  map_comp {X Y Z} first second := by
    cases first with
    | mk first =>
        cases second with
        | mk second =>
            change IndexedTotalHom.mk
                ((aatBranchReading _).map (first ≫ second)) =
              IndexedTotalHom.mk
                ((aatBranchReading _).map first ≫
                  (aatBranchReading _).map second)
            exact congrArg IndexedTotalHom.mk
              ((aatBranchReading _).map_comp first second)

/-- Directly assemble every Hom of the total local-model category. -/
noncomputable def aatTotalAssemble
    {X Y : AATTotalGlobal}
    (localMorphism : aatTotalReading.obj X ⟶ aatTotalReading.obj Y) : X ⟶ Y := by
  rcases X with ⟨parameter, source⟩
  rcases Y with ⟨targetParameter, target⟩
  cases localMorphism with
  | @mk parameter source target localMorphism =>
      exact .mk (aatBranchAssemble parameter localMorphism)

/-- Reading after direct total assembly is identity on every total local Hom. -/
@[simp] theorem aatTotal_read_assemble
    {X Y : AATTotalGlobal}
    (localMorphism : aatTotalReading.obj X ⟶ aatTotalReading.obj Y) :
    aatTotalReading.map (aatTotalAssemble localMorphism) = localMorphism := by
  rcases X with ⟨parameter, source⟩
  rcases Y with ⟨targetParameter, target⟩
  cases localMorphism with
  | @mk parameter source target localMorphism =>
      change IndexedTotalHom.mk
          ((aatBranchReading parameter).map
            (aatBranchAssemble parameter localMorphism)) =
        IndexedTotalHom.mk localMorphism
      exact congrArg IndexedTotalHom.mk
        (aatBranch_read_assemble parameter localMorphism)

/-- Direct total assembly after reading recovers every admitted total Hom. -/
@[simp] theorem aatTotal_assemble_read
    {X Y : AATTotalGlobal} (global : X ⟶ Y) :
    aatTotalAssemble (aatTotalReading.map global) = global := by
  rcases X with ⟨parameter, source⟩
  rcases Y with ⟨targetParameter, target⟩
  cases global with
  | @mk parameter source target global =>
      change IndexedTotalHom.mk
          (aatBranchAssemble parameter
            ((aatBranchReading parameter).map global)) =
        IndexedTotalHom.mk global
      exact congrArg IndexedTotalHom.mk
        (aatBranch_assemble_read parameter global)

/-- An isomorphism in one branch induces an isomorphism in the total category. -/
noncomputable def indexedTotalIso
    {Fiber : AATBranchParameter → Type 1}
    [∀ parameter, Category.{1} (Fiber parameter)]
    {parameter : AATBranchParameter} {X Y : Fiber parameter}
    (iso : X ≅ Y) :
    (IndexedTotalObject.mk parameter X : IndexedTotalObject Fiber) ≅
      IndexedTotalObject.mk parameter Y where
  hom := .mk iso.hom
  inv := .mk iso.inv
  hom_inv_id := by
    change IndexedTotalHom.mk (iso.hom ≫ iso.inv) =
      IndexedTotalHom.mk (𝟙 X)
    exact congrArg IndexedTotalHom.mk iso.hom_inv_id
  inv_hom_id := by
    change IndexedTotalHom.mk (iso.inv ≫ iso.hom) =
      IndexedTotalHom.mk (𝟙 Y)
    exact congrArg IndexedTotalHom.mk iso.inv_hom_id

/-- Realize an arbitrary object of the total local-model category. -/
noncomputable def aatTotalRealize (localObject : AATTotalLocal) : AATTotalGlobal :=
  ⟨localObject.parameter,
    aatBranchRealize localObject.parameter localObject.object⟩

/-- Reading the explicit total realization recovers the supplied local object. -/
noncomputable def aatTotalRealizeIso (localObject : AATTotalLocal) :
    aatTotalReading.obj (aatTotalRealize localObject) ≅ localObject := by
  rcases localObject with ⟨parameter, localObject⟩
  exact indexedTotalIso (aatBranchRealizeIso parameter localObject)

/-- Separation and Hom/object assembly for the single total reading. -/
noncomputable def aatTotalReconstructionData :
    ReconstructionData aatTotalReading where
  separation :=
    ⟨fun _ _ => ⟨fun first second equality => by
      rw [← aatTotal_assemble_read first, equality,
        aatTotal_assemble_read second]⟩⟩
  homAssembly :=
    { assemble := aatTotalAssemble
      map_assemble := aatTotal_read_assemble }
  objectAssembly :=
    { assembleObject := aatTotalRealize
      readAssembledIso := aatTotalRealizeIso }

/-- The one total four-family reading is an equivalence of categories. -/
noncomputable def aatTotalReconstructionEquivalence :
    AATTotalGlobal ≌ AATTotalLocal :=
  aatTotalReconstructionData.equivalence

/-- Every total local Hom has one unique admitted total global preimage. -/
theorem aatTotal_existsUnique_preimage
    {X Y : AATTotalGlobal}
    (localMorphism : aatTotalReading.obj X ⟶ aatTotalReading.obj Y) :
    ∃! global : X ⟶ Y, aatTotalReading.map global = localMorphism :=
  aatTotalReconstructionData.existsUnique_preimage localMorphism

/-! ### Exact recovery of every branch fiber -/

/-- Include one admitted global branch into the total global category. -/
noncomputable def aatGlobalFiberInclusion (parameter : AATBranchParameter) :
    AATBranchGlobal parameter ⥤ AATTotalGlobal where
  obj X := ⟨parameter, X⟩
  map morphism := .mk morphism
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Include one local-model branch into the total local category. -/
noncomputable def aatLocalFiberInclusion (parameter : AATBranchParameter) :
    AATBranchLocal parameter ⥤ AATTotalLocal where
  obj X := ⟨parameter, X⟩
  map morphism := .mk morphism
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Global fiber inclusion preserves and reflects every Hom exactly. -/
def aatGlobalFiberHomEquiv (parameter : AATBranchParameter)
    (X Y : AATBranchGlobal parameter) :
    (X ⟶ Y) ≃
      ((aatGlobalFiberInclusion parameter).obj X ⟶
        (aatGlobalFiberInclusion parameter).obj Y) where
  toFun := IndexedTotalHom.mk
  invFun total := by
    cases total with
    | mk morphism => exact morphism
  left_inv _ := rfl
  right_inv total := by cases total; rfl

/-- Local fiber inclusion preserves and reflects every Hom exactly. -/
def aatLocalFiberHomEquiv (parameter : AATBranchParameter)
    (X Y : AATBranchLocal parameter) :
    (X ⟶ Y) ≃
      ((aatLocalFiberInclusion parameter).obj X ⟶
        (aatLocalFiberInclusion parameter).obj Y) where
  toFun := IndexedTotalHom.mk
  invFun total := by
    cases total with
    | mk morphism => exact morphism
  left_inv _ := rfl
  right_inv total := by cases total; rfl

/-- Distinct family fibers have no total morphisms between them. -/
theorem aatTotal_noCrossFamilyHom
    {first second : AATBranchParameter} (different : first ≠ second)
    (X : AATBranchGlobal first) (Y : AATBranchGlobal second) :
    ¬ Nonempty
      ((aatGlobalFiberInclusion first).obj X ⟶
        (aatGlobalFiberInclusion second).obj Y) := by
  rintro ⟨morphism⟩
  cases morphism with
  | mk _ => exact different rfl

/-- Total reading restricted to a global fiber is the accepted branch reading. -/
noncomputable def aatFiberReadingIso (parameter : AATBranchParameter) :
    aatGlobalFiberInclusion parameter ⋙ aatTotalReading ≅
      aatBranchReading parameter ⋙ aatLocalFiberInclusion parameter :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y morphism
    change IndexedTotalHom.mk
        ((aatBranchReading parameter).map morphism ≫ 𝟙 _) =
      IndexedTotalHom.mk
        (𝟙 _ ≫ (aatBranchReading parameter).map morphism)
    rw [Category.comp_id, Category.id_comp])

/-- The total reading formula on every included branch Hom. -/
theorem aatTotalReading_map_fiber
    (parameter : AATBranchParameter)
    {X Y : AATBranchGlobal parameter} (morphism : X ⟶ Y) :
    aatTotalReading.map ((aatGlobalFiberInclusion parameter).map morphism) =
      (aatLocalFiberInclusion parameter).map
        ((aatBranchReading parameter).map morphism) := by
  rfl

/-- Projection of the total global category to its discrete family index. -/
noncomputable def aatTotalGlobalProjection :
    AATTotalGlobal ⥤ Discrete AATBranchParameter where
  obj total := Discrete.mk total.parameter
  map morphism := by
    cases morphism with
    | mk _ => exact 𝟙 _
  map_id X := by rcases X with ⟨parameter, X⟩; rfl
  map_comp first second := by
    cases first with
    | mk first =>
      cases second with
      | mk second => rfl

/-- Projection of the total local category to the same discrete family index. -/
noncomputable def aatTotalLocalProjection :
    AATTotalLocal ⥤ Discrete AATBranchParameter where
  obj total := Discrete.mk total.parameter
  map morphism := by
    cases morphism with
    | mk _ => exact 𝟙 _
  map_id X := by rcases X with ⟨parameter, X⟩; rfl
  map_comp first second := by
    cases first with
    | mk first =>
      cases second with
      | mk second => rfl

/-- Total reading lies over the identity of the family parameter. -/
theorem aatTotalReading_comp_projection :
    aatTotalReading ⋙ aatTotalLocalProjection =
      aatTotalGlobalProjection := by
  refine CategoryTheory.Functor.ext (fun X => rfl) ?_
  intros
  exact Subsingleton.elim _ _

/-! ### Family-specific statements recovered through the total reading -/

/-- Read an included branch Hom through the total category and recover its
local-fiber Hom. -/
noncomputable def aatTotalFiberReadingMap
    (parameter : AATBranchParameter)
    {X Y : AATBranchGlobal parameter} (morphism : X ⟶ Y) :
    (aatBranchReading parameter).obj X ⟶
      (aatBranchReading parameter).obj Y :=
  (aatLocalFiberHomEquiv parameter _ _).symm
    (aatTotalReading.map
      ((aatGlobalFiberInclusion parameter).map morphism))

/-- Reading through the total category is definitionally the accepted branch
reading after exact fiber recovery. -/
@[simp] theorem aatTotalFiberReadingMap_eq
    (parameter : AATBranchParameter)
    {X Y : AATBranchGlobal parameter} (morphism : X ⟶ Y) :
    aatTotalFiberReadingMap parameter morphism =
      (aatBranchReading parameter).map morphism := by
  rfl

/-- The tagged value formula remains visible after passage through the total
reading and recovery of the tagged fiber. -/
theorem aatTotalTaggedReadingValue
    {X Y : AATBranchGlobal AATBranchParameter.tagged}
    (morphism : X ⟶ Y) (S : Finset TagChangeGeneratedLocalModel.Index) :
    TagChangeGeneratedLocalModel.value
        ((aatTotalFiberReadingMap
          AATBranchParameter.tagged morphism).down) S =
      (TagChangeGeneratedLocalModel.readActualNormalizedFlag morphism.down,
        TagChange.LocalTagTable.read
          (TagChangeGeneratedLocalModel.readActualChoice morphism.down)
          (TagChangeGeneratedLocalModel.normalizationClosure S)) := by
  exact aatBranchTaggedReadingValue morphism S

/-- Total assembly on the tagged fiber is the accepted normal-form assembly. -/
theorem aatTotalTaggedAssemble_eq_normalForm
    {X Y : AATBranchGlobal AATBranchParameter.tagged}
    (localMorphism :
      (aatBranchReading AATBranchParameter.tagged).obj X ⟶
        (aatBranchReading AATBranchParameter.tagged).obj Y) :
    ((aatGlobalFiberHomEquiv AATBranchParameter.tagged X Y).symm
      (aatTotalAssemble
        ((aatLocalFiberInclusion AATBranchParameter.tagged).map
          localMorphism))).down =
      TagChangeGeneratedNormalForm.normalFormMulEquivGenerated
        (TagChangeGeneratedLocalModel.assemble localMorphism.down) := by
  exact aatBranchTaggedAssemble_eq_normalForm localMorphism

/-- The total G-122 reading exposes the accepted normalized comparison. -/
theorem aatTotalG122Reading_normalized
    {X Y : AATBranchGlobal AATBranchParameter.g122}
    (raw : X ⟶ Y) :
    ((aatTotalFiberReadingMap AATBranchParameter.g122 raw).down).normalized =
      restrictionHom raw.down := by
  exact aatBranchG122Reading_normalized raw

/-- The total G-122 reading exposes the unique full-kernel displacement. -/
theorem aatTotalG122Reading_kernel
    {X Y : AATBranchGlobal AATBranchParameter.g122}
    (raw : X ⟶ Y) :
    (MulOpposite.unop
      ((aatTotalFiberReadingMap
        AATBranchParameter.g122 raw).down).kernel).1 =
      (G122FullComparisonKernelDecomposition.canonicalSectionHom
        (restrictionHom raw.down))⁻¹ * raw.down := by
  exact aatBranchG122Reading_kernel raw

/-- The kernel coordinate recovered from the total G-122 reading carries the
canonical lift to the supplied full lift. -/
theorem aatTotalG122ReadingKernel_smul_canonicalLift
    (normalized : NormalizedComparison)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible normalized) :
    ((aatTotalFiberReadingMap AATBranchParameter.g122
      (aatBranchG122LiftHom normalized lift)).down).kernel •
        canonicalLift normalized = lift := by
  exact aatBranchG122ReadingKernel_smul_canonicalLift normalized lift

/-- Torsor uniqueness identifies any displacement with the coordinate
recovered through the total G-122 reading. -/
theorem aatTotalG122FullLiftFiber_unique_kernel_eq_reading
    (normalized : NormalizedComparison)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible normalized)
    (kernelValue : G122FullComparisonKernelDecomposition.FullKernelᵐᵒᵖ)
    (action : kernelValue • canonicalLift normalized = lift) :
    kernelValue =
      ((aatTotalFiberReadingMap AATBranchParameter.g122
        (aatBranchG122LiftHom normalized lift)).down).kernel := by
  exact aatBranchG122FullLiftFiber_unique_kernel_eq_reading
    normalized lift kernelValue action

/-! ### Finite-decoder, Karoubi, and Arrow routes through the total category -/

/-- The lens finite decoder lands directly in the lens fiber of the total
global category. -/
noncomputable def aatTotalLensFiniteDecoder (input : LensFamilyInput.{0}) :
    LensPresentation ⥤ AATTotalGlobal :=
  aatBranchLensFiniteDecoder input ⋙
    aatGlobalFiberInclusion (.lens input)

/-- Reading the total lens decoder recovers the accepted local decoder inside
the corresponding total local fiber. -/
noncomputable def aatTotalLensFiniteDecoderReadingIso
    (input : LensFamilyInput.{0}) :
    aatTotalLensFiniteDecoder input ⋙ aatTotalReading ≅
      lensFiberFiniteDecoder input ⋙
        (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        aatLocalFiberInclusion (.lens input) :=
  NatIso.ofComponents
    (fun object => indexedTotalIso
      ((aatBranchLensFiniteDecoderReadingIso input).app object))
    (by
      intro source target morphism
      change IndexedTotalHom.mk _ = IndexedTotalHom.mk _
      exact congrArg IndexedTotalHom.mk
        ((aatBranchLensFiniteDecoderReadingIso input).hom.naturality morphism))

/-- The protocol finite decoder lands directly in the protocol fiber of the
total global category. -/
noncomputable def aatTotalProtocolFiniteDecoder
    (input : ProtocolFamilyInput.{0}) :
    ProtocolPresentation input.schema input.observation ⥤ AATTotalGlobal :=
  aatBranchProtocolFiniteDecoder input ⋙
    aatGlobalFiberInclusion (.protocol input)

/-- Reading the total protocol decoder recovers the accepted local decoder
inside the corresponding total local fiber. -/
noncomputable def aatTotalProtocolFiniteDecoderReadingIso
    (input : ProtocolFamilyInput.{0}) :
    aatTotalProtocolFiniteDecoder input ⋙ aatTotalReading ≅
      protocolObservedFiniteDecoder input ⋙
        (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        aatLocalFiberInclusion (.protocol input) :=
  NatIso.ofComponents
    (fun object => indexedTotalIso
      ((aatBranchProtocolFiniteDecoderReadingIso input).app object))
    (by
      intro source target morphism
      change IndexedTotalHom.mk _ = IndexedTotalHom.mk _
      exact congrArg IndexedTotalHom.mk
        ((aatBranchProtocolFiniteDecoderReadingIso input).hom.naturality
          morphism))

/-- The accepted lens Karoubi equivalence is connected to the total global
category in the same cycle. -/
noncomputable def aatTotalLensKaroubiRoute (input : LensFamilyInput.{0}) :
    Karoubi LensPresentation ⥤ AATTotalGlobal :=
  (aatBranchLensKaroubiEquivalence input).functor ⋙
    aatGlobalFiberInclusion (.lens input)

/-- The accepted protocol Karoubi equivalence is connected to the total
global category in the same cycle. -/
noncomputable def aatTotalProtocolKaroubiRoute
    (input : ProtocolFamilyInput.{0}) :
    Karoubi (ProtocolPresentation input.schema input.observation) ⥤
      AATTotalGlobal :=
  (aatBranchProtocolKaroubiEquivalence input).functor ⋙
    aatGlobalFiberInclusion (.protocol input)

/-- The accepted lens Arrow equivalence is connected to the Arrow category of
the total global category. -/
noncomputable def aatTotalLensKaroubiArrowRoute
    (input : LensFamilyInput.{0}) :
    Karoubi (Arrow LensPresentation) ⥤ Arrow AATTotalGlobal :=
  (aatBranchLensKaroubiArrowEquivalence input).functor ⋙
    (aatGlobalFiberInclusion (.lens input)).mapArrow

/-- The accepted protocol Arrow equivalence is connected to the Arrow
category of the total global category. -/
noncomputable def aatTotalProtocolKaroubiArrowRoute
    (input : ProtocolFamilyInput.{0}) :
    Karoubi (Arrow
      (ProtocolPresentation input.schema input.observation)) ⥤
      Arrow AATTotalGlobal :=
  (aatBranchProtocolKaroubiArrowEquivalence input).functor ⋙
    (aatGlobalFiberInclusion (.protocol input)).mapArrow

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
