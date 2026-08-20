import ResearchLean.AG.AtomFoundation.FiniteTransportWitness

/-!
# FiniteModel-backed presentation schema for G-110

This module fixes the first dependent layer of the G-110 finite calculus.  A
presentation contains only an identification of the ambient Atom type with the
reviewed finite model and a finite raw code.  Its semantic pointed morphism is
decoded from that code.  No package lift, cartesianness witness, checker bit,
mate, or comparison certificate occurs in the authored data.

## Implementation notes

The ambient carrier remains arbitrary.  `FiniteModelBacking` identifies only
its primitive Atom type with a universe lift of the reviewed finite Atom type;
the five visible coordinate projections are not rewritten.  This is exactly
the information used by `ExtractionDoctrine` and `ExactDoctrineHom`.

The finite code has three doctrine shapes and three hom shapes.  The first two
doctrines and their nonidentity exact morphism are the reviewed G-101 finite
transport, transported through the backing equivalence.  The third doctrine is
the source-independent finite shape needed to code a genuinely noninvertible
source map.  It is built from the same reviewed finite field vocabulary and
does not contain any upper-package or target conclusion data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Universe-polymorphic backing of the reviewed finite Atom model -/

/--
An identification of the ambient primitive Atom type with the reviewed finite
Atom type, lifted to the ambient universe.

This is representation data only.  It carries no doctrine, morphism, package,
lift, or condition certificate.
-/
structure FiniteModelBacking (U : AtomCarrier.{u}) where
  /-- The finite Atom enumeration in the ambient universe. -/
  atomEquiv : ULift.{u, 0} FiniteModel.FiniteAtom ≃ U.Atom

/-- The original reviewed finite carrier has its canonical backing. -/
def finiteModelBacking : FiniteModelBacking FiniteModel.carrier where
  atomEquiv := Equiv.ulift

namespace FiniteModelBacking

/-- The reviewed nonidentity Atom swap, conjugated into the ambient carrier. -/
noncomputable def transportAtomEquiv {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : U.Atom ≃ U.Atom := by
  let liftedSwap : ULift.{u, 0} FiniteModel.FiniteAtom ≃
      ULift.{u, 0} FiniteModel.FiniteAtom := {
    toFun := fun atom => ⟨finiteTransportAtomEquiv atom.down⟩
    invFun := fun atom => ⟨finiteTransportAtomEquiv.symm atom.down⟩
    left_inv := by
      intro atom
      apply ULift.ext
      exact finiteTransportAtomEquiv.symm_apply_apply atom.down
    right_inv := by
      intro atom
      apply ULift.ext
      exact finiteTransportAtomEquiv.apply_symm_apply atom.down
  }
  exact backing.atomEquiv.symm.trans (liftedSwap.trans backing.atomEquiv)

/-- The conjugated finite transport is genuinely nonidentity. -/
theorem transportAtomEquiv_ne_refl {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) :
    backing.transportAtomEquiv ≠ Equiv.refl U.Atom := by
  intro equality
  have pointEquality := Equiv.congr_fun equality
    (backing.atomEquiv
      ⟨FiniteModel.FiniteAtom.componentC⟩)
  have pulledBack :
      FiniteModel.FiniteAtom.dependsAB =
        FiniteModel.FiniteAtom.componentC := by
    simpa [FiniteModelBacking.transportAtomEquiv] using
      congrArg (fun atom => (backing.atomEquiv.symm atom).down)
        pointEquality
  exact FiniteModel.FiniteAtom.noConfusion
    pulledBack

end FiniteModelBacking

/-! ## Finite doctrine and pointed-instance codes -/

/-- The three FiniteModel-backed doctrine shapes used by the finite calculus. -/
inductive FiniteDoctrineCode
  | extraction
  | transported
  | sourceIndependent
  deriving DecidableEq

/-- Explicit enumeration of the finite doctrine codes. -/
def finiteDoctrineCodeAll : List FiniteDoctrineCode :=
  [.extraction, .transported, .sourceIndependent]

/-- The doctrine-code enumeration is exhaustive. -/
theorem finiteDoctrineCode_mem_all (code : FiniteDoctrineCode) :
    code ∈ finiteDoctrineCodeAll := by
  cases code <;> simp [finiteDoctrineCodeAll]

instance finiteDoctrineCodeFintype : Fintype FiniteDoctrineCode :=
  Fintype.ofList finiteDoctrineCodeAll finiteDoctrineCode_mem_all

/-- The reviewed finite source values, used as finite point codes. -/
inductive FiniteSourceCode
  | all
  | withoutComponentC
  deriving DecidableEq

/-- Explicit enumeration of the finite point codes. -/
def finiteSourceCodeAll : List FiniteSourceCode :=
  [.all, .withoutComponentC]

/-- The point-code enumeration is exhaustive. -/
theorem finiteSourceCode_mem_all (code : FiniteSourceCode) :
    code ∈ finiteSourceCodeAll := by
  cases code <;> simp [finiteSourceCodeAll]

instance finiteSourceCodeFintype : Fintype FiniteSourceCode :=
  Fintype.ofList finiteSourceCodeAll finiteSourceCode_mem_all

/-- A finite pointed-doctrine code. -/
structure FiniteInstanceCode where
  /-- Finite doctrine shape. -/
  doctrine : FiniteDoctrineCode
  /-- Selected finite source. -/
  source : FiniteSourceCode
  deriving DecidableEq

/-- Finite instance codes are exactly pairs of doctrine and point codes. -/
def finiteInstanceCodeEquiv :
    (FiniteDoctrineCode × FiniteSourceCode) ≃ FiniteInstanceCode where
  toFun code := ⟨code.1, code.2⟩
  invFun code := (code.doctrine, code.source)
  left_inv _ := rfl
  right_inv _ := rfl

instance finiteInstanceCodeFintype : Fintype FiniteInstanceCode :=
  Fintype.ofEquiv (FiniteDoctrineCode × FiniteSourceCode)
    finiteInstanceCodeEquiv

/-- Decode a finite point code into the ambient-universe source type. -/
def decodeFiniteSource : FiniteSourceCode →
    ULift.{u, 0} FiniteModel.ExtractionSource
  | .all => ⟨FiniteModel.ExtractionSource.all⟩
  | .withoutComponentC =>
      ⟨FiniteModel.ExtractionSource.withoutComponentC⟩

/--
The reviewed selective extraction doctrine, transported through a finite Atom
backing.  Every semantic clause is the corresponding FiniteModel clause read
through `atomEquiv`.
-/
def finiteExtractionDoctrine {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : ExtractionDoctrine U where
  Source := ULift.{u, 0} FiniteModel.ExtractionSource
  Vocabulary := ULift.{u, 0} PUnit
  SemanticReading := ULift.{u, 0} PUnit
  Resolution := ULift.{u, 0} PUnit
  vocabulary := ⟨PUnit.unit⟩
  semanticReading := ⟨PUnit.unit⟩
  resolution := ⟨PUnit.unit⟩
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ source atom =>
    source.down = FiniteModel.ExtractionSource.all ∨
      (backing.atomEquiv.symm atom).down ≠
        FiniteModel.FiniteAtom.componentC
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- The conjugated target doctrine of the reviewed nonidentity finite transport. -/
def finiteTransportedDoctrine {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : ExtractionDoctrine U where
  Source := ULift.{u, 0} FiniteModel.ExtractionSource
  Vocabulary := ULift.{u, 0} PUnit
  SemanticReading := ULift.{u, 0} PUnit
  Resolution := ULift.{u, 0} PUnit
  vocabulary := ⟨PUnit.unit⟩
  semanticReading := ⟨PUnit.unit⟩
  resolution := ⟨PUnit.unit⟩
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ source atom =>
    source.down = FiniteModel.ExtractionSource.all ∨
      finiteTransportAtomEquiv.symm
          (backing.atomEquiv.symm atom).down ≠
        FiniteModel.FiniteAtom.componentC
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/--
A source-independent finite doctrine used to expose noninvertible exact source
maps without changing the finite Atom vocabulary.
-/
def finiteSourceIndependentDoctrine {U : AtomCarrier.{u}}
    (_backing : FiniteModelBacking U) : ExtractionDoctrine U where
  Source := ULift.{u, 0} FiniteModel.ExtractionSource
  Vocabulary := ULift.{u, 0} PUnit
  SemanticReading := ULift.{u, 0} PUnit
  Resolution := ULift.{u, 0} PUnit
  vocabulary := ⟨PUnit.unit⟩
  semanticReading := ⟨PUnit.unit⟩
  resolution := ⟨PUnit.unit⟩
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- Decode a finite doctrine code through its ambient Atom backing. -/
def decodeFiniteDoctrine {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) :
    FiniteDoctrineCode → ExtractionDoctrine U
  | .extraction => finiteExtractionDoctrine backing
  | .transported => finiteTransportedDoctrine backing
  | .sourceIndependent => finiteSourceIndependentDoctrine backing

/-- Decode one finite pointed-doctrine code. -/
def decodeFiniteInstance {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U)
    (code : FiniteInstanceCode) : ExtractionInstance U :=
  match code.doctrine with
  | .extraction => {
      doctrine := finiteExtractionDoctrine backing
      source := decodeFiniteSource code.source
    }
  | .transported => {
      doctrine := finiteTransportedDoctrine backing
      source := decodeFiniteSource code.source
    }
  | .sourceIndependent => {
      doctrine := finiteSourceIndependentDoctrine backing
      source := decodeFiniteSource code.source
    }

/-! ## Finite exact hom codes and semantic realization -/

/-- The finite exact-hom shapes available to an authored cartesian presentation. -/
inductive FiniteHomCode
  | identity
  | atomTransport
  | constantToAll
  deriving DecidableEq

/-- Explicit enumeration of finite exact-hom shapes. -/
def finiteHomCodeAll : List FiniteHomCode :=
  [.identity, .atomTransport, .constantToAll]

/-- The hom-code enumeration is exhaustive. -/
theorem finiteHomCode_mem_all (code : FiniteHomCode) :
    code ∈ finiteHomCodeAll := by
  cases code <;> simp [finiteHomCodeAll]

instance finiteHomCodeFintype : Fintype FiniteHomCode :=
  Fintype.ofList finiteHomCodeAll finiteHomCode_mem_all

/--
Raw finite code for one pointed exact morphism.

The endpoints and hom tag are data.  Compatibility is kept in the separate
`WellFormed` predicate so the raw/validated split is visible in the type.
-/
structure CartRawCode where
  /-- Authored source instance code. -/
  source : FiniteInstanceCode
  /-- Authored target instance code. -/
  target : FiniteInstanceCode
  /-- Authored finite hom description. -/
  hom : FiniteHomCode
  deriving DecidableEq

/-- Raw cartesian codes are a finite product of their three authored fields. -/
def cartRawCodeEquiv :
    ((FiniteInstanceCode × FiniteInstanceCode) × FiniteHomCode) ≃
      CartRawCode where
  toFun code := ⟨code.1.1, code.1.2, code.2⟩
  invFun code := ((code.source, code.target), code.hom)
  left_inv _ := rfl
  right_inv _ := rfl

instance cartRawCodeFintype : Fintype CartRawCode :=
  Fintype.ofEquiv
    ((FiniteInstanceCode × FiniteInstanceCode) × FiniteHomCode)
    cartRawCodeEquiv

namespace CartRawCode

/-- Decoder-domain condition for a raw finite cartesian code. -/
def WellFormed (code : CartRawCode) : Prop :=
  match code.hom with
  | .identity => code.target = code.source
  | .atomTransport =>
      code.source.doctrine = .extraction ∧
        code.target.doctrine = .transported ∧
        code.target.source = code.source.source
  | .constantToAll =>
      code.source.doctrine = .sourceIndependent ∧
        code.target.doctrine = .sourceIndependent ∧
        code.target.source = .all

instance wellFormedDecidable (code : CartRawCode) :
    Decidable code.WellFormed := by
  unfold WellFormed
  split <;> infer_instance

end CartRawCode

/-- A validated raw code.  This is the domain of semantic decoding. -/
abbrev ValidatedCartCode := {code : CartRawCode // code.WellFormed}

/-- Raw identity code at the selective reviewed finite point. -/
def finiteIdentityRawCode : CartRawCode where
  source := ⟨.extraction, .withoutComponentC⟩
  target := ⟨.extraction, .withoutComponentC⟩
  hom := .identity

/-- The raw finite identity code is accepted by the decoder domain. -/
theorem finiteIdentityRawCode_wellFormed :
    finiteIdentityRawCode.WellFormed := by
  rfl

/-- Raw code for the reviewed nonidentity Atom transport. -/
def finiteAtomTransportRawCode : CartRawCode where
  source := ⟨.extraction, .withoutComponentC⟩
  target := ⟨.transported, .withoutComponentC⟩
  hom := .atomTransport

/-- The reviewed nonidentity Atom transport code is accepted. -/
theorem finiteAtomTransportRawCode_wellFormed :
    finiteAtomTransportRawCode.WellFormed := by
  exact ⟨rfl, rfl, rfl⟩

/-- Raw code for the noninvertible finite source map. -/
def finiteConstantRawCode : CartRawCode where
  source := ⟨.sourceIndependent, .withoutComponentC⟩
  target := ⟨.sourceIndependent, .all⟩
  hom := .constantToAll

/-- The noninvertible finite source-map code is accepted. -/
theorem finiteConstantRawCode_wellFormed :
    finiteConstantRawCode.WellFormed := by
  exact ⟨rfl, rfl, rfl⟩

/-- A mismatched identity code used to fire the negative well-formedness case. -/
def finiteMalformedIdentityRawCode : CartRawCode where
  source := ⟨.extraction, .withoutComponentC⟩
  target := ⟨.transported, .withoutComponentC⟩
  hom := .identity

/-- The mismatched identity code is rejected before semantic decoding. -/
theorem finiteMalformedIdentityRawCode_not_wellFormed :
    ¬ finiteMalformedIdentityRawCode.WellFormed := by
  decide

/-- Validated identity code. -/
def finiteIdentityCode : ValidatedCartCode :=
  ⟨finiteIdentityRawCode, finiteIdentityRawCode_wellFormed⟩

/-- Validated reviewed Atom-transport code. -/
def finiteAtomTransportCode : ValidatedCartCode :=
  ⟨finiteAtomTransportRawCode, finiteAtomTransportRawCode_wellFormed⟩

/-- Validated noninvertible source-map code. -/
def finiteConstantCode : ValidatedCartCode :=
  ⟨finiteConstantRawCode, finiteConstantRawCode_wellFormed⟩

/-- The semantic pointed-arrow layer required by the fixed G-110 statement. -/
structure CartSemanticInput (U : AtomCarrier.{u}) where
  /-- Source pointed doctrine. -/
  source : ExtractionInstance U
  /-- Target pointed doctrine. -/
  target : ExtractionInstance U
  /-- Actual exact pointed morphism. -/
  hom : source ⟶ target

/--
FiniteModel-backed presentation of one semantic pointed arrow.

The backing is representation provenance, while `code` is the finite authored
payload.  Neither field can contain an upper lift or a cartesianness result.
-/
structure CartPresentation (U : AtomCarrier.{u}) where
  /-- Provenance identifying the finite Atom schema inside `U`. -/
  backing : FiniteModelBacking U
  /-- Validated finite source/target/hom code. -/
  code : ValidatedCartCode

/-- Exact morphism decoding the reviewed nonidentity finite Atom transport. -/
noncomputable def finiteAtomTransportHom {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) :
    ExactDoctrineHom (finiteExtractionDoctrine backing)
      (finiteTransportedDoctrine backing) where
  sourceMap := fun source => source
  atomEquiv := backing.transportAtomEquiv
  normalize_eq _ := rfl
  extraction_iff := by
    intro source atom
    change
      (True ∧
        (source.down = FiniteModel.ExtractionSource.all ∨
          (backing.atomEquiv.symm atom).down ≠
            FiniteModel.FiniteAtom.componentC) ∧
        True ∧ True) ↔
      (True ∧
        (source.down = FiniteModel.ExtractionSource.all ∨
          finiteTransportAtomEquiv.symm
              (backing.atomEquiv.symm
                (backing.transportAtomEquiv atom)).down ≠
            FiniteModel.FiniteAtom.componentC) ∧
        True ∧ True)
    simp [FiniteModelBacking.transportAtomEquiv]

/-- Exact noninvertible source map on the source-independent finite doctrine. -/
def finiteConstantToAllHom {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) :
    ExactDoctrineHom (finiteSourceIndependentDoctrine backing)
      (finiteSourceIndependentDoctrine backing) where
  sourceMap := fun _ => decodeFiniteSource .all
  atomEquiv := Equiv.refl U.Atom
  normalize_eq _ := rfl
  extraction_iff := by
    intro source atom
    simp [ExtractionDoctrine.extracts, finiteSourceIndependentDoctrine]

/-- The finite constant source map is genuinely noninjective. -/
theorem finiteConstantToAllHom_not_injective {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) :
    ¬ Function.Injective (finiteConstantToAllHom backing).sourceMap := by
  intro injective
  have equality := injective (show
    (finiteConstantToAllHom backing).sourceMap
        (decodeFiniteSource .all) =
      (finiteConstantToAllHom backing).sourceMap
        (decodeFiniteSource .withoutComponentC) by rfl)
  exact FiniteModel.ExtractionSource.noConfusion
    (congrArg ULift.down equality)

/-- Decode a validated finite hom code into an actual pointed exact morphism. -/
noncomputable def decodeCartHom {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) (code : ValidatedCartCode) :
    ExtInstHom (decodeFiniteInstance backing code.1.source)
      (decodeFiniteInstance backing code.1.target) := by
  rcases code with ⟨⟨source, target, hom⟩, wellFormed⟩
  cases hom with
  | identity =>
      change target = source at wellFormed
      subst target
      exact ExtInstHom.id (decodeFiniteInstance backing source)
  | atomTransport =>
      change
        source.doctrine = .extraction ∧
          target.doctrine = .transported ∧
          target.source = source.source at wellFormed
      rcases source with ⟨sourceDoctrine, sourcePoint⟩
      rcases target with ⟨targetDoctrine, targetPoint⟩
      simp only at wellFormed
      rcases wellFormed with ⟨rfl, rfl, rfl⟩
      exact {
        doctrineHom := finiteAtomTransportHom backing
        source_eq := by
          simp [decodeFiniteInstance, decodeFiniteSource,
            finiteAtomTransportHom]
      }
  | constantToAll =>
      change
        source.doctrine = .sourceIndependent ∧
          target.doctrine = .sourceIndependent ∧
          target.source = .all at wellFormed
      rcases source with ⟨sourceDoctrine, sourcePoint⟩
      rcases target with ⟨targetDoctrine, targetPoint⟩
      simp only at wellFormed
      rcases wellFormed with ⟨rfl, rfl, rfl⟩
      exact {
        doctrineHom := finiteConstantToAllHom backing
        source_eq := by
          simp [decodeFiniteInstance, decodeFiniteSource,
            finiteConstantToAllHom]
      }

/-- Decode a finite presentation to its actual semantic pointed arrow. -/
noncomputable def toSemanticCart {U : AtomCarrier.{u}}
    (presentation : CartPresentation U) : CartSemanticInput U where
  source := decodeFiniteInstance presentation.backing
    presentation.code.1.source
  target := decodeFiniteInstance presentation.backing
    presentation.code.1.target
  hom := decodeCartHom presentation.backing presentation.code

/--
Semantic realization satisfies the three actual G-101 morphism laws.

The proof reads the proofs constructed by `decodeCartHom`; callers do not
supply a separate soundness certificate.
-/
theorem toSemanticCart_sound {U : AtomCarrier.{u}}
    (presentation : CartPresentation U) :
    (∀ source,
      (toSemanticCart presentation).target.doctrine.normalize
          ((toSemanticCart presentation).hom.doctrineHom.sourceMap source) =
        (toSemanticCart presentation).hom.doctrineHom.sourceMap
          ((toSemanticCart presentation).source.doctrine.normalize source)) ∧
    (∀ source atom,
      (toSemanticCart presentation).source.doctrine.extracts source atom ↔
        (toSemanticCart presentation).target.doctrine.extracts
          ((toSemanticCart presentation).hom.doctrineHom.sourceMap source)
          ((toSemanticCart presentation).hom.doctrineHom.atomEquiv atom)) ∧
    (toSemanticCart presentation).hom.doctrineHom.sourceMap
        (toSemanticCart presentation).source.source =
      (toSemanticCart presentation).target.source :=
  ⟨(toSemanticCart presentation).hom.doctrineHom.normalize_eq,
    (toSemanticCart presentation).hom.doctrineHom.extraction_iff,
    (toSemanticCart presentation).hom.source_eq⟩

/-- Presentation of the reviewed finite identity over any chosen backing. -/
def finiteIdentityPresentation {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : CartPresentation U where
  backing := backing
  code := finiteIdentityCode

/-- Presentation of the reviewed nonidentity Atom transport. -/
def finiteAtomTransportPresentation {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : CartPresentation U where
  backing := backing
  code := finiteAtomTransportCode

/-- Presentation of a finite noninvertible source map. -/
def finiteConstantPresentation {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : CartPresentation U where
  backing := backing
  code := finiteConstantCode

/-- The constant presentation decoder uses the generated constant exact hom. -/
theorem decodeCartHom_finiteConstant_doctrineHom {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) :
    (decodeCartHom backing finiteConstantCode).doctrineHom =
      finiteConstantToAllHom backing := by
  have canonicalProof : finiteConstantRawCode.WellFormed :=
    ⟨rfl, rfl, rfl⟩
  have proofEquality :
      finiteConstantRawCode_wellFormed = canonicalProof :=
    Subsingleton.elim _ _
  unfold finiteConstantCode
  rw [proofEquality]
  rcases canonicalProof with ⟨sourceDoctrine, targetDoctrine, targetPoint⟩
  cases sourceDoctrine
  cases targetDoctrine
  cases targetPoint
  rfl

/-- The decoded finite constant presentation retains the noninjective source map. -/
theorem finiteConstantPresentation_not_injective {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) :
    ¬ Function.Injective
      (toSemanticCart (finiteConstantPresentation backing)).hom.doctrineHom.sourceMap := by
  rw [show
    (toSemanticCart
      (finiteConstantPresentation backing)).hom.doctrineHom =
        finiteConstantToAllHom backing by
      exact decodeCartHom_finiteConstant_doctrineHom backing]
  exact finiteConstantToAllHom_not_injective backing

/-- A semantic arrow together with a presentation witnessing its provenance. -/
structure RealizableHom (U : AtomCarrier.{u}) where
  /-- The semantic pointed arrow. -/
  semantic : CartSemanticInput U
  /-- Finite presentation producing that arrow. -/
  presentation : CartPresentation U
  /-- The semantic arrow is exactly the decoder output. -/
  realization_eq : toSemanticCart presentation = semantic

/-- Canonical realizable arrow generated by one validated presentation. -/
noncomputable def realizableHomOf {U : AtomCarrier.{u}}
    (presentation : CartPresentation U) : RealizableHom U where
  semantic := toSemanticCart presentation
  presentation := presentation
  realization_eq := rfl

/-! ## Fixed conclusion-free cartesian condition language -/

/-- Operand sorts available to the cartesian condition language. -/
inductive CartFieldKind
  | doctrine
  | source
  | hom

/-- The finite value type of each condition-language operand sort. -/
def CartFieldValue : CartFieldKind → Type
  | .doctrine => FiniteDoctrineCode
  | .source => FiniteSourceCode
  | .hom => FiniteHomCode

instance cartFieldValueDecidableEq (kind : CartFieldKind) :
    DecidableEq (CartFieldValue kind) := by
  cases kind <;> simp only [CartFieldValue] <;> infer_instance

/-- Fully enumerated field projections allowed in cartesian conditions. -/
inductive CartProjection : (kind : CartFieldKind) → Type
  | sourceDoctrine : CartProjection .doctrine
  | targetDoctrine : CartProjection .doctrine
  | sourcePoint : CartProjection .source
  | targetPoint : CartProjection .source
  | homCode : CartProjection .hom

/-- Read one allowed projection from a raw finite code. -/
def readCartProjection {kind : CartFieldKind}
    (projection : CartProjection kind) (code : CartRawCode) :
    CartFieldValue kind :=
  match projection with
  | .sourceDoctrine => code.source.doctrine
  | .targetDoctrine => code.target.doctrine
  | .sourcePoint => code.source.source
  | .targetPoint => code.target.source
  | .homCode => code.hom

/-- Presentation-derived finite sets allowed in membership atoms. -/
inductive CartDerivedSet : (kind : CartFieldKind) → Type
  | endpointDoctrines : CartDerivedSet .doctrine
  | endpointSources : CartDerivedSet .source
  | authoredHom : CartDerivedSet .hom

/-- Structural tests available to the finite-cell universal atom. -/
inductive CartCellTest
  | sourcePointPreserved
  | atomPermutationIdentity
  | sourceMapInjective
  | sourceMapSurjective
  deriving DecidableEq

/--
The complete G-110 cartesian condition syntax.

Its four constructors are exactly field equality, membership in a finite set
derived from the presentation itself, finite universal testing of presentation
cells, and conjunction.  No constructor accepts a proposition, checker result,
lift, mate, comparison, or external finite set.
-/
inductive CartConditionSyntax
  | fieldEq {kind : CartFieldKind}
      (left right : CartProjection kind)
  | fieldMem {kind : CartFieldKind}
      (field : CartProjection kind) (set : CartDerivedSet kind)
  | allCells (test : CartCellTest)
  | conjunction (left right : CartConditionSyntax)

/-- Membership in a named finite set derived from the authored code. -/
def evalCartMembership {kind : CartFieldKind}
    (value : CartFieldValue kind) (set : CartDerivedSet kind)
    (code : CartRawCode) : Bool :=
  match set with
  | .endpointDoctrines =>
      decide (value = code.source.doctrine ∨ value = code.target.doctrine)
  | .endpointSources =>
      decide (value = code.source.source ∨ value = code.target.source)
  | .authoredHom => decide (value = code.hom)

/-- Evaluate one structural test on the unique hom cell of a cart presentation. -/
def evalCartCellTest (test : CartCellTest) (code : CartRawCode) : Bool :=
  match test with
  | .sourcePointPreserved => decide (code.target.source = code.source.source)
  | .atomPermutationIdentity =>
      match code.hom with
      | .identity => true
      | .atomTransport => false
      | .constantToAll => true
  | .sourceMapInjective =>
      match code.hom with
      | .identity => true
      | .atomTransport => true
      | .constantToAll => false
  | .sourceMapSurjective =>
      match code.hom with
      | .identity => true
      | .atomTransport => true
      | .constantToAll => false

/-- Computable evaluation of the fixed conclusion-free condition language. -/
def evalCartCondition : CartConditionSyntax → ValidatedCartCode → Bool
  | .fieldEq left right, code =>
      decide (readCartProjection left code.1 = readCartProjection right code.1)
  | .fieldMem field set, code =>
      evalCartMembership (readCartProjection field code.1) set code.1
  | .allCells test, code => evalCartCellTest test code.1
  | .conjunction left right, code =>
      evalCartCondition left code && evalCartCondition right code

/-- The structural injectivity test accepts the reviewed Atom transport. -/
theorem evalCartCondition_atomTransport_injective :
    evalCartCondition (.allCells .sourceMapInjective)
      finiteAtomTransportCode = true := by
  rfl

/-- The structural injectivity test rejects the finite constant source map. -/
theorem evalCartCondition_constant_not_injective :
    evalCartCondition (.allCells .sourceMapInjective)
      finiteConstantCode = false := by
  rfl

/-- The Atom-permutation test distinguishes the reviewed nonidentity transport. -/
theorem evalCartCondition_atomTransport_nonidentity :
    evalCartCondition (.allCells .atomPermutationIdentity)
      finiteAtomTransportCode = false := by
  rfl

/-- A field-membership atom reads only the presentation's own endpoint set. -/
theorem evalCartCondition_sourceDoctrine_mem_endpoints :
    evalCartCondition
      (.fieldMem (.sourceDoctrine) (.endpointDoctrines))
      finiteConstantCode = true := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
