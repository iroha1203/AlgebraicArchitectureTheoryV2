import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import ResearchLean.AG.FullGeometryNormalization.SemanticExactBarBetaClassification
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedGeneratedEndpointBridge

/-!
# Primitive reconstruction of the semantic generated comparison

The original geometry and both exact derived routes come from an arbitrary
semantic pullback square. The representative primitive reader reconstructs
every complete-geometry Hom between them. The generated comparison and its
projectors are inserted only after their semantic construction.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open AAT.AG.DoctrineFiberProduct AAT.AG.FullGeometryNormalization
open AAT.AG.TransportCoherence
open IndependentAATPrimitiveReconstruction IndependentGeometryHomPrimitive

noncomputable section

universe u v

attribute [local instance] uliftCategory

/-- The representative primitive reading for the carrier of a semantic
base-change square. -/
abbrev semanticComparisonParameter (U : AtomCarrier.{u}) : Parameter.{u, v} :=
  .geometry U Mode.representative

/-- Put an arbitrary complete geometry in the native category used by the
common primitive reader. -/
noncomputable def semanticComparisonNativeObject
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U) :
    NativeCategory (semanticComparisonParameter U) :=
  ULiftHom.objUp G

/-- An arbitrary complete-geometry morphism, including all endpoint
automorphisms, in the same native category. -/
noncomputable def semanticComparisonNativeHom
    {U : AtomCarrier.{u}} {G H : GeomReadCategory.{u, v} U}
    (f : G ⟶ H) :
    semanticComparisonNativeObject G ⟶ semanticComparisonNativeObject H :=
  ULift.up f

/-- Read-then-assemble recovers every complete-geometry morphism between
semantic generated objects, not just the four displayed maps. -/
theorem semanticComparisonHom_assemble_read
    {U : AtomCarrier.{u}} {G H : GeomReadCategory.{u, v} U}
    (f : G ⟶ H) :
    assembleHom (semanticComparisonParameter U)
        ((reading (semanticComparisonParameter U)).map
          (semanticComparisonNativeHom f)) =
      semanticComparisonNativeHom f :=
  assembleHom_read (semanticComparisonParameter U)
    (semanticComparisonNativeHom f)

/-- Every lawful primitive local Hom between actual complete geometries has
a unique complete-geometry preimage. -/
theorem semanticComparisonHom_existsUnique
    {U : AtomCarrier.{u}} (G H : GeomReadCategory.{u, v} U)
    (localHom : (reading (semanticComparisonParameter U)).obj
        (semanticComparisonNativeObject G) ⟶
      (reading (semanticComparisonParameter U)).obj
        (semanticComparisonNativeObject H)) :
    ∃! f : G ⟶ H,
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonNativeHom f) = localHom := by
  obtain ⟨f, hf, unique⟩ :=
    existsUnique_preimage (semanticComparisonParameter U) localHom
  refine ⟨f.down, ?_, ?_⟩
  · exact hf
  · intro g hg
    exact congrArg ULift.down (unique (semanticComparisonNativeHom g) hg)

/-- A geometry read from its full primitive data is recovered up to the
native equivalence's canonical isomorphism. -/
noncomputable def semanticComparisonObject_reconstructionIso
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U) :
    (equivalence (semanticComparisonParameter U)).inverse.obj
      ((reading (semanticComparisonParameter U)).obj
        (semanticComparisonNativeObject G)) ≅
      semanticComparisonNativeObject G :=
  (equivalence (semanticComparisonParameter U)).unitIso.symm.app
    (semanticComparisonNativeObject G)

/-- Primitive reading reflects commuting squares formed by any endpoint
automorphisms and any complete-geometry morphism. -/
theorem semanticComparison_automorphismSquare_iff
    {U : AtomCarrier.{u}} {G H : GeomReadCategory.{u, v} U}
    (f : G ⟶ H)
    (a : Aut (semanticComparisonNativeObject G))
    (b : Aut (semanticComparisonNativeObject H)) :
    a.hom ≫ semanticComparisonNativeHom f =
        semanticComparisonNativeHom f ≫ b.hom ↔
      (reading (semanticComparisonParameter U)).map a.hom ≫
          (reading (semanticComparisonParameter U)).map
            (semanticComparisonNativeHom f) =
        (reading (semanticComparisonParameter U)).map
            (semanticComparisonNativeHom f) ≫
          (reading (semanticComparisonParameter U)).map b.hom := by
  constructor
  · intro h
    simpa only [← Functor.map_comp] using
      congrArg (reading (semanticComparisonParameter U)).map h
  · intro h
    apply (homEquiv (semanticComparisonParameter U)
      (semanticComparisonNativeObject G)
      (semanticComparisonNativeObject H)).injective
    change (reading (semanticComparisonParameter U)).map
        (a.hom ≫ semanticComparisonNativeHom f) =
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonNativeHom f ≫ b.hom)
    simpa only [Functor.map_comp] using h

/-- Primitive reading separates all automorphisms of each semantic geometry,
including both generated comparison endpoints. -/
theorem semanticComparison_automorphism_eq_of_read_eq
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    {a b : Aut (semanticComparisonNativeObject G)}
    (h : (reading (semanticComparisonParameter U)).map a.hom =
      (reading (semanticComparisonParameter U)).map b.hom) : a = b := by
  apply Iso.ext
  exact (homEquiv (semanticComparisonParameter U)
    (semanticComparisonNativeObject G)
    (semanticComparisonNativeObject G)).injective h

/-- Assemble both arrows of a local endpoint automorphism into the original
complete-geometry category. -/
noncomputable def semanticComparisonAutomorphismAssemble
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (localAut : Aut ((reading (semanticComparisonParameter U)).obj
      (semanticComparisonNativeObject G))) :
    Aut (semanticComparisonNativeObject G) where
  hom := assembleHom (semanticComparisonParameter U) localAut.hom
  inv := assembleHom (semanticComparisonParameter U) localAut.inv
  hom_inv_id := by
    apply (homEquiv (semanticComparisonParameter U)
      (semanticComparisonNativeObject G)
      (semanticComparisonNativeObject G)).injective
    change (reading (semanticComparisonParameter U)).map
        (assembleHom (semanticComparisonParameter U) localAut.hom ≫
          assembleHom (semanticComparisonParameter U) localAut.inv) =
      (reading (semanticComparisonParameter U)).map (𝟙 _)
    rw [Functor.map_comp, read_assembleHom, read_assembleHom]
    exact localAut.hom_inv_id.trans
      ((reading (semanticComparisonParameter U)).map_id _).symm
  inv_hom_id := by
    apply (homEquiv (semanticComparisonParameter U)
      (semanticComparisonNativeObject G)
      (semanticComparisonNativeObject G)).injective
    change (reading (semanticComparisonParameter U)).map
        (assembleHom (semanticComparisonParameter U) localAut.inv ≫
          assembleHom (semanticComparisonParameter U) localAut.hom) =
      (reading (semanticComparisonParameter U)).map (𝟙 _)
    rw [Functor.map_comp, read_assembleHom, read_assembleHom]
    exact localAut.inv_hom_id.trans
      ((reading (semanticComparisonParameter U)).map_id _).symm

/-- Every local endpoint automorphism has exactly one native preimage, with
inverse given by primitive Hom assembly. -/
noncomputable def semanticComparisonAutomorphismEquiv
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U) :
    Aut (semanticComparisonNativeObject G) ≃
      Aut ((reading (semanticComparisonParameter U)).obj
        (semanticComparisonNativeObject G)) where
  toFun := (reading (semanticComparisonParameter U)).mapIso
  invFun := semanticComparisonAutomorphismAssemble G
  left_inv := by
    intro a
    apply Iso.ext
    exact assembleHom_read (semanticComparisonParameter U) a.hom
  right_inv := by
    intro a
    apply Iso.ext
    exact read_assembleHom (semanticComparisonParameter U) a.hom

/-- A commuting square between arbitrary local endpoint automorphisms is
equivalent to the square formed by their uniquely assembled native preimages. -/
theorem semanticComparisonLocalAutomorphismSquare_iff
    {U : AtomCarrier.{u}} {G H : GeomReadCategory.{u, v} U}
    (f : G ⟶ H)
    (a : Aut ((reading (semanticComparisonParameter U)).obj
      (semanticComparisonNativeObject G)))
    (b : Aut ((reading (semanticComparisonParameter U)).obj
      (semanticComparisonNativeObject H))) :
    (semanticComparisonAutomorphismAssemble G a).hom ≫
        semanticComparisonNativeHom f =
      semanticComparisonNativeHom f ≫
        (semanticComparisonAutomorphismAssemble H b).hom ↔
      a.hom ≫ (reading (semanticComparisonParameter U)).map
          (semanticComparisonNativeHom f) =
        (reading (semanticComparisonParameter U)).map
            (semanticComparisonNativeHom f) ≫ b.hom := by
  have ha : (reading (semanticComparisonParameter U)).map
      (semanticComparisonAutomorphismAssemble G a).hom = a.hom :=
    read_assembleHom (semanticComparisonParameter U) a.hom
  have hb : (reading (semanticComparisonParameter U)).map
      (semanticComparisonAutomorphismAssemble H b).hom = b.hom :=
    read_assembleHom (semanticComparisonParameter U) b.hom
  simpa only [ha, hb] using
    semanticComparison_automorphismSquare_iff f
      (semanticComparisonAutomorphismAssemble G a)
      (semanticComparisonAutomorphismAssemble H b)

/-! ## The actual semantic square and its generated maps -/

/-- The original southwest complete geometry, before either derived route. -/
noncomputable def semanticComparisonOriginalNativeObject
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k) :
    NativeCategory (semanticComparisonParameter U) :=
  semanticComparisonNativeObject g.package

/-- The literal direct complete geometry from the semantic left-pull and
top-transport route. -/
noncomputable def semanticComparisonDirectNativeObject
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    NativeCategory (semanticComparisonParameter U) :=
  semanticComparisonNativeObject
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq).1

/-- The literal via-base complete geometry from semantic bottom transport
and right pullback. -/
noncomputable def semanticComparisonViaBaseNativeObject
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    NativeCategory (semanticComparisonParameter U) :=
  semanticComparisonNativeObject
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq).1

/-- Reconstruction of the actual southwest input geometry from its primitive
reading. -/
noncomputable def semanticComparisonOriginal_reconstructionIso
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k) :
    (equivalence (semanticComparisonParameter U)).inverse.obj
      ((reading (semanticComparisonParameter U)).obj
        (semanticComparisonOriginalNativeObject input interpretation z k g)) ≅
      semanticComparisonOriginalNativeObject input interpretation z k g :=
  semanticComparisonObject_reconstructionIso g.package

/-- Reconstruction of the actual direct endpoint from the left pull and top
transport route. -/
noncomputable def semanticComparisonDirect_reconstructionIso
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    (equivalence (semanticComparisonParameter U)).inverse.obj
      ((reading (semanticComparisonParameter U)).obj
        (semanticComparisonDirectNativeObject input interpretation z k g
          endpoint_eq)) ≅
      semanticComparisonDirectNativeObject input interpretation z k g
        endpoint_eq :=
  semanticComparisonObject_reconstructionIso
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1

/-- Reconstruction of the actual via-base endpoint from bottom transport and
right pullback. -/
noncomputable def semanticComparisonViaBase_reconstructionIso
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    (equivalence (semanticComparisonParameter U)).inverse.obj
      ((reading (semanticComparisonParameter U)).obj
        (semanticComparisonViaBaseNativeObject input interpretation z k g
          endpoint_eq)) ≅
      semanticComparisonViaBaseNativeObject input interpretation z k g
        endpoint_eq :=
  semanticComparisonObject_reconstructionIso
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1

/-- Every local automorphism of the generated direct endpoint has a unique
original complete-geometry automorphism. -/
noncomputable def semanticComparisonDirectAutomorphismEquiv
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    Aut (semanticComparisonDirectNativeObject input interpretation z k g
      endpoint_eq) ≃
      Aut ((reading (semanticComparisonParameter U)).obj
        (semanticComparisonDirectNativeObject input interpretation z k g
          endpoint_eq)) :=
  semanticComparisonAutomorphismEquiv
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1

/-- Every local automorphism of the generated via-base endpoint has a unique
original complete-geometry automorphism. -/
noncomputable def semanticComparisonViaBaseAutomorphismEquiv
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    Aut (semanticComparisonViaBaseNativeObject input interpretation z k g
      endpoint_eq) ≃
      Aut ((reading (semanticComparisonParameter U)).obj
        (semanticComparisonViaBaseNativeObject input interpretation z k g
          endpoint_eq)) :=
  semanticComparisonAutomorphismEquiv
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1

section GeneratedComparison

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) =
    input.square.southwest)
variable (square_isPullback : IsPullback input.square.left input.square.top
  input.square.bottom input.square.right)

/-- The generated semantic comparison isomorphism as the actual Hom of the
representative native category. -/
noncomputable def semanticComparisonAlphaNativeHom :
    semanticComparisonDirectNativeObject input interpretation z k g endpoint_eq ⟶
      semanticComparisonViaBaseNativeObject input interpretation z k g endpoint_eq :=
  semanticComparisonNativeHom
    (semanticDerivedBarAlphaIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq square_isPullback).hom.1

/-- The actual G-118 generated mate with both endpoint comparisons and the
unit/counit, regarded as a complete-geometry Hom in the primitive reader's
native category. -/
noncomputable def semanticComparisonG118FiveFactorNativeHom :
    semanticComparisonDirectNativeObject input interpretation z k g endpoint_eq ⟶
      semanticComparisonViaBaseNativeObject input interpretation z k g endpoint_eq :=
  semanticComparisonNativeHom
    ((semanticDerivedUnitTopPushIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom ≫
      (geomFiberTransportFunctor input.square.top).map
        (semanticDerivedBToGeneratedBaseNorthwestIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq square_isPullback).hom ≫
      semanticDerivedGeneratedMateTopPushAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq square_isPullback ≫
      (geomFiberTransportFunctor input.square.top).map
        (semanticDerivedGeneratedPulledToTNorthwestIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq square_isPullback).hom ≫
      (semanticDerivedTopCounitIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom).1

/-- The reconstructed α is precisely the five-factor comparison containing
the actual G-118 generated mate, with its unit, endpoint, and counit maps. -/
theorem semanticComparisonAlpha_eq_G118FiveFactor :
    semanticComparisonAlphaNativeHom input interpretation z k g endpoint_eq
        square_isPullback =
      semanticComparisonG118FiveFactorNativeHom input interpretation z k g
        endpoint_eq square_isPullback := by
  apply ULift.ext
  exact congrArg Subtype.val
    (semanticDerivedBarAlphaIsoAt_generatedFiveFactor_hom input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq square_isPullback)

/-- The primitive reading of α therefore reads the same five-factor G-118
generated mate and endpoint comparison composite. -/
theorem semanticComparisonReadAlpha_eq_G118FiveFactor :
    (reading (semanticComparisonParameter U)).map
        (semanticComparisonAlphaNativeHom input interpretation z k g
          endpoint_eq square_isPullback) =
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonG118FiveFactorNativeHom input interpretation z k g
          endpoint_eq square_isPullback) := by
  rw [semanticComparisonAlpha_eq_G118FiveFactor]

/-- The cochain-selected semantic comparison as an actual complete-geometry
Hom, before primitive reading. -/
noncomputable def semanticComparisonBetaNativeHom :
    semanticComparisonDirectNativeObject input interpretation z k g endpoint_eq ⟶
      semanticComparisonViaBaseNativeObject input interpretation z k g endpoint_eq :=
  semanticComparisonNativeHom
    (semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
      square_isPullback).1

/-- The semantic source projector as an actual complete-geometry Hom. -/
noncomputable def semanticComparisonENativeHom :
    semanticComparisonDirectNativeObject input interpretation z k g endpoint_eq ⟶
      semanticComparisonDirectNativeObject input interpretation z k g endpoint_eq :=
  semanticComparisonNativeHom
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback).1

/-- The semantic target projector as an actual complete-geometry Hom. -/
noncomputable def semanticComparisonDNativeHom :
    semanticComparisonViaBaseNativeObject input interpretation z k g endpoint_eq ⟶
      semanticComparisonViaBaseNativeObject input interpretation z k g endpoint_eq :=
  semanticComparisonNativeHom
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq).1

/-- Reading and reassembling the semantic generated comparison returns the
original α, with its complete geometry components. -/
theorem semanticComparisonAlpha_assemble_read :
    assembleHom (semanticComparisonParameter U)
        ((reading (semanticComparisonParameter U)).map
          (semanticComparisonAlphaNativeHom input interpretation z k g
            endpoint_eq square_isPullback)) =
      semanticComparisonAlphaNativeHom input interpretation z k g
        endpoint_eq square_isPullback :=
  semanticComparisonHom_assemble_read _

/-- Reading and reassembling the cochain-selected comparison returns the
original β. -/
theorem semanticComparisonBeta_assemble_read :
    assembleHom (semanticComparisonParameter U)
        ((reading (semanticComparisonParameter U)).map
          (semanticComparisonBetaNativeHom input interpretation z omega k g
            endpoint_eq square_isPullback)) =
      semanticComparisonBetaNativeHom input interpretation z omega k g
        endpoint_eq square_isPullback :=
  semanticComparisonHom_assemble_read _

/-- Reading and reassembling the source projector returns the original e. -/
theorem semanticComparisonE_assemble_read :
    assembleHom (semanticComparisonParameter U)
        ((reading (semanticComparisonParameter U)).map
          (semanticComparisonENativeHom input interpretation z omega k g
            endpoint_eq square_isPullback)) =
      semanticComparisonENativeHom input interpretation z omega k g
        endpoint_eq square_isPullback :=
  semanticComparisonHom_assemble_read _

/-- Reading and reassembling the target projector returns the original d. -/
theorem semanticComparisonD_assemble_read :
    assembleHom (semanticComparisonParameter U)
        ((reading (semanticComparisonParameter U)).map
          (semanticComparisonDNativeHom input interpretation z omega k g
            endpoint_eq)) =
      semanticComparisonDNativeHom input interpretation z omega k g
        endpoint_eq :=
  semanticComparisonHom_assemble_read _

/-- The semantic β is the original generated α followed by the selected
target projector in the representative native category. -/
theorem semanticComparisonBeta_factor :
    semanticComparisonBetaNativeHom input interpretation z omega k g
        endpoint_eq square_isPullback =
      semanticComparisonAlphaNativeHom input interpretation z k g
          endpoint_eq square_isPullback ≫
        semanticComparisonDNativeHom input interpretation z omega k g
          endpoint_eq := by
  apply ULift.ext
  rfl

/-- Both semantic endpoint projectors retain their idempotence as native
complete-geometry Homs. -/
theorem semanticComparisonE_idem :
    semanticComparisonENativeHom input interpretation z omega k g
        endpoint_eq square_isPullback ≫
      semanticComparisonENativeHom input interpretation z omega k g
        endpoint_eq square_isPullback =
      semanticComparisonENativeHom input interpretation z omega k g
        endpoint_eq square_isPullback := by
  apply ULift.ext
  exact congrArg Subtype.val
    (semanticExactBarEAt_idem input interpretation z omega k g endpoint_eq
      square_isPullback)

theorem semanticComparisonD_idem :
    semanticComparisonDNativeHom input interpretation z omega k g
        endpoint_eq ≫
      semanticComparisonDNativeHom input interpretation z omega k g
        endpoint_eq =
      semanticComparisonDNativeHom input interpretation z omega k g
        endpoint_eq := by
  apply ULift.ext
  exact congrArg Subtype.val
    (semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq)

/-- The two projectors are intertwined by the generated semantic comparison,
as in the fixed equation (8.20). -/
theorem semanticComparisonAlpha_projector_natural :
    semanticComparisonENativeHom input interpretation z omega k g
        endpoint_eq square_isPullback ≫
      semanticComparisonAlphaNativeHom input interpretation z k g
        endpoint_eq square_isPullback =
      semanticComparisonAlphaNativeHom input interpretation z k g
          endpoint_eq square_isPullback ≫
        semanticComparisonDNativeHom input interpretation z omega k g
          endpoint_eq := by
  let α := semanticDerivedBarAlphaIsoAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq square_isPullback
  have h : semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫ α.hom =
      α.hom ≫ semanticExactBarDAt input interpretation z omega k g
        endpoint_eq := by
    simp [semanticExactBarEAt, α, Category.assoc]
  apply ULift.ext
  exact congrArg Subtype.val h

/-- The selected semantic comparison is absorbed by both endpoint
projectors in the native category. -/
theorem semanticComparisonBeta_projector_factorizations :
    (semanticComparisonENativeHom input interpretation z omega k g
        endpoint_eq square_isPullback ≫
      semanticComparisonBetaNativeHom input interpretation z omega k g
        endpoint_eq square_isPullback =
      semanticComparisonBetaNativeHom input interpretation z omega k g
        endpoint_eq square_isPullback) ∧
    (semanticComparisonBetaNativeHom input interpretation z omega k g
        endpoint_eq square_isPullback ≫
      semanticComparisonDNativeHom input interpretation z omega k g
        endpoint_eq =
      semanticComparisonBetaNativeHom input interpretation z omega k g
        endpoint_eq square_isPullback) := by
  constructor
  · apply ULift.ext
    exact congrArg Subtype.val
      (semanticExactBarBetaAt_source_factorization input interpretation z
        omega k g endpoint_eq square_isPullback)
  · apply ULift.ext
    exact congrArg Subtype.val
      (semanticExactBarBetaAt_target_factorization input interpretation z
        omega k g endpoint_eq square_isPullback)

/-- Primitive reading preserves the generated comparison factorization. -/
theorem semanticComparison_read_beta_factor :
    (reading (semanticComparisonParameter U)).map
        (semanticComparisonBetaNativeHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      (reading (semanticComparisonParameter U)).map
          (semanticComparisonAlphaNativeHom input interpretation z k g
            endpoint_eq square_isPullback) ≫
        (reading (semanticComparisonParameter U)).map
          (semanticComparisonDNativeHom input interpretation z omega k g
            endpoint_eq) := by
  rw [semanticComparisonBeta_factor, Functor.map_comp]

/-- Primitive reading preserves the other two equations of (8.20). -/
theorem semanticComparison_read_projector_laws :
    ((reading (semanticComparisonParameter U)).map
        (semanticComparisonENativeHom input interpretation z omega k g
          endpoint_eq square_isPullback)) ≫
      ((reading (semanticComparisonParameter U)).map
        (semanticComparisonENativeHom input interpretation z omega k g
          endpoint_eq square_isPullback)) =
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonENativeHom input interpretation z omega k g
          endpoint_eq square_isPullback) ∧
    ((reading (semanticComparisonParameter U)).map
        (semanticComparisonDNativeHom input interpretation z omega k g
          endpoint_eq)) ≫
      ((reading (semanticComparisonParameter U)).map
        (semanticComparisonDNativeHom input interpretation z omega k g
          endpoint_eq)) =
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonDNativeHom input interpretation z omega k g
          endpoint_eq) := by
  constructor
  · rw [← Functor.map_comp, semanticComparisonE_idem]
  · rw [← Functor.map_comp, semanticComparisonD_idem]

/-- The primitive local square retains α's intertwining with the two
generated projectors. -/
theorem semanticComparison_read_alpha_projector_natural :
    (reading (semanticComparisonParameter U)).map
        (semanticComparisonENativeHom input interpretation z omega k g
          endpoint_eq square_isPullback) ≫
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonAlphaNativeHom input interpretation z k g
          endpoint_eq square_isPullback) =
      (reading (semanticComparisonParameter U)).map
          (semanticComparisonAlphaNativeHom input interpretation z k g
            endpoint_eq square_isPullback) ≫
        (reading (semanticComparisonParameter U)).map
          (semanticComparisonDNativeHom input interpretation z omega k g
            endpoint_eq) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    semanticComparisonAlpha_projector_natural]

/-- The primitive local model also retains absorption of β by both
projectors. -/
theorem semanticComparison_read_beta_projector_factorizations :
    ((reading (semanticComparisonParameter U)).map
        (semanticComparisonENativeHom input interpretation z omega k g
          endpoint_eq square_isPullback) ≫
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonBetaNativeHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonBetaNativeHom input interpretation z omega k g
          endpoint_eq square_isPullback)) ∧
    ((reading (semanticComparisonParameter U)).map
        (semanticComparisonBetaNativeHom input interpretation z omega k g
          endpoint_eq square_isPullback) ≫
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonDNativeHom input interpretation z omega k g
          endpoint_eq) =
      (reading (semanticComparisonParameter U)).map
        (semanticComparisonBetaNativeHom input interpretation z omega k g
          endpoint_eq square_isPullback)) := by
  obtain ⟨hsource, htarget⟩ :=
    semanticComparisonBeta_projector_factorizations input interpretation z
      omega k g endpoint_eq square_isPullback
  constructor
  · rw [← Functor.map_comp, hsource]
  · rw [← Functor.map_comp, htarget]

/-- For every complete-geometry Hom between the two actual semantic route
endpoints, primitive reading preserves and reflects every commuting square of
their unrestricted endpoint automorphisms. -/
theorem semanticComparisonGeneratedSquare_iff
    (f : (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1 ⟶
      (semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1)
    (a : Aut (semanticComparisonDirectNativeObject input interpretation z
      k g endpoint_eq))
    (b : Aut (semanticComparisonViaBaseNativeObject input interpretation z
      k g endpoint_eq)) :
    a.hom ≫ semanticComparisonNativeHom f =
        semanticComparisonNativeHom f ≫ b.hom ↔
      (reading (semanticComparisonParameter U)).map a.hom ≫
          (reading (semanticComparisonParameter U)).map
            (semanticComparisonNativeHom f) =
        (reading (semanticComparisonParameter U)).map
            (semanticComparisonNativeHom f) ≫
          (reading (semanticComparisonParameter U)).map b.hom :=
  semanticComparison_automorphismSquare_iff f a b

/-- Every commuting square made from local endpoint automorphisms and an
arbitrary local comparison Hom comes from the unique corresponding native
square. -/
theorem semanticComparisonGeneratedLocalSquare_iff
    (f : (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1 ⟶
      (semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1)
    (a : Aut ((reading (semanticComparisonParameter U)).obj
      (semanticComparisonDirectNativeObject input interpretation z k g
        endpoint_eq)))
    (b : Aut ((reading (semanticComparisonParameter U)).obj
      (semanticComparisonViaBaseNativeObject input interpretation z k g
        endpoint_eq))) :
    (semanticComparisonAutomorphismAssemble
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq).1 a).hom ≫ semanticComparisonNativeHom f =
      semanticComparisonNativeHom f ≫
        (semanticComparisonAutomorphismAssemble
          (semanticDerivedViaBaseGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z)
            k g endpoint_eq).1 b).hom ↔
      a.hom ≫ (reading (semanticComparisonParameter U)).map
          (semanticComparisonNativeHom f) =
        (reading (semanticComparisonParameter U)).map
            (semanticComparisonNativeHom f) ≫ b.hom :=
  semanticComparisonLocalAutomorphismSquare_iff f a b

end GeneratedComparison

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction
