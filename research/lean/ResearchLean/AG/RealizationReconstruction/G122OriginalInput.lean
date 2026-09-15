import ResearchLean.AG.FullGeometryNormalization.ExactDerivedRefinementBC
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness
import Formal.Util.AssertStandardAxioms

/-!
# The original G-122 input, separated from its generated constructions

G-123(D) must preserve the full common-input range of G-122 while refusing to
move the comparisons and transports that G-122 constructs back into the input.
This module records that dependency split.  The family parameter contains the
arbitrary Atom carrier, authored square, coefficient carrier, and their
algebraic instances.  A semantic object is then quantified after that
parameter and contains the original cell, cochain, selected geometry, and raw
restriction data.

`AuthoredBCDatumSquare` and `FixedCoefficientGeometryAt` are accepted original
inputs of the fixed G-122 theorem.  This file does not claim that they have
already been reconstructed from G-123 finite syntax.  In particular no source
transport, generated mate, `barAlpha`, `barBeta`, normalization, comparison
group element, section, kernel, or lift fiber is an input field.

## Implementation notes

The original-cell geometry hom below is deliberately the existing
`GeometryTotalHom` between the packages assembled from two arbitrary original
cell inputs.  It is defined before, and without reference to, any finite
display or operation-path syntax.  This fixes an all-component semantic
subcategory on the southwest input packages whose later enlargement must also
contain the generated northeast comparison endpoints; the abbrev itself
supplies neither that enlargement, representability, nor fullness.

The generated-object type later in the file performs exactly that first
enlargement from the same original input: constructor tags are interpreted by
the fixed transport and pullback constructions, and its Hom contains every
`GeometryTotalHom` between the resulting packages.  It is a required G-122
branch, not yet the cross-family final realization category.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence
open FullGeometryNormalization TransportCoherence

universe u v

local instance finiteAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The cell-independent parameters in a dependency-equivalent rearrangement
of the fixed G-122 quantifier range. -/
structure G122FamilyInput where
  /-- Arbitrary Atom carrier; no finiteness is imposed. -/
  Carrier : AtomCarrier.{u}
  /-- The exact decidable-equality input fixed by G-122. -/
  atomDecidableEq : DecidableEq Carrier.Atom
  /-- The original authored square, before any exact-derived construction. -/
  authored : @AuthoredBCDatumSquare Carrier atomDecidableEq
  /-- Arbitrary coefficient carrier. -/
  Coefficient : Type v
  /-- The coefficient-ring structure fixed by G-122. -/
  coefficientCommRing : CommRing Coefficient

/-- The cell-specific original G-122 input, quantified after one family
parameter.  Selected geometry and raw restriction data are kept as their two
source fields rather than accepting the assembled `GeometryPackage`. -/
structure G122CellInput (Θ : G122FamilyInput.{u, v}) where
  /-- Arbitrary cell of the original authored square. -/
  cell : let _ := Θ.atomDecidableEq; Θ.authored.context.Category
  /-- Arbitrary original cochain, including the required generated cochain as
  a later specialization. -/
  cochain : let _ := Θ.atomDecidableEq; DefectCochain Θ.authored.toTransportData
  /-- Selected geometry on the original support core. -/
  selectedGeometry :
    let _ := Θ.atomDecidableEq
    Site.SelectedGeometryReading
      (Θ.authored.context.supportPackage cell.as)
  /-- Original raw restriction data over the fixed coefficient carrier. -/
  raw :
    let _ := Θ.atomDecidableEq
    let _ := Θ.coefficientCommRing
    LawAlgebra.RawAmbientRestrictionSystem
      selectedGeometry.toAATSite Θ.Coefficient

namespace G122CellInput

/-- Reassemble exactly the accepted G-122 geometry input from its two source
fields.  The complete geometry package remains a constructed output. -/
def fixedGeometry (Θ : G122FamilyInput.{u, v}) (X : G122CellInput Θ) :
    let _ := Θ.atomDecidableEq
    let _ := Θ.coefficientCommRing
    FixedCoefficientGeometryAt
      (Θ.authored.context.supportPackage X.cell.as) Θ.Coefficient := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact { geometry := X.selectedGeometry, raw := X.raw }

/-- Assemble the geometry package only after receiving the original selected
geometry and raw fields. -/
def geometryPackage (Θ : G122FamilyInput.{u, v}) (X : G122CellInput Θ) :
    let _ := Θ.atomDecidableEq
    let _ := Θ.coefficientCommRing
    GeometryPackage.{u, v} Θ.Carrier := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact (X.fixedGeometry Θ).package

/-- The independent complete-geometry morphism type for two arbitrary G-122
original-cell inputs under one family input.  This is the existing all-component
geometry morphism and is not defined by finite-display representability. -/
abbrev G122OriginalCellGeometryHom
    (Θ : G122FamilyInput.{u, v}) (X Y : G122CellInput Θ) :=
  let _ := Θ.atomDecidableEq
  let _ := Θ.coefficientCommRing
  GeometryTotalHom (X.geometryPackage Θ) (Y.geometryPackage Θ)

namespace G122OriginalCellGeometryHom

/-- Identity in the independent original-cell geometry hom type. -/
noncomputable def id
    (Θ : G122FamilyInput.{u, v}) (X : G122CellInput Θ) :
    G122OriginalCellGeometryHom Θ X X := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact GeometryTotalHom.id (X.geometryPackage Θ)

/-- Composition in the independent original-cell geometry hom type. -/
noncomputable def comp
    (Θ : G122FamilyInput.{u, v}) {X Y Z : G122CellInput Θ}
    (first : G122OriginalCellGeometryHom Θ X Y)
    (second : G122OriginalCellGeometryHom Θ Y Z) :
    G122OriginalCellGeometryHom Θ X Z := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact GeometryTotalHom.comp first second

/-- Complete-geometry morphisms are equal from equality of the full core map
and heterogeneous equality of the geometry comparison, rather than from a
finite restriction equality. -/
theorem ext
    (Θ : G122FamilyInput.{u, v}) {X Y : G122CellInput Θ}
    {first second : G122OriginalCellGeometryHom Θ X Y}
    (hbase : first.base = second.base)
    (hgeometry : HEq first.geometry second.geometry) : first = second := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact GeometryTotalHom.ext hbase hgeometry

/-- Left identity for independently fixed complete-geometry morphisms. -/
theorem id_comp
    (Θ : G122FamilyInput.{u, v}) {X Y : G122CellInput Θ}
    (f : G122OriginalCellGeometryHom Θ X Y) :
    comp Θ (id Θ X) f = f := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  change (𝟙 (X.geometryPackage Θ)) ≫ f = f
  simp

/-- Right identity for independently fixed complete-geometry morphisms. -/
theorem comp_id
    (Θ : G122FamilyInput.{u, v}) {X Y : G122CellInput Θ}
    (f : G122OriginalCellGeometryHom Θ X Y) :
    comp Θ f (id Θ Y) = f := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  change f ≫ (𝟙 (Y.geometryPackage Θ)) = f
  simp

/-- Associativity for independently fixed complete-geometry morphisms. -/
theorem comp_assoc
    (Θ : G122FamilyInput.{u, v}) {W X Y Z : G122CellInput Θ}
    (first : G122OriginalCellGeometryHom Θ W X)
    (second : G122OriginalCellGeometryHom Θ X Y)
    (third : G122OriginalCellGeometryHom Θ Y Z) :
    comp Θ (comp Θ first second) third =
      comp Θ first (comp Θ second third) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  change GeometryTotalHom.comp (GeometryTotalHom.comp first second) third =
    GeometryTotalHom.comp first (GeometryTotalHom.comp second third)
  exact @Category.assoc
    (GeomReadCategory Θ.Carrier) (geometryTotalCategory Θ.Carrier)
    (W.geometryPackage Θ) (X.geometryPackage Θ)
    (Y.geometryPackage Θ) (Z.geometryPackage Θ) first second third

end G122OriginalCellGeometryHom

/-- Arbitrary original G-122 cell inputs form an independent semantic
subcategory whose arrows are all existing `GeometryTotalHom`s between their
assembled southwest packages.  This does not yet include the generated
northeast comparison endpoints.  No finite presentation or decoder image
occurs in this category instance. -/
noncomputable instance g122OriginalCellGeometryCategory
    (Θ : G122FamilyInput.{u, v}) : Category (G122CellInput Θ) where
  Hom := G122OriginalCellGeometryHom Θ
  id := G122OriginalCellGeometryHom.id Θ
  comp := G122OriginalCellGeometryHom.comp Θ
  id_comp := G122OriginalCellGeometryHom.id_comp Θ
  comp_id := G122OriginalCellGeometryHom.comp_id Θ
  assoc := G122OriginalCellGeometryHom.comp_assoc Θ

/-- The exact-derived local transport is generated from the original inputs;
it is not a field of either input structure. -/
noncomputable def sourceTransport
    (Θ : G122FamilyInput.{u, v}) (X : G122CellInput Θ) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact authoredExactSourceTransportAt Θ.authored X.cell Θ.Coefficient
    (X.fixedGeometry Θ)

/-- The generated compatible problem data, including its source transport, is
likewise an output of the original input. -/
noncomputable def compatibleProblemData
    (Θ : G122FamilyInput.{u, v}) (X : G122CellInput Θ) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact authoredExactCompatibleProblemDataAt Θ.authored X.cell Θ.Coefficient
    (X.fixedGeometry Θ)

/-- The selected exact comparison is generated only after the arbitrary
cochain is supplied.  In particular the comparison itself is not an input
field or a membership condition. -/
noncomputable def barBeta
    (Θ : G122FamilyInput.{u, v}) (X : G122CellInput Θ) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact authoredExactBarBetaAt Θ.authored X.cell X.cochain Θ.Coefficient
    (X.fixedGeometry Θ)

/-- The required generated cochain is an inhabitant of the same cochain type;
the general input is not narrowed to this one value. -/
noncomputable def initialCochain (Θ : G122FamilyInput.{u, v}) :
    let _ := Θ.atomDecidableEq
    DefectCochain Θ.authored.toTransportData := by
  letI := Θ.atomDecidableEq
  exact initialRawDefectCochain Θ.authored.toTransportData

end G122CellInput

/-! ## Display-independent objects for the generated G-122 comparison -/

/-- The source-generated geometry objects required to place the actual G-122
comparison in one category.  The constructors retain an arbitrary original
cell input and add its direct and via-base northeast endpoints; they do not
depend on a finite display or on successful decoding. -/
inductive G122GeneratedGeometryObject (Θ : G122FamilyInput.{u, v})
  /-- The original southwest package before generated transport. -/
  | original (input : G122CellInput Θ)
  /-- The direct-route generated northeast endpoint. -/
  | direct (input : G122CellInput Θ)
  /-- The via-base generated northeast endpoint. -/
  | viaBase (input : G122CellInput Θ)

namespace G122GeneratedGeometryObject

/-- Interpret a generated-object constructor as its actual complete geometry
package.  The northeast branches are constructed by the fixed G-122 transport
and pullback routes from the original input. -/
noncomputable def package
    (Θ : G122FamilyInput.{u, v}) :
    G122GeneratedGeometryObject Θ → GeometryPackage.{u, v} Θ.Carrier
  | .original input => input.geometryPackage Θ
  | .direct input => by
      letI := Θ.atomDecidableEq
      letI := Θ.coefficientCommRing
      exact (authoredExactDirectGeometryAt Θ.authored input.cell Θ.Coefficient
        (input.fixedGeometry Θ)).1
  | .viaBase input => by
      letI := Θ.atomDecidableEq
      letI := Θ.coefficientCommRing
      exact (authoredExactViaBaseGeometryAt Θ.authored input.cell Θ.Coefficient
        (input.fixedGeometry Θ)).1

/-- All complete-geometry morphisms between two generated G-122 objects.  The
Hom type is independent of finite syntax and is not restricted to the actual
`barAlpha` or `barBeta` images. -/
abbrev Hom (Θ : G122FamilyInput.{u, v})
    (X Y : G122GeneratedGeometryObject Θ) :=
  GeometryTotalHom (X.package Θ) (Y.package Θ)

/-- Identity generated-object morphism. -/
noncomputable def id (Θ : G122FamilyInput.{u, v})
    (X : G122GeneratedGeometryObject Θ) : Hom Θ X X :=
  GeometryTotalHom.id (X.package Θ)

/-- Composition of arbitrary complete-geometry morphisms between generated
objects. -/
noncomputable def comp (Θ : G122FamilyInput.{u, v})
    {X Y Z : G122GeneratedGeometryObject Θ}
    (first : Hom Θ X Y) (second : Hom Θ Y Z) : Hom Θ X Z :=
  GeometryTotalHom.comp first second

/-- Left identity for generated-object morphisms. -/
theorem id_comp (Θ : G122FamilyInput.{u, v})
    {X Y : G122GeneratedGeometryObject Θ} (f : Hom Θ X Y) :
    comp Θ (id Θ X) f = f := by
  change (𝟙 (X.package Θ)) ≫ f = f
  simp

/-- Right identity for generated-object morphisms. -/
theorem comp_id (Θ : G122FamilyInput.{u, v})
    {X Y : G122GeneratedGeometryObject Θ} (f : Hom Θ X Y) :
    comp Θ f (id Θ Y) = f := by
  change f ≫ (𝟙 (Y.package Θ)) = f
  simp

/-- Associativity for generated-object morphisms. -/
theorem comp_assoc (Θ : G122FamilyInput.{u, v})
    {W X Y Z : G122GeneratedGeometryObject Θ}
    (first : Hom Θ W X) (second : Hom Θ X Y) (third : Hom Θ Y Z) :
    comp Θ (comp Θ first second) third =
      comp Θ first (comp Θ second third) := by
  change GeometryTotalHom.comp (GeometryTotalHom.comp first second) third =
    GeometryTotalHom.comp first (GeometryTotalHom.comp second third)
  exact @Category.assoc
    (GeomReadCategory Θ.Carrier) (geometryTotalCategory Θ.Carrier)
    (W.package Θ) (X.package Θ) (Y.package Θ) (Z.package Θ)
    first second third

/-- Original and generated endpoint packages form a category with every
existing complete-geometry morphism between them. -/
noncomputable instance category (Θ : G122FamilyInput.{u, v}) :
    Category (G122GeneratedGeometryObject Θ) where
  Hom := Hom Θ
  id := id Θ
  comp := comp Θ
  id_comp := id_comp Θ
  comp_id := comp_id Θ
  assoc := comp_assoc Θ

/-- The actual five-factor `barAlpha` is a morphism between the two generated
northeast endpoint objects. -/
noncomputable def barAlpha (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    Hom Θ (.direct input) (.viaBase input) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact (authoredExactBarAlphaIsoAt Θ.authored input.cell Θ.Coefficient
    (input.fixedGeometry Θ)).hom.1

/-- The actual five-factor `barAlpha` remains an isomorphism after embedding
both generated endpoints and all complete-geometry morphisms in this category.
The inverse is the underlying morphism of the source-generated inverse, not an
additional input or a display certificate. -/
noncomputable def barAlphaIso (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    G122GeneratedGeometryObject.direct input ≅
      G122GeneratedGeometryObject.viaBase input := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  let comparison := authoredExactBarAlphaIsoAt Θ.authored input.cell
    Θ.Coefficient (input.fixedGeometry Θ)
  exact
    { hom := comparison.hom.1
      inv := comparison.inv.1
      hom_inv_id := congrArg Subtype.val comparison.hom_inv_id
      inv_hom_id := congrArg Subtype.val comparison.inv_hom_id }

/-- The actual cochain-selected `barBeta` is a morphism between the same two
generated northeast endpoint objects. -/
noncomputable def barBeta (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    Hom Θ (.direct input) (.viaBase input) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact (authoredExactBarBetaAt Θ.authored input.cell input.cochain Θ.Coefficient
    (input.fixedGeometry Θ)).1

/-- The source projector generated from the actual cochain is an endomorphism
of the direct endpoint object. -/
noncomputable def barE (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) : Hom Θ (.direct input) (.direct input) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact (authoredExactBarEAt Θ.authored input.cell input.cochain Θ.Coefficient
    (input.fixedGeometry Θ)).1

/-- The target projector generated from the actual cochain is an endomorphism
of the via-base endpoint object. -/
noncomputable def barD (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) : Hom Θ (.viaBase input) (.viaBase input) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact (authoredExactBarDAt Θ.authored input.cell input.cochain Θ.Coefficient
    (input.fixedGeometry Θ)).1

/-- The embedded selected comparison is the embedded actual `barAlpha`
followed by the target projector. -/
theorem barBeta_factor (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    barBeta Θ input = comp Θ (barAlpha Θ input) (barD Θ input) := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact congrArg Subtype.val
    (authoredExactBarBetaAt_factor Θ.authored input.cell input.cochain
      Θ.Coefficient (input.fixedGeometry Θ))

/-- The generated source projector remains idempotent in the enlarged
display-independent category. -/
theorem barE_idem (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    comp Θ (barE Θ input) (barE Θ input) = barE Θ input := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact congrArg Subtype.val
    (authoredExactBarEAt_idem Θ.authored input.cell input.cochain Θ.Coefficient
      (input.fixedGeometry Θ))

/-- The generated target projector remains idempotent in the enlarged
display-independent category. -/
theorem barD_idem (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    comp Θ (barD Θ input) (barD Θ input) = barD Θ input := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact congrArg Subtype.val
    (authoredExactBarDAt_idem Θ.authored input.cell input.cochain Θ.Coefficient
      (input.fixedGeometry Θ))

/-- The embedded selected comparison is fixed by its source projector. -/
theorem barBeta_source_factorization (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    comp Θ (barE Θ input) (barBeta Θ input) = barBeta Θ input := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact congrArg Subtype.val
    (authoredExactBarBetaAt_source_factorization Θ.authored input.cell
      input.cochain Θ.Coefficient (input.fixedGeometry Θ))

/-- The embedded selected comparison is fixed by its target projector. -/
theorem barBeta_target_factorization (Θ : G122FamilyInput.{u, v})
    (input : G122CellInput Θ) :
    comp Θ (barBeta Θ input) (barD Θ input) = barBeta Θ input := by
  letI := Θ.atomDecidableEq
  letI := Θ.coefficientCommRing
  exact congrArg Subtype.val
    (authoredExactBarBetaAt_target_factorization Θ.authored input.cell
      input.cochain Θ.Coefficient (input.fixedGeometry Θ))

end G122GeneratedGeometryObject

/-- The original finite axis-fold family is an instance of the general G-122
family input; the general branch is not defined by this witness. -/
noncomputable def finiteAxisFoldG122FamilyInput : G122FamilyInput.{0, 0} where
  Carrier := FiniteModel.carrier
  atomDecidableEq := finiteAxisFoldAtomDecidableEq
  authored := finiteAxisFoldBCDatumSquare
  Coefficient := Int
  coefficientCommRing := inferInstance

/-- The card-mandated second cell, generated cochain, and original integral
geometry/raw data inhabit the general input decomposition with the same values
used by G-122(C). -/
noncomputable def finiteAxisFoldG122CellInput :
    G122CellInput finiteAxisFoldG122FamilyInput where
  cell := Discrete.mk DoubleDiamondTwoCell.second
  cochain := initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
  selectedGeometry :=
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second)).geometry
  raw :=
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second)).raw

/-- The card-mandated constant-one cochain case on exactly the same finite
axis-fold cell and geometry input. -/
noncomputable def finiteAxisFoldIdentityCochainG122CellInput :
    G122CellInput finiteAxisFoldG122FamilyInput where
  cell := Discrete.mk DoubleDiamondTwoCell.second
  cochain := identityDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
  selectedGeometry :=
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second)).geometry
  raw :=
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second)).raw

/-- Reassembly preserves the exact fixed geometry input used by G-122(C). -/
theorem finiteAxisFoldG122CellInput_fixedGeometry :
    finiteAxisFoldG122CellInput.fixedGeometry finiteAxisFoldG122FamilyInput =
      finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second) :=
  rfl

/-- Reassembly of the constant-one case preserves the same fixed geometry
input; only the cochain differs from the generated-cochain case. -/
theorem finiteAxisFoldIdentityCochainG122CellInput_fixedGeometry :
    finiteAxisFoldIdentityCochainG122CellInput.fixedGeometry
        finiteAxisFoldG122FamilyInput =
      finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second) :=
  rfl

/-- The generated direct endpoint package is unchanged when only the cochain
is replaced by the constant-one cochain. -/
theorem finiteAxisFold_direct_package_identityCochain :
    (G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput).package
        finiteAxisFoldG122FamilyInput =
      (G122GeneratedGeometryObject.direct
        finiteAxisFoldIdentityCochainG122CellInput).package
          finiteAxisFoldG122FamilyInput :=
  rfl

/-- The generated via-base endpoint package is unchanged when only the
cochain is replaced by the constant-one cochain. -/
theorem finiteAxisFold_viaBase_package_identityCochain :
    (G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput).package
        finiteAxisFoldG122FamilyInput =
      (G122GeneratedGeometryObject.viaBase
        finiteAxisFoldIdentityCochainG122CellInput).package
          finiteAxisFoldG122FamilyInput :=
  rfl

/-- The finite specialization generates the same actual comparison classified
by G-122(C); it does not substitute a simpler comparison. -/
theorem finiteAxisFoldG122CellInput_barBeta :
    finiteAxisFoldG122CellInput.barBeta finiteAxisFoldG122FamilyInput =
      authoredExactBarBetaAt finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second)) :=
  rfl

/-- Cycle 43's embedded comparison at the generated-cochain input is exactly
the fixed nontrivial G-122 comparison, with only the fiber-incidence proof
forgotten. -/
theorem finiteAxisFold_generatedGeometry_barBeta :
    G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput =
      (authoredExactBarBetaAt finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))).1 :=
  rfl

/-- The actual five-factor `barAlpha` is shared by the generated and
constant-one cochain cases on the same fixed geometry. -/
theorem finiteAxisFold_barAlpha_identityCochain :
    G122GeneratedGeometryObject.barAlpha finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput =
      G122GeneratedGeometryObject.barAlpha finiteAxisFoldG122FamilyInput
        finiteAxisFoldIdentityCochainG122CellInput :=
  rfl

/-- In the generated-cochain case, the embedded target projector is the
actual transported canonical normalization route selected by G-122. -/
theorem finiteAxisFold_generatedGeometry_barD_eq_normalizationRoute :
    G122GeneratedGeometryObject.barD finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput =
      ((exactGeometryPullFunctor
          (authoredExactRightInput finiteAxisFoldBCDatumSquare)).map
        ((geomFiberTransportFunctor
          finiteAxisFoldBCDatumSquare.context.square.semantic.square.bottom).map
          (canonicalGeometryFiberNormalization
            (authoredSouthwestGeometryFiberAt finiteAxisFoldBCDatumSquare
              (Discrete.mk DoubleDiamondTwoCell.second) Int
              (finiteAxisFoldFixedCoefficientGeometryFamily
                (Discrete.mk DoubleDiamondTwoCell.second)))
            (by
              exact
                (finiteAxisFold_idempotentExchange_witnessPacket).2.1)))).1 := by
  exact congrArg Subtype.val
    (authoredExactBarDAt_eq_normalization_route finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      ⟨(finiteAxisFold_idempotentExchange_witnessPacket).1,
        (finiteAxisFold_idempotentExchange_witnessPacket).2.1⟩)

/-- For the constant-one cochain on the same input geometry, the embedded
target projector is the identity. -/
theorem finiteAxisFold_identityCochain_barD_eq_id :
    G122GeneratedGeometryObject.barD finiteAxisFoldG122FamilyInput
        finiteAxisFoldIdentityCochainG122CellInput =
      G122GeneratedGeometryObject.id finiteAxisFoldG122FamilyInput
        (.viaBase finiteAxisFoldIdentityCochainG122CellInput) := by
  exact congrArg Subtype.val
    (authoredExactBarDAt_eq_id finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      (identityDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      (by
        intro selected
        exact selected.1 rfl))

/-- Thus the constant-one cochain comparison on the fixed input is exactly
the same actual `barAlpha`, not a substituted comparison. -/
theorem finiteAxisFold_identityCochain_barBeta_eq_barAlpha :
    G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
        finiteAxisFoldIdentityCochainG122CellInput =
      G122GeneratedGeometryObject.barAlpha finiteAxisFoldG122FamilyInput
        finiteAxisFoldIdentityCochainG122CellInput := by
  rw [G122GeneratedGeometryObject.barBeta_factor,
    finiteAxisFold_identityCochain_barD_eq_id,
    G122GeneratedGeometryObject.comp_id]

/-- The fixed generated-cochain `barBeta` remains noninvertible in the
generated-object category.  Any inverse of its underlying complete-geometry
arrow would induce an inverse of the original fiber arrow, contradicting the
accepted G-122 finite witness. -/
theorem finiteAxisFold_generatedGeometry_barBeta_not_isIso :
    ¬ @IsIso
      (G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput)
      (G122GeneratedGeometryObject.category finiteAxisFoldG122FamilyInput)
      (G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput)
      (G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput)
      (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput) := by
  intro generatedIso
  letI : @IsIso
      (G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput)
      (G122GeneratedGeometryObject.category finiteAxisFoldG122FamilyInput)
      (G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput)
      (G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput)
      (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput) := generatedIso
  let inverse := @inv
    (G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput)
    (G122GeneratedGeometryObject.category finiteAxisFoldG122FamilyInput)
    (G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput)
    (G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput)
    (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput) _
  letI : @IsIso
      (GeomReadCategory FiniteModel.carrier)
      (geometryTotalCategory FiniteModel.carrier)
      _ _
      (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput) :=
    ⟨⟨inverse, by
      exact @IsIso.hom_inv_id
        (G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput)
        (G122GeneratedGeometryObject.category finiteAxisFoldG122FamilyInput)
        (G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput)
        (G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput)
        (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
          finiteAxisFoldG122CellInput) _, by
      exact @IsIso.inv_hom_id
        (G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput)
        (G122GeneratedGeometryObject.category finiteAxisFoldG122FamilyInput)
        (G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput)
        (G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput)
        (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
          finiteAxisFoldG122CellInput) _⟩⟩
  letI : IsIso
      (authoredExactBarBetaAt finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))).1 := by
    change @IsIso
      (GeomReadCategory FiniteModel.carrier)
      (geometryTotalCategory FiniteModel.carrier)
      _ _
      (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput)
    infer_instance
  have fiberIso : IsIso
      (authoredExactBarBetaAt finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))) :=
    geomFiberHom_isIso_of_total_isIso _
  exact finiteAxisFold_authoredExactBarBetaAt_not_isIso fiberIso

/-- The constant-one `barBeta` is invertible in the same generated-object
category, because it is the unchanged five-factor `barAlpha`. -/
noncomputable def finiteAxisFoldIdentityCochainBarBetaIso :
    G122GeneratedGeometryObject.direct
        finiteAxisFoldIdentityCochainG122CellInput ≅
      G122GeneratedGeometryObject.viaBase
        finiteAxisFoldIdentityCochainG122CellInput := by
  let comparison := G122GeneratedGeometryObject.barAlphaIso
    finiteAxisFoldG122FamilyInput finiteAxisFoldIdentityCochainG122CellInput
  exact
    { hom := G122GeneratedGeometryObject.barBeta
          finiteAxisFoldG122FamilyInput
          finiteAxisFoldIdentityCochainG122CellInput
      inv := comparison.inv
      hom_inv_id := by
        rw [finiteAxisFold_identityCochain_barBeta_eq_barAlpha]
        exact comparison.hom_inv_id
      inv_hom_id := by
        rw [finiteAxisFold_identityCochain_barBeta_eq_barAlpha]
        exact comparison.inv_hom_id }

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
