import ResearchLean.AG.RealizationReconstruction.AATClosedFamilySignature
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedRefinementBC
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness

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
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization TransportCoherence

universe u v

local instance finiteAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The parameters that precede the cell-specific semantic input in the fixed
G-122 quantifier order. -/
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

/-- Reassembly preserves the exact fixed geometry input used by G-122(C). -/
theorem finiteAxisFoldG122CellInput_fixedGeometry :
    finiteAxisFoldG122CellInput.fixedGeometry finiteAxisFoldG122FamilyInput =
      finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second) :=
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

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
