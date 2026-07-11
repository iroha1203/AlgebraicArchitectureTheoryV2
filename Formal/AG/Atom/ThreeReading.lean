import Formal.AG.Atom.Law

namespace AAT.AG

universe u

/--
peer-review hardening I-1: canonical witness family indexed by the required laws of a selected
law universe. A bad witness is no longer an arbitrary token: it is exactly a
selected required law that fails on the architecture object.
-/
def requiredLawWitnessFamily {U : AtomCarrier.{u}} (LU : LawUniverse U) :
    LawWitnessFamily U where
  Witness := { index : LU.Index // LU.Required index }
  badWitness A index := ¬ (LU.law index.1).holds A

/--
peer-review hardening I-1: canonical signature axes indexed by required laws. A selected axis
reads zero exactly when the corresponding required law holds.
-/
def requiredLawSignatureAxes {U : AtomCarrier.{u}} (LU : LawUniverse U) :
    SignatureAxes U where
  Axis := { index : LU.Index // LU.Required index }
  selected _ := True
  zero A index := (LU.law index.1).holds A

/--
peer-review hardening I-1: semantic lawfulness agrees with absence of canonical required-law
bad witnesses. This is an actual theorem about `Lawfulness`, not a projection
from an assumption package.
-/
theorem semanticLawful_iff_noRequiredObstruction_requiredLawWitness
    {U : AtomCarrier.{u}} (A : ArchitectureObject U) (LU : LawUniverse U) :
    SemanticLawful A LU ↔
      NoRequiredObstruction A (requiredLawWitnessFamily LU) := by
  constructor
  · intro h index hbad
    exact hbad (h index.1 index.2)
  · intro h index hrequired
    exact Classical.byContradiction (fun hfail =>
      h ⟨index, hrequired⟩ hfail)

/--
peer-review hardening I-1: semantic lawfulness agrees with zero on the canonical required-law
signature axes.
-/
theorem semanticLawful_iff_requiredSignatureAxesZero_requiredLawAxes
    {U : AtomCarrier.{u}} (A : ArchitectureObject U) (LU : LawUniverse U) :
    SemanticLawful A LU ↔
      RequiredSignatureAxesZero A (requiredLawSignatureAxes LU) := by
  constructor
  · intro h axis _hselected
    exact h axis.1 axis.2
  · intro h index hrequired
    exact h ⟨index, hrequired⟩ trivial

/--
peer-review hardening I-1: the two canonical concrete readings agree. Both sides are tied to
the selected required law predicates, so the theorem cannot be satisfied by
choosing `badWitness := True`.
-/
theorem noRequiredObstruction_iff_requiredSignatureAxesZero_requiredLaw
    {U : AtomCarrier.{u}} (A : ArchitectureObject U) (LU : LawUniverse U) :
    NoRequiredObstruction A (requiredLawWitnessFamily LU) ↔
      RequiredSignatureAxesZero A (requiredLawSignatureAxes LU) :=
  (semanticLawful_iff_noRequiredObstruction_requiredLawWitness A LU).symm.trans
    (semanticLawful_iff_requiredSignatureAxesZero_requiredLawAxes A LU)

/-- peer-review hardening I-1: concrete three-reading agreement for required-law readings. -/
theorem concreteThreeReadingAgreement {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) (LU : LawUniverse U) :
    (SemanticLawful A LU ↔
        NoRequiredObstruction A (requiredLawWitnessFamily LU)) ∧
      (NoRequiredObstruction A (requiredLawWitnessFamily LU) ↔
        RequiredSignatureAxesZero A (requiredLawSignatureAxes LU)) ∧
        (SemanticLawful A LU ↔
          RequiredSignatureAxesZero A (requiredLawSignatureAxes LU)) :=
  ⟨semanticLawful_iff_noRequiredObstruction_requiredLawWitness A LU,
    noRequiredObstruction_iff_requiredSignatureAxesZero_requiredLaw A LU,
    semanticLawful_iff_requiredSignatureAxesZero_requiredLawAxes A LU⟩

/--
I.定理9.3 後段: explicit assumptions under which the semantic, witness, and
signature-axis readings agree.
-/
structure ThreeReadingAgreementAssumptions {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) (LU : LawUniverse U)
    (W : LawWitnessFamily U) (S : SignatureAxes U) where
  witnessCompleteness : Prop
  axisExactness : Prop
  coverage : Prop
  selectedReadingExactness : Prop
  witnessCompleteness_holds : witnessCompleteness
  axisExactness_holds : axisExactness
  coverage_holds : coverage
  selectedReadingExactness_holds : selectedReadingExactness
  semantic_noObstruction :
    witnessCompleteness -> coverage -> selectedReadingExactness ->
      (SemanticLawful A LU ↔ NoRequiredObstruction A W)
  noObstruction_axesZero :
    axisExactness -> coverage -> selectedReadingExactness ->
      (NoRequiredObstruction A W ↔ RequiredSignatureAxesZero A S)

namespace ThreeReadingAgreementAssumptions

/--
I.定理9.3 後段: semantic lawfulness agrees with no required obstruction under
explicit witness-completeness, coverage, and selected-reading exactness.
-/
theorem semanticLawful_iff_noRequiredObstruction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {LU : LawUniverse U}
    {W : LawWitnessFamily U} {S : SignatureAxes U}
    (h : ThreeReadingAgreementAssumptions A LU W S) :
    SemanticLawful A LU ↔ NoRequiredObstruction A W :=
  h.semantic_noObstruction h.witnessCompleteness_holds h.coverage_holds
    h.selectedReadingExactness_holds

/--
I.定理9.3 後段: no required obstruction agrees with selected signature axes
zero under explicit axis-exactness, coverage, and selected-reading exactness.
-/
theorem noRequiredObstruction_iff_requiredSignatureAxesZero
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {LU : LawUniverse U}
    {W : LawWitnessFamily U} {S : SignatureAxes U}
    (h : ThreeReadingAgreementAssumptions A LU W S) :
    NoRequiredObstruction A W ↔ RequiredSignatureAxesZero A S :=
  h.noObstruction_axesZero h.axisExactness_holds h.coverage_holds
    h.selectedReadingExactness_holds

/--
I.定理9.3 後段: semantic lawfulness agrees directly with selected signature axes
zero under the explicit three-reading assumptions.
-/
theorem semanticLawful_iff_requiredSignatureAxesZero {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {LU : LawUniverse U}
    {W : LawWitnessFamily U} {S : SignatureAxes U}
    (h : ThreeReadingAgreementAssumptions A LU W S) :
    SemanticLawful A LU ↔ RequiredSignatureAxesZero A S :=
  (semanticLawful_iff_noRequiredObstruction h).trans
    (noRequiredObstruction_iff_requiredSignatureAxesZero h)

/-- I.定理9.3 後段: the three readings agree as a chain. -/
theorem threeReadingAgreement {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {LU : LawUniverse U}
    {W : LawWitnessFamily U} {S : SignatureAxes U}
    (h : ThreeReadingAgreementAssumptions A LU W S) :
    (SemanticLawful A LU ↔ NoRequiredObstruction A W) ∧
      (NoRequiredObstruction A W ↔ RequiredSignatureAxesZero A S) ∧
        (SemanticLawful A LU ↔ RequiredSignatureAxesZero A S) :=
  ⟨semanticLawful_iff_noRequiredObstruction h,
    noRequiredObstruction_iff_requiredSignatureAxesZero h,
    semanticLawful_iff_requiredSignatureAxesZero h⟩

end ThreeReadingAgreementAssumptions

end AAT.AG
