import Formal.AG.Atom.Law

namespace AAT.AG

universe u

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
