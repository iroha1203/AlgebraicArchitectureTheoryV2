import Formal.AG.Cohomology.BoundaryResidue

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

/--
IV.定義10.1: triple-overlap coherence failure.

The selected cochain `h` is a degree-two Cech cocycle, so it determines a class
`[h] in H^2(𝒰, Ob_U)`.  This records the obstruction surface only; it does not
construct a spectral sequence.
-/
structure TripleOverlapCoherenceFailure {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  h : K.Cn 2
  h_cocycle :
    letI := K.cochainAddCommGroup 3
    K.d 2 h = 0

namespace TripleOverlapCoherenceFailure

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}

/-- IV.定義10.1: read the degree-two cocycle. -/
def hCocycle (F : TripleOverlapCoherenceFailure K) :
    K.CechCocycle 2 :=
  letI := K.cochainAddCommGroup 2
  letI := K.cochainAddCommGroup 3
  ⟨F.h, F.h_cocycle⟩

/-- IV.定義10.1: the triple-overlap obstruction class `[h] in H^2(𝒰, Ob_U)`. -/
def hClass (F : TripleOverlapCoherenceFailure K) :
    K.CoverRelativeHn 2 :=
  K.cohomologyClassSucc 1 (F.hCocycle)

end TripleOverlapCoherenceFailure

/--
IV.定理候補10.4: low-degree five-term exact-sequence statement data.

This is deliberately only the five-object low-degree statement shape needed by
the PRD.  It records finite-cover Cech-filtration provenance, but does not
introduce a general spectral sequence mechanism.
-/
structure LowDegreeFiveTermData {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  finiteCover : Prop
  finiteCover_holds : finiteCover
  cechFiltration : Prop
  cechFiltration_holds : cechFiltration
  E10 : Type u
  E01 : Type u
  E20 : Type u
  H1 : Type u
  H2 : Type u
  add_E10 : AddCommGroup E10
  add_E01 : AddCommGroup E01
  add_E20 : AddCommGroup E20
  add_H1 : AddCommGroup H1
  add_H2 : AddCommGroup H2
  edge_H1_E10 : H1 →+ E10
  d10_E10_E01 : E10 →+ E01
  edge_E01_H2 : E01 →+ H2
  edge_H2_E20 : H2 →+ E20

namespace LowDegreeFiveTermData

attribute [instance] add_E10 add_E01 add_E20 add_H1 add_H2

/--
IV.定理候補10.4: five-term exactness predicate.

The finite-cover Cech filtration may instantiate these exactness clauses, but
this file records only the statement shape and no proof of spectral-sequence
exactness.
-/
def FiveTermExact {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {K : CoverRelativeCechComplex 𝒰 Ob}
    (T : LowDegreeFiveTermData K) : Prop :=
  (∀ x : T.H1, T.d10_E10_E01 (T.edge_H1_E10 x) = 0) ∧
    (∀ x : T.E10, T.d10_E10_E01 x = 0 ->
      ∃ y : T.H1, T.edge_H1_E10 y = x) ∧
    (∀ x : T.E10, T.edge_E01_H2 (T.d10_E10_E01 x) = 0) ∧
    (∀ x : T.E01, T.edge_E01_H2 x = 0 ->
      ∃ y : T.E10, T.d10_E10_E01 y = x) ∧
    (∀ x : T.E01, T.edge_H2_E20 (T.edge_E01_H2 x) = 0) ∧
    (∀ x : T.H2, T.edge_H2_E20 x = 0 ->
      ∃ y : T.E01, T.edge_E01_H2 y = x)

/-- IV.定理候補10.4: low-degree five-term statement as a proposition. -/
def FiveTermStatement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {K : CoverRelativeCechComplex 𝒰 Ob}
    (T : LowDegreeFiveTermData K) : Prop :=
  T.finiteCover ∧ T.cechFiltration ∧ T.FiveTermExact

/-- IV.定理候補10.4: the statement is exactly the low-degree exactness predicate. -/
theorem fiveTermExact_of_statement
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {K : CoverRelativeCechComplex 𝒰 Ob}
    (T : LowDegreeFiveTermData K) :
    T.FiveTermStatement -> T.FiveTermExact :=
  fun h => h.2.2

end LowDegreeFiveTermData

end Cohomology
end AAT.AG
