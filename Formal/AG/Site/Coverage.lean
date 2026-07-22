import Formal.AG.Site.Basic
import Formal.AG.Site.ContextCategory

namespace AAT.AG
namespace Site

universe u

/--
II.定義6.1: a coverage family `{ W_i -> W }` in `ArchCtx(A)`.

Each patch is a readable local context of the selected base context. The
underlying morphism data is still supplied by the chosen context preorder; this
definition does not generate new Atom data or infer additional observations.
-/
structure CoverageFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) where
  base : ArchCtx A
  Index : Type u
  patch : Index -> ArchCtx A
  inclusion : ∀ i : Index, C.Hom (patch i) base

namespace CoverageFamily

/-- II.定義6.1: the readable morphism represented by a patch inclusion. -/
def inclusionMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (F : CoverageFamily C) (i : F.Index) :
    ContextMorphism (F.patch i) F.base :=
  C.morphism (F.inclusion i)

/-- II.定義6.1: each patch inclusion is a readable restriction. -/
theorem inclusion_isRestriction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (F : CoverageFamily C) (i : F.Index) :
    (F.inclusionMorphism i).IsRestriction :=
  C.morphism_isRestriction (F.inclusion i)

/-- II.定義7.1: readable patch inclusions do not generate atoms. -/
theorem inclusion_nonGenerating {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (F : CoverageFamily C) (i : F.Index) :
    SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap :=
  ContextMorphism.nonGenerating_of_restriction (F.inclusion_isRestriction i)

end CoverageFamily

/--
II.定義7.1 前半: selected requirements read by admissible covers.

The required support, witness, and signature axes are typed by the selected
law universe and architecture signature. The law universe owns its unique
`selectedReading`; coverage does not select a second reading value. Visibility
predicates remain separate from the context data.
-/
structure CoverageRequirements {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (LU : LawUniverse U) (Sig : ArchitectureSignature U) where
  requiredSupport : U.Atom -> Prop
  requiredWitness : LU.witnessFamily.Witness -> Prop
  requiredAxis : Sig.Axis -> Prop
  supportVisibleOn : ArchCtx A -> U.Atom -> Prop
  witnessVisibleOn : ArchCtx A -> LU.witnessFamily.Witness -> Prop
  axisReadableOn : ArchCtx A -> Sig.Axis -> Prop
  boundaryVisibleOn : ArchCtx A -> ArchCtx A -> Prop

/--
II.定義7.1 前半: admissible cover conditions for a coverage family.

The five fields are exactly the R3 admissibility clauses: Atom support
coverage, law witness coverage, signature axis coverage, boundary coverage,
and context non-generation.
-/
structure AdmissibleCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} (R : CoverageRequirements A LU Sig)
    (P : ContextOverlapPullback C) (F : CoverageFamily C) : Prop where
  atomSupportCoverage :
    ∀ atom : U.Atom, R.requiredSupport atom ->
      ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom
  lawWitnessCoverage :
    ∀ witness : LU.witnessFamily.Witness, R.requiredWitness witness ->
      (∃ i : F.Index, R.witnessVisibleOn (F.patch i) witness) ∨
        ∃ i j : F.Index,
          R.witnessVisibleOn (P.overlap F.base (F.patch i) (F.patch j)) witness
  signatureAxisCoverage :
    ∀ axis : Sig.Axis, R.requiredAxis axis ->
      ∃ i : F.Index, R.axisReadableOn (F.patch i) axis
  boundaryCoverage :
    ∀ i j : F.Index,
      R.boundaryVisibleOn (P.overlap F.base (F.patch i) (F.patch j)) F.base
  nonGeneration :
    ∀ i : F.Index, SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap

namespace AdmissibleCover

/-- II.定義7.1: admissible covers expose required Atom support on patches. -/
theorem support {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    {atom : U.Atom} (hreq : R.requiredSupport atom) :
    ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom :=
  h.atomSupportCoverage atom hreq

/--
II.定義7.1: admissible covers expose required law witnesses on patches or
their selected overlaps.
-/
theorem witness {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    {witness : LU.witnessFamily.Witness}
    (hreq : R.requiredWitness witness) :
    (∃ i : F.Index, R.witnessVisibleOn (F.patch i) witness) ∨
      ∃ i j : F.Index,
        R.witnessVisibleOn (P.overlap F.base (F.patch i) (F.patch j)) witness :=
  h.lawWitnessCoverage witness hreq

/-- II.定義7.1: admissible covers expose required signature axes on patches. -/
theorem axis {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    {axis : Sig.Axis} (hreq : R.requiredAxis axis) :
    ∃ i : F.Index, R.axisReadableOn (F.patch i) axis :=
  h.signatureAxisCoverage axis hreq

/-- II.定義7.1: admissible covers expose boundary readings on overlaps. -/
theorem boundary {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    (i j : F.Index) :
    R.boundaryVisibleOn (P.overlap F.base (F.patch i) (F.patch j)) F.base :=
  h.boundaryCoverage i j

/-- II.定義7.1: admissible covers do not generate atoms along inclusions. -/
theorem nonGenerating {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    (i : F.Index) :
    SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap :=
  h.nonGeneration i

/--
II.定義7.1: any coverage family whose non-generation clause is inherited from
the context preorder satisfies the fifth admissibility condition.
-/
theorem nonGenerating_from_inclusions {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    {F : CoverageFamily C} :
    (∀ i : F.Index, SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap) :=
  F.inclusion_nonGenerating

end AdmissibleCover

end Site
end AAT.AG
