import Formal.AG.Site.Topology

namespace AAT.AG
namespace Site

universe u

open CategoryTheory

/--
II.定義7.2: extra ideal-preservation data used by `U`-adequate covers.

The selected witness ideal is not built into the context category. It is an
explicit predicate on the readable restriction maps of a chosen cover.
-/
structure UAdequacyRequirements {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {LU : LawUniverse U} {Sig : ArchitectureSignature U}
    (C : ContextPreorderCategory A)
    (R : CoverageRequirements A LU Sig) where
  selectedWitnessIdeal : LU.SelectedReading -> ArchCtx A -> Prop
  witnessIdealPreservedBy :
    {source target : ArchCtx A} -> C.Hom source target ->
      selectedWitnessIdeal R.selectedReading target ->
        selectedWitnessIdeal R.selectedReading source

/--
II.定義7.2: `U`-adequate cover.

An adequate cover is a `J_U` cover plus the selected support, witness, axis,
boundary, and witness-ideal preservation conditions needed by later theorem
packages.
-/
structure UAdequateCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    (Q : UAdequacyRequirements C R) {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (F : AATCoverageFamily R P base) : Prop where
  topologyCover :
    Sieve.generate F.presieve ∈ AATGrothendieckTopology R P base
  requiredSupportCovered :
    ∀ atom : U.Atom, R.requiredSupport R.selectedReading atom ->
      ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom
  requiredWitnessesVisible :
    ∀ witness : LU.witnessFamily.Witness, R.requiredWitness R.selectedReading witness ->
      (∃ i : F.Index, R.witnessVisibleOn (F.patch i) witness) ∨
        ∃ i j : F.Index,
          R.witnessVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) witness
  requiredAxesReadable :
    ∀ axis : Sig.Axis, R.requiredAxis R.selectedReading axis ->
      ∃ i : F.Index, R.axisReadableOn (F.patch i) axis
  boundaryWitnessesVisible :
    ∀ i j : F.Index,
      R.boundaryVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) base.ctx
  restrictionMapsPreserveWitnessIdeals :
    ∀ i : F.Index,
      Q.selectedWitnessIdeal R.selectedReading base.ctx ->
        Q.selectedWitnessIdeal R.selectedReading (F.patch i)

namespace UAdequateCover

/-- II.定義7.2: an adequate cover is a cover in the generated topology. -/
theorem isCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) :
    Sieve.generate F.presieve ∈ AATGrothendieckTopology R P base :=
  h.topologyCover

/-- II.定義7.2: adequate covers expose required support. -/
theorem support {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) {atom : U.Atom}
    (hreq : R.requiredSupport R.selectedReading atom) :
    ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom :=
  h.requiredSupportCovered atom hreq

/-- II.定義7.2: adequate covers expose required witnesses on patches or overlaps. -/
theorem witness {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) {witness : LU.witnessFamily.Witness}
    (hreq : R.requiredWitness R.selectedReading witness) :
    (∃ i : F.Index, R.witnessVisibleOn (F.patch i) witness) ∨
      ∃ i j : F.Index,
        R.witnessVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) witness :=
  h.requiredWitnessesVisible witness hreq

/-- II.定義7.2: adequate covers make required axes readable. -/
theorem axis {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) {axis : Sig.Axis}
    (hreq : R.requiredAxis R.selectedReading axis) :
    ∃ i : F.Index, R.axisReadableOn (F.patch i) axis :=
  h.requiredAxesReadable axis hreq

/-- II.定義7.2: adequate covers keep selected boundary witnesses visible. -/
theorem boundary {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) (i j : F.Index) :
    R.boundaryVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) base.ctx :=
  h.boundaryWitnessesVisible i j

/-- II.定義7.2: adequate covers preserve selected witness ideals on restrictions. -/
theorem witnessIdeal {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) (i : F.Index) :
    Q.selectedWitnessIdeal R.selectedReading base.ctx ->
      Q.selectedWitnessIdeal R.selectedReading (F.patch i) :=
  h.restrictionMapsPreserveWitnessIdeals i

end UAdequateCover

/-- II.補題7.2A: required witnesses selected by the current reading. -/
abbrev RequiredWitnessSubtype {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {LU : LawUniverse U} {Sig : ArchitectureSignature U}
    (R : CoverageRequirements A LU Sig) :=
  {witness : LU.witnessFamily.Witness // R.requiredWitness R.selectedReading witness}

/--
II.補題7.2A: closed index generated by seed patches, required witness supports,
and seed-boundary overlaps.
-/
abbrev WitnessClosureIndex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {LU : LawUniverse U} {Sig : ArchitectureSignature U}
    (R : CoverageRequirements A LU Sig) (SeedIndex : Type u) :=
  SeedIndex ⊕ (RequiredWitnessSubtype R ⊕ (SeedIndex × SeedIndex))

namespace WitnessClosureIndex

/-- II.補題7.2A: context selected by a closed-cover index. -/
def patch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {SeedIndex : Type u} (P : ContextOverlapPullback C)
    (base : ContextCategoryObject C) (seedPatch : SeedIndex -> ArchCtx A)
    (requiredWitnessSupport : RequiredWitnessSubtype R -> ArchCtx A) :
    WitnessClosureIndex R SeedIndex -> ArchCtx A
  | Sum.inl seed => seedPatch seed
  | Sum.inr (Sum.inl witness) => requiredWitnessSupport witness
  | Sum.inr (Sum.inr pair) => P.overlap base.ctx (seedPatch pair.1) (seedPatch pair.2)

end WitnessClosureIndex

/--
II.補題7.2A: witness-closure cover construction package.

The closed index set is generated from seed patches, one representable support
context for every required witness, and the selected seed-boundary overlaps.
The visibility and preservation fields are the explicit hypotheses that remain
after the closure construction has supplied those contexts.
-/
structure WitnessClosureCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    (Q : UAdequacyRequirements C R) (P : ContextOverlapPullback C)
    (base : ContextCategoryObject C) where
  SeedIndex : Type u
  seedPatch : SeedIndex -> ArchCtx A
  seedInclusion : ∀ i : SeedIndex, C.Hom (seedPatch i) base.ctx
  localFiniteRequiredWitnesses :
    Finite (RequiredWitnessSubtype R)
  RequiredWitnessSupport :
    RequiredWitnessSubtype R -> ArchCtx A
  requiredWitnessSupport_inclusion :
    ∀ witness, C.Hom (RequiredWitnessSupport witness) base.ctx
  requiredWitnessSupport_visible :
    ∀ witness, R.witnessVisibleOn (RequiredWitnessSupport witness) witness.1
  requiredSupportCovered :
    ∀ atom : U.Atom, R.requiredSupport R.selectedReading atom ->
      ∃ i : WitnessClosureIndex R SeedIndex,
        R.supportVisibleOn
          (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport i) atom
  readableRequiredAxes :
    ∀ axis : Sig.Axis, R.requiredAxis R.selectedReading axis ->
      ∃ i : WitnessClosureIndex R SeedIndex,
        R.axisReadableOn
          (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport i) axis
  visibleBoundaryWitnesses :
    ∀ i j : WitnessClosureIndex R SeedIndex,
      R.boundaryVisibleOn
        (P.overlap base.ctx
          (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport i)
          (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport j)) base.ctx

namespace WitnessClosureCover

/-- II.補題7.2A: index set of the closed cover. -/
abbrev ClosedIndex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : WitnessClosureCover Q P base) :=
  WitnessClosureIndex R K.SeedIndex

/-- II.補題7.2A: context carried by a closed-cover index. -/
def patch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : WitnessClosureCover Q P base) :
    K.ClosedIndex -> ArchCtx A :=
  WitnessClosureIndex.patch P base K.seedPatch K.RequiredWitnessSupport

/-- II.補題7.2A: each closed-cover context reads into the base. -/
def inclusion {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : WitnessClosureCover Q P base) :
    ∀ i : K.ClosedIndex, C.Hom (K.patch i) base.ctx
  | Sum.inl seed => K.seedInclusion seed
  | Sum.inr (Sum.inl witness) => K.requiredWitnessSupport_inclusion witness
  | Sum.inr (Sum.inr pair) =>
      P.overlap_le_base (K.seedInclusion pair.1) (K.seedInclusion pair.2)

/-- II.補題7.2A: the witness-closure construction as an admissible family. -/
def toAATCoverageFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A LU Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : WitnessClosureCover Q P base) :
    AATCoverageFamily R P base where
  Index := K.ClosedIndex
  patch := K.patch
  inclusion := K.inclusion
  admissible := {
    atomSupportCoverage := fun atom hreq =>
      let ⟨i, hi⟩ := K.requiredSupportCovered atom hreq
      ⟨i, by
        change R.supportVisibleOn (K.patch i) atom
        simpa [WitnessClosureCover.patch] using hi⟩
    lawWitnessCoverage := fun witness hreq =>
      let required : {witness : LU.witnessFamily.Witness //
          R.requiredWitness R.selectedReading witness} := ⟨witness, hreq⟩
      Or.inl ⟨Sum.inr (Sum.inl required), K.requiredWitnessSupport_visible required⟩
    signatureAxisCoverage := fun axis hreq =>
      let ⟨i, hi⟩ := K.readableRequiredAxes axis hreq
      ⟨i, by
        change R.axisReadableOn (K.patch i) axis
        simpa [WitnessClosureCover.patch] using hi⟩
    boundaryCoverage := fun i j => by
      change R.boundaryVisibleOn (P.overlap base.ctx (K.patch i) (K.patch j)) base.ctx
      simpa [WitnessClosureCover.patch] using K.visibleBoundaryWitnesses i j
    nonGeneration := fun i =>
      ContextMorphism.nonGenerating_of_restriction (C.morphism_isRestriction (K.inclusion i))
  }

end WitnessClosureCover

/--
II.補題7.2A: under the explicit witness-closure assumptions, the closed cover
is `U`-adequate.
-/
theorem witnessClosureCover_uAdequate {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    {LU : LawUniverse U} {Sig : ArchitectureSignature U}
    {R : CoverageRequirements A LU Sig} {Q : UAdequacyRequirements C R}
    {P : ContextOverlapPullback C} {base : ContextCategoryObject C}
    (K : WitnessClosureCover Q P base) :
    UAdequateCover Q K.toAATCoverageFamily where
  topologyCover := AATGrothendieckTopology.generate_mem K.toAATCoverageFamily
  requiredSupportCovered := fun atom hreq =>
    let ⟨i, hi⟩ := K.requiredSupportCovered atom hreq
    ⟨i, by
      change R.supportVisibleOn (K.patch i) atom
      simpa [WitnessClosureCover.patch] using hi⟩
  requiredWitnessesVisible := fun witness hreq =>
    let required : {witness : LU.witnessFamily.Witness //
        R.requiredWitness R.selectedReading witness} := ⟨witness, hreq⟩
    Or.inl ⟨Sum.inr (Sum.inl required), by
      change R.witnessVisibleOn (K.patch (Sum.inr (Sum.inl required))) witness
      exact K.requiredWitnessSupport_visible required⟩
  requiredAxesReadable := fun axis hreq =>
    let ⟨i, hi⟩ := K.readableRequiredAxes axis hreq
    ⟨i, by
      change R.axisReadableOn (K.patch i) axis
      simpa [WitnessClosureCover.patch] using hi⟩
  boundaryWitnessesVisible := fun i j => by
    change R.boundaryVisibleOn (P.overlap base.ctx (K.patch i) (K.patch j)) base.ctx
    simpa [WitnessClosureCover.patch] using K.visibleBoundaryWitnesses i j
  restrictionMapsPreserveWitnessIdeals := fun i hbase =>
    Q.witnessIdealPreservedBy (K.inclusion i) hbase

end Site
end AAT.AG
