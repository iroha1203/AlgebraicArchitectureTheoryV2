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
    (C : ContextPreorderCategory A) {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U}
    (R : CoverageRequirements A E Sig) where
  selectedWitnessIdeal : ArchCtx A -> Prop
  witnessIdealPreservedBy :
    {source target : ArchCtx A} -> C.Hom source target ->
      selectedWitnessIdeal target -> selectedWitnessIdeal source

/--
II.定義7.2: `U`-adequate cover.

An adequate cover is a `J_U` cover plus the selected support, witness, axis,
boundary, and witness-ideal preservation conditions needed by later theorem
packages.
-/
structure UAdequateCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    (Q : UAdequacyRequirements C R) {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (F : AATCoverageFamily R P base) : Prop where
  topologyCover :
    Sieve.generate F.presieve ∈ AATGrothendieckTopology R P base
  requiredSupportCovered :
    ∀ atom : U.Atom, R.requiredSupport atom ->
      ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom
  requiredEquationCoordinatesVisible :
    ∀ coordinate : E.RequiredCoordinate,
      R.requiredEquationCoordinate coordinate ->
        (∃ i : F.Index,
          R.equationCoordinateVisibleOn (F.patch i) coordinate) ∨
          ∃ i j : F.Index,
            R.equationCoordinateVisibleOn
              (P.overlap base.ctx (F.patch i) (F.patch j)) coordinate
  selectedViolationWitnessesVisible :
    ∀ witness : E.Coordinate, R.selectedViolationWitness witness ->
      (∃ i : F.Index, R.violationWitnessVisibleOn (F.patch i) witness) ∨
        ∃ i j : F.Index,
          R.violationWitnessVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) witness
  requiredAxesReadable :
    ∀ axis : Sig.Axis, R.requiredAxis axis ->
      ∃ i : F.Index, R.axisReadableOn (F.patch i) axis
  boundaryWitnessesVisible :
    ∀ i j : F.Index,
      R.boundaryVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) base.ctx
  restrictionMapsPreserveWitnessIdeals :
    ∀ i : F.Index,
      Q.selectedWitnessIdeal base.ctx -> Q.selectedWitnessIdeal (F.patch i)

namespace UAdequateCover

/-- II.定義7.2: an adequate cover is a cover in the generated topology. -/
theorem isCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) :
    Sieve.generate F.presieve ∈ AATGrothendieckTopology R P base :=
  h.topologyCover

/-- II.定義7.2: adequate covers expose required support. -/
theorem support {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) {atom : U.Atom}
    (hreq : R.requiredSupport atom) :
    ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom :=
  h.requiredSupportCovered atom hreq

/-- II.定義7.2: adequate covers expose required equation coordinates. -/
theorem equationCoordinate {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) {coordinate : E.RequiredCoordinate}
    (hreq : R.requiredEquationCoordinate coordinate) :
    (∃ i : F.Index, R.equationCoordinateVisibleOn (F.patch i) coordinate) ∨
      ∃ i j : F.Index,
        R.equationCoordinateVisibleOn
          (P.overlap base.ctx (F.patch i) (F.patch j)) coordinate :=
  h.requiredEquationCoordinatesVisible coordinate hreq

/-- II.定義7.2: adequate covers expose required witnesses on patches or overlaps. -/
theorem witness {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) {witness : E.Coordinate}
    (hreq : R.selectedViolationWitness witness) :
    (∃ i : F.Index, R.violationWitnessVisibleOn (F.patch i) witness) ∨
      ∃ i j : F.Index,
        R.violationWitnessVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) witness :=
  h.selectedViolationWitnessesVisible witness hreq

/-- II.定義7.2: adequate covers make required axes readable. -/
theorem axis {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) {axis : Sig.Axis}
    (hreq : R.requiredAxis axis) :
    ∃ i : F.Index, R.axisReadableOn (F.patch i) axis :=
  h.requiredAxesReadable axis hreq

/-- II.定義7.2: adequate covers keep selected boundary witnesses visible. -/
theorem boundary {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) (i j : F.Index) :
    R.boundaryVisibleOn (P.overlap base.ctx (F.patch i) (F.patch j)) base.ctx :=
  h.boundaryWitnessesVisible i j

/-- II.定義7.2: adequate covers preserve selected witness ideals on restrictions. -/
theorem witnessIdeal {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} {F : AATCoverageFamily R P base}
    (h : UAdequateCover Q F) (i : F.Index) :
    Q.selectedWitnessIdeal base.ctx -> Q.selectedWitnessIdeal (F.patch i) :=
  h.restrictionMapsPreserveWitnessIdeals i

end UAdequateCover

/-- II.補題7.2A: required witnesses fixed by the selected coverage requirements. -/
abbrev RequiredWitnessSubtype {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U}
    (R : CoverageRequirements A E Sig) :=
  {witness : E.Coordinate // R.selectedViolationWitness witness}

/--
II.補題7.2A: closed index generated by seed patches, required witness supports,
and seed-boundary overlaps.
-/
abbrev WitnessClosureIndex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U}
    (R : CoverageRequirements A E Sig) (SeedIndex : Type u) :=
  SeedIndex ⊕ (RequiredWitnessSubtype R ⊕ (SeedIndex × SeedIndex))

namespace WitnessClosureIndex

/-- II.補題7.2A: context selected by a closed-cover index. -/
def patch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
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
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
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
    ∀ witness, R.violationWitnessVisibleOn (RequiredWitnessSupport witness) witness.1
  requiredSupportCovered :
    ∀ atom : U.Atom, R.requiredSupport atom ->
      ∃ i : WitnessClosureIndex R SeedIndex,
        R.supportVisibleOn
          (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport i) atom
  requiredEquationCoordinatesVisible :
    ∀ coordinate : E.RequiredCoordinate,
      R.requiredEquationCoordinate coordinate ->
        (∃ i : WitnessClosureIndex R SeedIndex,
          R.equationCoordinateVisibleOn
            (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport i)
            coordinate) ∨
          ∃ i j : WitnessClosureIndex R SeedIndex,
            R.equationCoordinateVisibleOn
              (P.overlap base.ctx
                (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport i)
                (WitnessClosureIndex.patch P base seedPatch RequiredWitnessSupport j))
              coordinate
  readableRequiredAxes :
    ∀ axis : Sig.Axis, R.requiredAxis axis ->
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
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : WitnessClosureCover Q P base) :=
  WitnessClosureIndex R K.SeedIndex

/-- II.補題7.2A: context carried by a closed-cover index. -/
def patch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : WitnessClosureCover Q P base) :
    K.ClosedIndex -> ArchCtx A :=
  WitnessClosureIndex.patch P base K.seedPatch K.RequiredWitnessSupport

/-- II.補題7.2A: each closed-cover context reads into the base. -/
def inclusion {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : WitnessClosureCover Q P base) :
    ∀ i : K.ClosedIndex, C.Hom (K.patch i) base.ctx
  | Sum.inl seed => K.seedInclusion seed
  | Sum.inr (Sum.inl witness) => K.requiredWitnessSupport_inclusion witness
  | Sum.inr (Sum.inr pair) =>
      P.overlap_le_base (K.seedInclusion pair.1) (K.seedInclusion pair.2)

/-- II.補題7.2A: the witness-closure construction as an admissible family. -/
def toAATCoverageFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
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
    equationCoordinateCoverage := fun coordinate hreq => by
      rcases K.requiredEquationCoordinatesVisible coordinate hreq with h | h
      · exact Or.inl h
      · exact Or.inr h
    violationWitnessCoverage := fun witness hreq =>
      let required : {witness : E.Coordinate //
          R.selectedViolationWitness witness} := ⟨witness, hreq⟩
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
peer-review hardening II-1: seed-driven witness-closure cover input.

Unlike `WitnessClosureCover`, support and axis visibility are stated only on
seed patches. Required witnesses are made visible by the generated witness
support branch. Boundary visibility is split by the constructors of the closed
index, so the closure theorem shows exactly which generated contexts are used.
The older `WitnessClosureCover` remains as the Research-compatible packaged
surface.
-/
structure SeedWitnessClosureCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
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
    ∀ witness, R.violationWitnessVisibleOn (RequiredWitnessSupport witness) witness.1
  seedSupportCovered :
    ∀ atom : U.Atom, R.requiredSupport atom ->
      ∃ i : SeedIndex, R.supportVisibleOn (seedPatch i) atom
  seedEquationCoordinatesVisible :
    ∀ coordinate : E.RequiredCoordinate,
      R.requiredEquationCoordinate coordinate ->
        ∃ i : SeedIndex,
          R.equationCoordinateVisibleOn (seedPatch i) coordinate
  seedAxesReadable :
    ∀ axis : Sig.Axis, R.requiredAxis axis ->
      ∃ i : SeedIndex, R.axisReadableOn (seedPatch i) axis
  boundary_seed_seed :
    ∀ i j : SeedIndex,
      R.boundaryVisibleOn (P.overlap base.ctx (seedPatch i) (seedPatch j)) base.ctx
  boundary_seed_witness :
    ∀ i witness,
      R.boundaryVisibleOn
        (P.overlap base.ctx (seedPatch i) (RequiredWitnessSupport witness)) base.ctx
  boundary_seed_overlap :
    ∀ i (pair : SeedIndex × SeedIndex),
      R.boundaryVisibleOn
        (P.overlap base.ctx (seedPatch i)
          (P.overlap base.ctx (seedPatch pair.1) (seedPatch pair.2))) base.ctx
  boundary_witness_seed :
    ∀ witness i,
      R.boundaryVisibleOn
        (P.overlap base.ctx (RequiredWitnessSupport witness) (seedPatch i)) base.ctx
  boundary_witness_witness :
    ∀ witness1 witness2,
      R.boundaryVisibleOn
        (P.overlap base.ctx
          (RequiredWitnessSupport witness1) (RequiredWitnessSupport witness2)) base.ctx
  boundary_witness_overlap :
    ∀ witness (pair : SeedIndex × SeedIndex),
      R.boundaryVisibleOn
        (P.overlap base.ctx (RequiredWitnessSupport witness)
          (P.overlap base.ctx (seedPatch pair.1) (seedPatch pair.2))) base.ctx
  boundary_overlap_seed :
    ∀ (pair : SeedIndex × SeedIndex) i,
      R.boundaryVisibleOn
        (P.overlap base.ctx
          (P.overlap base.ctx (seedPatch pair.1) (seedPatch pair.2)) (seedPatch i))
          base.ctx
  boundary_overlap_witness :
    ∀ (pair : SeedIndex × SeedIndex) witness,
      R.boundaryVisibleOn
        (P.overlap base.ctx
          (P.overlap base.ctx (seedPatch pair.1) (seedPatch pair.2))
          (RequiredWitnessSupport witness)) base.ctx
  boundary_overlap_overlap :
    ∀ (pair1 pair2 : SeedIndex × SeedIndex),
      R.boundaryVisibleOn
        (P.overlap base.ctx
          (P.overlap base.ctx (seedPatch pair1.1) (seedPatch pair1.2))
          (P.overlap base.ctx (seedPatch pair2.1) (seedPatch pair2.2))) base.ctx

namespace SeedWitnessClosureCover

/-- peer-review hardening II-1: index set generated from seeds, required witnesses, and seed overlaps. -/
abbrev ClosedIndex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : SeedWitnessClosureCover Q P base) :=
  WitnessClosureIndex R K.SeedIndex

/-- peer-review hardening II-1: context selected by a generated closed index. -/
def patch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : SeedWitnessClosureCover Q P base) :
    K.ClosedIndex -> ArchCtx A :=
  WitnessClosureIndex.patch P base K.seedPatch K.RequiredWitnessSupport

/-- peer-review hardening II-1: each generated context reads into the base context. -/
def inclusion {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : SeedWitnessClosureCover Q P base) :
    ∀ i : K.ClosedIndex, C.Hom (K.patch i) base.ctx
  | Sum.inl seed => K.seedInclusion seed
  | Sum.inr (Sum.inl witness) => K.requiredWitnessSupport_inclusion witness
  | Sum.inr (Sum.inr pair) =>
      P.overlap_le_base (K.seedInclusion pair.1) (K.seedInclusion pair.2)

/-- peer-review hardening II-1: generated boundary visibility, by closed-index constructor. -/
def closedBoundaryVisible {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : SeedWitnessClosureCover Q P base) :
    ∀ i j : K.ClosedIndex,
      R.boundaryVisibleOn (P.overlap base.ctx (K.patch i) (K.patch j)) base.ctx
  | Sum.inl i, Sum.inl j => K.boundary_seed_seed i j
  | Sum.inl i, Sum.inr (Sum.inl witness) => K.boundary_seed_witness i witness
  | Sum.inl i, Sum.inr (Sum.inr pair) => K.boundary_seed_overlap i pair
  | Sum.inr (Sum.inl witness), Sum.inl i => K.boundary_witness_seed witness i
  | Sum.inr (Sum.inl witness1), Sum.inr (Sum.inl witness2) =>
      K.boundary_witness_witness witness1 witness2
  | Sum.inr (Sum.inl witness), Sum.inr (Sum.inr pair) =>
      K.boundary_witness_overlap witness pair
  | Sum.inr (Sum.inr pair), Sum.inl i => K.boundary_overlap_seed pair i
  | Sum.inr (Sum.inr pair), Sum.inr (Sum.inl witness) =>
      K.boundary_overlap_witness pair witness
  | Sum.inr (Sum.inr pair1), Sum.inr (Sum.inr pair2) =>
      K.boundary_overlap_overlap pair1 pair2

/-- peer-review hardening II-1: convert the seed-driven input to the frozen witness-closure package. -/
def toWitnessClosureCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : SeedWitnessClosureCover Q P base) :
    WitnessClosureCover Q P base where
  SeedIndex := K.SeedIndex
  seedPatch := K.seedPatch
  seedInclusion := K.seedInclusion
  localFiniteRequiredWitnesses := K.localFiniteRequiredWitnesses
  RequiredWitnessSupport := K.RequiredWitnessSupport
  requiredWitnessSupport_inclusion := K.requiredWitnessSupport_inclusion
  requiredWitnessSupport_visible := K.requiredWitnessSupport_visible
  requiredSupportCovered := fun atom hreq =>
    let ⟨i, hi⟩ := K.seedSupportCovered atom hreq
    ⟨Sum.inl i, hi⟩
  requiredEquationCoordinatesVisible := fun coordinate hreq =>
    let ⟨i, hi⟩ := K.seedEquationCoordinatesVisible coordinate hreq
    Or.inl ⟨Sum.inl i, hi⟩
  readableRequiredAxes := fun axis hreq =>
    let ⟨i, hi⟩ := K.seedAxesReadable axis hreq
    ⟨Sum.inl i, hi⟩
  visibleBoundaryWitnesses := K.closedBoundaryVisible

/-- peer-review hardening II-1: the generated closed cover as an admissible AAT coverage family. -/
def toAATCoverageFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {Q : UAdequacyRequirements C R} {P : ContextOverlapPullback C}
    {base : ContextCategoryObject C} (K : SeedWitnessClosureCover Q P base) :
    AATCoverageFamily R P base :=
  K.toWitnessClosureCover.toAATCoverageFamily

/--
peer-review hardening II-1: the seed-driven closed cover is admissible. Support and axis
coverage come from seed patches, required witnesses from generated support
contexts, and boundary coverage from the closed-index constructor cases.
-/
theorem toAATCoverageFamily_admissible {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    {E : ArchitecturalEquationSystem C} {Sig : ArchitectureSignature U}
    {R : CoverageRequirements A E Sig} {Q : UAdequacyRequirements C R}
    {P : ContextOverlapPullback C} {base : ContextCategoryObject C}
    (K : SeedWitnessClosureCover Q P base) :
    AdmissibleCover R P K.toAATCoverageFamily.toCoverageFamily :=
  K.toAATCoverageFamily.admissible

end SeedWitnessClosureCover

/--
II.補題7.2A: under the explicit witness-closure assumptions, the closed cover
is `U`-adequate.
-/
theorem witnessClosureCover_uAdequate {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    {E : ArchitecturalEquationSystem C} {Sig : ArchitectureSignature U}
    {R : CoverageRequirements A E Sig} {Q : UAdequacyRequirements C R}
    {P : ContextOverlapPullback C} {base : ContextCategoryObject C}
    (K : WitnessClosureCover Q P base) :
    UAdequateCover Q K.toAATCoverageFamily where
  topologyCover := AATGrothendieckTopology.generate_mem K.toAATCoverageFamily
  requiredSupportCovered := fun atom hreq =>
    let ⟨i, hi⟩ := K.requiredSupportCovered atom hreq
    ⟨i, by
      change R.supportVisibleOn (K.patch i) atom
      simpa [WitnessClosureCover.patch] using hi⟩
  requiredEquationCoordinatesVisible := fun coordinate hreq => by
    rcases K.requiredEquationCoordinatesVisible coordinate hreq with h | h
    · exact Or.inl h
    · exact Or.inr h
  selectedViolationWitnessesVisible := fun witness hreq =>
    let required : {witness : E.Coordinate //
        R.selectedViolationWitness witness} := ⟨witness, hreq⟩
    Or.inl ⟨Sum.inr (Sum.inl required), by
      change R.violationWitnessVisibleOn (K.patch (Sum.inr (Sum.inl required))) witness
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

namespace SeedWitnessClosureCover

/-- peer-review hardening II-1: the seed-driven closed cover is `U`-adequate. -/
theorem uAdequate {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    {E : ArchitecturalEquationSystem C} {Sig : ArchitectureSignature U}
    {R : CoverageRequirements A E Sig} {Q : UAdequacyRequirements C R}
    {P : ContextOverlapPullback C} {base : ContextCategoryObject C}
    (K : SeedWitnessClosureCover Q P base) :
    UAdequateCover Q K.toAATCoverageFamily :=
  witnessClosureCover_uAdequate K.toWitnessClosureCover

end SeedWitnessClosureCover

end Site
end AAT.AG
