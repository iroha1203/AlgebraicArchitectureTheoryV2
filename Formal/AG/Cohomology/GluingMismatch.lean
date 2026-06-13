import Formal.AG.Cohomology.CechComplex

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u v w

open CategoryTheory
open Opposite

/--
IV.定義5.1: local flatness data over a selected cover.

Each cover chart carries a PRD-3 lawful section, and the section is required to
satisfy the primary obstruction-ideal vanishing condition `s_i^* I_Ob^U = 0`.
The ambient ring and ideal are explicit parameters; this layer does not build a
scheme-level gluing theorem.
-/
structure LocalFlatnessData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (𝒰 : CoverRelativeCechCover S)
    (R : Type v) [CommRing R] (IOb : Ideal R) where
  localSection :
    𝒰.Index -> LawAlgebra.LawfulLocus.LawfulSectionData.{v, w} R IOb
  lawful : ∀ i : 𝒰.Index, (localSection i).Lawful

namespace LocalFlatnessData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}

/-- IV.定義5.1: each local section factors through the lawful locus `Flat_U`. -/
def factorsThroughFlat_U (D : LocalFlatnessData 𝒰 R IOb) (i : 𝒰.Index) :
    (D.localSection i).FactorsThroughLawfulLocus :=
  LawAlgebra.LawfulLocus.LawfulSectionData.factorsThroughLawfulLocus_of_lawful R
    (D.lawful i)

/-- IV.定義5.1: local lawfulness is exactly pulled obstruction-ideal vanishing. -/
theorem pulledObstructionIdeal_eq_bot
    (D : LocalFlatnessData 𝒰 R IOb) (i : 𝒰.Index) :
    (D.localSection i).pulledObstructionIdeal = ⊥ :=
  D.lawful i

end LocalFlatnessData

/--
IV.定義5.2: a local lawful section restricted to a selected 1-overlap.

The actual restriction morphism for lawful sections is not constructed at this
layer.  Instead, the restricted section and its relation to the chart-local
section are explicit selected data over the overlap simplex.
-/
structure RestrictedLocalLawfulSection {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    (D : LocalFlatnessData 𝒰 R IOb) (σ : 𝒰.simplex 1) (i : 𝒰.Index) where
  restrictedSection :
    LawAlgebra.LawfulLocus.LawfulSectionData.{v, w} R IOb
  restrictsLocalSection : Prop
  restriction_holds : restrictsLocalSection
  restrictedLawful : restrictedSection.Lawful

namespace RestrictedLocalLawfulSection

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}

/-- IV.定義5.2: restricted sections still factor through the lawful locus. -/
def factorsThroughFlat_U {σ : 𝒰.simplex 1} {i : 𝒰.Index}
    (s : RestrictedLocalLawfulSection D σ i) :
    s.restrictedSection.FactorsThroughLawfulLocus :=
  LawAlgebra.LawfulLocus.LawfulSectionData.factorsThroughLawfulLocus_of_lawful R
    s.restrictedLawful

end RestrictedLocalLawfulSection

/--
IV.定義5.2: parameterized gluing mismatch.

The restricted sections over a 1-overlap and the map comparing them are supplied
as data. This keeps the restriction and comparison maps selected and explicit
instead of deriving them from an unformalized general restriction/gluing theory.
-/
structure GluingMismatchData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    (Ob : ObstructionSheaf S) {R : Type v} [CommRing R] {IOb : Ideal R}
    (D : LocalFlatnessData 𝒰 R IOb) where
  leftIndex : 𝒰.simplex 1 -> 𝒰.Index
  rightIndex : 𝒰.simplex 1 -> 𝒰.Index
  leftRestriction :
    ∀ σ : 𝒰.simplex 1, RestrictedLocalLawfulSection D σ (leftIndex σ)
  rightRestriction :
    ∀ σ : 𝒰.simplex 1, RestrictedLocalLawfulSection D σ (rightIndex σ)
  mismatch :
    ∀ σ : 𝒰.simplex 1,
      RestrictedLocalLawfulSection D σ (leftIndex σ) ->
      RestrictedLocalLawfulSection D σ (rightIndex σ) ->
      Ob.carrier.toPresheaf.obj (op (𝒰.overlap 1 σ))

namespace GluingMismatchData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}

/-- IV.定義5.2: the selected mismatch value `g_ij` on a 1-overlap. -/
def value (M : GluingMismatchData Ob D) (σ : 𝒰.simplex 1) :
    Ob.carrier.toPresheaf.obj (op (𝒰.overlap 1 σ)) :=
  M.mismatch σ (M.leftRestriction σ) (M.rightRestriction σ)

/-- IV.定義5.2: the mismatch family as a degree-one Čech cochain. -/
def gluingMismatchCochain (M : GluingMismatchData Ob D) :
    CoverRelativeCechCochain 𝒰 Ob 1 :=
  fun σ => M.value σ

/-- IV.定義5.2: the cochain entry is the selected mismatch comparison map. -/
theorem gluingMismatchCochain_apply
    (M : GluingMismatchData Ob D) (σ : 𝒰.simplex 1) :
    M.gluingMismatchCochain σ =
      M.mismatch σ (M.leftRestriction σ) (M.rightRestriction σ) :=
  rfl

/-- IV.定義5.2: the left input of the mismatch is the selected overlap restriction. -/
theorem leftRestriction_holds
    (M : GluingMismatchData Ob D) (σ : 𝒰.simplex 1) :
    (M.leftRestriction σ).restrictsLocalSection :=
  (M.leftRestriction σ).restriction_holds

/-- IV.定義5.2: the right input of the mismatch is the selected overlap restriction. -/
theorem rightRestriction_holds
    (M : GluingMismatchData Ob D) (σ : 𝒰.simplex 1) :
    (M.rightRestriction σ).restrictsLocalSection :=
  (M.rightRestriction σ).restriction_holds

end GluingMismatchData

/--
IV.原則5.2A: pseudo-torsor normalized mismatch data.

The selected difference carrier models the abelian group `G_U` in which local
lawful sections form a pseudo-torsor. The edge mismatch is required to be the
normalized difference `s_j - s_i`; the cycle of vertices on a 2-simplex then
forces the triple-overlap sum to vanish. The final field states that the
selected Čech differential reads this triple sum for the chosen mismatch
cochain.
-/
structure PseudoTorsorNormalizedMismatch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} (M : GluingMismatchData Ob D)
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  Difference : Type u
  differenceAddCommGroup : AddCommGroup Difference
  readMismatch :
    ∀ σ : 𝒰.simplex 1,
      Ob.carrier.toPresheaf.obj (op (𝒰.overlap 1 σ)) -> Difference
  position : 𝒰.Index -> Difference
  edgeValue : 𝒰.simplex 1 -> Difference
  readMismatch_value :
    ∀ σ : 𝒰.simplex 1,
      readMismatch σ (M.value σ) = edgeValue σ
  edgeValue_eq_sub :
    ∀ σ : 𝒰.simplex 1,
      edgeValue σ = position (M.rightIndex σ) - position (M.leftIndex σ)
  vertex : 𝒰.simplex 2 -> Fin 3 -> 𝒰.Index
  edge01 : 𝒰.simplex 2 -> 𝒰.simplex 1
  edge12 : 𝒰.simplex 2 -> 𝒰.simplex 1
  edge20 : 𝒰.simplex 2 -> 𝒰.simplex 1
  edge01_left :
    ∀ τ : 𝒰.simplex 2, M.leftIndex (edge01 τ) = vertex τ 0
  edge01_right :
    ∀ τ : 𝒰.simplex 2, M.rightIndex (edge01 τ) = vertex τ 1
  edge12_left :
    ∀ τ : 𝒰.simplex 2, M.leftIndex (edge12 τ) = vertex τ 1
  edge12_right :
    ∀ τ : 𝒰.simplex 2, M.rightIndex (edge12 τ) = vertex τ 2
  edge20_left :
    ∀ τ : 𝒰.simplex 2, M.leftIndex (edge20 τ) = vertex τ 2
  edge20_right :
    ∀ τ : 𝒰.simplex 2, M.rightIndex (edge20 τ) = vertex τ 0
  selectedDifferential_vanishes_of_triple_sum_zero :
    letI := K.cochainAddCommGroup 2
    (∀ τ : 𝒰.simplex 2,
        edgeValue (edge01 τ) + edgeValue (edge12 τ) + edgeValue (edge20 τ) = 0
    ) ->
      K.d 1 M.gluingMismatchCochain = 0

attribute [instance] PseudoTorsorNormalizedMismatch.differenceAddCommGroup

namespace PseudoTorsorNormalizedMismatch

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}
variable {M : GluingMismatchData Ob D}
variable {K : CoverRelativeCechComplex 𝒰 Ob}

/--
IV.原則5.2A: the selected mismatch cochain reads as the normalized
pseudo-torsor edge value.
-/
theorem readMismatch_gluingMismatch
    (N : PseudoTorsorNormalizedMismatch M K) (σ : 𝒰.simplex 1) :
    N.readMismatch σ (M.gluingMismatchCochain σ) = N.edgeValue σ := by
  rw [GluingMismatchData.gluingMismatchCochain_apply]
  exact N.readMismatch_value σ

/--
IV.原則5.2A: the normalized edge differences cancel on each triple overlap.
-/
theorem triple_mismatch_sum_zero
    (N : PseudoTorsorNormalizedMismatch M K) (τ : 𝒰.simplex 2) :
    N.edgeValue (N.edge01 τ) + N.edgeValue (N.edge12 τ) +
      N.edgeValue (N.edge20 τ) = 0 := by
  letI := N.differenceAddCommGroup
  rw [N.edgeValue_eq_sub (N.edge01 τ), N.edgeValue_eq_sub (N.edge12 τ),
    N.edgeValue_eq_sub (N.edge20 τ), N.edge01_right τ, N.edge01_left τ,
    N.edge12_right τ, N.edge12_left τ, N.edge20_right τ, N.edge20_left τ]
  abel

/--
IV.原則5.2A: pseudo-torsor normalization automatically makes the selected
gluing mismatch a Čech 1-cocycle.
-/
theorem gluingMismatch_cocycle
    (N : PseudoTorsorNormalizedMismatch M K) :
    letI := K.cochainAddCommGroup 2
    K.d 1 M.gluingMismatchCochain = 0 :=
  N.selectedDifferential_vanishes_of_triple_sum_zero
    (fun τ => N.triple_mismatch_sum_zero τ)

end PseudoTorsorNormalizedMismatch

/-- IV.定義5.3: a descent cocycle is the mismatch cochain with its cocycle proof. -/
def descentCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} (M : GluingMismatchData Ob D)
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (h : letI := K.cochainAddCommGroup 2
      K.d 1 M.gluingMismatchCochain = 0) :
    K.CechCocycle 1 :=
  ⟨M.gluingMismatchCochain, h⟩

/--
IV.定義5.3: descent obstruction class `[g] in H^1(𝒰, Ob_U)` attached to a
selected gluing mismatch cocycle.
-/
def descentObstructionClass {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} (M : GluingMismatchData Ob D)
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (h : letI := K.cochainAddCommGroup 2
      K.d 1 M.gluingMismatchCochain = 0) :
    K.CoverRelativeHn 1 :=
  K.cohomologyClassSucc 0 (descentCocycle M K h)

/--
IV.定義5.3 / 原則5.2A: pseudo-torsor normalized mismatch yields the descent
obstruction class without an extra cocycle proof.
-/
def descentObstructionClassOfPseudoTorsor {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    (N : PseudoTorsorNormalizedMismatch M K) :
    K.CoverRelativeHn 1 :=
  descentObstructionClass M K N.gluingMismatch_cocycle

end Cohomology
end AAT.AG
