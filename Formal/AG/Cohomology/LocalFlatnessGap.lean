import Formal.AG.Cohomology.GluingMismatch

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u v w

/-- IV.R5: the zero class in cover-relative `H^1(𝒰, Ob_U)`. -/
def h1ZeroCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} (K : CoverRelativeCechComplex 𝒰 Ob) :
    K.CechCocycle 1 :=
  letI := K.cochainAddCommGroup 1
  letI := K.cochainAddCommGroup 2
  ⟨0, by simp [CoverRelativeCechComplex.d]⟩

/-- IV.R5: zero element of the selected cover-relative `H^1`. -/
def h1ZeroClass {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} (K : CoverRelativeCechComplex 𝒰 Ob) :
    K.CoverRelativeHn 1 :=
  K.cohomologyClassSucc 0 (h1ZeroCocycle K)

/--
IV.定義6.1 / 6.2: hidden coupling cocycle and class.

The hidden coupling class is the R4 descent obstruction class, read with the
selected gluing mismatch cocycle proof.  This layer does not assert that the
class is nonzero; nonvanishing is an explicit theorem hypothesis.
-/
structure HiddenCouplingData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} (M : GluingMismatchData Ob D)
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  cocycleProof :
    letI := K.cochainAddCommGroup 2
    K.d 1 M.gluingMismatchCochain = 0

namespace HiddenCouplingData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}
variable {M : GluingMismatchData Ob D}
variable {K : CoverRelativeCechComplex 𝒰 Ob}

/-- IV.定義6.1: hidden coupling cocycle `hc_U(X)` as a Čech 1-cocycle. -/
def hiddenCouplingCocycle (H : HiddenCouplingData M K) :
    K.CechCocycle 1 :=
  descentCocycle M K H.cocycleProof

/-- IV.定義6.2: hidden coupling class `[hc_U(X)] ∈ H^1(𝒰, Ob_U)`. -/
def hiddenCouplingClass (H : HiddenCouplingData M K) :
    K.CoverRelativeHn 1 :=
  descentObstructionClass M K H.cocycleProof

end HiddenCouplingData

/--
IV.定理7.1 hypothesis package: a global lawful section compatible with the
selected local sections.

This is the statement-level object whose nonexistence is concluded by
Theorem 7.1: a selected U-adequate cover, a global lawful section factoring
through `Flat_U(X)`, and explicit compatibility with the chosen local sections.
It does not by itself include a coboundary witness; that soundness step is a
separate assumption package below.
-/
structure CompatibleGlobalLawfulSection {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K) where
  uAdequateCover : Prop
  uAdequateCover_holds : uAdequateCover
  globalSection :
    LawAlgebra.LawfulLocus.LawfulSectionData.{v, w} R IOb
  globalLawful : globalSection.Lawful
  restrictsToLocalSections : Prop
  restrictsToLocalSections_holds : restrictsToLocalSections

namespace CompatibleGlobalLawfulSection

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}
variable {M : GluingMismatchData Ob D}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {H : HiddenCouplingData M K}

end CompatibleGlobalLawfulSection

/--
IV.定理7.1 soundness assumption: compatible global lawful sections produce
Čech coboundaries.

This is the formal bridge for the proof sentence "if a global section exists,
then the mismatch is a coboundary".  It is explicit because this implementation layer does
not construct a general descent theorem for all covers.
-/
structure GlobalSectionCoboundarySoundness {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K) where
  coboundaryWitness : K.Cn 0
  mismatch_eq_coboundary :
    M.gluingMismatchCochain = K.d 0 coboundaryWitness

namespace GlobalSectionCoboundarySoundness

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}
variable {M : GluingMismatchData Ob D}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {H : HiddenCouplingData M K}

/--
IV.定理7.1 proof step: a compatible global lawful section makes the hidden
coupling class vanish.
-/
theorem hiddenCouplingClass_eq_zero
    (B : GlobalSectionCoboundarySoundness H) :
    H.hiddenCouplingClass = h1ZeroClass K := by
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  letI := K.cochainAddCommGroup 2
  apply Quotient.sound
  refine ⟨B.coboundaryWitness, ?_⟩
  change M.gluingMismatchCochain - 0 = K.d 0 B.coboundaryWitness
  rw [sub_zero, B.mismatch_eq_coboundary]

end GlobalSectionCoboundarySoundness

/--
R5 / IV-3: finite selected restriction/coboundary surface for compatible
global lawful sections.

For the chosen finite cover/model, this package says how to read a compatible
global lawful section as a degree-zero Čech potential.  The coboundary equality
is not an unqualified field on the final soundness package; it is produced from
the selected compatibility proof `G.restrictsToLocalSections`.
-/
structure FiniteGlobalRestrictionCoboundarySurface {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K) where
  restrictionPotential :
    (G : CompatibleGlobalLawfulSection.{u, v, w} H) ->
      G.restrictsToLocalSections -> K.Cn 0
  mismatch_eq_coboundary_of_restricts :
    ∀ (G : CompatibleGlobalLawfulSection.{u, v, w} H)
      (hrestricts : G.restrictsToLocalSections),
      M.gluingMismatchCochain = K.d 0 (restrictionPotential G hrestricts)

/--
R5 / IV-3: finite overlap-wise soundness data.

This is the concrete finite check beneath
`FiniteGlobalRestrictionCoboundarySurface`: for every selected overlap simplex,
the selected global restriction potential has differential equal to the gluing
mismatch entry.  The surface-level cochain equality is derived from these
pointwise finite checks.
-/
structure FiniteGlobalRestrictionPointwiseSoundness {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K) where
  restrictionPotential :
    (G : CompatibleGlobalLawfulSection.{u, v, w} H) ->
      G.restrictsToLocalSections -> K.Cn 0
  mismatch_eq_coboundary_on_overlap :
    ∀ (G : CompatibleGlobalLawfulSection.{u, v, w} H)
      (hrestricts : G.restrictsToLocalSections) (σ : 𝒰.simplex 1),
      M.gluingMismatchCochain σ =
        K.d 0 (restrictionPotential G hrestricts) σ

namespace FiniteGlobalRestrictionPointwiseSoundness

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}
variable {M : GluingMismatchData Ob D}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {H : HiddenCouplingData M K}

/--
R5 / IV-3: finite overlap-wise checks assemble into the cochain-level
restriction/coboundary surface.
-/
def toFiniteGlobalRestrictionCoboundarySurface
    (P : FiniteGlobalRestrictionPointwiseSoundness.{u, v, w} H) :
    FiniteGlobalRestrictionCoboundarySurface.{u, v, w} H where
  restrictionPotential := P.restrictionPotential
  mismatch_eq_coboundary_of_restricts := by
    intro G hrestricts
    funext σ
    exact P.mismatch_eq_coboundary_on_overlap G hrestricts σ

end FiniteGlobalRestrictionPointwiseSoundness

/--
R5 / IV-3: selected restriction data witnessing that a compatible global
lawful section produces the mismatch as a concrete Čech coboundary.

This is the finite-regime bridge requested by peer-review hardening IV-3.  It does not assert a
general restriction functor for all lawful sections; the selected degree-zero
restriction potential and the equality with the mismatch cochain are explicit
data for the chosen cover/model.
-/
structure GlobalLawfulRestrictionCoboundaryData {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} {H : HiddenCouplingData M K}
    (G : CompatibleGlobalLawfulSection.{u, v, w} H) where
  restrictionPotential : K.Cn 0
  restrictsToLocalSections_holds : G.restrictsToLocalSections
  mismatch_eq_coboundary :
    M.gluingMismatchCochain = K.d 0 restrictionPotential

namespace GlobalLawfulRestrictionCoboundaryData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}
variable {R : Type v} [CommRing R] {IOb : Ideal R}
variable {D : LocalFlatnessData 𝒰 R IOb}
variable {M : GluingMismatchData Ob D}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {H : HiddenCouplingData M K}
variable {G : CompatibleGlobalLawfulSection.{u, v, w} H}

/--
R5 / IV-3: construct selected restriction/coboundary data from the finite
surface by using the actual compatibility proof carried by `G`.
-/
def ofFiniteGlobalRestrictionCoboundarySurface
    (Surf : FiniteGlobalRestrictionCoboundarySurface.{u, v, w} H) :
    GlobalLawfulRestrictionCoboundaryData G where
  restrictionPotential := Surf.restrictionPotential G G.restrictsToLocalSections_holds
  restrictsToLocalSections_holds := G.restrictsToLocalSections_holds
  mismatch_eq_coboundary :=
    Surf.mismatch_eq_coboundary_of_restricts G G.restrictsToLocalSections_holds

/--
R5 / IV-3: selected lawful restriction data gives the coboundary soundness
package consumed by Theorem 7.1.
-/
def toGlobalSectionCoboundarySoundness
    (Dg : GlobalLawfulRestrictionCoboundaryData G) :
    GlobalSectionCoboundarySoundness H where
  coboundaryWitness := Dg.restrictionPotential
  mismatch_eq_coboundary := Dg.mismatch_eq_coboundary

end GlobalLawfulRestrictionCoboundaryData

/--
IV.定理7.1 assumption package: global-to-coboundary soundness for the selected
local flatness setup.
-/
structure LocalFlatnessGapHypotheses {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K) where
  coboundarySoundness :
    CompatibleGlobalLawfulSection.{u, v, w} H -> GlobalSectionCoboundarySoundness H

/--
R5 / IV-3: finite selected restriction soundness for every compatible global
section packages the existing `LocalFlatnessGapHypotheses`.
-/
def localFlatnessGapHypotheses_of_globalRestrictionCoboundaryData
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} {H : HiddenCouplingData M K}
    (soundness :
      (G : CompatibleGlobalLawfulSection.{u, v, w} H) ->
        GlobalLawfulRestrictionCoboundaryData G) :
    LocalFlatnessGapHypotheses.{u, v, w} H where
  coboundarySoundness := fun G =>
    (soundness G).toGlobalSectionCoboundarySoundness

/--
R5 / IV-3: a finite selected restriction/coboundary surface packages the
existing `LocalFlatnessGapHypotheses`.
-/
def localFlatnessGapHypotheses_of_finiteGlobalRestrictionCoboundarySurface
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} {H : HiddenCouplingData M K}
    (Surf : FiniteGlobalRestrictionCoboundarySurface.{u, v, w} H) :
    LocalFlatnessGapHypotheses.{u, v, w} H :=
  localFlatnessGapHypotheses_of_globalRestrictionCoboundaryData
    (fun _G =>
      GlobalLawfulRestrictionCoboundaryData.ofFiniteGlobalRestrictionCoboundarySurface
        Surf)

/--
R5 / IV-3: finite overlap-wise soundness packages the existing
`LocalFlatnessGapHypotheses`.
-/
def localFlatnessGapHypotheses_of_finiteGlobalRestrictionPointwiseSoundness
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} {H : HiddenCouplingData M K}
    (P : FiniteGlobalRestrictionPointwiseSoundness.{u, v, w} H) :
    LocalFlatnessGapHypotheses.{u, v, w} H :=
  localFlatnessGapHypotheses_of_finiteGlobalRestrictionCoboundarySurface
    P.toFiniteGlobalRestrictionCoboundarySurface

/--
IV.定理7.1: Local Flatness Gap.

If the selected hidden coupling class is nonzero, then no global lawful section
can both factor through `Flat_U(X)` and restrict to the chosen local sections.
The statement is the contrapositive of the explicit coboundary step above and
does not claim global descent or construct nonzero classes.
-/
theorem localFlatnessGap_no_globalLawfulSection
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K)
    (Hyp : LocalFlatnessGapHypotheses.{u, v, w} H)
    (h_nonzero : H.hiddenCouplingClass ≠ h1ZeroClass K) :
    ¬ Nonempty (CompatibleGlobalLawfulSection.{u, v, w} H) := by
  intro hglobal
  rcases hglobal with ⟨G⟩
  exact h_nonzero (Hyp.coboundarySoundness G).hiddenCouplingClass_eq_zero

/--
R5 / IV-3: Local Flatness Gap using finite selected global-restriction
soundness data directly.

This theorem is the nonexistence conclusion of Theorem 7.1, but the
global-to-coboundary step is supplied as concrete restriction coboundary data
for each compatible global section rather than as an already-packaged
`GlobalSectionCoboundarySoundness`.
-/
theorem localFlatnessGap_no_globalLawfulSection_of_globalRestrictionCoboundaryData
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K)
    (soundness :
      (G : CompatibleGlobalLawfulSection.{u, v, w} H) ->
        GlobalLawfulRestrictionCoboundaryData G)
    (h_nonzero : H.hiddenCouplingClass ≠ h1ZeroClass K) :
    ¬ Nonempty (CompatibleGlobalLawfulSection.{u, v, w} H) :=
  localFlatnessGap_no_globalLawfulSection H
    (localFlatnessGapHypotheses_of_globalRestrictionCoboundaryData soundness)
    h_nonzero

/--
R5 / IV-3: Local Flatness Gap using a finite selected
global-restriction/coboundary surface directly.
-/
theorem localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionCoboundarySurface
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K)
    (Surf : FiniteGlobalRestrictionCoboundarySurface.{u, v, w} H)
    (h_nonzero : H.hiddenCouplingClass ≠ h1ZeroClass K) :
    ¬ Nonempty (CompatibleGlobalLawfulSection.{u, v, w} H) :=
  localFlatnessGap_no_globalLawfulSection H
    (localFlatnessGapHypotheses_of_finiteGlobalRestrictionCoboundarySurface Surf)
    h_nonzero

/--
R5 / IV-3: Local Flatness Gap using finite overlap-wise
global-restriction/coboundary soundness directly.
-/
theorem localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionPointwiseSoundness
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S} {R : Type v} [CommRing R] {IOb : Ideal R}
    {D : LocalFlatnessData 𝒰 R IOb} {M : GluingMismatchData Ob D}
    {K : CoverRelativeCechComplex 𝒰 Ob} (H : HiddenCouplingData M K)
    (P : FiniteGlobalRestrictionPointwiseSoundness.{u, v, w} H)
    (h_nonzero : H.hiddenCouplingClass ≠ h1ZeroClass K) :
    ¬ Nonempty (CompatibleGlobalLawfulSection.{u, v, w} H) :=
  localFlatnessGap_no_globalLawfulSection H
    (localFlatnessGapHypotheses_of_finiteGlobalRestrictionPointwiseSoundness P)
    h_nonzero

end Cohomology
end AAT.AG
