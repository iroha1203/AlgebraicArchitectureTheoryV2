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

/-- IV.定理7.1 hypothesis: the global section factors through `Flat_U`. -/
def globalFactorsThroughFlat_U (G : CompatibleGlobalLawfulSection H) :
    G.globalSection.FactorsThroughLawfulLocus :=
  LawAlgebra.LawfulLocus.LawfulSectionData.factorsThroughLawfulLocus_of_lawful R
    G.globalLawful

end CompatibleGlobalLawfulSection

/--
IV.定理7.1 soundness assumption: compatible global lawful sections produce
Čech coboundaries.

This is the formal bridge for the proof sentence "if a global section exists,
then the mismatch is a coboundary".  It is explicit because this PRD layer does
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

end Cohomology
end AAT.AG
