import Formal.AG.Evolution.TemporalLaw

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R4 / AC10 temporal mismatch, cocycle, and class surface.

This file records temporal obstruction classes only after the selected
temporal site, coefficient, Čech bridge, temporal law, and mismatch cocycle
are supplied.  It does not infer concrete temporal failure from a nonzero
cohomology group alone.
-/

/--
IX.§3.4 / AC10: temporal mismatch cochain for a selected temporal law.

The cochain lives in the Part IV cover-relative Čech complex selected by the
temporal bridge and the obstruction sheaf backing `TempCoeff_A`.
-/
structure TemporalMismatch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    (Coeff : TemporalCoefficient T) (Law : TemporalLaw St) where
  bridge : TemporalCechBridge T Coeff.obstructionSheaf
  degree : Nat
  cochain : bridge.siteComplex.Cn degree
  supportedByLaw : Prop
  supportedByLaw_cert : supportedByLaw

namespace TemporalMismatch

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}

/-- IX.§3.4 / AC10: read the selected mismatch cochain. -/
def asCochain (m : TemporalMismatch Coeff Law) :
    m.bridge.siteComplex.Cn m.degree :=
  m.cochain

/-- IX.§3.4 / AC10: the mismatch is explicitly tied to the selected law. -/
theorem supported_by_law (m : TemporalMismatch Coeff Law) :
    m.supportedByLaw :=
  m.supportedByLaw_cert

end TemporalMismatch

/--
IX.§3.4 / AC10: temporal cocycle package.

The zero-differential witness is stored at the selected degree of the mismatch.
-/
structure TemporalCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (m : TemporalMismatch Coeff Law) where
  differential_zero :
    letI := m.bridge.siteComplex.cochainAddCommGroup (m.degree + 1)
    m.bridge.siteComplex.d m.degree m.cochain = 0

namespace TemporalCocycle

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {m : TemporalMismatch Coeff Law}

/-- IX.§3.4 / AC10: package a mismatch cocycle as the Part IV cocycle subtype. -/
def asCechCocycle (hm : TemporalCocycle m) :
    m.bridge.siteComplex.CechCocycle m.degree :=
  ⟨m.cochain, hm.differential_zero⟩

/-- IX.§3.4 / AC10: the selected mismatch has zero Čech differential. -/
theorem differential_zero_holds (hm : TemporalCocycle m) :
    letI := m.bridge.siteComplex.cochainAddCommGroup (m.degree + 1)
    m.bridge.siteComplex.d m.degree m.cochain = 0 :=
  hm.differential_zero

/-- IX.§3.4 / AC10: the cover-relative cohomology class selected by a cocycle. -/
def cohomologyClass (hm : TemporalCocycle m) :
    m.bridge.siteComplex.CoverRelativeHn m.degree := by
  cases hdeg : m.degree with
  | zero =>
      simpa [Cohomology.CoverRelativeCechComplex.CoverRelativeHn, hdeg]
        using hm.asCechCocycle
  | succ n =>
      have hc : m.bridge.siteComplex.CechCocycle (n + 1) := by
        simpa [hdeg] using hm.asCechCocycle
      simpa [Cohomology.CoverRelativeCechComplex.CoverRelativeHn, hdeg]
        using m.bridge.siteComplex.cohomologyClassSucc n hc

end TemporalCocycle

/--
IX.§3.4 / AC10: temporal cohomology class of a mismatch cocycle.

The class is formed from a concrete selected mismatch and its cocycle witness.
This is the boundary that prevents reading bare nonzero cohomology groups as
concrete temporal failures.
-/
structure TemporalClass {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (m : TemporalMismatch Coeff Law) where
  cocycle : TemporalCocycle m

namespace TemporalClass

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {m : TemporalMismatch Coeff Law}

/-- IX.§3.4 / AC10: read the cohomology class selected for the mismatch. -/
def cohomologyClass (C : TemporalClass m) :
    m.bridge.siteComplex.CoverRelativeHn m.degree :=
  C.cocycle.cohomologyClass

/-- IX.§3.4 / AC10: the class is definitionally tied to the selected mismatch cocycle. -/
theorem class_matches_selected_cocycle (C : TemporalClass m) :
    C.cohomologyClass = C.cocycle.cohomologyClass :=
  rfl

end TemporalClass

/--
IX.§3.4 / AC10: concrete temporal obstruction class boundary.

A concrete obstruction class is a selected temporal class plus a selected
nonzero predicate for that class.  The predicate is an explicit input; it is
not inferred from the ambient cohomology group.
-/
structure ConcreteTemporalObstructionClass {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    {m : TemporalMismatch Coeff Law} (C : TemporalClass m) where
  selectedNonzero : m.bridge.siteComplex.CoverRelativeHn m.degree -> Prop
  obstructionWitness : selectedNonzero C.cohomologyClass

namespace ConcreteTemporalObstructionClass

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {m : TemporalMismatch Coeff Law}
variable {C : TemporalClass m}

/-- IX.§3.4 / AC10: concrete obstruction evidence is explicitly selected. -/
theorem selected_nonzero_holds (O : ConcreteTemporalObstructionClass C) :
    O.selectedNonzero C.cohomologyClass :=
  O.obstructionWitness

end ConcreteTemporalObstructionClass

end Evolution
end AAT.AG
