import Formal.AG.Atom.Axioms
import ResearchLean.AG.CanonicalResolution.Effective

/-!
# Doctrine-induced readings and admissible classes

This module defines the representability contract used by F3 and F4 of
`G-103-aat-canonical-resolution`.  A `DoctrineOn` carries an actual
`ExtractionDoctrine` together with equality of its internal source type to the
fixed source.  Its reading is generated from equality of extracted Atom sets.

An admissible class contains only a finite index and the corresponding
fixed-source doctrines.  It stores neither readings nor representability
certificates.
-/

namespace AAT.AG.CanonicalResolution

universe u

/-- An extraction doctrine whose internal source type is the fixed source. -/
structure DoctrineOn (U : AtomCarrier.{u}) (Source : Type u) where
  /-- The actual extraction doctrine. -/
  doctrine : ExtractionDoctrine U
  /-- Identification of the doctrine's internal source with the fixed source. -/
  source_eq : doctrine.Source = Source

namespace DoctrineOn

variable {U : AtomCarrier.{u}} {Source : Type u}

/-- Transport a fixed source into the source type stored by the doctrine. -/
def castSource (D : DoctrineOn U Source) (source : Source) : D.doctrine.Source :=
  D.source_eq.symm ▸ source

/-- The actual set of Atoms extracted by a doctrine from a fixed source. -/
def extractedAtoms (D : DoctrineOn U Source) (source : Source) : Set U.Atom :=
  { atom | D.doctrine.extracts (D.castSource source) atom }

/-- Two sources are doctrine-equivalent when their extracted Atom sets agree. -/
def Equivalent (D : DoctrineOn U Source) (x y : Source) : Prop :=
  D.extractedAtoms x = D.extractedAtoms y

/-- Equality of extracted Atom sets as a source setoid. -/
def setoid (D : DoctrineOn U Source) : Setoid Source where
  r := D.Equivalent
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun hxy hyz => hxy.trans hyz
  }

/-- The reading induced by equality of a doctrine's extracted Atom sets. -/
def reading (D : DoctrineOn U Source) : Reading Source where
  Target := Quotient D.setoid
  read := Quotient.mk D.setoid
  surjective := Quotient.mk_surjective

/-- The doctrine-induced reading kernel is exactly equality of extraction sets. -/
theorem reading_kernel_iff (D : DoctrineOn U Source) (x y : Source) :
    D.reading.Kernel x y ↔ D.extractedAtoms x = D.extractedAtoms y := by
  change Quotient.mk D.setoid x = Quotient.mk D.setoid y ↔ D.Equivalent x y
  exact Quotient.eq

end DoctrineOn

/-- A finite declared family of extraction doctrines on one fixed source. -/
structure AdmissibleClass (U : AtomCarrier.{u}) (Source : Type u) where
  /-- Finite doctrine index. -/
  Index : Type u
  /-- Enumeration of the declared doctrines. -/
  indexFintype : Fintype Index
  /-- The doctrine selected by each index. -/
  doctrine : Index → DoctrineOn U Source

namespace AdmissibleClass

variable {U : AtomCarrier.{u}} {Source : Type u}

instance instFintypeIndex (admissible : AdmissibleClass U Source) :
    Fintype admissible.Index :=
  admissible.indexFintype

/--
The canonical law reading is representable when one declared doctrine induces
the same source kernel.
-/
def Representable (admissible : AdmissibleClass U Source)
    (laws : FiniteLawFamily Source) : Prop :=
  ∃ index, laws.jointKernelReading.KernelEquivalent
    (admissible.doctrine index).reading

end AdmissibleClass

end AAT.AG.CanonicalResolution

#assert_standard_axioms_only AAT.AG.CanonicalResolution
