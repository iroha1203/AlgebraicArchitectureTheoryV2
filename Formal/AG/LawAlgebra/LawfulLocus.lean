import Formal.AG.LawAlgebra.ObstructionIdeal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v w

namespace LawfulLocus

variable (A : Type v) [CommRing A]

/-- III.定義7.1: affine zero-set calculation `Flat_U(X) = V(I_Ob^U)`. -/
def lawfulLocus (IOb : Ideal A) : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus IOb

/-- III.定義7.1: affine zero-set attached to a selected local obstruction ideal family. -/
def localLawfulLocus
    (F : ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :
    Set (PrimeSpectrum A) :=
  lawfulLocus A F.localObstructionIdeal

/--
III.定義7.2: section-valued pullback of an obstruction ideal.

The section is represented only by its ring pullback at this layer. This keeps
R8 independent of later scheme/gluing choices while preserving the primary
condition `s^* I_Ob^U = 0`.
-/
structure LawfulSectionData (IOb : Ideal A) where
  SectionRing : Type w
  commRing : CommRing SectionRing
  pullback : A →+* SectionRing

attribute [instance] LawfulSectionData.commRing

namespace LawfulSectionData

/-- III.定義7.2: pulled obstruction ideal `s^* I_Ob^U`. -/
def pulledObstructionIdeal {IOb : Ideal A} (s : LawfulSectionData.{v, w} A IOb) :
    Ideal s.SectionRing :=
  Ideal.map s.pullback IOb

/--
III.R4 / III-2: the affine point map induced by a section pullback.

This is the geometric map `Spec(s.SectionRing) -> Spec(A)` obtained by
pulling prime ideals back along `s.pullback`.
-/
def sectionPrimeMap {IOb : Ideal A} (s : LawfulSectionData.{v, w} A IOb) :
    PrimeSpectrum s.SectionRing -> PrimeSpectrum A :=
  PrimeSpectrum.comap s.pullback

/-- III.定義7.2: section lawfulness is primary obstruction-ideal vanishing. -/
def Lawful {IOb : Ideal A} (s : LawfulSectionData.{v, w} A IOb) : Prop :=
  s.pulledObstructionIdeal = ⊥

/-- III.定義7.2: lawfulness is exactly `s^* I_Ob^U = 0`. -/
theorem lawful_iff_pulledObstructionIdeal_eq_bot {IOb : Ideal A}
    (s : LawfulSectionData.{v, w} A IOb) :
    s.Lawful ↔ s.pulledObstructionIdeal = ⊥ :=
  Iff.rfl

/--
III.R4 / III-2: if the obstruction ideal is killed by the section pullback,
then every induced prime point lands in the lawful zero locus.

This is the one-way geometric bridge from ideal vanishing to image containment.
It deliberately does not assert the converse, where radical information matters.
-/
theorem sectionPrimeMap_mem_lawfulLocus_of_le_ker {IOb : Ideal A}
    (s : LawfulSectionData.{v, w} A IOb)
    (hI : IOb ≤ RingHom.ker s.pullback) (p : PrimeSpectrum s.SectionRing) :
    sectionPrimeMap A s p ∈ lawfulLocus A IOb := by
  rw [lawfulLocus, PrimeSpectrum.mem_zeroLocus]
  intro x hx
  change s.pullback x ∈ p.asIdeal
  have hx_zero : s.pullback x = 0 := hI hx
  rw [hx_zero]
  exact p.asIdeal.zero_mem

/--
III.R4 / III-2: pulled obstruction ideal vanishing forces the induced prime
map to land in the lawful zero locus.
-/
theorem sectionPrimeMap_mem_lawfulLocus_of_pulledObstructionIdeal_eq_bot
    {IOb : Ideal A} (s : LawfulSectionData.{v, w} A IOb)
    (hvanish : s.pulledObstructionIdeal = ⊥) (p : PrimeSpectrum s.SectionRing) :
    sectionPrimeMap A s p ∈ lawfulLocus A IOb :=
  sectionPrimeMap_mem_lawfulLocus_of_le_ker A s
    ((Ideal.map_eq_bot_iff_le_ker s.pullback).mp hvanish) p

/--
III.R4 / III-2: lawful sections induce prime maps whose image is contained in
the lawful zero locus.
-/
theorem sectionPrimeMap_mem_lawfulLocus_of_lawful {IOb : Ideal A}
    (s : LawfulSectionData.{v, w} A IOb) (h : s.Lawful)
    (p : PrimeSpectrum s.SectionRing) :
    sectionPrimeMap A s p ∈ lawfulLocus A IOb :=
  sectionPrimeMap_mem_lawfulLocus_of_pulledObstructionIdeal_eq_bot A s h p

end LawfulSectionData

/-- III.定義7.2: section data for a selected local obstruction ideal family. -/
abbrev LocalLawfulSectionData
    (F : ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :=
  LawfulSectionData.{v, w} A F.localObstructionIdeal

/--
III.R4 / III-2: section prime map for a selected local obstruction ideal family.
-/
def localSectionPrimeMap
    (F : ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A)
    (s : LocalLawfulSectionData.{u, v, w} A F) :
    PrimeSpectrum s.SectionRing -> PrimeSpectrum A :=
  LawfulSectionData.sectionPrimeMap A s

/--
III.R4 / III-2: a lawful local section for a selected witness family has image
contained in the corresponding local lawful zero locus.
-/
theorem localSectionPrimeMap_mem_localLawfulLocus_of_lawful
    (F : ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A)
    (s : LocalLawfulSectionData.{u, v, w} A F) (h : s.Lawful)
    (p : PrimeSpectrum s.SectionRing) :
    localSectionPrimeMap A F s p ∈ localLawfulLocus A F :=
  LawfulSectionData.sectionPrimeMap_mem_lawfulLocus_of_lawful A s h p

end LawfulLocus

end LawAlgebra
end AAT.AG
