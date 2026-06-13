import Formal.AG.LawAlgebra.ObstructionIdeal

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v w

namespace LawfulLocus

variable (A : Type v) [CommRing A]

/-- III.定義7.1: lawful locus `Flat_U(X) = V(I_Ob^U)`. -/
def lawfulLocus (IOb : Ideal A) : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus IOb

/-- III.定義7.1: lawful locus attached to a selected local obstruction ideal family. -/
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

/-- III.定義7.2: section lawfulness is primary obstruction-ideal vanishing. -/
def Lawful {IOb : Ideal A} (s : LawfulSectionData.{v, w} A IOb) : Prop :=
  s.pulledObstructionIdeal = ⊥

/--
III.定義7.2: factorization through the lawful locus.

At this abstraction level, factorization through `V(I_Ob)` is represented by
the same vanishing condition that defines the closed locus. Later affine/scheme
layers can attach the geometric map object without changing this equivalence.
-/
structure FactorsThroughLawfulLocus {IOb : Ideal A}
    (s : LawfulSectionData.{v, w} A IOb) : Prop where
  pulled_vanishes : s.pulledObstructionIdeal = ⊥

/-- III.定義7.2: lawfulness is exactly `s^* I_Ob^U = 0`. -/
theorem lawful_iff_pulledObstructionIdeal_eq_bot {IOb : Ideal A}
    (s : LawfulSectionData.{v, w} A IOb) :
    s.Lawful ↔ s.pulledObstructionIdeal = ⊥ :=
  Iff.rfl

/-- III.定義7.2: lawful sections factor through the lawful locus. -/
theorem factorsThroughLawfulLocus_of_lawful {IOb : Ideal A}
    {s : LawfulSectionData.{v, w} A IOb} (h : s.Lawful) :
    s.FactorsThroughLawfulLocus :=
  ⟨h⟩

/-- III.定義7.2: factorization through the lawful locus implies lawfulness. -/
theorem lawful_of_factorsThroughLawfulLocus {IOb : Ideal A}
    {s : LawfulSectionData.{v, w} A IOb} (h : s.FactorsThroughLawfulLocus) :
    s.Lawful :=
  h.pulled_vanishes

/-- III.定義7.2: factorization through `Flat_U(X)` is equivalent to lawfulness. -/
theorem lawful_iff_factorsThroughLawfulLocus {IOb : Ideal A}
    (s : LawfulSectionData.{v, w} A IOb) :
    s.Lawful ↔ s.FactorsThroughLawfulLocus :=
  ⟨factorsThroughLawfulLocus_of_lawful A, lawful_of_factorsThroughLawfulLocus A⟩

end LawfulSectionData

/-- III.定義7.2: section data for a selected local obstruction ideal family. -/
abbrev LocalLawfulSectionData
    (F : ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :=
  LawfulSectionData.{v, w} A F.localObstructionIdeal

end LawfulLocus

end LawAlgebra
end AAT.AG
