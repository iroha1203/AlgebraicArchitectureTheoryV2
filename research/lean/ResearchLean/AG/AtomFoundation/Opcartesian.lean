import ResearchLean.AG.AtomFoundation.Deconjugation
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# Opcartesian package transport

This module lifts complete upper deconjugation to the package total category.
For an arbitrary exact pointed tail and an arbitrary total hom over its
composite with the canonical base morphism, it constructs the unique total
factor and instantiates mathlib's strong cocartesian universal property.
-/

namespace AAT.AG.AtomFoundation

universe u

open CategoryTheory

/-- Atom compatibility required by the total factor is derived from its base. -/
private theorem packageTotalFactor_atomEquiv {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (tau : ExtInstHom (packagePoint (transportAlong P f)) (packagePoint R))
    (h : PackageTotalHom P R)
    (hbase : h.base = (transportAlongHom P f).base.comp tau) :
    h.upper.atomEquiv =
      f.atomEquiv.trans tau.doctrineHom.atomEquiv := by
  calc
    h.upper.atomEquiv = h.base.doctrineHom.atomEquiv := h.atomEquiv_eq
    _ = ((transportAlongHom P f).base.comp tau).doctrineHom.atomEquiv :=
      congrArg (fun base => base.doctrineHom.atomEquiv) hbase
    _ = f.atomEquiv.trans tau.doctrineHom.atomEquiv := rfl

/--
The total-package factor of an arbitrary hom over a composite exact base map.

No factor hom or universal-property certificate is an input.  Its upper part
is the canonical deconjugation and its lower part is exactly the supplied tail.
-/
noncomputable def packageTotalFactor {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (tau : ExtInstHom (packagePoint (transportAlong P f)) (packagePoint R))
    (h : PackageTotalHom P R)
    (hbase : h.base = (transportAlongHom P f).base.comp tau) :
    PackageTotalHom (transportAlong P f) R where
  base := tau
  upper := deconjugateTransportUpper P R f tau.doctrineHom.atomEquiv h.upper
    (packageTotalFactor_atomEquiv P R f tau h hbase)
  atomEquiv_eq := rfl

/-- The constructed total factor lies over the supplied exact pointed tail. -/
@[simp]
theorem packageTotalFactor_base {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (tau : ExtInstHom (packagePoint (transportAlong P f)) (packagePoint R))
    (h : PackageTotalHom P R)
    (hbase : h.base = (transportAlongHom P f).base.comp tau) :
    (packageTotalFactor P R f tau h hbase).base = tau :=
  rfl

/-- The canonical total hom followed by its constructed factor is the input hom. -/
theorem packageTotalFactor_fac {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (tau : ExtInstHom (packagePoint (transportAlong P f)) (packagePoint R))
    (h : PackageTotalHom P R)
    (hbase : h.base = (transportAlongHom P f).base.comp tau) :
    (transportAlongHom P f).comp (packageTotalFactor P R f tau h hbase) = h := by
  apply PackageTotalHom.ext
  · exact hbase.symm
  · exact transportAlongUpper_comp_deconjugate P R f
      tau.doctrineHom.atomEquiv h.upper
      (packageTotalFactor_atomEquiv P R f tau h hbase)

/-- Every total factor over the supplied tail is the constructed one. -/
theorem packageTotalFactor_unique {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (tau : ExtInstHom (packagePoint (transportAlong P f)) (packagePoint R))
    (h : PackageTotalHom P R)
    (hbase : h.base = (transportAlongHom P f).base.comp tau)
    (k : PackageTotalHom (transportAlong P f) R)
    (hkbase : k.base = tau)
    (hkfac : (transportAlongHom P f).comp k = h) :
    k = packageTotalFactor P R f tau h hbase := by
  apply PackageTotalHom.ext
  · exact hkbase
  · apply deconjugateTransportUpper_unique P R f
      tau.doctrineHom.atomEquiv h.upper
      (packageTotalFactor_atomEquiv P R f tau h hbase)
    exact congrArg PackageTotalHom.upper hkfac

/-- Explicit unique-factor formulation of the package transport universal property. -/
theorem transportAlongHom_factor_existsUnique {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (tau : ExtInstHom (packagePoint (transportAlong P f)) (packagePoint R))
    (h : PackageTotalHom P R)
    (hbase : h.base = (transportAlongHom P f).base.comp tau) :
    ∃! k : PackageTotalHom (transportAlong P f) R,
      k.base = tau ∧ (transportAlongHom P f).comp k = h := by
  refine ⟨packageTotalFactor P R f tau h hbase, ⟨rfl, ?_⟩, ?_⟩
  · exact packageTotalFactor_fac P R f tau h hbase
  · intro k hk
    exact packageTotalFactor_unique P R f tau h hbase k hk.1 hk.2

/--
Canonical package transport is strongly cocartesian over `packageProjection`.

The strong form is essential: its universal property quantifies over every
exact pointed tail, matching the G-101 statement rather than restricting the
base tail to an identity.
-/
theorem transportAlongHom_isStronglyCocartesian {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (packageProjection U).IsStronglyCocartesian
      (transportAlongHom P f).base (transportAlongHom P f) := by
  letI : (packageProjection U).IsHomLift
      (transportAlongHom P f).base (transportAlongHom P f) := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map (transportAlongHom P f))
      (transportAlongHom P f)
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCocartesian.mk
  intro R tau h hLift
  have hbase : h.base = (transportAlongHom P f).base.comp tau := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (packageProjection U)
      ((transportAlongHom P f).base.comp tau) h).symm
  rcases transportAlongHom_factor_existsUnique P R f tau h hbase with
    ⟨k, hk, hunique⟩
  refine ⟨k, ?_, ?_⟩
  · constructor
    · rw [← hk.1]
      change (packageProjection U).IsHomLift
        ((packageProjection U).map k) k
      infer_instance
    · exact hk.2
  · intro k' hk'
    apply hunique k'
    constructor
    · letI : (packageProjection U).IsHomLift tau k' := hk'.1
      exact (CategoryTheory.IsHomLift.eq_of_isHomLift
        (packageProjection U) tau k').symm
    · exact hk'.2

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
