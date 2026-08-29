import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Configuration
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.SelectedTransport

/-!
# Cartesian lifts for the refinement package projection

This module establishes the actual mathlib cartesian interface for the explicit
refinement projection.  The criterion needs a two-sided inverse only for the
complete upper reading; it never assumes that the lower refinement is exact.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Equality transport in the pointed refinement category fixes every Atom. -/
@[simp]
theorem PointedRefinementHom.eqToHom_atomMap
    {U : AtomCarrier.{u}} {X Y : PointedRefinementObject U} (h : X = Y)
    (atom : U.Atom) :
    ((eqToHom h : X ⟶ Y).doctrineHom.atomMap atom) = atom := by
  subst h
  rfl

/-- A strongly cartesian refinement-package lift of a pointed refinement. -/
structure RefinementCartesianLift {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (r : PointedRefinementHom X Y)
    (targetPackage : CoreFiber Y) where
  /-- Authored package over the refinement source. -/
  domain : AATCorePackage U
  /-- Complete package map ending at the requested target package. -/
  hom : RefinementPackageHom ⟨domain⟩ ⟨targetPackage.1⟩
  /-- The generated map is strongly cartesian for the refinement projection. -/
  isStronglyCartesian :
    (refinementPackageProjection U).IsStronglyCartesian r hom

/-- A cleavage is an objectwise choice of actual strong cartesian lifts. -/
structure RefinementCartesianCleavage {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (r : PointedRefinementHom X Y) where
  /-- Lift every actual package over the target selected point. -/
  lift : ∀ targetPackage : CoreFiber Y, RefinementCartesianLift r targetPackage

/-- A complete upper isomorphism makes a refinement package map strongly cartesian. -/
theorem refinementPackageHom_isStronglyCartesian_of_upper_inverse
    {U : AtomCarrier.{u}} {P Q : RefinementPackageObject U}
    (φ : RefinementPackageHom P Q)
    (inv : SignedExactCoreReadingHom Q.package P.package)
    (hom_inv : φ.upper.comp inv = SignedExactCoreReadingHom.refl P.package)
    (inv_hom : inv.comp φ.upper = SignedExactCoreReadingHom.refl Q.package) :
    (refinementPackageProjection U).IsStronglyCartesian φ.base φ := by
  letI : (refinementPackageProjection U).IsHomLift φ.base φ := by
    change (refinementPackageProjection U).IsHomLift
      ((refinementPackageProjection U).map φ) φ
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCartesian.mk
  intro R g h hLift
  have hbase : h.base = g.comp φ.base := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (refinementPackageProjection U) (g.comp φ.base) h).symm
  let k : RefinementPackageHom R P := {
    base := g
    upper := h.upper.comp inv
    atomEquiv_eq := by
      apply Equiv.ext
      intro atom
      change inv.atomEquiv (h.upper.atomEquiv atom) =
        g.doctrineHom.atomEquiv atom
      rw [h.atomEquiv_eq]
      have hbaseAtom := congrArg
        (fun base => base.doctrineHom.atomEquiv atom) hbase
      change h.base.doctrineHom.atomEquiv atom =
        φ.base.doctrineHom.atomEquiv (g.doctrineHom.atomEquiv atom)
          at hbaseAtom
      rw [hbaseAtom, ← φ.atomEquiv_eq]
      have hcancel := congrArg
        (fun upper => upper.atomEquiv (g.doctrineHom.atomEquiv atom)) hom_inv
      simpa [SignedExactCoreReadingHom.comp,
        SignedExactCoreReadingHom.refl] using hcancel
  }
  have hkfac : k.comp φ = h := by
    apply RefinementPackageHom.ext
    · exact hbase.symm
    · change (h.upper.comp inv).comp φ.upper = h.upper
      rw [PackageTotalHom.upper_comp_assoc, inv_hom,
        PackageTotalHom.upper_comp_id]
  refine ⟨k, ?_, ?_⟩
  · constructor
    · change (refinementPackageProjection U).IsHomLift g k
      change (refinementPackageProjection U).IsHomLift
        ((refinementPackageProjection U).map k) k
      infer_instance
    · exact hkfac
  · intro k' hk'
    apply RefinementPackageHom.ext
    · letI : (refinementPackageProjection U).IsHomLift g k' := hk'.1
      exact (CategoryTheory.IsHomLift.eq_of_isHomLift
        (refinementPackageProjection U) g k').symm
    · have hupper : k'.upper.comp φ.upper = h.upper := by
        simpa [RefinementPackageHom.comp] using
          congrArg RefinementPackageHom.upper hk'.2
      change k'.upper = h.upper.comp inv
      calc
        k'.upper = k'.upper.comp (SignedExactCoreReadingHom.refl P.package) :=
          (PackageTotalHom.upper_comp_id k'.upper).symm
        _ = k'.upper.comp (φ.upper.comp inv) := by rw [hom_inv]
        _ = (k'.upper.comp φ.upper).comp inv := by
          rw [PackageTotalHom.upper_comp_assoc]
        _ = h.upper.comp inv := by rw [hupper]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
