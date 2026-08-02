import ResearchLean.AG.AtomFoundation.Opcartesian

/-!
# Uniqueness of opcartesian package lifts

This module instantiates the categorical uniqueness theorem for the canonical
package transport.  The resulting isomorphism is described inside the fiber:
both legs lie over the equality-induced identity transport, and both complete
upper morphisms use `Equiv.refl` on Atoms.
-/

namespace AAT.AG.AtomFoundation

universe u

open CategoryTheory

/-- An equality-induced pointed morphism acts trivially on the fixed Atom carrier. -/
@[simp]
theorem ExtInstHom.eqToHom_atomEquiv {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (h : X = Y) :
    (eqToHom h : ExtInstHom X Y).doctrineHom.atomEquiv = Equiv.refl U.Atom := by
  subst h
  rfl

/--
A concrete package isomorphism inside one pointed-doctrine fiber.

The object equality `hpoint` supplies only the dependent type alignment.  The
two lower morphisms and the two upper Atom equivalences are fixed explicitly;
they are not supplied as certificates.
-/
structure PackageFiberInnerIso {U : AtomCarrier.{u}}
    (C Q : AATCorePackage U)
    (hpoint : packagePoint C = packagePoint Q) where
  /-- The package-level isomorphism. -/
  iso : C ≅ Q
  /-- Its forward leg is the equality-induced identity transport in the fiber. -/
  hom_base_eq :
    iso.hom.base =
      (eqToHom hpoint : ExtInstHom (packagePoint C) (packagePoint Q))
  /-- Its inverse leg is the reverse equality-induced identity transport. -/
  inv_base_eq :
    iso.inv.base =
      (eqToHom hpoint.symm : ExtInstHom (packagePoint Q) (packagePoint C))
  /-- The complete forward upper hom uses the identity Atom equivalence. -/
  hom_atomEquiv_eq : iso.hom.upper.atomEquiv = Equiv.refl U.Atom
  /-- The complete inverse upper hom uses the identity Atom equivalence. -/
  inv_atomEquiv_eq : iso.inv.upper.atomEquiv = Equiv.refl U.Atom

/--
The canonical transport lift and any strongly cocartesian lift over the same
exact base are connected by a concrete fiber-inner package isomorphism.

The arbitrary target `Q` need only be identified with the canonical target at
the pointed-doctrine level.  The isomorphism, both total homs, their inverses,
and their Atom equivalences are all derived from the two universal properties.
-/
noncomputable def transportAlong_liftUniqueUpToFiberIso {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (hpoint : packagePoint (transportAlong P f) = packagePoint Q)
    (phi : PackageTotalHom P Q)
    [(packageProjection U).IsStronglyCocartesian
      ((transportAlongHom P f).base.comp
        (eqToHom hpoint : ExtInstHom
          (packagePoint (transportAlong P f)) (packagePoint Q))) phi] :
    PackageFiberInnerIso (transportAlong P f) Q hpoint := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongHom P f).base (transportAlongHom P f) :=
    transportAlongHom_isStronglyCocartesian P f
  have baseFac :
      (transportAlongHom P f).base.comp
          (eqToHom hpoint : ExtInstHom
            (packagePoint (transportAlong P f)) (packagePoint Q)) =
        (transportAlongHom P f).base ≫ (eqToIso hpoint).hom := by
    rfl
  let packageIso : transportAlong P f ≅ Q :=
    CategoryTheory.Functor.IsStronglyCocartesian.codomainIsoOfBaseIso
      (p := packageProjection U)
      (f := (transportAlongHom P f).base)
      (f' := (transportAlongHom P f).base.comp
        (eqToHom hpoint : ExtInstHom
          (packagePoint (transportAlong P f)) (packagePoint Q)))
      (g := eqToIso hpoint)
      baseFac
      (transportAlongHom P f) phi
  have homLift : (packageProjection U).IsHomLift
      (eqToHom hpoint : ExtInstHom
        (packagePoint (transportAlong P f)) (packagePoint Q)) packageIso.hom := by
    change (packageProjection U).IsHomLift
      (eqToHom hpoint : ExtInstHom
        (packagePoint (transportAlong P f)) (packagePoint Q))
      (CategoryTheory.Functor.IsStronglyCocartesian.map
        (packageProjection U) (transportAlongHom P f).base
        (transportAlongHom P f) baseFac phi)
    infer_instance
  have invLift : (packageProjection U).IsHomLift
      (eqToHom hpoint.symm : ExtInstHom
        (packagePoint Q) (packagePoint (transportAlong P f))) packageIso.inv := by
    letI : (packageProjection U).IsHomLift
        (eqToIso hpoint).hom packageIso.hom := by
      simpa using homLift
    simpa using CategoryTheory.IsHomLift.inv_lift_inv
      (packageProjection U) (eqToIso hpoint) packageIso
  have homBase : packageIso.hom.base =
      (eqToHom hpoint : ExtInstHom
        (packagePoint (transportAlong P f)) (packagePoint Q)) := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (packageProjection U) _ packageIso.hom).symm
  have invBase : packageIso.inv.base =
      (eqToHom hpoint.symm : ExtInstHom
        (packagePoint Q) (packagePoint (transportAlong P f))) := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (packageProjection U) _ packageIso.inv).symm
  refine ⟨packageIso, homBase, invBase, ?_, ?_⟩
  · rw [packageIso.hom.atomEquiv_eq, homBase]
    exact ExtInstHom.eqToHom_atomEquiv hpoint
  · rw [packageIso.inv.atomEquiv_eq, invBase]
    exact ExtInstHom.eqToHom_atomEquiv hpoint.symm

/-- The forward fiber isomorphism identifies the canonical and arbitrary lifts. -/
@[simp]
theorem transportAlong_liftUniqueUpToFiberIso_hom_fac {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (hpoint : packagePoint (transportAlong P f) = packagePoint Q)
    (phi : PackageTotalHom P Q)
    [(packageProjection U).IsStronglyCocartesian
      ((transportAlongHom P f).base.comp
        (eqToHom hpoint : ExtInstHom
          (packagePoint (transportAlong P f)) (packagePoint Q))) phi] :
    (transportAlongHom P f).comp
        (transportAlong_liftUniqueUpToFiberIso P Q f hpoint phi).iso.hom = phi := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongHom P f).base (transportAlongHom P f) :=
    transportAlongHom_isStronglyCocartesian P f
  unfold transportAlong_liftUniqueUpToFiberIso
  dsimp only
  simpa only using (CategoryTheory.Functor.IsStronglyCocartesian.fac
    (p := packageProjection U)
    (f := (transportAlongHom P f).base)
    (φ := transportAlongHom P f)
    (g := eqToHom hpoint)
    (f' := (transportAlongHom P f).base.comp
      (eqToHom hpoint : ExtInstHom
        (packagePoint (transportAlong P f)) (packagePoint Q)))
    (hf' := by rfl) (φ' := phi))

/-- The inverse fiber isomorphism recovers the canonical lift. -/
@[simp]
theorem transportAlong_liftUniqueUpToFiberIso_inv_fac {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (hpoint : packagePoint (transportAlong P f) = packagePoint Q)
    (phi : PackageTotalHom P Q)
    [(packageProjection U).IsStronglyCocartesian
      ((transportAlongHom P f).base.comp
        (eqToHom hpoint : ExtInstHom
          (packagePoint (transportAlong P f)) (packagePoint Q))) phi] :
    phi.comp (transportAlong_liftUniqueUpToFiberIso P Q f hpoint phi).iso.inv =
      transportAlongHom P f := by
  let packageIso := (transportAlong_liftUniqueUpToFiberIso P Q f hpoint phi).iso
  have homFac : (transportAlongHom P f).comp packageIso.hom = phi :=
    transportAlong_liftUniqueUpToFiberIso_hom_fac P Q f hpoint phi
  calc
    phi.comp packageIso.inv =
        ((transportAlongHom P f).comp packageIso.hom).comp packageIso.inv :=
      congrArg (fun k => k.comp packageIso.inv) homFac.symm
    _ = transportAlongHom P f := by
      change ((transportAlongHom P f) ≫ packageIso.hom) ≫ packageIso.inv =
        transportAlongHom P f
      simp

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
