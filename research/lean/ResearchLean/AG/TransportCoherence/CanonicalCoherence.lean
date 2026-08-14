import ResearchLean.AG.AtomFoundation.LiftUniqueness

/-!
# Canonical coherence of AAT package transport

This module begins G-106 at the accepted G-101 universal property.  It compares
the canonical lift of a composite exact doctrine morphism with the composite of
the two canonical lifts and proves the adjacent-composition equation by
uniqueness of strongly cocartesian factorization.

## Implementation notes

The comparison is constructed by `transportAlong_liftUniqueUpToFiberIso`; no
comparison or coherence certificate is accepted as input.  Direct equality of
the two transported package structures was rejected because G-106 needs the
fiber isomorphism supplied by the opcartesian universal property.
-/

namespace AAT.AG.TransportCoherence

universe u

open CategoryTheory
open AtomFoundation

/-- The composite of the two canonical package lifts. -/
def transportAlongCompHom {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E) :
    PackageTotalHom P (transportAlong (transportAlong P f) g) :=
  (transportAlongHom P f).comp (transportAlongHom (transportAlong P f) g)

/-- The two-step canonical lift is strongly cocartesian over the composite base map. -/
theorem transportAlongCompHom_isStronglyCocartesian {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E) :
    (packageProjection U).IsStronglyCocartesian
      (transportAlongCompHom P f g).base (transportAlongCompHom P f g) := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongHom P f).base (transportAlongHom P f) :=
    transportAlongHom_isStronglyCocartesian P f
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongHom (transportAlong P f) g).base
      (transportAlongHom (transportAlong P f) g) :=
    transportAlongHom_isStronglyCocartesian (transportAlong P f) g
  change (packageProjection U).IsStronglyCocartesian
    ((transportAlongHom P f).base.comp
      (transportAlongHom (transportAlong P f) g).base)
    ((transportAlongHom P f).comp
      (transportAlongHom (transportAlong P f) g))
  exact CategoryTheory.Functor.IsStronglyCocartesian.comp (packageProjection U)

/-- Direct and iterated transport have the same pointed doctrine. -/
theorem transportAlong_comp_point {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E) :
    packagePoint (transportAlong P (f.comp g)) =
      packagePoint (transportAlong (transportAlong P f) g) :=
  rfl

/-- The iterated lift lies over the direct composite base followed by fiber identity. -/
theorem transportAlongCompHom_base_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E) :
    (transportAlongHom P (f.comp g)).base.comp
        (eqToHom (transportAlong_comp_point P f g) : ExtInstHom
          (packagePoint (transportAlong P (f.comp g)))
          (packagePoint (transportAlong (transportAlong P f) g))) =
      (transportAlongCompHom P f g).base := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/--
The canonical fiber isomorphism from transport along a composite to iterated
transport.  Both legs lie over the equality-induced identity of the common
pointed doctrine.
-/
noncomputable def transportAlong_compFiberIso {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E) :
    PackageFiberInnerIso
      (transportAlong P (f.comp g))
      (transportAlong (transportAlong P f) g)
      (transportAlong_comp_point P f g) := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongCompHom P f g).base (transportAlongCompHom P f g) :=
    transportAlongCompHom_isStronglyCocartesian P f g
  letI : (packageProjection U).IsStronglyCocartesian
      ((transportAlongHom P (f.comp g)).base.comp
        (eqToHom (transportAlong_comp_point P f g) : ExtInstHom
          (packagePoint (transportAlong P (f.comp g)))
          (packagePoint (transportAlong (transportAlong P f) g))))
      (transportAlongCompHom P f g) := by
    rw [transportAlongCompHom_base_eq]
    exact transportAlongCompHom_isStronglyCocartesian P f g
  exact transportAlong_liftUniqueUpToFiberIso P
    (transportAlong (transportAlong P f) g) (f.comp g)
    (transportAlong_comp_point P f g)
    (transportAlongCompHom P f g)

/-- The comparison identifies the direct composite lift with the iterated lift. -/
theorem transportAlong_compFiberIso_hom_fac {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E) :
    (transportAlongHom P (f.comp g)).comp
        (transportAlong_compFiberIso P f g).iso.hom =
      transportAlongCompHom P f g := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongCompHom P f g).base (transportAlongCompHom P f g) :=
    transportAlongCompHom_isStronglyCocartesian P f g
  letI : (packageProjection U).IsStronglyCocartesian
      ((transportAlongHom P (f.comp g)).base.comp
        (eqToHom (transportAlong_comp_point P f g) : ExtInstHom
          (packagePoint (transportAlong P (f.comp g)))
          (packagePoint (transportAlong (transportAlong P f) g))))
      (transportAlongCompHom P f g) := by
    rw [transportAlongCompHom_base_eq]
    exact transportAlongCompHom_isStronglyCocartesian P f g
  exact transportAlong_liftUniqueUpToFiberIso_hom_fac P
    (transportAlong (transportAlong P f) g) (f.comp g)
    (transportAlong_comp_point P f g)
    (transportAlongCompHom P f g)

/-- The composite of three adjacent canonical package lifts. -/
def transportAlongTripleHom {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    PackageTotalHom P
      (transportAlong (transportAlong (transportAlong P f) g) h) :=
  (transportAlongCompHom P f g).comp
    (transportAlongHom (transportAlong (transportAlong P f) g) h)

/-- The three-step canonical lift is strongly cocartesian over its composite base map. -/
theorem transportAlongTripleHom_isStronglyCocartesian {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    (packageProjection U).IsStronglyCocartesian
      (transportAlongTripleHom P f g h).base
      (transportAlongTripleHom P f g h) := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongCompHom P f g).base (transportAlongCompHom P f g) :=
    transportAlongCompHom_isStronglyCocartesian P f g
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongHom (transportAlong (transportAlong P f) g) h).base
      (transportAlongHom (transportAlong (transportAlong P f) g) h) :=
    transportAlongHom_isStronglyCocartesian
      (transportAlong (transportAlong P f) g) h
  change (packageProjection U).IsStronglyCocartesian
    ((transportAlongCompHom P f g).base.comp
      (transportAlongHom (transportAlong (transportAlong P f) g) h).base)
    ((transportAlongCompHom P f g).comp
      (transportAlongHom (transportAlong (transportAlong P f) g) h))
  exact CategoryTheory.Functor.IsStronglyCocartesian.comp (packageProjection U)

/-- Direct and fully iterated three-step transport have the same pointed doctrine. -/
theorem transportAlong_triple_point {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    packagePoint (transportAlong P (f.comp (g.comp h))) =
      packagePoint
        (transportAlong (transportAlong (transportAlong P f) g) h) :=
  rfl

/-- The fully iterated lift has the base of the right-associated direct composite. -/
theorem transportAlongTripleHom_base_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    (transportAlongHom P (f.comp (g.comp h))).base.comp
        (eqToHom (transportAlong_triple_point P f g h) : ExtInstHom
          (packagePoint (transportAlong P (f.comp (g.comp h))))
          (packagePoint
            (transportAlong (transportAlong (transportAlong P f) g) h))) =
      (transportAlongTripleHom P f g h).base := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- The universal comparison from direct three-step transport to full iteration. -/
noncomputable def transportAlong_tripleFiberIso {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    PackageFiberInnerIso
      (transportAlong P (f.comp (g.comp h)))
      (transportAlong (transportAlong (transportAlong P f) g) h)
      (transportAlong_triple_point P f g h) := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongTripleHom P f g h).base
      (transportAlongTripleHom P f g h) :=
    transportAlongTripleHom_isStronglyCocartesian P f g h
  letI : (packageProjection U).IsStronglyCocartesian
      ((transportAlongHom P (f.comp (g.comp h))).base.comp
        (eqToHom (transportAlong_triple_point P f g h) : ExtInstHom
          (packagePoint (transportAlong P (f.comp (g.comp h))))
          (packagePoint
            (transportAlong (transportAlong (transportAlong P f) g) h))))
      (transportAlongTripleHom P f g h) := by
    rw [transportAlongTripleHom_base_eq]
    exact transportAlongTripleHom_isStronglyCocartesian P f g h
  exact transportAlong_liftUniqueUpToFiberIso P
    (transportAlong (transportAlong (transportAlong P f) g) h)
    (f.comp (g.comp h)) (transportAlong_triple_point P f g h)
    (transportAlongTripleHom P f g h)

/-- The direct three-step lift followed by its comparison is the fully iterated lift. -/
theorem transportAlong_tripleFiberIso_hom_fac {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    (transportAlongHom P (f.comp (g.comp h))).comp
        (transportAlong_tripleFiberIso P f g h).iso.hom =
      transportAlongTripleHom P f g h := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongTripleHom P f g h).base
      (transportAlongTripleHom P f g h) :=
    transportAlongTripleHom_isStronglyCocartesian P f g h
  letI : (packageProjection U).IsStronglyCocartesian
      ((transportAlongHom P (f.comp (g.comp h))).base.comp
        (eqToHom (transportAlong_triple_point P f g h) : ExtInstHom
          (packagePoint (transportAlong P (f.comp (g.comp h))))
          (packagePoint
            (transportAlong (transportAlong (transportAlong P f) g) h))))
      (transportAlongTripleHom P f g h) := by
    rw [transportAlongTripleHom_base_eq]
    exact transportAlongTripleHom_isStronglyCocartesian P f g h
  exact transportAlong_liftUniqueUpToFiberIso_hom_fac P
    (transportAlong (transportAlong (transportAlong P f) g) h)
    (f.comp (g.comp h)) (transportAlong_triple_point P f g h)
    (transportAlongTripleHom P f g h)

/--
The adjacent binary comparisons from right-associated direct transport to full
three-step iteration.
-/
noncomputable def transportAlongAdjacentCompHom {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    PackageTotalHom
      (transportAlong P (f.comp (g.comp h)))
      (transportAlong (transportAlong (transportAlong P f) g) h) :=
  (transportAlong_compFiberIso P f (g.comp h)).iso.hom.comp
    (transportAlong_compFiberIso (transportAlong P f) g h).iso.hom

/-- The adjacent binary comparison lies over identity in the endpoint fiber. -/
theorem transportAlongAdjacentCompHom_base {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    (transportAlongAdjacentCompHom P f g h).base =
      (eqToHom (transportAlong_triple_point P f g h) : ExtInstHom
        (packagePoint (transportAlong P (f.comp (g.comp h))))
        (packagePoint
          (transportAlong (transportAlong (transportAlong P f) g) h))) := by
  change
    (transportAlong_compFiberIso P f (g.comp h)).iso.hom.base.comp
        (transportAlong_compFiberIso (transportAlong P f) g h).iso.hom.base = _
  rw [(transportAlong_compFiberIso P f (g.comp h)).hom_base_eq]
  rw [(transportAlong_compFiberIso (transportAlong P f) g h).hom_base_eq]
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- The direct lift followed by the two adjacent comparisons is the triple lift. -/
theorem transportAlongAdjacentCompHom_fac {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    (transportAlongHom P (f.comp (g.comp h))).comp
        (transportAlongAdjacentCompHom P f g h) =
      transportAlongTripleHom P f g h := by
  change
    (transportAlongHom P (f.comp (g.comp h))) ≫
        ((transportAlong_compFiberIso P f (g.comp h)).iso.hom ≫
          (transportAlong_compFiberIso (transportAlong P f) g h).iso.hom) = _
  rw [← Category.assoc]
  change
    ((transportAlongHom P (f.comp (g.comp h))).comp
        (transportAlong_compFiberIso P f (g.comp h)).iso.hom).comp
      (transportAlong_compFiberIso (transportAlong P f) g h).iso.hom = _
  rw [transportAlong_compFiberIso_hom_fac]
  change
    (transportAlongCompHom P f (g.comp h)) ≫
        (transportAlong_compFiberIso (transportAlong P f) g h).iso.hom = _
  change
    ((transportAlongHom P f) ≫
        (transportAlongHom (transportAlong P f) (g.comp h))) ≫
        (transportAlong_compFiberIso (transportAlong P f) g h).iso.hom = _
  rw [Category.assoc]
  change
    (transportAlongHom P f).comp
      ((transportAlongHom (transportAlong P f) (g.comp h)).comp
        (transportAlong_compFiberIso (transportAlong P f) g h).iso.hom) = _
  rw [transportAlong_compFiberIso_hom_fac]
  exact (@Category.assoc
    (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
    P (transportAlong P f) (transportAlong (transportAlong P f) g)
    (transportAlong (transportAlong (transportAlong P f) g) h)
    (transportAlongHom P f)
    (transportAlongHom (transportAlong P f) g)
    (transportAlongHom (transportAlong (transportAlong P f) g) h)).symm

/--
Adjacent canonical transport comparisons satisfy the three-step coherence
equation.  The equality is forced by the G-101 opcartesian universal property.
-/
theorem transportAlong_comp_coherence {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    transportAlongAdjacentCompHom P f g h =
      (transportAlong_tripleFiberIso P f g h).iso.hom := by
  letI : (packageProjection U).IsStronglyCocartesian
      (transportAlongHom P (f.comp (g.comp h))).base
      (transportAlongHom P (f.comp (g.comp h))) :=
    transportAlongHom_isStronglyCocartesian P (f.comp (g.comp h))
  letI : (packageProjection U).IsHomLift
      (eqToHom (transportAlong_triple_point P f g h) : ExtInstHom
        (packagePoint (transportAlong P (f.comp (g.comp h))))
        (packagePoint
          (transportAlong (transportAlong (transportAlong P f) g) h)))
      (transportAlongAdjacentCompHom P f g h) := by
    rw [← transportAlongAdjacentCompHom_base]
    change (packageProjection U).IsHomLift
      ((packageProjection U).map (transportAlongAdjacentCompHom P f g h))
      (transportAlongAdjacentCompHom P f g h)
    infer_instance
  letI : (packageProjection U).IsHomLift
      (eqToHom (transportAlong_triple_point P f g h) : ExtInstHom
        (packagePoint (transportAlong P (f.comp (g.comp h))))
        (packagePoint
          (transportAlong (transportAlong (transportAlong P f) g) h)))
      (transportAlong_tripleFiberIso P f g h).iso.hom := by
    rw [← (transportAlong_tripleFiberIso P f g h).hom_base_eq]
    change (packageProjection U).IsHomLift
      ((packageProjection U).map
        (transportAlong_tripleFiberIso P f g h).iso.hom)
      (transportAlong_tripleFiberIso P f g h).iso.hom
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (transportAlongHom P (f.comp (g.comp h))).base
    (transportAlongHom P (f.comp (g.comp h)))
    (eqToHom (transportAlong_triple_point P f g h))
  exact (transportAlongAdjacentCompHom_fac P f g h).trans
    (transportAlong_tripleFiberIso_hom_fac P f g h).symm

end AAT.AG.TransportCoherence

#assert_standard_axioms_only AAT.AG.TransportCoherence
