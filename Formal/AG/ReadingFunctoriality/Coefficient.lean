import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.ReadingFunctoriality.Coverage
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.Derived.Intersection
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.RingHom.Flat

/-!
# Coefficient-change functoriality

This module owns direct closed-equational reuse and flat coefficient change
for raw systems, standard schemes, ideal geometry, Tor, linear Čech
cohomology, and actual sheaf cohomology fixed by Part 4 SD2 and SD6–SD8.

## Implementation notes (SD6 position)

The declarations in `FlatCoefficientChange` are the coefficient-extension
foundation required by SD6, AC27, and the coefficient-coherence part of AC30.
The primitive data are exactly a ring homomorphism and its flatness proof.
Site-dependent `HasSheafCompose` proofs remain explicit premises of the
scheme-level route; sheaves, sections, schemes, and comparison isomorphisms
are not stored in the change data.

The coefficient functor uses the common-universe presentation fixed by SD6:
`liftedHom` conjugates the coefficient map by `ULift.ringEquiv`, and
`coefficientExtension` applies Mathlib’s `Under.pushout` directly. A
cross-universe category equivalence is not introduced because it would add a
repackaging layer outside the fixed statement. Finite-limit preservation
comes from the supplied flatness proof, while sheafification preservation
comes independently from the pushout adjunction.
-/

namespace AAT.AG

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v w x

noncomputable section

/-- A coefficient change whose underlying ring homomorphism is flat. -/
structure FlatCoefficientChange
    (k : Type v) [CommRing k]
    (k' : Type w) [CommRing k'] where
  /-- The coefficient-ring homomorphism fixed by SD6. -/
  hom : k →+* k'
  /-- The SD6 flatness premise, consumed by finite-limit preservation. -/
  flat : hom.Flat

namespace FlatCoefficientChange

/-- The identity coefficient change is flat. -/
def refl (k : Type v) [CommRing k] :
    FlatCoefficientChange k k where
  hom := RingHom.id k
  flat := RingHom.Flat.id k

/-- Flat coefficient changes compose. -/
def comp
    {k : Type v} {k' : Type w} {k'' : Type x}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'') :
    FlatCoefficientChange k k'' where
  hom := g.hom.comp f.hom
  flat := f.flat.comp g.flat

/-- The universe-lifted coefficient homomorphism used by the under-category
pushout functor. -/
noncomputable def liftedHom
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    ULift.{max u v, v} k →+* ULift.{max u v, v} k' :=
  ULift.ringEquiv.symm.toRingHom.comp
    (f.hom.comp ULift.ringEquiv.toRingHom)

/-- Internal bridge transporting the supplied flatness proof across the
universe-lift equivalences. -/
private theorem liftedHom_flat
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    f.liftedHom.Flat := by
  exact
    ((RingHom.Flat.of_bijective
        (ULift.ringEquiv (R := k)).bijective).comp f.flat).comp
      (RingHom.Flat.of_bijective
        (ULift.ringEquiv (R := k')).symm.bijective)

/-- Extension of coefficients on the category of AAT commutative algebras. -/
noncomputable def coefficientExtension
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    LawAlgebra.AATCommAlgCat.{u, v} k ⥤
      LawAlgebra.AATCommAlgCat.{u, v} k' :=
  Under.pushout (CommRingCat.ofHom f.liftedHom)

/-- Flat extension of coefficients preserves finite limits. -/
noncomputable instance coefficientExtension_preservesFiniteLimits
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    PreservesFiniteLimits (coefficientExtension f) :=
  CommRingCat.Under.preservesFiniteLimits_of_flat
    (CommRingCat.ofHom f.liftedHom) (liftedHom_flat f)

/-- Flat extension of coefficients preserves sheafification. -/
noncomputable instance coefficientExtension_preservesSheafification
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A)
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    S.topology.PreservesSheafification
      (coefficientExtension f :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k') :=
  Sheaf.preservesSheafification_of_adjunction S.topology
    (Under.mapPushoutAdj (CommRingCat.ofHom f.liftedHom))

/-- Extension along the identity coefficient change is naturally isomorphic
to the identity functor. -/
noncomputable def coefficientExtensionReflIso
    (k : Type v) [CommRing k] :
    (coefficientExtension (refl k) :
      LawAlgebra.AATCommAlgCat.{u, v} k ⥤
        LawAlgebra.AATCommAlgCat.{u, v} k) ≅ 𝟭 _ := by
  simpa only [coefficientExtension, liftedHom, refl] using
    (Under.pushoutId :
      Under.pushout
          (𝟙 (CommRingCat.of (ULift.{max u v, v} k))) ≅
        𝟭 (LawAlgebra.AATCommAlgCat.{u, v} k))

/-- Successive coefficient extensions agree with extension along the
composite coefficient change. -/
noncomputable def coefficientExtensionCompIso
    {k k' k'' : Type v}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'') :
    (coefficientExtension (f.comp g) :
      LawAlgebra.AATCommAlgCat.{u, v} k ⥤
        LawAlgebra.AATCommAlgCat.{u, v} k'') ≅
      (coefficientExtension f :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k') ⋙
      (coefficientExtension g :
        LawAlgebra.AATCommAlgCat.{u, v} k' ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'') := by
  simpa only [coefficientExtension, liftedHom, comp] using
    Under.pushoutComp
      (CommRingCat.ofHom f.liftedHom)
      (CommRingCat.ofHom g.liftedHom)

/-- Identity coefficient extension preserves sheaves on every site. -/
noncomputable instance coefficientExtension_hasSheafCompose_refl
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A)
    (k : Type v) [CommRing k] :
    S.topology.HasSheafCompose
      (coefficientExtension (refl k) :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k) where
  isSheaf P hP := by
    apply
      (Presheaf.isSheaf_of_iso_iff
        (Functor.isoWhiskerLeft P
          (coefficientExtensionReflIso k :
            (coefficientExtension (refl k) :
              LawAlgebra.AATCommAlgCat.{u, v} k ⥤
                LawAlgebra.AATCommAlgCat.{u, v} k) ≅ 𝟭 _))).2
    simpa using hP

/-- The composite of two sheaf-preserving coefficient extensions preserves
sheaves, compatibly with the composite coefficient change. -/
theorem coefficientExtension_hasSheafCompose_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {k k' k'' : Type v}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'')
    (hf : S.topology.HasSheafCompose
      (coefficientExtension f :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'))
    (hg : S.topology.HasSheafCompose
      (coefficientExtension g :
        LawAlgebra.AATCommAlgCat.{u, v} k' ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'')) :
    S.topology.HasSheafCompose
      (coefficientExtension (f.comp g) :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'') := by
  refine ⟨fun P hP => ?_⟩
  apply
    (Presheaf.isSheaf_of_iso_iff
      (Functor.isoWhiskerLeft P
        (coefficientExtensionCompIso f g :
          (coefficientExtension (f.comp g) :
            LawAlgebra.AATCommAlgCat.{u, v} k ⥤
              LawAlgebra.AATCommAlgCat.{u, v} k'') ≅
            (coefficientExtension f :
              LawAlgebra.AATCommAlgCat.{u, v} k ⥤
                LawAlgebra.AATCommAlgCat.{u, v} k') ⋙
            (coefficientExtension g :
              LawAlgebra.AATCommAlgCat.{u, v} k' ⥤
                LawAlgebra.AATCommAlgCat.{u, v} k'')))).2
  have hPf : Presheaf.IsSheaf S.topology
      (P ⋙ (coefficientExtension f :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k')) :=
    hf.isSheaf P hP
  exact hg.isSheaf
    (P ⋙ (coefficientExtension f :
      LawAlgebra.AATCommAlgCat.{u, v} k ⥤
        LawAlgebra.AATCommAlgCat.{u, v} k')) hPf

end FlatCoefficientChange

end

end AAT.AG
