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
import Mathlib.Logic.Function.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.RingHom.Flat

/-!
# Coefficient-change functoriality

This module owns direct closed-equational reuse and the flat coefficient-change
foundation for raw systems, ideal geometry, Tor, linear Čech cohomology, and
actual sheaf cohomology.  The standard-scheme
pullback built from this foundation lives in `StandardSchemeCoefficient`.

## Implementation notes

The declarations in `FlatCoefficientChange` are the coefficient-extension
foundation for raw systems, scheme change, and coefficient coherence.  The
primitive data are exactly a ring homomorphism and its flatness proof.
Site-dependent `HasSheafCompose` proofs remain explicit premises of the
scheme-level route; sheaves, sections, schemes, and comparison isomorphisms
are not stored in the change data.

The coefficient functor uses a common-universe presentation: `liftedHom`
conjugates the coefficient map by `ULift.ringEquiv`, and
`coefficientExtension` applies Mathlib’s `Under.pushout` directly. A
cross-universe category equivalence is not introduced because it would add a
repackaging layer outside the fixed statement. Finite-limit preservation
comes from the supplied flatness proof, while sheafification preservation
comes independently from the pushout adjunction.
-/

namespace AAT.AG

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

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

namespace LawAlgebra

/-- SD6 / AC28 coefficient change of a structural relation family.

Implementation notes: relation indices and coordinates are unchanged; only
polynomial coefficients are mapped. This keeps the primitive change data at
the ring homomorphism and avoids introducing a second relation witness. -/
noncomputable def StructuralRelationFamily.baseChange
    {A : ArchitectureObject U} {W : Site.ArchitectureContext A}
    {k k' : Type v} [CommRing k] [CommRing k']
    {F : CoordinateFamily W}
    (R : StructuralRelationFamily F k)
    (f : k →+* k') :
    StructuralRelationFamily F k' where
  Relation := R.Relation
  polynomial r := MvPolynomial.map f (R.polynomial r)

namespace StructuralRelationFamily

private theorem baseChange_JStruct
    {A : ArchitectureObject U} {W : Site.ArchitectureContext A}
    {k k' : Type v} [CommRing k] [CommRing k']
    {F : CoordinateFamily W}
    (R : StructuralRelationFamily F k)
    (f : k →+* k') :
    (R.baseChange f).JStruct =
      Ideal.map (MvPolynomial.map f) R.JStruct := by
  simp only [JStruct, RelStruct, StructuralRelationFamily.baseChange,
    Ideal.map_span]
  congr 1
  ext p
  simp

private theorem baseChange_id
    {A : ArchitectureObject U} {W : Site.ArchitectureContext A}
    {k : Type v} [CommRing k] {F : CoordinateFamily W}
    (R : StructuralRelationFamily F k) :
    R.baseChange (RingHom.id k) = R := by
  cases R
  simp [StructuralRelationFamily.baseChange, MvPolynomial.map_id]

private theorem baseChange_comp
    {A : ArchitectureObject U} {W : Site.ArchitectureContext A}
    {k k' k'' : Type v} [CommRing k] [CommRing k'] [CommRing k'']
    {F : CoordinateFamily W}
    (R : StructuralRelationFamily F k)
    (f : k →+* k') (g : k' →+* k'') :
    R.baseChange (g.comp f) = (R.baseChange f).baseChange g := by
  cases R
  simp [StructuralRelationFamily.baseChange, MvPolynomial.map_map]

end StructuralRelationFamily

namespace RestrictionStableStructuralRelations

/-- SD6 / AC28 transports restriction-stability by mapping every selected
variable-image polynomial across the coefficient homomorphism. -/
noncomputable def baseChange
    {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k k' : Type v} [CommRing k] [CommRing k']
    {sourceRelations : StructuralRelationFamily sourceFamily k}
    {targetRelations : StructuralRelationFamily targetFamily k}
    {g : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations
      sourceRelations targetRelations g)
    (f : k →+* k') :
    RestrictionStableStructuralRelations
      (sourceRelations.baseChange f)
      (targetRelations.baseChange f) g := by
  let rho : TypedCoordinateRestriction sourceFamily targetFamily k' g :=
    { variableImage := fun c =>
        MvPolynomial.map f (h.restriction.variableImage c) }
  refine { restriction := rho, maps_JStruct := ?_ }
  intro p hp
  rw [StructuralRelationFamily.baseChange_JStruct] at hp ⊢
  have hcomm :
      rho.polynomialMap.comp (MvPolynomial.map f) =
        (MvPolynomial.map f).comp h.restriction.polynomialMap := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rho, TypedCoordinateRestriction.polynomialMap]
    · intro c
      simp [rho, TypedCoordinateRestriction.polynomialMap]
  have hold :
      Ideal.map h.restriction.polynomialMap targetRelations.JStruct ≤
        sourceRelations.JStruct := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    exact h.maps_JStruct q hq
  have htotal :
      Ideal.map rho.polynomialMap
          (Ideal.map (MvPolynomial.map f) targetRelations.JStruct) ≤
        Ideal.map (MvPolynomial.map f) sourceRelations.JStruct := by
    rw [Ideal.map_map, hcomm, ← Ideal.map_map]
    exact Ideal.map_mono hold
  exact htotal (Ideal.mem_map_of_mem rho.polynomialMap hp)

private theorem baseChange_polynomialMap_map
    {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k k' : Type v} [CommRing k] [CommRing k']
    {sourceRelations : StructuralRelationFamily sourceFamily k}
    {targetRelations : StructuralRelationFamily targetFamily k}
    {g : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations
      sourceRelations targetRelations g)
    (f : k →+* k')
    (p : FreeTypedCommAlg targetFamily k) :
    (h.baseChange f).restriction.polynomialMap
        (MvPolynomial.map f p) =
      MvPolynomial.map f (h.restriction.polynomialMap p) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.map f p) = _
  rw [MvPolynomial.eval₂Hom_map_hom]
  symm
  simpa [baseChange, TypedCoordinateRestriction.polynomialMap,
    Function.comp_def] using
    (MvPolynomial.map_eval₂Hom MvPolynomial.C
      h.restriction.variableImage (MvPolynomial.map f) p)

private theorem heq_of_relations_of_variableImage
    {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k : Type v} [CommRing k]
    {sourceRelations sourceRelations' :
      StructuralRelationFamily sourceFamily k}
    {targetRelations targetRelations' :
      StructuralRelationFamily targetFamily k}
    {g : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations
      sourceRelations targetRelations g)
    (h' : RestrictionStableStructuralRelations
      sourceRelations' targetRelations' g)
    (hsource : sourceRelations = sourceRelations')
    (htarget : targetRelations = targetRelations')
    (hvariable : h.restriction.variableImage =
      h'.restriction.variableImage) :
    HEq h h' := by
  cases hsource
  cases htarget
  cases h with
  | mk hrestriction hmaps =>
      cases h' with
      | mk hrestriction' hmaps' =>
          cases hrestriction
          cases hrestriction'
          cases hvariable
          rfl

private theorem baseChange_id
    {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k : Type v} [CommRing k]
    {sourceRelations : StructuralRelationFamily sourceFamily k}
    {targetRelations : StructuralRelationFamily targetFamily k}
    {g : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations
      sourceRelations targetRelations g) :
    HEq (h.baseChange (RingHom.id k)) h := by
  apply heq_of_relations_of_variableImage
    (h.baseChange (RingHom.id k)) h
    (StructuralRelationFamily.baseChange_id sourceRelations)
    (StructuralRelationFamily.baseChange_id targetRelations)
  funext c
  exact MvPolynomial.map_id (h.restriction.variableImage c)

private theorem baseChange_comp
    {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k k' k'' : Type v} [CommRing k] [CommRing k'] [CommRing k'']
    {sourceRelations : StructuralRelationFamily sourceFamily k}
    {targetRelations : StructuralRelationFamily targetFamily k}
    {g : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations
      sourceRelations targetRelations g)
    (f : k →+* k') (f' : k' →+* k'') :
    HEq (h.baseChange (f'.comp f))
      ((h.baseChange f).baseChange f') := by
  apply heq_of_relations_of_variableImage
    (h.baseChange (f'.comp f)) ((h.baseChange f).baseChange f')
    (StructuralRelationFamily.baseChange_comp sourceRelations f f')
    (StructuralRelationFamily.baseChange_comp targetRelations f f')
  funext c
  exact (MvPolynomial.map_map f f'
    (h.restriction.variableImage c)).symm

end RestrictionStableStructuralRelations

namespace RawAmbientRestrictionSystem

/-- SD6 / AC28 changes the coefficient ring of every structural relation and
restriction while leaving the selected coordinate families unchanged. -/
noncomputable def baseChange
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') :
    RawAmbientRestrictionSystem S k' where
  coordFamily := raw.coordFamily
  relationFamily W := (raw.relationFamily W).baseChange f
  restrictionStable g := (raw.restrictionStable g).baseChange f
  identity_polynomialMap X := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RestrictionStableStructuralRelations.baseChange,
        TypedCoordinateRestriction.polynomialMap]
    · intro c
      have h := RingHom.congr_fun (raw.identity_polynomialMap X)
        (MvPolynomial.X c)
      simp only [RestrictionStableStructuralRelations.baseChange,
        TypedCoordinateRestriction.polynomialMap,
        MvPolynomial.eval₂Hom_X', RingHom.id_apply]
      change MvPolynomial.map f
          ((raw.restrictionStable (𝟙 X)).restriction.variableImage c) =
        MvPolynomial.X c
      rw [show
        (raw.restrictionStable (𝟙 X)).restriction.variableImage c =
          MvPolynomial.X c by
            simpa [TypedCoordinateRestriction.polynomialMap] using h]
      simp
  composition_polynomialMap f' g' := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RestrictionStableStructuralRelations.baseChange,
        TypedCoordinateRestriction.polynomialMap]
    · intro c
      have h := RingHom.congr_fun
        (raw.composition_polynomialMap f' g') (MvPolynomial.X c)
      simp only [RestrictionStableStructuralRelations.baseChange,
        TypedCoordinateRestriction.polynomialMap,
        MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
      change MvPolynomial.map f
          ((raw.restrictionStable (f' ≫ g')).restriction.variableImage c) =
        ((raw.restrictionStable f').baseChange f).restriction.polynomialMap
            (MvPolynomial.map f
              ((raw.restrictionStable g').restriction.variableImage c))
      rw [RestrictionStableStructuralRelations.baseChange_polynomialMap_map]
      congr 1
      simpa [TypedCoordinateRestriction.polynomialMap] using h

private noncomputable def quotientBaseChangeMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') (W : S.category) :
    raw.rawAlgebra W →+* (raw.baseChange f).rawAlgebra W :=
  Ideal.quotientMap
    ((raw.baseChange f).relationFamily W).JStruct
    (MvPolynomial.map f) (by
      intro p hp
      rw [Ideal.mem_comap]
      change MvPolynomial.map f p ∈
        ((raw.relationFamily W).baseChange f).JStruct
      rw [StructuralRelationFamily.baseChange_JStruct]
      exact Ideal.mem_map_of_mem (MvPolynomial.map f) hp)

@[simp] private theorem quotientBaseChangeMap_mk
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') (W : S.category)
    (p : FreeTypedCommAlg (raw.coordFamily W) k) :
    quotientBaseChangeMap raw f W
        ((raw.relationFamily W).quotientMap p) =
      ((raw.baseChange f).relationFamily W).quotientMap
        (MvPolynomial.map f p) := by
  rfl

private theorem quotientBaseChangeMap_natural
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') {X Y : S.category} (g : X ⟶ Y) :
    (quotientBaseChangeMap raw f X).comp
        (raw.restrictionStable g).quotientDesc =
      ((raw.baseChange f).restrictionStable g).quotientDesc.comp
        (quotientBaseChangeMap raw f Y) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change ((raw.baseChange f).relationFamily X).quotientMap
      (MvPolynomial.map f
        ((raw.restrictionStable g).restriction.polynomialMap p)) =
    ((raw.baseChange f).relationFamily X).quotientMap
      (((raw.restrictionStable g).baseChange f).restriction.polynomialMap
        (MvPolynomial.map f p))
  rw [RestrictionStableStructuralRelations.baseChange_polynomialMap_map]
  rfl

private noncomputable def quotientBaseChangeIsPushout
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : FlatCoefficientChange k k') (W : S.category) :
    IsPushout
      (raw.toPresheaf.obj (op W)).hom
      (CommRingCat.ofHom f.liftedHom)
      (CommRingCat.ofHom (quotientBaseChangeMap raw f.hom W))
      ((raw.baseChange f.hom).toPresheaf.obj (op W)).hom := by
  let oldQuotient := (raw.relationFamily W).quotientMap
  let newQuotient := ((raw.baseChange f.hom).relationFamily W).quotientMap
  let coefficientMap := fun (t : CommRingCat) (right :
      CommRingCat.of (ULift.{max u v, v} k') ⟶ t) =>
    right.hom.comp ULift.ringEquiv.symm.toRingHom
  refine
    { w := ?_
      isColimit' := ⟨PushoutCocone.isColimitAux'
        (PushoutCocone.mk _ _ ?_) ?_⟩ }
  · ext x
    rcases x with ⟨x⟩
    change newQuotient (MvPolynomial.map f.hom (MvPolynomial.C x)) =
      newQuotient (MvPolynomial.C (f.hom x))
    rw [MvPolynomial.map_C]
  · ext x
    rcases x with ⟨x⟩
    change newQuotient (MvPolynomial.map f.hom (MvPolynomial.C x)) =
      newQuotient (MvPolynomial.C (f.hom x))
    rw [MvPolynomial.map_C]
  · intro s
    let coeff : k' →+* s.pt := coefficientMap s.pt s.inr
    let variableValues : (raw.coordFamily W).CoordX → s.pt := fun c =>
      s.inl.hom (oldQuotient (MvPolynomial.X c))
    let eval : FreeTypedCommAlg (raw.coordFamily W) k' →+* s.pt :=
      MvPolynomial.eval₂Hom coeff variableValues
    have hcoeff (a : k) :
        coeff (f.hom a) = s.inl.hom (oldQuotient (MvPolynomial.C a)) := by
      have hs := congrArg
        (fun h : CommRingCat.of (ULift.{max u v, v} k) ⟶ s.pt =>
          h.hom (ULift.up a)) s.condition
      simpa [coeff, coefficientMap, oldQuotient,
        FlatCoefficientChange.liftedHom] using hs.symm
    have hevalMap :
        eval.comp (MvPolynomial.map f.hom) =
          s.inl.hom.comp oldQuotient := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simpa [eval] using hcoeff a
      · intro c
        simp [eval, variableValues]
        rfl
    have hevalJ :
        ((raw.baseChange f.hom).relationFamily W).JStruct ≤
          RingHom.ker eval := by
      rw [show (raw.baseChange f.hom).relationFamily W =
        (raw.relationFamily W).baseChange f.hom from rfl,
        StructuralRelationFamily.baseChange_JStruct]
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker]
      calc
        eval (MvPolynomial.map f.hom p) =
            s.inl.hom (oldQuotient p) := RingHom.congr_fun hevalMap p
        _ = 0 := by
          rw [show oldQuotient p = 0 by
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hp]
          simp
    let descRing :
        (raw.baseChange f.hom).rawAlgebra W →+* s.pt :=
      Ideal.Quotient.lift
        ((raw.baseChange f.hom).relationFamily W).JStruct eval hevalJ
    let desc :
        CommRingCat.of ((raw.baseChange f.hom).rawAlgebra W) ⟶ s.pt :=
      CommRingCat.ofHom descRing
    have hdesc (p : FreeTypedCommAlg (raw.coordFamily W) k') :
        descRing (newQuotient p) = eval p := by
      change (Ideal.Quotient.lift
        ((raw.baseChange f.hom).relationFamily W).JStruct eval hevalJ)
          (Ideal.Quotient.mk
            ((raw.baseChange f.hom).relationFamily W).JStruct p) = eval p
      exact Ideal.Quotient.lift_mk
        ((raw.baseChange f.hom).relationFamily W).JStruct eval hevalJ
    refine ⟨desc, ?_, ?_, ?_⟩
    · ext x
      refine Quotient.inductionOn' x ?_
      intro p
      change descRing (newQuotient (MvPolynomial.map f.hom p)) =
        s.inl.hom (oldQuotient p)
      exact RingHom.congr_fun hevalMap p
    · ext x
      rcases x with ⟨x⟩
      change descRing (newQuotient (MvPolynomial.C x)) =
        s.inr.hom (ULift.up x)
      rw [hdesc]
      calc
        eval (MvPolynomial.C x) = coeff x := by
          simp [eval]
        _ = s.inr.hom (ULift.up x) := rfl
    · intro m hmLeft hmRight
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro a
        have hm := congrArg
          (fun h : CommRingCat.of (ULift.{max u v, v} k') ⟶ s.pt =>
            h.hom (ULift.up a)) hmRight
        change m.hom (newQuotient (MvPolynomial.C a)) =
          descRing (newQuotient (MvPolynomial.C a))
        rw [hdesc]
        have hm' : m.hom (newQuotient (MvPolynomial.C a)) =
            s.inr.hom (ULift.up a) := by
          simpa only [CommRingCat.comp_apply] using hm
        calc
          m.hom (newQuotient (MvPolynomial.C a)) =
              s.inr.hom (ULift.up a) := hm'
          _ = coeff a := rfl
          _ = eval (MvPolynomial.C a) := by
            symm
            simp [eval]
      · intro c
        have hm := congrArg
          (fun h : CommRingCat.of (raw.rawAlgebra W) ⟶ s.pt =>
            h.hom (oldQuotient (MvPolynomial.X c))) hmLeft
        change m.hom (newQuotient (MvPolynomial.X c)) =
          descRing (newQuotient (MvPolynomial.X c))
        rw [hdesc]
        have hq : quotientBaseChangeMap raw f.hom W
              (oldQuotient (MvPolynomial.X c)) =
            newQuotient (MvPolynomial.X c) := by
          rw [quotientBaseChangeMap_mk, MvPolynomial.map_X]
        have hm' : m.hom
              (quotientBaseChangeMap raw f.hom W
                (oldQuotient (MvPolynomial.X c))) =
            s.inl.hom (oldQuotient (MvPolynomial.X c)) := by
          simpa only [CommRingCat.comp_apply] using hm
        calc
          m.hom (newQuotient (MvPolynomial.X c)) =
              m.hom (quotientBaseChangeMap raw f.hom W
                (oldQuotient (MvPolynomial.X c))) := congrArg m.hom hq.symm
          _ = s.inl.hom (oldQuotient (MvPolynomial.X c)) := hm'
          _ = variableValues c := rfl
          _ = eval (MvPolynomial.X c) := by
            symm
            simp [eval]

/-- SD6 / AC28 coefficient change preserves the selected coordinate family. -/
@[simp] theorem baseChange_coordFamily
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') :
    (raw.baseChange f).coordFamily = raw.coordFamily :=
  rfl

/-- SD6 / AC28 characterizes the changed structural relations objectwise. -/
@[simp] theorem baseChange_relationFamily
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') (W : S.category) :
    (raw.baseChange f).relationFamily W =
      (raw.relationFamily W).baseChange f :=
  rfl

/-- SD6 / AC28 characterizes the transported restriction-stability proof. -/
theorem baseChange_restrictionStable
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k')
    {W V : S.category} (g : W ⟶ V) :
    HEq ((raw.baseChange f).restrictionStable g)
      ((raw.restrictionStable g).baseChange f) :=
  HEq.rfl

/-- SD6 / AC28 raw coefficient change along the identity is the original
restriction system. -/
@[simp] theorem baseChange_id
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k) :
    raw.baseChange (RingHom.id k) = raw := by
  let hrelation :
      (raw.baseChange (RingHom.id k)).relationFamily = raw.relationFamily := by
    funext W
    exact StructuralRelationFamily.baseChange_id (raw.relationFamily W)
  refine RawAmbientRestrictionSystem.ext
    (raw.baseChange (RingHom.id k)) raw rfl (heq_of_eq hrelation) ?_
  apply Function.hfunext rfl
  intro X X' hX
  cases hX
  apply Function.hfunext rfl
  intro Y Y' hY
  cases hY
  apply Function.hfunext rfl
  intro g g' hg
  cases hg
  exact RestrictionStableStructuralRelations.baseChange_id
    (raw.restrictionStable g)

/-- SD6 / AC28 successive raw coefficient changes agree with coefficient
change along the composite ring homomorphism. -/
@[simp] theorem baseChange_comp
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' k'' : Type v} [CommRing k] [CommRing k'] [CommRing k'']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') (g : k' →+* k'') :
    raw.baseChange (g.comp f) =
      (raw.baseChange f).baseChange g := by
  let hrelation :
      (raw.baseChange (g.comp f)).relationFamily =
        ((raw.baseChange f).baseChange g).relationFamily := by
    funext W
    exact StructuralRelationFamily.baseChange_comp (raw.relationFamily W) f g
  refine RawAmbientRestrictionSystem.ext
    (raw.baseChange (g.comp f)) ((raw.baseChange f).baseChange g)
      rfl (heq_of_eq hrelation) ?_
  apply Function.hfunext rfl
  intro X X' hX
  cases hX
  apply Function.hfunext rfl
  intro Y Y' hY
  cases hY
  apply Function.hfunext rfl
  intro h h' hh
  cases hh
  exact RestrictionStableStructuralRelations.baseChange_comp
    (raw.restrictionStable h) f g

/-- SD6 / AC28 identifies the structural quotient after coefficient change
with objectwise extension of coefficients, including restriction naturality. -/
noncomputable def baseChangePresheafIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : FlatCoefficientChange k k') :
    (raw.baseChange f.hom).toPresheaf ≅
      raw.toPresheaf ⋙ f.coefficientExtension := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · let h := quotientBaseChangeIsPushout raw f X.unop
    refine Under.isoMk h.isoPushout ?_
    exact h.inr_isoPushout_hom
  · intro X Y g
    apply Under.UnderMorphism.ext
    let hX := quotientBaseChangeIsPushout raw f X.unop
    let hY := quotientBaseChangeIsPushout raw f Y.unop
    change ((raw.baseChange f.hom).toPresheaf.map g).right ≫
        hY.isoPushout.hom =
      hX.isoPushout.hom ≫
        (f.coefficientExtension.map (raw.toPresheaf.map g)).right
    rw [← cancel_epi hX.isoPushout.inv]
    simp only [Iso.inv_hom_id_assoc]
    have hnat :
        (CommRingCat.ofHom (quotientBaseChangeMap raw f.hom X.unop)) ≫
            ((raw.baseChange f.hom).toPresheaf.map g).right =
          (raw.toPresheaf.map g).right ≫
            CommRingCat.ofHom
              (quotientBaseChangeMap raw f.hom Y.unop) := by
      apply CommRingCat.hom_ext
      change ((raw.baseChange f.hom).restrictionStable g.unop).quotientDesc.comp
          (quotientBaseChangeMap raw f.hom X.unop) =
        (quotientBaseChangeMap raw f.hom Y.unop).comp
          (raw.restrictionStable g.unop).quotientDesc
      exact (quotientBaseChangeMap_natural raw f.hom g.unop).symm
    apply pushout.hom_ext
    · simp only [← Category.assoc, hX.inl_isoPushout_inv]
      rw [hnat]
      rw [Category.assoc, hY.inl_isoPushout_hom]
      simp [FlatCoefficientChange.coefficientExtension]
    · simp only [← Category.assoc, hX.inr_isoPushout_inv]
      rw [Under.w]
      rw [hY.inr_isoPushout_hom]
      simp [FlatCoefficientChange.coefficientExtension]

/-! ### SD6 / AC29: sheafified sections and affine spectra -/

/-- SD6 / AC29 identifies extension of a sheafified section object with the
section object of the changed raw system.

The comparison is the composite of the canonical `sheafifyComposeIso` and
the sheafification of `baseChangePresheafIso`; no section comparison is
supplied by the caller. -/
noncomputable def sheafifiedSectionObjectBaseChangeIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (f.coefficientExtension.obj
        (raw.toRingedSite.structureSheaf.val.obj (op W)) :
      AATCommAlgCat.{u, v} k') ≅
      (raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj (op W) := by
  let comparison :
      raw.toRingedSite.structureSheaf.val ⋙ f.coefficientExtension ≅
        (raw.baseChange f.hom).toRingedSite.structureSheaf.val :=
    (sheafifyComposeIso S.topology f.coefficientExtension raw.toPresheaf).symm ≪≫
      ((CategoryTheory.sheafification S.topology
        (AATCommAlgCat.{u, v} k')).mapIso
          (baseChangePresheafIso raw f)).symm
  exact comparison.app (op W)

/-- SD6 / AC29 identifies a changed affine chart with the actual pullback of
the source chart along the coefficient-ring spectrum map.

The construction passes from the section-object comparison to the
under-category pushout, uses Mathlib's tensor-product presentation of that
pushout, and then applies `pullbackSpecIso`. -/
noncomputable def sheafifiedSectionSpecBaseChangeIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    architectureChartSpec (raw.baseChange f.hom) W ≅
      pullback
        (AlgebraicGeometry.Scheme.Spec.map
          (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.op)
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom f.liftedHom).op) := by
  let oldObject := raw.toRingedSite.structureSheaf.val.obj (op W)
  let sourceRing := ULift.{max u v, v} k
  let targetRing := ULift.{max u v, v} k'
  let sectionRing := oldObject.right
  letI : Algebra sourceRing targetRing := f.liftedHom.toAlgebra
  letI : Algebra sourceRing sectionRing := oldObject.hom.hom.toAlgebra
  let sectionObjectIso :
      (Under.pushout (CommRingCat.ofHom f.liftedHom)).obj oldObject ≅
        (raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj (op W) := by
    simpa [FlatCoefficientChange.coefficientExtension] using
      sheafifiedSectionObjectBaseChangeIso raw f W
  let changedToPushout :
      SheafifiedSectionRing (raw.baseChange f.hom) W ≅
        ((Under.pushout (CommRingCat.ofHom f.liftedHom)).obj oldObject).right :=
    (Comma.rightIso sectionObjectIso).symm
  let tensorToPushout :
      CommRingCat.of
          (targetRing ⊗[sourceRing]
            (sectionRing : Type (max u v))) ≅
        ((Under.pushout (CommRingCat.ofHom f.liftedHom)).obj oldObject).right := by
    simpa using Comma.rightIso
      (CommRingCat.tensorProdObjIsoPushoutObj
        (CommRingCat.of targetRing) oldObject)
  exact
    ((Scheme.Spec.mapIso changedToPushout.symm.op ≪≫
        Scheme.Spec.mapIso tensorToPushout.op) ≪≫
      (AlgebraicGeometry.pullbackSpecIso
        sourceRing targetRing sectionRing).symm) ≪≫
      pullbackSymmetry _ _

/-- SD6 / AC29 is the canonical map from source sheafified sections to
changed sheafified sections: the pushout inclusion followed by the canonical
section-object comparison. -/
noncomputable def sheafifiedSectionBaseChangeMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    SheafifiedSectionRing raw W ⟶
      SheafifiedSectionRing (raw.baseChange f.hom) W :=
  Limits.pushout.inl
      (raw.toRingedSite.structureSheaf.val.obj (op W)).hom
      (CommRingCat.ofHom f.liftedHom) ≫
    (sheafifiedSectionObjectBaseChangeIso raw f W).hom.right

/-- SD6 / AC29 characterization of the canonical sheafified-section map. -/
theorem sheafifiedSectionBaseChangeMap_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    sheafifiedSectionBaseChangeMap raw f W =
      Limits.pushout.inl
          (raw.toRingedSite.structureSheaf.val.obj (op W)).hom
          (CommRingCat.ofHom f.liftedHom) ≫
        (sheafifiedSectionObjectBaseChangeIso raw f W).hom.right :=
  rfl

/-- The first projection of the canonical affine base-change comparison is
the spectrum of the canonical section-ring base-change map. -/
@[reassoc]
theorem sheafifiedSectionSpecBaseChangeIso_hom_fst
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (sheafifiedSectionSpecBaseChangeIso raw f W).hom ≫
        pullback.fst
          (AlgebraicGeometry.Scheme.Spec.map
            (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.op)
          (AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom f.liftedHom).op) =
      AlgebraicGeometry.Scheme.Spec.map
        (sheafifiedSectionBaseChangeMap raw f W).op := by
  letI : Algebra (ULift.{max u v, v} k) (ULift.{max u v, v} k') :=
    f.liftedHom.toAlgebra
  letI : Algebra (ULift.{max u v, v} k)
      (raw.toRingedSite.structureSheaf.val.obj (op W)).right :=
    (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.hom.toAlgebra
  simp [sheafifiedSectionSpecBaseChangeIso,
    sheafifiedSectionBaseChangeMap, FlatCoefficientChange.coefficientExtension,
    Category.assoc]
  erw [pullbackSymmetry_hom_comp_fst]
  rw [AlgebraicGeometry.pullbackSpecIso_inv_snd]
  let tensorIso := CommRingCat.tensorProdObjIsoPushoutObj
    (CommRingCat.of (ULift.{max u v, v} k'))
    (raw.toRingedSite.structureSheaf.val.obj (op W))
  have hTensorLeg :
      AlgebraicGeometry.Scheme.Spec.map tensorIso.hom.right.op ≫
          AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom)).op =
        AlgebraicGeometry.Scheme.Spec.map
          (pushout.inl
            (raw.toRingedSite.structureSheaf.val.obj (op W)).hom
            (CommRingCat.ofHom f.liftedHom)).op := by
    rw [← AlgebraicGeometry.Scheme.Spec.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    rw [← cancel_mono tensorIso.inv.right]
    simpa [tensorIso] using
      (CommRingCat.pushout_inl_tensorProdObjIsoPushoutObj_inv_right
        (R := CommRingCat.of (ULift.{max u v, v} k))
        (S := CommRingCat.of (ULift.{max u v, v} k'))
        (raw.toRingedSite.structureSheaf.val.obj (op W))).symm
  simpa only [tensorIso, Category.assoc] using congrArg
    (fun q =>
      AlgebraicGeometry.Scheme.Spec.map
          (sheafifiedSectionObjectBaseChangeIso raw f W).hom.right.op ≫ q)
    hTensorLeg

/-- The second projection of the canonical affine base-change comparison is
the coefficient structure morphism of the changed section object. -/
@[reassoc]
theorem sheafifiedSectionSpecBaseChangeIso_hom_snd
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (sheafifiedSectionSpecBaseChangeIso raw f W).hom ≫
        pullback.snd
          (AlgebraicGeometry.Scheme.Spec.map
            (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.op)
          (AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom f.liftedHom).op) =
      AlgebraicGeometry.Scheme.Spec.map
        ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
          (op W)).hom.op := by
  letI : Algebra (ULift.{max u v, v} k) (ULift.{max u v, v} k') :=
    f.liftedHom.toAlgebra
  letI : Algebra (ULift.{max u v, v} k)
      (raw.toRingedSite.structureSheaf.val.obj (op W)).right :=
    (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.hom.toAlgebra
  simp [sheafifiedSectionSpecBaseChangeIso, Category.assoc]
  erw [pullbackSymmetry_hom_comp_snd]
  rw [AlgebraicGeometry.pullbackSpecIso_inv_fst]
  let tensorIso := CommRingCat.tensorProdObjIsoPushoutObj
    (CommRingCat.of (ULift.{max u v, v} k'))
    (raw.toRingedSite.structureSheaf.val.obj (op W))
  have hTensorLeg :
      AlgebraicGeometry.Scheme.Spec.map tensorIso.hom.right.op ≫
          AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom
              Algebra.TensorProduct.includeLeftRingHom).op =
        AlgebraicGeometry.Scheme.Spec.map
          (pushout.inr
            (raw.toRingedSite.structureSheaf.val.obj (op W)).hom
            (CommRingCat.ofHom f.liftedHom)).op := by
    rw [← AlgebraicGeometry.Scheme.Spec.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    rw [← cancel_mono tensorIso.inv.right]
    simpa [tensorIso] using
      (CommRingCat.pushout_inr_tensorProdObjIsoPushoutObj_inv_right
        (R := CommRingCat.of (ULift.{max u v, v} k))
        (S := CommRingCat.of (ULift.{max u v, v} k'))
        (raw.toRingedSite.structureSheaf.val.obj (op W))).symm
  have hSectionLeg :
      AlgebraicGeometry.Scheme.Spec.map
          (sheafifiedSectionObjectBaseChangeIso raw f W).hom.right.op ≫
        AlgebraicGeometry.Scheme.Spec.map
          (pushout.inr
            (raw.toRingedSite.structureSheaf.val.obj (op W)).hom
            (CommRingCat.ofHom f.liftedHom)).op =
      AlgebraicGeometry.Scheme.Spec.map
        ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
          (op W)).hom.op := by
    rw [← AlgebraicGeometry.Scheme.Spec.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    simpa [FlatCoefficientChange.coefficientExtension] using
      (sheafifiedSectionObjectBaseChangeIso raw f W).hom.w.symm
  calc
    _ = AlgebraicGeometry.Scheme.Spec.map
          (sheafifiedSectionObjectBaseChangeIso raw f W).hom.right.op ≫
        AlgebraicGeometry.Scheme.Spec.map
          (pushout.inr
            (raw.toRingedSite.structureSheaf.val.obj (op W)).hom
            (CommRingCat.ofHom f.liftedHom)).op := by
      simpa only [tensorIso, Category.assoc] using congrArg
        (fun q =>
          AlgebraicGeometry.Scheme.Spec.map
              (sheafifiedSectionObjectBaseChangeIso raw f W).hom.right.op ≫ q)
        hTensorLeg
    _ = _ := hSectionLeg

end RawAmbientRestrictionSystem

end LawAlgebra

namespace Derived.Intersection

open scoped ChangeOfRings

/-- The SD7 / AC34 supporting scalar-extension object. It uses Mathlib's functor directly;
`f.hom` supplies the coefficient action, while flatness is used by homology comparisons. -/
noncomputable def moduleScalarExtension
    {R R' : Type u}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R' :=
  (ModuleCat.extendScalars f.hom).obj M

/-- The SD7 / AC34 supporting unit for class-level formulas. It is the canonical adjunction unit
determined by the coefficient homomorphism `f.hom`. -/
noncomputable def moduleScalarExtensionUnit
    {R R' : Type u}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{max u v} R) :
    M ⟶ (ModuleCat.restrictScalars f.hom).obj
      (moduleScalarExtension f M) :=
  (ModuleCat.extendRestrictScalarsAdj f.hom).unit.app M

/-- The SD7 characterization API for `moduleScalarExtensionUnit`: the unit determined by `f.hom`
sends every element to its canonical pure tensor. -/
@[simp] theorem moduleScalarExtensionUnit_apply
    {R R' : Type u}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{max u v} R) (m : M) :
    moduleScalarExtensionUnit f M m =
      (1 : R') ⊗ₜ[R, f.hom] m := by
  rfl

/-- The SD7 identity-coherence API. The identity coefficient change supplies the ring identity
homomorphism, and Mathlib's canonical extension-of-scalars identity iso supplies the result. -/
noncomputable def moduleScalarExtensionIdIso
    {R : Type u} [CommRing R]
    (M : ModuleCat.{max u v} R) :
    moduleScalarExtension (FlatCoefficientChange.refl R) M ≅ M :=
  (ModuleCat.extendScalarsId R).app M

/-- The SD7 composition-coherence API. The coefficient changes `f` and `g` supply the composite
ring homomorphism, and Mathlib's scalar-extension compositor supplies the canonical iso. -/
noncomputable def moduleScalarExtensionCompIso
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    (M : ModuleCat.{max u v} R) :
    moduleScalarExtension g (moduleScalarExtension f M) ≅
      moduleScalarExtension (f.comp g) M :=
  (ModuleCat.extendScalarsComp f.hom g.hom).symm.app M

end Derived.Intersection

namespace Cohomology

open scoped ChangeOfRings

/-- A large fixed-ring coefficient presheaf whose underlying additive
presheaf satisfies the actual sheaf condition. -/
structure LinearCoefficientSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (R : Type u) [CommRing R]
    (S : Site.AATSite A) where
  /-- The large `R`-module-valued coefficient presheaf. -/
  modulePresheaf : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R
  /-- The sheaf condition after forgetting only the fixed `R`-module action. -/
  isSheaf : Presheaf.IsSheaf S.topology
    (modulePresheaf ⋙
      forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

namespace LinearCoefficientSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/-- The underlying large additive sheaf of a linear coefficient sheaf. -/
noncomputable def toAddCommGrpSheaf
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S) :
    Sheaf S.topology AddCommGrpCat.{u + 1} :=
  ⟨_, Ob.isSheaf⟩

/-!
## Implementation notes

The fixed `R`-action is transported through additive sheafification by mapping
`ModuleCat.smulNatTrans`.  `ModuleCat.mkOfSMul` reconstructs every section as
an `R`-module, and naturality of the mapped scalar endomorphisms makes every
restriction map linear.  Thus this construction uses only additive
`HasSheafify`; it does not request a module-valued sheafification instance or
accept a target coefficient sheaf from the caller.

Composition coherence is obtained from the universal property of this
additive construction.  The internal adjunction to Mathlib's category of
module-valued sheaves lets the existing `PreservesSheafification` theorem for
the scalar-extension adjunction prove that the whiskered unit becomes an
isomorphism.  This avoids treating iterated sheafification as definitional.
-/

private noncomputable def sheafifiedScalarAction
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (W : S.categoryᵒᵖ) :
    R →+* End ((sheafify S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj W) where
  toFun r := (sheafifyMap S.topology
    (Functor.whiskerLeft P (ModuleCat.smulNatTrans R r))).app W
  map_one' := by simp
  map_zero' := by
    change ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerLeft P (ModuleCat.smulNatTrans R 0))).val.app W = 0
    rw [map_zero]
    change ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map 0).val.app W = 0
    rw [Functor.map_zero]
    rfl
  map_mul' r s := by simp
  map_add' r s := by
    change ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerLeft P (ModuleCat.smulNatTrans R (r + s)))).val.app W = _
    rw [map_add]
    change ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerLeft P
        ((ModuleCat.smulNatTrans R) r + (ModuleCat.smulNatTrans R) s))).val.app W = _
    rw [show Functor.whiskerLeft P
      ((ModuleCat.smulNatTrans R) r + (ModuleCat.smulNatTrans R) s) =
        Functor.whiskerLeft P (ModuleCat.smulNatTrans R r) +
          Functor.whiskerLeft P (ModuleCat.smulNatTrans R s) by rfl]
    rw [Functor.map_add]
    rfl

private noncomputable def sheafifiedModulePresheaf
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj W := ModuleCat.mkOfSMul (sheafifiedScalarAction P W)
  map {X Y} g := ModuleCat.homMk
    ((sheafify S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map g)
    (fun r => (sheafifyMap S.topology
      (Functor.whiskerLeft P (ModuleCat.smulNatTrans R r))).naturality g)
  map_id X := by
    apply ModuleCat.hom_ext
    ext x
    change ((sheafify S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map (𝟙 X)) x = x
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    change ((sheafify S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map (f ≫ g)) x = _
    simp
    rfl

/-- Additively sheafify a large fixed-ring module presheaf and transport its
scalar action through the sheafification functor. -/
noncomputable def moduleSheafification
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    LinearCoefficientSheaf R S where
  modulePresheaf := sheafifiedModulePresheaf P
  isSheaf := by
    exact ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).cond

private noncomputable def moduleSheafificationUnit
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    P ⟶ (moduleSheafification P).modulePresheaf where
  app W := ModuleCat.homMk
    ((toSheafify S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).app W)
    (fun r => (NatTrans.congr_app
      (toSheafify_naturality (J := S.topology)
        (Functor.whiskerLeft P (ModuleCat.smulNatTrans R r))) W).symm)
  naturality X Y g := by
    apply ModuleCat.hom_ext
    ext x
    exact CategoryTheory.congr_fun
      ((toSheafify S.topology
        (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).naturality g) x

/-- Objectwise extension of scalars before additive sheafification. -/
noncomputable def rawBaseChangePresheaf
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R') :
    S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R' :=
  Ob.modulePresheaf ⋙ ModuleCat.extendScalars f.hom

/-- The canonical SD8 coefficient change: extend scalars objectwise and then
apply additive sheafification. -/
noncomputable def baseChange
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    LinearCoefficientSheaf R' S :=
  moduleSheafification (Ob.rawBaseChangePresheaf f)

/-- Scalar extension of a large module, used by the linear Čech API. -/
noncomputable def moduleScalarExtension
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{u + 1} R) :
    ModuleCat.{u + 1} R' :=
  (ModuleCat.extendScalars f.hom).obj M

/-- The sectionwise component of the additive sheafification unit after
objectwise scalar extension. -/
noncomputable def baseChangeSectionMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (W : S.category) :
    moduleScalarExtension f (Ob.modulePresheaf.obj (op W)) ⟶
      (Ob.baseChange f).modulePresheaf.obj (op W) :=
  (moduleSheafificationUnit (Ob.rawBaseChangePresheaf f)).app (op W)

/-- Naturality of the canonical section map with respect to site
restriction morphisms. -/
theorem baseChangeSectionMap_naturality
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {source target : S.category} (g : source ⟶ target) :
    (ModuleCat.extendScalars f.hom).map
          (Ob.modulePresheaf.map g.op) ≫
        Ob.baseChangeSectionMap f source =
      Ob.baseChangeSectionMap f target ≫
        (Ob.baseChange f).modulePresheaf.map g.op := by
  exact (moduleSheafificationUnit (Ob.rawBaseChangePresheaf f)).naturality g.op

private noncomputable def moduleSheafificationMap
    {R : Type u} [CommRing R]
    {P Q : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (α : P ⟶ Q) :
    (moduleSheafification P).modulePresheaf ⟶
      (moduleSheafification Q).modulePresheaf where
  app W := ModuleCat.homMk
    ((sheafifyMap S.topology
      (Functor.whiskerRight α
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))).app W)
    (fun r => by
      change (sheafifyMap S.topology
          (Functor.whiskerRight α
            (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) ≫
        sheafifyMap S.topology
          (Functor.whiskerLeft Q (ModuleCat.smulNatTrans R r))).app W =
        (sheafifyMap S.topology
          (Functor.whiskerLeft P (ModuleCat.smulNatTrans R r)) ≫
        sheafifyMap S.topology
          (Functor.whiskerRight α
            (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))).app W
      apply NatTrans.congr_app
      rw [← sheafifyMap_comp, ← sheafifyMap_comp]
      congr 1
      ext W x
      exact ((α.app W).hom.map_smul r x).symm)
  naturality X Y g := by
    apply ModuleCat.hom_ext
    ext x
    exact CategoryTheory.congr_fun
      ((sheafifyMap S.topology
        (Functor.whiskerRight α
          (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))).naturality g) x

@[simp]
private theorem moduleSheafificationMap_id
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    moduleSheafificationMap (𝟙 P) = 𝟙 _ := by
  ext W x
  change (sheafifyMap S.topology
    (Functor.whiskerRight (𝟙 P)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))).app W x = x
  simp

@[simp]
private theorem moduleSheafificationMap_comp
    {R : Type u} [CommRing R]
    {P Q T : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (α : P ⟶ Q) (β : Q ⟶ T) :
    moduleSheafificationMap (α ≫ β) =
      moduleSheafificationMap α ≫ moduleSheafificationMap β := by
  ext W x
  change (sheafifyMap S.topology
    (Functor.whiskerRight (α ≫ β)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))).app W x = _
  simp
  rfl

@[reassoc (attr := simp)]
private theorem moduleSheafificationUnit_map
    {R : Type u} [CommRing R]
    {P Q : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (α : P ⟶ Q) :
    α ≫ moduleSheafificationUnit Q =
      moduleSheafificationUnit P ≫ moduleSheafificationMap α := by
  ext W x
  exact CategoryTheory.congr_fun
    (NatTrans.congr_app
      (toSheafify_naturality (J := S.topology)
        (Functor.whiskerRight α
          (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))) W) x

private noncomputable def moduleSheafificationUnitIso
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (hP : Presheaf.IsSheaf S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) :
    P ≅ (moduleSheafification P).modulePresheaf := by
  letI : IsIso (toSheafify S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) :=
    isIso_toSheafify S.topology hP
  haveI (W : S.categoryᵒᵖ) : IsIso ((moduleSheafificationUnit P).app W) := by
    letI : IsIso ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
        ((moduleSheafificationUnit P).app W)) := by
      change IsIso ((toSheafify S.topology
        (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).app W)
      infer_instance
    exact isIso_of_reflects_iso ((moduleSheafificationUnit P).app W)
      ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))
  haveI : IsIso (moduleSheafificationUnit P) :=
    NatIso.isIso_of_isIso_app (moduleSheafificationUnit P)
  exact asIso (moduleSheafificationUnit P)

/-- A sectionwise base-change map is an isomorphism when the raw
scalar-extended additive presheaf already satisfies the sheaf condition. -/
theorem baseChangeSectionMap_isIso_of_raw_isSheaf
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (hraw : Presheaf.IsSheaf S.topology
      (Ob.rawBaseChangePresheaf f ⋙
        forget₂ (ModuleCat.{u + 1} R') AddCommGrpCat.{u + 1}))
    (W : S.category) :
    IsIso (Ob.baseChangeSectionMap f W) := by
  let e := moduleSheafificationUnitIso
    (Ob.rawBaseChangePresheaf f) hraw
  change IsIso (e.hom.app (op W))
  infer_instance

private def IsLinearSheaf
    (R : Type u) [CommRing R] :
    ObjectProperty (S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R) :=
  fun P => Presheaf.IsSheaf S.topology
    (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

private abbrev LinearSheafCategory
    (R : Type u) [CommRing R] :=
  (IsLinearSheaf (S := S) R).FullSubcategory

private noncomputable def moduleSheafificationLift
    {R : Type u} [CommRing R]
    {P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (T : LinearSheafCategory (S := S) R)
    (α : P ⟶ T.obj) :
    (moduleSheafification P).modulePresheaf ⟶ T.obj where
  app W := ModuleCat.homMk
    ((sheafifyLift S.topology
      (Functor.whiskerRight α
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) T.property).app W)
    (fun r => by
      change (sheafifyLift S.topology
          (Functor.whiskerRight α
            (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) T.property ≫
        Functor.whiskerLeft T.obj (ModuleCat.smulNatTrans R r)).app W =
        (sheafifyMap S.topology
            (Functor.whiskerLeft P (ModuleCat.smulNatTrans R r)) ≫
          sheafifyLift S.topology
            (Functor.whiskerRight α
              (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) T.property).app W
      apply NatTrans.congr_app
      apply sheafify_hom_ext S.topology _ _ T.property
      rw [← Category.assoc, toSheafify_sheafifyLift]
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        toSheafify_sheafifyLift]
      ext W x
      exact ((α.app W).hom.map_smul r x).symm)
  naturality X Y g := by
    apply ModuleCat.hom_ext
    ext x
    exact CategoryTheory.congr_fun
      ((sheafifyLift S.topology
        (Functor.whiskerRight α
          (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) T.property).naturality g) x

@[reassoc (attr := simp)]
private theorem moduleSheafificationUnit_lift
    {R : Type u} [CommRing R]
    {P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (T : LinearSheafCategory (S := S) R)
    (α : P ⟶ T.obj) :
    moduleSheafificationUnit P ≫ moduleSheafificationLift T α = α := by
  ext W x
  exact CategoryTheory.congr_fun
    (NatTrans.congr_app
      (toSheafify_sheafifyLift S.topology
        (Functor.whiskerRight α
          (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) T.property) W) x

private theorem moduleSheafificationLift_unique
    {R : Type u} [CommRing R]
    {P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (T : LinearSheafCategory (S := S) R)
    (α : P ⟶ T.obj)
    (γ : (moduleSheafification P).modulePresheaf ⟶ T.obj)
    (h : moduleSheafificationUnit P ≫ γ = α) :
    γ = moduleSheafificationLift T α := by
  apply NatTrans.ext
  ext W x
  have hUnderlying :
      toSheafify S.topology
          (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ≫
        Functor.whiskerRight γ
          (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) =
      Functor.whiskerRight α
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) := by
    simpa using congrArg
      (fun τ => Functor.whiskerRight τ
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) h
  have hLift := sheafifyLift_unique S.topology
    (Functor.whiskerRight α
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) T.property
    (Functor.whiskerRight γ
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) hUnderlying
  exact CategoryTheory.congr_fun (NatTrans.congr_app hLift W) x

private noncomputable def linearSheafCategoryOfSheaf
    (R : Type u) [CommRing R]
    (T : Sheaf S.topology (ModuleCat.{u + 1} R)) :
    LinearSheafCategory (S := S) R :=
  ⟨T.val, Presheaf.isSheaf_comp_of_isSheaf S.topology T.val
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) T.cond⟩

private noncomputable def modulePresheafToMathlibSheaf
    (R : Type u) [CommRing R]
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    (S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R) ⥤
      Sheaf S.topology (ModuleCat.{u + 1} R) where
  obj P := ⟨(moduleSheafification P).modulePresheaf,
    Presheaf.isSheaf_of_isSheaf_comp S.topology
      (moduleSheafification P).modulePresheaf
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
      (moduleSheafification P).isSheaf⟩
  map α := ⟨moduleSheafificationMap α⟩
  map_id P := Sheaf.Hom.ext (moduleSheafificationMap_id P)
  map_comp α β := Sheaf.Hom.ext (moduleSheafificationMap_comp α β)

private noncomputable def moduleSheafificationMathlibAdjunction
    (R : Type u) [CommRing R]
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    modulePresheafToMathlibSheaf (S := S) R ⊣
      sheafToPresheaf S.topology (ModuleCat.{u + 1} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P T =>
        { toFun := fun e => by
            change P ⟶ T.val
            exact moduleSheafificationUnit P ≫ e.val
          invFun := fun α => by
            refine ⟨moduleSheafificationLift
              (linearSheafCategoryOfSheaf R T) α⟩
          left_inv := fun e => by
            apply Sheaf.Hom.ext
            change moduleSheafificationLift
              (linearSheafCategoryOfSheaf R T)
              (moduleSheafificationUnit P ≫ e.val) = e.val
            symm
            apply moduleSheafificationLift_unique
              (linearSheafCategoryOfSheaf R T) _ e.val
            rfl
          right_inv := fun α =>
            moduleSheafificationUnit_lift
              (linearSheafCategoryOfSheaf R T) α }
      homEquiv_naturality_left_symm := by
        intro P Q T f g
        apply Sheaf.Hom.ext
        change moduleSheafificationLift
            (linearSheafCategoryOfSheaf R T) (f ≫ g) =
          moduleSheafificationMap f ≫
            moduleSheafificationLift (linearSheafCategoryOfSheaf R T) g
        symm
        apply moduleSheafificationLift_unique
          (linearSheafCategoryOfSheaf R T) _ _
        rw [← Category.assoc, ← moduleSheafificationUnit_map f,
          Category.assoc, moduleSheafificationUnit_lift]
      homEquiv_naturality_right := by
        intro P T T' f g
        rfl }

private theorem isIso_moduleSheafificationMap_whiskeredUnit
    {R R' : Type u} [CommRing R] [CommRing R']
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    IsIso (moduleSheafificationMap
      (Functor.whiskerRight (moduleSheafificationUnit P)
        (ModuleCat.extendScalars.{u, u, u + 1} f.hom))) := by
  letI : S.topology.PreservesSheafification
      (ModuleCat.extendScalars.{u, u, u + 1} f.hom) :=
    Sheaf.preservesSheafification_of_adjunction S.topology
      (show ModuleCat.extendScalars.{u, u, u + 1} f.hom ⊣ _ from
        ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} f.hom)
  haveI : IsIso
      ((modulePresheafToMathlibSheaf (S := S) R').map
        (Functor.whiskerRight (moduleSheafificationUnit P)
          (ModuleCat.extendScalars.{u, u, u + 1} f.hom))) :=
    ((S.topology.preservesSheafification_iff_of_adjunctions
      (ModuleCat.extendScalars.{u, u, u + 1} f.hom)
      (moduleSheafificationMathlibAdjunction (S := S) R)
      (moduleSheafificationMathlibAdjunction (S := S) R')).mp
        (by infer_instance)) P
  change IsIso (((modulePresheafToMathlibSheaf (S := S) R').map
    (Functor.whiskerRight (moduleSheafificationUnit P)
      (ModuleCat.extendScalars.{u, u, u + 1} f.hom))).val)
  exact (inferInstance : IsIso
    ((sheafToPresheaf S.topology (ModuleCat.{u + 1} R')).map
      ((modulePresheafToMathlibSheaf (S := S) R').map
        (Functor.whiskerRight (moduleSheafificationUnit P)
          (ModuleCat.extendScalars.{u, u, u + 1} f.hom)))))

private noncomputable def moduleSheafificationWhiskeredUnitIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    (moduleSheafification
      (P ⋙ ModuleCat.extendScalars.{u, u, u + 1} f.hom)).modulePresheaf ≅
    (moduleSheafification
      ((moduleSheafification P).modulePresheaf ⋙
        ModuleCat.extendScalars.{u, u, u + 1} f.hom)).modulePresheaf := by
  letI := isIso_moduleSheafificationMap_whiskeredUnit P f
  exact asIso (moduleSheafificationMap
    (Functor.whiskerRight (moduleSheafificationUnit P)
      (ModuleCat.extendScalars.{u, u, u + 1} f.hom)))

private noncomputable def moduleSheafificationMapIso
    {R : Type u} [CommRing R]
    {P Q : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (e : P ≅ Q) :
    (moduleSheafification P).modulePresheaf ≅
      (moduleSheafification Q).modulePresheaf :=
  (sheafToPresheaf S.topology (ModuleCat.{u + 1} R)).mapIso
    ((modulePresheafToMathlibSheaf (S := S) R).mapIso e)

private noncomputable def rawBaseChangeIdUnderlyingIso
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S) :
    (Ob.rawBaseChangePresheaf (FlatCoefficientChange.refl R) ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ≅
      (Ob.modulePresheaf ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) := by
  simpa [rawBaseChangePresheaf, FlatCoefficientChange.refl] using
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft Ob.modulePresheaf
        (ModuleCat.extendScalarsId.{u, u + 1} R))
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

private theorem rawBaseChangeId_isSheaf
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S) :
    Presheaf.IsSheaf S.topology
      (Ob.rawBaseChangePresheaf (FlatCoefficientChange.refl R) ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
  (Presheaf.isSheaf_of_iso_iff (rawBaseChangeIdUnderlyingIso Ob)).2 Ob.isSheaf

/-- Identity coherence for canonical coefficient base change, using the
sheafification unit and Mathlib's scalar-extension identity isomorphism. -/
noncomputable def baseChangeIdIso
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    (Ob.baseChange (FlatCoefficientChange.refl R)).modulePresheaf ≅
      Ob.modulePresheaf :=
  (moduleSheafificationUnitIso
      (Ob.rawBaseChangePresheaf (FlatCoefficientChange.refl R))
      (rawBaseChangeId_isSheaf Ob)).symm ≪≫
    Functor.isoWhiskerLeft Ob.modulePresheaf
      (ModuleCat.extendScalarsId.{u, u + 1} R)

/-- Composition coherence for canonical coefficient base change, using the
additive sheafification compositor and Mathlib's scalar-extension compositor. -/
noncomputable def baseChangeCompIso
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    ((Ob.baseChange f).baseChange g).modulePresheaf ≅
      (Ob.baseChange (f.comp g)).modulePresheaf :=
  (moduleSheafificationWhiskeredUnitIso
      (Ob.rawBaseChangePresheaf f) g).symm ≪≫
    moduleSheafificationMapIso
      (Functor.isoWhiskerLeft Ob.modulePresheaf
        (ModuleCat.extendScalarsComp.{u, u + 1} f.hom g.hom).symm)

/-- Internal natural-transformation form of section-map composition coherence.
It uses the additive sheafification units and Mathlib's scalar-extension compositor;
`baseChangeSectionMap_comp` is the public pointwise API. -/
private theorem baseChangeSectionMap_comp_nat
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    Functor.whiskerRight
          (moduleSheafificationUnit (Ob.rawBaseChangePresheaf f))
          (ModuleCat.extendScalars.{u, u, u + 1} g.hom) ≫
        moduleSheafificationUnit
          ((moduleSheafification (Ob.rawBaseChangePresheaf f)).modulePresheaf ⋙
            ModuleCat.extendScalars.{u, u, u + 1} g.hom) ≫
        (moduleSheafificationWhiskeredUnitIso
          (Ob.rawBaseChangePresheaf f) g).inv ≫
        (moduleSheafificationMapIso
          (Functor.isoWhiskerLeft Ob.modulePresheaf
            (ModuleCat.extendScalarsComp.{u, u + 1}
              f.hom g.hom).symm)).hom =
      (Functor.isoWhiskerLeft Ob.modulePresheaf
          (ModuleCat.extendScalarsComp.{u, u + 1}
            f.hom g.hom).symm).hom ≫
        moduleSheafificationUnit (Ob.rawBaseChangePresheaf (f.comp g)) := by
  let E := ModuleCat.extendScalars.{u, u, u + 1} g.hom
  let P := Ob.rawBaseChangePresheaf f
  let α := Functor.whiskerRight (moduleSheafificationUnit P) E
  let β := Functor.isoWhiskerLeft Ob.modulePresheaf
    (ModuleCat.extendScalarsComp.{u, u + 1} f.hom g.hom).symm
  rw [← Category.assoc, ← Category.assoc,
    moduleSheafificationUnit_map α]
  change
    moduleSheafificationUnit (P ⋙ E) ≫
        (moduleSheafificationWhiskeredUnitIso P g).hom ≫
        (moduleSheafificationWhiskeredUnitIso P g).inv ≫
        (moduleSheafificationMapIso β).hom =
      β.hom ≫ moduleSheafificationUnit (Ob.rawBaseChangePresheaf (f.comp g))
  rw [Iso.hom_inv_id_assoc]
  exact (moduleSheafificationUnit_map β.hom).symm

/-- The canonical section map for the identity coefficient change is the
Mathlib scalar-extension identity map after the canonical sheafification
identity isomorphism. -/
@[reassoc] theorem baseChangeSectionMap_id
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (W : S.category) :
    Ob.baseChangeSectionMap (FlatCoefficientChange.refl R) W ≫
        (Ob.baseChangeIdIso).hom.app (op W) =
      (ModuleCat.extendScalarsId.{u, u + 1} R).hom.app
        (Ob.modulePresheaf.obj (op W)) := by
  simp [baseChangeSectionMap, baseChangeIdIso,
    moduleSheafificationUnitIso, rawBaseChangePresheaf]

/-- Iterated canonical section maps agree with the composite section map
after the additive-sheafification and scalar-extension compositors. -/
@[reassoc] theorem baseChangeSectionMap_comp
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (W : S.category) :
    (ModuleCat.extendScalars g.hom).map
          (Ob.baseChangeSectionMap f W) ≫
        (Ob.baseChange f).baseChangeSectionMap g W ≫
        (Ob.baseChangeCompIso f g).hom.app (op W) =
      (ModuleCat.extendScalarsComp.{u, u + 1}
          f.hom g.hom).symm.hom.app
          (Ob.modulePresheaf.obj (op W)) ≫
        Ob.baseChangeSectionMap (f.comp g) W := by
  simpa only [baseChangeSectionMap, baseChangeCompIso,
    moduleSheafificationWhiskeredUnitIso, moduleSheafificationMapIso,
    rawBaseChangePresheaf, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app] using
      NatTrans.congr_app (baseChangeSectionMap_comp_nat Ob f g) (op W)

end LinearCoefficientSheaf

/-!
## Linear Čech implementation notes

The module-valued cosimplicial object is built directly from the selected
overlap restrictions. `CochainComplex.of` consumes Mathlib's
`AlternatingCofaceMapComplex.d_squared`, so neither the complex nor its
square-zero proof is caller data.

For scalar extension in `ModuleCat.{u + 1}`, the same-universe finite-limit
instance from `ModuleCat.Descent` is not applicable. The homology comparison
therefore proves exactness directly from `f.flat` via
`Module.Flat.lTensor_exact`. Class change is then the actual target
`homologyπ` of the cycle produced by the scalar-extension unit and
`mapCyclesIso`; it is not defined by reading the requested class equality.
-/

/-- A large fixed-ring Čech complex together with its canonical selected-overlap
cochain presentation. -/
structure LinearCoverRelativeCechComplex
    (R : Type u) [CommRing R]
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : LinearCoefficientSheaf R S) where
  /-- The actual module-valued cochain complex. -/
  complex : CochainComplex (ModuleCat.{u + 1} R) Nat
  /-- Its degreewise identification with selected-overlap sections. -/
  cochainIso :
    ∀ n, complex.X n ≅
      ModuleCat.of R
        (∀ σ : (canonicalCoverRelative 𝒰).simplex n,
          Ob.modulePresheaf.obj
            (op ((canonicalCoverRelative 𝒰).overlap n σ)))

private noncomputable def linearCechCosimplicialObject
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    CosimplicialObject (ModuleCat.{u + 1} R) where
  obj x := ModuleCat.of R
    (∀ σ : (canonicalCoverRelative 𝒰).simplex x.len,
      Ob.modulePresheaf.obj
        (op ((canonicalCoverRelative 𝒰).overlap x.len σ)))
  map {x y} f := ModuleCat.ofHom
    { toFun := fun c σ =>
        Ob.modulePresheaf.map (canonicalTupleOverlapMap 𝒰 f σ).op
          (c (fun i => σ (f.toOrderHom i)))
      map_add' := by
        intro c d
        funext σ
        exact map_add _ _ _
      map_smul' := by
        intro r c
        funext σ
        exact map_smul _ _ _ }
  map_id x := by
    apply ModuleCat.hom_ext
    ext c σ
    change Ob.modulePresheaf.map
      (canonicalTupleOverlapMap 𝒰 (𝟙 x) σ).op (c σ) = c σ
    have hf : canonicalTupleOverlapMap 𝒰 (𝟙 x) σ = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [hf]
    exact FunctorToTypes.map_id_apply
      (F := Ob.modulePresheaf ⋙ forget (ModuleCat.{u + 1} R)) (c σ)
  map_comp {x y z} f g := by
    apply ModuleCat.hom_ext
    ext c σ
    change
      Ob.modulePresheaf.map (canonicalTupleOverlapMap 𝒰 (f ≫ g) σ).op
          (c (fun i => σ ((f ≫ g).toOrderHom i))) =
        Ob.modulePresheaf.map (canonicalTupleOverlapMap 𝒰 g σ).op
          (Ob.modulePresheaf.map
            (canonicalTupleOverlapMap 𝒰 f
              (fun i => σ (g.toOrderHom i))).op
            (c (fun i => σ (g.toOrderHom (f.toOrderHom i)))))
    change
      (Ob.modulePresheaf ⋙ forget (ModuleCat.{u + 1} R)).map
          (canonicalTupleOverlapMap 𝒰 (f ≫ g) σ).op
          (c (fun i => σ ((f ≫ g).toOrderHom i))) =
        (Ob.modulePresheaf ⋙ forget (ModuleCat.{u + 1} R)).map
          (canonicalTupleOverlapMap 𝒰 g σ).op
          ((Ob.modulePresheaf ⋙ forget (ModuleCat.{u + 1} R)).map
            (canonicalTupleOverlapMap 𝒰 f
              (fun i => σ (g.toOrderHom i))).op
            (c (fun i => σ (g.toOrderHom (f.toOrderHom i)))))
    rw [← FunctorToTypes.map_comp_apply]
    congr

/-- The canonical module-valued Čech differential, obtained as the alternating
sum of selected-overlap restriction maps. -/
noncomputable def linearCechDifferential
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    ModuleCat.of R
        (∀ σ : (canonicalCoverRelative 𝒰).simplex n,
          Ob.modulePresheaf.obj
            (op ((canonicalCoverRelative 𝒰).overlap n σ))) ⟶
      ModuleCat.of R
        (∀ σ : (canonicalCoverRelative 𝒰).simplex (n + 1),
          Ob.modulePresheaf.obj
            (op ((canonicalCoverRelative 𝒰).overlap (n + 1) σ))) :=
  AlgebraicTopology.AlternatingCofaceMapComplex.objD
    (linearCechCosimplicialObject Ob 𝒰) n

namespace LinearCoefficientSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- The canonical large linear Čech complex generated by the selected cover's
actual overlap restrictions. The square-zero proof comes from Mathlib's
alternating-coface construction rather than from caller data. -/
noncomputable def canonicalLinearCech
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    LinearCoverRelativeCechComplex R 𝒰 Ob where
  complex := CochainComplex.of
    (fun n => ModuleCat.of R
      (∀ σ : (canonicalCoverRelative 𝒰).simplex n,
        Ob.modulePresheaf.obj
          (op ((canonicalCoverRelative 𝒰).overlap n σ))))
    (linearCechDifferential Ob 𝒰)
    (fun n => AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
      (linearCechCosimplicialObject Ob 𝒰) n)
  cochainIso := fun _ => Iso.refl _

/-- The differential of the canonical linear Čech complex is the named
alternating restriction map in every degree. -/
theorem canonicalLinearCech_d
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.d n (n + 1) =
      ((Ob.canonicalLinearCech 𝒰).cochainIso n).hom ≫
        linearCechDifferential Ob 𝒰 n ≫
        ((Ob.canonicalLinearCech 𝒰).cochainIso (n + 1)).inv := by
  simp [canonicalLinearCech, linearCechDifferential]

/-- Pointwise alternating-sum formula for the canonical linear Čech differential. -/
theorem canonicalLinearCech_d_apply
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.X n)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 1)) :
    ((Ob.canonicalLinearCech 𝒰).complex.d n (n + 1)).hom c σ =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
        Ob.modulePresheaf.map
          (canonicalTupleOverlapMap 𝒰 (SimplexCategory.δ i) σ).op
          (c (fun j => σ ((SimplexCategory.δ i).toOrderHom j))) := by
  rw [canonicalLinearCech_d]
  simp only [canonicalLinearCech, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp]
  change (linearCechDifferential Ob 𝒰 n).hom c σ = _
  simp only [linearCechDifferential,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

end LinearCoefficientSheaf

private noncomputable instance linearExtendScalars_additive
    {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') :
    (ModuleCat.extendScalars.{u, u, u + 1} φ).Additive where
  map_add := by
    intro X Y a b
    letI := φ.toAlgebra
    ext s
    change
      ((1 : R') ⊗ₜ[R, φ] (a.hom s + b.hom s)) =
        (1 : R') ⊗ₜ[R, φ] a.hom s +
          (1 : R') ⊗ₜ[R, φ] b.hom s
    exact TensorProduct.tmul_add _ _ _

private theorem linearExtendScalars_preservesHomology
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R') :
    (ModuleCat.extendScalars.{u, u, u + 1} f.hom).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro L hL
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hL ⊢
  letI := f.hom.toAlgebra
  haveI : Module.Flat R R' := f.flat
  simpa only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
      LinearMap.baseChange_eq_ltensor] using
    (Module.Flat.lTensor_exact R' hL)

namespace LinearCoverRelativeCechComplex

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}
variable {R : Type u} [CommRing R]
variable {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
variable {Ob : LinearCoefficientSheaf R S}

/-- Objectwise scalar extension of the actual module-valued Čech complex. -/
noncomputable def scalarExtension
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R') :
    CochainComplex (ModuleCat.{u + 1} R') Nat := by
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
    ModuleCat.extendScalars.{u, u, u + 1} f.hom
  exact (E.mapHomologicalComplex (ComplexShape.up Nat)).obj K.complex

/-- Degreewise identification of the mapped complex with the named scalar
extension object. -/
noncomputable def scalarExtensionObjIso
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    (K.scalarExtension f).X n ≅
      LinearCoefficientSheaf.moduleScalarExtension f (K.complex.X n) :=
  eqToIso (Functor.mapHomologicalComplex_obj_X
    (ModuleCat.extendScalars.{u, u, u + 1} f.hom)
    (ComplexShape.up Nat) K.complex n)

/-- The canonical extension/restriction unit on degree-`n` cochains. -/
noncomputable def scalarExtensionCochain
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.complex.X n ⟶
      (ModuleCat.restrictScalars f.hom).obj ((K.scalarExtension f).X n) := by
  exact Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
    f (K.complex.X n)

/-- The canonical cochain map agrees with the named scalar-extension unit
under the degreewise object isomorphism. -/
theorem scalarExtensionCochain_objIso
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.scalarExtensionCochain f n ≫
        (ModuleCat.restrictScalars f.hom).map
          (K.scalarExtensionObjIso f n).hom =
      Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
        f (K.complex.X n) := by
  simp [scalarExtensionCochain, scalarExtensionObjIso]

/-- Scalar extension carries each source differential to the corresponding
differential of the mapped complex. -/
theorem scalarExtension_d
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    (K.scalarExtension f).d n (n + 1) ≫
        (K.scalarExtensionObjIso f (n + 1)).hom =
      (K.scalarExtensionObjIso f n).hom ≫
        (ModuleCat.extendScalars f.hom).map
          (K.complex.d n (n + 1)) := by
  dsimp [scalarExtensionObjIso, scalarExtension]
  simp

/-- Flat scalar extension preserves the homology of every large linear Čech
complex in every degree.

Implementation notes: the standard same-universe finite-limit theorem for
`ModuleCat.extendScalars` does not apply to `ModuleCat.{u + 1}`. Instead this
proof derives preservation of homology directly: `f.flat` supplies
`Module.Flat R R'`, and `Module.Flat.lTensor_exact` proves that the mapped
short complex remains exact. This keeps arbitrary degree and introduces no
finite, projective, or caller-supplied comparison premise. -/
noncomputable def hnFlatBaseChangeIso
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    LinearCoefficientSheaf.moduleScalarExtension f
        (K.complex.homology n) ≅
      (K.scalarExtension f).homology n := by
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
    ModuleCat.extendScalars.{u, u, u + 1} f.hom
  letI : E.PreservesHomology := linearExtendScalars_preservesHomology f
  simpa only [LinearCoefficientSheaf.moduleScalarExtension, scalarExtension,
    HomologicalComplex.homology] using
    ((K.complex.sc n).mapHomologyIso E).symm

private theorem hnFlatBaseChangeIso_homologyπ
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat)
    [(ModuleCat.extendScalars.{u, u, u + 1} f.hom).PreservesHomology] :
    (ModuleCat.extendScalars f.hom).map (K.complex.homologyπ n) ≫
        (K.hnFlatBaseChangeIso f n).hom =
      ((K.complex.sc n).mapCyclesIso
          (ModuleCat.extendScalars.{u, u, u + 1} f.hom)).inv ≫
        (K.scalarExtension f).homologyπ n := by
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
    ModuleCat.extendScalars.{u, u, u + 1} f.hom
  let h := (K.complex.sc n).leftHomologyData
  change E.map (K.complex.homologyπ n) ≫
      ((K.complex.sc n).mapHomologyIso E).inv =
    ((K.complex.sc n).mapCyclesIso E).inv ≫
      ((E.mapHomologicalComplex (ComplexShape.up Nat)).obj
        K.complex).homologyπ n
  rw [h.mapHomologyIso_eq E, h.mapCyclesIso_eq E]
  dsimp only [HomologicalComplex.homologyπ, Iso.trans_inv,
    Functor.mapIso, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← Category.assoc, ← E.map_comp,
    h.homologyπ_comp_homologyIso_hom, E.map_comp]
  change E.map h.cyclesIso.hom ≫ (h.map E).π ≫
    (h.map E).homologyIso.inv = _
  rw [(h.map E).π_comp_homologyIso_inv]
  rfl

/-- The actual target cycle obtained from the scalar-extension unit on source
cycles and Mathlib's cycle comparison for a homology-preserving functor. -/
private noncomputable def cycleBaseChange
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.complex.cycles n → (K.scalarExtension f).cycles n := by
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
    ModuleCat.extendScalars.{u, u, u + 1} f.hom
  letI : E.PreservesHomology := linearExtendScalars_preservesHomology f
  intro c
  exact ((K.complex.sc n).mapCyclesIso E).inv
    (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
      (K.complex.cycles n) c)

/-- Send the actual scalar-extended target cycle through the target complex's
canonical homology quotient. -/
noncomputable def classBaseChange
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.complex.cycles n →
      (K.scalarExtension f).homology n := fun c =>
  (K.scalarExtension f).homologyπ n (K.cycleBaseChange f n c)

/-- Characterization of class base change by the canonical unit and the
arbitrary-degree flat homology isomorphism. -/
theorem class_baseChange_naturality
    {R' : Type u} [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat)
    (c : K.complex.cycles n) :
    (K.hnFlatBaseChangeIso f n).hom
        (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
          (K.complex.homology n) (K.complex.homologyπ n c)) =
      K.classBaseChange f n c :=
by
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
    ModuleCat.extendScalars.{u, u, u + 1} f.hom
  letI : E.PreservesHomology := linearExtendScalars_preservesHomology f
  have hunit := ConcreteCategory.congr_hom
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} f.hom).unit.naturality
      (K.complex.homologyπ n)) c
  have hunit' :
      Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
          (K.complex.homology n) (K.complex.homologyπ n c) =
        E.map (K.complex.homologyπ n)
          (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
            (K.complex.cycles n) c) := by
    simpa only [Derived.Intersection.moduleScalarExtensionUnit,
      ConcreteCategory.comp_apply, Functor.id_obj, Functor.id_map] using hunit
  have hπ := ConcreteCategory.congr_hom
    (K.hnFlatBaseChangeIso_homologyπ f n)
    (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
      (K.complex.cycles n) c)
  rw [hunit']
  simpa only [classBaseChange, cycleBaseChange,
    ConcreteCategory.comp_apply] using hπ

end LinearCoverRelativeCechComplex

namespace LinearCoefficientSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

private noncomputable def linearCechProjection
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    ModuleCat.of R
        (∀ τ : (canonicalCoverRelative 𝒰).simplex n,
          Ob.modulePresheaf.obj
            (op ((canonicalCoverRelative 𝒰).overlap n τ))) ⟶
      Ob.modulePresheaf.obj
        (op ((canonicalCoverRelative 𝒰).overlap n σ)) :=
  ModuleCat.ofHom (LinearMap.proj σ)

private noncomputable def linearCechBaseChangeNatTrans
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ((CosimplicialObject.whiskering
      (ModuleCat.{u + 1} R) (ModuleCat.{u + 1} R')).obj
        (ModuleCat.extendScalars.{u, u, u + 1} f.hom)).obj
          (linearCechCosimplicialObject Ob 𝒰) ⟶
      linearCechCosimplicialObject (Ob.baseChange f) 𝒰 where
  app x := ModuleCat.ofHom (LinearMap.pi (R := R') fun σ =>
    (((ModuleCat.extendScalars.{u, u, u + 1} f.hom).map
        (linearCechProjection Ob 𝒰 x.len σ)) ≫
      Ob.baseChangeSectionMap f
        ((canonicalCoverRelative 𝒰).overlap x.len σ)).hom)
  naturality x y g := by
    let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
      ModuleCat.extendScalars.{u, u, u + 1} f.hom
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext σ
    have hproj :
        (linearCechCosimplicialObject Ob 𝒰).map g ≫
            linearCechProjection Ob 𝒰 y.len σ =
          linearCechProjection Ob 𝒰 x.len
              (fun i => σ (g.toOrderHom i)) ≫
            Ob.modulePresheaf.map
              (canonicalTupleOverlapMap 𝒰 g σ).op := by
      apply ModuleCat.hom_ext
      ext c
      rfl
    have hE :
        E.map ((linearCechCosimplicialObject Ob 𝒰).map g) ≫
            E.map (linearCechProjection Ob 𝒰 y.len σ) =
          E.map (linearCechProjection Ob 𝒰 x.len
              (fun i => σ (g.toOrderHom i))) ≫
            E.map (Ob.modulePresheaf.map
              (canonicalTupleOverlapMap 𝒰 g σ).op) := by
      rw [← E.map_comp, hproj, E.map_comp]
    have hEapply :
        (E.map (linearCechProjection Ob 𝒰 y.len σ)).hom
            ((E.map ((linearCechCosimplicialObject Ob 𝒰).map g)).hom z) =
          (E.map (Ob.modulePresheaf.map
              (canonicalTupleOverlapMap 𝒰 g σ).op)).hom
            ((E.map (linearCechProjection Ob 𝒰 x.len
              (fun i => σ (g.toOrderHom i)))).hom z) := by
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom hE z
    have hsection := ConcreteCategory.congr_hom
      (Ob.baseChangeSectionMap_naturality f
        (canonicalTupleOverlapMap 𝒰 g σ))
      ((E.map (linearCechProjection Ob 𝒰 x.len
        (fun i => σ (g.toOrderHom i)))).hom z)
    dsimp [CosimplicialObject.whiskering, Functor.whiskeringRight,
      linearCechCosimplicialObject]
    exact (congrArg
      (fun w => Ob.baseChangeSectionMap f
        ((canonicalCoverRelative 𝒰).overlap y.len σ) w) hEapply).trans
      (by simpa only [ConcreteCategory.comp_apply] using hsection)

/-- The canonical degreewise map from scalar-extended source cochains to the
cochains of the canonically base-changed coefficient sheaf. -/
noncomputable def canonicalBaseChangeCochain
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    ((Ob.canonicalLinearCech 𝒰).scalarExtension f).X n ⟶
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.X n :=
  ((Ob.canonicalLinearCech 𝒰).scalarExtensionObjIso f n).hom ≫
    (linearCechBaseChangeNatTrans Ob f 𝒰).app (SimplexCategory.mk n)

/-- Pointwise formula for the canonical cochain base-change map: project to
one source section after scalar extension, then apply the sectionwise
sheafification unit. -/
theorem canonicalBaseChangeCochain_apply
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (z : ((Ob.canonicalLinearCech 𝒰).scalarExtension f).X n)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (canonicalBaseChangeCochain Ob f 𝒰 n).hom z σ =
      (Ob.baseChangeSectionMap f
        ((canonicalCoverRelative 𝒰).overlap n σ)).hom
        (((ModuleCat.extendScalars f.hom).map
          (ModuleCat.ofHom (LinearMap.proj σ))).hom
          (((Ob.canonicalLinearCech 𝒰).scalarExtensionObjIso f n).hom z)) :=
  rfl

private theorem canonicalBaseChangeCochain_comm
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    ((Ob.canonicalLinearCech 𝒰).scalarExtension f).d n (n + 1) ≫
        canonicalBaseChangeCochain Ob f 𝒰 (n + 1) =
      canonicalBaseChangeCochain Ob f 𝒰 n ≫
        ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.d n (n + 1) := by
  rw [canonicalBaseChangeCochain, canonicalBaseChangeCochain,
    ← Category.assoc,
    (Ob.canonicalLinearCech 𝒰).scalarExtension_d f n]
  simp only [Category.assoc]
  rw [cancel_epi
    ((Ob.canonicalLinearCech 𝒰).scalarExtensionObjIso f n).hom]
  simp only [canonicalLinearCech, CochainComplex.of_d]
  change
    (ModuleCat.extendScalars f.hom).map
          (linearCechDifferential Ob 𝒰 n) ≫
        (linearCechBaseChangeNatTrans Ob f 𝒰).app
          (SimplexCategory.mk (n + 1)) =
      (linearCechBaseChangeNatTrans Ob f 𝒰).app
          (SimplexCategory.mk n) ≫
        linearCechDifferential (Ob.baseChange f) 𝒰 n
  letI := linearExtendScalars_additive f.hom
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
    ModuleCat.extendScalars.{u, u, u + 1} f.hom
  have hsource :
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
          (((CosimplicialObject.whiskering
            (ModuleCat.{u + 1} R) (ModuleCat.{u + 1} R')).obj E).obj
              (linearCechCosimplicialObject Ob 𝒰)) n =
        E.map (linearCechDifferential Ob 𝒰 n) := by
    dsimp [linearCechDifferential,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD,
      CosimplicialObject.whiskering, Functor.whiskeringRight]
    rw [Functor.map_sum]
    simp only [Functor.map_zsmul]
    apply Finset.sum_congr rfl
    intro i _hi
    rfl
  rw [← hsource]
  have hcomm := (AlgebraicTopology.AlternatingCofaceMapComplex.map
    (linearCechBaseChangeNatTrans Ob f 𝒰)).comm' n (n + 1) rfl
  dsimp [AlgebraicTopology.AlternatingCofaceMapComplex.map,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj] at hcomm
  simpa only [CochainComplex.of_d, linearCechDifferential] using hcomm.symm

/-- The canonical complex hom generated by the sectionwise sheafification
unit and its restriction naturality. -/
noncomputable def canonicalCechBaseChangeHom
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (Ob.canonicalLinearCech 𝒰).scalarExtension f ⟶
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex where
  f n := canonicalBaseChangeCochain Ob f 𝒰 n
  comm' i j hij := by
    obtain rfl := hij
    exact (canonicalBaseChangeCochain_comm Ob f 𝒰 i).symm

/-- The components of the canonical complex hom are the named degreewise
base-change maps. -/
theorem canonicalCechBaseChangeHom_f
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (canonicalCechBaseChangeHom Ob f 𝒰).f n =
      canonicalBaseChangeCochain Ob f 𝒰 n :=
  rfl

/-- Coefficient compatibility asks exactly that the canonical degreewise
cochain maps are isomorphisms. -/
def CechCoefficientBaseChangeCompatible
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) : Prop :=
  ∀ n, IsIso (canonicalBaseChangeCochain Ob f 𝒰 n)

/-- Finite Čech products commute with scalar extension when the raw
sectionwise extension is already a sheaf. -/
theorem cechCoefficientBaseChangeCompatible_of_finite_raw_isSheaf
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [Fintype 𝒰.Index]
    (hraw : Presheaf.IsSheaf S.topology
      (Ob.rawBaseChangePresheaf f ⋙
        forget₂ (ModuleCat.{u + 1} R') AddCommGrpCat.{u + 1})) :
    CechCoefficientBaseChangeCompatible Ob f 𝒰 := by
  classical
  haveI (W : S.category) : IsIso (Ob.baseChangeSectionMap f W) := by
    change IsIso
      ((moduleSheafificationUnit (Ob.rawBaseChangePresheaf f)).app (op W))
    let e := moduleSheafificationUnitIso
      (Ob.rawBaseChangePresheaf f) hraw
    change IsIso (e.hom.app (op W))
    infer_instance
  intro n
  let I := (canonicalCoverRelative 𝒰).simplex n
  let M : I → Type (u + 1) := fun σ ↦
    Ob.modulePresheaf.obj
      (op ((canonicalCoverRelative 𝒰).overlap n σ))
  let N : I → Type (u + 1) := fun σ ↦
    (Ob.baseChange f).modulePresheaf.obj
      (op ((canonicalCoverRelative 𝒰).overlap n σ))
  letI : Algebra R R' := f.hom.toAlgebra
  letI : Fintype I := by
    dsimp [I]
    infer_instance
  let epi :
      (ModuleCat.extendScalars f.hom).obj
          (ModuleCat.of R (∀ σ : I, M σ)) ≅
        ModuleCat.of R'
          (∀ σ : I,
            (ModuleCat.extendScalars f.hom).obj
              (ModuleCat.of R (M σ))) :=
    (TensorProduct.piRight R R' R' M).toModuleIso
  let esec :
      ModuleCat.of R'
          (∀ σ : I,
            (ModuleCat.extendScalars f.hom).obj
              (ModuleCat.of R (M σ))) ≅
        ModuleCat.of R' (∀ σ : I, N σ) :=
    (LinearEquiv.piCongrRight fun σ ↦
      (asIso (Ob.baseChangeSectionMap f
        ((canonicalCoverRelative 𝒰).overlap n σ))).toLinearEquiv).toModuleIso
  have heq :
      canonicalBaseChangeCochain Ob f 𝒰 n =
        ((Ob.canonicalLinearCech 𝒰).scalarExtensionObjIso f n).hom ≫
          epi.hom ≫ esec.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul s m =>
        change
          (fun σ : I ↦
            (Ob.baseChangeSectionMap f
              ((canonicalCoverRelative 𝒰).overlap n σ)).hom
                (s ⊗ₜ[R] m σ)) =
          (fun σ : I ↦
            (Ob.baseChangeSectionMap f
              ((canonicalCoverRelative 𝒰).overlap n σ)).hom
                (s ⊗ₜ[R] m σ))
        rfl
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
  rw [heq]
  infer_instance

/-- The canonical Hn map: flat homology comparison followed by the homology
map of the canonical coefficient complex hom. -/
noncomputable def canonicalCechHnBaseChangeMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    moduleScalarExtension f
        ((Ob.canonicalLinearCech 𝒰).complex.homology n) ⟶
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homology n :=
  ((Ob.canonicalLinearCech 𝒰).hnFlatBaseChangeIso f n).hom ≫
    HomologicalComplex.homologyMap
      (canonicalCechBaseChangeHom Ob f 𝒰) n

/-- The actual target cocycle obtained from the flat scalar-extension cycle
and the canonical coefficient complex hom. -/
noncomputable def canonicalCocycleBaseChange
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.cycles n →
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.cycles n := fun c =>
  HomologicalComplex.cyclesMap
    (canonicalCechBaseChangeHom Ob f 𝒰) n
    ((Ob.canonicalLinearCech 𝒰).cycleBaseChange f n c)

/-- The canonical base-changed cocycle is obtained sectionwise by applying
the scalar-extension unit followed by the canonical sheafification section map. -/
theorem canonicalCocycleBaseChange_iCycles_apply
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.cycles n)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.iCycles n).hom
        (canonicalCocycleBaseChange Ob f 𝒰 n c) σ =
      Ob.baseChangeSectionMap f
        ((canonicalCoverRelative 𝒰).overlap n σ)
        ((1 : R') ⊗ₜ[R, f.hom]
          (((Ob.canonicalLinearCech 𝒰).complex.iCycles n).hom c σ)) := by
  let K := Ob.canonicalLinearCech 𝒰
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R' :=
    ModuleCat.extendScalars.{u, u, u + 1} f.hom
  letI : E.PreservesHomology := linearExtendScalars_preservesHomology f
  have hcycle := ConcreteCategory.congr_hom
    ((K.complex.sc n).mapCyclesIso_hom_iCycles E)
    (K.cycleBaseChange f n c)
  have hcycle' :
      ((K.scalarExtension f).iCycles n).hom (K.cycleBaseChange f n c) =
        (E.map (K.complex.iCycles n)).hom
          (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
            f (K.complex.cycles n) c) := by
    calc
      _ = (E.map (K.complex.iCycles n)).hom
          (((K.complex.sc n).mapCyclesIso E).hom
            (K.cycleBaseChange f n c)) := hcycle.symm
      _ = _ := by
        change (E.map (K.complex.iCycles n)).hom
          (((K.complex.sc n).mapCyclesIso E).hom
            (((K.complex.sc n).mapCyclesIso E).inv
              (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
                f (K.complex.cycles n) c))) = _
        rw [Iso.inv_hom_id_apply]
  have hmap := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (canonicalCechBaseChangeHom Ob f 𝒰) n)
    (K.cycleBaseChange f n c)
  have hmap' :
      (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.iCycles n).hom
          (HomologicalComplex.cyclesMap
            (canonicalCechBaseChangeHom Ob f 𝒰) n
            (K.cycleBaseChange f n c)) σ =
        ((canonicalCechBaseChangeHom Ob f 𝒰).f n).hom
          (((K.scalarExtension f).iCycles n).hom
            (K.cycleBaseChange f n c)) σ := by
    simpa only [ConcreteCategory.comp_apply] using congrArg (fun z => z σ) hmap
  rw [canonicalCocycleBaseChange]
  rw [hmap']
  rw [hcycle']
  rfl

/-- The canonical cocycle map represents the image of the source class under
the canonical Hn base-change map. -/
theorem canonicalCocycleBaseChange_class
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.cycles n) :
    ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homologyπ n
        (canonicalCocycleBaseChange Ob f 𝒰 n c) =
      canonicalCechHnBaseChangeMap Ob f 𝒰 n
        (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
          ((Ob.canonicalLinearCech 𝒰).complex.homology n)
          ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n c)) := by
  let K := Ob.canonicalLinearCech 𝒰
  have hclass := K.class_baseChange_naturality f n c
  have hπ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (φ := canonicalCechBaseChangeHom Ob f 𝒰) (i := n))
    (K.cycleBaseChange f n c)
  simpa only [canonicalCocycleBaseChange, canonicalCechHnBaseChangeMap,
    LinearCoverRelativeCechComplex.classBaseChange,
    ConcreteCategory.comp_apply] using hπ.symm.trans
      (congrArg
        (fun z => HomologicalComplex.homologyMap
          (canonicalCechBaseChangeHom Ob f 𝒰) n z) hclass.symm)

/-- Degreewise coefficient compatibility makes the canonical Hn map an
isomorphism in every degree. -/
theorem canonicalCechHnBaseChangeMap_isIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (n : Nat) :
    IsIso (canonicalCechHnBaseChangeMap Ob f 𝒰 n) := by
  letI (m : Nat) : IsIso
      ((canonicalCechBaseChangeHom Ob f 𝒰).f m) := by
    rw [canonicalCechBaseChangeHom_f]
    exact hcompat m
  letI : IsIso (canonicalCechBaseChangeHom Ob f 𝒰) :=
    HomologicalComplex.Hom.isIso_of_components _
  dsimp only [canonicalCechHnBaseChangeMap]
  infer_instance

/-- The canonical arbitrary-degree flat Čech homology base-change
isomorphism under coefficient compatibility. -/
noncomputable def canonicalCechHnFlatBaseChangeIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (n : Nat) :
    moduleScalarExtension f
        ((Ob.canonicalLinearCech 𝒰).complex.homology n) ≅
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homology n := by
  letI : IsIso (canonicalCechHnBaseChangeMap Ob f 𝒰 n) :=
    canonicalCechHnBaseChangeMap_isIso Ob f 𝒰 hcompat n
  exact asIso (canonicalCechHnBaseChangeMap Ob f 𝒰 n)

end LinearCoefficientSheaf

end Cohomology

end

end AAT.AG
