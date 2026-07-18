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

end LinearCoefficientSheaf

end Cohomology

end

end AAT.AG
