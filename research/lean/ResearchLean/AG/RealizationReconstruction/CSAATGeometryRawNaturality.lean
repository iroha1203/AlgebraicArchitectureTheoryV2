import ResearchLean.AG.RealizationReconstruction.CSAATGeometryRawIntegration
import Formal.Util.AssertStandardAxioms

/-!
# Restriction naturality for the concrete CS raw-algebra readings

Cycle 132 identified every objectwise empty-structural quotient with the full
Law coordinate polynomial ring.  This file proves that those identifications
commute with every morphism of the selected AAT site.  The result is quantified
over the whole site and then specialized to both concrete CS readings; it is
not a statement about a selected cover arrow or a post-selected family of
representable morphisms.

This is the naturality equation needed to package a presheaf comparison.  It
does not itself construct a geometry morphism, a readback, a `ReadingCore`, or
the terminal A--F conjunction.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Generic restriction naturality on the full selected site -/

/-- The Cycle 132 quotient equivalences intertwine every descended raw
restriction with the corresponding polynomial restriction. -/
theorem equationCoordinateRawQuotientEquiv_natural
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) {W V : S.category} (f : W ⟶ V) :
    (equationCoordinateRawQuotientEquiv S W).toRingEquiv.toRingHom.comp
        ((equationCoordinateRawSystemOn S).restrictionStable f).quotientDesc =
      (equationCoordinateRawRestriction S f).polynomialMap.comp
        (equationCoordinateRawQuotientEquiv S V).toRingEquiv.toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro polynomial
  change equationCoordinateRawQuotientEquiv S W
      (((equationCoordinateRawSystemOn S).restrictionStable f).quotientDesc
        ((emptyStructuralRelationFamilyOn S V).quotientMap polynomial)) =
    (equationCoordinateRawRestriction S f).polynomialMap
      (equationCoordinateRawQuotientEquiv S V
        ((emptyStructuralRelationFamilyOn S V).quotientMap polynomial))
  change equationCoordinateRawQuotientEquiv S W
      ((emptyStructuralRestrictionStableOn S f).quotientDesc
        ((emptyStructuralRelationFamilyOn S V).quotientMap polynomial)) = _
  rw [LawAlgebra.RestrictionStableStructuralRelations.quotientDesc_mk]
  change equationCoordinateRawQuotientEquiv S W
      ((emptyStructuralRelationFamilyOn S W).quotientMap
        ((equationCoordinateRawRestriction S f).polynomialMap polynomial)) = _
  rw [equationCoordinateRawQuotientEquiv_quotientMap,
    equationCoordinateRawQuotientEquiv_quotientMap]

/-- For this raw system every polynomial restriction is the identity, so the
generic naturality square has an identity bottom edge. -/
theorem equationCoordinateRawQuotientEquiv_natural_identity
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) {W V : S.category} (f : W ⟶ V) :
    (equationCoordinateRawQuotientEquiv S W).toRingEquiv.toRingHom.comp
        ((equationCoordinateRawSystemOn S).restrictionStable f).quotientDesc =
      (equationCoordinateRawQuotientEquiv S V).toRingEquiv.toRingHom := by
  rw [equationCoordinateRawQuotientEquiv_natural S f,
    equationCoordinateRawRestriction_polynomialMap S f]
  apply RingHom.ext
  intro polynomial
  rfl

/-- Pointwise form of restriction naturality under the quotient/free
identifications. -/
@[simp] theorem equationCoordinateRawQuotientEquiv_quotientDesc
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) {W V : S.category} (f : W ⟶ V)
    (x : (equationCoordinateRawSystemOn S).rawAlgebra V) :
    equationCoordinateRawQuotientEquiv S W
        (((equationCoordinateRawSystemOn S).restrictionStable f).quotientDesc x) =
      equationCoordinateRawQuotientEquiv S V x := by
  simpa only [RingHom.comp_apply] using congrArg (fun g => g x)
    (equationCoordinateRawQuotientEquiv_natural_identity S f)

/-! ## Exact lens and protocol specializations -/

/-- Naturality holds for every context morphism of the concrete lens reading
site, not only for arrows chosen by a cover. -/
theorem lensAATGeometryReadingRawQuotientEquiv_natural
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    {W V : (lensAATGeometryReadingSite input X).category} (f : W ⟶ V)
    (x : (lensAATGeometryReadingRawSystem input X).rawAlgebra V) :
    lensAATGeometryReadingRawQuotientEquiv input X W
        (((lensAATGeometryReadingRawSystem input X).restrictionStable f).quotientDesc x) =
      lensAATGeometryReadingRawQuotientEquiv input X V x :=
  equationCoordinateRawQuotientEquiv_quotientDesc
    (lensAATGeometryReadingSite input X) f x

/-- Naturality holds for every context morphism of the concrete protocol
reading site, including the non-invertible protocol maps retained by the
reading construction. -/
theorem protocolAATGeometryReadingRawQuotientEquiv_natural
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    {W V : (protocolAATGeometryReadingSite input X).category} (f : W ⟶ V)
    (x : (protocolAATGeometryReadingRawSystem input X).rawAlgebra V) :
    protocolAATGeometryReadingRawQuotientEquiv input X W
        (((protocolAATGeometryReadingRawSystem input X).restrictionStable f).quotientDesc x) =
      protocolAATGeometryReadingRawQuotientEquiv input X V x :=
  equationCoordinateRawQuotientEquiv_quotientDesc
    (protocolAATGeometryReadingSite input X) f x

/-! ## Presheaf-level packaging -/

/-- The full Law coordinate polynomial algebra at a site object, with its
canonical lifted-integer structure map.  The object carrier is independent of
the context; the context index records which component of the presheaf is
being described. -/
noncomputable def equationCoordinatePolynomialObject
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (W : S.category) :
    LawAlgebra.AATCommAlgCat Int :=
  CategoryTheory.Under.mk (CommRingCat.ofHom
    (((MvPolynomial.C : Int →+*
      LawAlgebra.FreeTypedCommAlg (equationCoordinateRawFamily S W) Int)).comp
        ULift.ringEquiv.toRingHom))

/-- The polynomial endpoint presheaf.  All restriction maps are identities on
the full equation-index/Atom coordinate polynomial ring. -/
noncomputable def equationCoordinatePolynomialPresheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) : LawAlgebra.AlgebraValuedAATPresheaf S Int where
  obj W := equationCoordinatePolynomialObject S W.unop
  map {X Y} f := CategoryTheory.Under.homMk
    (CommRingCat.ofHom (RingHom.id _)) (by
      ext value
      rfl)
  map_id X := by
    apply CategoryTheory.Under.UnderMorphism.ext
    rfl
  map_comp f g := by
    apply CategoryTheory.Under.UnderMorphism.ext
    rfl

/-- Objectwise, the quotient/free algebra equivalence is an isomorphism in
the lifted-integer under-category. -/
noncomputable def equationCoordinatePolynomialObjectIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (W : S.category) :
    (equationCoordinateRawSystemOn S).toPresheaf.obj (Opposite.op W) ≅
      equationCoordinatePolynomialObject S W :=
  CategoryTheory.Under.isoMk
    (equationCoordinateRawQuotientEquiv S W).toRingEquiv.toCommRingCatIso
    (by
      ext value
      change equationCoordinateRawQuotientEquiv S W
          ((emptyStructuralRelationFamilyOn S W).quotientMap
            (MvPolynomial.C value.down)) = MvPolynomial.C value.down
      rw [equationCoordinateRawQuotientEquiv_quotientMap])

/-- The raw quotient presheaf is naturally isomorphic to the full Law
coordinate polynomial presheaf.  Naturality is proved for every morphism of
the selected AAT site. -/
noncomputable def equationCoordinateRawPresheafIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) :
    (equationCoordinateRawSystemOn S).toPresheaf ≅
      equationCoordinatePolynomialPresheaf S := by
  refine NatIso.ofComponents
    (fun W => equationCoordinatePolynomialObjectIso S W.unop) ?_
  intro X Y f
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  change (equationCoordinateRawQuotientEquiv S Y.unop).toRingEquiv.toRingHom.comp
      ((equationCoordinateRawSystemOn S).restrictionStable f.unop).quotientDesc =
    (equationCoordinateRawQuotientEquiv S X.unop).toRingEquiv.toRingHom
  exact equationCoordinateRawQuotientEquiv_natural_identity S f.unop

/-- Presheaf-level raw/polynomial comparison for the concrete lens reading. -/
noncomputable def lensAATGeometryReadingRawPresheafIso
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATGeometryReadingRawSystem input X).toPresheaf ≅
      equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input X) :=
  equationCoordinateRawPresheafIso (lensAATGeometryReadingSite input X)

/-- Presheaf-level raw/polynomial comparison for the concrete protocol
reading, with the same construction used for the lens reading. -/
noncomputable def protocolAATGeometryReadingRawPresheafIso
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolAATGeometryReadingRawSystem input X).toPresheaf ≅
      equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input X) :=
  equationCoordinateRawPresheafIso (protocolAATGeometryReadingSite input X)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
