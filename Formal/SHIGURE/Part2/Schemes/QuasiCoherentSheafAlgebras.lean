import Formal.SHIGURE.Part2.Schemes.AffineModuleSections
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Formal.SHIGURE.Part2.Schemes.AlgebraModule
import Formal.SHIGURE.Part2.Schemes.RelativeSpecSheaves

/-! # Quasi-coherence of actual algebra sheaves

The underlying module criterion yields principal-open localization of
the original algebras of sections. The resulting affine-site algebra
is the input to the relative spectrum construction.

## Implementation notes

We derive the ring localization from the underlying module localization
and the actual ring restriction map. The affine-site equivalence then
recovers the input algebra sheaf and its structure morphism.
`AffineAlgebraPresentations` then identifies its algebra restrictions
with the algebras associated to the original affine sections.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

variable {X : Scheme.{u}}

/-- A sheaf of algebras is quasi-coherent when its actual module is quasi-coherent.
This is the quasi-coherence condition of Lemma B.7 on an algebra under the structure sheaf. -/
def IsQuasiCoherentSheafAlgebra (C : Under X.sheaf) : Prop :=
  IsQuasiCoherentModule (algebraUnderlyingModule C)

/-- Affine-local tilde presentations of the underlying module determine
quasi-coherence of the algebra on the whole scheme.
This is the underlying-module form of the algebra cover criterion in the opening of Appendix B
and Lemma B.7. -/
theorem isQuasiCoherentSheafAlgebra_iff_affineCover (C : Under X.sheaf) :
    IsQuasiCoherentSheafAlgebra C ↔ HasAffineTildeCover (algebraUnderlyingModule C) :=
  isQuasiCoherentModule_iff_affineCover (algebraUnderlyingModule C)

/-- The section algebra on a principal open is the localization of the
original section algebra at the image of the specified scalar.
This proves the principal-open localization step of Lemma B.7. Quasi-coherence of the underlying
module supplies the localization of the original section ring. -/
theorem sheafAlgebra_localizes (C : Under X.sheaf) (qc : IsQuasiCoherentSheafAlgebra C)
    {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    let F := C.right.val
    let action : Γ(X, U) ⟶ F.obj (op U) := C.hom.val.app (op U)
    letI := (F.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    IsLocalization.Away (action r) (F.obj (op (X.basicOpen r))) := by
  let R := Γ(X, U)
  let V := X.basicOpen r
  let incl : op U ⟶ op V := (homOfLE (X.basicOpen_le r)).op
  let F := C.right.val
  let A := F.obj (op U)
  let B := F.obj (op V)
  let a : R ⟶ A := C.hom.val.app (op U)
  let b : R ⟶ B := X.presheaf.map incl ≫ C.hom.val.app (op V)
  let f : A ⟶ B := F.map incl
  letI : Algebra R A := a.hom.toAlgebra
  letI : Algebra R B := b.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (by
    change b.hom = f.hom.comp a.hom
    exact congrArg CommRingCat.Hom.hom (C.hom.val.naturality incl))
  have source : HasTildeOn (algebraUnderlyingModule C) hU := qc ⟨U, hU⟩
  have localizes := affineSections_localize hU (algebraUnderlyingModule C) source r
  have compatible : IsLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom R A B).toLinearMap :=
    localizes
  have localization := isLocalizedModule_iff_isLocalization.mp compatible
  change IsLocalization.Away (a r) B
  change IsLocalization ((Submonoid.powers r).map a.hom) B at localization
  rw [Submonoid.map_powers] at localization
  exact localization

/-- Restrict the actual section algebras to the affine site with their
proved localization maps, ready for the relative spectrum.
This is the input conversion for Lemma B.7. The actual quasi-coherence hypothesis supplies the
required localization proof. -/
def QuasiCoherentAlgebra.ofSheaf (C : Under X.sheaf) (qc : IsQuasiCoherentSheafAlgebra C) :
    QuasiCoherentAlgebra X where
  sections := (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ C.right.val
  algebra := Functor.whiskerLeft (Scheme.AffineZariskiSite.toOpensFunctor X).op C.hom.val
  localization U r := sheafAlgebra_localizes C qc U.property r

/-- Reconstructing the algebra sheaf from its affine-site sections returns
the original algebra and its original structure morphism.
This is the reconstruction comparison in Lemma B.7. The affine site supplies the local ring and
structure-map identifications. -/
def QuasiCoherentAlgebra.ofSheaf_algebraSheafIso (C : Under X.sheaf)
    (qc : IsQuasiCoherentSheafAlgebra C) : (QuasiCoherentAlgebra.ofSheaf C qc).algebraSheaf ≅ C := by
  let E := Scheme.AffineZariskiSite.sheafEquiv (X := X) (A := CommRingCat.{u})
  let R := Under.post (X := X.sheaf) E.inverse
  apply R.preimageIso
  exact (QuasiCoherentAlgebra.ofSheaf C qc).affineAlgebraSheafIso

end

end SHIGURE.SchemeDescent
