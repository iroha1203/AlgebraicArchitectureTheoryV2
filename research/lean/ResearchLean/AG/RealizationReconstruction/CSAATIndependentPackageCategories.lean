import ResearchLean.AG.RealizationReconstruction.CSAATIndependentDirectedReadback
import Mathlib.CategoryTheory.Endomorphism
import Formal.Util.AssertStandardAxioms

/-!
# Categories of independent generated package morphisms

The Cycle 176 hom-set equivalences are made identity- and
composition-compatible here.  Separate object wrappers avoid installing a
second category instance on the independently defined CS realization types.
The semantic functors are proved full and faithful from the constructed
round trips, and therefore induce genuine endpoint automorphism group
equivalences.  No automorphism or comparison-group equivalence is accepted as
an input field.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Lens package category -/

/-- A wrapper used only to carry the generated-package Hom category. -/
@[ext]
structure LensAATIndependentPackageObject (input : LensFamilyInput.{u}) where
  realization : LensRealization input.View input.reference

namespace LensAATIndependentGeneratedPackageHom

def id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    LensAATIndependentGeneratedPackageHom input X X :=
  ofSemanticHom (𝟙 X)

def comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATIndependentGeneratedPackageHom input X Y)
    (g : LensAATIndependentGeneratedPackageHom input Y Z) :
    LensAATIndependentGeneratedPackageHom input X Z :=
  ofSemanticHom (f.toSemanticHom ≫ g.toSemanticHom)

end LensAATIndependentGeneratedPackageHom

instance lensAATIndependentPackageCategory (input : LensFamilyInput.{u}) :
    Category (LensAATIndependentPackageObject input) where
  Hom X Y := LensAATIndependentGeneratedPackageHom
    input X.realization Y.realization
  id X := LensAATIndependentGeneratedPackageHom.id X.realization
  comp f g := LensAATIndependentGeneratedPackageHom.comp f g
  id_comp f := by
    ext state
    rfl
  comp_id f := by
    ext state
    rfl
  assoc f g h := by
    ext state
    rfl

/-- Forget the object wrapper and read every generated package Hom back as
the independently defined semantic lens Hom. -/
def lensAATIndependentPackageSemanticFunctor (input : LensFamilyInput.{u}) :
    LensAATIndependentPackageObject input ⥤
      LensRealization input.View input.reference where
  obj X := X.realization
  map f := f.toSemanticHom
  map_id X := by
    apply LensRealization.Hom.ext
    funext state
    rfl
  map_comp f g := by
    apply LensRealization.Hom.ext
    funext state
    rfl

def lensAATIndependentPackageSemanticFullyFaithful
    (input : LensFamilyInput.{u}) :
    (lensAATIndependentPackageSemanticFunctor input).FullyFaithful where
  preimage f := LensAATIndependentGeneratedPackageHom.ofSemanticHom f
  map_preimage f :=
    LensAATIndependentGeneratedPackageHom.toSemanticHom_ofSemanticHom f
  preimage_map f :=
    LensAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom f

instance lensAATIndependentPackageSemanticFunctor_faithful
    (input : LensFamilyInput.{u}) :
    (lensAATIndependentPackageSemanticFunctor input).Faithful where
  map_injective :=
    (lensAATIndependentPackageSemanticFullyFaithful input).map_injective

instance lensAATIndependentPackageSemanticFunctor_full
    (input : LensFamilyInput.{u}) :
    (lensAATIndependentPackageSemanticFunctor input).Full where
  map_surjective :=
    (lensAATIndependentPackageSemanticFullyFaithful input).map_surjective

/-- The full and faithful generated-package readback induces the exact
endpoint automorphism group equivalence. -/
noncomputable def lensAATIndependentPackageAutMulEquiv
    (input : LensFamilyInput.{u})
    (X : LensAATIndependentPackageObject input) :
    Aut X ≃* Aut X.realization :=
  (lensAATIndependentPackageSemanticFullyFaithful input).autMulEquivOfFullyFaithful X

@[simp] theorem lensAATIndependentPackageAutMulEquiv_hom
    (input : LensFamilyInput.{u})
    (X : LensAATIndependentPackageObject input) (a : Aut X) :
    (lensAATIndependentPackageAutMulEquiv input X a).hom =
      (lensAATIndependentPackageSemanticFunctor input).map a.hom :=
  rfl

/-! ## Protocol package category -/

/-- Protocol object wrapper carrying the independent generated-package Hom
category without replacing the original semantic category. -/
@[ext]
structure ProtocolAATIndependentPackageObject (input : ProtocolFamilyInput.{u}) where
  realization : ProtocolRealization input.schema input.observation

namespace ProtocolAATIndependentGeneratedPackageHom

def id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    ProtocolAATIndependentGeneratedPackageHom input X X :=
  ofSemanticHom (𝟙 X)

def comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATIndependentGeneratedPackageHom input X Y)
    (g : ProtocolAATIndependentGeneratedPackageHom input Y Z) :
    ProtocolAATIndependentGeneratedPackageHom input X Z :=
  ofSemanticHom (f.toSemanticHom ≫ g.toSemanticHom)

end ProtocolAATIndependentGeneratedPackageHom

instance protocolAATIndependentPackageCategory (input : ProtocolFamilyInput.{u}) :
    Category (ProtocolAATIndependentPackageObject input) where
  Hom X Y := ProtocolAATIndependentGeneratedPackageHom
    input X.realization Y.realization
  id X := ProtocolAATIndependentGeneratedPackageHom.id X.realization
  comp f g := ProtocolAATIndependentGeneratedPackageHom.comp f g
  id_comp f := by
    ext vertex state
    rfl
  comp_id f := by
    ext vertex state
    rfl
  assoc f g h := by
    ext vertex state
    rfl

/-- Protocol package readback as a functor on every object and every quotient
execution morphism. -/
def protocolAATIndependentPackageSemanticFunctor
    (input : ProtocolFamilyInput.{u}) :
    ProtocolAATIndependentPackageObject input ⥤
      ProtocolRealization input.schema input.observation where
  obj X := X.realization
  map f := f.toSemanticHom
  map_id X := by
    apply ProtocolRealization.Hom.ext
    apply NatTrans.ext
    funext object state
    rfl
  map_comp f g := by
    apply ProtocolRealization.Hom.ext
    apply NatTrans.ext
    funext object state
    rfl

def protocolAATIndependentPackageSemanticFullyFaithful
    (input : ProtocolFamilyInput.{u}) :
    (protocolAATIndependentPackageSemanticFunctor input).FullyFaithful where
  preimage f := ProtocolAATIndependentGeneratedPackageHom.ofSemanticHom f
  map_preimage f :=
    ProtocolAATIndependentGeneratedPackageHom.toSemanticHom_ofSemanticHom f
  preimage_map f :=
    ProtocolAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom f

instance protocolAATIndependentPackageSemanticFunctor_faithful
    (input : ProtocolFamilyInput.{u}) :
    (protocolAATIndependentPackageSemanticFunctor input).Faithful where
  map_injective :=
    (protocolAATIndependentPackageSemanticFullyFaithful input).map_injective

instance protocolAATIndependentPackageSemanticFunctor_full
    (input : ProtocolFamilyInput.{u}) :
    (protocolAATIndependentPackageSemanticFunctor input).Full where
  map_surjective :=
    (protocolAATIndependentPackageSemanticFullyFaithful input).map_surjective

/-- Protocol endpoint automorphisms are recovered as a group, not merely as a
set of bijective carrier maps. -/
noncomputable def protocolAATIndependentPackageAutMulEquiv
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolAATIndependentPackageObject input) :
    Aut X ≃* Aut X.realization :=
  (protocolAATIndependentPackageSemanticFullyFaithful input).autMulEquivOfFullyFaithful X

@[simp] theorem protocolAATIndependentPackageAutMulEquiv_hom
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolAATIndependentPackageObject input) (a : Aut X) :
    (protocolAATIndependentPackageAutMulEquiv input X a).hom =
      (protocolAATIndependentPackageSemanticFunctor input).map a.hom :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
