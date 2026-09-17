import Mathlib.CategoryTheory.Equivalence
import ResearchLean.AG.RealizationReconstruction.AATClosedRealizationCategory
import Formal.Util.AssertStandardAxioms

/-!
# The general local-model reconstruction spine

A local model is a contravariant diagram on an independently supplied
restriction category.  Its objects are restriction-compatible local values,
and its morphisms are natural transformations, so identities and composition
are componentwise and coherence contains no global extension witness.

For a reading functor into this category, morphism separation, morphism
assembly, object separation, and object assembly are stated independently.
Morphism separation and assembly give the explicit `read`/`assemble` Hom
equivalence; adding object assembly gives the categorical equivalence.

This is the general spine allowed by G-124(B).  It does not construct the
actual AAT local index, finite typed local values, primitive reading functor,
or the A-derived proofs of separation and assembly.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe uΛ uV uR vΛ vV vR

/-- Local models on a restriction category are contravariant diagrams of
local values.  Functoriality is restriction coherence, and naturality is the
coherence condition for local morphism families. -/
abbrev LocalModelCategory (Λ : Type uΛ) [Category.{vΛ} Λ]
    (V : Type uV) [Category.{vV} V] :=
  Λᵒᵖ ⥤ V

/-- Type of possible G-124(A--B) reading functors from the accepted closed
realization category into an independently chosen local-model category.
This alias supplies only the type of the connection, not an actual reading. -/
abbrev ClosedFamilyLocalReading
    (theta : ClosedFamilyParameter.{uR, vR})
    (Λ : Type uΛ) [Category.{vΛ} Λ]
    (V : Type uV) [Category.{vV} V] :=
  FamilyRealization theta ⥤ LocalModelCategory Λ V

namespace LocalReading

variable {R : Type uR} [Category.{vR} R]
variable {Λ : Type uΛ} [Category.{vΛ} Λ]
variable {V : Type uV} [Category.{vV} V]

/-- Local reading separates morphisms when its map on every Hom type is
injective.  This is uniqueness, stated independently of assembly. -/
def MorphismSeparates (N : R ⥤ LocalModelCategory Λ V) : Prop :=
  ∀ X Y, Function.Injective
    (N.map : (X ⟶ Y) → (N.obj X ⟶ N.obj Y))

/-- Local reading assembles morphisms when every coherent local natural
transformation is the reading of a global morphism.  This is existence,
stated independently of separation. -/
def MorphismAssembles (N : R ⥤ LocalModelCategory Λ V) : Prop :=
  ∀ X Y, Function.Surjective
    (N.map : (X ⟶ Y) → (N.obj X ⟶ N.obj Y))

/-- Local reading separates objects up to isomorphism when a local-model
isomorphism between two readings lifts to a global isomorphism. -/
def ObjectSeparates (N : R ⥤ LocalModelCategory Λ V) : Prop :=
  ∀ X Y, Nonempty (N.obj X ≅ N.obj Y) → Nonempty (X ≅ Y)

/-- Local reading assembles objects when every local model is isomorphic to
the reading of some global realization.  This is the object-existence part
of reconstruction and contains no chosen assembler. -/
def ObjectAssembles (N : R ⥤ LocalModelCategory Λ V) : Prop :=
  ∀ Z, ∃ X, Nonempty (N.obj X ≅ Z)

/-- Morphism separation supplies the faithful-functor interface without
changing the independently stated separation predicate. -/
def faithfulOfMorphismSeparates (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) : N.Faithful where
  map_injective := fun {X Y} => hsep X Y

/-- Morphism assembly supplies the full-functor interface without replacing
the independently stated assembly predicate. -/
def fullOfMorphismAssembles (N : R ⥤ LocalModelCategory Λ V)
    (hasm : MorphismAssembles N) : N.Full where
  map_surjective := fun {X Y} => hasm X Y

/-- Object assembly supplies essential surjectivity without choosing a global
realization inside the definition of a local model. -/
def essSurjOfObjectAssembles (N : R ⥤ LocalModelCategory Λ V)
    (hasm : ObjectAssembles N) : N.EssSurj :=
  Functor.EssSurj.mk hasm

/-- Reading and assembly give an explicit equivalence on each Hom type once
the separately stated uniqueness and existence properties are available. -/
noncomputable def homEquiv (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasm : MorphismAssembles N)
    (X Y : R) :
    (X ⟶ Y) ≃ (N.obj X ⟶ N.obj Y) :=
  Equiv.ofBijective N.map ⟨hsep X Y, hasm X Y⟩

/-- The forward Hom equivalence is exactly primitive reading by the functor. -/
@[simp] theorem homEquiv_apply (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasm : MorphismAssembles N)
    {X Y : R} (f : X ⟶ Y) :
    homEquiv N hsep hasm X Y f = N.map f :=
  rfl

/-- Reading an assembled local morphism returns the original coherent local
morphism. -/
@[simp] theorem read_assemble (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasm : MorphismAssembles N)
    {X Y : R} (f : N.obj X ⟶ N.obj Y) :
    N.map ((homEquiv N hsep hasm X Y).symm f) = f :=
  (homEquiv N hsep hasm X Y).apply_symm_apply f

/-- Assembling the reading of a global morphism returns that global morphism. -/
@[simp] theorem assemble_read (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasm : MorphismAssembles N)
    {X Y : R} (f : X ⟶ Y) :
    (homEquiv N hsep hasm X Y).symm (N.map f) = f :=
  (homEquiv N hsep hasm X Y).symm_apply_apply f

/-- Morphism separation and assembly lift every isomorphism between local
readings to an isomorphism between the corresponding global objects. -/
noncomputable def objectIsoOfLocalIso
    (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasm : MorphismAssembles N)
    {X Y : R} (e : N.obj X ≅ N.obj Y) : X ≅ Y := by
  letI : N.Faithful := faithfulOfMorphismSeparates N hsep
  letI : N.Full := fullOfMorphismAssembles N hasm
  exact N.preimageIso e

/-- The morphism reconstruction laws imply object separation up to
isomorphism; this conclusion is kept distinct from object assembly. -/
theorem objectSeparates_of_morphism_reconstruction
    (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasm : MorphismAssembles N) :
    ObjectSeparates N := by
  intro X Y e
  exact ⟨objectIsoOfLocalIso N hsep hasm e.some⟩

/-- The general G-124(B) reconstruction theorem: morphism uniqueness,
morphism existence, and object existence turn the original reading functor
into an equivalence of categories. -/
noncomputable def reconstructionEquivalence
    (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasmHom : MorphismAssembles N)
    (hasmObj : ObjectAssembles N) :
    R ≌ LocalModelCategory Λ V := by
  letI : N.Faithful := faithfulOfMorphismSeparates N hsep
  letI : N.Full := fullOfMorphismAssembles N hasmHom
  letI : N.EssSurj := essSurjOfObjectAssembles N hasmObj
  letI : N.IsEquivalence := {}
  exact N.asEquivalence

/-- The functor of the reconstructed equivalence is definitionally the
original primitive reading functor. -/
@[simp] theorem reconstructionEquivalence_functor
    (N : R ⥤ LocalModelCategory Λ V)
    (hsep : MorphismSeparates N) (hasmHom : MorphismAssembles N)
    (hasmObj : ObjectAssembles N) :
    (reconstructionEquivalence N hsep hasmHom hasmObj).functor = N :=
  rfl

end LocalReading

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.LocalReading
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
