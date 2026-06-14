import Formal.AG.SingularityMonodromyStack.CodebaseEssence
import Formal.AG.Cohomology.Cohomology

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/-- VI.定義15.1: selected kinds of decomposition equivalence. -/
inductive DecompositionEquivalenceKind where
  | refactor
  | semantic
  | boundaryPreserving
deriving DecidableEq

/--
VI.定義15.1: fiber admissible decomposition groupoid.

The objects are selected fiber decompositions and morphisms are selected
decomposition equivalences. The morphism kind records whether the equivalence is
read as refactor, semantic, or boundary-preserving equivalence. This is a
bounded groupoid-valued surface, not a classification of all decompositions.
-/
structure DecompositionGroupoid where
  Object : Type z
  Hom : Object -> Object -> Type z
  equivalenceKind : ∀ {a b : Object}, Hom a b -> DecompositionEquivalenceKind
  id : ∀ a : Object, Hom a a
  inv : ∀ {a b : Object}, Hom a b -> Hom b a
  comp : ∀ {a b c : Object}, Hom a b -> Hom b c -> Hom a c
  id_comp : ∀ {a b : Object} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b : Object} (f : Hom a b), comp f (id b) = f
  assoc : ∀ {a b c d : Object} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)
  inv_comp : ∀ {a b : Object} (f : Hom a b), comp (inv f) f = id b
  comp_inv : ∀ {a b : Object} (f : Hom a b), comp f (inv f) = id a

namespace DecompositionGroupoid

/-- VI.定義15.1: a selected decomposition equivalence has a recorded kind. -/
def homKind (D : DecompositionGroupoid.{z}) {a b : D.Object} (f : D.Hom a b) :
    DecompositionEquivalenceKind :=
  D.equivalenceKind f

/-- VI.定義15.1: identity decomposition equivalence. -/
theorem id_kind_defined (D : DecompositionGroupoid.{z}) (a : D.Object) :
    (D.homKind (D.id a) = D.homKind (D.id a)) :=
  rfl

/-- VI.定義15.1: inverse decomposition equivalence. -/
def inverseHom (D : DecompositionGroupoid.{z}) {a b : D.Object} (f : D.Hom a b) :
    D.Hom b a :=
  D.inv f

/-- VI.定義15.1: composite decomposition equivalence. -/
def compHom (D : DecompositionGroupoid.{z}) {a b c : D.Object}
    (f : D.Hom a b) (g : D.Hom b c) : D.Hom a c :=
  D.comp f g

end DecompositionGroupoid

/--
VI.定義15.1: groupoid-valued decomposition presheaf.

For each selected architecture-stack context `W`, this returns the fiber
decomposition groupoid `Dec_U(X)(W)` together with restriction data.
-/
structure DecompositionPresheaf (B : ArchitectureStackBase.{z}) where
  fiber : B.Context -> DecompositionGroupoid.{z}
  restrictObject : ∀ {T W : B.Context}, B.restrict W T ->
    (fiber T).Object -> (fiber W).Object
  restrictHom : ∀ {T W : B.Context} (r : B.restrict W T)
    {a b : (fiber T).Object}, (fiber T).Hom a b ->
      (fiber W).Hom (restrictObject r a) (restrictObject r b)
  restrict_id : ∀ {T W : B.Context} (r : B.restrict W T) (a : (fiber T).Object),
    restrictHom r ((fiber T).id a) = (fiber W).id (restrictObject r a)
  restrict_comp : ∀ {T W : B.Context} (r : B.restrict W T)
    {a b c : (fiber T).Object} (f : (fiber T).Hom a b) (g : (fiber T).Hom b c),
      restrictHom r ((fiber T).comp f g) =
        (fiber W).comp (restrictHom r f) (restrictHom r g)

namespace DecompositionPresheaf

variable {B : ArchitectureStackBase.{z}}

/-- VI.定義15.1: fiber decompositions over a selected context. -/
def Dec_U (D : DecompositionPresheaf.{z} B) (W : B.Context) : Type z :=
  (D.fiber W).Object

/-- VI.定義15.1: selected equivalences in `Dec_U(X)(W)`. -/
def Equiv (D : DecompositionPresheaf.{z} B) (W : B.Context)
    (a b : D.Dec_U W) : Type z :=
  (D.fiber W).Hom a b

/-- VI.定義15.1: restriction preserves selected decomposition objects. -/
theorem restrictObject_eq (D : DecompositionPresheaf.{z} B)
    {T W : B.Context} (r : B.restrict W T) (a : D.Dec_U T) :
    D.restrictObject r a = D.restrictObject r a :=
  rfl

end DecompositionPresheaf

/--
VI.定義15.1: selected decomposition stack.

This packages the fiber decomposition groupoids together with cover descent
for selected fiber decomposition data. It does not assert a privileged global
decomposition or a complete classification of all decompositions.
-/
structure DecompositionStack (B : ArchitectureStackBase.{z}) where
  presheaf : DecompositionPresheaf.{z} B
  LocalIndex : Type z
  localContext : LocalIndex -> B.Context
  localDecomposition : ∀ i : LocalIndex, (presheaf.fiber (localContext i)).Object
  overlapCompatible : Prop
  overlapCompatible_cert : overlapCompatible
  effectiveDescent : Prop
  effectiveDescent_cert : effectiveDescent

namespace DecompositionStack

variable {B : ArchitectureStackBase.{z}}

/-- VI.定義15.1: fiber decomposition groupoid-valued stack has overlap compatibility. -/
theorem overlapCompatible_holds (D : DecompositionStack.{z} B) :
    D.overlapCompatible :=
  D.overlapCompatible_cert

/-- VI.定義15.1: selected fiber decompositions satisfy the supplied descent predicate. -/
theorem effectiveDescent_holds (D : DecompositionStack.{z} B) :
    D.effectiveDescent :=
  D.effectiveDescent_cert

end DecompositionStack

/--
VI.定義16.1: selected non-abelian gerbe obstruction.

`GerbeClass` is an abstract pointed obstruction type. Nonzero is a selected
predicate tied to the distinguished class. This avoids claiming a general
construction of non-abelian gerbe cohomology.
-/
structure GerbeObstructionData {B : ArchitectureStackBase.{z}}
    (D : DecompositionStack.{z} B) where
  GerbeClass : Type z
  zero : GerbeClass
  gerbeClass : GerbeClass
  nonzero : Prop
  nonzero_cert : nonzero -> gerbeClass ≠ zero
  automorphismSheaf : Type z
  autSheafDefined : Prop
  autSheafDefined_cert : autSheafDefined
  nonAbelianReading : Prop
  nonAbelianReading_cert : nonAbelianReading

namespace GerbeObstructionData

variable {B : ArchitectureStackBase.{z}}
variable {D : DecompositionStack.{z} B}

/-- VI.定義16.1: the selected gerbe obstruction class is defined. -/
def gerbeClassValue (G : GerbeObstructionData.{z} D) : G.GerbeClass :=
  G.gerbeClass

/-- VI.定義16.1: nonzero selected gerbe class gives inequality from zero. -/
theorem gerbeClass_ne_zero (G : GerbeObstructionData.{z} D) (h : G.nonzero) :
    G.gerbeClass ≠ G.zero :=
  G.nonzero_cert h

/-- VI.定義16.1: the selected automorphism sheaf reading is available. -/
theorem autSheafDefined_holds (G : GerbeObstructionData.{z} D) :
    G.autSheafDefined :=
  G.autSheafDefined_cert

/-- VI.定義16.1: the selected obstruction is read non-abelianly. -/
theorem nonAbelianReading_holds (G : GerbeObstructionData.{z} D) :
    G.nonAbelianReading :=
  G.nonAbelianReading_cert

end GerbeObstructionData

/--
VI.定義16.1: bridge from a banded abelian gerbe to the PRD-4 `H^2` surface.

The bridge is conditional on the existing PRD-4 Čech-to-space cohomology
surface. It records a selected class in `H^2(X, A)` without constructing
general non-abelian gerbe cohomology.
-/
structure BandedAbelianGerbeBridge {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {𝒰 : Cohomology.CoverRelativeCechCover S} {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
    (H2 : Cohomology.ConditionalSpaceCohomology K 2)
    {B : ArchitectureStackBase.{z}} {D : DecompositionStack.{z} B}
    (G : GerbeObstructionData.{z} D) where
  bandedBy : Cohomology.ObstructionSheaf S
  h2Class : H2.HnX
  representsGerbeClass : Prop
  representsGerbeClass_cert : representsGerbeClass
  abelianBridgeOnlyWhenBanded : Prop
  abelianBridgeOnlyWhenBanded_cert : abelianBridgeOnlyWhenBanded

namespace BandedAbelianGerbeBridge

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : Cohomology.CoverRelativeCechCover S} {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
variable {H2 : Cohomology.ConditionalSpaceCohomology K 2}
variable {B : ArchitectureStackBase.{z}} {D : DecompositionStack.{z} B}
variable {G : GerbeObstructionData.{z} D}

/-- VI.定義16.1: selected abelian `H^2(X,A)` representative exists. -/
theorem representsGerbeClass_holds
    (Br : BandedAbelianGerbeBridge.{u, z} H2 G) :
    Br.representsGerbeClass :=
  Br.representsGerbeClass_cert

/-- VI.定義16.1: the abelian bridge is restricted to banded gerbes. -/
theorem abelianBridgeOnlyWhenBanded_holds
    (Br : BandedAbelianGerbeBridge.{u, z} H2 G) :
    Br.abelianBridgeOnlyWhenBanded :=
  Br.abelianBridgeOnlyWhenBanded_cert

end BandedAbelianGerbeBridge

/--
VI.定理16.2: selected assumptions for no canonical decomposition.

The key soundness field is the bounded implication
`globalCanonicalDecomposition -> gerbeClass = 0`.
-/
structure NoCanonicalDecompositionData {B : ArchitectureStackBase.{z}}
    {D : DecompositionStack.{z} B} (G : GerbeObstructionData.{z} D) where
  localDecompositionsExist : Prop
  localDecompositionsExist_cert : localDecompositionsExist
  globalCanonicalDecomposition : Prop
  soundness :
    globalCanonicalDecomposition -> G.gerbeClass = G.zero

namespace NoCanonicalDecompositionData

variable {B : ArchitectureStackBase.{z}}
variable {D : DecompositionStack.{z} B}
variable {G : GerbeObstructionData.{z} D}

/-- VI.定理16.2: selected fiber decompositions exist. -/
theorem localDecompositionsExist_holds
    (N : NoCanonicalDecompositionData.{z} G) :
    N.localDecompositionsExist :=
  N.localDecompositionsExist_cert

/--
VI.定理16.2: No Canonical Decomposition.

Under the explicit soundness hypothesis that a global canonical decomposition
would force the selected gerbe class to vanish, a selected nonzero gerbe class
rules out a global canonical decomposition.
-/
theorem noCanonicalDecomposition
    (N : NoCanonicalDecompositionData.{z} G) (h : G.nonzero) :
    ¬ N.globalCanonicalDecomposition := by
  intro hglobal
  exact G.gerbeClass_ne_zero h (N.soundness hglobal)

end NoCanonicalDecompositionData

end SingularityMonodromyStack
end AAT.AG
