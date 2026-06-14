import Mathlib.Order.GaloisConnection.Defs
import Formal.AG.SingularityMonodromyStack.OperationCategory

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/--
VI.定義12.1: selected refactor groupoid package.

The objects are a selected family over the operation states, and morphisms are
selected refactor equivalences. The groupoid laws are supplied as data; this
does not claim that every semantic equivalence or source refactoring operation
has been selected.
-/
structure RefactorGroupoid {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G) where
  Object : Type z
  state : Object -> G.State
  Hom : Object -> Object -> Type z
  toRefactorEquivalent :
    ∀ {a b : Object}, Hom a b -> R.RefactorEquivalent (state a) (state b)
  id : ∀ a : Object, Hom a a
  inv : ∀ {a b : Object}, Hom a b -> Hom b a
  comp : ∀ {a b c : Object}, Hom a b -> Hom b c -> Hom a c
  id_comp : ∀ {a b : Object} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b : Object} (f : Hom a b), comp f (id b) = f
  assoc : ∀ {a b c d : Object} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)
  inv_comp : ∀ {a b : Object} (f : Hom a b), comp (inv f) f = id b
  comp_inv : ∀ {a b : Object} (f : Hom a b), comp f (inv f) = id a

namespace RefactorGroupoid

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}

/-- VI.定義12.1: a selected refactor morphism reads as endpoint equivalence. -/
theorem hom_refactorEquivalent
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R)
    {a b : RG.Object} (f : RG.Hom a b) :
    R.RefactorEquivalent (RG.state a) (RG.state b) :=
  RG.toRefactorEquivalent f

/-- VI.定義12.1: selected refactor identity morphism. -/
theorem id_refactorEquivalent
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R)
    (a : RG.Object) :
    R.RefactorEquivalent (RG.state a) (RG.state a) :=
  RG.toRefactorEquivalent (RG.id a)

/-- VI.定義12.1: selected inverse morphism. -/
theorem inv_refactorEquivalent
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R)
    {a b : RG.Object} (f : RG.Hom a b) :
    R.RefactorEquivalent (RG.state b) (RG.state a) :=
  RG.toRefactorEquivalent (RG.inv f)

/-- VI.定義12.1: selected composite morphism. -/
theorem comp_refactorEquivalent
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R)
    {a b c : RG.Object} (f : RG.Hom a b) (g : RG.Hom b c) :
    R.RefactorEquivalent (RG.state a) (RG.state c) :=
  RG.toRefactorEquivalent (RG.comp f g)

end RefactorGroupoid

/-- VI.定義12.3: a selected family of refactor morphisms. -/
def RefactorMorphismFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R) : Type z :=
  ∀ {a b : RG.Object}, RG.Hom a b -> Prop

/--
VI.定義12.3: selected sub-groupoid predicate.

This records closure of a selected morphism family under identity, inverse, and
composition. It is a bounded `SubGpd(Ref_U(X))` surface, not a classification of
all subgroupoids.
-/
structure RefactorSubgroupoid {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R) where
  carrier : RefactorMorphismFamily RG
  id_mem : ∀ a : RG.Object, carrier (RG.id a)
  inv_mem : ∀ {a b : RG.Object} {f : RG.Hom a b}, carrier f -> carrier (RG.inv f)
  comp_mem : ∀ {a b c : RG.Object} {f : RG.Hom a b} {g : RG.Hom b c},
    carrier f -> carrier g -> carrier (RG.comp f g)

/-- VI.定義12.3: notation-level alias for selected sub-groupoids. -/
abbrev SubGpd {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R) : Type z :=
  RefactorSubgroupoid RG

/-- VI.定義12.3: selected morphism-family inclusion. -/
def RefactorMorphismFamilySubset {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {RG : RefactorGroupoid.{u, v, w, x, y, z} R}
    (G₁ G₂ : RefactorMorphismFamily RG) : Prop :=
  ∀ {a b : RG.Object} (g : RG.Hom a b), G₁ g -> G₂ g

/-- VI.定義12.3: packaged operation-invariant preservation relation. -/
structure OperationInvariantGaloisData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R) where
  Invariant : Type z
  Preserves : ∀ {a b : RG.Object}, RG.Hom a b -> Invariant -> Prop
  id_preserves : ∀ (a : RG.Object) (i : Invariant), Preserves (RG.id a) i
  inv_preserves : ∀ {a b : RG.Object} (g : RG.Hom a b) (i : Invariant),
    Preserves g i -> Preserves (RG.inv g) i
  comp_preserves : ∀ {a b c : RG.Object} (g : RG.Hom a b) (h : RG.Hom b c)
    (i : Invariant), Preserves g i -> Preserves h i -> Preserves (RG.comp g h) i

namespace OperationInvariantGaloisData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {RG : RefactorGroupoid.{u, v, w, x, y, z} R}

/-- VI.定義12.3: selected invariant families. -/
abbrev InvFam (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG) : Type z :=
  D.Invariant -> Prop

/-- VI.定義12.3: invariant-family inclusion. -/
def InvFamSubset
    {D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG}
    (I₁ I₂ : D.InvFam) : Prop :=
  ∀ i : D.Invariant, I₁ i -> I₂ i

/-- VI.定義12.3: operation family preserving every selected invariant. -/
def Ops
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (I : D.InvFam) : RefactorMorphismFamily RG :=
  fun {_a _b} g => ∀ i : D.Invariant, I i -> D.Preserves g i

/-- VI.定義12.3: invariant family preserved by every selected operation. -/
def Inv
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (Gfam : RefactorMorphismFamily RG) : D.InvFam :=
  fun i => ∀ {_a _b} (g : RG.Hom _a _b), Gfam g -> D.Preserves g i

/-- VI.定義12.3: `Ops(I)` as a selected sub-groupoid. -/
def OpsSubgpd
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (I : D.InvFam) : SubGpd RG where
  carrier := D.Ops I
  id_mem := by
    intro a i _hi
    exact D.id_preserves a i
  inv_mem := by
    intro a b g hg i hi
    exact D.inv_preserves g i (hg i hi)
  comp_mem := by
    intro a b c g h hg hh i hi
    exact D.comp_preserves g h i (hg i hi) (hh i hi)

/-- VI.定義12.3: invariant family preserved by every morphism in a selected sub-groupoid. -/
def InvSubgpd
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (Gsub : SubGpd RG) : D.InvFam :=
  D.Inv Gsub.carrier

/-- VI.定義12.3: selected sub-groupoid inclusion. -/
def SubGpdSubset
    (G₁ G₂ : SubGpd RG) : Prop :=
  RefactorMorphismFamilySubset G₁.carrier G₂.carrier

/--
VI.定理12.4: Operation-Invariant Galois Correspondence.

For the fixed selected preservation relation, a selected operation family is
contained in the operations preserving `I` exactly when `I` is contained in the
invariants preserved by that operation family.
-/
theorem operationInvariantGaloisCorrespondence
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (Gfam : RefactorMorphismFamily RG) (I : D.InvFam) :
    RefactorMorphismFamilySubset Gfam (D.Ops I) ↔
      D.InvFamSubset I (D.Inv Gfam) := by
  constructor
  · intro hG i hi _a _b g hg
    exact hG g hg i hi
  · intro hI _a _b g hg i hi
    exact hI i hi g hg

/--
VI.定理12.4: Operation-Invariant Galois Correspondence on selected
sub-groupoids.

This is the `SubGpd(Ref_U(X))` form: a selected sub-groupoid is contained in
`Ops(I)` exactly when `I` is contained in the invariants preserved by that
sub-groupoid.
-/
theorem operationInvariantGaloisCorrespondence_subgpd
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (Gsub : SubGpd RG) (I : D.InvFam) :
    SubGpdSubset Gsub (D.OpsSubgpd I) ↔
      D.InvFamSubset I (D.InvSubgpd Gsub) :=
  D.operationInvariantGaloisCorrespondence Gsub.carrier I

/-- VI.定理12.4: operation-family direction of the Galois correspondence. -/
theorem subset_ops_of_invFamSubset_inv
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    {Gfam : RefactorMorphismFamily RG} {I : D.InvFam}
    (hI : D.InvFamSubset I (D.Inv Gfam)) :
    RefactorMorphismFamilySubset Gfam (D.Ops I) :=
  (D.operationInvariantGaloisCorrespondence Gfam I).mpr hI

/-- VI.定理12.4: invariant-family direction of the Galois correspondence. -/
theorem invFamSubset_inv_of_subset_ops
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    {Gfam : RefactorMorphismFamily RG} {I : D.InvFam}
    (hG : RefactorMorphismFamilySubset Gfam (D.Ops I)) :
    D.InvFamSubset I (D.Inv Gfam) :=
  (D.operationInvariantGaloisCorrespondence Gfam I).mp hG

/-- A first-order morphism package used for the Mathlib `GaloisConnection` bridge. -/
structure RefactorMorphism
    (RG : RefactorGroupoid.{u, v, w, x, y, z} R) where
  source : RG.Object
  target : RG.Object
  hom : RG.Hom source target

/-- VI.定理12.4: set-valued `Ops` used by the Mathlib bridge. -/
def OpsSet
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (I : Set D.Invariant) : Set (RefactorMorphism RG) :=
  fun g => ∀ i : D.Invariant, i ∈ I -> D.Preserves g.hom i

/-- VI.定理12.4: set-valued `Inv` used by the Mathlib bridge. -/
def InvSet
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (Gset : Set (RefactorMorphism RG)) : Set D.Invariant :=
  fun i => ∀ g : RefactorMorphism RG, g ∈ Gset -> D.Preserves g.hom i

/-- VI.定理12.4: set-valued form of the selected operation-invariant correspondence. -/
theorem operationInvariantGaloisCorrespondence_set
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG)
    (Gset : Set (RefactorMorphism RG)) (I : Set D.Invariant) :
    Gset ⊆ D.OpsSet I ↔ I ⊆ D.InvSet Gset := by
  constructor
  · intro hG i hi g hg
    exact hG hg i hi
  · intro hI g hg i hi
    exact hI hi g hg

/--
VI.定理12.4: Mathlib `GaloisConnection` bridge.

`Inv` is antitone, so the invariant side is order-dualized. This is only the
selected preservation relation for `Ref_U(X)`; it does not assert a lattice
isomorphism or completeness of all invariants.
-/
theorem operationInvariant_galoisConnection
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG) :
    GaloisConnection
      (fun Gset : Set (RefactorMorphism RG) => OrderDual.toDual (D.InvSet Gset))
      (fun I : OrderDual (Set D.Invariant) => D.OpsSet (OrderDual.ofDual I)) := by
  intro Gset I
  change OrderDual.ofDual I ⊆ D.InvSet Gset ↔
    Gset ⊆ D.OpsSet (OrderDual.ofDual I)
  exact (D.operationInvariantGaloisCorrespondence_set Gset (OrderDual.ofDual I)).symm

end OperationInvariantGaloisData

end SingularityMonodromyStack
end AAT.AG
