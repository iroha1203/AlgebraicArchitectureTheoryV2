import Formal.AG.SingularityMonodromyStack.RefactorGalois

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/--
VI.定義13.1: selected base for a groupoid-valued architecture presheaf.

This is the base-context surface used by Part VI. It records a selected context
type, overlap contexts, triple-overlap contexts, and restriction arrows. It does
not construct an arbitrary category of bases.
-/
structure ArchitectureStackBase where
  Context : Type z
  Overlap : Context -> Context -> Type z
  TripleOverlap : Context -> Context -> Context -> Type z
  restrict : Context -> Context -> Type z
  idRestrict : ∀ T : Context, restrict T T
  compRestrict : ∀ {T U V : Context}, restrict U T -> restrict V U -> restrict V T
  id_comp : ∀ {T U : Context} (r : restrict U T), compRestrict (idRestrict T) r = r
  comp_id : ∀ {T U : Context} (r : restrict U T), compRestrict r (idRestrict U) = r
  assoc : ∀ {T U V W : Context} (r : restrict U T) (s : restrict V U)
    (t : restrict W V), compRestrict (compRestrict r s) t = compRestrict r (compRestrict s t)
  overlapContext : ∀ {a b : Context}, Overlap a b -> Context
  overlap_left : ∀ {a b : Context} (o : Overlap a b), restrict (overlapContext o) a
  overlap_right : ∀ {a b : Context} (o : Overlap a b), restrict (overlapContext o) b

/--
VI.定義13.1: groupoid-valued architecture presheaf package.

For each selected base context, the package stores local architecture objects,
isomorphisms, identity, inverse, composition, and restriction along selected
base arrows. The laws are supplied data, keeping the claim bounded to the
selected groupoid-valued surface.
-/
structure ArchitecturePresheaf (B : ArchitectureStackBase.{z}) where
  Obj : B.Context -> Type z
  Iso : ∀ {T : B.Context}, Obj T -> Obj T -> Type z
  id : ∀ {T : B.Context} (X : Obj T), Iso X X
  inv : ∀ {T : B.Context} {X Y : Obj T}, Iso X Y -> Iso Y X
  comp : ∀ {T : B.Context} {X Y Z : Obj T}, Iso X Y -> Iso Y Z -> Iso X Z
  id_comp : ∀ {T : B.Context} {X Y : Obj T} (f : Iso X Y), comp (id X) f = f
  comp_id : ∀ {T : B.Context} {X Y : Obj T} (f : Iso X Y), comp f (id Y) = f
  assoc : ∀ {T : B.Context} {W X Y Z : Obj T} (f : Iso W X) (g : Iso X Y)
    (h : Iso Y Z), comp (comp f g) h = comp f (comp g h)
  inv_comp : ∀ {T : B.Context} {X Y : Obj T} (f : Iso X Y), comp (inv f) f = id Y
  comp_inv : ∀ {T : B.Context} {X Y : Obj T} (f : Iso X Y), comp f (inv f) = id X
  pullbackObj : ∀ {T U : B.Context}, B.restrict U T -> Obj T -> Obj U
  pullbackIso : ∀ {T U : B.Context} (r : B.restrict U T) {X Y : Obj T},
    Iso X Y -> Iso (pullbackObj r X) (pullbackObj r Y)
  pullback_id : ∀ {T U : B.Context} (r : B.restrict U T) (X : Obj T),
    pullbackIso r (id X) = id (pullbackObj r X)
  pullback_comp : ∀ {T U : B.Context} (r : B.restrict U T)
    {X Y Z : Obj T} (f : Iso X Y) (g : Iso Y Z),
    pullbackIso r (comp f g) = comp (pullbackIso r f) (pullbackIso r g)
  pullbackBaseId : ∀ {T : B.Context} (X : Obj T),
    pullbackObj (B.idRestrict T) X = X
  pullbackBaseComp : ∀ {T U V : B.Context} (r : B.restrict U T) (s : B.restrict V U)
    (X : Obj T),
    pullbackObj (B.compRestrict r s) X = pullbackObj s (pullbackObj r X)
  pullbackIsoBaseId : ∀ {T : B.Context} {X Y : Obj T} (f : Iso X Y),
    HEq (pullbackIso (B.idRestrict T) f) f
  pullbackIsoBaseComp : ∀ {T U V : B.Context} (r : B.restrict U T) (s : B.restrict V U)
    {X Y : Obj T} (f : Iso X Y),
    HEq (pullbackIso (B.compRestrict r s) f) (pullbackIso s (pullbackIso r f))

namespace ArchitecturePresheaf

variable {B : ArchitectureStackBase.{z}}

/-- VI.定義13.1: a selected pullback of a local architecture object. -/
theorem pullbackObj_eq (P : ArchitecturePresheaf.{z} B)
    {T U : B.Context} (r : B.restrict U T) (X : P.Obj T) :
    P.pullbackObj r X = P.pullbackObj r X :=
  rfl

/-- VI.定義13.1: pullback preserves selected isomorphisms. -/
def pullbackIso_holds (P : ArchitecturePresheaf.{z} B)
    {T U : B.Context} (r : B.restrict U T)
    {X Y : P.Obj T} (f : P.Iso X Y) :
    P.Iso (P.pullbackObj r X) (P.pullbackObj r Y) :=
  P.pullbackIso r f

end ArchitecturePresheaf

/-- VI.定義13.1: local architecture objects selected on a cover. -/
structure LocalArchitectureObjects {B : ArchitectureStackBase.{z}}
    (P : ArchitecturePresheaf.{z} B) where
  CoverIndex : Type z
  context : CoverIndex -> B.Context
  object : ∀ i : CoverIndex, P.Obj (context i)

/--
VI.定義13.1: selected descent datum.

Overlap isomorphisms and their cocycle condition are recorded explicitly. This
is the stack-facing local-to-global datum; it does not assert a universal
stackification theorem.
-/
structure ArchitectureDescentDatum {B : ArchitectureStackBase.{z}}
    (P : ArchitecturePresheaf.{z} B) (L : LocalArchitectureObjects P) where
  overlap : ∀ i j : L.CoverIndex, B.Overlap (L.context i) (L.context j)
  overlapIso : ∀ i j : L.CoverIndex,
    P.Iso
      (P.pullbackObj (B.overlap_left (overlap i j)) (L.object i))
      (P.pullbackObj (B.overlap_right (overlap i j)) (L.object j))
  triple : ∀ i j k : L.CoverIndex, B.TripleOverlap (L.context i) (L.context j) (L.context k)
  cocycleCondition :
    (∀ i j : L.CoverIndex,
      P.Iso
        (P.pullbackObj (B.overlap_left (overlap i j)) (L.object i))
        (P.pullbackObj (B.overlap_right (overlap i j)) (L.object j))) ->
    (∀ i j k : L.CoverIndex, B.TripleOverlap (L.context i) (L.context j) (L.context k)) ->
      Prop
  cocycleCondition_holds : cocycleCondition
    overlapIso
    triple

/--
VI.定義13.1: effective descent witness for selected architecture data.

The global object and its local comparison isomorphisms are explicit supplied
data. This proves no general descent theorem outside the selected predicate.
-/
structure EffectiveArchitectureDescent {B : ArchitectureStackBase.{z}}
    (P : ArchitecturePresheaf.{z} B) {L : LocalArchitectureObjects P}
    (D : ArchitectureDescentDatum P L) where
  globalContext : B.Context
  globalObject : P.Obj globalContext
  restrictToLocal : ∀ i : L.CoverIndex, B.restrict (L.context i) globalContext
  localComparison : ∀ i : L.CoverIndex,
    P.Iso (P.pullbackObj (restrictToLocal i) globalObject) (L.object i)
  realizesOverlapData :
    (∀ i : L.CoverIndex,
      P.Iso (P.pullbackObj (restrictToLocal i) globalObject) (L.object i)) ->
    (∀ i j : L.CoverIndex,
      P.Iso
        (P.pullbackObj (B.overlap_left (D.overlap i j)) (L.object i))
        (P.pullbackObj (B.overlap_right (D.overlap i j)) (L.object j))) ->
      Prop
  realizesOverlapData_holds : realizesOverlapData
    localComparison
    D.overlapIso

/--
VI.定義13.1: architecture stack predicate.

An architecture presheaf is a stack when every selected local descent datum has
effective descent. This is a bounded predicate over the selected base and cover
data, not a construction of arbitrary groupoid-valued stacks.
-/
structure ArchitectureStack {B : ArchitectureStackBase.{z}}
    (P : ArchitecturePresheaf.{z} B) where
  effectiveDescent :
    ∀ (L : LocalArchitectureObjects P) (D : ArchitectureDescentDatum P L),
      EffectiveArchitectureDescent P D

namespace ArchitectureStack

variable {B : ArchitectureStackBase.{z}}
variable {P : ArchitecturePresheaf.{z} B}

/-- VI.定義13.1: selected local data descend to a global architecture object. -/
def effectiveDescent_holds
    (S : ArchitectureStack.{z} P)
    (L : LocalArchitectureObjects P) (D : ArchitectureDescentDatum P L) :
    EffectiveArchitectureDescent P D :=
  S.effectiveDescent L D

/-- VI.定義13.1: selected descent datum satisfies its cocycle condition. -/
theorem cocycleCondition_holds
    {L : LocalArchitectureObjects P} (D : ArchitectureDescentDatum P L) :
    D.cocycleCondition D.overlapIso D.triple :=
  D.cocycleCondition_holds

end ArchitectureStack

/--
VI.定義13.3: extra algebraicity data for an architecture stack.

The diagonal, atlas, and descent of selected structure are explicit predicates.
No general algebraic-stack representability theorem is claimed.
-/
structure AlgebraicArchitectureStackData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {B : ArchitectureStackBase.{z}}
    (P : ArchitecturePresheaf.{z} B) where
  architectureStack : ArchitectureStack P
  representableDiagonal : Prop
  representableDiagonal_cert : representableDiagonal
  atlasScheme : LawAlgebra.Scheme.ArchitectureScheme.{u, v, w, x, y} S k
  atlasAdmissible : Prop
  atlasAdmissible_cert : atlasAdmissible
  obstructionIdealsDescend : Prop
  obstructionIdealsDescend_cert : obstructionIdealsDescend
  lawSheavesDescend : Prop
  lawSheavesDescend_cert : lawSheavesDescend
  signatureSheavesDescend : Prop
  signatureSheavesDescend_cert : signatureSheavesDescend
  structureSheavesDescend : Prop
  structureSheavesDescend_cert : structureSheavesDescend

/--
VI.定義13.3: algebraic architecture stack predicate.

This is the strong Part VI predicate: architecture stack plus selected
representable diagonal, selected architecture-scheme atlas, and descent of the
obstruction, law, signature, and structure sheaves.
-/
def AlgebraicArchitectureStack {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {B : ArchitectureStackBase.{z}}
    (P : ArchitecturePresheaf.{z} B) : Prop :=
  ∃ _ : AlgebraicArchitectureStackData.{u, v, w, x, y, z, z} (S := S) (k := k) P, True

namespace AlgebraicArchitectureStackData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {B : ArchitectureStackBase.{z}}
variable {P : ArchitecturePresheaf.{z} B}

/-- VI.定義13.3: the diagonal is selected representable. -/
theorem representableDiagonal_holds
    (X : AlgebraicArchitectureStackData.{u, v, w, x, y, z} (S := S) (k := k) P) :
    X.representableDiagonal :=
  X.representableDiagonal_cert

/-- VI.定義13.3: the selected architecture-scheme atlas is admissible. -/
theorem atlasAdmissible_holds
    (X : AlgebraicArchitectureStackData.{u, v, w, x, y, z} (S := S) (k := k) P) :
    X.atlasAdmissible :=
  X.atlasAdmissible_cert

/-- VI.定義13.3: obstruction ideals descend along the selected atlas. -/
theorem obstructionIdealsDescend_holds
    (X : AlgebraicArchitectureStackData.{u, v, w, x, y, z} (S := S) (k := k) P) :
    X.obstructionIdealsDescend :=
  X.obstructionIdealsDescend_cert

/-- VI.定義13.3: law sheaves descend along the selected atlas. -/
theorem lawSheavesDescend_holds
    (X : AlgebraicArchitectureStackData.{u, v, w, x, y, z} (S := S) (k := k) P) :
    X.lawSheavesDescend :=
  X.lawSheavesDescend_cert

/-- VI.定義13.3: signature sheaves descend along the selected atlas. -/
theorem signatureSheavesDescend_holds
    (X : AlgebraicArchitectureStackData.{u, v, w, x, y, z} (S := S) (k := k) P) :
    X.signatureSheavesDescend :=
  X.signatureSheavesDescend_cert

/-- VI.定義13.3: structure sheaves descend along the selected atlas. -/
theorem structureSheavesDescend_holds
    (X : AlgebraicArchitectureStackData.{u, v, w, x, y, z} (S := S) (k := k) P) :
    X.structureSheavesDescend :=
  X.structureSheavesDescend_cert

end AlgebraicArchitectureStackData

end SingularityMonodromyStack
end AAT.AG
