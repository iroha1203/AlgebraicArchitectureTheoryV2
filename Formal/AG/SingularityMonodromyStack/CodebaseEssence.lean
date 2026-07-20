import Formal.AG.SingularityMonodromyStack.ArchitectureStack

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v y z

/--
VI.定義14.1: selected refactor arrow for the codebase quotient presentation.

This is the `Ref_U` arrow surface over the selected geometry objects `X^U`.
The endpoints are carried explicitly so that source, target, identity, inverse,
and composition can be exposed without constructing a general quotient stack.
-/
structure CodebaseRefactorArrow {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    (RG : RefactorGroupoid.{u, v, y, z} R) where
  source : RG.Object
  target : RG.Object
  hom : RG.Hom source target

namespace CodebaseRefactorArrow

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {RG : RefactorGroupoid.{u, v, y, z} R}

/-- VI.定義14.1: source map `s : Ref_U -> X^U`. -/
def sourceObject (g : CodebaseRefactorArrow RG) : RG.Object :=
  g.source

/-- VI.定義14.1: target map `t : Ref_U -> X^U`. -/
def targetObject (g : CodebaseRefactorArrow RG) : RG.Object :=
  g.target

/-- VI.定義14.1: identity arrow `e : X^U -> Ref_U`. -/
def identity (RG : RefactorGroupoid.{u, v, y, z} R) (a : RG.Object) :
    CodebaseRefactorArrow RG where
  source := a
  target := a
  hom := RG.id a

/-- VI.定義14.1: inverse arrow in `Ref_U`. -/
def inverse (g : CodebaseRefactorArrow RG) : CodebaseRefactorArrow RG where
  source := g.target
  target := g.source
  hom := RG.inv g.hom

/-- VI.定義14.1: composition on the fiber product `Ref_U x_{X^U} Ref_U`. -/
def comp {a b c : RG.Object} (g : RG.Hom a b) (h : RG.Hom b c) :
    CodebaseRefactorArrow RG where
  source := a
  target := c
  hom := RG.comp g h

/-- VI.定義14.1: identity arrow has the selected source. -/
theorem source_identity
    (RG : RefactorGroupoid.{u, v, y, z} R) (a : RG.Object) :
    (identity RG a).sourceObject = a :=
  rfl

/-- VI.定義14.1: identity arrow has the selected target. -/
theorem target_identity
    (RG : RefactorGroupoid.{u, v, y, z} R) (a : RG.Object) :
    (identity RG a).targetObject = a :=
  rfl

/-- VI.定義14.1: inverse swaps source and target. -/
theorem source_inverse (g : CodebaseRefactorArrow RG) :
    g.inverse.sourceObject = g.targetObject :=
  rfl

/-- VI.定義14.1: inverse swaps target and source. -/
theorem target_inverse (g : CodebaseRefactorArrow RG) :
    g.inverse.targetObject = g.sourceObject :=
  rfl

/-- VI.定義14.1: selected composition has the first source. -/
theorem source_comp {a b c : RG.Object} (g : RG.Hom a b) (h : RG.Hom b c) :
    (comp g h).sourceObject = a :=
  rfl

/-- VI.定義14.1: selected composition has the second target. -/
theorem target_comp {a b c : RG.Object} (g : RG.Hom a b) (h : RG.Hom b c) :
    (comp g h).targetObject = c :=
  rfl

end CodebaseRefactorArrow

/--
VI.定義14.1: compatibility of the refactor action with selected geometry.

The action is not a source-code equality relation. It records the selected
refactor arrows together with predicates saying that law, obstruction,
signature, and structure-sheaf readings are preserved by every selected arrow.
-/
structure CodebaseEssenceAction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    (RG : RefactorGroupoid.{u, v, y, z} R) where
  lawCompatible : CodebaseRefactorArrow RG -> Prop
  lawCompatible_cert : ∀ g : CodebaseRefactorArrow RG, lawCompatible g
  obstructionCompatible : CodebaseRefactorArrow RG -> Prop
  obstructionCompatible_cert : ∀ g : CodebaseRefactorArrow RG, obstructionCompatible g
  signatureCompatible : CodebaseRefactorArrow RG -> Prop
  signatureCompatible_cert : ∀ g : CodebaseRefactorArrow RG, signatureCompatible g
  structureSheafCompatible : CodebaseRefactorArrow RG -> Prop
  structureSheafCompatible_cert : ∀ g : CodebaseRefactorArrow RG, structureSheafCompatible g

namespace CodebaseEssenceAction

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {RG : RefactorGroupoid.{u, v, y, z} R}

/-- VI.定義14.1: selected refactor arrows preserve the chosen law reading. -/
theorem lawCompatible_holds (A : CodebaseEssenceAction RG)
    (g : CodebaseRefactorArrow RG) :
    A.lawCompatible g :=
  A.lawCompatible_cert g

/-- VI.定義14.1: selected refactor arrows preserve obstruction readings. -/
theorem obstructionCompatible_holds (A : CodebaseEssenceAction RG)
    (g : CodebaseRefactorArrow RG) :
    A.obstructionCompatible g :=
  A.obstructionCompatible_cert g

/-- VI.定義14.1: selected refactor arrows preserve signature readings. -/
theorem signatureCompatible_holds (A : CodebaseEssenceAction RG)
    (g : CodebaseRefactorArrow RG) :
    A.signatureCompatible g :=
  A.signatureCompatible_cert g

/-- VI.定義14.1: selected refactor arrows preserve structure sheaf readings. -/
theorem structureSheafCompatible_holds (A : CodebaseEssenceAction RG)
    (g : CodebaseRefactorArrow RG) :
    A.structureSheafCompatible g :=
  A.structureSheafCompatible_cert g

end CodebaseEssenceAction

/--
VI.定義14.1: presentation of `[X^U / Ref_U]` by a groupoid-valued presheaf.

`objectToGeometry` reads local presheaf objects as selected `X^U` objects, and
`isoToRefactor` reads local isomorphisms as selected `Ref_U` arrows. The final
predicates record the intended quotient meaning: geometry modulo refactor
equivalence, not text identity and not graph isomorphism.
-/
structure CodebaseEssencePresentation {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P0 : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P0 k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    {B : ArchitectureStackBase.{z}}
    (P : ArchitecturePresheaf.{z} B)
    (RG : RefactorGroupoid.{u, v, y, z} R) where
  objectToGeometry : ∀ {T : B.Context}, P.Obj T -> RG.Object
  isoToRefactor : ∀ {T : B.Context} {X Y : P.Obj T}, P.Iso X Y ->
    RG.Hom (objectToGeometry X) (objectToGeometry Y)
  iso_id :
    ∀ {T : B.Context} (X : P.Obj T),
      isoToRefactor (P.id X) = RG.id (objectToGeometry X)
  iso_comp :
    ∀ {T : B.Context} {X Y Z : P.Obj T} (f : P.Iso X Y) (g : P.Iso Y Z),
      isoToRefactor (P.comp f g) = RG.comp (isoToRefactor f) (isoToRefactor g)
  geometryModuloRefactor : Prop
  geometryModuloRefactor_cert : geometryModuloRefactor
  notTextIdentity : Prop
  notTextIdentity_cert : notTextIdentity
  notGraphIsomorphism : Prop
  notGraphIsomorphism_cert : notGraphIsomorphism

namespace CodebaseEssencePresentation

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P0 : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P0 k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {B : ArchitectureStackBase.{z}}
variable {P : ArchitecturePresheaf.{z} B}
variable {RG : RefactorGroupoid.{u, v, y, z} R}

/-- VI.定義14.1: a local isomorphism is read as a selected refactor arrow. -/
def refactorArrow
    (E : CodebaseEssencePresentation.{u, v, y, z} P RG)
    {T : B.Context} {X Y : P.Obj T} (f : P.Iso X Y) :
    CodebaseRefactorArrow RG where
  source := E.objectToGeometry X
  target := E.objectToGeometry Y
  hom := E.isoToRefactor f

/-- VI.定義14.1: local identities read as refactor identities. -/
theorem iso_id_holds
    (E : CodebaseEssencePresentation.{u, v, y, z} P RG)
    {T : B.Context} (X : P.Obj T) :
    E.isoToRefactor (P.id X) = RG.id (E.objectToGeometry X) :=
  E.iso_id X

/-- VI.定義14.1: local composition reads as refactor composition. -/
theorem iso_comp_holds
    (E : CodebaseEssencePresentation.{u, v, y, z} P RG)
    {T : B.Context} {X Y Z : P.Obj T} (f : P.Iso X Y) (g : P.Iso Y Z) :
    E.isoToRefactor (P.comp f g) = RG.comp (E.isoToRefactor f) (E.isoToRefactor g) :=
  E.iso_comp f g

/-- VI.原則14.2: essence is selected geometry modulo refactor equivalence. -/
theorem geometryModuloRefactor_holds
    (E : CodebaseEssencePresentation.{u, v, y, z} P RG) :
    E.geometryModuloRefactor :=
  E.geometryModuloRefactor_cert

/-- VI.原則14.2: codebase essence is not source text identity. -/
theorem notTextIdentity_holds
    (E : CodebaseEssencePresentation.{u, v, y, z} P RG) :
    E.notTextIdentity :=
  E.notTextIdentity_cert

/-- VI.原則14.2: codebase essence is not graph isomorphism. -/
theorem notGraphIsomorphism_holds
    (E : CodebaseEssencePresentation.{u, v, y, z} P RG) :
    E.notGraphIsomorphism :=
  E.notGraphIsomorphism_cert

end CodebaseEssencePresentation

/--
VI.定義14.1: codebase essence quotient stack data.

This is the selected Lean surface for `Ess_U(X) = [X^U / Ref_U]`: an action
groupoid compatible with the selected readings, a groupoid-valued presheaf, a
stack predicate for descent, and a presentation reading local isomorphisms as
refactor arrows. It does not construct a general quotient stack or compare
source text / graph isomorphism as complete semantics.
-/
structure CodebaseEssenceQuotientStack {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P0 : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P0 k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    (RG : RefactorGroupoid.{u, v, y, z} R) where
  base : ArchitectureStackBase.{z}
  presheaf : ArchitecturePresheaf.{z} base
  action : CodebaseEssenceAction RG
  stack : ArchitectureStack presheaf
  presentation : CodebaseEssencePresentation presheaf RG

/-- VI.定義14.1: notation-level name for the selected codebase essence. -/
abbrev CodebaseEssence {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P0 : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P0 k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    (RG : RefactorGroupoid.{u, v, y, z} R) :=
  CodebaseEssenceQuotientStack.{u, v, y, z} RG

/-- VI.定義14.1: `Ess_U(X)` as the selected quotient-stack package. -/
abbrev Ess_U {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P0 : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P0 k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    (RG : RefactorGroupoid.{u, v, y, z} R) :=
  CodebaseEssence RG

namespace CodebaseEssenceQuotientStack

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P0 : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P0 k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {RG : RefactorGroupoid.{u, v, y, z} R}

/-- VI.定義14.1: the selected groupoid-valued presheaf presenting `Ess_U(X)`. -/
def quotientPresheaf (E : CodebaseEssenceQuotientStack.{u, v, y, z} RG) :
    ArchitecturePresheaf E.base :=
  E.presheaf

/-- VI.定義14.1: selected descent predicate for the quotient-stack presentation. -/
def stack_holds (E : CodebaseEssenceQuotientStack.{u, v, y, z} RG) :
    ArchitectureStack E.presheaf :=
  E.stack

/-- VI.定義14.1: selected compatibility action of `Ref_U` on `X^U`. -/
def action_holds (E : CodebaseEssenceQuotientStack.{u, v, y, z} RG) :
    CodebaseEssenceAction RG :=
  E.action

/-- VI.原則14.2: selected essence is geometry modulo refactor equivalence. -/
theorem geometryModuloRefactor_holds
    (E : CodebaseEssenceQuotientStack.{u, v, y, z} RG) :
    E.presentation.geometryModuloRefactor :=
  E.presentation.geometryModuloRefactor_holds

/-- VI.原則14.2: selected essence is not source text identity. -/
theorem notTextIdentity_holds
    (E : CodebaseEssenceQuotientStack.{u, v, y, z} RG) :
    E.presentation.notTextIdentity :=
  E.presentation.notTextIdentity_holds

/-- VI.原則14.2: selected essence is not graph isomorphism. -/
theorem notGraphIsomorphism_holds
    (E : CodebaseEssenceQuotientStack.{u, v, y, z} RG) :
    E.presentation.notGraphIsomorphism :=
  E.presentation.notGraphIsomorphism_holds

end CodebaseEssenceQuotientStack

end SingularityMonodromyStack
end AAT.AG
