import Formal.AG.SingularityMonodromyStack.Kuranishi

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/--
VI.定義8.1: selected operation graph for a law universe.

This is the finite/composable-path surface used before the R5 homotopy
quotient. It does not claim that every source operation is selected, nor that
formal inverses are executable reverse operations.
-/
structure OperationCategoryData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    (X : ArchitectureStratum.{u, v, w, x, y} P k) where
  State : Type z
  Operation : State -> State -> Type z
  selectedState : X.Point -> State
  operationRespectsLawUniverse : ∀ {a b : State}, Operation a b -> Prop

/-- VI.定義8.1: a selected operation edge with its law-universe certificate. -/
structure SelectedOperation {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    (G : OperationCategoryData.{u, v, w, x, y, z} X)
    (a b : G.State) where
  op : G.Operation a b
  respectsLawUniverse : G.operationRespectsLawUniverse op

namespace OperationCategoryData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}

/-- VI.定義8.1: expose the selected state reading of a stratum point. -/
theorem selectedState_eq
    (G : OperationCategoryData.{u, v, w, x, y, z} X) :
    G.selectedState = G.selectedState :=
  rfl

end OperationCategoryData

/-- VI.定義8.2: finite composable operation paths. -/
inductive OperationPath {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    (G : OperationCategoryData.{u, v, w, x, y, z} X) :
    G.State -> G.State -> Type z where
  | nil (a : G.State) : OperationPath G a a
  | cons {a b c : G.State} :
      SelectedOperation G a b -> OperationPath G b c -> OperationPath G a c

namespace OperationPath

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}

/-- VI.定義8.2: identity operation path at a selected state. -/
def id (a : G.State) : OperationPath G a a :=
  OperationPath.nil a

/-- VI.定義8.2: concatenation of composable operation paths. -/
def concat {a b c : G.State} :
    OperationPath G a b -> OperationPath G b c -> OperationPath G a c
  | OperationPath.nil _, q => q
  | OperationPath.cons op p, q => OperationPath.cons op (concat p q)

@[simp] theorem concat_nil {a b : G.State} (p : OperationPath G a b) :
    concat p (OperationPath.nil b) = p := by
  induction p with
  | nil a => rfl
  | cons op p ih =>
      simp [concat, ih]

@[simp] theorem nil_concat {a b : G.State} (p : OperationPath G a b) :
    concat (OperationPath.nil a) p = p :=
  rfl

/-- VI.R4: operation path concatenation is associative. -/
theorem concat_assoc {a b c d : G.State}
    (p : OperationPath G a b) (q : OperationPath G b c) (r : OperationPath G c d) :
    concat (concat p q) r = concat p (concat q r) := by
  induction p with
  | nil a => rfl
  | cons op p ih =>
      simp [concat, ih]

end OperationPath

/--
VI.定義9.1: selected refactor-equivalent endpoint relation.

The equivalence and preservation clauses are supplied data. R4 does not build a
global semantic equivalence relation or a quotient groupoid.
-/
structure RefactorEndpointReading {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    (G : OperationCategoryData.{u, v, w, x, y, z} X) where
  RefactorEquivalent : G.State -> G.State -> Prop
  refl : ∀ a : G.State, RefactorEquivalent a a
  symm : ∀ {a b : G.State}, RefactorEquivalent a b -> RefactorEquivalent b a
  trans : ∀ {a b c : G.State},
    RefactorEquivalent a b -> RefactorEquivalent b c -> RefactorEquivalent a c
  preservesSelectedInvariants : ∀ {a b : G.State}, RefactorEquivalent a b -> Prop
  preservesSelectedEssence : ∀ {a b : G.State}, RefactorEquivalent a b -> Prop
  invariantCertificate :
    ∀ {a b : G.State} (h : RefactorEquivalent a b), preservesSelectedInvariants h
  essenceCertificate :
    ∀ {a b : G.State} (h : RefactorEquivalent a b), preservesSelectedEssence h

namespace RefactorEndpointReading

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}

/-- VI.定義9.1: endpoint equivalence is reflexive on selected states. -/
theorem refactorEquivalent_refl
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G)
    (a : G.State) :
    R.RefactorEquivalent a a :=
  R.refl a

/-- VI.定義9.1: endpoint equivalence is symmetric by selected data. -/
theorem refactorEquivalent_symm
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G)
    {a b : G.State} (h : R.RefactorEquivalent a b) :
    R.RefactorEquivalent b a :=
  R.symm h

/-- VI.定義9.1: endpoint equivalence is transitive by selected data. -/
theorem refactorEquivalent_trans
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G)
    {a b c : G.State}
    (hab : R.RefactorEquivalent a b) (hbc : R.RefactorEquivalent b c) :
    R.RefactorEquivalent a c :=
  R.trans hab hbc

/-- VI.定義9.1: selected endpoint equivalence preserves selected invariants. -/
theorem preservesSelectedInvariants_holds
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G)
    {a b : G.State} (h : R.RefactorEquivalent a b) :
    R.preservesSelectedInvariants h :=
  R.invariantCertificate h

/-- VI.定義9.1: selected endpoint equivalence preserves selected essence. -/
theorem preservesSelectedEssence_holds
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G)
    {a b : G.State} (h : R.RefactorEquivalent a b) :
    R.preservesSelectedEssence h :=
  R.essenceCertificate h

end RefactorEndpointReading

/-- VI.定義9.1: a path whose endpoint is selected-refactor equivalent to a target. -/
def EndpointEquivalentPath {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G)
    {a b target : G.State} (_gamma : OperationPath G a b) : Prop :=
  R.RefactorEquivalent b target

/-- VI.定義9.2: operation loop as a path returning up to refactor equivalence. -/
structure OperationLoop {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G) where
  base : G.State
  endpoint : G.State
  gamma : OperationPath G base endpoint
  endpoint_equivalent : R.RefactorEquivalent endpoint base

namespace OperationLoop

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}

/-- VI.定義9.2: the identity path is an operation loop. -/
def identity (a : G.State) : OperationLoop R where
  base := a
  endpoint := a
  gamma := OperationPath.id a
  endpoint_equivalent := R.refl a

/-- VI.定義9.2: expose endpoint-equivalence for a selected operation loop. -/
theorem endpoint_equivalent_holds (L : OperationLoop R) :
    R.RefactorEquivalent L.endpoint L.base :=
  L.endpoint_equivalent

end OperationLoop

end SingularityMonodromyStack
end AAT.AG
