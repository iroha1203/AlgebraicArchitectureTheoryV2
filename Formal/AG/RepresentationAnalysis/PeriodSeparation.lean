import Formal.AG.RepresentationAnalysis.Period
import Mathlib.Data.Fintype.Card

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y z

/--
VII.定理6.1: selected graph / semantic / effect reading family used for period
separation witnesses.

This is a finite witness surface, not a completeness theorem about all
representations.  It records three broad readings of the same selected object
carrier.
-/
structure PeriodSeparationReadingFamily where
  Object : Type u
  GraphReading : Type v
  SemanticReading : Type w
  EffectReading : Type x
  graphReading : Object -> GraphReading
  semanticReading : Object -> SemanticReading
  effectReading : Object -> EffectReading

namespace PeriodSeparationReadingFamily

variable (F : PeriodSeparationReadingFamily.{u, v, w, x})

/-- VII.定理6.1: same graph broad period / reading. -/
def SameGraphReading (X Y : F.Object) : Prop :=
  F.graphReading X = F.graphReading Y

/-- VII.定理6.1: separated semantic broad period / reading. -/
def SemanticSeparated (X Y : F.Object) : Prop :=
  F.semanticReading X ≠ F.semanticReading Y

/-- VII.定理6.1: separated effect broad period / reading. -/
def EffectSeparated (X Y : F.Object) : Prop :=
  F.effectReading X ≠ F.effectReading Y

/-- VII.定理6.1: at least one non-graph reading separates the selected pair. -/
def NonGraphReadingSeparated (X Y : F.Object) : Prop :=
  F.SemanticSeparated X Y ∨ F.EffectSeparated X Y

/-- VII.定理6.1: selected period separation property for a reading family. -/
def PeriodSeparation : Prop :=
  ∃ X Y : F.Object, F.SameGraphReading X Y ∧ F.NonGraphReadingSeparated X Y

end PeriodSeparationReadingFamily

/--
VII.定理6.1 witness: two selected objects with the same graph reading but a
different semantic or effect reading.
-/
structure PeriodSeparationWitness
    (F : PeriodSeparationReadingFamily.{u, v, w, x}) where
  X : F.Object
  Y : F.Object
  sameGraphReading : F.SameGraphReading X Y
  nonGraphReadingSeparated : F.NonGraphReadingSeparated X Y

namespace PeriodSeparationWitness

variable {F : PeriodSeparationReadingFamily.{u, v, w, x}}

/-- VII.定理6.1: the selected witness gives period separation. -/
theorem periodSeparation (W : PeriodSeparationWitness F) :
    F.PeriodSeparation :=
  ⟨W.X, W.Y, W.sameGraphReading, W.nonGraphReadingSeparated⟩

/-- VII.定理6.1: expose the same-graph reading from the witness. -/
theorem sameGraphReading_holds (W : PeriodSeparationWitness F) :
    F.SameGraphReading W.X W.Y :=
  W.sameGraphReading

/-- VII.定理6.1: expose non-graph separation from the witness. -/
theorem nonGraphReadingSeparated_holds (W : PeriodSeparationWitness F) :
    F.NonGraphReadingSeparated W.X W.Y :=
  W.nonGraphReadingSeparated

end PeriodSeparationWitness

/--
VII.定理6.1: the graph / semantic / effect reading family selected from an
existing `RepresentationFamily`.
-/
def RepresentationFamily.toPeriodSeparationReadingFamily
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter.{u, v, w, x} raw}
    (F : RepresentationFamily p)
    (graphIndex semanticIndex effectIndex : F.Index) :
    PeriodSeparationReadingFamily where
  Object := AATSch p
  GraphReading := F.Target graphIndex
  SemanticReading := F.Target semanticIndex
  EffectReading := F.Target effectIndex
  graphReading := F.Read graphIndex
  semanticReading := F.Read semanticIndex
  effectReading := F.Read effectIndex

/--
VII.定理6.1: selected period-separation witness inside an existing
`RepresentationFamily`.
-/
structure RepresentationFamilyPeriodSeparationWitness
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter.{u, v, w, x} raw}
    (F : RepresentationFamily p) where
  graphIndex : F.Index
  semanticIndex : F.Index
  effectIndex : F.Index
  X : AATSch p
  Y : AATSch p
  sameGraphReading : F.Read graphIndex X = F.Read graphIndex Y
  nonGraphReadingSeparated :
    F.Read semanticIndex X ≠ F.Read semanticIndex Y ∨
      F.Read effectIndex X ≠ F.Read effectIndex Y

namespace RepresentationFamilyPeriodSeparationWitness

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter.{u, v, w, x} raw}
variable {F : RepresentationFamily p}

/-- VII.定理6.1: convert a representation-family witness to the reading surface. -/
def toWitness (W : RepresentationFamilyPeriodSeparationWitness F) :
    PeriodSeparationWitness
      (F.toPeriodSeparationReadingFamily W.graphIndex W.semanticIndex W.effectIndex) where
  X := W.X
  Y := W.Y
  sameGraphReading := W.sameGraphReading
  nonGraphReadingSeparated := W.nonGraphReadingSeparated

/--
VII.定理6.1: a witness inside an existing `RepresentationFamily` gives period
separation for the selected graph / semantic / effect indices.
-/
theorem periodSeparation (W : RepresentationFamilyPeriodSeparationWitness F) :
    (F.toPeriodSeparationReadingFamily
      W.graphIndex W.semanticIndex W.effectIndex).PeriodSeparation :=
  W.toWitness.periodSeparation

end RepresentationFamilyPeriodSeparationWitness

namespace PeriodSeparationExample62

/-- VII.例6.2: the two selected finite architecture geometries. -/
inductive Geometry where
  | X
  | Y
deriving DecidableEq, Fintype

/-- VII.例6.2: the shared graph broad reading. -/
inductive GraphReading where
  | sharedDependencyGraph
deriving DecidableEq, Fintype

/-- VII.例6.2: semantic readings distinguished by the selected finite example. -/
inductive SemanticReading where
  | contractRespected
  | contractViolated
deriving DecidableEq, Fintype

/-- VII.例6.2: effect readings distinguished by the selected finite example. -/
inductive EffectReading where
  | harmlessEffect
  | harmfulEffect
deriving DecidableEq, Fintype

/-- VII.例6.2: graph reading forgets the semantic / effect distinction. -/
def graphReading (_X : Geometry) : GraphReading :=
  GraphReading.sharedDependencyGraph

/-- VII.例6.2: selected semantic reading. -/
def semanticReading : Geometry -> SemanticReading
  | Geometry.X => SemanticReading.contractRespected
  | Geometry.Y => SemanticReading.contractViolated

/-- VII.例6.2: selected effect reading. -/
def effectReading : Geometry -> EffectReading
  | Geometry.X => EffectReading.harmlessEffect
  | Geometry.Y => EffectReading.harmfulEffect

/-- VII.例6.2: finite graph / semantic / effect representation family. -/
def family : PeriodSeparationReadingFamily where
  Object := Geometry
  GraphReading := GraphReading
  SemanticReading := SemanticReading
  EffectReading := EffectReading
  graphReading := graphReading
  semanticReading := semanticReading
  effectReading := effectReading

/-- VII.例6.2: the selected pair has the same graph reading. -/
theorem sameGraphReading :
    family.SameGraphReading Geometry.X Geometry.Y :=
  rfl

/-- VII.例6.2: semantic reading separates the selected pair. -/
theorem semanticSeparated :
    family.SemanticSeparated Geometry.X Geometry.Y := by
  simp [PeriodSeparationReadingFamily.SemanticSeparated, family, semanticReading]

/-- VII.例6.2: effect reading separates the selected pair. -/
theorem effectSeparated :
    family.EffectSeparated Geometry.X Geometry.Y := by
  simp [PeriodSeparationReadingFamily.EffectSeparated, family, effectReading]

/-- VII.例6.2: the selected object carrier is finite. -/
theorem geometry_card :
    Fintype.card Geometry = 2 := by
  decide

/-- VII.例6.2: the selected graph reading carrier has one value. -/
theorem graphReading_card :
    Fintype.card GraphReading = 1 := by
  decide

/-- VII.例6.2: the selected semantic reading carrier is finite with two values. -/
theorem semanticReading_card :
    Fintype.card SemanticReading = 2 := by
  decide

/-- VII.例6.2: the selected effect reading carrier is finite with two values. -/
theorem effectReading_card :
    Fintype.card EffectReading = 2 := by
  decide

/-- VII.例6.2: the selected finite witness for Period Separation. -/
def witness : PeriodSeparationWitness family where
  X := Geometry.X
  Y := Geometry.Y
  sameGraphReading := sameGraphReading
  nonGraphReadingSeparated := Or.inl semanticSeparated

/-- VII.例6.2: same graph broad period with different semantic reading. -/
theorem sameGraph_differentSemantic :
    family.SameGraphReading Geometry.X Geometry.Y ∧
      family.SemanticSeparated Geometry.X Geometry.Y :=
  ⟨sameGraphReading, semanticSeparated⟩

/-- VII.例6.2: same graph broad period with different effect reading. -/
theorem sameGraph_differentEffect :
    family.SameGraphReading Geometry.X Geometry.Y ∧
      family.EffectSeparated Geometry.X Geometry.Y :=
  ⟨sameGraphReading, effectSeparated⟩

/-- VII.定理6.1: Period Separation, proved by the finite witness of example 6.2. -/
theorem periodSeparation_theorem6_1 :
    family.PeriodSeparation :=
  witness.periodSeparation

end PeriodSeparationExample62

end RepresentationAnalysis
end AAT.AG
