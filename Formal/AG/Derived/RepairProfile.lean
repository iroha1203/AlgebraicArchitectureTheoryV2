import Formal.AG.Derived.Transversality

noncomputable section

namespace AAT.AG
namespace Derived

universe u v w

namespace RepairProfile

/-- V.定義8.1: repair comparison may be read at section level or geometry level. -/
inductive RepairComparisonLevel where
  | section
  | geometry
  deriving DecidableEq

/--
V.定義8.1: selected repair comparison profile.

The profile records both the comparison relation and the stronger improvement
predicate at section and geometry level. The only built-in theorem is that
improvement implies the chosen comparison; preorder or monotonicity laws must be
supplied by later profiles when they are needed.
-/
structure RepairComparisonProfile where
  Section : Type u
  Geometry : Type u
  sectionComparison : Section -> Section -> Prop
  geometryComparison : Geometry -> Geometry -> Prop
  sectionImproves : Section -> Section -> Prop
  geometryImproves : Geometry -> Geometry -> Prop
  section_improves_implies_comparison :
    ∀ {s' s : Section}, sectionImproves s' s -> sectionComparison s' s
  geometry_improves_implies_comparison :
    ∀ {X' X : Geometry}, geometryImproves X' X -> geometryComparison X' X

namespace RepairComparisonProfile

/-- V.定義8.1: the selected section-level comparison. -/
def sectionLe (P : RepairComparisonProfile.{u}) (s' s : P.Section) : Prop :=
  P.sectionComparison s' s

/-- V.定義8.1: the selected geometry-level comparison. -/
def geometryLe (P : RepairComparisonProfile.{u}) (X' X : P.Geometry) : Prop :=
  P.geometryComparison X' X

/-- V.定義8.1: section-level improvement implies the selected section comparison. -/
theorem sectionComparison_of_improves
    (P : RepairComparisonProfile.{u}) {s' s : P.Section}
    (h : P.sectionImproves s' s) :
    P.sectionLe s' s :=
  P.section_improves_implies_comparison h

/-- V.定義8.1: geometry-level improvement implies the selected geometry comparison. -/
theorem geometryComparison_of_improves
    (P : RepairComparisonProfile.{u}) {X' X : P.Geometry}
    (h : P.geometryImproves X' X) :
    P.geometryLe X' X :=
  P.geometry_improves_implies_comparison h

/-- V.定義8.1: a representative ideal-order repair profile. -/
def idealOrderRepairProfile (A : Type v) [CommRing A]
    {Section Geometry : Type u}
    (sectionIdeal : Section -> Ideal A)
    (geometryIdeal : Geometry -> Ideal A) :
    RepairComparisonProfile.{u} where
  Section := Section
  Geometry := Geometry
  sectionComparison := fun s' s => sectionIdeal s' < sectionIdeal s
  geometryComparison := fun X' X => geometryIdeal X' < geometryIdeal X
  sectionImproves := fun s' s => sectionIdeal s' < sectionIdeal s
  geometryImproves := fun X' X => geometryIdeal X' < geometryIdeal X
  section_improves_implies_comparison := fun h => h
  geometry_improves_implies_comparison := fun h => h

/-- V.定義8.1: a representative valuation repair profile. -/
def valuationRepairProfile
    {Section Geometry : Type u}
    (sectionValuation : Section -> Nat)
    (geometryValuation : Geometry -> Nat) :
    RepairComparisonProfile.{u} where
  Section := Section
  Geometry := Geometry
  sectionComparison := fun s' s => sectionValuation s' < sectionValuation s
  geometryComparison := fun X' X => geometryValuation X' < geometryValuation X
  sectionImproves := fun s' s => sectionValuation s' < sectionValuation s
  geometryImproves := fun X' X => geometryValuation X' < geometryValuation X
  section_improves_implies_comparison := fun h => h
  geometry_improves_implies_comparison := fun h => h

/-- V.定義8.1: a representative rank repair profile. -/
def rankRepairProfile
    {Section Geometry : Type u}
    (sectionRank : Section -> Nat)
    (geometryRank : Geometry -> Nat) :
    RepairComparisonProfile.{u} where
  Section := Section
  Geometry := Geometry
  sectionComparison := fun s' s => sectionRank s' < sectionRank s
  geometryComparison := fun X' X => geometryRank X' < geometryRank X
  sectionImproves := fun s' s => sectionRank s' < sectionRank s
  geometryImproves := fun X' X => geometryRank X' < geometryRank X
  section_improves_implies_comparison := fun h => h
  geometry_improves_implies_comparison := fun h => h

/-- V.定義8.1: a representative support repair profile. -/
def supportRepairProfile
    {Section Geometry : Type u} {Support : Type w}
    (sectionSupport : Section -> Set Support)
    (geometrySupport : Geometry -> Set Support) :
    RepairComparisonProfile.{u} where
  Section := Section
  Geometry := Geometry
  sectionComparison := fun s' s => sectionSupport s' < sectionSupport s
  geometryComparison := fun X' X => geometrySupport X' < geometrySupport X
  sectionImproves := fun s' s => sectionSupport s' < sectionSupport s
  geometryImproves := fun X' X => geometrySupport X' < geometrySupport X
  section_improves_implies_comparison := fun h => h
  geometry_improves_implies_comparison := fun h => h

end RepairComparisonProfile

/-- V.定義8.2: internal section repair or geometric repair. -/
inductive RepairKind where
  | internal
  | geometric
  deriving DecidableEq

/--
V.定義8.2: selected pullback / probe repair profile.

The field `pullbackObstructionComparison_holds` is the abstract Lean carrier for
the text's comparison `r^{-1} I'_U · O_X <= I_U`. The `probeComparison` fields
record the optional probe-level reading `(r circ s)^* I'_U <= s^* I_U`.
-/
structure PullbackRepairProfile (P : RepairComparisonProfile.{u}) where
  sourceGeometry : P.Geometry
  targetGeometry : P.Geometry
  Repair : Type u
  selectedRepair : Repair
  repairKind : RepairKind
  pullbackObstructionComparison : Prop
  pullbackObstructionComparison_holds : pullbackObstructionComparison
  probeComparison : P.Section -> Prop
  probeComparison_holds : ∀ s, probeComparison s
  geometryComparison_holds : P.geometryLe targetGeometry sourceGeometry
  geometryImproves_holds : P.geometryImproves targetGeometry sourceGeometry

namespace PullbackRepairProfile

variable {P : RepairComparisonProfile.{u}}

/-- V.定義8.2: the selected repair is internal exactly when the kind says so. -/
def IsInternal (R : PullbackRepairProfile P) : Prop :=
  R.repairKind = RepairKind.internal

/-- V.定義8.2: the selected repair is geometric exactly when the kind says so. -/
def IsGeometric (R : PullbackRepairProfile P) : Prop :=
  R.repairKind = RepairKind.geometric

/-- V.定義8.2: the pullback obstruction comparison carried by the profile. -/
theorem pullbackObstructionComparison_certificate
    (R : PullbackRepairProfile P) :
    R.pullbackObstructionComparison :=
  R.pullbackObstructionComparison_holds

/-- V.定義8.2: the probe-level obstruction comparison carried by the profile. -/
theorem probeComparison_certificate
    (R : PullbackRepairProfile P) (s : P.Section) :
    R.probeComparison s :=
  R.probeComparison_holds s

/-- V.定義8.2: the selected target geometry improves the selected source geometry. -/
theorem geometryImproves_certificate
    (R : PullbackRepairProfile P) :
    P.geometryImproves R.targetGeometry R.sourceGeometry :=
  R.geometryImproves_holds

end PullbackRepairProfile

/--
V.定義8.3: selected conflict comparison profile.

`RepairedConflict d` is the repaired-side conflict reading in the selected
positive degree. The comparison map and order are profile data; this file does
not choose pullback, pushforward, or probe semantics globally.
-/
structure ConflictComparisonProfile (A : Type v) [CommRing A]
    {I_U I_V : Ideal A}
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  Degree : Type u
  degree : Degree -> Nat
  positive_degree : ∀ d, 0 < degree d
  RepairedConflict : Degree -> Type v
  comparisonMap : (d : Degree) -> RepairedConflict d -> P.LawConflict (degree d)
  conflictOrder : (d : Degree) -> RepairedConflict d -> P.LawConflict (degree d) -> Prop
  comparisonMap_ordered :
    ∀ (d : Degree) (x : RepairedConflict d), conflictOrder d x (comparisonMap d x)
  vanishingPredicate : (d : Degree) -> RepairedConflict d -> Prop
  doesNotIncreaseSelectedConflict : Prop
  doesNotIncreaseSelectedConflict_holds : doesNotIncreaseSelectedConflict

namespace ConflictComparisonProfile

variable {A : Type v} [CommRing A]
variable {I_U I_V : Ideal A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/-- V.定義8.3: every selected degree is positive. -/
theorem selectedDegree_positive
    (Q : ConflictComparisonProfile.{u, v} A P) (d : Q.Degree) :
    0 < Q.degree d :=
  Q.positive_degree d

/-- V.定義8.3: the selected comparison map is ordered by the chosen conflict profile. -/
theorem comparisonMap_ordered_certificate
    (Q : ConflictComparisonProfile.{u, v} A P)
    (d : Q.Degree) (x : Q.RepairedConflict d) :
    Q.conflictOrder d x (Q.comparisonMap d x) :=
  Q.comparisonMap_ordered d x

/-- V.定義8.3: the profile records that selected repaired conflict does not increase. -/
theorem doesNotIncreaseSelectedConflict_certificate
    (Q : ConflictComparisonProfile.{u, v} A P) :
    Q.doesNotIncreaseSelectedConflict :=
  Q.doesNotIncreaseSelectedConflict_holds

end ConflictComparisonProfile

/-- V.定義8.4: repair path shape, either geometric morphism or section deformation. -/
inductive RepairPathKind where
  | geometryMorphism
  | sectionDeformation
  deriving DecidableEq

/-- V.定義8.4: `U`-axis obstruction decrease under the fixed profile. -/
def UAxisObstructionDecreases
    (P : RepairComparisonProfile.{u}) (s' s : P.Section) : Prop :=
  P.sectionImproves s' s

/-- V.定義8.4: selected repair path and its `U`-axis decrease certificate. -/
structure RepairPath (P : RepairComparisonProfile.{u}) where
  kind : RepairPathKind
  sourceGeometry : P.Geometry
  targetGeometry : P.Geometry
  sourceSection : P.Section
  targetSection : P.Section
  geometryComparison_holds : P.geometryLe targetGeometry sourceGeometry
  sectionComparison_holds : P.sectionLe targetSection sourceSection
  decreasesUAxis : Prop
  decreasesUAxis_holds : decreasesUAxis
  uAxisDecrease_holds :
    UAxisObstructionDecreases P targetSection sourceSection

namespace RepairPath

variable {P : RepairComparisonProfile.{u}}

/-- V.定義8.4: the path's declared decrease predicate holds. -/
theorem decreasesUAxis_certificate (ρ : RepairPath P) :
    ρ.decreasesUAxis :=
  ρ.decreasesUAxis_holds

/-- V.定義8.4: the target section improves the source section under `P_U`. -/
theorem uAxisDecrease_certificate (ρ : RepairPath P) :
    UAxisObstructionDecreases P ρ.targetSection ρ.sourceSection :=
  ρ.uAxisDecrease_holds

/-- V.定義8.4: the section-level comparison follows from the selected improvement. -/
theorem sectionComparison_of_uAxisDecrease (ρ : RepairPath P) :
    P.sectionLe ρ.targetSection ρ.sourceSection :=
  P.sectionComparison_of_improves ρ.uAxisDecrease_holds

end RepairPath

end RepairProfile

end Derived
end AAT.AG
