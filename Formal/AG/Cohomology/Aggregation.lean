import Formal.AG.Cohomology.PeriodStokes

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

/--
IV.定義14.1: selected finite site morphism `pi : X_fine -> X_coarse`.

The object map is the finite-site aggregation surface.  It is intentionally a
selected map between the two AAT site categories and not a general geometric
morphism construction.
-/
structure FiniteSiteMorphism {U : AtomCarrier.{u}}
    {A_fine A_coarse : ArchitectureObject U}
    (S_fine : Site.AATSite A_fine) (S_coarse : Site.AATSite A_coarse) where
  mapObject : S_fine.category -> S_coarse.category
  preservesSelectedCover : Prop
  preservesSelectedCover_holds : preservesSelectedCover

/--
IV.定義14.1: selected pushforward coefficient surface `pi_* Ob`.

The carrier is explicit because this implementation layer only needs the comparison
surface and does not construct direct images for arbitrary site morphisms.
-/
structure PushforwardObstructionSheaf {U : AtomCarrier.{u}}
    {A_fine A_coarse : ArchitectureObject U}
    {S_fine : Site.AATSite A_fine} {S_coarse : Site.AATSite A_coarse}
    (pi : FiniteSiteMorphism S_fine S_coarse)
    (Ob : ObstructionSheaf S_fine) where
  carrier : ObstructionSheaf S_coarse
  readsSectionsByFinePullback : Prop
  readsSectionsByFinePullback_holds : readsSectionsByFinePullback

/--
IV.R12: Čech-style higher direct image surface `R^q pi_* Ob` for statements.

This is a statement-level carrier for theorem candidate 14.2; no derived
functor or spectral sequence construction is claimed here.
-/
structure HigherDirectImageCech {U : AtomCarrier.{u}}
    {A_fine A_coarse : ArchitectureObject U}
    {S_fine : Site.AATSite A_fine} {S_coarse : Site.AATSite A_coarse}
    (pi : FiniteSiteMorphism S_fine S_coarse)
    (Ob : ObstructionSheaf S_fine) (q : Nat) where
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  cechComputes : Prop
  cechComputes_holds : cechComputes

attribute [instance] HigherDirectImageCech.addCommGroup

/--
IV.R12: comparison map
`H^1(X_coarse, pi_* Ob) -> H^1(X_fine, Ob)`.
-/
structure AggregationComparisonMap {U : AtomCarrier.{u}}
    {A_fine A_coarse : ArchitectureObject U}
    {S_fine : Site.AATSite A_fine} {S_coarse : Site.AATSite A_coarse}
    {pi : FiniteSiteMorphism S_fine S_coarse}
    {Ob : ObstructionSheaf S_fine}
    (POb : PushforwardObstructionSheaf pi Ob) where
  coarseH1 : Type u
  fineH1 : Type u
  coarseAddCommGroup : AddCommGroup coarseH1
  fineAddCommGroup : AddCommGroup fineH1
  comparison : coarseH1 →+ fineH1
  comparisonReadsPullback : Prop
  comparisonReadsPullback_holds : comparisonReadsPullback

attribute [instance] AggregationComparisonMap.coarseAddCommGroup
attribute [instance] AggregationComparisonMap.fineAddCommGroup

namespace AggregationComparisonMap

variable {U : AtomCarrier.{u}}
variable {A_fine A_coarse : ArchitectureObject U}
variable {S_fine : Site.AATSite A_fine} {S_coarse : Site.AATSite A_coarse}
variable {pi : FiniteSiteMorphism S_fine S_coarse}
variable {Ob : ObstructionSheaf S_fine}
variable {POb : PushforwardObstructionSheaf pi Ob}

/-- IV.R12: membership in the image of the aggregation comparison map. -/
def InComparisonImage (M : AggregationComparisonMap POb) (x : M.fineH1) : Prop :=
  ∃ y : M.coarseH1, M.comparison y = x

end AggregationComparisonMap

/--
IV.定理候補14.2: five-term aggregation statement shape.

The theorem candidate is intentionally statement-only.  It records the exact
five-object low-degree shape needed for aggregation without proving a spectral
sequence.
-/
structure AggregationFiveTermStatement {U : AtomCarrier.{u}}
    {A_fine A_coarse : ArchitectureObject U}
    {S_fine : Site.AATSite A_fine} {S_coarse : Site.AATSite A_coarse}
    {pi : FiniteSiteMorphism S_fine S_coarse}
    {Ob : ObstructionSheaf S_fine}
    (POb : PushforwardObstructionSheaf pi Ob) where
  H1_coarse_piOb : Type u
  H1_fine_Ob : Type u
  H0_coarse_R1piOb : Type u
  H2_coarse_piOb : Type u
  H2_fine_Ob : Type u
  add_H1_coarse : AddCommGroup H1_coarse_piOb
  add_H1_fine : AddCommGroup H1_fine_Ob
  add_H0_R1 : AddCommGroup H0_coarse_R1piOb
  add_H2_coarse : AddCommGroup H2_coarse_piOb
  add_H2_fine : AddCommGroup H2_fine_Ob
  edge_H1coarse_H1fine : H1_coarse_piOb →+ H1_fine_Ob
  edge_H1fine_H0R1 : H1_fine_Ob →+ H0_coarse_R1piOb
  edge_H0R1_H2coarse : H0_coarse_R1piOb →+ H2_coarse_piOb
  edge_H2coarse_H2fine : H2_coarse_piOb →+ H2_fine_Ob
  exactness : Prop

attribute [instance] AggregationFiveTermStatement.add_H1_coarse
attribute [instance] AggregationFiveTermStatement.add_H1_fine
attribute [instance] AggregationFiveTermStatement.add_H0_R1
attribute [instance] AggregationFiveTermStatement.add_H2_coarse
attribute [instance] AggregationFiveTermStatement.add_H2_fine

/--
IV.定義14.3: scale-stable debt over a selected aggregation family.

A debt class is scale-stable when every selected aggregation map reads it as
coming from the corresponding coarse comparison image.
-/
structure ScaleStableDebt where
  AggregationIndex : Type u
  FineDebt : Type u
  fineDebtAddCommGroup : AddCommGroup FineDebt
  CoarseDebt : AggregationIndex -> Type u
  coarseDebtAddCommGroup : ∀ i : AggregationIndex, AddCommGroup (CoarseDebt i)
  comparison : ∀ i : AggregationIndex, CoarseDebt i →+ FineDebt
  debtClass : FineDebt
  stable : ∀ i : AggregationIndex, ∃ y : CoarseDebt i, comparison i y = debtClass

attribute [instance] ScaleStableDebt.fineDebtAddCommGroup
attribute [instance] ScaleStableDebt.coarseDebtAddCommGroup

namespace ScaleStableDebt

/-- IV.定義14.3: read scale stability for a selected aggregation. -/
theorem in_comparison_image (D : ScaleStableDebt.{u}) (i : D.AggregationIndex) :
    ∃ y : D.CoarseDebt i, D.comparison i y = D.debtClass :=
  D.stable i

end ScaleStableDebt

end Cohomology
end AAT.AG
