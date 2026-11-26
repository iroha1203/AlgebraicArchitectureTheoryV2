import Formal.SHIGURE.Part2.Recovery.PredicateDescent
import Formal.SHIGURE.Part2.Recovery.StructureArrowDescent
import Formal.SHIGURE.Part2.Recovery.SheafStructureIso

/-!
# Effective descent of primitive sheaf structures

A chart isomorphism preserves all primitive data on the common
fiber product. The carrier cocycle also acts on tuples and their
subsheaves. Their compatible arrows provide the glued operations.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} (C : Scheme.OpenCover.{u} S) (sig : Signature.{u})

/-- Primitive structures on each chart, compared on the actual pairwise fiber products. -/
structure StructureCharts where
  /-- A primitive structure on the relative site of the chart. -/
  chart (i : C.I₀) : SheafStructure sig (Scheme.zariskiTopology.over (C.X i))
  /-- The transition respects every primitive of the structures. -/
  transition (i j : C.I₀) :
    restrictStructure (pullback.fst (C.f i) (C.f j)) (chart i) ≅
      restrictStructure (pullback.snd (C.f i) (C.f j)) (chart j)

namespace StructureCharts

variable {C sig} (D : StructureCharts C sig)

/-- Each sort gives sheaf charts on the same open cover. -/
def carrierCharts (s : sig.SortType) : SheafCharts C where
  chart i := (D.chart i).carrier s
  transition i j :=
    ⟨(D.transition i j).hom.onSort s, (D.transition i j).inv.onSort s,
      congrArg (fun f => f.onSort s) (D.transition i j).hom_inv_id,
      congrArg (fun f => f.onSort s) (D.transition i j).inv_hom_id⟩

/-- The cocycle on structure isomorphisms is checked at every sort, which determines those arrows. -/
abbrev Coherent := ∀ s, (D.carrierCharts s).Coherent

/-- Total operations give compatible local sheaf maps from the full input tuples. -/
def totalCharts (p : sig.Total) :
    (SheafCharts.tuples D.carrierCharts (sig.totalArity p).inputs).Arrow (D.carrierCharts (sig.totalArity p).output) :=
  SheafCharts.Arrow.ofOverlap _ (fun i => (D.chart i).total p) (fun i j => (D.transition i j).hom.preservesTotal p)

/-- Quantities give compatible local sheaf maps from the full input tuples. -/
def quantityCharts (q : sig.Quantity) :
    (SheafCharts.tuples D.carrierCharts (sig.quantityArity q).inputs).Arrow (D.carrierCharts (sig.quantityArity q).output) :=
  SheafCharts.Arrow.ofOverlap _ (fun i => (D.chart i).quantity q) (fun i j => (D.transition i j).hom.preservesQuantity q)

/-- The transitions preserve the relation predicate in both directions. -/
def relationCharts (r : sig.Rel) :
    SheafCharts.PreservesPredicates D.carrierCharts (sig.relInputs r) (fun i => (D.chart i).relation r) :=
  ⟨fun i j => (D.transition i j).hom.preservesRelation r, fun i j => (D.transition i j).inv.preservesRelation r⟩

/-- The transitions preserve the partial domain in both directions. -/
def domainCharts (p : sig.Partial) :
    SheafCharts.PreservesPredicates D.carrierCharts (sig.partialArity p).inputs (fun i => (D.chart i).partialDomain p) :=
  ⟨fun i j => (D.transition i j).hom.preservesDomain p, fun i j => (D.transition i j).inv.preservesDomain p⟩

/-- Partial values give compatible local sheaf maps on the specified partial domains. -/
def partialCharts (p : sig.Partial) :
    (SheafCharts.predicateCharts (D.domainCharts p)).Arrow (D.carrierCharts (sig.partialArity p).output) :=
  SheafCharts.Arrow.ofOverlap _ (fun i => (D.chart i).partialValue p)
    (fun i j => (D.transition i j).hom.preservesPartial p)

/-- Glue the carriers, all operations and quantities, and the specified relations and domains. -/
def glue (hD : D.Coherent) : SheafStructure sig (Scheme.zariskiTopology.over S) where
  carrier s := (D.carrierCharts s).matchingSheaf
  total p := (SheafCharts.tupleComparisonIso D.carrierCharts (sig.totalArity p).inputs hD).inv ≫ (D.totalCharts p).glue
  relation r := SheafCharts.gluedPredicate (D.relationCharts r) hD
  partialDomain p := SheafCharts.gluedPredicate (D.domainCharts p) hD
  partialValue p := (SheafCharts.gluedPredicateIso (D.domainCharts p) hD).inv ≫ (D.partialCharts p).glue
  quantity q := (SheafCharts.tupleComparisonIso D.carrierCharts (sig.quantityArity q).inputs hD).inv ≫
    (D.quantityCharts q).glue

private abbrev chartCarrierIso (hD : D.Coherent) (i : C.I₀) (s : sig.SortType) :=
  (D.carrierCharts s).restrictMatchingIso (hD s) i

private theorem restrictTotalMap (hD : D.Coherent) (i : C.I₀) {Γ : List sig.SortType} {s : sig.SortType}
    (f : (SheafCharts.tuples D.carrierCharts Γ).Arrow (D.carrierCharts s)) :
    (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map
        ((SheafCharts.tupleComparisonIso D.carrierCharts Γ hD).inv ≫ f.glue) ≫ (D.chartCarrierIso hD i s).hom =
      sheafTupleMap (fun t => (D.chartCarrierIso hD i t).hom) Γ ≫ f.onChart i := by
  ext V x
  let T := (Over.map (C.f i)).obj V.unop
  let a := CoverLift.ofTest V.unop
  let e := SheafCharts.tupleComparisonIso D.carrierCharts Γ hD
  let y := e.inv.val.app (op T) x
  have hy : (SheafCharts.tupleComparison D.carrierCharts Γ).val.app (op T) y = x :=
    congrArg (fun g => g.val.app (op T) x) e.inv_hom_id
  change (D.carrierCharts s).readChart a (f.glue.val.app (op T) y) =
    (f.onChart i).val.app (op a.test) ⟨fun {t} v => (D.carrierCharts t).readChart a (x.get v)⟩
  rw [f.glue_readChart]
  refine congrArg ((f.onChart i).val.app (op a.test)) (Assignment.ext ?_)
  intro t v
  exact (SheafCharts.tupleComparison_readChart D.carrierCharts Γ a y v).symm.trans
    (congrArg (fun z : (sheafTuple (fun t => (D.carrierCharts t).matchingSheaf) Γ).val.obj (op T) =>
      (D.carrierCharts t).readChart a (z.get v)) hy)

private theorem restrictGluedPredicate (hD : D.Coherent) (i : C.I₀) {Γ : List sig.SortType}
    {P : ∀ i, SheafPredicate ((SheafCharts.tuples D.carrierCharts Γ).chart i)}
    (hP : SheafCharts.PreservesPredicates D.carrierCharts Γ P) :
    (restrictPredicate (C.f i) (SheafCharts.gluedPredicate hP hD)).carrier =
      ((P i).preimage (sheafTupleMap (fun s => (D.chartCarrierIso hD i s).hom) Γ)).carrier := by
  ext U x
  exact SheafCharts.gluedPredicate_mem_iff hP hD (CoverLift.ofTest U.unop) x

private theorem restrictPartialMap (hD : D.Coherent) (i : C.I₀) {Γ : List sig.SortType} {s : sig.SortType}
    {P : ∀ i, SheafPredicate ((SheafCharts.tuples D.carrierCharts Γ).chart i)}
    (hP : SheafCharts.PreservesPredicates D.carrierCharts Γ P)
    (f : (SheafCharts.predicateCharts hP).Arrow (D.carrierCharts s)) :
    (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map
        ((SheafCharts.gluedPredicateIso hP hD).inv ≫ f.glue) ≫ (D.chartCarrierIso hD i s).hom =
      SheafPredicate.mapAlong (sheafTupleMap (fun t => (D.chartCarrierIso hD i t).hom) Γ)
        (le_of_eq (D.restrictGluedPredicate hD i hP)) ≫ f.onChart i := by
  ext V x
  let T := (Over.map (C.f i)).obj V.unop
  let a := CoverLift.ofTest V.unop
  let e := SheafCharts.gluedPredicateIso hP hD
  let Q := SheafCharts.gluedPredicate hP hD
  let y := e.inv.val.app (op T) x
  have hy : (SheafCharts.gluedPredicateMap hP).val.app (op T) y = x.val :=
    congrArg (fun g : Q.toSheaf ⟶ sheafTuple (fun t => (D.carrierCharts t).matchingSheaf) Γ => g.val.app (op T) x)
      (show e.inv ≫ SheafCharts.gluedPredicateMap hP = Q.inclusion by
        change e.inv ≫ e.hom ≫ Q.inclusion = Q.inclusion
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp])
  change (D.carrierCharts s).readChart a (f.glue.val.app (op T) y) = (f.onChart i).val.app (op a.test) _
  rw [f.glue_readChart]
  apply congrArg ((f.onChart i).val.app (op a.test))
  apply Subtype.ext
  apply Assignment.ext
  intro t v
  exact (SheafCharts.gluedPredicateMap_readChart hP a y v).symm.trans
    (congrArg (fun z : (sheafTuple (fun t => (D.carrierCharts t).matchingSheaf) Γ).val.obj (op T) =>
      (D.carrierCharts t).readChart a (z.get v)) hy)

/-- The glued structure recovers all the primitives of each original chart under restriction. -/
def restrictGlueIso (hD : D.Coherent) (i : C.I₀) : restrictStructure (C.f i) (D.glue hD) ≅ D.chart i :=
  SheafStructure.isoOfCarrier (D.chartCarrierIso hD i)
    (fun p => D.restrictTotalMap hD i (D.totalCharts p))
    (fun q => D.restrictTotalMap hD i (D.quantityCharts q))
    (fun r => D.restrictGluedPredicate hD i (D.relationCharts r))
    (fun p => D.restrictGluedPredicate hD i (D.domainCharts p))
    (fun p => D.restrictPartialMap hD i (D.domainCharts p) (D.partialCharts p))

/-- The chart comparison on a relative test is the carrier reading used in the gluing. -/
theorem restrictGlueIso_app (hD : D.Coherent) (i : C.I₀) (s : sig.SortType) (T : Over (C.X i))
    (x : ((D.glue hD).carrier s).val.obj (op ((Over.map (C.f i)).obj T))) :
    ((D.restrictGlueIso hD i).hom.onSort s).val.app (op T) x =
      (D.carrierCharts s).readChart (CoverLift.ofTest T) x := rfl

/-- The two comparisons of the glued structure on any common test give the original transition. -/
theorem restrictGlue_transition (hD : D.Coherent) {i j : C.I₀} {T : Over S}
    (a : CoverLift C i T) (b : CoverLift C j T) (s : sig.SortType) (x : ((D.glue hD).carrier s).val.obj (op T)) :
    (D.carrierCharts s).transitionAt a b ((D.carrierCharts s).readChart a x) =
      (D.carrierCharts s).readChart b x :=
  (D.carrierCharts s).readChart_agrees a b x

/-- A locally split structure is obtained by gluing locally split chart structures. -/
theorem glue_isZariskiSplit {T : Theory.{u}} {D : StructureCharts C T.signature} (hD : D.Coherent)
    (split : ∀ i, IsZariskiSplit T (D.chart i)) : IsZariskiSplit T (D.glue hD) := by
  choose K hK using split
  refine ⟨C.bind K, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨M, ⟨e⟩⟩ := hK i j
  refine ⟨M, ⟨?_⟩⟩
  exact (eqToIso (restrictStructure_comp ((K i).f j) (C.f i) (D.glue hD))).symm ≪≫
    (restrictStructureFunctor T.signature ((K i).f j)).mapIso (D.restrictGlueIso hD i) ≪≫ e

/-- Every written Law descends along the comparisons of the glued structure. -/
theorem glue_holdsLaw (hD : D.Coherent) (law : Law sig) (h : ∀ i, (D.chart i).holdsLaw law) :
    (D.glue hD).holdsLaw law :=
  holdsLaw_of_openCover C _ law (fun i => SheafStructure.holdsLaw_of_iso (D.restrictGlueIso hD i).symm law (h i))

/-- Effective object descent takes local models and their descent data to a global copying model. -/
def glueModel {T : Theory.{u}} {D : StructureCharts C T.signature} (hD : D.Coherent)
    (models : ∀ i, zariskiCopyingProperty T (C.X i) (D.chart i)) :
    (zariskiCopyingProperty T S).FullSubcategory :=
  ⟨D.glue hD, glue_isZariskiSplit hD (fun i => (models i).1),
    fun l => D.glue_holdsLaw hD (T.law l) (fun i => (models i).2 l)⟩

end StructureCharts
end SHIGURE.Copying
