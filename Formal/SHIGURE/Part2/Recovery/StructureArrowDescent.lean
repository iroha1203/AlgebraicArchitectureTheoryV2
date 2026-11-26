import Formal.SHIGURE.Part2.Recovery.SheafArrowDescent

/-!
# Gluing structure-preserving arrows over a coefficient cover

The carrier maps glue on the relative Zariski site. Membership in the
relation and domain sheaves is local, and equality of the operation maps
is detected by their restrictions. This gives a unique preserving arrow.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {sig : Signature.{u}} (C : Scheme.OpenCover.{u} S)
  (A B : SheafStructure sig (Scheme.zariskiTopology.over S))

/-- Compatible preserving maps on a coefficient cover, with overlap compatibility at each sort. -/
structure LocalStructureMaps where
  /-- The preserving arrow on each cover member. -/
  onOpen (i : C.I₀) : restrictStructure (C.f i) A ⟶ restrictStructure (C.f i) B
  /-- The local carrier arrows agree on the overlap at every sort. -/
  agree (s : sig.SortType) (i j : C.I₀) {T : Over S} {U : Over (C.X i)} {V : Over (C.X j)}
    (a : T ⟶ (Over.map (C.f i)).obj U) (b : T ⟶ (Over.map (C.f j)).obj V)
    (x : (A.carrier s).val.obj (op ((Over.map (C.f i)).obj U)))
    (y : (A.carrier s).val.obj (op ((Over.map (C.f j)).obj V))) :
    (A.carrier s).val.map a.op x = (A.carrier s).val.map b.op y →
      (B.carrier s).val.map a.op (((onOpen i).onSort s).val.app (op U) x) =
        (B.carrier s).val.map b.op (((onOpen j).onSort s).val.app (op V) y)

namespace LocalStructureMaps

variable {C A B} (D : LocalStructureMaps C A B)

/-- Restrict a global preserving map to the cover. -/
def ofGlobal (h : A ⟶ B) : LocalStructureMaps C A B where
  onOpen i := restrictStructureMap (C.f i) h
  agree s := (LocalSheafMaps.ofGlobal (C := C) (h.onSort s)).agree

private def onCarrier (s : sig.SortType) : LocalSheafMaps C (A.carrier s) (B.carrier s) :=
  ⟨fun i => (D.onOpen i).onSort s, D.agree s⟩

private def gluedCarriers (s : sig.SortType) : A.carrier s ⟶ B.carrier s :=
  (D.onCarrier s).glue

private theorem gluedCarriers_restrict (i : C.I₀) :
    (fun s => (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map (D.gluedCarriers s)) =
      (D.onOpen i).onSort :=
  funext fun s => (D.onCarrier s).glue_onOpen i

private theorem gluedCarriers_predicate {Γ : List sig.SortType} (P : SheafPredicate (sheafTuple A.carrier Γ))
    (Q : SheafPredicate (sheafTuple B.carrier Γ))
    (preserves : ∀ i, (restrictPredicate (C.f i) P).carrier ≤
      ((restrictPredicate (C.f i) Q).preimage (sheafTupleMap (D.onOpen i).onSort Γ)).carrier) :
    P.carrier ≤ (Q.preimage (sheafTupleMap D.gluedCarriers Γ)).carrier := by
  intro U x hx
  let t := sheafTupleMap D.gluedCarriers Γ
  apply coefficientCoverTest_predicate C U.unop Q
  intro i
  let T := coefficientCoverTest C U.unop i
  let g := coefficientCoverTestInclusion C U.unop i
  rw [← FunctorToTypes.naturality _ _ t.val g.op]
  have mem := P.carrier.map g.op hx
  have localMem := preserves i (op T) mem
  change (sheafTupleMap (D.onOpen i).onSort Γ).val.app (op T) ((sheafTuple A.carrier Γ).val.map g.op x) ∈
    (restrictPredicate (C.f i) Q).carrier.obj (op T) at localMem
  rw [← D.gluedCarriers_restrict i] at localMem
  exact localMem

/-- The glued carrier maps preserve every primitive, including the maps on partial domains. -/
def glue : A ⟶ B where
  onSort := D.gluedCarriers
  preservesTotal p := by
    apply coefficientCover_sheafMap_ext C
    intro i
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    change (restrictStructure (C.f i) A).total p ≫
        (fun s => (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map (D.gluedCarriers s)) _ =
      sheafTupleMap (fun s => (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map (D.gluedCarriers s)) _ ≫
        (restrictStructure (C.f i) B).total p
    rw [D.gluedCarriers_restrict i]
    exact (D.onOpen i).preservesTotal p
  preservesRelation r := D.gluedCarriers_predicate (A.relation r) (B.relation r)
    (fun i => (D.onOpen i).preservesRelation r)
  preservesDomain p := D.gluedCarriers_predicate (A.partialDomain p) (B.partialDomain p)
    (fun i => (D.onOpen i).preservesDomain p)
  preservesPartial p := by
    apply coefficientCover_sheafMap_ext C
    intro i
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    let carr := fun s => (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map (D.gluedCarriers s)
    let A' := restrictStructure (C.f i) A
    let B' := restrictStructure (C.f i) B
    let domain (c : ∀ s, A'.carrier s ⟶ B'.carrier s) : Prop :=
      (A'.partialDomain p).carrier ≤ ((B'.partialDomain p).preimage
        (sheafTupleMap c (sig.partialArity p).inputs)).carrier
    let condition (c : ∀ s, A'.carrier s ⟶ B'.carrier s) : Prop :=
      ∀ hc : domain c,
        A'.partialValue p ≫ c _ = SheafPredicate.mapAlong (sheafTupleMap c _) hc ≫ B'.partialValue p
    have isLocal : condition (D.onOpen i).onSort := fun _ => (D.onOpen i).preservesPartial p
    have mapsDomain : domain carr := Eq.mp (congrArg domain (D.gluedCarriers_restrict i).symm)
      ((D.onOpen i).preservesDomain p)
    change A'.partialValue p ≫ carr _ =
      SheafPredicate.mapAlong (sheafTupleMap carr _) mapsDomain ≫ B'.partialValue p
    exact (Eq.mp (congrArg condition (D.gluedCarriers_restrict i).symm) isLocal) mapsDomain
  preservesQuantity q := by
    apply coefficientCover_sheafMap_ext C
    intro i
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    let carr := fun s => (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map (D.gluedCarriers s)
    change (restrictStructure (C.f i) A).quantity q ≫ carr _ =
      sheafTupleMap carr _ ≫ (restrictStructure (C.f i) B).quantity q
    dsimp only [carr]
    rw [D.gluedCarriers_restrict i, congrFun (D.gluedCarriers_restrict i) (sig.quantityArity q).output]
    exact (D.onOpen i).preservesQuantity q

/-- The global preserving map recovers the local arrows. -/
theorem glue_onOpen (i : C.I₀) : restrictStructureMap (C.f i) D.glue = D.onOpen i :=
  SheafStructure.Hom.ext (D.gluedCarriers_restrict i)

/-- The gluing is the unique preserving map with the required restrictions. -/
theorem existsUnique_glue : ∃! f : A ⟶ B, ∀ i, restrictStructureMap (C.f i) f = D.onOpen i :=
  ⟨D.glue, D.glue_onOpen, fun _ h => restrictStructureMap_openCover_ext C _ _
    (fun i => (h i).trans (D.glue_onOpen i).symm)⟩

end LocalStructureMaps
end SHIGURE.Copying
