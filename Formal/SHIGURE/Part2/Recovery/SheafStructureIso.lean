import Formal.SHIGURE.Part2.Realizations.SheafStructureMaps

/-!
# Isomorphisms from the component sheaves

A carrier isomorphism preserving the operations and reflecting the
chosen predicates has a structure-preserving inverse. The inverse on
each partial domain is the restriction of the inverse on its tuples.
-/

open CategoryTheory

universe u v w

noncomputable section

namespace SHIGURE.SheafStructure

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C} {sig : Signature.{u}}
variable {A B : SheafStructure sig J}
variable (e : ∀ s, A.carrier s ≅ B.carrier s)

private theorem tuple_inv_hom (Γ : List sig.SortType) :
    sheafTupleMap (fun s => (e s).inv) Γ ≫ sheafTupleMap (fun s => (e s).hom) Γ = 𝟙 _ := by
  rw [← sheafTupleMap_comp]
  simp only [Iso.inv_hom_id, sheafTupleMap_id]

private theorem inversePredicate {Γ : List sig.SortType}
    (P : SheafPredicate (sheafTuple A.carrier Γ)) (Q : SheafPredicate (sheafTuple B.carrier Γ))
    (reflects : (Q.preimage (sheafTupleMap (fun s => (e s).hom) Γ)).carrier ≤ P.carrier) :
    Q.carrier ≤ (P.preimage (sheafTupleMap (fun s => (e s).inv) Γ)).carrier := by
  intro T y hy
  apply reflects T
  have he : (sheafTupleMap (fun s => (e s).hom) Γ).val.app T
      ((sheafTupleMap (fun s => (e s).inv) Γ).val.app T y) = y :=
    congrArg (fun f => f.val.app T y) (tuple_inv_hom e Γ)
  change (sheafTupleMap (fun s => (e s).hom) Γ).val.app T
    ((sheafTupleMap (fun s => (e s).inv) Γ).val.app T y) ∈ Q.carrier.obj T
  rwa [he]

private theorem inverseOperation {Γ : List sig.SortType} {s : sig.SortType}
    (a : sheafTuple A.carrier Γ ⟶ A.carrier s) (b : sheafTuple B.carrier Γ ⟶ B.carrier s)
    (commutes : a ≫ (e s).hom = sheafTupleMap (fun t => (e t).hom) Γ ≫ b) :
    b ≫ (e s).inv = sheafTupleMap (fun t => (e t).inv) Γ ≫ a := by
  apply (cancel_mono (e s).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, commutes,
    ← Category.assoc, tuple_inv_hom, Category.id_comp]

/-- Construct the structure isomorphism from the carrier isomorphisms and primitive diagrams. -/
def isoOfCarrier {A B : SheafStructure sig J} (e : ∀ s, A.carrier s ≅ B.carrier s)
    (total : ∀ p, A.total p ≫ (e _).hom = sheafTupleMap (fun s => (e s).hom) _ ≫ B.total p)
    (quantity : ∀ q, A.quantity q ≫ (e _).hom = sheafTupleMap (fun s => (e s).hom) _ ≫ B.quantity q)
    (relation : ∀ r, (A.relation r).carrier =
      ((B.relation r).preimage (sheafTupleMap (fun s => (e s).hom) _)).carrier)
    (domain : ∀ p, (A.partialDomain p).carrier =
      ((B.partialDomain p).preimage (sheafTupleMap (fun s => (e s).hom) _)).carrier)
    (value : ∀ p, A.partialValue p ≫ (e _).hom =
      SheafPredicate.mapAlong (sheafTupleMap (fun s => (e s).hom) _) (le_of_eq (domain p)) ≫ B.partialValue p) :
    A ≅ B where
  hom :=
    { onSort := fun s => (e s).hom
      preservesTotal := total
      preservesQuantity := quantity
      preservesRelation := fun r => le_of_eq (relation r)
      preservesDomain := fun p => le_of_eq (domain p)
      preservesPartial := value }
  inv :=
    { onSort := fun s => (e s).inv
      preservesTotal := fun p => inverseOperation e _ _ (total p)
      preservesQuantity := fun q => inverseOperation e _ _ (quantity q)
      preservesRelation := fun r => inversePredicate e _ _ (le_of_eq (relation r).symm)
      preservesDomain := fun p => inversePredicate e _ _ (le_of_eq (domain p).symm)
      preservesPartial := by
        intro p
        let Γ := (sig.partialArity p).inputs
        let P := A.partialDomain p
        let Q := B.partialDomain p
        let f := sheafTupleMap (fun s => (e s).hom) Γ
        let g := sheafTupleMap (fun s => (e s).inv) Γ
        let pf := SheafPredicate.mapAlong f (P := P) (Q := Q) (le_of_eq (domain p))
        let pg := SheafPredicate.mapAlong g (P := Q) (Q := P) (inversePredicate e P Q (le_of_eq (domain p).symm))
        have he : pg ≫ pf = 𝟙 Q.toSheaf := by
          ext U y
          apply Subtype.ext
          exact congrArg (fun m => m.val.app U y.val) (tuple_inv_hom e Γ)
        change B.partialValue p ≫ (e _).inv = pg ≫ A.partialValue p
        apply (cancel_mono (e _).hom).mp
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, value p]
        change B.partialValue p = pg ≫ pf ≫ B.partialValue p
        rw [← Category.assoc, he, Category.id_comp] }
  hom_inv_id := Hom.ext (funext fun s => (e s).hom_inv_id)
  inv_hom_id := Hom.ext (funext fun s => (e s).inv_hom_id)

end SHIGURE.SheafStructure
