import Formal.SHIGURE.Part2.Recovery.RelativeTotalSheaf
import Formal.SHIGURE.Part2.Recovery.CopyingBaseChange
import Formal.SHIGURE.Part2.Recovery.ConstantFormulas
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# Schemes representing the locally split primitive diagrams

Each native chart gives constant schemes for carriers, finite tuples,
and the subtypes for relations and partial domains. Gluing these
relative representations gives the schemes of the entire structure.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S S' : Scheme.{u}}

namespace RelativeRepresentation

variable {F G : ZariskiSheaf S} (X : RelativeRepresentation F) (Y : RelativeRepresentation G)

/-- A map of represented sheaves is the actual relative scheme morphism. -/
def readMap (f : F ⟶ G) : X.space ⟶ Y.space :=
  (relativePointsHomEquiv X.space Y.space).symm (X.points.hom ≫ f ≫ Y.points.inv)

/-- The scheme map induces the original map under the two representing isomorphisms. -/
theorem readMap_points (f : F ⟶ G) :
    relativePointsMap (X.readMap Y f) = X.points.hom ≫ f ≫ Y.points.inv :=
  (relativePointsHomEquiv X.space Y.space).apply_symm_apply _

/-- A monomorphism of represented sheaves gives a monomorphism of relative schemes. -/
theorem readMap_mono (f : F ⟶ G) [Mono f] : Mono (X.readMap Y f) where
  right_cancellation {Z} a b e := by
    apply (relativePointsHomEquiv Z X.space).injective
    change relativePointsMap a = relativePointsMap b
    apply (cancel_mono (X.points.hom ≫ f ≫ Y.points.inv)).mp
    rw [← X.readMap_points Y f, ← relativePointsMap_comp, ← relativePointsMap_comp, e]

/-- Changing coefficients uses the actual scheme fiber product. -/
def baseChange (f : S' ⟶ S) : RelativeRepresentation
    ((Scheme.zariskiTopology.overMapPullback (Type u) f).obj F) :=
  ⟨(relativeSchemePullback f).obj X.space,
    (relativePointsPullbackIso f X.space).symm ≪≫
      (Scheme.zariskiTopology.overMapPullback (Type u) f).mapIso X.points⟩

/-- Base change of a representing map is its actual map between the fiber products. -/
theorem baseChange_readMap (f : S' ⟶ S) (m : F ⟶ G) :
    (X.baseChange f).readMap (Y.baseChange f) ((Scheme.zariskiTopology.overMapPullback (Type u) f).map m) =
      (relativeSchemePullback f).map (X.readMap Y m) := by
  let P := Scheme.zariskiTopology.overMapPullback (Type u) f
  let eX := relativePointsPullbackIso f X.space
  let eY := relativePointsPullbackIso f Y.space
  apply (relativePointsHomEquiv (X.baseChange f).space (Y.baseChange f).space).injective
  change relativePointsMap _ = relativePointsMap _
  rw [(X.baseChange f).readMap_points]
  have h := relativePointsPullbackIso_naturality f (X.readMap Y m)
  rw [X.readMap_points Y m] at h
  apply (cancel_epi eX.hom).mp
  change eX.hom ≫ (eX.inv ≫ P.map X.points.hom) ≫ P.map m ≫ P.map Y.points.inv ≫ eY.hom =
    eX.hom ≫ relativePointsMap ((relativeSchemePullback f).map (X.readMap Y m))
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp] using h

/-- The constant sheaf is represented by the constant scheme. -/
def constant (S : Scheme.{u}) (X : Type u) : RelativeRepresentation (constantCarrier S X) :=
  ⟨constantSchemeOver S X, constantCarrierIso S X⟩

end RelativeRepresentation

private def tupleIso {K : Type u} {A B : K → ZariskiSheaf S} (e : ∀ s, A s ≅ B s) (Γ : List K) :
    sheafTuple A Γ ≅ sheafTuple B Γ :=
  ⟨sheafTupleMap (fun s => (e s).hom) Γ, sheafTupleMap (fun s => (e s).inv) Γ,
    by rw [← sheafTupleMap_comp]; simp only [Iso.hom_inv_id, sheafTupleMap_id],
    by rw [← sheafTupleMap_comp]; simp only [Iso.inv_hom_id, sheafTupleMap_id]⟩

private def sortIso {sig : Signature.{u}} {A B : SheafStructure sig (Scheme.zariskiTopology.over S)}
    (e : A ≅ B) (s : sig.SortType) : A.carrier s ≅ B.carrier s :=
  ⟨e.hom.onSort s, e.inv.onSort s, congrArg (fun h => h.onSort s) e.hom_inv_id,
    congrArg (fun h => h.onSort s) e.inv_hom_id⟩

private def predicateIso {F G : ZariskiSheaf S} (P : SheafPredicate F) (Q : SheafPredicate G) (e : F ≅ G)
    (h : P.carrier ≤ (Q.preimage e.hom).carrier) (k : Q.carrier ≤ (P.preimage e.inv).carrier) :
    P.toSheaf ≅ Q.toSheaf :=
  ⟨SheafPredicate.mapAlong e.hom h, SheafPredicate.mapAlong e.inv k,
    by
      ext T x
      apply Subtype.ext
      exact congrArg (fun m => m.val.app T x.val) e.hom_inv_id,
    by
      ext T x
      apply Subtype.ext
      exact congrArg (fun m => m.val.app T x.val) e.inv_hom_id⟩

private def preimageIso {F G : ZariskiSheaf S} (P : SheafPredicate G) (e : F ≅ G) :
    (P.preimage e.hom).toSheaf ≅ P.toSheaf :=
  predicateIso _ _ e le_rfl (by
    intro T x hx
    have h : e.hom.val.app T (e.inv.val.app T x) = x := congrArg (fun m => m.val.app T x) e.inv_hom_id
    change e.hom.val.app T (e.inv.val.app T x) ∈ P.carrier.obj T
    rwa [h])

private def constantTupleRepresentation (S : Scheme.{u}) {K : Type u} (M : K → Type u) (Γ : List K) :
    RelativeRepresentation (sheafTuple (fun s => constantCarrier S (M s)) Γ) :=
  ⟨constantSchemeOver S (Assignment M Γ), constantCarrierIso S _ ≪≫ (constantTupleIso S M Γ).symm⟩

private def constantPredicateRepresentation (S : Scheme.{u}) {K : Type u} (M : K → Type u) (Γ : List K)
    (P : Set (Assignment M Γ)) :
    RelativeRepresentation (((constantPredicate S P).preimage (constantTupleMap S M Γ)).toSheaf) :=
  ⟨constantSchemeOver S P, constantCarrierIso S P ≪≫ (constantPredicateIso S P).symm ≪≫
    (preimageIso (constantPredicate S P) (constantTupleIso S M Γ)).symm⟩

/-- Relative schemes for all carriers, inputs and chosen subobjects of a copying structure. -/
structure CopyingRepresentation {sig : Signature.{u}} (A : SheafStructure sig (Scheme.zariskiTopology.over S)) where
  /-- Representing scheme of each carrier. -/
  carrier (s : sig.SortType) : RelativeRepresentation (A.carrier s)
  /-- Representing scheme of every finite typed input tuple. -/
  input (Γ : List sig.SortType) : RelativeRepresentation (sheafTuple A.carrier Γ)
  /-- Representing scheme of a relation subsheaf. -/
  relation (r : sig.Rel) : RelativeRepresentation (A.relation r).toSheaf
  /-- Representing scheme of the chosen partial domain. -/
  domain (p : sig.Partial) : RelativeRepresentation (A.partialDomain p).toSheaf

private def representationAlongIso {F G : ZariskiSheaf S} (e : F ≅ G) (X : RelativeRepresentation G) :
    RelativeRepresentation F :=
  ⟨X.space, X.points ≪≫ e.symm⟩

/-- Zariski local splitting represents the entire primitive diagram by relative schemes. -/
def CopyingRepresentation.ofSplit {T : Theory.{u}} {A : SheafStructure T.signature (Scheme.zariskiTopology.over S)}
    (hA : IsZariskiSplit T A) : CopyingRepresentation A := by
  let C := hA.choose
  let M (i : C.I₀) := (hA.choose_spec i).choose
  let e (i : C.I₀) := (hA.choose_spec i).choose_spec.some
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact RelativeRepresentation.ofOpenCover (A.carrier s) C (fun i =>
      representationAlongIso (sortIso (e i) s) (RelativeRepresentation.constant (C.X i) ((M i).obj.carrier s)))
  · intro Γ
    exact RelativeRepresentation.ofOpenCover (sheafTuple A.carrier Γ) C (fun i =>
      representationAlongIso (tupleIso (sortIso (e i)) Γ) (constantTupleRepresentation (C.X i) (M i).obj.carrier Γ))
  · intro r
    exact RelativeRepresentation.ofOpenCover (A.relation r).toSheaf C (fun i =>
      representationAlongIso
        (predicateIso ((restrictStructure (C.f i) A).relation r)
          ((constantStructure (C.X i) (M i).obj).relation r) (tupleIso (sortIso (e i)) _)
          ((e i).hom.preservesRelation r) ((e i).inv.preservesRelation r))
        (constantPredicateRepresentation (C.X i) (M i).obj.carrier _ ((M i).obj.relation r)))
  · intro p
    exact RelativeRepresentation.ofOpenCover (A.partialDomain p).toSheaf C (fun i =>
      representationAlongIso
        (predicateIso ((restrictStructure (C.f i) A).partialDomain p)
          ((constantStructure (C.X i) (M i).obj).partialDomain p) (tupleIso (sortIso (e i)) _)
          ((e i).hom.preservesDomain p) ((e i).inv.preservesDomain p))
        (constantPredicateRepresentation (C.X i) (M i).obj.carrier _ ((M i).obj.partialDomain p)))

namespace CopyingRepresentation

variable {sig : Signature.{u}} {A B : SheafStructure sig (Scheme.zariskiTopology.over S)}
variable (X : CopyingRepresentation A)

/-- Represent the total operation as a relative scheme morphism. -/
def total (p : sig.Total) : (X.input (sig.totalArity p).inputs).space ⟶ (X.carrier (sig.totalArity p).output).space :=
  (X.input _).readMap (X.carrier _) (A.total p)

/-- Represent the inclusion of a basic relation as a relative scheme morphism. -/
def relationInclusion (r : sig.Rel) : (X.relation r).space ⟶ (X.input (sig.relInputs r)).space :=
  (X.relation r).readMap (X.input _) (A.relation r).inclusion

/-- Represent the inclusion of a partial domain as a relative scheme morphism. -/
def domainInclusion (p : sig.Partial) : (X.domain p).space ⟶ (X.input (sig.partialArity p).inputs).space :=
  (X.domain p).readMap (X.input _) (A.partialDomain p).inclusion

/-- Represent the partial operation on its actual domain scheme. -/
def partialValue (p : sig.Partial) : (X.domain p).space ⟶ (X.carrier (sig.partialArity p).output).space :=
  (X.domain p).readMap (X.carrier _) (A.partialValue p)

/-- Represent the marked quantity as a relative scheme morphism. -/
def quantity (q : sig.Quantity) : (X.input (sig.quantityArity q).inputs).space ⟶ (X.carrier (sig.quantityArity q).output).space :=
  (X.input _).readMap (X.carrier _) (A.quantity q)

/-- The relation scheme is a subobject of the scheme of its input tuples. -/
theorem relationInclusion_mono (r : sig.Rel) : Mono (X.relationInclusion r) := by
  letI := Sheaf.mono_of_injective (A.relation r).inclusion (fun _ => Subtype.val_injective)
  exact (X.relation r).readMap_mono (X.input _) (A.relation r).inclusion

/-- The partial domain is a subobject of its scheme of input tuples. -/
theorem domainInclusion_mono (p : sig.Partial) : Mono (X.domainInclusion p) := by
  letI := Sheaf.mono_of_injective (A.partialDomain p).inclusion (fun _ => Subtype.val_injective)
  exact (X.domain p).readMap_mono (X.input _) (A.partialDomain p).inclusion

/-- Represent a structure-preserving arrow on each carrier. -/
def mapOnSort (Y : CopyingRepresentation B) (h : A ⟶ B) (s : sig.SortType) :
    (X.carrier s).space ⟶ (Y.carrier s).space :=
  (X.carrier s).readMap (Y.carrier s) (h.onSort s)

/-- Each primitive in the coefficient restriction has the corresponding actual fiber product. -/
def baseChange (f : S' ⟶ S) : CopyingRepresentation (restrictStructure f A) where
  carrier s := (X.carrier s).baseChange f
  input Γ := (X.input Γ).baseChange f
  relation r := (X.relation r).baseChange f
  domain p := (X.domain p).baseChange f

/-- Total operations are pulled back as maps of schemes. -/
theorem baseChange_total (f : S' ⟶ S) (p : sig.Total) :
    (X.baseChange f).total p = (relativeSchemePullback f).map (X.total p) :=
  (X.input _).baseChange_readMap (X.carrier _) f (A.total p)

/-- Relation inclusions are pulled back as maps of schemes. -/
theorem baseChange_relation (f : S' ⟶ S) (r : sig.Rel) :
    (X.baseChange f).relationInclusion r = (relativeSchemePullback f).map (X.relationInclusion r) :=
  (X.relation r).baseChange_readMap (X.input _) f (A.relation r).inclusion

/-- Domain inclusions are pulled back as maps of schemes. -/
theorem baseChange_domain (f : S' ⟶ S) (p : sig.Partial) :
    (X.baseChange f).domainInclusion p = (relativeSchemePullback f).map (X.domainInclusion p) :=
  (X.domain p).baseChange_readMap (X.input _) f (A.partialDomain p).inclusion

/-- Partial values are pulled back on the actual domain schemes. -/
theorem baseChange_partialValue (f : S' ⟶ S) (p : sig.Partial) :
    (X.baseChange f).partialValue p = (relativeSchemePullback f).map (X.partialValue p) :=
  (X.domain p).baseChange_readMap (X.carrier _) f (A.partialValue p)

/-- Quantities are pulled back as maps of schemes. -/
theorem baseChange_quantity (f : S' ⟶ S) (q : sig.Quantity) :
    (X.baseChange f).quantity q = (relativeSchemePullback f).map (X.quantity q) :=
  (X.input _).baseChange_readMap (X.carrier _) f (A.quantity q)

/-- A structure-preserving arrow acts on the fiber products of the representing schemes. -/
theorem baseChange_mapOnSort (Y : CopyingRepresentation B) (f : S' ⟶ S) (g : A ⟶ B) (s : sig.SortType) :
    (X.baseChange f).mapOnSort (Y.baseChange f) (restrictStructureMap f g) s =
      (relativeSchemePullback f).map (X.mapOnSort Y g s) :=
  (X.carrier s).baseChange_readMap (Y.carrier s) f (g.onSort s)

end CopyingRepresentation
end SHIGURE.Copying
