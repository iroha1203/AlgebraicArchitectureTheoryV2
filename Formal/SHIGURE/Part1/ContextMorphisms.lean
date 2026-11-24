import Formal.SHIGURE.Part1.ContextStructures

/-! # Structure maps and their declaration restrictions

Each arrow carries just the component functions at retained sorts and the
preservation proofs for each retained relation, partial domain and graph.
-/

universe u

namespace SHIGURE
namespace ContextStructure

open CategoryTheory DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V W : DeclarationContext P}

/-- Structure-preserving maps of the restricted presentation. -/
structure Hom (A B : ContextStructure U) where
  /-- A component at every retained sort. -/
  onSort : CarrierMap U A.carrier B.carrier
  /-- A source relation fact induces a target relation fact. -/
  relation_mem (r : P.signature.Rel) (keep : Declaration.relation r ∈ U.declarations)
    (e : Assignment A.carrier (P.signature.relInputs r)) :
    A.evaluation.relation r keep e →
      B.evaluation.relation r keep (mapAssignment onSort (relationInputs r keep) e)
  /-- A source defined input maps into the target domain. -/
  domain_mem (p : P.signature.Partial) (keep : Declaration.partialOp p ∈ U.declarations)
    (e : Assignment A.carrier (P.signature.partialArity p).inputs) :
    A.evaluation.domain p keep e →
      B.evaluation.domain p keep (mapAssignment onSort (operationInputs (.partialOp p) keep) e)
  /-- Each retained operation commutes on its defined inputs. -/
  graph_mem (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (e : Assignment A.carrier op.arity.inputs) (y : A.carrier op.arity.output) :
    A.evaluation.graph op keep e y → B.evaluation.graph op keep
      (mapAssignment onSort (operationInputs op keep) e) (onSort _ (operationOutput op keep) y)

namespace Hom

variable {A B C : ContextStructure U}

/-- All arrows are determined by their retained components. -/
@[ext] theorem ext {f g : Hom A B} (same : ∀ s keep x, f.onSort s keep x = g.onSort s keep x) : f = g := by
  have onSort : f.onSort = g.onSort := funext fun s => funext fun keep => funext (same s keep)
  cases f
  cases g
  cases onSort
  rfl

/-- The identity is the identity function at each retained sort. -/
def identity (A : ContextStructure U) : Hom A A where
  onSort _ _ := id
  relation_mem r keep e := by simpa only [id_eq, mapAssignment_id] using id
  domain_mem p keep e := by simpa only [id_eq, mapAssignment_id] using id
  graph_mem op keep e y := by simpa only [id_eq, mapAssignment_id] using id

/-- Structure maps compose at every retained sort. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  onSort s keep x := g.onSort s keep (f.onSort s keep x)
  relation_mem r keep e he := by
    rw [← mapAssignment_comp f.onSort g.onSort (le_refl U)]
    exact g.relation_mem r keep _ (f.relation_mem r keep e he)
  domain_mem p keep e he := by
    rw [← mapAssignment_comp f.onSort g.onSort (le_refl U)]
    exact g.domain_mem p keep _ (f.domain_mem p keep e he)
  graph_mem op keep e y he := by
    rw [← mapAssignment_comp f.onSort g.onSort (le_refl U)]
    exact g.graph_mem op keep _ _ (f.graph_mem op keep e y he)

end Hom

/-- The category of structures in a declaration context. -/
instance category : Category.{u} (ContextStructure U) where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp _ := Hom.ext (fun _ _ _ => rfl)
  comp_id _ := Hom.ext (fun _ _ _ => rfl)
  assoc _ _ _ := Hom.ext (fun _ _ _ => rfl)

/-- The categorical identity acts as the identity on each retained carrier. -/
@[simp] theorem id_onSort (A : ContextStructure U) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : A.carrier s) :
    (𝟙 A : Hom A A).onSort s keep x = x :=
  rfl

/-- The categorical composite is the composition at each retained carrier. -/
@[simp] theorem comp_onSort {A B C : ContextStructure U} (f : A ⟶ B) (g : B ⟶ C)
    (s : P.signature.SortType) (keep : Declaration.sort s ∈ U.declarations) (x : A.carrier s) :
    (show Hom A C from f ≫ g).onSort s keep x = (show Hom B C from g).onSort s keep
      ((show Hom A B from f).onSort s keep x) :=
  rfl

/-- Transporting endpoints by equality transports component values along the corresponding carrier equality. -/
theorem eqToHom_onSort {A B : ContextStructure U} (h : A = B) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : A.carrier s) :
    (show Hom A B from eqToHom h).onSort s keep x = cast (congrArg (fun M => M.carrier s) h) x := by
  cases h
  rw [eqToHom_refl, id_onSort]
  rfl

namespace Hom

variable {A B C : ContextStructure U}

/-- Transport the retained component along the two carrier identifications. -/
noncomputable def restrictOnSort (f : Hom A B) (inside : V ≤ U) :
    CarrierMap V (A.restrict inside).carrier (B.restrict inside).carrier :=
  fun s keep x => cast (B.restrict_carrier inside (s := s) keep).symm
    (f.onSort s (inside keep) (selectedMap V A.carrier s keep x))

/-- The restricted component at a retained sort transports the given arrow
using the source and target carrier identifications of Proposition 3.2. -/
theorem restrictOnSort_apply (f : Hom A B) (inside : V ≤ U) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ V.declarations) (x : (A.restrict inside).carrier s) :
    f.restrictOnSort inside s keep x = cast (B.restrict_carrier inside (s := s) keep).symm
      (f.onSort s (inside keep) (selectedMap V A.carrier s keep x)) :=
  rfl

/-- A local component is exactly the original component after identifying the retained carriers. -/
theorem selectedMap_restrictOnSort (f : Hom A B) (inside : V ≤ U) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ V.declarations) (x : (A.restrict inside).carrier s) :
    selectedMap V B.carrier s keep (f.restrictOnSort inside s keep x) =
      f.onSort s (inside keep) (selectedMap V A.carrier s keep x) := by
  simp only [restrictOnSort, selectedMap_apply, cast_cast]
  rfl

/-- The corresponding square of maps on retained tuples commutes. -/
theorem restrict_assignment (f : Hom A B) (inside : V ≤ U) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ V.declarations) (e : Assignment (A.restrict inside).carrier Γ) :
    mapAssignment (selectedMap V B.carrier) keep (mapAssignment (f.restrictOnSort inside) keep e) =
      mapAssignment f.onSort (fun _ hd => inside (keep hd)) (mapAssignment (selectedMap V A.carrier) keep e) := by
  apply Assignment.ext
  intro s var
  simp only [mapAssignment_apply, selectedMap_restrictOnSort]

/-- Forget every component except those retained in the smaller context. -/
noncomputable def restrict (f : Hom A B) (inside : V ≤ U) : Hom (A.restrict inside) (B.restrict inside) where
  onSort := f.restrictOnSort inside
  relation_mem r keep e he := by
    simp only [restrict_evaluation, RestrictedEvaluation.pullback_relation, restrict_assignment] at he ⊢
    exact f.relation_mem r (inside keep) _ he
  domain_mem p keep e he := by
    simp only [restrict_evaluation, RestrictedEvaluation.pullback_domain, restrict_assignment] at he ⊢
    exact f.domain_mem p (inside keep) _ he
  graph_mem op keep e y he := by
    simp only [restrict_evaluation, RestrictedEvaluation.pullback_graph, restrict_assignment,
      selectedMap_restrictOnSort] at he ⊢
    exact f.graph_mem op (inside keep) _ _ he

/-- The calculation rule for restricted structure maps. -/
theorem restrict_onSort (f : Hom A B) (inside : V ≤ U) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ V.declarations) (x : (A.restrict inside).carrier s) :
    (f.restrict inside).onSort s keep x = f.restrictOnSort inside s keep x :=
  rfl

end Hom

/-- The structure reduct is a functor. -/
noncomputable def restrictFunctor (inside : V ≤ U) : ContextStructure U ⥤ ContextStructure V where
  obj A := A.restrict inside
  map f := Hom.restrict f inside
  map_id A := by
    apply Hom.ext
    intro s keep x
    apply (selectedMap_bijective A.carrier s keep).1
    rw [Hom.restrict_onSort, Hom.selectedMap_restrictOnSort, id_onSort, id_onSort]
  map_comp f g := by
    apply Hom.ext
    intro s keep x
    apply (selectedMap_bijective _ s keep).1
    simp only [comp_onSort, Hom.restrict_onSort, Hom.selectedMap_restrictOnSort]

/-- The restriction functor's arrow component is the retained map. -/
theorem restrictFunctor_map (inside : V ≤ U) {A B : ContextStructure U} (f : A ⟶ B) :
    (restrictFunctor inside).map f = Hom.restrict f inside :=
  rfl

/-- The identity inclusion restricts to the identity functor. -/
theorem restrictFunctor_id : restrictFunctor (le_refl U) = 𝟭 (ContextStructure U) := by
  refine Functor.ext (fun A => A.restrict_id) ?_
  intro A B f
  apply Hom.ext
  intro s kept x
  simp only [restrictFunctor_map, Hom.restrict_onSort, Hom.restrictOnSort, selectedMap_apply, comp_onSort,
    Functor.id_map, eqToHom_onSort]

/-- Successive structure reducts compose strictly as functors. -/
theorem restrictFunctor_comp (inside : V ≤ U) (smaller : W ≤ V) :
    restrictFunctor inside ⋙ restrictFunctor smaller = restrictFunctor (smaller.trans inside) := by
  refine Functor.ext (fun A => A.restrict_comp inside smaller) ?_
  intro A B f
  apply Hom.ext
  intro s kept x
  simp only [Functor.comp_map, restrictFunctor_map, Hom.restrict_onSort, Hom.restrictOnSort, selectedMap_apply,
    comp_onSort, eqToHom_onSort, cast_cast]

end ContextStructure
end SHIGURE
