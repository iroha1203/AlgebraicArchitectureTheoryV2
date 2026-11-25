import Formal.SHIGURE.Part2.Recovery.StructureMaps
import Formal.SHIGURE.Part2.Recovery.SheafLawMaps
import Formal.SHIGURE.Part2.Recovery.CoefficientLaws
import Formal.SHIGURE.Part2.Realizations.ZariskiModels
import Formal.SHIGURE.Part1.SelectedPresentation

/-!
# Restriction of the declarations of a copying structure

A reduct retypes the tuples of sections using the Part I position map.
Relations and partial domains are the preimages of the original
predicates, and the partial value uses the induced map on those domains.

## Implementation notes

The Part I names determine the reduct on each test object's sections.
This preserves the written arguments and avoids choosing new maps for
repeated sorts or dropping the original domains. The same position
map handles both sections and their restrictions along test arrows.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {B B' : Scheme.{u}} {S T : Signature.{u}}

/-- Retype every section of a finite tuple to its corresponding named position. -/
def renameTuple {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    (Γ : List K) : sheafTuple (A ∘ g) Γ ⟶ sheafTuple A (Γ.map g) :=
  ⟨{ app := fun U => ↾fun a => Assignment.mapSorts (X := fun i => (A i).val.obj U) g a
     naturality := by
       intro U V f
       ext a
       apply Assignment.ext_mapSorts g
       intro s i
       let aU : Assignment (fun k => (A (g k)).val.obj U) Γ := a
       let aV : Assignment (fun k => (A (g k)).val.obj V) Γ := (sheafTuple (A ∘ g) Γ).val.map f a
       change (aV.mapSorts (X := fun l => (A l).val.obj V) g).get (i.mapSorts g) =
         (A (g s)).val.map f ((aU.mapSorts (X := fun l => (A l).val.obj U) g).get (i.mapSorts g))
       rw [Assignment.mapSorts_apply, Assignment.mapSorts_apply]
       rfl }⟩

/-- Retyping arguments along the specified equality of contexts keeps their actual sections. -/
private def renameTupleAt {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    {Γ : List K} {Δ : List L} (h : Γ.map g = Δ) :
    sheafTuple (A ∘ g) Γ ⟶ sheafTuple A Δ :=
  ⟨{ app := fun U => ↾fun a =>
       h ▸ (Assignment.mapSorts (X := fun i => (A i).val.obj U) g a)
     naturality := by
       subst Δ
       exact (renameTuple g A Γ).val.naturality }⟩

/-- A total operation on the reduct is the original operation on the retyped arguments. -/
private def renameTotal {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    {a : Arity K} {b : Arity L} (h : ⟨a.inputs.map g, g a.output⟩ = b)
    (op : sheafTuple A b.inputs ⟶ A b.output) :
    sheafTuple (A ∘ g) a.inputs ⟶ A (g a.output) :=
  ⟨{ app := fun U => ↾fun x =>
       cast (congrArg (fun arity : Arity L => (A arity.output).val.obj U) h.symm)
         (op.val.app U ((renameTupleAt g A (congrArg Arity.inputs h)).val.app U x))
     naturality := by
       subst b
       exact (renameTuple g A a.inputs ≫ op).val.naturality }⟩

/-- The partial operation on the reduct uses the original operation on the retyped domain. -/
private def renamePartial {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    {a : Arity K} {b : Arity L} (h : ⟨a.inputs.map g, g a.output⟩ = b)
    (P : SheafPredicate (sheafTuple A b.inputs)) (op : P.toSheaf ⟶ A b.output) :
    (P.preimage (renameTupleAt g A (congrArg Arity.inputs h))).toSheaf ⟶ A (g a.output) :=
  let r := renameTupleAt g A (congrArg Arity.inputs h)
  ⟨{ app := fun U => ↾fun x =>
       cast (congrArg (fun arity : Arity L => (A arity.output).val.obj U) h.symm)
         (op.val.app U ⟨r.val.app U x.val, x.property⟩)
     naturality := by
       subst b
       exact (SheafPredicate.mapAlong (renameTuple g A _) (P := P.preimage (renameTuple g A _))
         (Q := P) le_rfl ≫ op).val.naturality }⟩

/-- Restrict a sheaf structure to the selected Part I names and arities. -/
def restrictDeclarations (names : SignatureNames S T)
    (A : SheafStructure T (Scheme.zariskiTopology.over B)) :
    SheafStructure S (Scheme.zariskiTopology.over B) where
  carrier := A.carrier ∘ names.onSort
  total p := renameTotal names.onSort A.carrier (names.totalArity p) (A.total (names.onTotal p))
  relation r := (A.relation (names.onRel r)).preimage (renameTupleAt names.onSort A.carrier (names.relInputs r))
  partialDomain p := (A.partialDomain (names.onPartial p)).preimage
    (renameTupleAt names.onSort A.carrier (congrArg Arity.inputs (names.partialArity p)))
  partialValue p := renamePartial names.onSort A.carrier (names.partialArity p)
    (A.partialDomain (names.onPartial p)) (A.partialValue (names.onPartial p))
  quantity q := renameTotal names.onSort A.carrier (names.quantityArity q) (A.quantity (names.onQuantity q))

/-- Forming the sections of the sheaf reduct is exactly the Part I reduct on those sections. -/
theorem restrictDeclarations_sections (names : SignatureNames S T)
    (A : SheafStructure T (Scheme.zariskiTopology.over B)) (U : (Over B)ᵒᵖ) :
    (restrictDeclarations names A).sections U = names.restrict (A.sections U) := by
  rfl

/-- The Part I assignment retyping with a specified destination context. -/
private def retypeAssignment {K L : Type u} (g : K → L) {X : L → Type u}
    {Γ : List K} {Δ : List L} (he : Γ.map g = Δ) (a : Assignment (X ∘ g) Γ) : Assignment X Δ :=
  he ▸ a.mapSorts g

/-- Restricting the sort names commutes with applying a family of carrier maps to an assignment. -/
private theorem retypeAssignment_map {K L : Type u} (g : K → L) {X Y : L → Type u}
    {Γ : List K} {Δ : List L} (he : Γ.map g = Δ) (h : ∀ s, X s → Y s)
    (a : Assignment (X ∘ g) Γ) :
    retypeAssignment g he (a.map (fun s => h (g s))) = (retypeAssignment g he a).map h := by
  subst Δ
  apply Assignment.ext_mapSorts g
  intro s i
  change ((a.map (fun s => h (g s))).mapSorts g).get (i.mapSorts g) =
    h (g s) ((a.mapSorts g).get (i.mapSorts g))
  simp only [Assignment.mapSorts_apply, Assignment.map_apply]

/-- A carrier map commutes with transport of the output sort. -/
private theorem mapCast {K : Type u} {X Y : K → Type u} (h : ∀ s, X s → Y s)
    {s t : K} (e : t = s) (x : X s) :
    h t (cast (congrArg X e.symm) x) = cast (congrArg Y e.symm) (h s x) := by
  cases e
  rfl

/-- The native reduct of a structure map keeps the actual functions at its selected sorts. -/
def restrictNativeMap (names : SignatureNames S T) {A B : Structure T} (h : StructureMap A B) :
    StructureMap (names.restrict A) (names.restrict B) where
  onSort s := h.onSort (names.onSort s)
  total_comm p a := by
    let e := congrArg Arity.inputs (names.totalArity p)
    let o := congrArg Arity.output (names.totalArity p)
    change h.onSort _ (cast (congrArg A.carrier o.symm)
      (A.total (names.onTotal p) (retypeAssignment names.onSort e a))) =
      cast (congrArg B.carrier o.symm) (B.total (names.onTotal p)
        (retypeAssignment names.onSort e (a.map (fun s => h.onSort (names.onSort s)))))
    rw [mapCast h.onSort o, h.total_comm, retypeAssignment_map]
  relation_mem r a ha := by
    change retypeAssignment names.onSort _ a ∈ A.relation (names.onRel r) at ha
    change retypeAssignment names.onSort (names.relInputs r) (a.map _) ∈ B.relation (names.onRel r)
    rw [retypeAssignment_map]
    exact h.relation_mem (names.onRel r) _ ha
  partial_mem p a ha := by
    change retypeAssignment names.onSort _ a ∈ A.partialDomain (names.onPartial p) at ha
    change retypeAssignment names.onSort (congrArg Arity.inputs (names.partialArity p)) (a.map _) ∈
      B.partialDomain (names.onPartial p)
    rw [retypeAssignment_map]
    exact h.partial_mem (names.onPartial p) _ ha
  partial_comm p a := by
    let e := congrArg Arity.inputs (names.partialArity p)
    let o := congrArg Arity.output (names.partialArity p)
    let x : A.partialDomain (names.onPartial p) := ⟨retypeAssignment names.onSort e a.val, a.property⟩
    change h.onSort _ (cast (congrArg A.carrier o.symm) (A.partialValue (names.onPartial p) x)) =
      cast (congrArg B.carrier o.symm) (B.partialValue (names.onPartial p)
        ⟨retypeAssignment names.onSort e (a.val.map (fun s => h.onSort (names.onSort s))), _⟩)
    rw [mapCast h.onSort o, h.partial_comm]
    apply congrArg (cast (congrArg B.carrier o.symm))
    apply congrArg (B.partialValue (names.onPartial p))
    apply Subtype.ext
    exact (retypeAssignment_map names.onSort e h.onSort a.val).symm
  quantity_comm q a := by
    let e := congrArg Arity.inputs (names.quantityArity q)
    let o := congrArg Arity.output (names.quantityArity q)
    change h.onSort _ (cast (congrArg A.carrier o.symm)
      (A.quantity (names.onQuantity q) (retypeAssignment names.onSort e a))) =
      cast (congrArg B.carrier o.symm) (B.quantity (names.onQuantity q)
        (retypeAssignment names.onSort e (a.map (fun s => h.onSort (names.onSort s)))))
    rw [mapCast h.onSort o, h.quantity_comm, retypeAssignment_map]

/-- Declaring a reduct also restricts every preserving arrow to the selected components. -/
def restrictDeclarationsMap (names : SignatureNames S T)
    {A D : SheafStructure T (Scheme.zariskiTopology.over B)} (h : SheafStructure.Hom A D) :
    SheafStructure.Hom (restrictDeclarations names A) (restrictDeclarations names D) where
  onSort s := h.onSort (names.onSort s)
  preservesTotal p := by
    ext U a
    exact (restrictNativeMap names (h.sections U)).total_comm p a
  preservesRelation r U a ha := (restrictNativeMap names (h.sections U)).relation_mem r a ha
  preservesDomain p U a ha := (restrictNativeMap names (h.sections U)).partial_mem p a ha
  preservesPartial p := by
    ext U a
    exact (restrictNativeMap names (h.sections U)).partial_comm p a
  preservesQuantity q := by
    ext U a
    exact (restrictNativeMap names (h.sections U)).quantity_comm q a

/-- Declaring a reduct is functorial on all primitive structures and arrows. -/
def restrictDeclarationsFunctor (B : Scheme.{u}) (names : SignatureNames S T) :
    SheafStructure T (Scheme.zariskiTopology.over B) ⥤
      SheafStructure S (Scheme.zariskiTopology.over B) where
  obj := restrictDeclarations names
  map := restrictDeclarationsMap names
  map_id _ := SheafStructure.Hom.ext rfl
  map_comp _ _ := SheafStructure.Hom.ext rfl

/-- Changing coefficients on a native map keeps each original carrier function. -/
theorem restrictConstantStructureMap_onSort (f : B' ⟶ B) {A C : Structure T}
    (h : StructureMap A C) (s : T.SortType) :
    (restrictStructureMap f (constantStructureMap B h)).onSort s =
      (constantStructureMap B' h).onSort s := by
  ext U a
  rfl

/-- Changing coefficients on a native arrow gives its constant realization over the new base. -/
theorem restrictConstantStructureMap_eq (f : B' ⟶ B) {A C : Structure T}
    (h : StructureMap A C) :
    restrictStructureMap f (constantStructureMap B h) = constantStructureMap B' h :=
  SheafStructure.Hom.ext (funext (restrictConstantStructureMap_onSort f h))

/-- Pulling coefficients back commutes with the named reduct of a copying structure. -/
theorem restrictStructure_restrictDeclarations (f : B' ⟶ B) (names : SignatureNames S T)
    (A : SheafStructure T (Scheme.zariskiTopology.over B)) :
    restrictStructure f (restrictDeclarations names A) =
      restrictDeclarations names (restrictStructure f A) := by
  rfl

/-- The arrow components of coefficient change and the named reduct agree in both orders. -/
theorem restrictStructureMap_restrictDeclarationsMap (f : B' ⟶ B) (names : SignatureNames S T)
    {A D : SheafStructure T (Scheme.zariskiTopology.over B)} (h : SheafStructure.Hom A D) :
    restrictStructureMap f (restrictDeclarationsMap names h) =
      restrictDeclarationsMap names (restrictStructureMap f h) :=
  SheafStructure.Hom.ext rfl

/-- The coefficient and declaration restriction functors commute on structures and all arrows. -/
def restrictDeclarations_changeIso (f : B' ⟶ B) (names : SignatureNames S T) :
    restrictDeclarationsFunctor B names ⋙ restrictStructureFunctor S f ≅
      restrictStructureFunctor T f ⋙ restrictDeclarationsFunctor B' names :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A D h
    simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (restrictStructureMap_restrictDeclarationsMap f names h).symm)

/-- Every assignment in the renamed context has an original tuple with exactly those entries. -/
private theorem renameTuple_surjective {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    (Γ : List K) (U : (Over B)ᵒᵖ) :
    Function.Surjective ((renameTuple g A Γ).val.app U) := by
  intro a
  let e : Assignment (fun i => (A i).val.obj U) (Γ.map g) := a
  let pre : Assignment (fun i => (A (g i)).val.obj U) Γ := ⟨fun i => e.get (i.mapSorts g)⟩
  refine ⟨pre, ?_⟩
  change pre.mapSorts g = e
  apply Assignment.ext_mapSorts g
  intro s i
  exact Assignment.mapSorts_apply (X := fun l => (A l).val.obj U) g pre i

/-- Retyping assignments preserves all coordinates and is injective. -/
private theorem renameTuple_injective {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    (Γ : List K) (U : (Over B)ᵒᵖ) : Function.Injective ((renameTuple g A Γ).val.app U) := by
  intro a b h
  let x : Assignment (fun i => (A (g i)).val.obj U) Γ := a
  let y : Assignment (fun i => (A (g i)).val.obj U) Γ := b
  change x = y
  have h' : x.mapSorts (X := fun i => (A i).val.obj U) g = y.mapSorts g := h
  apply Assignment.ext
  intro s i
  have he := congrArg (fun e : Assignment (fun i => (A i).val.obj U) (Γ.map g) =>
    e.get (i.mapSorts g)) h'
  simpa only [Assignment.mapSorts_apply] using he

/-- Retyping an existential witness commutes with forgetting its head. -/
private theorem renameTuple_tail {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    (Γ : List K) (U : (Over B)ᵒᵖ) (s : K)
    (x : (sheafTuple (A ∘ g) (s :: Γ)).val.obj U) :
    (renameTuple g A Γ).val.app U
      ((sheafTupleRename (A ∘ g) (fun i => Var.there (t := s) i)).val.app U x) =
    (sheafTupleRename A (fun i => Var.there (t := g s) i)).val.app U
      ((renameTuple g A (s :: Γ)).val.app U x) := by
  let a : Assignment (fun i => (A (g i)).val.obj U) (s :: Γ) := x
  let b : Assignment (fun l => (A l).val.obj U) ((s :: Γ).map g) := a.mapSorts g
  change a.tail.mapSorts (X := fun l => (A l).val.obj U) g = b.tail
  apply Assignment.ext_mapSorts g
  intro r i
  rw [Assignment.mapSorts_apply]
  exact (Assignment.mapSorts_apply (X := fun l => (A l).val.obj U) g a (.there i)).symm

/-- A relative covering is unchanged when the two sieves have the same local arrows. -/
private theorem same_sieve_cover {U : Over B} {P Q : Sieve U}
    (h : ∀ {V} (g : V ⟶ U), P g ↔ Q g) :
    P ∈ (Scheme.zariskiTopology.over B) U ↔ Q ∈ (Scheme.zariskiTopology.over B) U := by
  have e : P = Q := by
    ext V g
    exact h g
  rw [e]

/-- A positive formula in the named reduct agrees with its written ambient renaming on every test. -/
theorem restrictDeclarations_formula_iff (names : SignatureNames S T)
    (A : SheafStructure T (Scheme.zariskiTopology.over B)) {Γ : List S.SortType}
    (p : Formula S Γ) (U : (Over B)ᵒᵖ)
    (a : (sheafTuple (restrictDeclarations names A).carrier Γ).val.obj U) :
    a ∈ ((restrictDeclarations names A).interpretFormula p).carrier.obj U ↔
      (renameTuple names.onSort A.carrier Γ).val.app U a ∈ (A.interpretFormula (names.formula p)).carrier.obj U := by
  induction p generalizing U with
  | atom p =>
    have h := names.restrict_formula_iff (A.sections U) (Formula.atom p) a
    rw [names.formula_atom] at h ⊢
    exact (((restrictDeclarations names A).mem_interpretAtom_iff_sections p U a).trans h).trans
      (A.mem_interpretAtom_iff_sections _ U _).symm
  | truth =>
    rw [names.formula_truth]
    exact ⟨fun _ => SheafPredicate.mem_truth _ _, fun _ => SheafPredicate.mem_truth _ _⟩
  | falsehood =>
    rw [names.formula_falsehood]
    simp only [SheafStructure.interpretFormula, SheafPredicate.falsehood, SheafPredicate.mem_ofLocal_iff]
    exact same_sieve_cover fun _ => Iff.rfl
  | conj p q hp hq =>
    simp only [names.formula_conj, SheafStructure.interpretFormula, SheafPredicate.mem_conj_iff]
    exact and_congr (hp U a) (hq U a)
  | @disj Γ p q hp hq =>
    simp only [names.formula_disj, SheafStructure.interpretFormula, SheafPredicate.mem_disj_iff]
    apply same_sieve_cover
    intro V g
    let small := sheafTuple (restrictDeclarations names A).carrier Γ
    let big := sheafTuple A.carrier (Γ.map names.onSort)
    let m := renameTuple names.onSort A.carrier Γ
    let b := small.val.map g.op a
    have hm := FunctorToTypes.naturality _ _ m.val g.op a
    change (b ∈ ((restrictDeclarations names A).interpretFormula p).carrier.obj (op V) ∨
      b ∈ ((restrictDeclarations names A).interpretFormula q).carrier.obj (op V)) ↔
      (big.val.map g.op (m.val.app U a) ∈ (A.interpretFormula (names.formula p)).carrier.obj (op V) ∨
       big.val.map g.op (m.val.app U a) ∈ (A.interpretFormula (names.formula q)).carrier.obj (op V))
    rw [← hm]
    exact or_congr (hp (op V) b) (hq (op V) b)
  | @ex Γ s p ih =>
    simp only [names.formula_ex, SheafStructure.interpretFormula, SheafPredicate.mem_existsAlong_iff]
    apply same_sieve_cover
    intro V g
    let small := sheafTuple (restrictDeclarations names A).carrier Γ
    let big := sheafTuple A.carrier (Γ.map names.onSort)
    let m := renameTuple names.onSort A.carrier Γ
    let m' := renameTuple names.onSort A.carrier (s :: Γ)
    let b := small.val.map g.op a
    let smallProj := sheafTupleRename (restrictDeclarations names A).carrier (Γ := Γ) (fun i => Var.there (t := s) i)
    let bigProj := sheafTupleRename A.carrier (Γ := Γ.map names.onSort) (fun i => Var.there (t := names.onSort s) i)
    have hm := FunctorToTypes.naturality _ _ m.val g.op a
    constructor
    · rintro ⟨⟨x, hx⟩, he⟩
      refine ⟨⟨m'.val.app (op V) x, (ih (op V) x).mp hx⟩, ?_⟩
      change bigProj.val.app (op V) (m'.val.app (op V) x) = big.val.map g.op (m.val.app U a)
      rw [← renameTuple_tail, ← hm]
      exact congrArg (m.val.app (op V)) he
    · rintro ⟨⟨y, hy⟩, he⟩
      obtain ⟨x, rfl⟩ := renameTuple_surjective names.onSort A.carrier (s :: Γ) (op V) y
      refine ⟨⟨x, (ih (op V) x).mpr hy⟩, ?_⟩
      change smallProj.val.app (op V) x = b
      apply renameTuple_injective names.onSort A.carrier Γ (op V)
      change bigProj.val.app (op V) (m'.val.app (op V) x) =
        big.val.map g.op (m.val.app U a) at he
      rw [← renameTuple_tail, ← hm] at he
      exact he

/-- The named reduct has exactly the Laws of the ambient structure restricted to the retained names. -/
theorem restrictDeclarations_holdsLaw_iff (names : SignatureNames S T)
    (A : SheafStructure T (Scheme.zariskiTopology.over B)) (law : Law S) :
    (restrictDeclarations names A).holdsLaw law ↔ A.holdsLaw (names.law law) := by
  constructor
  · intro h U a ha
    obtain ⟨b, rfl⟩ := renameTuple_surjective names.onSort A.carrier law.context U a
    exact (restrictDeclarations_formula_iff names A law.conclusion U b).mp
      (h U ((restrictDeclarations_formula_iff names A law.input U b).mpr ha))
  · intro h U a ha
    exact (restrictDeclarations_formula_iff names A law.conclusion U a).mpr
      (h U ((restrictDeclarations_formula_iff names A law.input U a).mp ha))

/-- A retyped predicate on constant sections is evaluated by retyping the native values. -/
private theorem mem_retypedConstantPredicate {K L : Type u} (g : K → L) (M : L → Type u)
    {Γ : List K} {Δ : List L} (e : Γ.map g = Δ) (P : Set (Assignment M Δ))
    (U : (Over B)ᵒᵖ) (a : (sheafTuple (fun s => constantCarrier B (M (g s))) Γ).val.obj U) :
    a ∈ (((constantPredicate B P).preimage (constantTupleMap B M Δ)).preimage
      (renameTupleAt g (fun t => constantCarrier B (M t)) e)).carrier.obj U ↔
    ∀ x : U.unop.left, retypeAssignment g e
      (⟨fun {s} i => (show LocallyConstant U.unop.left (M (g s)) from a.get i) x⟩) ∈ P := by
  let z := (renameTupleAt g (fun t => constantCarrier B (M t)) e).val.app U a
  refine (mem_constantPredicate B P U ((constantTupleMap B M Δ).val.app U z)).trans ?_
  apply forall_congr'
  intro x
  let h (t : L) (y : LocallyConstant U.unop.left (M t)) : M t := y x
  let a' : Assignment (fun s => LocallyConstant U.unop.left (M (g s))) Γ := a
  change (retypeAssignment (X := fun t => LocallyConstant U.unop.left (M t)) g e a').map h ∈ P ↔
    retypeAssignment g e (a'.map (fun s => h (g s))) ∈ P
  rw [retypeAssignment_map g e h a']

/-- Restricting a constant structure is the constant realization of the Part I reduct. -/
def restrictDeclarationsConstantIso (names : SignatureNames S T) (A : Structure T) (B : Scheme.{u}) :
    restrictDeclarations names (constantStructure B A) ≅ constantStructure B (names.restrict A) := by
  let L := restrictDeclarations names (constantStructure B A)
  let D := constantStructure B (names.restrict A)
  have total (p : S.Total) : L.total p = D.total p := by
    ext U a
    apply LocallyConstant.ext
    intro x
    have hl := (restrictNativeMap names (evaluateConstantSections A U.unop x)).total_comm p a
    have hd := (evaluateConstantSections (names.restrict A) U.unop x).total_comm p a
    exact hl.trans hd.symm
  have quantity (q : S.Quantity) : L.quantity q = D.quantity q := by
    ext U a
    apply LocallyConstant.ext
    intro x
    have hl := (restrictNativeMap names (evaluateConstantSections A U.unop x)).quantity_comm q a
    have hd := (evaluateConstantSections (names.restrict A) U.unop x).quantity_comm q a
    exact hl.trans hd.symm
  have relation (r : S.Rel) (U : (Over B)ᵒᵖ)
      (a : (sheafTuple L.carrier (S.relInputs r)).val.obj U) :
      a ∈ (L.relation r).carrier.obj U ↔ a ∈ (D.relation r).carrier.obj U := by
    exact (mem_retypedConstantPredicate names.onSort A.carrier (names.relInputs r)
      (A.relation (names.onRel r)) U a).trans
      (mem_constantPredicate B ((names.restrict A).relation r) U
        ((constantTupleMap B (names.restrict A).carrier _).val.app U a)).symm
  have domain (p : S.Partial) (U : (Over B)ᵒᵖ)
      (a : (sheafTuple L.carrier (S.partialArity p).inputs).val.obj U) :
      a ∈ (L.partialDomain p).carrier.obj U ↔ a ∈ (D.partialDomain p).carrier.obj U := by
    exact (mem_retypedConstantPredicate names.onSort A.carrier (congrArg Arity.inputs (names.partialArity p))
      (A.partialDomain (names.onPartial p)) U a).trans
      (mem_constantPredicate B ((names.restrict A).partialDomain p) U
        ((constantTupleMap B (names.restrict A).carrier _).val.app U a)).symm
  have partialValue (p : S.Partial) (U : (Over B)ᵒᵖ)
      (a : (sheafTuple L.carrier (S.partialArity p).inputs).val.obj U)
      (hl : a ∈ (L.partialDomain p).carrier.obj U) (hd : a ∈ (D.partialDomain p).carrier.obj U) :
      (L.partialValue p).val.app U ⟨a, hl⟩ = (D.partialValue p).val.app U ⟨a, hd⟩ := by
    apply LocallyConstant.ext
    intro x
    have h₁ := (restrictNativeMap names (evaluateConstantSections A U.unop x)).partial_comm p ⟨a, hl⟩
    have h₂ := (evaluateConstantSections (names.restrict A) U.unop x).partial_comm p ⟨a, hd⟩
    exact h₁.trans h₂.symm
  let forward : SheafStructure.Hom L D :=
    { onSort := fun _ => 𝟙 _
      preservesTotal := fun p => by simpa only [Category.comp_id, sheafTupleMap_id, Category.id_comp] using total p
      preservesRelation := fun r U a ha => by
        simpa only [sheafTupleMap_id] using (relation r U a).mp ha
      preservesDomain := fun p U a ha => by
        simpa only [sheafTupleMap_id] using (domain p U a).mp ha
      preservesPartial := fun p => by
        ext U a
        exact partialValue p U a.val a.property ((domain p U a.val).mp a.property)
      preservesQuantity := fun q => by simpa only [Category.comp_id, sheafTupleMap_id, Category.id_comp] using quantity q }
  let backward : SheafStructure.Hom D L :=
    { onSort := fun _ => 𝟙 _
      preservesTotal := fun p => by simpa only [Category.comp_id, sheafTupleMap_id, Category.id_comp] using (total p).symm
      preservesRelation := fun r U a ha => by
        simpa only [sheafTupleMap_id] using (relation r U a).mpr ha
      preservesDomain := fun p U a ha => by
        simpa only [sheafTupleMap_id] using (domain p U a).mpr ha
      preservesPartial := fun p => by
        ext U a
        exact (partialValue p U a.val ((domain p U a.val).mpr a.property) a.property).symm
      preservesQuantity := fun q => by simpa only [Category.comp_id, sheafTupleMap_id, Category.id_comp] using (quantity q).symm }
  exact ⟨forward, backward, SheafStructure.Hom.ext (funext fun _ => Category.id_comp _),
    SheafStructure.Hom.ext (funext fun _ => Category.id_comp _)⟩

end SHIGURE.Copying
