import Formal.SHIGURE.Part1.ContextSelectedMorphisms
import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Formal.SHIGURE.Part2.Realizations.ZariskiModels
import Formal.SHIGURE.Part2.Realizations.SectionStructures
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# The copying mode as a coefficient realization

The mode takes actual sheaf arrows as carrier maps and uses the preservation
conditions of the primitive sheaf structure. The admissible objects are
Zariski locally split. The Law test is subsheaf inclusion on the test site.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

universe u

noncomputable section

namespace SHIGURE

/-- The affine coefficient scheme associated to a specified ring. -/
def CoefficientRing.spec (R : CoefficientRing.{u}) : Scheme.{u} :=
  letI := R.ring
  Spec (CommRingCat.of R.Carrier)

/-- A coefficient ring map acts contravariantly on affine coefficient schemes. -/
def CoefficientRing.specMap {R S : CoefficientRing.{u}} (f : R.Hom S) : S.spec ⟶ R.spec :=
  letI := R.ring
  letI := S.ring
  Spec.map (CommRingCat.ofHom f)

namespace Copying

/-- View a predicate as the monomorphism into its ambient sheaf. -/
private def realizedPredicate {S : Scheme.{u}} {F : ZariskiSheaf S}
    (P : SheafPredicate F) : MonoOver F :=
  letI : Mono P.inclusion.val := inferInstanceAs (Mono P.carrier.ι)
  letI : Mono P.inclusion :=
    Sheaf.Hom.mono_of_presheaf_mono (Scheme.zariskiTopology.over S) (Type u) P.inclusion
  MonoOver.mk P.inclusion

/-- Form the sheaf of assignments in the declared context. -/
private def copyingInputs (S : Scheme.{u}) {K : Type u} (Γ : List K) :
    (K → ZariskiSheaf S) ⥤ ZariskiSheaf S where
  obj A := sheafTuple A Γ
  map f := sheafTupleMap f Γ
  map_id A := sheafTupleMap_id A Γ
  map_comp f g := sheafTupleMap_comp f g Γ

/-- Form the sheaf product indexed by the actual positions of the declaration. -/
private def copyingPositionInputs (S : Scheme.{u}) (I : Type u) :
    (I → ZariskiSheaf S) ⥤ ZariskiSheaf S where
  obj A := ∏ᶜ A
  map f := Limits.Pi.map f
  map_id _ := Limits.Pi.map_id
  map_comp f g := (Limits.Pi.map_comp_map f g).symm

/-- Compare assignment syntax with the position-indexed product at one carrier family. -/
private def copyingInputIsoAt {S : Scheme.{u}} {K : Type u} (A : K → ZariskiSheaf S) (Γ : List K) :
    sheafTuple A Γ ≅ ∏ᶜ (fun i : (s : K) × Var Γ s => A i.1) :=
  (sheafTupleFanIsLimit A Γ).conePointUniqueUpToIso (limit.isLimit _)

/-- Identify each projection of the position-indexed product with assignment lookup. -/
private theorem copyingInputIsoAt_hom_π {S : Scheme.{u}} {K : Type u}
    (A : K → ZariskiSheaf S) (Γ : List K) (i : (s : K) × Var Γ s) :
    (copyingInputIsoAt A Γ).hom ≫ Limits.Pi.π _ i = sheafTupleProj A i.2 := by
  exact limit.lift_π (sheafTupleFan A Γ) ⟨i⟩

/-- Make the lookup comparison natural in all carrier maps. -/
private def copyingInputIso (S : Scheme.{u}) {K : Type u} (Γ : List K) :
    copyingInputs S Γ ≅ CategoryTheory.Pi.comap (fun _ : K => ZariskiSheaf S) (fun i : (s : K) × Var Γ s => i.1) ⋙
      copyingPositionInputs S ((s : K) × Var Γ s) :=
  NatIso.ofComponents (fun A => copyingInputIsoAt A Γ) (by
    intro A B f
    apply Limits.Pi.hom_ext
    intro i
    change (sheafTupleMap f Γ ≫ (copyingInputIsoAt B Γ).hom) ≫ Limits.Pi.π _ i =
      ((copyingInputIsoAt A Γ).hom ≫ Limits.Pi.map (fun j => f j.1)) ≫ Limits.Pi.π _ i
    rw [Category.assoc, copyingInputIsoAt_hom_π, Category.assoc, Limits.Pi.map_π,
      ← Category.assoc, copyingInputIsoAt_hom_π]
    exact Sheaf.Hom.ext rfl)

/-- Identify a single-position assignment with its entry. -/
private def copyingUnaryIsoAt {S : Scheme.{u}} {K : Type u} (A : K → ZariskiSheaf S) (s : K) :
    sheafTuple A [s] ≅ A s where
  hom := sheafTupleProj A Var.here
  inv := ⟨{
    app := fun _ => ↾fun x => Assignment.cons x Assignment.empty
    naturality := by
      intro U V f
      ext x
      apply Assignment.ext
      intro t i
      cases i with
      | here => rfl
      | there i => exact nomatch i }⟩
  hom_inv_id := by
    ext U x
    apply Assignment.ext
    intro t i
    cases i with
    | here => rfl
    | there i => exact nomatch i
  inv_hom_id := Sheaf.Hom.ext rfl

/-- Lift the single-position comparison to an isomorphism of input functors. -/
private def copyingUnaryIso (S : Scheme.{u}) {K : Type u} (s : K) :
    copyingInputs S [s] ≅ CategoryTheory.Pi.eval (fun _ : K => ZariskiSheaf S) s :=
  NatIso.ofComponents (fun A => copyingUnaryIsoAt A s) (fun _ => Sheaf.Hom.ext rfl)

/-- The empty assignment is the unique section of the tensor unit. -/
private def copyingNullaryIsoAt {S : Scheme.{u}} {K : Type u} (A : K → ZariskiSheaf S) :
    sheafTuple A [] ≅ 𝟙_ (ZariskiSheaf S) where
  hom := ⟨{ app := fun _ => ↾fun _ => PUnit.unit }⟩
  inv := ⟨{
    app := fun _ => ↾fun _ => Assignment.empty
    naturality := by
      intro U V f
      ext x
      apply Assignment.ext
      intro t i
      exact nomatch i }⟩
  hom_inv_id := by
    ext U a
    apply Assignment.ext
    intro t i
    exact nomatch i
  inv_hom_id := by
    ext U x
    exact @Subsingleton.elim PUnit inferInstance _ _

/-- Compare the empty assignment functor with the constant terminal sheaf. -/
private def copyingNullaryIso (S : Scheme.{u}) (K : Type u) :
    copyingInputs S ([] : List K) ≅ (Functor.const (K → ZariskiSheaf S)).obj (𝟙_ (ZariskiSheaf S)) :=
  NatIso.ofComponents copyingNullaryIsoAt (by
    intro A B f
    ext U x
    exact @Subsingleton.elim PUnit inferInstance _ _)

/-- Split off the first entry of a sheaf assignment. -/
private def copyingConsIsoAt {S : Scheme.{u}} {K : Type u}
    (A : K → ZariskiSheaf S) (s : K) (Γ : List K) :
    sheafTuple A (s :: Γ) ≅ A s ⊗ sheafTuple A Γ where
  hom := ⟨{
    app := fun _ => ↾fun a => (a.get .here, ⟨fun i => a.get (.there i)⟩)
    naturality := by
      intro U V f
      ext a
      rfl }⟩
  inv := ⟨{
    app := fun _ => ↾fun a => Assignment.cons a.1 a.2
    naturality := by
      intro U V f
      ext a
      apply Assignment.ext
      intro t i
      cases i <;> rfl }⟩
  hom_inv_id := by
    ext U a
    apply Assignment.ext
    intro t i
    cases i <;> rfl
  inv_hom_id := Sheaf.Hom.ext rfl

/-- Make the first-entry splitting natural in all carrier maps. -/
private def copyingConsIso (S : Scheme.{u}) {K : Type u} (s : K) (Γ : List K) :
    copyingInputs S (s :: Γ) ≅
      ((CategoryTheory.Pi.eval (fun _ : K => ZariskiSheaf S) s).prod' (copyingInputs S Γ)) ⋙
        MonoidalCategory.tensor (ZariskiSheaf S) :=
  NatIso.ofComponents (fun A => copyingConsIsoAt A s Γ) (by
    intro A B f
    apply Sheaf.Hom.ext
    ext U a
    rfl)

/-- Build a generalized input point from its coordinate maps using the product limit. -/
private def copyingTuplePoint {S : Scheme.{u}} {K : Type u} (Γ : List K)
    (A : K → ZariskiSheaf S) {P : ZariskiSheaf S}
    (p : ∀ i : (s : K) × Var Γ s, P ⟶ A i.1) : P ⟶ sheafTuple A Γ :=
  (sheafTupleFanIsLimit A Γ).lift (Fan.mk P p)

/-- The product lift recovers exactly the given map at every argument position. -/
private theorem copyingTuplePoint_proj {S : Scheme.{u}} {K : Type u} (Γ : List K)
    (A : K → ZariskiSheaf S) {P : ZariskiSheaf S}
    (p : ∀ i : (s : K) × Var Γ s, P ⟶ A i.1) (i : (s : K) × Var Γ s) :
    copyingTuplePoint Γ A p ≫ sheafTupleProj A i.2 = p i :=
  (sheafTupleFanIsLimit A Γ).fac (Fan.mk P p) ⟨i⟩

/-- Send each section to the unique state of the singleton sheaf. -/
private def toOneState {S : Scheme.{u}} (P : ZariskiSheaf S) : P ⟶ constantCarrier S PUnit :=
  ⟨{ app := fun _ => ↾fun _ => LocallyConstant.const _ PUnit.unit }⟩

/-- The singleton sheaf has the terminal property used to identify global sections. -/
private def copyingPointTerminal (S : Scheme.{u}) : IsTerminal (constantCarrier S PUnit) :=
  IsTerminal.ofUniqueHom toOneState (fun _ _ => by
    apply Sheaf.Hom.ext
    ext U a
    apply LocallyConstant.ext
    intro x
    exact Subsingleton.elim _ _)

/-- Identify the singleton point source with empty inputs throughout the carrier category. -/
private def copyingNullaryPoints (S : Scheme.{u}) {K : Type u} :
    (Functor.const (K → ZariskiSheaf S)).obj (constantCarrier S PUnit) ≅ copyingInputs S ([] : List K) :=
  NatIso.ofComponents (fun A =>
    { hom := copyingTuplePoint [] A (fun i => nomatch i.2)
      inv := toOneState (sheafTuple A [])
      hom_inv_id := (copyingPointTerminal S).hom_ext _ _
      inv_hom_id := (sheafTupleFanIsLimit A []).hom_ext (fun ⟨i⟩ => nomatch i.2) })
    (by
      intro _ B _
      exact (sheafTupleFanIsLimit B []).hom_ext (fun ⟨i⟩ => nomatch i.2))

/-- The primitive diagrams of a copying realization use Cartesian tuples and
the inclusions of the relation and domain subsheaves. -/
def copyingStructureRule (sig : Signature.{u}) (S : Scheme.{u}) :
    StructureRule sig (Cat.of (ZariskiSheaf S))
      (SheafStructure sig (Scheme.zariskiTopology.over S)) where
  carrier A := A.carrier
  Ambient := Cat.of (ZariskiSheaf S)
  view := 𝟭 _
  view_faithful := inferInstance
  input := copyingInputs S
  positionalInput Γ := copyingPositionInputs S ((s : sig.SortType) × Var Γ s)
  inputIso := copyingInputIso S
  unaryIso := copyingUnaryIso S
  monoidal := inferInstanceAs (MonoidalCategory (ZariskiSheaf S))
  fullInput := copyingInputs S
  fullInput_nil := copyingNullaryIso S _
  fullInput_cons := copyingConsIso S
  multipleInputComparison s t Γ := 𝟙 (copyingInputs S (s :: t :: Γ))
  multipleInputComparison_epi _ _ _ _ := inferInstanceAs (Epi (𝟙 _))
  pointObject := constantCarrier S PUnit
  pointUnit := (copyingNullaryPoints S (K := sig.SortType)).app (fun _ => constantCarrier S PUnit) ≪≫
    (copyingNullaryIso S sig.SortType).app (fun _ => constantCarrier S PUnit)
  nullaryInput := copyingNullaryPoints S
  total := SheafStructure.total
  relation A r := realizedPredicate (A.relation r)
  domain A p := realizedPredicate (A.partialDomain p)
  partialValue := SheafStructure.partialValue
  quantity := SheafStructure.quantity

/-- The Cartesian full input of unit points is the tuple given by the product limit. -/
private theorem copyingFullInputPoint (sig : Signature.{u}) (S : Scheme.{u})
    (Γ : List sig.SortType) (A : sig.SortType → ZariskiSheaf S)
    (p : ∀ i : (s : sig.SortType) × Var Γ s, constantCarrier S PUnit ⟶ A i.1) :
    (copyingStructureRule sig S).fullInputPoint A Γ p = copyingTuplePoint Γ A p := by
  let rule := copyingStructureRule sig S
  induction Γ with
  | nil =>
    apply (sheafTupleFanIsLimit A []).hom_ext
    rintro ⟨⟨_, i⟩⟩
    exact nomatch i
  | cons s Γ ih =>
    apply (sheafTupleFanIsLimit A (s :: Γ)).hom_ext
    rintro ⟨⟨t, i⟩⟩
    change rule.fullInputPoint A (s :: Γ) p ≫ sheafTupleProj A i =
      copyingTuplePoint (s :: Γ) A p ≫ sheafTupleProj A i
    refine Eq.trans ?_ (copyingTuplePoint_proj (s :: Γ) A p ⟨t, i⟩).symm
    cases i with
    | here => rfl
    | there j =>
      let q : ∀ i : (s : sig.SortType) × Var Γ s, constantCarrier S PUnit ⟶ A i.1 :=
        fun i => p ⟨i.1, .there i.2⟩
      apply Sheaf.Hom.ext
      ext U x
      change (((rule.fullInputPoint A Γ q).val.app U)
        (rule.pointUnit.inv.val.app U PUnit.unit)).get j = (q ⟨t, j⟩).val.app U x
      have hx : rule.pointUnit.inv.val.app U PUnit.unit = x := by
        change (_ : LocallyConstant U.unop.left PUnit) = _
        apply LocallyConstant.ext
        intro y
        exact Subsingleton.elim _ _
      rw [hx, ih q]
      exact congrArg (fun f : constantCarrier S PUnit ⟶ A t => f.val.app U x)
        (copyingTuplePoint_proj Γ A q ⟨t, j⟩)

/-- The Cartesian input of the copying mode is tested on all sheaf tuples. -/
def copyingInputPoints (sig : Signature.{u}) (S : Scheme.{u}) :
    StructureInputPoints (copyingStructureRule sig S) where
  Probe := Cat.of (ZariskiSheaf S)
  probe := 𝟭 _
  tuplePoint P Γ A p := copyingTuplePoint Γ A p
  tuplePoint_map P Γ {A B} f p := by
    apply (sheafTupleFanIsLimit B Γ).hom_ext
    intro ⟨i⟩
    change (copyingTuplePoint Γ A p ≫ sheafTupleMap f Γ) ≫ sheafTupleProj B i.2 =
      copyingTuplePoint Γ B (fun j => p j ≫ f j.1) ≫ sheafTupleProj B i.2
    rw [Category.assoc, copyingTuplePoint_proj]
    have hf : sheafTupleMap f Γ ≫ sheafTupleProj B i.2 = sheafTupleProj A i.2 ≫ f i.1 :=
      Sheaf.Hom.ext rfl
    rw [hf, ← Category.assoc, copyingTuplePoint_proj]
  tuplePoint_restrict {P Q} f Γ A p := by
    apply (sheafTupleFanIsLimit A Γ).hom_ext
    intro ⟨i⟩
    change copyingTuplePoint Γ A (fun j => f ≫ p j) ≫ sheafTupleProj A i.2 =
      (f ≫ copyingTuplePoint Γ A p) ≫ sheafTupleProj A i.2
    rw [Category.assoc, copyingTuplePoint_proj, copyingTuplePoint_proj]
  tuplePoint_ext Γ A {Y f g} h := by
    have hi : copyingTuplePoint Γ A (fun i => sheafTupleProj A i.2) = 𝟙 _ :=
      (sheafTupleFanIsLimit A Γ).lift_self
    simpa only [hi, Category.id_comp] using h (sheafTuple A Γ) (fun i => sheafTupleProj A i.2)

/-- At the singleton test, the copying tests and unit-point input use the same Cartesian tuple. -/
theorem copyingInputPoints_unit (sig : Signature.{u}) (S : Scheme.{u})
    (Γ : List sig.SortType) (A : sig.SortType → ZariskiSheaf S)
    (p : ∀ i : (s : sig.SortType) × Var Γ s, constantCarrier S PUnit ⟶ A i.1) :
    (copyingInputPoints sig S).tuplePoint (constantCarrier S PUnit) Γ A p =
      (copyingStructureRule sig S).inputPoint A Γ p := by
  let rule := copyingStructureRule sig S
  change copyingTuplePoint Γ A p = rule.inputPoint A Γ p
  match Γ with
  | [] =>
    apply (sheafTupleFanIsLimit A []).hom_ext
    rintro ⟨⟨_, i⟩⟩
    exact nomatch i
  | [s] =>
    apply (cancel_mono ((rule.unaryIso s).hom.app A)).mp
    rw [rule.inputPoint_unary]
    change copyingTuplePoint [s] A p ≫ sheafTupleProj A (Var.here : Var [s] s) = p ⟨s, .here⟩
    exact copyingTuplePoint_proj [s] A p ⟨s, .here⟩
  | s :: t :: Γ =>
    change _ = rule.fullInputPoint A (s :: t :: Γ) p ≫ 𝟙 _
    rw [Category.comp_id, copyingFullInputPoint]

/-- A nullary copying input is the terminal sheaf. -/
def copyingStructureRule_nullaryIso (sig : Signature.{u}) (S : Scheme.{u}) :
    (copyingStructureRule sig S).input [] ≅
      (Functor.const (sig.SortType → ZariskiSheaf S)).obj (𝟙_ (ZariskiSheaf S)) :=
  copyingNullaryIso S _

/-- A copying input with one more position is the Cartesian product with its carrier. -/
def copyingStructureRule_consIso (sig : Signature.{u}) (S : Scheme.{u}) (s : sig.SortType)
    (Γ : List sig.SortType) :
    (copyingStructureRule sig S).input (s :: Γ) ≅
      ((CategoryTheory.Pi.eval (fun _ : sig.SortType => ZariskiSheaf S) s).prod'
        ((copyingStructureRule sig S).input Γ)) ⋙ MonoidalCategory.tensor (ZariskiSheaf S) :=
  copyingConsIso S s Γ

/-- An actual factorization through a predicate gives inclusion in its inverse image. -/
private theorem predicate_le_of_factor {S : Scheme.{u}} {F G : ZariskiSheaf S}
    {P : SheafPredicate F} {Q : SheafPredicate G} {f : F ⟶ G}
    {g : P.toSheaf ⟶ Q.toSheaf} (h : g ≫ Q.inclusion = P.inclusion ≫ f) :
    P.carrier ≤ (Q.preimage f).carrier := by
  intro U x hx
  change f.val.app U x ∈ Q.carrier.obj U
  have he := congrArg (fun k : P.toSheaf ⟶ G => k.val.app U ⟨x, hx⟩) h
  change (g.val.app U ⟨x, hx⟩).val = f.val.app U x at he
  exact he ▸ (g.val.app U ⟨x, hx⟩).property

/-- A predicate inclusion into an inverse image induces the map on the representing subsheaves. -/
private theorem mapAlong_factor {S : Scheme.{u}} {F G : ZariskiSheaf S}
    {P : SheafPredicate F} {Q : SheafPredicate G} {f : F ⟶ G}
    (h : P.carrier ≤ (Q.preimage f).carrier) :
    SheafPredicate.mapAlong f h ≫ Q.inclusion = P.inclusion ≫ f :=
  Sheaf.Hom.ext rfl

/-- The target predicate monomorphism determines any factorization uniquely. -/
private theorem predicate_factor_unique {S : Scheme.{u}} {F G : ZariskiSheaf S}
    {P : SheafPredicate F} {Q : SheafPredicate G} {f : F ⟶ G}
    {g : P.toSheaf ⟶ Q.toSheaf} (h : g ≫ Q.inclusion = P.inclusion ≫ f)
    (h' : P.carrier ≤ (Q.preimage f).carrier) : g = SheafPredicate.mapAlong f h' := by
  letI : Mono Q.inclusion := (realizedPredicate Q).property
  exact (cancel_mono Q.inclusion).mp (h.trans (mapAlong_factor h').symm)

/-- A preserving carrier family in the primitive diagrams is exactly a
structure-preserving sheaf morphism. -/
def copyingStructureHomEquiv (sig : Signature.{u}) (S : Scheme.{u})
    (A B : (copyingStructureRule sig S).Category) :
    (A ⟶ B) ≃ SheafStructure.Hom A B where
  toFun h :=
    have domain (p : sig.Partial) :
        (A.partialDomain p).carrier ≤
          ((B.partialDomain p).preimage (sheafTupleMap h.val _)).carrier := by
      obtain ⟨_, hi, _⟩ := h.property.partialOp p
      exact predicate_le_of_factor hi
    { onSort := h.val
      preservesTotal := h.property.total
      preservesRelation := fun r => by
        obtain ⟨_, hi⟩ := h.property.relation r
        exact predicate_le_of_factor hi
      preservesDomain := domain
      preservesPartial := fun p => by
        obtain ⟨g, hi, hv⟩ := h.property.partialOp p
        have hg : g = SheafPredicate.mapAlong (sheafTupleMap h.val _) (domain p) :=
          predicate_factor_unique hi (domain p)
        rw [← hg]
        exact hv.symm
      preservesQuantity := h.property.quantity }
  invFun h := ⟨h.onSort,
    { total := h.preservesTotal
      relation := fun r => ⟨_, mapAlong_factor (h.preservesRelation r)⟩
      partialOp := fun p => ⟨_, mapAlong_factor (h.preservesDomain p), (h.preservesPartial p).symm⟩
      quantity := h.preservesQuantity }⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := SheafStructure.Hom.ext rfl

/-- A designated state of a sheaf structure is its section over the coefficient scheme. -/
private abbrev states {sig : Signature.{u}} {S : Scheme.{u}}
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) (s : sig.SortType) :=
  (A.carrier s).val.obj (op (Over.mk (𝟙 S)))

/-- Pull a designated state back to the new coefficient scheme. -/
def restrictState {sig : Signature.{u}} {S S' : Scheme.{u}}
    (f : S' ⟶ S) (A : SheafStructure sig (Scheme.zariskiTopology.over S)) (s : sig.SortType) :
    states A s → states (restrictStructure f A) s :=
  let g : (Over.map f).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S) :=
    Over.homMk f (by simp)
  (A.carrier s).val.map g.op

/-- Use the structure map as the unique arrow to the terminal relative test. -/
private def toCoefficient {S : Scheme.{u}} (U : Over S) : U ⟶ Over.mk (𝟙 S) :=
  Over.homMk U.hom (by simp)

/-- Read a section at the coefficient scheme as a map from the singleton sheaf. -/
private def sectionAsPoint {S : Scheme.{u}} {F : ZariskiSheaf S}
    (x : F.val.obj (op (Over.mk (𝟙 S)))) : constantCarrier S PUnit ⟶ F :=
  ⟨{ app := fun U => ↾fun _ => F.val.map (toCoefficient U.unop).op x
     naturality := by
       intro U V f
       ext y
       change F.val.map (toCoefficient V.unop).op x =
         F.val.map f (F.val.map (toCoefficient U.unop).op x)
       have h : (toCoefficient U.unop).op ≫ f = (toCoefficient V.unop).op := by
         apply Quiver.Hom.unop_inj
         apply Over.OverMorphism.ext
         exact Over.w f.unop
       rw [← h, Functor.map_comp]
       rfl }⟩

/-- A point from the one-state carrier is precisely a section over the coefficient scheme. -/
def copyingPointEquiv {S : Scheme.{u}} (F : ZariskiSheaf S) :
    (constantCarrier S PUnit ⟶ F) ≃ F.val.obj (op (Over.mk (𝟙 S))) where
  toFun p := p.val.app _ (LocallyConstant.const _ PUnit.unit)
  invFun := sectionAsPoint
  left_inv p := by
    apply Sheaf.Hom.ext
    ext U y
    change F.val.map (toCoefficient U.unop).op (p.val.app _ _) = p.val.app U y
    rw [← FunctorToTypes.naturality]
    congr
  right_inv x := by
    change F.val.map (toCoefficient (Over.mk (𝟙 S))).op x = x
    have h : toCoefficient (Over.mk (𝟙 S)) = 𝟙 _ := Over.OverMorphism.ext rfl
    simpa only [h, op_id] using FunctorToTypes.map_id_apply F.val x

/-- The concrete copying realization mode of Definition 4.1. -/
def copyingMode (base : CoefficientRing.{u}) (T : Theory.{u}) :
    CoefficientRealizationMode base (RealizationTheory.ofTheory T) where
  Object R := SheafStructure T.signature (Scheme.zariskiTopology.over R.scalars.spec)
  Carrier R := Cat.of (ZariskiSheaf R.scalars.spec)
  rule R := copyingStructureRule T.signature R.scalars.spec
  admissible _ := IsZariskiSplit T
  Native := Structure T.signature
  nativeStates A := A.carrier
  nativePointSource R _ := (copyingStructureRule T.signature R.scalars.spec).pointObject
  realizeNative R := constantStructure R.scalars.spec
  nativePoints R A s x := (copyingPointEquiv ((constantStructure R.scalars.spec A).carrier s)).symm
    (nativeState R.scalars.spec (Over.mk (𝟙 R.scalars.spec)) x)
  change f := restrictStructure (CoefficientRing.specMap f)
  changePoints f A s p :=
    (copyingPointEquiv ((restrictStructure (CoefficientRing.specMap f) A).carrier s)).symm
      (restrictState (CoefficientRing.specMap f) A s (copyingPointEquiv (A.carrier s) p))
  holds _ A l := A.holdsLaw l

/-- The copying meaning of a selected primitive presentation in its coefficient algebra. -/
abbrev SelectedCopyingModels {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    {base : CoefficientRing.{u}} (R : CoefficientAlgebra base) :=
  (copyingMode base (DeclarationContext.Selected.presentation U).theory).Models R

/-- The global section structure read at the retained sorts of the Part I context. -/
def readCopyingContext {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    {S : Scheme.{u}} (A : SheafStructure (DeclarationContext.Selected.signature U)
      (Scheme.zariskiTopology.over S)) : ContextStructure U :=
  DeclarationContext.Selected.writeStructure (A.sections (op (Over.mk (𝟙 S))))

/-- A copying arrow gives the Part I structure-preserving map on the retained points. -/
def readCopyingContextMap {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {S : Scheme.{u}} {A B : SheafStructure (DeclarationContext.Selected.signature U)
      (Scheme.zariskiTopology.over S)} (f : SheafStructure.Hom A B) :
    ContextStructure.Hom (readCopyingContext U A) (readCopyingContext U B) :=
  DeclarationContext.Selected.writeStructureMap (f.sections (op (Over.mk (𝟙 S))))

/-- A semantic arrow in the selected copying mode acts on the Part I retained points. -/
def readSelectedCopyingMap {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} {R : CoefficientAlgebra base} {A B : SelectedCopyingModels U R}
    (f : A ⟶ B) : ContextStructure.Hom (readCopyingContext U A.obj) (readCopyingContext U B.obj) :=
  readCopyingContextMap
    (copyingStructureHomEquiv (DeclarationContext.Selected.signature U) R.scalars.spec A.obj B.obj f.hom)

/-- The Part I reading of a semantic arrow uses its action on the representing points. -/
theorem copyingPointEquiv_map {S : Scheme.{u}} {F G : ZariskiSheaf S}
    (h : F ⟶ G) (p : constantCarrier S PUnit ⟶ F) :
    copyingPointEquiv G (p ≫ h) =
      h.val.app (op (Over.mk (𝟙 S))) (copyingPointEquiv F p) :=
  rfl

/-- Realize the native structure read from the retained Part I declaration context. -/
def realizeSelectedCopying {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} (R : CoefficientAlgebra base) (A : ContextStructure U) :=
  (copyingMode base (DeclarationContext.Selected.presentation U).theory).realizeNative R
    (DeclarationContext.Selected.readStructure A)

/-- The native point of a retained sort has the original carrier of the context. -/
def realizeSelectedCopyingPoint {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} (R : CoefficientAlgebra base) (A : ContextStructure U)
    (s : DeclarationContext.Selected.SortName U) (x : A.carrier s.val) :=
  (copyingMode base (DeclarationContext.Selected.presentation U).theory).nativePoints R
    (DeclarationContext.Selected.readStructure A) s
    (DeclarationContext.Selected.readCarrierEquiv A s.val s.property x)

end Copying

end SHIGURE
