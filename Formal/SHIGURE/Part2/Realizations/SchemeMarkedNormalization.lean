import Formal.SHIGURE.Part2.Realizations.MarkedSchemeChart

/-! # Normalizing marked realizations along their actual selected sheaf bases -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SHIGURE.SchemeDescent SHIGURE.TensorRealization

noncomputable section

universe u

variable (X : Scheme.{u}) (sig : Signature.{u}) (rank m : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank m)

private abbrev operationOn (E : sig.SortType → X.Modules) (a : Arity sig.SortType) :=
  moduleMultilinearTensor (fun i : TensorPosition a.inputs => E i.1) ⟶ E a.output

/-- A marked scheme realization whose designated columns form global sheaf bases.
Its original carriers may be any modules with those actual bases. -/
structure BasedSchemeMarkedRealization where
  carrier : sig.SortType → X.Modules
  basis (s : sig.SortType) : coordinateModuleSheaf X (rank s) ≅ carrier s
  marking (s : sig.SortType) : coordinateModuleSheaf X (m s) ⟶ carrier s
  total (e : sig.Total) : operationOn X sig carrier (sig.totalArity e)
  quantity (q : sig.Quantity) : operationOn X sig carrier (sig.quantityArity q)
  selected : ∀ s i j, schemeMarkingMatricesEquiv X sig rank m
    (fun t => marking t ≫ (basis t).inv) s i (choice s j) = if i = j then 1 else 0

namespace BasedSchemeMarkedRealization

variable (A B : BasedSchemeMarkedRealization X sig rank m choice)

private def operationInBasis {a : Arity sig.SortType} (u : operationOn X sig A.carrier a) :
    operationOn X sig (fun s => coordinateModuleSheaf X (rank s)) a :=
  moduleMultilinearTensorMap (fun i : TensorPosition a.inputs => (A.basis i.1).hom) ≫
    u ≫ (A.basis a.output).inv

/-- Read the original operations and markings on their actual chosen bases. -/
def normalize : NormalizedSchemeMarkedTensor X sig rank m choice :=
  ⟨⟨fun e => operationInBasis X sig rank m choice A (A.total e),
      fun q => operationInBasis X sig rank m choice A (A.quantity q)⟩,
    ⟨fun s => A.marking s ≫ (A.basis s).inv, A.selected⟩⟩

/-- The standard carrier and marking maps of a normalized chart realization. -/
def ofNormalized (P : NormalizedSchemeMarkedTensor X sig rank m choice) :
    BasedSchemeMarkedRealization X sig rank m choice where
  carrier s := coordinateModuleSheaf X (rank s)
  basis s := Iso.refl _
  marking s := P.2.val s
  total := P.1.total
  quantity := P.1.quantity
  selected := by
    have base : (fun s => P.2.val s ≫ (Iso.refl _).inv) = P.2.val := funext fun s => Category.comp_id _
    rw [base]
    exact P.2.property

/-- A family of actual sheaf isomorphisms preserving the original markings and operations. -/
structure MarkedIso where
  carrier (s : sig.SortType) : A.carrier s ≅ B.carrier s
  marking (s : sig.SortType) : A.marking s ≫ (carrier s).hom = B.marking s
  total (e : sig.Total) :
    A.total e ≫ (carrier (sig.totalArity e).output).hom =
      moduleMultilinearTensorMap (fun i : TensorPosition (sig.totalArity e).inputs =>
        (carrier i.1).hom) ≫ B.total e
  quantity (q : sig.Quantity) :
    A.quantity q ≫ (carrier (sig.quantityArity q).output).hom =
      moduleMultilinearTensorMap (fun i : TensorPosition (sig.quantityArity q).inputs =>
        (carrier i.1).hom) ≫ B.quantity q

private theorem operationInBasis_commutes {a : Arity sig.SortType} (u : operationOn X sig A.carrier a) :
    operationInBasis X sig rank m choice A u ≫ (A.basis a.output).hom =
      moduleMultilinearTensorMap (fun i : TensorPosition a.inputs => (A.basis i.1).hom) ≫ u := by
  unfold operationInBasis
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The normalized chart presentation is isomorphic to the original
realization by the actual chosen bases and preserves every marked generator. -/
def normalizeIso :
    MarkedIso X sig rank m choice
      (ofNormalized X sig rank m choice (A.normalize X sig rank m choice)) A where
  carrier := A.basis
  marking s := by
    change (A.marking s ≫ (A.basis s).inv) ≫ (A.basis s).hom = A.marking s
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  total e := operationInBasis_commutes X sig rank m choice A (A.total e)
  quantity q := operationInBasis_commutes X sig rank m choice A (A.quantity q)

/-- The original marking is surjective on every open whenever the selected
sections form the chosen basis. -/
theorem marking_surjective (s : sig.SortType) (U : X.Opensᵒᵖ) :
    Function.Surjective ((A.marking s).val.app U) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf U
  let b := (F.mapIso (A.basis s)).toLinearEquiv
  intro y
  obtain ⟨x, hx⟩ := normalizedSchemeMarking_surjective_sections X sig rank m choice
    (A.normalize X sig rank m choice).2 s U (b.symm y)
  refine ⟨x, ?_⟩
  change b.symm ((A.marking s).val.app U x) = b.symm y at hx
  exact b.symm.injective hx

/-- The actual underlying sheaf isomorphisms preserving a marking are unique. -/
theorem markingIso_carrier_unique (f g : MarkedIso X sig rank m choice A B) (s : sig.SortType) :
    f.carrier s = g.carrier s := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext y
  obtain ⟨x, rfl⟩ := A.marking_surjective X sig rank m choice s U y
  have same := (f.marking s).trans (g.marking s).symm
  exact congrArg (fun t => t.val.app U x) same

private theorem normalized_marking_map_is_identity
    (P Q : NormalizedSchemeMarking X sig rank m choice) (s : sig.SortType)
    (g : coordinateModuleSheaf X (rank s) ⟶ coordinateModuleSheaf X (rank s))
    (compatible : P.val s ≫ g = Q.val s) : g = 𝟙 _ := by
  let U := op (⊤ : X.Opens)
  let n := rank s
  apply (coordinateModuleMatrixEquiv X n n).injective
  ext i j
  let V := coordinateModuleUnitColumn X (m s) U (choice s j)
  let W := coordinateModuleUnitColumn X n U j
  have equation := congrArg (fun f => f.val.app U V) compatible
  change g.val.app U ((P.val s).val.app U V) = (Q.val s).val.app U V at equation
  have a : (P.val s).val.app U V = W := normalizedSchemeMarking_selected_sections X sig rank m choice P s U j
  have b : (Q.val s).val.app U V = W := normalizedSchemeMarking_selected_sections X sig rank m choice Q s U j
  rw [a, b] at equation
  exact congrArg (fun x => (coordinateModuleSectionIso X n U).hom x i) equation

private theorem markedIso_chosen_basis (e : MarkedIso X sig rank m choice A B) (s : sig.SortType) :
    (A.basis s).hom ≫ (e.carrier s).hom = (B.basis s).hom := by
  let g := (A.basis s).hom ≫ (e.carrier s).hom ≫ (B.basis s).inv
  have marking : (A.normalize X sig rank m choice).2.val s ≫ g =
      (B.normalize X sig rank m choice).2.val s := by
    change (A.marking s ≫ (A.basis s).inv) ≫ ((A.basis s).hom ≫ (e.carrier s).hom ≫ (B.basis s).inv) =
      B.marking s ≫ (B.basis s).inv
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (B.basis s).inv) (e.marking s))
  have id := normalized_marking_map_is_identity X sig rank m choice
    (A.normalize X sig rank m choice).2 (B.normalize X sig rank m choice).2 s g marking
  apply (cancel_mono (B.basis s).inv).mp
  exact (Category.assoc _ _ _).trans (id.trans (B.basis s).hom_inv_id.symm)

private theorem markedIso_chosen_inverse (e : MarkedIso X sig rank m choice A B) (s : sig.SortType) :
    (e.carrier s).hom ≫ (B.basis s).inv = (A.basis s).inv := by
  apply (cancel_epi (A.basis s).hom).mp
  rw [← Category.assoc, markedIso_chosen_basis X sig rank m choice A B e s,
    Iso.hom_inv_id, Iso.hom_inv_id]

private theorem normalized_operation_eq (e : MarkedIso X sig rank m choice A B)
    {a : Arity sig.SortType} (l : operationOn X sig A.carrier a) (r : operationOn X sig B.carrier a)
    (preserved : l ≫ (e.carrier a.output).hom =
      moduleMultilinearTensorMap (fun i : TensorPosition a.inputs => (e.carrier i.1).hom) ≫ r) :
    operationInBasis X sig rank m choice A l = operationInBasis X sig rank m choice B r := by
  let F := moduleMultilinearTensorFunctor X (TensorPosition a.inputs)
  let x (i : TensorPosition a.inputs) := (A.basis i.1).hom
  let y (i : TensorPosition a.inputs) := (e.carrier i.1).hom
  let z (i : TensorPosition a.inputs) := (B.basis i.1).hom
  have equalBasis : (fun i : TensorPosition a.inputs => x i ≫ y i) = z :=
    funext fun i => markedIso_chosen_basis X sig rank m choice A B e i.1
  have image : F.map x ≫ F.map y = F.map z :=
    (F.map_comp x y).symm.trans (congrArg F.map equalBasis)
  change F.map x ≫ l ≫ (A.basis a.output).inv = F.map z ≫ r ≫ (B.basis a.output).inv
  rw [← markedIso_chosen_inverse X sig rank m choice A B e a.output]
  rw [← Category.assoc l, preserved]
  change F.map x ≫ (F.map y ≫ r) ≫ (B.basis a.output).inv = _
  calc
    _ = (F.map x ≫ F.map y) ≫ r ≫ (B.basis a.output).inv := by
      simp only [Category.assoc]
    _ = _ := congrArg (· ≫ r ≫ (B.basis a.output).inv) image

/-- Isomorphic originally marked realizations have exactly the same normalized data. -/
theorem normalize_eq_of_iso (e : MarkedIso X sig rank m choice A B) :
    A.normalize X sig rank m choice = B.normalize X sig rank m choice := by
  apply Prod.ext
  · apply FreeSchemePrimitive.ext
    · funext k
      exact normalized_operation_eq X sig rank m choice A B e _ _ (e.total k)
    · funext k
      exact normalized_operation_eq X sig rank m choice A B e _ _ (e.quantity k)
  · apply Subtype.ext
    funext s
    change A.marking s ≫ (A.basis s).inv = B.marking s ≫ (B.basis s).inv
    rw [← markedIso_chosen_inverse X sig rank m choice A B e s, ← Category.assoc, e.marking]

private theorem normalize_ofNormalized (P : NormalizedSchemeMarkedTensor X sig rank m choice) :
    (ofNormalized X sig rank m choice P).normalize X sig rank m choice = P := by
  apply Prod.ext
  · apply FreeSchemePrimitive.ext
    · funext k
      change (moduleMultilinearTensorFunctor X (TensorPosition (sig.totalArity k).inputs)).map
        (𝟙 _) ≫ P.1.total k ≫ 𝟙 _ = _
      have h := (moduleMultilinearTensorFunctor X (TensorPosition (sig.totalArity k).inputs)).map_id
        (fun i : TensorPosition (sig.totalArity k).inputs => coordinateModuleSheaf X (rank i.1))
      rw [h, Category.id_comp, Category.comp_id]
    · funext k
      change (moduleMultilinearTensorFunctor X (TensorPosition (sig.quantityArity k).inputs)).map
        (𝟙 _) ≫ P.1.quantity k ≫ 𝟙 _ = _
      have h := (moduleMultilinearTensorFunctor X (TensorPosition (sig.quantityArity k).inputs)).map_id
        (fun i : TensorPosition (sig.quantityArity k).inputs => coordinateModuleSheaf X (rank i.1))
      rw [h, Category.id_comp, Category.comp_id]
  · apply Subtype.ext
    exact funext fun s => Category.comp_id (P.2.val s)

/-- The actual isomorphism classes given by the chosen global basis are
represented by the normalized marked objects. -/
def markedIsoClassEquiv :
    Quot (fun A B : BasedSchemeMarkedRealization X sig rank m choice =>
      Nonempty (MarkedIso X sig rank m choice A B)) ≃
      NormalizedSchemeMarkedTensor X sig rank m choice where
  toFun := Quot.lift (normalize X sig rank m choice)
    (fun A B ⟨e⟩ => normalize_eq_of_iso X sig rank m choice A B e)
  invFun P := Quot.mk _ (ofNormalized X sig rank m choice P)
  left_inv x := Quot.inductionOn x (fun A => Quot.sound ⟨normalizeIso X sig rank m choice A⟩)
  right_inv := normalize_ofNormalized X sig rank m choice

end BasedSchemeMarkedRealization

end

end SHIGURE.RealizationFamilies
