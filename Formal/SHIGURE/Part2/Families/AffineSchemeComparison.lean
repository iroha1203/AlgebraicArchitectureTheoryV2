import Formal.SHIGURE.Part2.Families.SchemeLaws
import Formal.SHIGURE.Part2.Schemes.TensorAffine
import Formal.SHIGURE.Part2.Schemes.ModuleTensorComparisons
import Formal.SHIGURE.Part2.Families.SchemeLawLocality
import Formal.SHIGURE.Part2.Families.AffineLawCoefficientComparison
import Formal.SHIGURE.Part2.Schemes.ConstantRankExamples

/-! # Associated sheaves of primitive tensor structures

Definition 6.1 and Appendix B.3 compare multilinear operations on coefficient
modules with morphisms from the actual ordered tensor product of associated
module sheaves. The comparison includes the empty input context.

## Implementation notes

The finite input comparison iterates the canonical binary affine tensor
comparison and the structure-sheaf unit comparison. Thus the construction
uses associated sheaves of the given coefficient modules and the actual
multilinear operations, without selecting bases.
-/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SchemeDescent TensorRealization
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

variable {R : CommRingCat.{u}} {S : Type u} {sig : Signature.{u}}

/-- The canonical affine comparison for ordered finite tensor inputs in
Definition 6.1. The empty input is identified using `tildeSelf`. -/
def tildeInputIso (E : S → ModuleCat.{u} R) : (ss : List S) →
    tensorModules (fun s => tilde (E s)) ss ≅
      tilde (ModuleCat.of R (InputTensor R E ss))
  | [] => tildeSelf.symm ≪≫
      (tilde.functor R).mapIso (inputTensorUnit R E).symm.toModuleIso
  | s :: ss => tensorModuleIso (Iso.refl _) (tildeInputIso E ss) ≪≫
      (tildeTensorIso R).app (E s, ModuleCat.of R (InputTensor R E ss)) ≪≫
      (tilde.functor R).mapIso (inputTensorCons R E s ss).symm.toModuleIso

/-- The recursive affine comparison exposes only its three canonical
component maps, without unfolding sheafification. -/
theorem tildeInputIso_hom_cons (E : S → ModuleCat.{u} R) (s : S) (ss : List S) :
    (tildeInputIso E (s :: ss)).hom =
      tensorModuleMap (𝟙 _) (tildeInputIso E ss).hom ≫
        tildeTensorMap R (E s) (ModuleCat.of R (InputTensor R E ss)) ≫
          tilde.map (inputTensorCons R E s ss).toModuleIso.inv := rfl

/-- The coefficient map on an input tensor, retaining all typed positions.
This API is used in the naturality of the affine input comparison. -/
def inputTensorMap {E F : S → ModuleCat.{u} R} (m : ∀ s, E s ⟶ F s) (ss : List S) :
    ModuleCat.of R (InputTensor R E ss) ⟶ ModuleCat.of R (InputTensor R F ss) :=
  ModuleCat.ofHom (PiTensorProduct.map fun i => (m i.1).hom)

/-- The empty coefficient tensor comparison respects every family of maps. -/
theorem inputTensorMap_nil {E F : S → ModuleCat.{u} R} (m : ∀ s, E s ⟶ F s) :
    inputTensorMap m [] ≫ (inputTensorUnit R F).toModuleIso.hom =
      (inputTensorUnit R E).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply PiTensorProduct.ext
  ext x
  change inputTensorUnit R F
      ((PiTensorProduct.map fun i => (m i.1).hom) (PiTensorProduct.tprod R x)) =
    inputTensorUnit R E (PiTensorProduct.tprod R x)
  rw [PiTensorProduct.map_tprod, inputTensorUnit_tprod, inputTensorUnit_tprod]

/-- Splitting off the first coefficient tensor commutes with maps at all
typed positions. This is the recursive naturality API for `tildeInputIso`. -/
theorem inputTensorMap_cons {E F : S → ModuleCat.{u} R} (m : ∀ s, E s ⟶ F s)
    (s : S) (ss : List S) :
    inputTensorMap m (s :: ss) ≫ (inputTensorCons R F s ss).toModuleIso.hom =
      (inputTensorCons R E s ss).toModuleIso.hom ≫
        ModuleCat.ofHom (TensorProduct.map (m s).hom (inputTensorMap m ss).hom) := by
  apply ModuleCat.hom_ext
  apply PiTensorProduct.ext
  ext x
  change inputTensorCons R F s ss
      ((PiTensorProduct.map fun i => (m i.1).hom) (PiTensorProduct.tprod R x)) =
    TensorProduct.map (m s).hom (PiTensorProduct.map fun i => (m i.1).hom)
      (inputTensorCons R E s ss (PiTensorProduct.tprod R x))
  rw [PiTensorProduct.map_tprod, inputTensorCons_tprod, inputTensorCons_tprod,
    TensorProduct.map_tmul, PiTensorProduct.map_tprod]

/-- Naturality of the empty coefficient comparison in the inverse direction. -/
theorem inputTensorMap_nil_inv {E F : S → ModuleCat.{u} R} (m : ∀ s, E s ⟶ F s) :
    (inputTensorUnit R E).toModuleIso.inv ≫ inputTensorMap m [] =
      (inputTensorUnit R F).toModuleIso.inv := by
  apply (cancel_mono (inputTensorUnit R F).toModuleIso.hom).1
  rw [Category.assoc, inputTensorMap_nil, Iso.inv_hom_id, Iso.inv_hom_id]

/-- Naturality of the first-factor coefficient comparison in the inverse direction. -/
theorem inputTensorMap_cons_inv {E F : S → ModuleCat.{u} R}
    (m : ∀ s, E s ⟶ F s) (s : S) (ss : List S) :
    (inputTensorCons R E s ss).toModuleIso.inv ≫ inputTensorMap m (s :: ss) =
      ModuleCat.ofHom (TensorProduct.map (m s).hom (inputTensorMap m ss).hom) ≫
        (inputTensorCons R F s ss).toModuleIso.inv := by
  apply (cancel_mono (inputTensorCons R F s ss).toModuleIso.hom).1
  rw [Category.assoc, inputTensorMap_cons, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual ordered tensor sheaf comparison is natural in the entire
family of coefficient module maps. This includes noninvertible maps. -/
theorem tildeInputIso_naturality {E F : S → ModuleCat.{u} R}
    (m : ∀ s, E s ⟶ F s) (ss : List S) :
    tensorModulesMap (fun s => tilde.map (m s)) ss ≫ (tildeInputIso F ss).hom =
      (tildeInputIso E ss).hom ≫ tilde.map (inputTensorMap m ss) := by
  induction ss with
  | nil =>
    change 𝟙 _ ≫ (tildeSelf.symm ≪≫ (tilde.functor R).mapIso
        (inputTensorUnit R F).symm.toModuleIso).hom =
      (tildeSelf.symm ≪≫ (tilde.functor R).mapIso
        (inputTensorUnit R E).symm.toModuleIso).hom ≫ _
    simp only [Category.id_comp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    change _ = tildeSelf.symm.hom ≫ (tilde.functor R).map
      (inputTensorUnit R E).toModuleIso.inv ≫ (tilde.functor R).map (inputTensorMap m [])
    rw [← Functor.map_comp, inputTensorMap_nil_inv]
    rfl
  | cons s ss ih =>
    change tensorModuleMap (tilde.map (m s)) (tensorModulesMap (fun t => tilde.map (m t)) ss) ≫
      ((tensorModuleIso (Iso.refl _) (tildeInputIso F ss)).hom ≫
        (tildeTensorIso R).hom.app (F s, ModuleCat.of R (InputTensor R F ss)) ≫
        (tilde.functor R).map (inputTensorCons R F s ss).toModuleIso.inv) =
      ((tensorModuleIso (Iso.refl _) (tildeInputIso E ss)).hom ≫
        (tildeTensorIso R).hom.app (E s, ModuleCat.of R (InputTensor R E ss)) ≫
        (tilde.functor R).map (inputTensorCons R E s ss).toModuleIso.inv) ≫ _
    change tensorModuleMap _ _ ≫ (tensorModuleMap (𝟙 _) (tildeInputIso F ss).hom ≫ _) =
      (tensorModuleMap (𝟙 _) (tildeInputIso E ss).hom ≫ _) ≫ _
    rw [← Category.assoc, ← tensorModuleMap_comp, Category.comp_id, ih]
    rw [show tensorModuleMap (tilde.map (m s))
        ((tildeInputIso E ss).hom ≫ tilde.map (inputTensorMap m ss)) =
      tensorModuleMap (𝟙 _) (tildeInputIso E ss).hom ≫
        tensorModuleMap (tilde.map (m s)) (tilde.map (inputTensorMap m ss)) by
          rw [← tensorModuleMap_comp, Category.id_comp]]
    change (tensorModuleMap (𝟙 _) (tildeInputIso E ss).hom ≫
      tensorModuleMap (tilde.map (m s)) (tilde.map (inputTensorMap m ss))) ≫
        (tildeTensorMap R _ _ ≫ _) = _
    rw [Category.assoc, ← Category.assoc (tensorModuleMap (tilde.map (m s)) _) _,
      tildeTensorMap_naturality]
    simp only [Category.assoc]
    change _ = tensorModuleMap (𝟙 _) (tildeInputIso E ss).hom ≫
      tildeTensorMap R _ _ ≫ (tilde.functor R).map
        (inputTensorCons R E s ss).toModuleIso.inv ≫
          (tilde.functor R).map (inputTensorMap m (s :: ss))
    rw [← Functor.map_comp, inputTensorMap_cons_inv]
    rw [Functor.map_comp]
    rfl

/-- Associate a sheaf morphism to a genuine multilinear coefficient
operation, using its universal tensor linearization. -/
def tildeOperation (E : S → ModuleCat.{u} R) (a : Arity S)
    (f : TensorOperation R E a) :
    tensorModules (fun s => tilde (E s)) a.inputs ⟶ tilde (E a.output) :=
  (tildeInputIso E a.inputs).hom ≫ tilde.map (ModuleCat.ofHom (PiTensorProduct.lift f))

/-- The affine operation comparison is bijective by the universal property
of the coefficient tensor and full faithfulness of associated sheaves. -/
def tildeOperationEquiv (E : S → ModuleCat.{u} R) (a : Arity S) :
    TensorOperation R E a ≃
      (tensorModules (fun s => tilde (E s)) a.inputs ⟶ tilde (E a.output)) where
  toFun := tildeOperation E a
  invFun f := PiTensorProduct.lift.symm
    ((tilde.fullyFaithfulFunctor (R := R)).preimage ((tildeInputIso E a.inputs).inv ≫ f)).hom
  left_inv f := by
    apply PiTensorProduct.lift.injective
    simp only [LinearEquiv.apply_symm_apply]
    change ((tilde.fullyFaithfulFunctor (R := R)).preimage
      ((tildeInputIso E a.inputs).inv ≫
        ((tildeInputIso E a.inputs).hom ≫
          (tilde.functor R).map (ModuleCat.ofHom (PiTensorProduct.lift f))))).hom = _
    rw [Iso.inv_hom_id_assoc, Functor.FullyFaithful.preimage_map]
    rfl
  right_inv f := by
    change (tildeInputIso E a.inputs).hom ≫ (tilde.functor R).map
      (ModuleCat.ofHom (PiTensorProduct.lift (PiTensorProduct.lift.symm _))) = f
    rw [LinearEquiv.apply_symm_apply]
    change (tildeInputIso E a.inputs).hom ≫ (tilde.functor R).map
      ((tilde.fullyFaithfulFunctor (R := R)).preimage
        ((tildeInputIso E a.inputs).inv ≫ f)) = f
    rw [Functor.FullyFaithful.map_preimage, Iso.hom_inv_id_assoc]

/-- A coefficient family preserving an actual multilinear operation
preserves its associated-sheaf operation. This API applies to arbitrary
module maps and includes nullary operations. -/
theorem tildeOperation_naturality {E F : S → ModuleCat.{u} R}
    (m : ∀ s, E s ⟶ F s) (a : Arity S)
    (f : TensorOperation R E a) (g : TensorOperation R F a)
    (h : ∀ x, m a.output (f x) = g (fun i => m i.1 (x i))) :
    tildeOperation E a f ≫ tilde.map (m a.output) =
      tensorModulesMap (fun s => tilde.map (m s)) a.inputs ≫ tildeOperation F a g := by
  have linearized : ModuleCat.ofHom (PiTensorProduct.lift f) ≫ m a.output =
      inputTensorMap m a.inputs ≫ ModuleCat.ofHom (PiTensorProduct.lift g) := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    ext x
    change m a.output (PiTensorProduct.lift f (PiTensorProduct.tprod R x)) =
      PiTensorProduct.lift g
        ((PiTensorProduct.map fun i => (m i.1).hom) (PiTensorProduct.tprod R x))
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    exact h x
  change ((tildeInputIso E a.inputs).hom ≫ (tilde.functor R).map _) ≫
      (tilde.functor R).map _ =
    tensorModulesMap _ _ ≫ ((tildeInputIso F a.inputs).hom ≫ (tilde.functor R).map _)
  rw [Category.assoc, ← Functor.map_comp, linearized, Functor.map_comp,
    ← Category.assoc]
  change ((tildeInputIso E a.inputs).hom ≫ tilde.map (inputTensorMap m a.inputs)) ≫ _ = _
  rw [← tildeInputIso_naturality, Category.assoc]

/-- Faithfulness of associated sheaves reflects preservation of the actual
multilinear operation. It supplies fullness for the affine structure functor. -/
theorem tildeOperation_preserves_iff {E F : S → ModuleCat.{u} R}
    (m : ∀ s, E s ⟶ F s) (a : Arity S)
    (f : TensorOperation R E a) (g : TensorOperation R F a) :
    tildeOperation E a f ≫ tilde.map (m a.output) =
        tensorModulesMap (fun s => tilde.map (m s)) a.inputs ≫ tildeOperation F a g ↔
      ∀ x, m a.output (f x) = g (fun i => m i.1 (x i)) := by
  refine ⟨fun h x => ?_, tildeOperation_naturality m a f g⟩
  have linearized : ModuleCat.ofHom (PiTensorProduct.lift f) ≫ m a.output =
      inputTensorMap m a.inputs ≫ ModuleCat.ofHom (PiTensorProduct.lift g) := by
    apply (tilde.functor R).map_injective
    apply (cancel_epi (tildeInputIso E a.inputs).hom).1
    simp only [Functor.map_comp]
    change (tildeInputIso E a.inputs).hom ≫
        (tilde.map (ModuleCat.ofHom (PiTensorProduct.lift f)) ≫ tilde.map (m a.output)) =
      (tildeInputIso E a.inputs).hom ≫
        (tilde.map (inputTensorMap m a.inputs) ≫ tilde.map (ModuleCat.ofHom (PiTensorProduct.lift g)))
    rw [← Category.assoc, ← Category.assoc, ← tildeInputIso_naturality]
    exact h
  have value := congrArg (fun q => q.hom (PiTensorProduct.tprod R x)) linearized
  change m a.output (PiTensorProduct.lift f (PiTensorProduct.tprod R x)) =
    PiTensorProduct.lift g ((PiTensorProduct.map fun i => (m i.1).hom)
      (PiTensorProduct.tprod R x)) at value
  rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod] at value
  exact value

/-- Associated sheaves of a coefficient tensor structure, as in Definition
6.1. Each primitive map comes from the given multilinear operation. -/
@[simps]
def tildeStructure (A : TensorStructure R sig) : SchemeTensorStructure (Spec R) sig where
  carrier s := tilde (A.carrier s)
  total op := tildeOperation A.carrier (sig.totalArity op) (A.total op)
  quantity q := tildeOperation A.carrier (sig.quantityArity q) (A.quantity q)

/-- A structure-preserving coefficient map induces the actual associated
module-sheaf maps on all carriers. -/
@[simps]
def tildeStructureMap {A B : TensorStructure R sig} (f : A ⟶ B) :
    tildeStructure A ⟶ tildeStructure B where
  onSort s := tilde.map (ModuleCat.ofHom (f.onSort s))
  preservesTotal op := tildeOperation_naturality
    (fun s => ModuleCat.ofHom (f.onSort s)) (sig.totalArity op) _ _ (f.preservesTotal op)
  preservesQuantity q := tildeOperation_naturality
    (fun s => ModuleCat.ofHom (f.onSort s)) (sig.quantityArity q) _ _ (f.preservesQuantity q)

/-- The affine primitive-structure functor of Definition 6.1 before
restricting to the separate finite-rank and Law predicates. -/
@[simps]
def tildeStructureFunctor (R : CommRingCat.{u}) (sig : Signature.{u}) :
    TensorStructure R sig ⥤ SchemeTensorStructure (Spec R) sig where
  obj := tildeStructure
  map := tildeStructureMap
  map_id A := by
    apply SchemeTensorStructure.Hom.ext
    intro s
    exact (tilde.functor R).map_id (A.carrier s)
  map_comp f g := by
    apply SchemeTensorStructure.Hom.ext
    intro s
    exact (tilde.functor R).map_comp (ModuleCat.ofHom (f.onSort s))
      (ModuleCat.ofHom (g.onSort s))

/-- Associated sheaves retain precisely all primitive-structure maps.
Fullness follows by reflecting each commuting operation diagram. -/
def tildeStructureFullyFaithful : (tildeStructureFunctor R sig).FullyFaithful where
  preimage {A B} f :=
    { onSort := fun s => ((tilde.fullyFaithfulFunctor (R := R)).preimage (f.onSort s)).hom
      preservesTotal := fun op => (tildeOperation_preserves_iff
        (fun s => (tilde.fullyFaithfulFunctor (R := R)).preimage (f.onSort s))
          (sig.totalArity op) (A.total op) (B.total op)).mp (by
            have maps (s) : tilde.map
                ((tilde.fullyFaithfulFunctor (R := R)).preimage (f.onSort s)) = f.onSort s :=
              (tilde.fullyFaithfulFunctor (R := R)).map_preimage (f.onSort s)
            simp only [maps]
            exact f.preservesTotal op)
      preservesQuantity := fun q => (tildeOperation_preserves_iff
        (fun s => (tilde.fullyFaithfulFunctor (R := R)).preimage (f.onSort s))
          (sig.quantityArity q) (A.quantity q) (B.quantity q)).mp (by
            have maps (s) : tilde.map
                ((tilde.fullyFaithfulFunctor (R := R)).preimage (f.onSort s)) = f.onSort s :=
              (tilde.fullyFaithfulFunctor (R := R)).map_preimage (f.onSort s)
            simp only [maps]
            exact f.preservesQuantity q) }
  map_preimage f := by
    apply SchemeTensorStructure.Hom.ext
    intro s
    exact (tilde.fullyFaithfulFunctor (R := R)).map_preimage (f.onSort s)
  preimage_map f := by
    apply TensorStructure.Hom.ext
    funext s
    exact congrArg ModuleCat.Hom.hom
      ((tilde.fullyFaithfulFunctor (R := R)).preimage_map (ModuleCat.ofHom (f.onSort s)))

/-- Carrier isomorphisms preserving the primitive maps assemble into a
structure isomorphism. Preservation by the inverses follows by cancellation. -/
def SchemeTensorStructure.isoOfCarrierIso {X : Scheme.{u}}
    {A B : SchemeTensorStructure X sig} (e : ∀ s, A.carrier s ≅ B.carrier s)
    (total : ∀ op, A.total op ≫ (e _).hom =
      tensorModulesMap (fun s => (e s).hom) _ ≫ B.total op)
    (quantity : ∀ q, A.quantity q ≫ (e _).hom =
      tensorModulesMap (fun s => (e s).hom) _ ≫ B.quantity q) : A ≅ B where
  hom := ⟨fun s => (e s).hom, total, quantity⟩
  inv :=
    { onSort := fun s => (e s).inv
      preservesTotal := fun op => by
        apply (cancel_mono (e _).hom).1
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
          total, ← Category.assoc, ← tensorModulesMap_comp]
        simp only [Iso.inv_hom_id, tensorModulesMap_id, Category.id_comp]
      preservesQuantity := fun q => by
        apply (cancel_mono (e _).hom).1
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
          quantity, ← Category.assoc, ← tensorModulesMap_comp]
        simp only [Iso.inv_hom_id, tensorModulesMap_id, Category.id_comp] }
  hom_inv_id := SchemeTensorStructure.Hom.ext fun s => (e s).hom_inv_id
  inv_hom_id := SchemeTensorStructure.Hom.ext fun s => (e s).inv_hom_id

/-- Read primitive coefficient operations through arbitrary associated-sheaf
presentations of the carriers. The actual sheaf operations supply all data. -/
@[simps]
def coefficientStructureOfTilde (A : SchemeTensorStructure (Spec R) sig)
    (E : sig.SortType → ModuleCat.{u} R) (e : ∀ s, tilde (E s) ≅ A.carrier s) :
    TensorStructure R sig where
  carrier := E
  total op := (tildeOperationEquiv E (sig.totalArity op)).symm
    (tensorModulesMap (fun s => (e s).hom) _ ≫ A.total op ≫ (e _).inv)
  quantity q := (tildeOperationEquiv E (sig.quantityArity q)).symm
    (tensorModulesMap (fun s => (e s).hom) _ ≫ A.quantity q ≫ (e _).inv)

/-- Re-associating the recovered coefficient operations gives the original
primitive sheaf structure, with precisely the chosen carrier comparisons. -/
def coefficientStructureOfTildeIso (A : SchemeTensorStructure (Spec R) sig)
    (E : sig.SortType → ModuleCat.{u} R) (e : ∀ s, tilde (E s) ≅ A.carrier s) :
    tildeStructure (coefficientStructureOfTilde A E e) ≅ A :=
  SchemeTensorStructure.isoOfCarrierIso e
    (fun op => by
      change (tildeOperationEquiv E (sig.totalArity op))
        ((tildeOperationEquiv E (sig.totalArity op)).symm _) ≫ (e _).hom = _
      rw [Equiv.apply_symm_apply, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id])
    (fun q => by
      change (tildeOperationEquiv E (sig.quantityArity q))
        ((tildeOperationEquiv E (sig.quantityArity q)).symm _) ≫ (e _).hom = _
      rw [Equiv.apply_symm_apply, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id])

/-- Primitive structures with associated-sheaf presentations on every
carrier belong to the essential image of the actual affine structure functor. -/
theorem tildeStructure_essImage (A : SchemeTensorStructure (Spec R) sig)
    (h : ∀ s, (tilde.functor R).essImage (A.carrier s)) :
    (tildeStructureFunctor R sig).essImage A := by
  classical
  choose E hE using h
  let e := fun s => (hE s).some
  exact ⟨coefficientStructureOfTilde A E e, ⟨coefficientStructureOfTildeIso A E e⟩⟩

/-- A presentation on the whole affine open supplies a presentation over
the original coefficient ring, by the canonical spectrum/global-sections
isomorphism. No finite-generation hypothesis enters this comparison. -/
theorem affineModule_tilde_essImage (M : (Spec R).Modules)
    (h : HasTildeOn M (isAffineOpen_top (Spec R))) : (tilde.functor R).essImage M := by
  let X := Spec R
  let topAffine := isAffineOpen_top X
  let e := Scheme.ΓSpecIso R
  have fromSpec : topAffine.fromSpec = Spec.map e.inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have inverse : Spec.map e.hom ≫ topAffine.fromSpec = 𝟙 X := by
    rw [fromSpec, ← Spec.map_comp, e.inv_hom_id, Spec.map_id]
  obtain ⟨N, ⟨k⟩⟩ := h
  refine ⟨(ModuleCat.extendScalars e.hom.hom).obj N, ⟨?_⟩⟩
  exact ((tildeRestrictIso e.hom).app N).symm ≪≫
    (Scheme.Modules.restrictFunctor (Spec.map e.hom)).mapIso k ≪≫
    ((Scheme.Modules.restrictFunctorComp (Spec.map e.hom) topAffine.fromSpec).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr inverse).app M ≪≫
    (Scheme.Modules.restrictFunctorId (X := X)).app M

/-- The canonical coefficient map from an affine spectrum to the section
ring of one of its opens. It is the actual restriction of global sections. -/
def affineOpenCoefficientMap (U : (Spec R).Opens) : R ⟶ Γ(Spec R, U) :=
  (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op

/-- The geometric section map agrees with the canonical scalar action
used by the associated-module sheaf on the open. -/
theorem affineOpenCoefficientMap_eq_algebraMap (U : (Spec R).Opens) :
    (affineOpenCoefficientMap U).hom = algebraMap R Γ(Spec R, U) := by
  rfl

/-- The affine chart inclusion is the spectrum of its actual coefficient
map. This connects the coefficient comparison to the scheme geometry. -/
theorem affineOpenCoefficientMap_fromSpec (U : (Spec R).affineOpens) :
    Spec.map (affineOpenCoefficientMap U.1) = U.property.fromSpec := by
  rw [affineOpenCoefficientMap, Spec.map_comp, ← U.property.fromSpec_toSpecΓ,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- An affine chart presented as the spectrum of an abstract ring map
gives its coefficient-extension presentation. This abstract core keeps
the canonical section-ring map out of adjoint-uniqueness reductions. -/
def affineTildePresentationOfMap (U : (Spec R).affineOpens)
    (a : R ⟶ Γ(Spec R, U.1)) (ha : Spec.map a = U.property.fromSpec)
    (M : ModuleCat.{u} R) :
    tilde ((ModuleCat.extendScalars a.hom).obj M) ≅
      (tilde M).restrict U.property.fromSpec := by
  haveI : IsOpenImmersion (Spec.map a) := by rw [ha]; infer_instance
  exact ((tildeRestrictIso a).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr ha).app (tilde M)

/-- The abstract affine-map presentation identifies coefficient extension
with the actual sections on its affine chart. -/
def affineTildeSectionsIsoOfMap (U : (Spec R).affineOpens)
    (a : R ⟶ Γ(Spec R, U.1)) (ha : Spec.map a = U.property.fromSpec)
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars a.hom).obj M ≅ (tilde M).val.obj (op U.1) :=
  affinePresentationSectionsIso U.property (tilde M) _ (affineTildePresentationOfMap U a ha M)

/-- Restricting an associated sheaf to an arbitrary affine open presents
it by extension along the canonical section-ring map. -/
def affineOpenTildePresentation (U : (Spec R).affineOpens) (M : ModuleCat.{u} R) :
    tilde ((ModuleCat.extendScalars (affineOpenCoefficientMap U.1).hom).obj M) ≅
      (tilde M).restrict U.property.fromSpec :=
  affineTildePresentationOfMap U (affineOpenCoefficientMap U.1)
    (affineOpenCoefficientMap_fromSpec U) M

/-- The coefficient module of a restricted associated sheaf is the actual
module of sections on that affine open, with its section-ring action. -/
def affineOpenTildeSectionsIso (U : (Spec R).affineOpens) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (affineOpenCoefficientMap U.1).hom).obj M ≅
      (tilde M).val.obj (op U.1) :=
  affineTildeSectionsIsoOfMap U (affineOpenCoefficientMap U.1)
    (affineOpenCoefficientMap_fromSpec U) M

/-- The tensor presentation of coefficient extension identifies the actual
sections of an associated sheaf on every affine open. Its coefficient map
is the canonical restriction from the original affine spectrum. -/
def affineOpenTensorSectionsIso (U : (Spec R).affineOpens) (M : ModuleCat.{u} R) :
    ModuleCat.of Γ(Spec R, U.1) (Γ(Spec R, U.1) ⊗[R] M) ≅
      (tilde M).val.obj (op U.1) :=
  (CoefficientDescent.extendScalarsTensorIso (B := Γ(Spec R, U.1)) M).symm ≪≫
    affineOpenTildeSectionsIso U M

/-- Every primitive tensor structure with quasi-coherent carriers on a
spectrum comes from actual multilinear coefficient operations. -/
theorem tildeStructure_essImage_of_quasiCoherent (A : SchemeTensorStructure (Spec R) sig)
    (h : ∀ s, IsQuasiCoherentModule (A.carrier s)) :
    (tildeStructureFunctor R sig).essImage A := by
  apply tildeStructure_essImage
  intro s
  exact affineModule_tilde_essImage (A.carrier s) (h s ⟨⊤, isAffineOpen_top _⟩)

/-- Associated module maps take canonical coefficient sections to the
sections of their actual coefficient images, on every open. -/
theorem tilde_map_toOpen {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (U : (Spec R).Opens) (x : M) :
    (tilde.map f).val.app (op U) (StructureSheaf.toOpenₗ R M U x) =
      StructureSheaf.toOpenₗ R N U (f x) :=
  congr($(tilde.toOpen_map_app f U).hom x)

/-- Restriction of the canonical section of a coefficient element is its
canonical section on the smaller open. -/
theorem tilde_toOpen_restrict (M : ModuleCat.{u} R) {U V : (Spec R).Opens}
    (inside : V ≤ U) (x : M) :
    (tilde M).val.map (homOfLE inside).op (StructureSheaf.toOpenₗ R M U x) =
      StructureSheaf.toOpenₗ R M V x :=
  congr($(tilde.toOpen_res M U V (homOfLE inside)).hom x)

/-- Evaluation of a composite module-sheaf morphism can be performed
without unfolding the particular tensor or associated-sheaf objects. -/
theorem moduleSheaf_comp_apply {X : Scheme.{u}} {M N K : X.Modules}
    (f : M ⟶ N) (g : N ⟶ K) (U : X.Opens) (x : M.val.obj (op U)) :
    (f ≫ g).val.app (op U) x = g.val.app (op U) (f.val.app (op U) x) := rfl

/-- Evaluation of the identity module-sheaf morphism is the identity. -/
theorem moduleSheaf_id_apply {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (op U)) :
    (𝟙 M : M ⟶ M).val.app (op U) x = x := rfl

/-- The affine restriction comparison sends the actual adjunction-unit
section to the coefficient scalar-extension unit. Its normalization is
inherited from the canonical pullback and restriction comparisons. -/
theorem tildeRestrictIso_unit_top {T : CommRingCat.{u}} (a : R ⟶ T)
    [IsOpenImmersion (Spec.map a)] (M : ModuleCat.{u} R) (m : M) :
    ((tildeRestrictIso a).hom.app M).val.app (op ⊤)
      (((Scheme.Modules.restrictAdjunction (Spec.map a)).unit.app (tilde M)).val.app (op ⊤)
        (StructureSheaf.toOpenₗ R M ⊤ m)) =
      StructureSheaf.toOpenₗ T ((ModuleCat.extendScalars a.hom).obj M) ⊤
        ((1 : T) ⊗ₜ[R, a.hom] m) := by
  have unit := congrArg (fun q => q.val.app (op ⊤) (StructureSheaf.toOpenₗ R M ⊤ m))
    (restrictFunctorIsoPullback_unit_eq (Spec.map a) (tilde M))
  change ((Scheme.Modules.restrictFunctorIsoPullback (Spec.map a)).hom.app (tilde M)).val.app (op ⊤)
    (((Scheme.Modules.restrictAdjunction (Spec.map a)).unit.app (tilde M)).val.app (op ⊤)
      (StructureSheaf.toOpenₗ R M ⊤ m)) = _ at unit
  rw [show (tildeRestrictIso a).hom.app M =
      (Scheme.Modules.restrictFunctorIsoPullback (Spec.map a)).hom.app (tilde M) ≫
        (tildePullbackIso a).hom.app M from rfl, moduleSheaf_comp_apply]
  erw [unit]
  exact affineTildePullbackIso_unit_top a M m

/-- An isomorphism normalization determines the corresponding inverse
normalization on actual module-sheaf sections. -/
theorem moduleSheafIso_inv_apply_of_hom {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) (x : M.val.obj (op U)) (y : N.val.obj (op U))
    (h : e.hom.val.app (op U) x = y) : e.inv.val.app (op U) y = x := by
  rw [← h]
  have identity := congrArg (fun q : M ⟶ M => q.val.app (op U) x) e.hom_inv_id
  exact identity

/-- The inverse affine restriction comparison recovers the actual unit
section from a coefficient scalar-extension unit. -/
theorem tildeRestrictIso_inv_unit_top {T : CommRingCat.{u}} (a : R ⟶ T)
    [IsOpenImmersion (Spec.map a)] (M : ModuleCat.{u} R) (m : M) :
    ((tildeRestrictIso a).inv.app M).val.app (op ⊤)
        (StructureSheaf.toOpenₗ T ((ModuleCat.extendScalars a.hom).obj M) ⊤
          ((1 : T) ⊗ₜ[R, a.hom] m)) =
      (((Scheme.Modules.restrictAdjunction (Spec.map a)).unit.app (tilde M)).val.app (op ⊤)
        (StructureSheaf.toOpenₗ R M ⊤ m)) := by
  exact moduleSheafIso_inv_apply_of_hom ((tildeRestrictIso a).app M) ⊤ _ _
    (tildeRestrictIso_unit_top a M m)

/-- Equality transport of an open immersion preserves its actual
restriction-adjunction unit. This eliminates proof-dependent chart transports. -/
theorem restrictFunctorCongr_unit_top {X Y : Scheme.{u}} {f g : Y ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) (M : X.Modules)
    (x : M.val.obj (op ⊤)) :
    ((Scheme.Modules.restrictFunctorCongr h).hom.app M).val.app (op ⊤)
        (((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op ⊤) x) =
      ((Scheme.Modules.restrictAdjunction g).unit.app M).val.app (op ⊤) x := by
  subst g
  let z := ((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op ⊤) x
  change M.presheaf.map (𝟙 _) z = z
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The affine presentation/section comparison evaluates by its three
canonical maps. Keeping the presentation abstract avoids unfolding its
pullback construction when checking primitive operations. -/
theorem affinePresentationSectionsIso_apply {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) (N : ModuleCat.{u} Γ(X, U))
    (e : tilde N ≅ M.restrict hU.fromSpec) (x : N) :
    (affinePresentationSectionsIso hU M N e).hom x =
      (affineModuleSectionsIso hU M).hom
        (e.hom.val.app (op ⊤) (StructureSheaf.toOpenₗ Γ(X, U) N ⊤ x)) := rfl

/-- The affine-presentation section map has its actual restriction-unit
normalization whenever the chosen presentation has that normalization.
This abstract API avoids reducing concrete pullback isomorphisms. -/
theorem affinePresentationSectionsIso_unit_core {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) (N : ModuleCat.{u} Γ(X, U))
    (e : tilde N ≅ M.restrict hU.fromSpec) (x : N) (y : M.val.obj (op ⊤))
    (h : e.hom.val.app (op ⊤) (StructureSheaf.toOpenₗ Γ(X, U) N ⊤ x) =
      (((Scheme.Modules.restrictAdjunction hU.fromSpec).unit.app M).val.app (op ⊤) y)) :
    (affinePresentationSectionsIso hU M N e).hom x =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op y := by
  rw [affinePresentationSectionsIso_apply, h]
  exact affineModuleSectionsIso_restrict_unit hU M y

/-- The coefficient-extension section comparison is normalized on the
actual extension-unit generators. This discharges the carrier comparison
needed for primitive-operation compatibility on every affine open. -/
theorem affineTildeSectionsIsoOfMap_unit (U : (Spec R).affineOpens)
    (a : R ⟶ Γ(Spec R, U.1)) (ha : Spec.map a = U.property.fromSpec)
    (M : ModuleCat.{u} R) (m : M) :
    (affineTildeSectionsIsoOfMap U a ha M).hom
      ((1 : Γ(Spec R, U.1)) ⊗ₜ[R, a.hom] m) =
      StructureSheaf.toOpenₗ R M U.1 m := by
  haveI : IsOpenImmersion (Spec.map a) := by rw [ha]; infer_instance
  apply Eq.trans ?_ (tilde_toOpen_restrict M le_top m)
  apply affinePresentationSectionsIso_unit_core U.property (tilde M) _
    (affineTildePresentationOfMap U a ha M) _ (StructureSheaf.toOpenₗ R M ⊤ m)
  have presented : (affineTildePresentationOfMap U a ha M).hom =
      (tildeRestrictIso a).inv.app M ≫
        (Scheme.Modules.restrictFunctorCongr ha).hom.app (tilde M) := rfl
  rw [presented, moduleSheaf_comp_apply]
  erw [tildeRestrictIso_inv_unit_top a M m]
  exact restrictFunctorCongr_unit_top ha (tilde M) (StructureSheaf.toOpenₗ R M ⊤ m)

/-- The canonical affine section comparison has the extension-unit
normalization inherited from the abstract affine-map comparison. -/
theorem affineOpenTildeSectionsIso_unit (U : (Spec R).affineOpens)
    (M : ModuleCat.{u} R) (m : M) :
    (affineOpenTildeSectionsIso U M).hom
      ((1 : Γ(Spec R, U.1)) ⊗ₜ[R, (affineOpenCoefficientMap U.1).hom] m) =
      StructureSheaf.toOpenₗ R M U.1 m :=
  affineTildeSectionsIsoOfMap_unit U (affineOpenCoefficientMap U.1)
    (affineOpenCoefficientMap_fromSpec U) M m

/-- Inverting one carrier comparison and following another evaluates
by cancellation. This abstract API keeps concrete affine comparison
definitions out of kernel reductions. -/
theorem moduleIso_symm_trans_hom_apply {T : Type u} [Ring T]
    {M N K : ModuleCat.{u} T} (e : M ≅ N) (f : M ≅ K)
    (x : M) (y : N) (h : e.hom x = y) :
    (e.symm ≪≫ f).hom y = f.hom x := by
  change f.hom (e.inv y) = f.hom x
  apply congrArg f.hom
  rw [← h]
  exact congrArg (fun g : M ⟶ M => g x) e.hom_inv_id

/-- In the canonical tensor presentation, the affine section comparison
sends each unit pure tensor to its actual coefficient section. -/
theorem affineOpenTensorSectionsIso_unit (U : (Spec R).affineOpens)
    (M : ModuleCat.{u} R) (m : M) :
    (affineOpenTensorSectionsIso U M).hom ((1 : Γ(Spec R, U.1)) ⊗ₜ[R] m) =
      StructureSheaf.toOpenₗ R M U.1 m := by
  exact (moduleIso_symm_trans_hom_apply
    (CoefficientDescent.extendScalarsTensorIso (B := Γ(Spec R, U.1)) M)
    (affineOpenTildeSectionsIso U M)
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap R Γ(Spec R, U.1))).unit.app M m)
    ((1 : Γ(Spec R, U.1)) ⊗ₜ[R] m)
    (CoefficientDescent.extendScalarsTensorIso_unit (B := Γ(Spec R, U.1)) M m)).trans
      (affineOpenTildeSectionsIso_unit U M m)

/-- The finite affine tensor comparison sends pure sections of coefficient
tuples to the section of their coefficient pure tensor. This normalization
connects the actual sheaf operation to `sectionsStructure`. -/
theorem tildeInputIso_pureTensorSections (E : S → ModuleCat.{u} R) (ss : List S)
    (r : R) (x : ∀ i : TensorPosition ss, E i.1) :
    (tildeInputIso E ss).hom.val.app (op (PrimeSpectrum.basicOpen r))
        (pureTensorSections (fun s => tilde (E s)) (PrimeSpectrum.basicOpen r) ss
          (fun i => StructureSheaf.toOpenₗ R (E i.1) _ (x i))) =
      StructureSheaf.toOpenₗ R (ModuleCat.of R (InputTensor R E ss)) _
        (PiTensorProduct.tprod R x) := by
  induction ss with
  | nil =>
    rw [pureTensorSections_nil]
    change (tilde.map (inputTensorUnit R E).toModuleIso.inv).val.app
      (op (PrimeSpectrum.basicOpen r)) (1 : Γ(Spec R, PrimeSpectrum.basicOpen r)) = _
    have unit : StructureSheaf.toOpenₗ R (ModuleCat.of R R)
        (PrimeSpectrum.basicOpen r) 1 = (1 : Γ(Spec R, PrimeSpectrum.basicOpen r)) :=
      StructureSheaf.const_one _
    rw [← unit, tilde_map_toOpen]
    congr 1
    apply (inputTensorUnit R E).injective
    exact (inputTensorUnit R E).apply_symm_apply 1 |>.trans
      (inputTensorUnit_tprod R E x).symm
  | cons s ss ih =>
    rw [pureTensorSections_cons, tildeInputIso_hom_cons]
    rw [moduleSheaf_comp_apply, moduleSheaf_comp_apply]
    erw [sectionTensorMap_naturality (𝟙 (tilde (E s))) (tildeInputIso E ss).hom
      (PrimeSpectrum.basicOpen r)
      (StructureSheaf.toOpenₗ R (E s) _ (x ⟨s, .here⟩))
      (pureTensorSections (fun t => tilde (E t)) (PrimeSpectrum.basicOpen r) ss
        (fun i => StructureSheaf.toOpenₗ R (E i.1) _ (x ⟨i.1, .there i.2⟩))), ih]
    rw [moduleSheaf_id_apply]
    rw [show (tildeTensorMap R (E s) (ModuleCat.of R (InputTensor R E ss))).val.app
        (op (PrimeSpectrum.basicOpen r))
        (sectionTensorMap _ _ _
          (StructureSheaf.toOpenₗ R (E s) _ (x ⟨s, .here⟩) ⊗ₜ[_]
            StructureSheaf.toOpenₗ R (ModuleCat.of R (InputTensor R E ss)) _
              (PiTensorProduct.tprod R (fun i => x ⟨i.1, .there i.2⟩)))) =
        StructureSheaf.toOpenₗ R (ModuleCat.of R (E s ⊗[R] InputTensor R E ss)) _
          (x ⟨s, .here⟩ ⊗ₜ[R] PiTensorProduct.tprod R (fun i => x ⟨i.1, .there i.2⟩)) from
      tildeTensorMap_toOpen R (E s) (ModuleCat.of R (InputTensor R E ss)) _ _ r]
    rw [tilde_map_toOpen]
    congr 1
    apply (inputTensorCons R E s ss).injective
    exact (inputTensorCons R E s ss).apply_symm_apply _ |>.trans
      (inputTensorCons_tprod R E x).symm

/-- Interpreting an associated-sheaf primitive on coefficient sections
gives exactly the canonical section of its multilinear coefficient value.
This connects the affine operation construction to actual section semantics. -/
theorem tildeOperation_sections (E : S → ModuleCat.{u} R) (a : Arity S)
    (f : TensorOperation R E a) (r : R)
    (x : ∀ i : TensorPosition a.inputs, E i.1) :
    sectionOperation (fun s => tilde (E s)) (PrimeSpectrum.basicOpen r) a
        (tildeOperation E a f)
        (fun i => StructureSheaf.toOpenₗ R (E i.1) _ (x i)) =
      StructureSheaf.toOpenₗ R (E a.output) _ (f x) := by
  rw [sectionOperation_apply]
  change ((tildeInputIso E a.inputs).hom ≫
    tilde.map (ModuleCat.ofHom (PiTensorProduct.lift f))).val.app _ _ = _
  rw [moduleSheaf_comp_apply, tildeInputIso_pureTensorSections, tilde_map_toOpen]
  exact congrArg (StructureSheaf.toOpenₗ R (E a.output) _)
    (PiTensorProduct.lift.tprod (φ := f) x)

/-- The section normalization in particular holds on the top open. This
is the comparison with the original coefficient realization on a spectrum. -/
theorem tildeOperation_sections_top (E : S → ModuleCat.{u} R) (a : Arity S)
    (f : TensorOperation R E a) (x : ∀ i : TensorPosition a.inputs, E i.1) :
    sectionOperation (fun s => tilde (E s)) ⊤ a (tildeOperation E a f)
        (fun i => StructureSheaf.toOpenₗ R (E i.1) ⊤ (x i)) =
      StructureSheaf.toOpenₗ R (E a.output) ⊤ (f x) := by
  have h := tildeOperation_sections E a f (1 : R) x
  erw [PrimeSpectrum.basicOpen_one] at h
  exact h

/-- The normalization of an associated primitive on coefficient sections
holds on every open. The proof uses actual sheaf separatedness and the
basic-open normalization, rather than an affine-presentation assumption. -/
theorem tildeOperation_sections_open (E : S → ModuleCat.{u} R) (a : Arity S)
    (f : TensorOperation R E a) (U : (Spec R).Opens)
    (x : ∀ i : TensorPosition a.inputs, E i.1) :
    sectionOperation (fun s => tilde (E s)) U a (tildeOperation E a f)
        (fun i => StructureSheaf.toOpenₗ R (E i.1) U (x i)) =
      StructureSheaf.toOpenₗ R (E a.output) U (f x) := by
  apply moduleSections_eq_of_locally_eq (tilde (E a.output))
  intro p hp
  obtain ⟨_, ⟨r, rfl⟩, hpr, inside⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨PrimeSpectrum.basicOpen r, inside, hpr, ?_⟩
  erw [sectionOperation_restrict (fun s => tilde (E s)) inside a (tildeOperation E a f)]
  rw [tilde_toOpen_restrict]
  have arguments : (fun i : TensorPosition a.inputs => (tilde (E i.1)).val.map (homOfLE inside).op
      (StructureSheaf.toOpenₗ R (E i.1) U (x i))) =
      fun i => StructureSheaf.toOpenₗ R (E i.1) (PrimeSpectrum.basicOpen r) (x i) :=
    funext fun i => tilde_toOpen_restrict (E i.1) inside (x i)
  erw [arguments]
  exact tildeOperation_sections E a f r x

/-- A comparison of extended multilinear operations is determined by
the unit-coefficient tuples. The module families and comparison maps are
abstract, so concrete sheaf comparisons need not be reduced in this proof. -/
theorem multilinear_extension_preserves_of_units
    (Acoef Bcoef : Type u) [CommRing Acoef] [CommRing Bcoef] [Algebra Acoef Bcoef]
    (E : S → ModuleCat.{u} Acoef) (F : S → ModuleCat.{u} Bcoef)
    (m : ∀ s, extendCarriers Acoef E Bcoef s →ₗ[Bcoef] F s) (a : Arity S)
    (f : TensorOperation Acoef E a) (g : TensorOperation Bcoef F a)
    (h : ∀ x, m a.output ((1 : Bcoef) ⊗ₜ[Acoef] f x) =
      g (fun i => m i.1 ((1 : Bcoef) ⊗ₜ[Acoef] x i)))
    (y : ∀ i : TensorPosition a.inputs, extendCarriers Acoef E Bcoef i.1) :
    m a.output (extendOperation Acoef E Bcoef f y) = g (fun i => m i.1 (y i)) := by
  have equal : (m a.output).compMultilinearMap (extendOperation Acoef E Bcoef f) =
      g.compLinearMap (fun i => m i.1) := by
    apply multilinear_ext_unit Acoef E Bcoef
    intro x
    change m a.output (extendOperation Acoef E Bcoef f
      (fun i => (1 : Bcoef) ⊗ₜ[Acoef] x i)) =
      g (fun i => m i.1 ((1 : Bcoef) ⊗ₜ[Acoef] x i))
    rw [extendOperation_unit]
    exact h x
  exact congrArg (fun operation => operation y) equal

/-- On an arbitrary affine open, the actual carrier scalar-extension
comparisons preserve the full multilinear operation. Equality on all
arguments follows from equality on coefficient-unit generators. -/
theorem affineOpenOperation_preserves (E : S → ModuleCat.{u} R) (a : Arity S)
    (f : TensorOperation R E a) (U : (Spec R).affineOpens)
    (y : ∀ i : TensorPosition a.inputs, extendCarriers R E Γ(Spec R, U.1) i.1) :
    (affineOpenTensorSectionsIso U (E a.output)).hom
        (extendOperation R E Γ(Spec R, U.1) f y) =
      sectionOperation (fun s => tilde (E s)) U.1 a (tildeOperation E a f)
        (fun i => (affineOpenTensorSectionsIso U (E i.1)).hom (y i)) := by
  apply multilinear_extension_preserves_of_units R Γ(Spec R, U.1) E
    (fun s => (tilde (E s)).val.obj (op U.1))
    (fun s => (affineOpenTensorSectionsIso U (E s)).hom.hom) a f
    (sectionOperation (fun s => tilde (E s)) U.1 a (tildeOperation E a f)) ?_ y
  intro x
  change (affineOpenTensorSectionsIso U (E a.output)).hom ((1 : Γ(Spec R, U.1)) ⊗ₜ[R] f x) =
    sectionOperation (fun s => tilde (E s)) U.1 a (tildeOperation E a f)
      (fun i => (affineOpenTensorSectionsIso U (E i.1)).hom
        ((1 : Γ(Spec R, U.1)) ⊗ₜ[R] x i))
  rw [affineOpenTensorSectionsIso_unit U (E a.output) (f x)]
  have arguments : (fun i : TensorPosition a.inputs =>
      (affineOpenTensorSectionsIso U (E i.1)).hom ((1 : Γ(Spec R, U.1)) ⊗ₜ[R] x i)) =
      fun i => StructureSheaf.toOpenₗ R (E i.1) U.1 (x i) :=
    funext fun i => affineOpenTensorSectionsIso_unit U (E i.1) (x i)
  erw [arguments]
  exact (tildeOperation_sections_open E a f U.1 x).symm

/-- The affine comparison on actual section structures, with all primitive
operations and quantities preserved. -/
def affineOpenSectionsStructureMap (A : TensorStructure R sig) (U : (Spec R).affineOpens) :
    extendStructure R Γ(Spec R, U.1) A ⟶ sectionsStructure (tildeStructure A) U.1 where
  onSort s := (affineOpenTensorSectionsIso U (A.carrier s)).hom.hom
  preservesTotal op := affineOpenOperation_preserves A.carrier (sig.totalArity op) (A.total op) U
  preservesQuantity q := affineOpenOperation_preserves A.carrier (sig.quantityArity q) (A.quantity q) U

/-- Abstract module-category carrier isomorphisms assemble into a tensor
structure isomorphism. The abstract core avoids reducing concrete affine
section comparisons when converting isomorphisms to linear equivalences. -/
def tensorStructureIsoOfModuleIso {T : Type u} [CommRing T]
    {A B : TensorStructure T sig} (f : A ⟶ B) (e : ∀ s, A.carrier s ≅ B.carrier s)
    (he : ∀ s, f.onSort s = (e s).hom.hom) : A ≅ B :=
  structureIsoOfCarrierEquiv f (fun s => (e s).toLinearEquiv) he

/-- Coefficient extension to the section ring of an affine open gives
exactly the actual section interpretation of the associated sheaf structure. -/
def affineOpenSectionsStructureIso (A : TensorStructure R sig) (U : (Spec R).affineOpens) :
    extendStructure R Γ(Spec R, U.1) A ≅ sectionsStructure (tildeStructure A) U.1 :=
  tensorStructureIsoOfModuleIso (affineOpenSectionsStructureMap A U)
    (fun s => affineOpenTensorSectionsIso U (A.carrier s))
    (fun _ => rfl)

variable {k : Type u} [CommRing k]

/-- The coefficient map used by the scheme Law semantics is the original
coefficient map followed by actual restriction to the affine open. -/
theorem sectionBaseMap_affine {T : Type u} [CommRing T] (c : k →+* T)
    (U : (Spec (CommRingCat.of T)).Opens) :
    sectionBaseMap (Spec.map (CommRingCat.ofHom c)) U =
      (affineOpenCoefficientMap U).hom.comp c := by
  ext x
  exact congrArg
    (fun f : CommRingCat.of k ⟶ Γ(Spec (CommRingCat.of T), ⊤) =>
      (Spec (CommRingCat.of T)).presheaf.map (homOfLE le_top).op (f x))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c)).symm

/-- Associating sheaves to an affine realization preserves finite local
freeness, the specified stalk ranks, and every written Law. Laws on an
affine open are transported along the actual section-structure comparison. -/
theorem schemeRealizationProperty_tilde (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (c : k →+* R) (A : TensorStructure R sig)
    (h : affineProperty P rank c A) :
    schemeRealizationProperty P rank (Spec.map (CommRingCat.ofHom c)) (tildeStructure A) := by
  refine ⟨fun s => ?_, fun U => ?_⟩
  · exact (affineTilde_finiteLocallyFreeOfRank_iff (A.carrier s) (rank s)).mpr
      ⟨h.1 s, h.2.1 s⟩
  · have extended := affineProperty_baseChange (S := Γ(Spec R, U.1)) P rank c A h
    have onSections := (affineProperty_iff_of_iso P rank
      ((algebraMap R Γ(Spec R, U.1)).comp c) (affineOpenSectionsStructureIso A U)).mp extended
    rw [sectionBaseMap_affine, affineOpenCoefficientMap_eq_algebraMap]
    exact ⟨onSections.2.2.1, onSections.2.2.2⟩

/-- On the whole spectrum the actual coefficient section map is the
canonical inverse of `ΓSpecIso`, including the zero ring. -/
theorem affineOpenCoefficientMap_top :
    affineOpenCoefficientMap (R := R) ⊤ = (Scheme.ΓSpecIso R).inv := by
  change (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (𝟙 (op ⊤)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The associated-sheaf realization property reflects the original
affine realization property. The top-open section structure is scalar
extension along the actual ring isomorphism `ΓSpecIso`. -/
theorem affineProperty_of_schemeRealizationProperty_tilde
    (P : AffineLawPresentation k sig) (rank : sig.SortType → ℕ)
    (c : k →+* R) (A : TensorStructure R sig)
    (h : schemeRealizationProperty P rank (Spec.map (CommRingCat.ofHom c)) (tildeStructure A)) :
    affineProperty P rank c A := by
  let U : (Spec R).affineOpens := ⟨⊤, isAffineOpen_top (Spec R)⟩
  have sections := schemeRealizationProperty_affine h U
  rw [sectionBaseMap_affine, affineOpenCoefficientMap_eq_algebraMap] at sections
  have extended := (affineProperty_iff_of_iso P rank
    ((algebraMap R Γ(Spec R, U.1)).comp c) (affineOpenSectionsStructureIso A U)).mpr sections
  apply affineProperty_of_baseChange_ringEquiv P rank
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv _ c A extended
  rw [← affineOpenCoefficientMap_eq_algebraMap (R := R) ⊤, affineOpenCoefficientMap_top]
  rfl

/-- A primitive sheaf-structure isomorphism gives the actual carrier
module-sheaf isomorphism at every sort. -/
def schemeTensorCarrierIso {X : Scheme.{u}} {A B : SchemeTensorStructure X sig}
    (e : A ≅ B) (s : sig.SortType) : A.carrier s ≅ B.carrier s where
  hom := e.hom.onSort s
  inv := e.inv.onSort s
  hom_inv_id := congrArg (fun f : A ⟶ A => f.onSort s) e.hom_inv_id
  inv_hom_id := congrArg (fun f : B ⟶ B => f.onSort s) e.inv_hom_id

/-- The full geometric realization property is preserved by actual
primitive structure isomorphisms, with its finite-rank and Law components. -/
theorem schemeRealizationProperty_of_iso (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) {X : Scheme.{u}} (b : X ⟶ Spec (CommRingCat.of k))
    {A B : SchemeTensorStructure X sig} (e : A ≅ B)
    (h : schemeRealizationProperty P rank b A) : schemeRealizationProperty P rank b B :=
  ⟨fun s => (h.1 s).ofIso (schemeTensorCarrierIso e s),
    (SatisfiesSchemeLaws.iff_of_iso P b e).mp h.2⟩

/-- The actual associated-sheaf functor restricted to finite-rank affine
realizations and all their structure-preserving maps. -/
def affineSchemeRealizationFunctor (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (c : k →+* R) :
    AffineRealization P rank c ⥤ SchemeRealization P rank (Spec.map (CommRingCat.ofHom c)) where
  obj A := ⟨tildeStructure A.obj, schemeRealizationProperty_tilde P rank c A.obj A.property⟩
  map f := ObjectProperty.homMk (tildeStructureMap f.hom)
  map_id A := ObjectProperty.hom_ext _ ((tildeStructureFunctor R sig).map_id A.obj)
  map_comp f g := ObjectProperty.hom_ext _ ((tildeStructureFunctor R sig).map_comp f.hom g.hom)

/-- The affine realization comparison retains precisely all preserving
maps, by the already proved full faithfulness of the primitive comparison. -/
def affineSchemeRealizationFullyFaithful (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (c : k →+* R) :
    (affineSchemeRealizationFunctor P rank c).FullyFaithful where
  preimage f := ObjectProperty.homMk ((tildeStructureFullyFaithful (R := R) (sig := sig)).preimage f.hom)
  map_preimage f := ObjectProperty.hom_ext _ ((tildeStructureFullyFaithful (R := R) (sig := sig)).map_preimage f.hom)
  preimage_map f := ObjectProperty.hom_ext _ ((tildeStructureFullyFaithful (R := R) (sig := sig)).preimage_map f.hom)

/-- Every geometric realization on a spectrum comes from its affine
coefficient realization, recovering the actual operations and reflecting
the finite-rank and written-Law predicates. -/
theorem affineSchemeRealization_essSurj (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (c : k →+* R) :
    (affineSchemeRealizationFunctor P rank c).EssSurj := by
  refine ⟨fun B => ?_⟩
  obtain ⟨A, ⟨e⟩⟩ := tildeStructure_essImage_of_quasiCoherent (R := R) B.obj
    (fun s => (B.property.1 s).1.quasiCoherent)
  have h := schemeRealizationProperty_of_iso P rank (Spec.map (CommRingCat.ofHom c)) e.symm B.property
  let A' : AffineRealization P rank c :=
    ⟨A, affineProperty_of_schemeRealizationProperty_tilde P rank c A h⟩
  exact ⟨A', ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Affine coefficient realizations and geometric realizations on a spectrum
are equivalent, on all structure-preserving maps (Definition 6.1).
The base map is exactly the spectrum of the input coefficient map. -/
def affineSchemeRealizationEquivalence (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) {R : Type u} [CommRing R] (c : k →+* R) :
    AffineRealization P rank c ≌
      SchemeRealization P rank (Spec.map (CommRingCat.ofHom c)) := by
  let F := affineSchemeRealizationFunctor (R := CommRingCat.of R) P rank c
  letI : F.Full := (affineSchemeRealizationFullyFaithful (R := CommRingCat.of R) P rank c).full
  letI : F.Faithful := (affineSchemeRealizationFullyFaithful (R := CommRingCat.of R) P rank c).faithful
  letI : F.EssSurj := affineSchemeRealization_essSurj (R := CommRingCat.of R) P rank c
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-- The affine comparison uses associated sheaves of the actual
coefficient carriers. This fixes its connection to the tilde API. -/
theorem affineSchemeRealizationEquivalence_carrier
    (P : AffineLawPresentation k sig) (rank : sig.SortType → ℕ)
    {R : Type u} [CommRing R] (c : k →+* R) (A : AffineRealization P rank c)
    (s : sig.SortType) :
    Nonempty ((tilde.functor (CommRingCat.of R)).obj (A.obj.carrier s) ≅
      ((affineSchemeRealizationEquivalence P rank c).functor.obj A).obj.carrier s) := by
  exact ⟨Iso.refl _⟩

end

end SHIGURE.RealizationFamilies
