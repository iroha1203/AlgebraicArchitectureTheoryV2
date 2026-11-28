import Formal.SHIGURE.Part2.Families.SchemeTensorPullback
import Formal.SHIGURE.Part2.Families.AffineSchemeComparison
import Formal.SHIGURE.Part2.Families.SchemeLaws
import Formal.SHIGURE.Part2.Families.SchemeLawLocality
import Formal.SHIGURE.Part2.Families.SchemeLawRestriction
import Formal.SHIGURE.Part2.Schemes.AffinePullbackSections
import Formal.SHIGURE.Part2.Schemes.ModuleTensorComparisons
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Formal.SHIGURE.Part2.Realizations.TensorRestriction
import Formal.SHIGURE.Part2.Schemes.CoreDescent
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Scheme pullback and the realization pseudofunctors

Definition 6.1 and Lemma 6.2 use actual module-sheaf pullback on arbitrary
schemes. The test scheme's map to `Spec k` is part of each fiber object.

## Implementation notes

The all-schemes fiber is a full subcategory of the product of the discrete
base-map category and the primitive sheaf-structure category. Thus arrows
preserve the base map, and pullback composes it with the test morphism.
This keeps the indexing category
`Scheme`, as required by the relative-spectrum-on-a-stack API. Using only
affine test schemes, or taking modules of global sections as carriers,
would not supply these fibers. Equality transport of base maps is kept
explicit in the fixed-base-map unit and composition comparisons.
A sigma category would unnecessarily raise the morphism universe with
the object universe; this product presentation retains the existing
module-sheaf pseudofunctor's morphism universe.

The pullback comparisons use the canonical module-pseudofunctor constraints
on each carrier, and their coherence is inherited componentwise.
-/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite SchemeDescent

noncomputable section

universe u

variable {k : Type u} [CommRing k] {sig : Signature.{u}}
variable {X Y Z : Scheme.{u}}

/-- Primitive structures whose actual carrier sheaves are quasi-coherent.
Implementation notes: this is mathlib's full subcategory of the unchanged
primitive data category. It retains all preserving maps and is the ambient
category on which canonical tensor-pullback comparisons are available. -/
abbrev QuasiCoherentSchemeTensorStructure (X : Scheme.{u}) (sig : Signature.{u}) :=
  ObjectProperty.FullSubcategory
    (fun A : SchemeTensorStructure X sig => ∀ s, IsQuasiCoherentModule (A.carrier s))

/-- API for structure isomorphisms: inverse carrier isomorphisms preserve
an operation whenever the forward isomorphisms preserve it. -/
theorem inverse_preserves_operation {S : Type u} {E F : S → X.Modules}
    (e : ∀ s, E s ≅ F s) (ss : List S) (out : S)
    (a : tensorModules E ss ⟶ E out) (b : tensorModules F ss ⟶ F out)
    (h : a ≫ (e out).hom = tensorModulesMap (fun s => (e s).hom) ss ≫ b) :
    b ≫ (e out).inv = tensorModulesMap (fun s => (e s).inv) ss ≫ a := by
  apply (cancel_mono (e out).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
    ← Category.assoc, ← tensorModulesMap_comp]
  simp only [Iso.inv_hom_id, tensorModulesMap_id, Category.id_comp]

/-- The pullback identity preserves an arbitrary primitive operation.
This API combines finite-tensor identity coherence with naturality. -/
theorem pullbackOperation_id {S : Type u} (E : S → X.Modules)
    (h : ∀ s, IsQuasiCoherentModule (E s)) (ss : List S) (out : S)
    (a : tensorModules E ss ⟶ E out) :
    ((tensorModulesPullbackIso (𝟙 X) E h ss).inv ≫ (Scheme.Modules.pullback (𝟙 X)).map a) ≫
        (Scheme.Modules.pullbackId X).hom.app (E out) =
      tensorModulesMap (fun s => (Scheme.Modules.pullbackId X).hom.app (E s)) ss ≫ a := by
  rw [Category.assoc, (Scheme.Modules.pullbackId X).hom.naturality,
    ← tensorModulesPullbackIso_id E h ss]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  rfl

/-- Iterated pullback and direct pullback preserve the same primitive
operation, using finite-tensor composition coherence. -/
theorem pullbackOperation_comp {S : Type u} (f : Y ⟶ X) (g : Z ⟶ Y)
    (E : S → X.Modules) (h : ∀ s, IsQuasiCoherentModule (E s)) (ss : List S) (out : S)
    (a : tensorModules E ss ⟶ E out) :
    ((tensorModulesPullbackIso g (fun s => (Scheme.Modules.pullback f).obj (E s))
        (fun s => (h s).pullback) ss).inv ≫
      (Scheme.Modules.pullback g).map
        ((tensorModulesPullbackIso f E h ss).inv ≫ (Scheme.Modules.pullback f).map a)) ≫
        (Scheme.Modules.pullbackComp g f).hom.app (E out) =
    tensorModulesMap (fun s => (Scheme.Modules.pullbackComp g f).hom.app (E s)) ss ≫
      ((tensorModulesPullbackIso (g ≫ f) E h ss).inv ≫
        (Scheme.Modules.pullback (g ≫ f)).map a) := by
  apply (cancel_epi ((Scheme.Modules.pullback g).map (tensorModulesPullbackIso f E h ss).hom ≫
    (tensorModulesPullbackIso g (fun s => (Scheme.Modules.pullback f).obj (E s))
      (fun s => (h s).pullback) ss).hom)).1
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback g).map _) ((Scheme.Modules.pullback g).map _) _,
    ← Functor.map_comp, Iso.hom_inv_id, (Scheme.Modules.pullback g).map_id, Category.id_comp]
  trans (Scheme.Modules.pullbackComp g f).hom.app (tensorModules E ss) ≫
    (Scheme.Modules.pullback (g ≫ f)).map a
  · exact (Scheme.Modules.pullbackComp g f).hom.naturality a
  have comparison := congrArg
    (fun q => q ≫ (tensorModulesPullbackIso (g ≫ f) E h ss).inv ≫
      (Scheme.Modules.pullback (g ≫ f)).map a)
    (tensorModulesPullbackIso_comp f g E h ss)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using comparison.symm

/-- Pull back the primitive structure in equation (6.1).
Implementation notes: carrier sheaves are mathlib's actual module
pullbacks. Quasi-coherence supplies the canonical finite-tensor pullback
comparison, and it is preserved by the actual sheaf pullback. -/
@[simps! obj_carrier]
def schemeStructurePullback (f : Y ⟶ X) (A : QuasiCoherentSchemeTensorStructure X sig) :
    QuasiCoherentSchemeTensorStructure Y sig :=
  ⟨{ carrier := fun s => (Scheme.Modules.pullback f).obj (A.obj.carrier s)
     total := fun op =>
       (tensorModulesPullbackIso f A.obj.carrier A.property (sig.totalArity op).inputs).inv ≫
         (Scheme.Modules.pullback f).map (A.obj.total op)
     quantity := fun q =>
       (tensorModulesPullbackIso f A.obj.carrier A.property (sig.quantityArity q).inputs).inv ≫
         (Scheme.Modules.pullback f).map (A.obj.quantity q) },
    fun s => (A.property s).pullback⟩

/-- Pull back every structure-preserving sheaf map, including
noninvertible ones. Implementation notes: the map on each carrier is
the actual map of the module pullback functor. -/
def schemeStructurePullbackMap (f : Y ⟶ X)
    {A B : QuasiCoherentSchemeTensorStructure X sig}
    (m : A ⟶ B) : schemeStructurePullback f A ⟶ schemeStructurePullback f B :=
  ObjectProperty.homMk
    { onSort := fun s => (Scheme.Modules.pullback f).map (m.hom.onSort s)
      preservesTotal := fun op => by
        change ((tensorModulesPullbackIso f A.obj.carrier A.property _).inv ≫
          (Scheme.Modules.pullback f).map _) ≫ (Scheme.Modules.pullback f).map (m.hom.onSort _) =
          _ ≫ ((tensorModulesPullbackIso f B.obj.carrier B.property _).inv ≫
            (Scheme.Modules.pullback f).map _)
        rw [Category.assoc, ← Functor.map_comp, m.hom.preservesTotal, Functor.map_comp]
        rw [← Category.assoc]
        have natural := tensorModulesPullbackIso_naturality f A.property B.property
          m.hom.onSort (sig.totalArity op).inputs
        apply (cancel_epi (tensorModulesPullbackIso f A.obj.carrier A.property _).hom).1
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [← Category.assoc _ (tensorModulesMap _ _) _, ← natural]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      preservesQuantity := fun q => by
        change ((tensorModulesPullbackIso f A.obj.carrier A.property _).inv ≫
          (Scheme.Modules.pullback f).map _) ≫ (Scheme.Modules.pullback f).map (m.hom.onSort _) =
          _ ≫ ((tensorModulesPullbackIso f B.obj.carrier B.property _).inv ≫
            (Scheme.Modules.pullback f).map _)
        rw [Category.assoc, ← Functor.map_comp, m.hom.preservesQuantity, Functor.map_comp]
        rw [← Category.assoc]
        have natural := tensorModulesPullbackIso_naturality f A.property B.property
          m.hom.onSort (sig.quantityArity q).inputs
        apply (cancel_epi (tensorModulesPullbackIso f A.obj.carrier A.property _).hom).1
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [← Category.assoc _ (tensorModulesMap _ _) _, ← natural]
        simp only [Category.assoc, Iso.hom_inv_id_assoc] }

/-- The primitive-structure pullback functor for Definition 6.1.
Implementation notes: the carrier map functor laws are inherited directly
from module pullback; operation-preservation is part of the map above. -/
@[simps]
def schemeStructurePullbackFunctor (f : Y ⟶ X) :
    QuasiCoherentSchemeTensorStructure X sig ⥤ QuasiCoherentSchemeTensorStructure Y sig where
  obj := schemeStructurePullback f
  map := schemeStructurePullbackMap f
  map_id A := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
    (Scheme.Modules.pullback f).map_id (A.obj.carrier s))
  map_comp m n := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
    (Scheme.Modules.pullback f).map_comp (m.hom.onSort s) (n.hom.onSort s))

/-- The primitive QC structure pullback unit is induced by the actual
module-sheaf pullback unit. This is the Law-independent unit API. -/
def schemeStructurePullbackId (X : Scheme.{u}) :
    schemeStructurePullbackFunctor (sig := sig) (𝟙 X) ≅
      𝟭 (QuasiCoherentSchemeTensorStructure X sig) :=
  NatIso.ofComponents (fun A =>
    { hom := ObjectProperty.homMk
        { onSort := fun s => (Scheme.Modules.pullbackId X).hom.app (A.obj.carrier s)
          preservesTotal := fun op => pullbackOperation_id A.obj.carrier A.property _ _ (A.obj.total op)
          preservesQuantity := fun q => pullbackOperation_id A.obj.carrier A.property _ _ (A.obj.quantity q) }
      inv := ObjectProperty.homMk
        { onSort := fun s => (Scheme.Modules.pullbackId X).inv.app (A.obj.carrier s)
          preservesTotal := fun op => inverse_preserves_operation
            (fun s => (Scheme.Modules.pullbackId X).app (A.obj.carrier s)) _ _ _ _
            (pullbackOperation_id A.obj.carrier A.property _ _ (A.obj.total op))
          preservesQuantity := fun q => inverse_preserves_operation
            (fun s => (Scheme.Modules.pullbackId X).app (A.obj.carrier s)) _ _ _ _
            (pullbackOperation_id A.obj.carrier A.property _ _ (A.obj.quantity q)) }
      hom_inv_id := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
        (Scheme.Modules.pullbackId X).hom_inv_id_app (A.obj.carrier s))
      inv_hom_id := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
        (Scheme.Modules.pullbackId X).inv_hom_id_app (A.obj.carrier s)) }) (by
    intro A B m
    apply ObjectProperty.hom_ext
    apply SchemeTensorStructure.Hom.ext
    intro s
    exact (Scheme.Modules.pullbackId X).hom.naturality (m.hom.onSort s))

/-- The primitive QC structure comparison for iterated pullback, before
restricting to any finite rank or written Law property. -/
def schemeStructurePullbackComp (f : Y ⟶ X) (g : Z ⟶ Y) :
    schemeStructurePullbackFunctor (sig := sig) f ⋙ schemeStructurePullbackFunctor g ≅
      schemeStructurePullbackFunctor (g ≫ f) :=
  NatIso.ofComponents (fun A =>
    { hom := ObjectProperty.homMk
        { onSort := fun s => (Scheme.Modules.pullbackComp g f).hom.app (A.obj.carrier s)
          preservesTotal := fun op => pullbackOperation_comp f g A.obj.carrier A.property _ _ (A.obj.total op)
          preservesQuantity := fun q => pullbackOperation_comp f g A.obj.carrier A.property _ _ (A.obj.quantity q) }
      inv := ObjectProperty.homMk
        { onSort := fun s => (Scheme.Modules.pullbackComp g f).inv.app (A.obj.carrier s)
          preservesTotal := fun op => inverse_preserves_operation
            (fun s => (Scheme.Modules.pullbackComp g f).app (A.obj.carrier s)) _ _ _ _
            (pullbackOperation_comp f g A.obj.carrier A.property _ _ (A.obj.total op))
          preservesQuantity := fun q => inverse_preserves_operation
            (fun s => (Scheme.Modules.pullbackComp g f).app (A.obj.carrier s)) _ _ _ _
            (pullbackOperation_comp f g A.obj.carrier A.property _ _ (A.obj.quantity q)) }
      hom_inv_id := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
        (Scheme.Modules.pullbackComp g f).hom_inv_id_app (A.obj.carrier s))
      inv_hom_id := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
        (Scheme.Modules.pullbackComp g f).inv_hom_id_app (A.obj.carrier s)) }) (by
    intro A B m
    apply ObjectProperty.hom_ext
    apply SchemeTensorStructure.Hom.ext
    intro s
    exact (Scheme.Modules.pullbackComp g f).hom.naturality (m.hom.onSort s))

/-- The unit comparison on each carrier is exactly mathlib's canonical
module pullback unit, fixing the normalization of the structure unit. -/
theorem schemeStructurePullbackId_onSort (A : QuasiCoherentSchemeTensorStructure X sig)
    (s : sig.SortType) :
    ((schemeStructurePullbackId X).hom.app A).hom.onSort s =
      (Scheme.Modules.pullbackId X).hom.app (A.obj.carrier s) := by
  rfl

/-- The composition comparison on each carrier is exactly the canonical
module pullback composition comparison. -/
theorem schemeStructurePullbackComp_onSort (f : Y ⟶ X) (g : Z ⟶ Y)
    (A : QuasiCoherentSchemeTensorStructure X sig) (s : sig.SortType) :
    ((schemeStructurePullbackComp f g).hom.app A).hom.onSort s =
      (Scheme.Modules.pullbackComp g f).hom.app (A.obj.carrier s) := by
  rfl

open scoped TensorProduct

/-- A carrier comparison normalized on the actual pullback unit lifts to
the section structures, because every primitive operation is multilinear. -/
def schemeStructurePullbackSectionsIsoOfNormalizedEquiv (f : Y ⟶ X)
    (A : QuasiCoherentSchemeTensorStructure X sig) (U : X.affineOpens) (V : Y.affineOpens)
    (inside : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
    ∀ (e : ∀ s, (Γ(Y, V.1) ⊗[Γ(X, U.1)] (A.obj.carrier s).val.obj (op U.1)) ≃ₗ[Γ(Y, V.1)]
        ((Scheme.Modules.pullback f).obj (A.obj.carrier s)).val.obj (op V.1))
      (_unit : ∀ s (x : (A.obj.carrier s).val.obj (op U.1)),
        e s ((1 : Γ(Y, V.1)) ⊗ₜ[Γ(X, U.1)] x) =
          pullbackSection f (A.obj.carrier s) U.1 V.1 inside x),
      TensorRealization.extendStructure Γ(X, U.1) Γ(Y, V.1) (sectionsStructure A.obj U.1) ≅
        sectionsStructure (schemeStructurePullback f A).obj V.1 := by
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
  intro e unit
  exact TensorRealization.structureIsoOfCarrierEquiv
    { onSort := fun s => (e s).toLinearMap
      preservesTotal := fun q => sectionOperation_baseChange_of_normalized_equiv f A.obj.carrier
        A.property U.1 V.1 inside (sig.totalArity q) (A.obj.total q) e unit
      preservesQuantity := fun q => sectionOperation_baseChange_of_normalized_equiv f A.obj.carrier
        A.property U.1 V.1 inside (sig.quantityArity q) (A.obj.quantity q) e unit }
    e (fun _ => rfl)

/-- The gluing step for Law pullback: actual affine section comparisons
reduce the assertion to coefficient extension on a principal refinement
of each source affine open. -/
theorem satisfiesSchemeLaws_pullback_of_affineSectionsIso
    {P : AffineLawPresentation k sig} {b : X ⟶ Spec (CommRingCat.of k)}
    {A : QuasiCoherentSchemeTensorStructure X sig}
    (h : SatisfiesSchemeLaws P b A.obj) (f : Y ⟶ X)
    (comparison : ∀ (U : X.affineOpens) (V : Y.affineOpens) (inside : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
      TensorRealization.extendStructure Γ(X, U.1) Γ(Y, V.1) (sectionsStructure A.obj U.1) ≅
        sectionsStructure (schemeStructurePullback f A).obj V.1) :
    SatisfiesSchemeLaws P (f ≫ b) (schemeStructurePullback f A).obj := by
  intro W
  let I := {r : Γ(Y, W.1) // ∃ U : X.affineOpens, Y.basicOpen r ≤ f ⁻¹ᵁ U.1}
  let r : I → Γ(Y, W.1) := fun i => i.val
  have range : Set.range r = {r : Γ(Y, W.1) | ∃ U : X.affineOpens, Y.basicOpen r ≤ f ⁻¹ᵁ U.1} := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact i.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have covers : Ideal.span (Set.range r) = ⊤ := by
    rw [range]
    exact affinePullbackPrincipalCoefficients_span f W
  apply schemeLaws_on_affine_of_principal_cover P (f ≫ b) (schemeStructurePullback f A).obj
    (schemeStructurePullback f A).property W r covers
  intro i
  obtain ⟨U, inside⟩ := i.property
  let V : Y.affineOpens := ⟨Y.basicOpen i.val, W.property.basicOpen i.val⟩
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
  let e := comparison U V inside
  have coefficients : (algebraMap Γ(X, U.1) Γ(Y, V.1)).comp (sectionBaseMap b U.1) =
      sectionBaseMap (f ≫ b) V.1 := sectionBaseMap_appLE f b inside
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have extended := TensorRealization.tensorLaw_holds_baseChange (R := Γ(Y, V.1)) (h.tensor U j)
    rw [tensorLaw_mapScalars_comp, coefficients] at extended
    exact (TensorLaw.holds_iff_of_iso _ e).mp extended
  · have extended := (P.polynomialLaw j).holds_baseChange (S := Γ(Y, V.1))
      (sectionBaseMap b U.1) (sectionsStructure A.obj U.1) (h.polynomial U j)
    rw [coefficients] at extended
    exact ((P.polynomialLaw j).holds_iff_of_iso _ e).mp extended

/-- The actual affine-section comparison for primitive structure
pullback. Its carrier maps are the normalized module-sheaf comparisons. -/
def schemeStructurePullbackSectionsIso (f : Y ⟶ X)
    (A : QuasiCoherentSchemeTensorStructure X sig) (U : X.affineOpens) (V : Y.affineOpens)
    (inside : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
    TensorRealization.extendStructure Γ(X, U.1) Γ(Y, V.1) (sectionsStructure A.obj U.1) ≅
      sectionsStructure (schemeStructurePullback f A).obj V.1 := by
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
  apply schemeStructurePullbackSectionsIsoOfNormalizedEquiv f A U V inside
    (fun s => affinePullbackSectionsEquiv f (A.obj.carrier s) (A.property s) U V inside)
  intro s x
  exact affinePullbackSectionsEquiv_unit f (A.obj.carrier s) (A.property s) U V inside x

/-- Written tensor and universal polynomial Laws in Definition 6.1 are
preserved by pullback along every scheme morphism, without flatness. -/
theorem SatisfiesSchemeLaws.pullback {P : AffineLawPresentation k sig}
    {b : X ⟶ Spec (CommRingCat.of k)} {A : QuasiCoherentSchemeTensorStructure X sig}
    (h : SatisfiesSchemeLaws P b A.obj) (f : Y ⟶ X) :
    SatisfiesSchemeLaws P (f ≫ b) (schemeStructurePullback f A).obj := by
  apply satisfiesSchemeLaws_pullback_of_affineSectionsIso h f
  intro U V inside
  exact schemeStructurePullbackSectionsIso f A U V inside

/-- The affine-open Law semantics agrees with testing the actual
pulled-back realization after every test-scheme morphism, as required by
Definition 6.1. The polynomial clause retains its universal scalar tests. -/
theorem satisfiesSchemeLaws_iff_all_test_schemes (P : AffineLawPresentation k sig)
    (b : X ⟶ Spec (CommRingCat.of k)) (A : QuasiCoherentSchemeTensorStructure X sig) :
    SatisfiesSchemeLaws P b A.obj ↔
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X) (U : Y.affineOpens),
        (∀ i, ((P.tensorLaw i).mapScalars (sectionBaseMap (f ≫ b) U.1)).holds
          (sectionsStructure (schemeStructurePullback f A).obj U.1)) ∧
        (∀ i, (P.polynomialLaw i).Holds (sectionBaseMap (f ≫ b) U.1)
          (sectionsStructure (schemeStructurePullback f A).obj U.1)) := by
  constructor
  · intro h Y f U
    exact h.pullback f U
  · intro h
    have identityLaws : SatisfiesSchemeLaws P ((𝟙 X) ≫ b)
        (schemeStructurePullback (𝟙 X) A).obj := h X (𝟙 X)
    rw [Category.id_comp] at identityLaws
    exact (SatisfiesSchemeLaws.iff_of_iso P b
      ((ObjectProperty.ι (fun B : SchemeTensorStructure X sig =>
        ∀ s, IsQuasiCoherentModule (B.carrier s))).mapIso
          ((schemeStructurePullbackId X).app A))).mp identityLaws

/-- Changing a base-map expression by equality preserves the full
realization category. Implementation notes: this transports only an
equality of the actual scheme maps, not an additional geometric premise. -/
def schemeRealizationBaseMapCongr (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) {b c : X ⟶ Spec (CommRingCat.of k)} (h : b = c) :
    SchemeRealization P rank b ≌ SchemeRealization P rank c := by
  subst c
  exact CategoryTheory.Equivalence.refl

/-- Equality transport of the coefficient base map retains the actual
primitive data and every underlying structure-preserving morphism. -/
def schemeRealizationBaseMapCongrForgetIso (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) {b c : X ⟶ Spec (CommRingCat.of k)} (h : b = c) :
    (schemeRealizationBaseMapCongr P rank h).functor ⋙
        (schemeRealizationProperty P rank c).ι ≅
      (schemeRealizationProperty P rank b).ι := by
  subst c
  exact Iso.refl _

/-- A realization's finite locally free carriers discharge the ambient
quasi-coherence condition. Implementation notes: this is the actual
full-subcategory inclusion with the existing FLF-to-QC theorem applied. -/
@[simps]
def schemeRealizationToQuasiCoherent (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (b : X ⟶ Spec (CommRingCat.of k)) :
    SchemeRealization P rank b ⥤ QuasiCoherentSchemeTensorStructure X sig where
  obj A := ⟨A.obj, fun s => (A.property.1 s).1.quasiCoherent⟩
  map m := ObjectProperty.homMk m.hom
  map_id _ := ObjectProperty.hom_ext _ rfl
  map_comp _ _ := ObjectProperty.hom_ext _ rfl

/-- Pullback on fixed-base-map realization categories in Definition 6.1.
Implementation notes: this is a restriction of actual structure pullback;
rank preservation uses the existing geometric rank theorem. -/
@[simps]
def schemeRealizationPullback (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (b : X ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ X) :
    SchemeRealization P rank b ⥤ SchemeRealization P rank (f ≫ b) where
  obj A := ⟨(schemeStructurePullback f ((schemeRealizationToQuasiCoherent P rank b).obj A)).obj,
    ⟨fun s => (A.property.1 s).pullback,
      SatisfiesSchemeLaws.pullback
        (A := (schemeRealizationToQuasiCoherent P rank b).obj A) A.property.2 f⟩⟩
  map m := ObjectProperty.homMk
    (schemeStructurePullbackMap f ((schemeRealizationToQuasiCoherent P rank b).map m)).hom
  map_id A := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
    (Scheme.Modules.pullback f).map_id (A.obj.carrier s))
  map_comp m n := ObjectProperty.hom_ext _ (SchemeTensorStructure.Hom.ext fun s =>
    (Scheme.Modules.pullback f).map_comp (m.hom.onSort s) (n.hom.onSort s))

/-- The unit comparison for realization pullback, with the base-map
identity transported by the category identity law. -/
def schemeRealizationPullbackId (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (b : X ⟶ Spec (CommRingCat.of k)) :
    schemeRealizationPullback P rank b (𝟙 X) ⋙
        (schemeRealizationBaseMapCongr P rank (Category.id_comp b)).functor ≅
      𝟭 (SchemeRealization P rank b) := by
  apply ((schemeRealizationProperty P rank b).fullyFaithfulι.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerLeft (schemeRealizationPullback P rank b (𝟙 X))
      (schemeRealizationBaseMapCongrForgetIso P rank (Category.id_comp b)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (schemeRealizationToQuasiCoherent P rank b) (schemeStructurePullbackId X))
      (ObjectProperty.ι (fun A : SchemeTensorStructure X sig =>
        ∀ s, IsQuasiCoherentModule (A.carrier s)))


/-- The composition comparison identifies iterated and direct actual
sheaf pullback, with the associativity transport of the base map. -/
def schemeRealizationPullbackComp (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (b : X ⟶ Spec (CommRingCat.of k))
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (schemeRealizationPullback P rank b f ⋙
        schemeRealizationPullback P rank (f ≫ b) g) ⋙
        (schemeRealizationBaseMapCongr P rank (Category.assoc g f b).symm).functor ≅
      schemeRealizationPullback P rank b (g ≫ f) := by
  apply ((schemeRealizationProperty P rank ((g ≫ f) ≫ b)).fullyFaithfulι.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerLeft
      (schemeRealizationPullback P rank b f ⋙ schemeRealizationPullback P rank (f ≫ b) g)
      (schemeRealizationBaseMapCongrForgetIso P rank (Category.assoc g f b).symm) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (schemeRealizationToQuasiCoherent P rank b) (schemeStructurePullbackComp f g))
      (ObjectProperty.ι (fun A : SchemeTensorStructure Z sig =>
        ∀ s, IsQuasiCoherentModule (A.carrier s)))


/-- Realizations over all `k`-structures of a fixed test scheme.
Implementation notes: the product with a discrete base-map category
retains precisely the actual sheaf maps in a common fixed-base-map fiber,
and preserves the module-sheaf category's morphism universe. -/
abbrev allSchemeRealizations (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun A : Discrete (X ⟶ Spec (CommRingCat.of k)) × SchemeTensorStructure X sig =>
      schemeRealizationProperty P rank A.1.as A.2)

/-- Forget a realization and its base map to the ambient QC primitive
structure. Implementation notes: every quasi-coherence premise is
generated by the existing finite locally free carrier theorem. -/
@[simps]
def allSchemeToQuasiCoherent (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (X : Scheme.{u}) :
    allSchemeRealizations P rank X ⥤ QuasiCoherentSchemeTensorStructure X sig where
  obj A := ⟨A.obj.2, fun s => (A.property.1 s).1.quasiCoherent⟩
  map m := ObjectProperty.homMk m.hom.2
  map_id _ := ObjectProperty.hom_ext _ rfl
  map_comp _ _ := ObjectProperty.hom_ext _ rfl

/-- Precomposition is the actual pullback of a test scheme's `k`-structure.
Implementation notes: the discrete category enforces equality of base
maps on every morphism. -/
def schemeBaseMapsPullback (f : Y ⟶ X) :
    Discrete (X ⟶ Spec (CommRingCat.of k)) ⥤
      Discrete (Y ⟶ Spec (CommRingCat.of k)) :=
  Discrete.functor fun b => Discrete.mk (f ≫ b)

/-- The all-schemes arrow action retains the actual composite base map.
Implementation notes: the product action pulls back the base map and
primitive sheaf data, and the property is preserved by geometric pullback. -/
def allSchemeRealizationPullback (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (f : Y ⟶ X) :
    allSchemeRealizations P rank X ⥤ allSchemeRealizations P rank Y where
  obj A := ⟨(Discrete.mk (f ≫ A.obj.1.as),
    (schemeStructurePullback f ((allSchemeToQuasiCoherent P rank X).obj A)).obj),
    ⟨fun s => (A.property.1 s).pullback,
      SatisfiesSchemeLaws.pullback
        (A := (allSchemeToQuasiCoherent P rank X).obj A) A.property.2 f⟩⟩
  map m := ObjectProperty.homMk
    ((schemeBaseMapsPullback f).map m.hom.1,
      (schemeStructurePullbackMap f ((allSchemeToQuasiCoherent P rank X).map m)).hom)
  map_id A := ObjectProperty.hom_ext _ (Prod.ext
    ((schemeBaseMapsPullback f).map_id A.obj.1)
    (SchemeTensorStructure.Hom.ext fun s =>
      (Scheme.Modules.pullback f).map_id (A.obj.2.carrier s)))
  map_comp m n := ObjectProperty.hom_ext _ (Prod.ext
    ((schemeBaseMapsPullback f).map_comp m.hom.1 n.hom.1)
    (SchemeTensorStructure.Hom.ext fun s =>
      (Scheme.Modules.pullback f).map_comp (m.hom.2.onSort s) (n.hom.2.onSort s)))

/-- Forget to the actual quasi-coherent carrier at one sort.
Implementation notes: finite local freeness discharges quasi-coherence,
and every underlying map is the original module-sheaf map. No universe
lifting is necessary for this connection to the existing module fiber. -/
@[simps]
def allSchemeCarrierFunctor (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (X : Scheme.{u}) (s : sig.SortType) :
    allSchemeRealizations P rank X ⥤
      quasiCoherentModulesPseudofunctor.obj (.mk (op X)) where
  obj A := ⟨A.obj.2.carrier s, (A.property.1 s).1.quasiCoherent⟩
  map m := ObjectProperty.homMk (m.hom.2.onSort s)
  map_id _ := ObjectProperty.hom_ext _ rfl
  map_comp _ _ := ObjectProperty.hom_ext _ rfl

/-- The carrier forgetful functor commutes with the actual module-sheaf
pullback. Both sides retain the same sheaf and the same maps. -/
def allSchemeCarrierPullbackIso (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (f : Y ⟶ X) (s : sig.SortType) :
    allSchemeRealizationPullback P rank f ⋙ allSchemeCarrierFunctor P rank Y s ≅
      allSchemeCarrierFunctor P rank X s ⋙
        (quasiCoherentModulesPseudofunctor.map f.op.toLoc).toFunctor :=
  NatIso.ofComponents (fun A => ObjectProperty.isoMk _ (Iso.refl _)) (by
    intro A B m
    apply ObjectProperty.hom_ext
    change (Scheme.Modules.pullback f).map (m.hom.2.onSort s) ≫ 𝟙 _ =
      𝟙 _ ≫ (Scheme.Modules.pullback f).map (m.hom.2.onSort s)
    simp)

/-- The all-schemes pullback unit includes the identity base-map equality. -/
def allSchemeRealizationPullbackId (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (X : Scheme.{u}) :
    allSchemeRealizationPullback P rank (𝟙 X) ≅ 𝟭 (allSchemeRealizations P rank X) := by
  refine NatIso.ofComponents (fun A => ObjectProperty.isoMk _
    (Iso.prod (eqToIso (congrArg Discrete.mk (Category.id_comp A.obj.1.as)))
      ((ObjectProperty.ι (fun B : SchemeTensorStructure X sig =>
          ∀ s, IsQuasiCoherentModule (B.carrier s))).mapIso
        ((schemeStructurePullbackId X).app ((allSchemeToQuasiCoherent P rank X).obj A))))) ?_
  intro A B m
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · apply SchemeTensorStructure.Hom.ext
    intro s
    exact (Scheme.Modules.pullbackId X).hom.naturality (m.hom.2.onSort s)


/-- Iterated pullback agrees with direct pullback on both the realization
and its actual map to `Spec k`. -/
def allSchemeRealizationPullbackComp (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (f : Y ⟶ X) (g : Z ⟶ Y) :
    allSchemeRealizationPullback P rank f ⋙ allSchemeRealizationPullback P rank g ≅
      allSchemeRealizationPullback P rank (g ≫ f) := by
  refine NatIso.ofComponents (fun A => ObjectProperty.isoMk _
    (Iso.prod (eqToIso (congrArg Discrete.mk (Category.assoc g f A.obj.1.as).symm))
      ((ObjectProperty.ι (fun B : SchemeTensorStructure Z sig =>
          ∀ s, IsQuasiCoherentModule (B.carrier s))).mapIso
        ((schemeStructurePullbackComp f g).app ((allSchemeToQuasiCoherent P rank X).obj A))))) ?_
  intro A B m
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · apply SchemeTensorStructure.Hom.ext
    intro s
    exact (Scheme.Modules.pullbackComp g f).hom.naturality (m.hom.2.onSort s)


/-- The pseudofunctor of actual realizations and all structure-preserving
maps over all test schemes, including each object's `k`-structure. -/
def schemeRealizationsPseudofunctor (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u,u+1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (allSchemeRealizations P rank X.unop))
    (fun f => (allSchemeRealizationPullback P rank f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk (allSchemeRealizationPullbackId P rank X.unop))
    (fun f g => Cat.Hom.isoMk (allSchemeRealizationPullbackComp P rank f.unop g.unop).symm)
    ?_ ?_ ?_
  · intro W X Y Z f g h
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      Cat.associator_hom_app, Cat.eqToHom_app]
    apply ObjectProperty.hom_ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply SchemeTensorStructure.Hom.ext
      intro s
      have coherence := congrArg (fun η => η.app (A.obj.2.carrier s))
        (Scheme.Modules.pseudofunctor_associativity h.unop g.unop f.unop)
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, eqToHom_app] using coherence
  · intro X Y f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_app, Cat.eqToHom_app]
    apply ObjectProperty.hom_ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply SchemeTensorStructure.Hom.ext
      intro s
      have coherence := congrArg (fun η => η.app (A.obj.2.carrier s))
        (Scheme.Modules.pseudofunctor_left_unitality f.unop)
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
        eqToHom_app] using coherence
  · intro X Y f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.rightUnitor_hom_app, Cat.eqToHom_app]
    apply ObjectProperty.hom_ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply SchemeTensorStructure.Hom.ext
      intro s
      have coherence := congrArg (fun η => η.app (A.obj.2.carrier s))
        (Scheme.Modules.pseudofunctor_right_unitality f.unop)
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
        eqToHom_app] using coherence

/-- The maximal subgroupoid pseudofunctor `Real_n` of Definition 6.1,
on all schemes with the base map retained in its fiber objects. -/
def schemeRealizationCorePseudofunctor (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u,u+1} :=
  corePseudofunctor (schemeRealizationsPseudofunctor P rank)

end

end SHIGURE.RealizationFamilies
