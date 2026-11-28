import Formal.SHIGURE.Part2.Families.SchemeLawLocality
import Formal.SHIGURE.Part2.Families.AffineLawCoefficientComparison
import Formal.SHIGURE.Part2.Families.SchemeTensorPullback

/-! # Scalar extension on principal-open sections

Quasi-coherent carrier sections localize on principal opens. Their actual
restriction maps supply the normalized scalar-extension comparison.
-/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SchemeDescent TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {X : Scheme.{u}} {sig : Signature.{u}}

/-- Principal opens of a source affine chart that map into individual
target affine charts cover the entire source chart. Their defining
coefficients therefore generate the unit ideal. -/
theorem affinePullbackPrincipalCoefficients_span {Y : Scheme.{u}} (f : Y ⟶ X)
    (W : Y.affineOpens) :
    Ideal.span {r : Γ(Y, W.1) | ∃ U : X.affineOpens, Y.basicOpen r ≤ f ⁻¹ᵁ U.1} = ⊤ := by
  apply W.property.self_le_iSup_basicOpen_iff.mp
  intro y hyW
  obtain ⟨U, hfy⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ (f y)))
  obtain ⟨r, inside, hyr⟩ := W.property.exists_basicOpen_le
    (V := f ⁻¹ᵁ U.1) ⟨y, hfy⟩ hyW
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, ⟨U, inside⟩⟩, hyr⟩

/-- A section is pulled to a smaller source open by the actual module
pullback-adjunction unit, followed by actual sheaf restriction. -/
def pullbackSection {Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (inside : V ≤ f ⁻¹ᵁ U) (x : M.val.obj (op U)) :
    ((Scheme.Modules.pullback f).obj M).val.obj (op V) :=
  ((Scheme.Modules.pullback f).obj M).val.map (homOfLE inside).op
    ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)) x)

/-- The canonical binary tensor-pullback comparison takes the unit image
of a pure tensor section to the pure tensor of the unit-image sections. -/
theorem pullbackTensorMap_sectionTensorMap_unit {Y : Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) (U : X.Opens) (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    (pullbackTensorMap f M N).val.app (op (f ⁻¹ᵁ U))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (tensorModule M N)).val.app (op U)) (sectionTensorMap M N U (x ⊗ₜ[Γ(X, U)] y))) =
      sectionTensorMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
        (f ⁻¹ᵁ U)
        (((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)) x) ⊗ₜ[
          Γ(Y, f ⁻¹ᵁ U)]
          ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op U)) y)) := by
  let q := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackTensorMap f M N)
  have natural := tensorModuleHomEquiv_comp (𝟙 (tensorModule M N)) q
  rw [Category.id_comp] at natural
  have comparison := congrArg (fun m => m.app (op U) (x ⊗ₜ[Γ(X, U)] y)) natural
  have normalized := pullbackTensorMap_homEquiv_app_tmul f M N (op U) x y
  have composed := comparison.symm.trans normalized
  change q.val.app (op U) (sectionTensorMap M N U (x ⊗ₜ[Γ(X, U)] y)) = _ at composed
  dsimp only [q] at composed
  rw [Adjunction.homEquiv_unit] at composed
  exact composed

/-- The normalized ordered tensor-pullback comparison maps the unit
image of a pure section tuple to the tuple of its pulled-back sections.
This includes the empty input context. -/
theorem tensorModulesPullbackIso_pureTensorSections_unit {Y : Scheme.{u}}
    {S : Type u} (f : Y ⟶ X) (E : S → X.Modules)
    (hE : ∀ s, IsQuasiCoherentModule (E s)) (U : X.Opens) (ss : List S)
    (x : ∀ i : TensorPosition ss, (E i.1).val.obj (op U)) :
    (tensorModulesPullbackIso f E hE ss).hom.val.app (op (f ⁻¹ᵁ U))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (tensorModules E ss)).val.app (op U)) (pureTensorSections E U ss x)) =
      pureTensorSections (fun s => (Scheme.Modules.pullback f).obj (E s)) (f ⁻¹ᵁ U) ss
        (fun i => (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (E i.1)).val.app
          (op U)) (x i)) := by
  induction ss with
  | nil =>
    rw [pureTensorSections_nil, pureTensorSections_nil]
    have normalized := unitModulePullbackIso_homEquiv f
    rw [Adjunction.homEquiv_unit] at normalized
    have evaluated := congrArg (fun m => m.val.app (op U) (1 : Γ(X, U))) normalized
    change (unitModulePullbackIso f).hom.val.app (op (f ⁻¹ᵁ U))
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (unitModule X)).val.app (op U))
        (1 : Γ(X, U))) =
      (f.app U) (1 : Γ(X, U)) at evaluated
    exact evaluated.trans (map_one (f.app U).hom)
  | cons s ss ih =>
    rw [pureTensorSections_cons, pureTensorSections_cons]
    change (tensorModuleMap (𝟙 _) (tensorModulesPullbackIso f E hE ss).hom).val.app
      (op (f ⁻¹ᵁ U)) ((pullbackTensorMap f (E s) (tensorModules E ss)).val.app
        (op (f ⁻¹ᵁ U)) ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (tensorModule (E s) (tensorModules E ss))).val.app (op U))
          (sectionTensorMap (E s) (tensorModules E ss) U
            (x ⟨s, .here⟩ ⊗ₜ[Γ(X, U)] pureTensorSections E U ss
              (fun i => x ⟨i.1, .there i.2⟩))))) = _
    rw [pullbackTensorMap_sectionTensorMap_unit, sectionTensorMap_naturality, ih]
    rfl

/-- Actual section pullback preserves every primitive operation defined
using the canonical ordered tensor-pullback comparison. -/
theorem sectionOperation_pullback {Y : Scheme.{u}} {S : Type u} (f : Y ⟶ X)
    (E : S → X.Modules) (hE : ∀ s, IsQuasiCoherentModule (E s))
    (U : X.Opens) (V : Y.Opens) (inside : V ≤ f ⁻¹ᵁ U)
    (a : Arity S) (q : tensorModules E a.inputs ⟶ E a.output)
    (x : ∀ i : TensorPosition a.inputs, (E i.1).val.obj (op U)) :
    pullbackSection f (E a.output) U V inside (sectionOperation E U a q x) =
      sectionOperation (fun s => (Scheme.Modules.pullback f).obj (E s)) V a
        ((tensorModulesPullbackIso f E hE a.inputs).inv ≫ (Scheme.Modules.pullback f).map q)
        (fun i => pullbackSection f (E i.1) U V inside (x i)) := by
  let d := tensorModulesPullbackIso f E hE a.inputs
  let q' := d.inv ≫ (Scheme.Modules.pullback f).map q
  have normalized := tensorModulesPullbackIso_pureTensorSections_unit f E hE U a.inputs x
  have natural := congrArg (fun m => m.val.app (op U) (pureTensorSections E U a.inputs x))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality q)
  have original :
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (E a.output)).val.app (op U))
          (sectionOperation E U a q x) =
        sectionOperation (fun s => (Scheme.Modules.pullback f).obj (E s)) (f ⁻¹ᵁ U) a q'
          (fun i => (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (E i.1)).val.app
            (op U)) (x i)) := by
    change _ = ((Scheme.Modules.pullback f).map q).val.app (op (f ⁻¹ᵁ U))
      (d.inv.val.app (op (f ⁻¹ᵁ U)) _)
    rw [← normalized]
    have inverse := congrArg (fun m => m.val.app (op (f ⁻¹ᵁ U))
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (tensorModules E a.inputs)).val.app (op U)) (pureTensorSections E U a.inputs x)))
      d.hom_inv_id
    exact natural.trans
      (congrArg (((Scheme.Modules.pullback f).map q).val.app (op (f ⁻¹ᵁ U))) inverse).symm
  change ((Scheme.Modules.pullback f).obj (E a.output)).val.map (homOfLE inside).op _ = _
  rw [original]
  exact sectionOperation_restrict (fun s => (Scheme.Modules.pullback f).obj (E s)) inside a q'
    (fun i => (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (E i.1)).val.app
      (op U)) (x i))

/-- A scalar-extension equivalence normalized by the actual pullback
unit preserves the entire multilinear primitive operation, since its
values on unit-coefficient input tuples determine the extended map. -/
theorem sectionOperation_baseChange_of_normalized_equiv {Y : Scheme.{u}} {S : Type u}
    (f : Y ⟶ X) (E : S → X.Modules) (hE : ∀ s, IsQuasiCoherentModule (E s))
    (U : X.Opens) (V : Y.Opens) (inside : V ≤ f ⁻¹ᵁ U)
    (a : Arity S) (q : tensorModules E a.inputs ⟶ E a.output) :
    letI : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V inside).hom.toAlgebra
    ∀ (e : ∀ s, (Γ(Y, V) ⊗[Γ(X, U)] (E s).val.obj (op U)) ≃ₗ[Γ(Y, V)]
        ((Scheme.Modules.pullback f).obj (E s)).val.obj (op V))
      (_unit : ∀ s (x : (E s).val.obj (op U)),
        e s ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] x) = pullbackSection f (E s) U V inside x)
      (x : ∀ i : TensorPosition a.inputs, Γ(Y, V) ⊗[Γ(X, U)] (E i.1).val.obj (op U)),
      e a.output (extendOperation Γ(X, U) (fun s => (E s).val.obj (op U)) Γ(Y, V)
          (sectionOperation E U a q) x) =
        sectionOperation (fun s => (Scheme.Modules.pullback f).obj (E s)) V a
          ((tensorModulesPullbackIso f E hE a.inputs).inv ≫ (Scheme.Modules.pullback f).map q)
          (fun i => e i.1 (x i)) := by
  letI : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V inside).hom.toAlgebra
  intro e unit x
  have equal : (e a.output).toLinearMap.compMultilinearMap
        (extendOperation Γ(X, U) (fun s => (E s).val.obj (op U)) Γ(Y, V)
          (sectionOperation E U a q)) =
      (sectionOperation (fun s => (Scheme.Modules.pullback f).obj (E s)) V a
        ((tensorModulesPullbackIso f E hE a.inputs).inv ≫ (Scheme.Modules.pullback f).map q)).compLinearMap
        (fun i => (e i.1).toLinearMap) := by
    apply multilinear_ext_unit Γ(X, U) (fun s => (E s).val.obj (op U)) Γ(Y, V)
    intro y
    change e a.output (extendOperation Γ(X, U) (fun s => (E s).val.obj (op U)) Γ(Y, V)
      (sectionOperation E U a q) (fun i => (1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] y i)) = _
    rw [extendOperation_unit, unit]
    change pullbackSection f (E a.output) U V inside (sectionOperation E U a q y) =
      sectionOperation (fun s => (Scheme.Modules.pullback f).obj (E s)) V a
        ((tensorModulesPullbackIso f E hE a.inputs).inv ≫ (Scheme.Modules.pullback f).map q)
        (fun i => e i.1 ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] y i))
    simp only [unit]
    exact sectionOperation_pullback f E hE U V inside a q y
  exact MultilinearMap.congr_fun equal x

/-- A Law tested over any actual principal localization also holds over
the canonical localization, by the unique localization-ring comparison. -/
theorem TensorLaw.holds_canonicalLocalization_of_actual
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (law : TensorLaw R sig) (A : TensorStructure R sig)
    (h : (law.mapScalars (algebraMap R S)).holds (extendStructure R S A)) :
    (law.mapScalars (algebraMap R (Localization.Away r))).holds
      (extendStructure R (Localization.Away r) A) := by
  let T := Localization.Away r
  let e : T ≃ₐ[R] S := IsLocalization.algEquiv (Submonoid.powers r) T S
  letI : Algebra T S := e.toRingHom.toAlgebra
  letI : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
  apply (TensorLaw.holds_iff_baseChange_ringEquiv e.toRingEquiv rfl
    (law.mapScalars (algebraMap R T)) (extendStructure R T A)).mp
  rw [tensorLaw_mapScalars_comp, ← IsScalarTower.algebraMap_eq R T S]
  exact (TensorLaw.holds_iff_of_iso _
    (structureScalarTower (k := R) (R := T) (S := S) A)).mpr h

/-- Universal polynomial Laws are transported from an actual principal
localization to the canonical one without choosing bases. -/
theorem PolynomialLaw.holds_canonicalLocalization_of_actual
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] {ss : List sig.SortType} {s : sig.SortType}
    (law : PolynomialLaw k sig ss s) (c : k →+* R) (A : TensorStructure R sig)
    (h : law.Holds ((algebraMap R S).comp c) (extendStructure R S A)) :
    law.Holds ((algebraMap R (Localization.Away r)).comp c)
      (extendStructure R (Localization.Away r) A) := by
  let T := Localization.Away r
  let e : T ≃ₐ[R] S := IsLocalization.algEquiv (Submonoid.powers r) T S
  letI : Algebra T S := e.toRingHom.toAlgebra
  letI : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
  apply (PolynomialLaw.holds_iff_baseChange_ringEquiv e.toRingEquiv rfl law
    ((algebraMap R T).comp c) (extendStructure R T A)).mp
  have same : (algebraMap T S).comp ((algebraMap R T).comp c) = (algebraMap R S).comp c :=
    RingHom.ext fun a => (IsScalarTower.algebraMap_apply R T S (c a)).symm
  rw [same]
  exact (law.holds_iff_of_iso _ (structureScalarTower (k := R) (R := T) (S := S) A)).mpr h

/-- Principal-open restriction of a quasi-coherent carrier is actual
scalar extension of its affine section module. -/
def principalCarrierSectionsEquiv (M : X.Modules) (hM : IsQuasiCoherentModule M)
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    (Γ(X, X.basicOpen r) ⊗[Γ(X, U.1)] M.val.obj (op U.1)) ≃ₗ[Γ(X, X.basicOpen r)]
      M.val.obj (op (X.basicOpen r)) := by
  let V := X.basicOpen r
  let a := X.presheaf.map (homOfLE (X.basicOpen_le r)).op
  letI : Algebra Γ(X, U.1) Γ(X, V) := a.hom.toAlgebra
  let N := (ModuleCat.restrictScalars a.hom).obj (M.val.obj (op V))
  letI : Module Γ(X, V) N := (M.val.obj (op V)).isModule
  letI : IsScalarTower Γ(X, U.1) Γ(X, V) N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsLocalization.Away r Γ(X, V) := U.property.isLocalization_basicOpen r
  let f : M.val.obj (op U.1) →ₗ[Γ(X, U.1)] N :=
    (M.val.map (homOfLE (X.basicOpen_le r)).op).hom
  letI : IsLocalizedModule (Submonoid.powers r) f := affineSections_localize U.property M (hM U) r
  exact (IsLocalizedModule.isBaseChange (Submonoid.powers r) Γ(X, V) f).equiv

/-- The principal-section comparison takes a unit coefficient tensor to
the original restriction map of the carrier sheaf. -/
theorem principalCarrierSectionsEquiv_unit (M : X.Modules) (hM : IsQuasiCoherentModule M)
    (U : X.affineOpens) (r : Γ(X, U.1)) (x : M.val.obj (op U.1)) :
    letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    principalCarrierSectionsEquiv M hM U r ((1 : Γ(X, X.basicOpen r)) ⊗ₜ[Γ(X, U.1)] x) =
      M.val.map (homOfLE (X.basicOpen_le r)).op x := by
  change (1 : Γ(X, X.basicOpen r)) • (M.val.map (homOfLE (X.basicOpen_le r)).op x) = _
  exact one_smul _ _

/-- Principal-open scalar extension preserves the actual finite-arity sheaf operation. -/
private theorem principalSectionsOperation {S : Type u} (E : S → X.Modules)
    (hE : ∀ s, IsQuasiCoherentModule (E s)) (U : X.affineOpens) (r : Γ(X, U.1))
    (a : Arity S) (f : tensorModules E a.inputs ⟶ E a.output) :
    letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    ∀ x : (i : TensorPosition a.inputs) →
      Γ(X, X.basicOpen r) ⊗[Γ(X, U.1)] (E i.1).val.obj (op U.1),
      principalCarrierSectionsEquiv (E a.output) (hE _) U r
          (extendOperation Γ(X, U.1) (fun s => (E s).val.obj (op U.1))
            Γ(X, X.basicOpen r) (sectionOperation E U.1 a f) x) =
        sectionOperation E (X.basicOpen r) a f
          (fun i => principalCarrierSectionsEquiv (E i.1) (hE _) U r (x i)) := by
  letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  have equal :
      (principalCarrierSectionsEquiv (E a.output) (hE _) U r).toLinearMap.compMultilinearMap
          (extendOperation Γ(X, U.1) (fun s => (E s).val.obj (op U.1))
            Γ(X, X.basicOpen r) (sectionOperation E U.1 a f)) =
        (sectionOperation E (X.basicOpen r) a f).compLinearMap
          (fun i => (principalCarrierSectionsEquiv (E i.1) (hE _) U r).toLinearMap) := by
    apply multilinear_ext_unit Γ(X, U.1) (fun s => (E s).val.obj (op U.1)) Γ(X, X.basicOpen r)
    intro y
    change principalCarrierSectionsEquiv (E a.output) (hE _) U r
        (extendOperation Γ(X, U.1) (fun s => (E s).val.obj (op U.1)) Γ(X, X.basicOpen r)
          (sectionOperation E U.1 a f) (fun i => (1 : Γ(X, X.basicOpen r)) ⊗ₜ[Γ(X, U.1)] y i)) = _
    rw [extendOperation_unit, principalCarrierSectionsEquiv_unit]
    change (E a.output).val.map (homOfLE (X.basicOpen_le r)).op
      (sectionOperation E U.1 a f y) = sectionOperation E (X.basicOpen r) a f
        (fun i => principalCarrierSectionsEquiv (E i.1) (hE _) U r
          ((1 : Γ(X, X.basicOpen r)) ⊗ₜ[Γ(X, U.1)] y i))
    simp only [principalCarrierSectionsEquiv_unit]
    exact sectionOperation_restrict E (X.basicOpen_le r) a f y
  exact fun x => MultilinearMap.congr_fun equal x

/-- All primitive operations on a principal open are scalar extensions
of their affine-section interpretations, with the original restriction
map as the comparison on unit tensors. -/
def principalSectionsStructureIso (A : SchemeTensorStructure X sig)
    (hA : ∀ s, IsQuasiCoherentModule (A.carrier s))
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    extendStructure Γ(X, U.1) Γ(X, X.basicOpen r) (sectionsStructure A U.1) ≅
      sectionsStructure A (X.basicOpen r) := by
  letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  exact structureIsoOfCarrierEquiv
    { onSort := fun s => (principalCarrierSectionsEquiv (A.carrier s) (hA s) U r).toLinearMap
      preservesTotal := fun f => principalSectionsOperation A.carrier hA U r
        (sig.totalArity f) (A.total f)
      preservesQuantity := fun q => principalSectionsOperation A.carrier hA U r
        (sig.quantityArity q) (A.quantity q) }
    (fun s => principalCarrierSectionsEquiv (A.carrier s) (hA s) U r) (fun _ => rfl)

/-- Written tensor and universal polynomial Laws on a quasi-coherent
affine section structure are detected on any principal cover of that
affine open, using the actual smaller-open section structures. -/
theorem schemeLaws_on_affine_of_principal_cover
    {k ι : Type u} [CommRing k] (P : AffineLawPresentation k sig)
    (b : X ⟶ Spec (CommRingCat.of k)) (A : SchemeTensorStructure X sig)
    (hA : ∀ s, IsQuasiCoherentModule (A.carrier s)) (U : X.affineOpens)
    (r : ι → Γ(X, U.1)) (covers : Ideal.span (Set.range r) = ⊤)
    (h : ∀ i,
      (∀ j, ((P.tensorLaw j).mapScalars (sectionBaseMap b (X.basicOpen (r i)))).holds
        (sectionsStructure A (X.basicOpen (r i)))) ∧
      (∀ j, (P.polynomialLaw j).Holds (sectionBaseMap b (X.basicOpen (r i)))
        (sectionsStructure A (X.basicOpen (r i))))) :
    (∀ j, ((P.tensorLaw j).mapScalars (sectionBaseMap b U.1)).holds
      (sectionsStructure A U.1)) ∧
    (∀ j, (P.polynomialLaw j).Holds (sectionBaseMap b U.1) (sectionsStructure A U.1)) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · apply TensorLaw.holds_of_principal_cover _ _ r covers
    intro i
    let V := X.basicOpen (r i)
    letI : Algebra Γ(X, U.1) Γ(X, V) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le (r i))).op).hom.toAlgebra
    letI : IsLocalization.Away (r i) Γ(X, V) := U.property.isLocalization_basicOpen (r i)
    apply TensorLaw.holds_canonicalLocalization_of_actual (S := Γ(X, V)) (r i)
    apply (TensorLaw.holds_iff_of_iso _ (principalSectionsStructureIso A hA U (r i))).mpr
    have coefficients : (algebraMap Γ(X, U.1) Γ(X, V)).comp (sectionBaseMap b U.1) =
        sectionBaseMap b V := sectionBaseMap_restrict b (X.basicOpen_le (r i))
    rw [tensorLaw_mapScalars_comp, coefficients]
    exact (h i).1 j
  · apply (P.polynomialLaw j).holds_of_principal_cover _ _ r covers
    intro i
    let V := X.basicOpen (r i)
    letI : Algebra Γ(X, U.1) Γ(X, V) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le (r i))).op).hom.toAlgebra
    letI : IsLocalization.Away (r i) Γ(X, V) := U.property.isLocalization_basicOpen (r i)
    apply (P.polynomialLaw j).holds_canonicalLocalization_of_actual (S := Γ(X, V)) (r i)
    apply ((P.polynomialLaw j).holds_iff_of_iso _ (principalSectionsStructureIso A hA U (r i))).mpr
    have coefficients : (algebraMap Γ(X, U.1) Γ(X, V)).comp (sectionBaseMap b U.1) =
        sectionBaseMap b V := sectionBaseMap_restrict b (X.basicOpen_le (r i))
    rw [coefficients]
    exact (h i).2 j

end

end SHIGURE.RealizationFamilies
