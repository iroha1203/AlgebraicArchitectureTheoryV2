import Formal.SHIGURE.Part2.Families.SchemeLaws
import Formal.SHIGURE.Part2.Schemes.TensorPullback
import Formal.SHIGURE.Part2.Descent.ExpressionNaturality
import Formal.SHIGURE.Part2.Tensor.CoefficientPoints

/-! # Local evaluation of written Laws on actual module-sheaf sections

Polynomial term evaluation commutes with the semilinear restriction maps
of the carrier sheaves. Consequently equality of term values can be
checked locally on the underlying scheme. This concerns the original
section values; universal scalar tests remain part of `PolynomialLaw.Holds`.
-/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SchemeDescent TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {sig : Signature.{u}}

/-- The coefficient map on source sections is the actual extension of
the target coefficient map along the scheme morphism's section map. -/
theorem sectionBaseMap_appLE {Y : Scheme.{u}} (f : Y ⟶ X)
    (b : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} {V : Y.Opens}
    (inside : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V inside).hom.comp (sectionBaseMap b U) = sectionBaseMap (f ≫ b) V := by
  ext r
  exact congrArg (fun m : Γ(X, ⊤) ⟶ Γ(Y, V) =>
    m (b.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)))
    (f.map_appLE inside (homOfLE (show U ≤ ⊤ from le_top)).op)

/-- A principal cover detects a zero coefficient-module element, even
when each open requires a different power of its defining coefficient. -/
theorem coefficient_eq_zero_of_powers_cover {R M ι : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (r : ι → R)
    (covers : Ideal.span (Set.range r) = ⊤) (m : M)
    (vanishes : ∀ i, ∃ n : ℕ, r i ^ n • m = 0) : m = 0 := by
  let I : Ideal R := (Submodule.span R ({m} : Set M)).annihilator
  have inside : Ideal.span (Set.range r) ≤ I.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := vanishes i
    exact ⟨n, (Submodule.mem_annihilator_span_singleton m _).mpr hn⟩
  have radicalTop : I.radical = ⊤ := top_le_iff.mp (covers ▸ inside)
  have idealTop : I = ⊤ := Ideal.radical_eq_top.mp radicalTop
  have oneMem : (1 : R) ∈ I := idealTop ▸ trivial
  simpa only [one_smul] using (Submodule.mem_annihilator_span_singleton m 1).mp oneMem

/-- Localized coefficient-module maps on a principal cover jointly
detect zero. No finiteness, flatness or freeness of the module is needed. -/
theorem coefficient_eq_zero_of_localizations {R M ι : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (r : ι → R)
    (covers : Ideal.span (Set.range r) = ⊤) (N : ι → Type u)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (r i)) (f i)]
    (m : M) (vanishes : ∀ i, f i m = 0) : m = 0 := by
  apply coefficient_eq_zero_of_powers_cover r covers m
  intro i
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (r i)) (f i)).mp
    (vanishes i)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.val (r i)).mp s.property
  exact ⟨n, by simpa only [hn, Submonoid.smul_def] using hs⟩

/-- The coefficients defining a principal cover continue to generate
the unit ideal after every scalar test of a polynomial Law. -/
theorem coefficient_cover_map {R S ι : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (r : ι → R) (covers : Ideal.span (Set.range r) = ⊤) :
    Ideal.span (Set.range (fun i => g (r i))) = ⊤ := by
  have sameRange : Set.range (fun i => g (r i)) = g '' Set.range r := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨r i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [sameRange, ← Ideal.map_span, covers, Ideal.map_top]

/-- Every sort of a tensor-structure isomorphism is an actual linear
equivalence, using the inverse structure morphism. -/
def tensorStructureIsoOnSort {R : Type u} [CommRing R]
    {A B : TensorStructure R sig} (e : A ≅ B) (s : sig.SortType) :
    A.carrier s ≃ₗ[R] B.carrier s :=
  LinearEquiv.ofLinear (e.hom.onSort s) (e.inv.onSort s)
    (congrArg (fun m : B ⟶ B => m.onSort s) e.inv_hom_id)
    (congrArg (fun m : A ⟶ A => m.onSort s) e.hom_inv_id)

/-- Written tensor Law equality is invariant under actual structure
isomorphisms. The proof uses naturality for all typed tensor shapes. -/
theorem TensorLaw.holds_iff_of_iso {R : Type u} [CommRing R]
    (law : TensorLaw R sig) {A B : TensorStructure R sig} (e : A ≅ B) :
    law.holds A ↔ law.holds B := by
  have transport {A B : TensorStructure R sig} (e : A ≅ B)
      (h : law.holds A) : law.holds B := by
    have comparison (T : TensorShape sig.SortType) :
        T.mapSorts e.hom.onSort = (T.equivSorts (tensorStructureIsoOnSort e)).toLinearMap :=
      (TensorShape.equivSorts_toLinearMap (tensorStructureIsoOnSort e) T).symm
    apply (LinearMap.cancel_right
      (g := (law.source.equivSorts (tensorStructureIsoOnSort e)).toLinearMap)
      (law.source.equivSorts (tensorStructureIsoOnSort e)).surjective).1
    rw [← comparison law.source, ← law.left.eval_natural e.hom,
      ← law.right.eval_natural e.hom, h]
  exact ⟨transport e, transport e.symm⟩

/-- Tensor Law equality is detected after scalar extension to the
members of a principal cover, for every written input and output shape. -/
theorem TensorLaw.holds_of_principal_cover {R ι : Type u} [CommRing R]
    (law : TensorLaw R sig) (A : TensorStructure R sig) (r : ι → R)
    (covers : Ideal.span (Set.range r) = ⊤)
    (h : ∀ i, (law.mapScalars (algebraMap R (Localization.Away (r i)))).holds
      (extendStructure R (Localization.Away (r i)) A)) : law.holds A := by
  apply LinearMap.ext
  intro z
  apply sub_eq_zero.mp
  apply coefficient_eq_zero_of_localizations r covers
    (fun i => Localization.Away (r i) ⊗[R] law.target.module A)
    (fun i => TensorProduct.mk R (Localization.Away (r i)) (law.target.module A) 1)
  intro i
  let S := Localization.Away (r i)
  have equal := h i
  change (law.left.mapScalars (algebraMap R S)).eval (extendStructure R S A) =
    (law.right.mapScalars (algebraMap R S)).eval (extendStructure R S A) at equal
  rw [eval_mapScalars_eq_extendShapeMap, eval_mapScalars_eq_extendShapeMap] at equal
  have evaluated := LinearMap.congr_fun equal
    (shapeBaseChange A law.source ((1 : S) ⊗ₜ[R] z))
  rw [extendShapeMap_unit, extendShapeMap_unit] at evaluated
  have native := (shapeBaseChange (R := S) A law.target).injective evaluated
  change (1 : S) ⊗ₜ[R] (_ - _) = 0
  rw [TensorProduct.tmul_sub, native, sub_self]

/-- The sectionwise tensor comparison is natural in both actual module
sheaf maps. Its proof uses the universal property of sheafification. -/
theorem sectionTensorMap_naturality
    {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') (U : X.Opens)
    (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    (tensorModuleMap f g).val.app (op U)
        (sectionTensorMap M N U (x ⊗ₜ[Γ(X, U)] y)) =
      sectionTensorMap M' N' U
        (f.val.app (op U) x ⊗ₜ[Γ(X, U)] g.val.app (op U) y) := by
  have h := tensorModuleHomEquiv_map_comp f g (𝟙 (tensorModule M' N'))
  rw [Category.comp_id] at h
  have h' := tensorModuleHomEquiv_comp (𝟙 (tensorModule M N)) (tensorModuleMap f g)
  rw [Category.id_comp] at h'
  have equal := h'.symm.trans h
  exact congrArg (fun m => m.app (op U) (x ⊗ₜ[Γ(X, U)] y)) equal

/-- Pure tensor sections commute with every family of actual carrier
sheaf maps, including repeated sorts and the empty input list. -/
theorem pureTensorSections_naturality {S : Type u} {E F : S → X.Modules}
    (m : ∀ s, E s ⟶ F s) (U : X.Opens) (ss : List S)
    (x : ∀ i : TensorPosition ss, (E i.1).val.obj (op U)) :
    (tensorModulesMap m ss).val.app (op U) (pureTensorSections E U ss x) =
      pureTensorSections F U ss (fun i => (m i.1).val.app (op U) (x i)) := by
  induction ss with
  | nil => rw [pureTensorSections_nil, pureTensorSections_nil]; rfl
  | cons s ss ih =>
    rw [pureTensorSections_cons, pureTensorSections_cons]
    change (tensorModuleMap (m s) (tensorModulesMap m ss)).val.app (op U) _ = _
    rw [sectionTensorMap_naturality, ih]

/-- A structure-preserving sheaf map acts on actual sections and
preserves their multilinear primitive operations. -/
def sectionsStructureMap {A B : SchemeTensorStructure X sig} (m : A ⟶ B) (U : X.Opens) :
    sectionsStructure A U ⟶ sectionsStructure B U where
  onSort s := ((m.onSort s).val.app (op U)).hom
  preservesTotal f x := by
    change (m.onSort _).val.app (op U)
      ((A.total f).val.app (op U) (pureTensorSections A.carrier U _ x)) = _
    have h := congrArg (fun q => q.val.app (op U) (pureTensorSections A.carrier U _ x))
      (m.preservesTotal f)
    exact h.trans (congrArg ((B.total f).val.app (op U))
      (pureTensorSections_naturality m.onSort U _ x))
  preservesQuantity q x := by
    change (m.onSort _).val.app (op U)
      ((A.quantity q).val.app (op U) (pureTensorSections A.carrier U _ x)) = _
    have h := congrArg (fun q => q.val.app (op U) (pureTensorSections A.carrier U _ x))
      (m.preservesQuantity q)
    exact h.trans (congrArg ((B.quantity q).val.app (op U))
      (pureTensorSections_naturality m.onSort U _ x))

/-- Reading a fixed open's sections is functorial on all preserving
sheaf maps. In particular it transports actual sheaf isomorphisms. -/
def sectionsStructureFunctor (U : X.Opens) :
    SchemeTensorStructure X sig ⥤ TensorStructure Γ(X, U) sig where
  obj A := sectionsStructure A U
  map m := sectionsStructureMap m U
  map_id _ := TensorStructure.Hom.ext (funext fun _ => rfl)
  map_comp _ _ := TensorStructure.Hom.ext (funext fun _ => rfl)

/-- Universal polynomial Law semantics includes the original coefficient
module, via the canonical scalar-unit isomorphism. -/
theorem PolynomialLaw.eval_eq_of_holds {R : Type u} [CommRing R]
    {ss : List sig.SortType} {s : sig.SortType}
    (l : PolynomialLaw k sig ss s) (c : k →+* R) (A : TensorStructure R sig)
    (h : l.Holds c A) (x : ∀ i : TensorPosition ss, A.carrier i.1) :
    l.left.eval c A x = l.right.eval c A x := by
  let e := structureScalarUnit A
  let y (i : TensorPosition ss) := e.inv.onSort i.1 (x i)
  have recovered : (fun i : TensorPosition ss => e.hom.onSort i.1 (y i)) = x :=
    funext fun i => congrArg (fun m : A ⟶ A => m.onSort i.1 (x i)) e.inv_hom_id
  have equal := h R y
  have scalars : (algebraMap R R).comp c = c := RingHom.id_comp c
  rw [scalars] at equal
  have mapped := congrArg (e.hom.onSort s) equal
  rw [PolynomialTerm.eval_map, PolynomialTerm.eval_map, recovered] at mapped
  exact mapped

/-- Polynomial term evaluation on unit tensors is the unit tensor of
the original value, including scalar literals from the written base ring. -/
theorem PolynomialTerm.eval_unit {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (c : k →+* R) (A : TensorStructure R sig)
    {ss : List sig.SortType} {s : sig.SortType}
    (x : ∀ i : TensorPosition ss, A.carrier i.1) (t : PolynomialTerm k sig ss s) :
    t.eval ((algebraMap R S).comp c) (extendStructure R S A)
        (fun i => (1 : S) ⊗ₜ[R] x i) = (1 : S) ⊗ₜ[R] t.eval c A x := by
  induction t with
  | var i => rfl
  | total f args ih =>
    change extendOperation R A.carrier S (A.total f) _ = _
    rw [funext ih, extendOperation_unit]
    rfl
  | quantity q args ih =>
    change extendOperation R A.carrier S (A.quantity q) _ = _
    rw [funext ih, extendOperation_unit]
    rfl
  | zero s => simp only [PolynomialTerm.eval, TensorProduct.tmul_zero]
  | add a b ha hb =>
    rw [PolynomialTerm.eval, ha, hb, PolynomialTerm.eval, TensorProduct.tmul_add]
  | smul a b hb =>
    rw [PolynomialTerm.eval, hb, PolynomialTerm.eval, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl

/-- The scalar-tower comparison reads a unit tensor as direct coefficient substitution. -/
private theorem scalarTower_unit_mapCoefficients {R S T M : Type u}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [AddCommGroup M] [Module R M] (f : S →ₐ[R] T) (z : S ⊗[R] M) :
    letI : Algebra S T := f.toRingHom.toAlgebra
    letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
    scalarTower (k := R) ((1 : T) ⊗ₜ[S] z) = mapCoefficients f z := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | tmul a m =>
    rw [scalarTower_tmul, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Evaluation of written polynomial terms commutes with arbitrary
coefficient substitution on scalar-extended carrier modules. -/
theorem PolynomialTerm.eval_mapCoefficients {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (c : k →+* R) (A : TensorStructure R sig)
    {ss : List sig.SortType} {s : sig.SortType}
    (x : ∀ i : TensorPosition ss, S ⊗[R] A.carrier i.1) (t : PolynomialTerm k sig ss s) :
    mapCoefficients f (t.eval ((algebraMap R S).comp c) (extendStructure R S A) x) =
      t.eval ((algebraMap R T).comp c) (extendStructure R T A)
        (fun i => mapCoefficients f (x i)) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let e := structureScalarTower (k := R) (R := S) (S := T) A
  have sameCoefficients : (algebraMap S T).comp ((algebraMap R S).comp c) =
      (algebraMap R T).comp c :=
    RingHom.ext fun a => (IsScalarTower.algebraMap_apply R S T (c a)).symm
  rw [← scalarTower_unit_mapCoefficients f]
  change e.hom.onSort s ((1 : T) ⊗ₜ[S]
    t.eval ((algebraMap R S).comp c) (extendStructure R S A) x) = _
  rw [← t.eval_unit ((algebraMap R S).comp c) (extendStructure R S A) x,
    PolynomialTerm.eval_map, sameCoefficients]
  exact congrArg (t.eval ((algebraMap R T).comp c) (extendStructure R T A))
    (funext fun i => scalarTower_unit_mapCoefficients f (x i))

/-- Transport a universally satisfied Law through the actual two-step scalar-extension comparison. -/
private theorem polynomialLaw_holds_direct_of_tower {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T]
    {ss : List sig.SortType} {s : sig.SortType} (l : PolynomialLaw k sig ss s)
    (c : k →+* R) (A : TensorStructure R sig)
    (h : l.Holds ((algebraMap R S).comp c) (extendStructure R S A)) :
    l.Holds ((algebraMap R T).comp c) (extendStructure R T A) := by
  have stage := l.holds_baseChange (S := T) ((algebraMap R S).comp c) (extendStructure R S A) h
  have same : (algebraMap S T).comp ((algebraMap R S).comp c) = (algebraMap R T).comp c :=
    RingHom.ext fun a => (IsScalarTower.algebraMap_apply R S T (c a)).symm
  rw [same] at stage
  exact (l.holds_iff_of_iso _ (structureScalarTower (k := R) (R := S) (S := T) A)).mp stage

/-- Universal polynomial Laws are detected on an arbitrary principal
cover. Each scalar test is checked using its own localized output module,
so the result applies to arbitrary carrier modules. -/
theorem PolynomialLaw.holds_of_principal_cover {R ι : Type u} [CommRing R]
    {ss : List sig.SortType} {s : sig.SortType} (l : PolynomialLaw k sig ss s)
    (c : k →+* R) (A : TensorStructure R sig) (r : ι → R)
    (covers : Ideal.span (Set.range r) = ⊤)
    (h : ∀ i, l.Holds ((algebraMap R (Localization.Away (r i))).comp c)
      (extendStructure R (Localization.Away (r i)) A)) : l.Holds c A := by
  intro S _ _ x
  apply sub_eq_zero.mp
  apply coefficient_eq_zero_of_powers_cover (fun i => algebraMap R S (r i))
    (coefficient_cover_map (algebraMap R S) r covers)
  intro i
  let Ri := Localization.Away (r i)
  let Ti := Localization.Away (algebraMap R S (r i))
  haveI : IsScalarTower R S Ti := inferInstance
  haveI : IsLocalization.Away ((Algebra.ofId R S) (r i)) Ti := by
    change IsLocalization.Away (algebraMap R S (r i)) (Localization.Away (algebraMap R S (r i)))
    infer_instance
  let g : Ri →ₐ[R] Ti := IsLocalization.Away.mapₐ Ri Ti (Algebra.ofId R S) (r i)
  letI : Algebra Ri Ti := g.toRingHom.toAlgebra
  letI : IsScalarTower R Ri Ti :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.commutes a).symm)
  have direct : l.Holds ((algebraMap R Ti).comp c) (extendStructure R Ti A) :=
    polynomialLaw_holds_direct_of_tower (S := Ri) l c A (h i)
  let e := structureScalarTower (k := R) (R := S) (S := Ti) A
  have stage := (l.holds_iff_of_iso ((algebraMap R Ti).comp c) e).mpr direct
  have same : (algebraMap S Ti).comp ((algebraMap R S).comp c) = (algebraMap R Ti).comp c := rfl
  rw [← same] at stage
  have equal := l.eval_eq_of_holds _ _ stage (fun j => (1 : Ti) ⊗ₜ[S] x j)
  rw [PolynomialTerm.eval_unit, PolynomialTerm.eval_unit] at equal
  have zero : (TensorProduct.mk S Ti ((extendStructure R S A).carrier s) 1)
      (l.left.eval ((algebraMap R S).comp c) (extendStructure R S A) x -
        l.right.eval ((algebraMap R S).comp c) (extendStructure R S A) x) = 0 := by
    change (1 : Ti) ⊗ₜ[S] (_ - _) = 0
    rw [TensorProduct.tmul_sub, equal, sub_self]
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff
    (Submonoid.powers (algebraMap R S (r i)))
    (TensorProduct.mk S Ti ((extendStructure R S A).carrier s) 1)).mp zero
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a.val (algebraMap R S (r i))).mp a.property
  exact ⟨n, by simpa only [hn, Submonoid.smul_def] using ha⟩

/-- A sheaf-structure isomorphism preserves the universal polynomial
Law on each open, through its actual sectionwise structure isomorphism. -/
theorem PolynomialLaw.holds_sections_iff_of_iso
    {ss : List sig.SortType} {s : sig.SortType}
    (l : PolynomialLaw k sig ss s) (b : X ⟶ Spec (CommRingCat.of k))
    {A B : SchemeTensorStructure X sig} (e : A ≅ B) (U : X.Opens) :
    l.Holds (sectionBaseMap b U) (sectionsStructure A U) ↔
      l.Holds (sectionBaseMap b U) (sectionsStructure B U) :=
  l.holds_iff_of_iso (sectionBaseMap b U) ((sectionsStructureFunctor U).mapIso e)

/-- Written tensor and universally quantified polynomial Laws are
invariant under actual isomorphisms of primitive sheaf structures. -/
theorem SatisfiesSchemeLaws.iff_of_iso
    (P : AffineLawPresentation k sig) (b : X ⟶ Spec (CommRingCat.of k))
    {A B : SchemeTensorStructure X sig} (e : A ≅ B) :
    SatisfiesSchemeLaws P b A ↔ SatisfiesSchemeLaws P b B := by
  have transport {A B : SchemeTensorStructure X sig} (e : A ≅ B)
      (h : SatisfiesSchemeLaws P b A) : SatisfiesSchemeLaws P b B := by
    intro U
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (TensorLaw.holds_iff_of_iso _ ((sectionsStructureFunctor U.1).mapIso e)).mp
        (h.tensor U i)
    · exact ((P.polynomialLaw i).holds_sections_iff_of_iso b e U.1).mp (h.polynomial U i)
  exact ⟨transport e, transport e.symm⟩

/-- Evaluating a written polynomial term and then restricting its value
agrees with evaluation on the restricted input tuple, with the actual
coefficient map supplied by the base morphism. -/
theorem PolynomialTerm.eval_sections_restrict
    (b : X ⟶ Spec (CommRingCat.of k)) (A : SchemeTensorStructure X sig)
    {U V : X.Opens} (inside : V ≤ U) {ss : List sig.SortType}
    (x : ∀ i : TensorPosition ss, (A.carrier i.1).val.obj (op U))
    {s : sig.SortType} (t : PolynomialTerm k sig ss s) :
    (A.carrier s).val.map (homOfLE inside).op
        (t.eval (sectionBaseMap b U) (sectionsStructure A U) x) =
      t.eval (sectionBaseMap b V) (sectionsStructure A V)
        (fun i => (A.carrier i.1).val.map (homOfLE inside).op (x i)) := by
  induction t with
  | var i => rfl
  | total f args ih =>
    rw [PolynomialTerm.eval, sectionsStructure_total_restrict]
    exact congrArg ((sectionsStructure A V).total f) (funext ih)
  | quantity q args ih =>
    rw [PolynomialTerm.eval, sectionsStructure_quantity_restrict]
    exact congrArg ((sectionsStructure A V).quantity q) (funext ih)
  | zero s => exact map_zero _
  | add a b ha hb =>
    rw [PolynomialTerm.eval, map_add, ha, hb, PolynomialTerm.eval]
  | smul r t ih =>
    rw [PolynomialTerm.eval, (A.carrier _).val.map_smul, ih, PolynomialTerm.eval]
    exact congrArg (fun a : Γ(X, V) => a • _)
      (congrArg (fun c : k →+* Γ(X, V) => c r) (sectionBaseMap_restrict b inside))

/-- Actual module sections are equal if their restrictions agree near
every point. This isolates the sheaf argument from term interpretation. -/
theorem moduleSections_eq_of_locally_eq (M : X.Modules) {U : X.Opens}
    (x y : M.val.obj (op U))
    (h : ∀ p ∈ U, ∃ V : X.Opens, ∃ inside : V ≤ U, p ∈ V ∧
      M.val.map (homOfLE inside).op x = M.val.map (homOfLE inside).op y) :
    x = y := by
  exact TopCat.Presheaf.IsSheaf.section_ext M.isSheaf h

/-- Equality of polynomial term values is local for the actual carrier
sheaf. At each point the witnessing smaller open can be chosen separately. -/
theorem PolynomialLaw.eval_eq_of_locally_eq
    (b : X ⟶ Spec (CommRingCat.of k)) (A : SchemeTensorStructure X sig)
    {U : X.Opens} {ss : List sig.SortType} {s : sig.SortType}
    (l : PolynomialLaw k sig ss s)
    (x : ∀ i : TensorPosition ss, (A.carrier i.1).val.obj (op U))
    (h : ∀ p ∈ U, ∃ V : X.Opens, ∃ inside : V ≤ U, p ∈ V ∧
      l.left.eval (sectionBaseMap b V) (sectionsStructure A V)
          (fun i => (A.carrier i.1).val.map (homOfLE inside).op (x i)) =
        l.right.eval (sectionBaseMap b V) (sectionsStructure A V)
          (fun i => (A.carrier i.1).val.map (homOfLE inside).op (x i))) :
    l.left.eval (sectionBaseMap b U) (sectionsStructure A U) x =
      l.right.eval (sectionBaseMap b U) (sectionsStructure A U) x := by
  apply moduleSections_eq_of_locally_eq (A.carrier s)
  intro p hp
  obtain ⟨V, inside, hpV, equal⟩ := h p hp
  exact ⟨V, inside, hpV, by
    exact (PolynomialTerm.eval_sections_restrict b A inside x l.left).trans
      (equal.trans (PolynomialTerm.eval_sections_restrict b A inside x l.right).symm)⟩

/-- Affine-open universal Law satisfaction implies the written equation
on actual sections of every open. The extension from affine opens uses
the affine basis and separatedness of the output carrier sheaf. -/
theorem SatisfiesSchemeLaws.polynomial_eval
    {P : AffineLawPresentation k sig} {b : X ⟶ Spec (CommRingCat.of k)}
    {A : SchemeTensorStructure X sig} (h : SatisfiesSchemeLaws P b A)
    (i : P.polynomialIndex) (U : X.Opens)
    (x : ∀ j : TensorPosition (P.inputs i), (A.carrier j.1).val.obj (op U)) :
    (P.polynomialLaw i).left.eval (sectionBaseMap b U) (sectionsStructure A U) x =
      (P.polynomialLaw i).right.eval (sectionBaseMap b U) (sectionsStructure A U) x := by
  apply (P.polynomialLaw i).eval_eq_of_locally_eq b A x
  intro p hp
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, inside⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨V, inside, hpV, ?_⟩
  exact (P.polynomialLaw i).eval_eq_of_holds _ _ (h.polynomial ⟨V, hV⟩ i) _

end

end SHIGURE.RealizationFamilies
