import Formal.AG.ReadingFunctoriality.FiniteExamples
import Formal.AG.Derived.FreeResolution
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

noncomputable section

namespace AAT.AG.ReadingFunctorialityFinite

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped Pointwise

private abbrev ModTwoZero := ModuleCat.of Int PUnit
private abbrev ModTwoQuotient := ModuleCat.of Int (Int ⧸ properIdeal)

private def IntPolynomialCanonical := Polynomial Int

private instance : AddCommGroup IntPolynomialCanonical := by
  dsimp only [IntPolynomialCanonical]
  infer_instance

private instance : Module Int IntPolynomialCanonical := by
  dsimp only [IntPolynomialCanonical]
  exact Polynomial.module

private instance : Module.FaithfullyFlat Int IntPolynomialCanonical := by
  exact Module.FaithfullyFlat.of_linearEquiv Int (Nat →₀ Int)
    (Polynomial.toFinsuppIsoLinear Int)

private def modTwoDifferential :
    ModuleCat.of Int Int ⟶ ModuleCat.of Int Int :=
  ModuleCat.ofHom ((2 : Int) • (LinearMap.id : Int →ₗ[Int] Int))

private def modTwoQuotientMap :
    ModuleCat.of Int Int ⟶ ModTwoQuotient :=
  ModuleCat.ofHom properIdeal.mkQ

private lemma modTwoDifferential_comp_quotientMap :
    modTwoDifferential ≫ modTwoQuotientMap = 0 := by
  rw [ModuleCat.hom_ext_iff]
  apply LinearMap.ext
  intro a
  change properIdeal.mkQ ((2 : Int) * a) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, properIdeal_eq]
  exact Ideal.mem_span_singleton'.mpr ⟨a, by ring⟩

private def modTwoPrincipalComplex :
    ChainComplex (ModuleCat.{0} Int) Nat :=
  ChainComplex.mk' (ModuleCat.of Int Int) (ModuleCat.of Int Int)
    modTwoDifferential (fun {X0 X1} f => ⟨ModTwoZero, 0, by simp⟩)

private def modTwoQuotientMapZero :
    modTwoPrincipalComplex.X 0 ⟶ ModTwoQuotient :=
  modTwoQuotientMap

private lemma modTwoPrincipalComplex_d_comp_quotientMapZero :
    modTwoPrincipalComplex.d 1 0 ≫ modTwoQuotientMapZero = 0 := by
  simpa [modTwoPrincipalComplex, modTwoQuotientMapZero] using
    modTwoDifferential_comp_quotientMap

private def modTwoPrincipalPi :
    modTwoPrincipalComplex ⟶
      (ChainComplex.single₀ (ModuleCat.{0} Int)).obj ModTwoQuotient := by
  refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
  exact ⟨modTwoQuotientMapZero,
    modTwoPrincipalComplex_d_comp_quotientMapZero⟩

private def modTwoPrincipalComplex_X_succ_succ_iso_zero (n : Nat) :
    modTwoPrincipalComplex.X (n + 2) ≅ ModTwoZero := by
  let succ' : ∀ {X₀ X₁ : ModuleCat.{0} Int} (f : X₁ ⟶ X₀),
      Σ' (X₂ : ModuleCat.{0} Int) (_d : X₂ ⟶ X₁), _d ≫ f = 0 :=
    fun {X₀ X₁} f => ⟨ModTwoZero, 0, by simp⟩
  exact ChainComplex.mk'XIso (ModuleCat.of Int Int) (ModuleCat.of Int Int)
    modTwoDifferential succ' n

private lemma modTwoPrincipalComplex_projective (n : Nat) :
    Projective (modTwoPrincipalComplex.X n) := by
  cases n with
  | zero =>
      simpa [modTwoPrincipalComplex] using
        (inferInstance : Projective (ModuleCat.of Int Int))
  | succ n =>
      cases n with
      | zero =>
          simpa [modTwoPrincipalComplex] using
            (inferInstance : Projective (ModuleCat.of Int Int))
      | succ n =>
          exact Projective.of_iso
            (modTwoPrincipalComplex_X_succ_succ_iso_zero n).symm
            (inferInstance : Projective ModTwoZero)

private lemma modTwoDifferential_injective :
    Function.Injective modTwoDifferential.hom := by
  exact smul_right_injective (M := Int) (by norm_num : (2 : Int) ≠ 0)

private lemma modTwoPrincipalComplex_exactAt_one :
    modTwoPrincipalComplex.ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro y hy
  change modTwoDifferential.hom (y : Int) = 0 at hy
  have hz : (y : Int) = 0 := modTwoDifferential_injective (by simpa using hy)
  subst hz
  exact ⟨0, by simp [modTwoPrincipalComplex]⟩

private lemma modTwoPrincipalComplex_isZero_X_succ_succ (n : Nat) :
    IsZero (modTwoPrincipalComplex.X (n + 2)) := by
  exact (ModuleCat.isZero_of_subsingleton ModTwoZero).of_iso
    (modTwoPrincipalComplex_X_succ_succ_iso_zero n)

private lemma modTwoPrincipalComplex_exactAt_succ (n : Nat) :
    modTwoPrincipalComplex.ExactAt (n + 1) := by
  cases n with
  | zero => simpa using modTwoPrincipalComplex_exactAt_one
  | succ n =>
      rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)]
      apply ShortComplex.exact_of_isZero_X₂
      exact modTwoPrincipalComplex_isZero_X_succ_succ n

private lemma modTwoDifferential_quotientMap_exact :
    (ShortComplex.mk modTwoDifferential modTwoQuotientMap
      modTwoDifferential_comp_quotientMap).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨a, ha⟩
    subst ha
    change properIdeal.mkQ ((2 : Int) * a) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, properIdeal_eq]
    exact Ideal.mem_span_singleton'.mpr ⟨a, by ring⟩
  · intro y hy
    change properIdeal.mkQ (y : Int) = 0 at hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      properIdeal_eq, Ideal.mem_span_singleton'] at hy
    rcases hy with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha]
    change modTwoDifferential.hom a = a * 2
    simp [modTwoDifferential]
    ring

private lemma modTwoQuotientMap_epi : Epi modTwoQuotientMap := by
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

private lemma modTwoPrincipalPi_quasiIsoAt_zero :
    QuasiIsoAt modTwoPrincipalPi 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros']
  constructor
  · simpa [modTwoQuotientMapZero, modTwoPrincipalComplex] using
      modTwoDifferential_quotientMap_exact
  · simpa [modTwoPrincipalPi, modTwoQuotientMapZero] using
      modTwoQuotientMap_epi
  all_goals simp [modTwoPrincipalComplex]

private lemma modTwoPrincipalPi_quasiIsoAt_succ (n : Nat) :
    QuasiIsoAt modTwoPrincipalPi (n + 1) := by
  rw [quasiIsoAt_iff_exactAt' _ _
    (ChainComplex.exactAt_succ_single_obj ModTwoQuotient n)]
  exact modTwoPrincipalComplex_exactAt_succ n

private lemma modTwoPrincipalPi_quasiIso : QuasiIso modTwoPrincipalPi where
  quasiIsoAt i := by
    cases i with
    | zero => exact modTwoPrincipalPi_quasiIsoAt_zero
    | succ n => exact modTwoPrincipalPi_quasiIsoAt_succ n

private noncomputable def modTwoPrincipalProjectiveResolution :
    ProjectiveResolution ModTwoQuotient where
  complex := modTwoPrincipalComplex
  projective := modTwoPrincipalComplex_projective
  π := modTwoPrincipalPi
  quasiIso := modTwoPrincipalPi_quasiIso

private abbrev modTwoTensorComplex :
    ChainComplex (ModuleCat.{0} Int) Nat :=
  ((((MonoidalCategory.tensoringLeft (ModuleCat.{0} Int)).obj
    ModTwoQuotient).mapHomologicalComplex _).obj modTwoPrincipalComplex)

private def modTwoTensorCycleRepresentative : modTwoTensorComplex.X 1 :=
  TensorProduct.tmul Int
    (Submodule.Quotient.mk (1 : Int) : Int ⧸ properIdeal) (1 : Int)

private lemma one_not_mem_properIdeal : (1 : Int) ∉ properIdeal := by
  intro h
  apply properIdeal_ne_top
  exact (Ideal.eq_top_iff_one properIdeal).mpr h

private lemma modTwoTensorCycleRepresentative_ne_zero :
    modTwoTensorCycleRepresentative ≠ 0 := by
  intro h
  have hmap :
      (TensorProduct.rid Int (Int ⧸ properIdeal)).toLinearMap
          modTwoTensorCycleRepresentative = 0 := by
    rw [h]
    exact (TensorProduct.rid Int (Int ⧸ properIdeal)).toLinearMap.map_zero
  have hcalc :
      (TensorProduct.rid Int (Int ⧸ properIdeal)).toLinearMap
          modTwoTensorCycleRepresentative =
        (Submodule.Quotient.mk (1 : Int) : Int ⧸ properIdeal) := by
    simp [modTwoTensorCycleRepresentative]
  rw [hcalc] at hmap
  apply one_not_mem_properIdeal
  rw [← Submodule.Quotient.mk_eq_zero]
  simpa using hmap

private lemma modTwoTensorCycleRepresentative_is_cycle :
    modTwoTensorComplex.d 1 0 modTwoTensorCycleRepresentative = 0 := by
  change (((2 : Int) • (LinearMap.id : Int →ₗ[Int] Int)).lTensor
      (Int ⧸ properIdeal))
    (TensorProduct.tmul Int
      (Submodule.Quotient.mk (1 : Int) : Int ⧸ properIdeal) (1 : Int)) = 0
  rw [LinearMap.lTensor_tmul]
  change TensorProduct.tmul Int
      (Submodule.Quotient.mk (1 : Int) : Int ⧸ properIdeal)
      ((2 : Int) * 1) = 0
  rw [mul_one]
  have htwo : (2 : Int) = (2 : Int) • (1 : Int) := by simp
  rw [htwo, TensorProduct.tmul_smul]
  change TensorProduct.tmul Int
      ((2 : Int) • (Submodule.Quotient.mk (1 : Int) : Int ⧸ properIdeal))
      (1 : Int) = 0
  rw [← Submodule.Quotient.mk_smul]
  change TensorProduct.tmul Int
      (Submodule.Quotient.mk ((2 : Int) * 1) : Int ⧸ properIdeal)
      (1 : Int) = 0
  rw [show (Submodule.Quotient.mk ((2 : Int) * 1) : Int ⧸ properIdeal) = 0 by
    rw [Submodule.Quotient.mk_eq_zero, mul_one, properIdeal_eq]
    exact Ideal.subset_span (by simp)]
  simp

private abbrev modTwoTensorShortComplexAtOne :
    ShortComplex (ModuleCat.{0} Int) :=
  modTwoTensorComplex.sc 1

private def modTwoTensorKernelAtOne :
    LinearMap.ker modTwoTensorShortComplexAtOne.g.hom where
  val := modTwoTensorCycleRepresentative
  property := by
    rw [LinearMap.mem_ker]
    unfold modTwoTensorShortComplexAtOne
    change modTwoTensorComplex.d 1 ((ComplexShape.down Nat).next 1)
      modTwoTensorCycleRepresentative = 0
    rw [show (ComplexShape.down Nat).next 1 = 0 by simp]
    exact modTwoTensorCycleRepresentative_is_cycle

private noncomputable def modTwoTensorConcreteHomologyAtOne :
    modTwoTensorShortComplexAtOne.moduleCatLeftHomologyData.H :=
  Submodule.Quotient.mk modTwoTensorKernelAtOne

private lemma modTwoTensorConcreteHomologyAtOne_ne_zero :
    modTwoTensorConcreteHomologyAtOne ≠ 0 := by
  intro h
  have hmem : modTwoTensorKernelAtOne ∈
      LinearMap.range modTwoTensorShortComplexAtOne.moduleCatToCycles := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [modTwoTensorConcreteHomologyAtOne] using h
  rcases hmem with ⟨b, hb⟩
  have hbzero : modTwoTensorShortComplexAtOne.moduleCatToCycles b = 0 := by
    have hsource_zero : IsZero modTwoTensorShortComplexAtOne.X₁ := by
      dsimp [modTwoTensorShortComplexAtOne, modTwoTensorComplex,
        HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
        HomologicalComplex.shortComplexFunctor']
      rw [show (ComplexShape.down Nat).prev 1 = 2 by simp]
      change IsZero
        (((MonoidalCategory.tensoringLeft (ModuleCat.{0} Int)).obj
          ModTwoQuotient).obj (modTwoPrincipalComplex.X 2))
      refine Functor.map_isZero _ ?_
      exact (ModuleCat.isZero_of_subsingleton ModTwoZero).of_iso
        (modTwoPrincipalComplex_X_succ_succ_iso_zero 0)
    haveI : Subsingleton modTwoTensorShortComplexAtOne.X₁ :=
      ModuleCat.subsingleton_of_isZero hsource_zero
    have hb_src : b = 0 := Subsingleton.elim _ _
    rw [hb_src]
    exact modTwoTensorShortComplexAtOne.moduleCatToCycles.map_zero
  have hcyclezero : modTwoTensorCycleRepresentative = 0 := by
    have hkernel : modTwoTensorKernelAtOne = 0 := hb.symm.trans hbzero
    exact congrArg Subtype.val hkernel
  exact modTwoTensorCycleRepresentative_ne_zero hcyclezero

private noncomputable def modTwoTensorHomologyAtOne :
    modTwoTensorComplex.homology 1 :=
  modTwoTensorShortComplexAtOne.moduleCatHomologyIso.inv
    modTwoTensorConcreteHomologyAtOne

private lemma modTwoTensorHomologyAtOne_ne_zero :
    modTwoTensorHomologyAtOne ≠ 0 := by
  intro h
  apply modTwoTensorConcreteHomologyAtOne_ne_zero
  have hmap := congrArg
    modTwoTensorShortComplexAtOne.moduleCatHomologyIso.hom h
  simpa [modTwoTensorHomologyAtOne] using hmap

/-- The generic flat Tor base-change isomorphism specialized to `(2)` and `ℤ → ℤ[X]`. -/
noncomputable def modTwoTorOneBaseChangeIso :
    Derived.Intersection.moduleScalarExtension intPolynomialFlatChange
        (Derived.Intersection.mathlibTor Int properIdeal properIdeal 1) ≅
      Derived.Intersection.mathlibTor (Polynomial Int)
        (properIdeal.map intPolynomialFlatChange.hom)
        (properIdeal.map intPolynomialFlatChange.hom) 1 :=
  Derived.Intersection.mathlibTorFlatBaseChangeIso
    intPolynomialFlatChange properIdeal properIdeal 1

/-- The nonzero class in `Tor₁^ℤ(ℤ/(2), ℤ/(2))` computed by the two-term principal resolution. -/
noncomputable def modTwoTorOneSourceWitness :
    Derived.Intersection.mathlibTor Int properIdeal properIdeal 1 :=
  (Derived.FreeResolution.MathlibResolution.torIsoProjectiveResolutionHomology
    Int properIdeal modTwoPrincipalProjectiveResolution 1).inv
      modTwoTensorHomologyAtOne

/-- The selected source class is nonzero by the explicit tensor-homology calculation. -/
theorem modTwoTorOneSourceWitness_ne_zero :
    modTwoTorOneSourceWitness ≠ 0 := by
  intro h
  apply modTwoTensorHomologyAtOne_ne_zero
  have hmap := congrArg
    (Derived.FreeResolution.MathlibResolution.torIsoProjectiveResolutionHomology
      Int properIdeal modTwoPrincipalProjectiveResolution 1).hom h
  simpa [modTwoTorOneSourceWitness] using hmap

/-- The target class obtained from the canonical scalar-extension unit and the generic Tor iso. -/
noncomputable def modTwoTorOneTargetWitness :
    Derived.Intersection.mathlibTor (Polynomial Int)
      (properIdeal.map intPolynomialFlatChange.hom)
      (properIdeal.map intPolynomialFlatChange.hom) 1 :=
  modTwoTorOneBaseChangeIso.hom
    (Derived.Intersection.moduleScalarExtensionUnit
      intPolynomialFlatChange
      (Derived.Intersection.mathlibTor Int properIdeal properIdeal 1)
      modTwoTorOneSourceWitness)

private theorem intPolynomialFaithfullyFlat :
    intPolynomialFlatChange.hom.FaithfullyFlat := by
  rw [intPolynomialFlatChange_hom]
  letI : Algebra Int (Polynomial Int) := Polynomial.C.toAlgebra
  letI : Module Int (Polynomial Int) := Algebra.toModule
  change Module.FaithfullyFlat Int (Polynomial Int)
  let e : Polynomial Int ≃ₗ[Int] IntPolynomialCanonical := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r p
      change Polynomial.C r * p = r • (p : IntPolynomialCanonical)
      rw [Polynomial.smul_eq_C_mul] }
  exact Module.FaithfullyFlat.of_linearEquiv Int IntPolynomialCanonical e

/-- The target class is nonzero by faithful-flat injectivity of the scalar-extension unit. -/
theorem modTwoTorOneTargetWitness_ne_zero :
    modTwoTorOneTargetWitness ≠ 0 := by
  letI : Algebra Int (Polynomial Int) :=
    intPolynomialFlatChange.hom.toAlgebra
  letI : Module Int (Polynomial Int) := Algebra.toModule
  letI : Module.FaithfullyFlat Int (Polynomial Int) := by
    have h := intPolynomialFaithfullyFlat
    change Module.FaithfullyFlat Int (Polynomial Int) at h
    exact h
  intro hzero
  have hunit :
      Derived.Intersection.moduleScalarExtensionUnit
          intPolynomialFlatChange
          (Derived.Intersection.mathlibTor Int properIdeal properIdeal 1)
          modTwoTorOneSourceWitness = 0 := by
    have hinjective : Function.Injective modTwoTorOneBaseChangeIso.hom :=
      ((ConcreteCategory.isIso_iff_bijective
        modTwoTorOneBaseChangeIso.hom).mp (by infer_instance)).1
    apply hinjective
    simpa [modTwoTorOneTargetWitness] using hzero
  apply modTwoTorOneSourceWitness_ne_zero
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff
    (R := Int)
    (M := Derived.Intersection.mathlibTor Int properIdeal properIdeal 1)
    (A := Polynomial Int) modTwoTorOneSourceWitness).mp (by
      simpa only [Derived.Intersection.moduleScalarExtensionUnit_apply] using hunit)

/-- The target Tor object is nontrivial, witnessed by the transported class. -/
theorem modTwoTorOne_baseChange_nonzero :
    Nontrivial
      (Derived.Intersection.mathlibTor (Polynomial Int)
        (properIdeal.map intPolynomialFlatChange.hom)
        (properIdeal.map intPolynomialFlatChange.hom) 1) :=
  nontrivial_iff.mpr
    ⟨modTwoTorOneTargetWitness, 0,
      modTwoTorOneTargetWitness_ne_zero⟩

end AAT.AG.ReadingFunctorialityFinite
