import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.RingTheory.Derivation.ToSquareZero
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.AmbientOperationLocalization

/-!
# Quotient-valued semantic operation derivations

This file maps one ambient law ideal into every J1a chart and overlap, induces
the canonical quotient restrictions, and composes the J1b localized ambient
derivations with the corresponding quotient maps. The resulting derivations
are then sent directly through mathlib's square-zero lift equivalence.

## Implementation notes

The law ideal is a plain ambient parameter rather than a family of chartwise
fields. Taking its images generates the ideal transport and both quotient
restriction maps, so their compatibility is proved instead of supplied.
Requiring the ambient derivation to preserve the law ideal is also rejected:
the quotient-valued derivation exists without that premise, while ideal
preservation is characterized by a later conormal-response theorem.

For the semantic operation, a hand-written pair formula or a supplied lift
would duplicate or bypass mathlib's universal API. `derivationEquivLift`
therefore combines the canonical coefficient identification with
`derivationToSquareZeroEquivLift`; its projection and recovery theorems form
the no-unfold API passed to J3a.
-/

namespace ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent

universe uₖ uA uS uOp uChart uState uBefore uAfter

namespace QuotientValuedDerivation

variable {k : Type uₖ} {S : Type uS}
variable [CommRing k] [CommRing S] [Algebra k S]

/-- Push a derivation through the canonical quotient map on its coefficients. -/
noncomputable def quotientDerivation (I : Ideal S) (d : Derivation k S S) :
    Derivation k S (S ⧸ I) :=
  (Ideal.Quotient.mkₐ S I).toLinearMap.compDer d

/-- Quotient coefficient push-forward is pointwise application of the quotient map. -/
@[simp] theorem quotientDerivation_apply (I : Ideal S)
    (d : Derivation k S S) (x : S) :
    quotientDerivation I d x = Ideal.Quotient.mk I (d x) := rfl

end QuotientValuedDerivation

namespace TypedLocalizationGeometry

variable {k : Type uₖ} {A₀ : Type uA} {Chart : Type uChart}
variable [Field k] [CommRing A₀] [Algebra k A₀] [Fintype Chart]

/-- The ambient law ideal transported to one principal chart. -/
def chartLawIdeal (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i : Chart) : Ideal (G.chartRing i) :=
  I₀.map (algebraMap A₀ (G.chartRing i))

/-- The ambient law ideal transported to one pairwise overlap. -/
def overlapLawIdeal (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) : Ideal (G.overlapRing i j) :=
  I₀.map (algebraMap A₀ (G.overlapRing i j))

/-- The lawful coordinate algebra of one selected chart. -/
abbrev chartLawQuotient (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i : Chart) :=
  G.chartRing i ⧸ G.chartLawIdeal I₀ i

/-- The lawful coordinate algebra of one selected pairwise overlap. -/
abbrev overlapLawQuotient (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :=
  G.overlapRing i j ⧸ G.overlapLawIdeal I₀ i j

/-- The left chart restriction maps the transported ideal onto the overlap ideal. -/
theorem leftChartLawIdeal_map
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    (G.chartLawIdeal I₀ i).map (G.leftChartToOverlap i j) =
      G.overlapLawIdeal I₀ i j := by
  calc
    _ = I₀.map ((G.leftChartToOverlap i j).toRingHom.comp
        (algebraMap A₀ (G.chartRing i))) := Ideal.map_map _ _
    _ = _ := by
      congr 1
      ext a
      exact G.leftChartToOverlap_algebraMap i j a

/-- The right chart restriction maps the transported ideal onto the overlap ideal. -/
theorem rightChartLawIdeal_map
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    (G.chartLawIdeal I₀ j).map (G.rightChartToOverlap i j) =
      G.overlapLawIdeal I₀ i j := by
  calc
    _ = I₀.map ((G.rightChartToOverlap i j).toRingHom.comp
        (algebraMap A₀ (G.chartRing j))) := Ideal.map_map _ _
    _ = _ := by
      congr 1
      ext a
      exact G.rightChartToOverlap_algebraMap i j a

/-- Ideal compatibility needed to induce the left quotient restriction. -/
theorem chartLawIdeal_le_left_comap
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    G.chartLawIdeal I₀ i ≤
      (G.overlapLawIdeal I₀ i j).comap (G.leftChartToOverlap i j) := by
  exact Ideal.map_le_iff_le_comap.mp (G.leftChartLawIdeal_map I₀ i j).le

/-- Ideal compatibility needed to induce the right quotient restriction. -/
theorem chartLawIdeal_le_right_comap
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    G.chartLawIdeal I₀ j ≤
      (G.overlapLawIdeal I₀ i j).comap (G.rightChartToOverlap i j) := by
  exact Ideal.map_le_iff_le_comap.mp (G.rightChartLawIdeal_map I₀ i j).le

/-- The left restriction induced on the generated law quotients. -/
noncomputable def leftLawQuotientRestriction
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    (G.chartRing i ⧸ G.chartLawIdeal I₀ i) →ₐ[k]
      (G.overlapRing i j ⧸ G.overlapLawIdeal I₀ i j) :=
  Ideal.quotientMapₐ (G.overlapLawIdeal I₀ i j)
    ((G.leftChartToOverlap i j).restrictScalars k)
    (G.chartLawIdeal_le_left_comap I₀ i j)

/-- The right restriction induced on the generated law quotients. -/
noncomputable def rightLawQuotientRestriction
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    (G.chartRing j ⧸ G.chartLawIdeal I₀ j) →ₐ[k]
      (G.overlapRing i j ⧸ G.overlapLawIdeal I₀ i j) :=
  Ideal.quotientMapₐ (G.overlapLawIdeal I₀ i j)
    ((G.rightChartToOverlap i j).restrictScalars k)
    (G.chartLawIdeal_le_right_comap I₀ i j)

/-- The left quotient restriction sends a class to the class of its restriction. -/
@[simp] theorem leftLawQuotientRestriction_mk
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) (x : G.chartRing i) :
    G.leftLawQuotientRestriction I₀ i j
        (Ideal.Quotient.mk (G.chartLawIdeal I₀ i) x) =
      Ideal.Quotient.mk (G.overlapLawIdeal I₀ i j)
        (G.leftChartToOverlap i j x) := rfl

/-- The right quotient restriction sends a class to the class of its restriction. -/
@[simp] theorem rightLawQuotientRestriction_mk
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) (x : G.chartRing j) :
    G.rightLawQuotientRestriction I₀ i j
        (Ideal.Quotient.mk (G.chartLawIdeal I₀ j) x) =
      Ideal.Quotient.mk (G.overlapLawIdeal I₀ i j)
        (G.rightChartToOverlap i j x) := rfl

/-- The left quotient restriction commutes with the two quotient maps. -/
theorem leftLawQuotientRestriction_comp_mk
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    (G.leftLawQuotientRestriction I₀ i j).comp
        (Ideal.Quotient.mkₐ k (G.chartLawIdeal I₀ i)) =
      (Ideal.Quotient.mkₐ k (G.overlapLawIdeal I₀ i j)).comp
        ((G.leftChartToOverlap i j).restrictScalars k) :=
  Ideal.quotient_map_comp_mkₐ _ _ _

/-- The right quotient restriction commutes with the two quotient maps. -/
theorem rightLawQuotientRestriction_comp_mk
    (G : TypedLocalizationGeometry k A₀ Chart)
    (I₀ : Ideal A₀) (i j : Chart) :
    (G.rightLawQuotientRestriction I₀ i j).comp
        (Ideal.Quotient.mkₐ k (G.chartLawIdeal I₀ j)) =
      (Ideal.Quotient.mkₐ k (G.overlapLawIdeal I₀ i j)).comp
        ((G.rightChartToOverlap i j).restrictScalars k) :=
  Ideal.quotient_map_comp_mkₐ _ _ _

end TypedLocalizationGeometry

namespace ArchitectureOperationPresentation

open QuotientValuedDerivation

variable {k : Type uₖ} {A₀ : Type uA} {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [CommRing A₀] [Algebra k A₀]
variable [Fintype Op] [Fintype Chart]

/-- The selected chart derivation with coefficients pushed to its law quotient. -/
noncomputable def chartQuotientDerivation
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i : Chart) :
    Derivation k (G.chartRing i) (G.chartRing i ⧸ G.chartLawIdeal I₀ i) :=
  quotientDerivation (G.chartLawIdeal I₀ i) (P.chartDerivation G op i)

/-- The selected overlap derivation with coefficients pushed to its law quotient. -/
noncomputable def overlapQuotientDerivation
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) :
    Derivation k (G.overlapRing i j)
      (G.overlapRing i j ⧸ G.overlapLawIdeal I₀ i j) :=
  quotientDerivation (G.overlapLawIdeal I₀ i j) (P.overlapDerivation G op i j)

/-- Quotient-valued derivations commute with the generated left restriction. -/
theorem leftQuotientDerivation_natural
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) (x : G.chartRing i) :
    P.overlapQuotientDerivation G I₀ op i j (G.leftChartToOverlap i j x) =
      G.leftLawQuotientRestriction I₀ i j (P.chartQuotientDerivation G I₀ op i x) := by
  rw [overlapQuotientDerivation, quotientDerivation_apply,
    P.leftChartToOverlap_derivation_natural]
  rfl

/-- Quotient-valued derivations commute with the generated right restriction. -/
theorem rightQuotientDerivation_natural
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) (x : G.chartRing j) :
    P.overlapQuotientDerivation G I₀ op i j (G.rightChartToOverlap i j x) =
      G.rightLawQuotientRestriction I₀ i j (P.chartQuotientDerivation G I₀ op j x) := by
  rw [overlapQuotientDerivation, quotientDerivation_apply,
    P.rightChartToOverlap_derivation_natural]
  rfl

/-- On ambient elements, the chart response is the quotient of the ambient derivative. -/
@[simp] theorem chartQuotientDerivation_algebraMap
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i : Chart) (a : A₀) :
    P.chartQuotientDerivation G I₀ op i
        (algebraMap A₀ (G.chartRing i) a) =
      Ideal.Quotient.mk (G.chartLawIdeal I₀ i)
        (algebraMap A₀ (G.chartRing i) (P.ambientDerivation op a)) := by
  rw [chartQuotientDerivation, quotientDerivation_apply,
    P.chartDerivation_algebraMap]

/-- On ambient elements, the overlap response is the quotient of the ambient derivative. -/
@[simp] theorem overlapQuotientDerivation_algebraMap
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) (a : A₀) :
    P.overlapQuotientDerivation G I₀ op i j
        (algebraMap A₀ (G.overlapRing i j) a) =
      Ideal.Quotient.mk (G.overlapLawIdeal I₀ i j)
        (algebraMap A₀ (G.overlapRing i j) (P.ambientDerivation op a)) := by
  rw [overlapQuotientDerivation, quotientDerivation_apply,
    P.overlapDerivation_algebraMap]

end ArchitectureOperationPresentation

namespace TrivialSquareZeroOperation

universe uR uDomain uCodomain
variable {R : Type uR} {A : Type uDomain} {B : Type uCodomain}
variable [CommSemiring R] [CommSemiring A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The kernel ideal of the first projection from a trivial square-zero extension. -/
def extensionIdeal : Ideal (TrivSqZeroExt B B) :=
  RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom

/-- The kernel of the first projection has square zero. -/
theorem extensionIdeal_sq : extensionIdeal (B := B) ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm
  · intro z hz
    change z = 0
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro x hx y hy
      change TrivSqZeroExt.fst x = 0 at hx
      change TrivSqZeroExt.fst y = 0 at hy
      apply TrivSqZeroExt.ext
      · simp [hx, hy]
      · simp [hx, hy]
    · intro x y hx hy
      rw [hx, hy, add_zero]
  · exact bot_le

/-- The coefficient module maps linearly onto the square-zero kernel. -/
def inrLinear : B →ₗ[B] extensionIdeal (B := B) :=
  { toFun := fun b ↦ ⟨TrivSqZeroExt.inr b, by simp [extensionIdeal]⟩
    map_add' := fun x y ↦ by
      apply Subtype.ext
      exact TrivSqZeroExt.inr_add B x y
    map_smul' := fun r x ↦ by
      apply Subtype.ext
      exact TrivSqZeroExt.inr_smul B r x }

/-- The coefficient-to-kernel linear map is bijective. -/
theorem inrLinear_bijective : Function.Bijective (inrLinear (B := B)) := by
  constructor
  · intro x y h
    have hsnd := congrArg (fun z : TrivSqZeroExt B B ↦ TrivSqZeroExt.snd z)
      (congrArg Subtype.val h)
    simpa [inrLinear] using hsnd
  · rintro ⟨x, hx⟩
    refine ⟨TrivSqZeroExt.snd x, Subtype.ext ?_⟩
    change ↑(inrLinear (B := B) (TrivSqZeroExt.snd x)) = x
    simp only [inrLinear]
    apply TrivSqZeroExt.ext
    · change TrivSqZeroExt.fst x = 0 at hx
      simp [hx]
    · simp

/-- The canonical linear equivalence between coefficients and the square-zero kernel. -/
noncomputable def inrEquiv : B ≃ₗ[B] extensionIdeal (B := B) :=
  LinearEquiv.ofBijective inrLinear inrLinear_bijective

/-- A square-zero algebra lift together with mathlib's canonical quotient equation. -/
abbrev LiftWitness
    (R : Type uR) (A : Type uDomain) (B : Type uCodomain)
    [CommSemiring R] [CommSemiring A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :=
    { f : A →ₐ[R] TrivSqZeroExt B B //
      (Ideal.Quotient.mkₐ R (extensionIdeal (B := B))).comp f =
        IsScalarTower.toAlgHom R A
          (TrivSqZeroExt B B ⧸ extensionIdeal (B := B)) }

/-- The direct mathlib equivalence between coefficient derivations and square-zero lifts. -/
noncomputable def derivationEquivLift :
    Derivation R A B ≃ LiftWitness R A B :=
  ((inrEquiv (B := B)).restrictScalars A).compDer.toEquiv.trans
    (derivationToSquareZeroEquivLift (extensionIdeal (B := B))
      (extensionIdeal_sq (B := B)))

/-- The square-zero lift witness selected by a derivation. -/
noncomputable def liftWitness (d : Derivation R A B) :=
  derivationEquivLift d

/-- The algebra hom underlying the selected square-zero lift witness. -/
noncomputable def lift (d : Derivation R A B) : A →ₐ[R] TrivSqZeroExt B B :=
  (liftWitness d).1

/-- The first projection of the selected lift is the coefficient algebra map. -/
theorem lift_fst (d : Derivation R A B) :
    (TrivSqZeroExt.fstHom R B B).comp (lift d) = IsScalarTower.toAlgHom R A B := by
  ext a
  simp [lift, liftWitness, derivationEquivLift, inrLinear, inrEquiv,
    TrivSqZeroExt.algebraMap_eq_inl']

/-- The second projection of the selected lift recovers the input derivation. -/
theorem lift_snd (d : Derivation R A B) (a : A) :
    TrivSqZeroExt.snd (lift d a) = d a := by
  simp [lift, liftWitness, derivationEquivLift, inrLinear, inrEquiv,
    TrivSqZeroExt.algebraMap_eq_inl']

/-- Applying the inverse equivalence to the selected witness recovers the derivation. -/
theorem derivationEquivLift_symm_liftWitness (d : Derivation R A B) :
    derivationEquivLift.symm (liftWitness d) = d :=
  Equiv.symm_apply_apply _ d

end TrivialSquareZeroOperation

namespace ArchitectureOperationPresentation

variable {k : Type uₖ} {A₀ : Type uA} {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [CommRing A₀] [Algebra k A₀]
variable [Fintype Op] [Fintype Chart]

/-- The semantic first-order operation lift generated on one chart. -/
noncomputable def chartSemanticFirstOrderOperation
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i : Chart) :
    TrivialSquareZeroOperation.LiftWitness
      k (G.chartRing i) (G.chartLawQuotient I₀ i) :=
  TrivialSquareZeroOperation.liftWitness
    (P.chartQuotientDerivation G I₀ op i)

/-- The semantic first-order operation lift generated on one pairwise overlap. -/
noncomputable def overlapSemanticFirstOrderOperation
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) :
    TrivialSquareZeroOperation.LiftWitness
      k (G.overlapRing i j) (G.overlapLawQuotient I₀ i j) :=
  TrivialSquareZeroOperation.liftWitness
    (P.overlapQuotientDerivation G I₀ op i j)

/-- The chart lift projects to the chart law quotient map. -/
theorem chartSemanticFirstOrderOperation_fst
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i : Chart) :
    (TrivSqZeroExt.fstHom k (G.chartLawQuotient I₀ i)
        (G.chartLawQuotient I₀ i)).comp
        (P.chartSemanticFirstOrderOperation G I₀ op i).1 =
      Ideal.Quotient.mkₐ k (G.chartLawIdeal I₀ i) := by
  change
    (TrivSqZeroExt.fstHom k (G.chartLawQuotient I₀ i)
      (G.chartLawQuotient I₀ i)).comp
        (TrivialSquareZeroOperation.lift
          (P.chartQuotientDerivation G I₀ op i)) = _
  calc
    _ = IsScalarTower.toAlgHom k (G.chartRing i)
        (G.chartLawQuotient I₀ i) :=
      TrivialSquareZeroOperation.lift_fst _
    _ = _ := rfl

/-- The overlap lift projects to the overlap law quotient map. -/
theorem overlapSemanticFirstOrderOperation_fst
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) :
    (TrivSqZeroExt.fstHom k (G.overlapLawQuotient I₀ i j)
        (G.overlapLawQuotient I₀ i j)).comp
        (P.overlapSemanticFirstOrderOperation G I₀ op i j).1 =
      Ideal.Quotient.mkₐ k (G.overlapLawIdeal I₀ i j) := by
  change
    (TrivSqZeroExt.fstHom k (G.overlapLawQuotient I₀ i j)
      (G.overlapLawQuotient I₀ i j)).comp
        (TrivialSquareZeroOperation.lift
          (P.overlapQuotientDerivation G I₀ op i j)) = _
  calc
    _ = IsScalarTower.toAlgHom k (G.overlapRing i j)
        (G.overlapLawQuotient I₀ i j) :=
      TrivialSquareZeroOperation.lift_fst _
    _ = _ := rfl

/-- The chart lift's second component is the generated quotient-valued derivation. -/
@[simp] theorem chartSemanticFirstOrderOperation_snd
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i : Chart) (x : G.chartRing i) :
    TrivSqZeroExt.snd ((P.chartSemanticFirstOrderOperation G I₀ op i).1 x) =
      P.chartQuotientDerivation G I₀ op i x := by
  change TrivSqZeroExt.snd
    (TrivialSquareZeroOperation.lift
      (P.chartQuotientDerivation G I₀ op i) x) = _
  exact TrivialSquareZeroOperation.lift_snd _ _

/-- The overlap lift's second component is the generated quotient-valued derivation. -/
@[simp] theorem overlapSemanticFirstOrderOperation_snd
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) (x : G.overlapRing i j) :
    TrivSqZeroExt.snd ((P.overlapSemanticFirstOrderOperation G I₀ op i j).1 x) =
      P.overlapQuotientDerivation G I₀ op i j x := by
  change TrivSqZeroExt.snd
    (TrivialSquareZeroOperation.lift
      (P.overlapQuotientDerivation G I₀ op i j) x) = _
  exact TrivialSquareZeroOperation.lift_snd _ _

/-- The square-zero equivalence recovers the chart quotient-valued derivation. -/
theorem chartSemanticFirstOrderOperation_recovers_derivation
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i : Chart) :
    TrivialSquareZeroOperation.derivationEquivLift.symm
        (P.chartSemanticFirstOrderOperation G I₀ op i) =
      P.chartQuotientDerivation G I₀ op i :=
  TrivialSquareZeroOperation.derivationEquivLift_symm_liftWitness _

/-- The square-zero equivalence recovers the overlap quotient-valued derivation. -/
theorem overlapSemanticFirstOrderOperation_recovers_derivation
    (P : ArchitectureOperationPresentation k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart) (I₀ : Ideal A₀)
    (op : Op) (i j : Chart) :
    TrivialSquareZeroOperation.derivationEquivLift.symm
        (P.overlapSemanticFirstOrderOperation G I₀ op i j) =
      P.overlapQuotientDerivation G I₀ op i j :=
  TrivialSquareZeroOperation.derivationEquivLift_symm_liftWitness _

end ArchitectureOperationPresentation

end ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.QuotientValuedDerivation
#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.TypedLocalizationGeometry
#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.TrivialSquareZeroOperation
#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ArchitectureOperationPresentation
