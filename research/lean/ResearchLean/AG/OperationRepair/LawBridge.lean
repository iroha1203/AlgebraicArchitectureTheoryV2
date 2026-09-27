import ResearchLean.AG.OperationRepair.Classification
import ResearchLean.AG.CanonicalResolution.JointKernel

/-!
# Law observations and operation-preserving readings

The joint Law evaluation is the observation of the operation system. An
ordinary surjective reading carries a repair quotient structure exactly when
its kernel supports the named operations, all Laws descend, and it identifies
the requested pairs.
-/

namespace AAT.AG.OperationRepair

open AAT.AG.CanonicalResolution

universe u v

variable {S : Type u} {E : Type v}

/-- The dependent product of the original Law evaluations. -/
def lawObserve (laws : FiniteLawFamily S) (x : S) :
    (law : laws.Law) → laws.Value law :=
  fun law => laws.eval law x

theorem lawObserve_eq_iff (laws : FiniteLawFamily S) (x y : S) :
    lawObserve laws x = lawObserve laws y ↔ laws.Equivalent x y := by
  constructor
  · intro h law
    exact congrFun h law
  · intro h
    funext law
    exact h law

/-- A repair quotient gives an existing Reading on the same source. -/
def RepairQuotient.toReading {T : OperationSystem S E}
    {laws : FiniteLawFamily S} {R : S → S → Prop}
    (q : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) : Reading S where
  Target := q.Target
  read := q.read
  surjective := q.surjective

theorem RepairQuotient.toReading_kernel {T : OperationSystem S E}
    {laws : FiniteLawFamily S} {R : S → S → Prop}
    (q : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) (x y : S) :
    q.toReading.Kernel x y ↔ q.kernel.setoid.r x y := Iff.rfl

/-- These are precisely the existing-Reading conditions needed to recover
the additional repair operations, observation, and request identification. -/
def LawReadingConditions (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop) (q : Reading S) : Prop :=
  (∀ e, q.Factors (fun x => q.read (T.step e x))) ∧
    laws.Adequate q ∧
      ∀ x y, R x y → q.Kernel x y

theorem repair_to_lawReadingConditions (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop)
    (repair : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) :
    LawReadingConditions laws T R repair.toReading := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact ⟨repair.step e, fun x => (repair.step_comm e x).symm⟩
  · intro law
    exact ⟨fun z => repair.observation z law, fun x =>
      congrFun (repair.observation_comm x) law⟩
  · intro x y hxy
    exact repair.identifies x y hxy

/-- Individual Law adequacy constructs descent of the full dependent-product
observation through an existing Reading. -/
theorem lawObserve_factors (laws : FiniteLawFamily S) (q : Reading S)
    (hadequate : laws.Adequate q) : q.Factors (lawObserve laws) := by
  apply (q.factors_iff_kernel (lawObserve laws)).mpr
  intro x y hxy
  apply (lawObserve_eq_iff laws x y).mpr
  exact (laws.adequate_iff_kernel q).mp hadequate hxy

/-- Recover all repair data from Reading factorization and Law adequacy.
No quotient operation or observation is supplied as a conclusion field. -/
noncomputable def lawReadingToRepair (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop) (q : Reading S)
    (h : LawReadingConditions laws T R q) :
    RepairQuotient.{u, v, u, u} T (lawObserve laws) R where
  Target := q.Target
  read := q.read
  surjective := q.surjective
  step := fun e => Classical.choose (h.1 e)
  observation := Classical.choose (lawObserve_factors laws q h.2.1)
  step_comm := by
    intro e x
    exact (Classical.choose_spec (h.1 e) x).symm
  observation_comm := by
    intro x
    exact Classical.choose_spec (lawObserve_factors laws q h.2.1) x
  identifies := h.2.2

theorem lawReadingToRepair_read (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop) (q : Reading S)
    (h : LawReadingConditions laws T R q) (x : S) :
    (lawReadingToRepair laws T R q h).read x = q.read x := rfl

/-- Recovering repair data does not alter the original Reading. -/
theorem lawReadingToRepair_toReading (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop) (q : Reading S)
    (h : LawReadingConditions laws T R q) :
    (lawReadingToRepair laws T R q h).toReading = q := by
  cases q
  rfl

/-- Surjectivity makes the descended operations in the repair round trip unique. -/
theorem repair_lawReading_roundtrip_step (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop)
    (repair : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) :
    (lawReadingToRepair laws T R repair.toReading
      (repair_to_lawReadingConditions laws T R repair)).step = repair.step := by
  let recovered := lawReadingToRepair laws T R repair.toReading
    (repair_to_lawReadingConditions laws T R repair)
  funext e z
  obtain ⟨x, rfl⟩ := repair.surjective z
  exact (recovered.step_comm e x).symm.trans (repair.step_comm e x)

/-- The joint Law observation is also recovered on every target point. -/
theorem repair_lawReading_roundtrip_observation (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop)
    (repair : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) :
    (lawReadingToRepair laws T R repair.toReading
      (repair_to_lawReadingConditions laws T R repair)).observation =
        repair.observation := by
  let recovered := lawReadingToRepair laws T R repair.toReading
    (repair_to_lawReadingConditions laws T R repair)
  funext z
  obtain ⟨x, rfl⟩ := repair.surjective z
  exact (recovered.observation_comm x).trans
    (repair.observation_comm x).symm

/-- The two repairs are related by a source-commuting, operation- and
observation-preserving identity morphism. -/
def repair_lawReading_roundtrip_hom (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop)
    (repair : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) :
    RepairHom T (lawObserve laws) R
      (lawReadingToRepair laws T R repair.toReading
        (repair_to_lawReadingConditions laws T R repair)) repair where
  toFun := id
  source_comm := by intro x; rfl
  step_comm := by
    intro e z
    exact congrFun (congrFun
      (repair_lawReading_roundtrip_step laws T R repair) e) z
  observation_comm := by
    intro z
    exact (congrFun
      (repair_lawReading_roundtrip_observation laws T R repair) z).symm

/-- The reverse identity morphism completes the structure-preserving
round trip on the same target. -/
def repair_lawReading_roundtrip_hom_inv (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop)
    (repair : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) :
    RepairHom T (lawObserve laws) R repair
      (lawReadingToRepair laws T R repair.toReading
        (repair_to_lawReadingConditions laws T R repair)) where
  toFun := id
  source_comm := by intro x; rfl
  step_comm := by
    intro e z
    exact (congrFun (congrFun
      (repair_lawReading_roundtrip_step laws T R repair) e) z).symm
  observation_comm := by
    intro z
    exact congrFun
      (repair_lawReading_roundtrip_observation laws T R repair) z

theorem repair_lawReading_roundtrip_left_inv (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop)
    (repair : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) :
    (repair_lawReading_roundtrip_hom laws T R repair).toFun ∘
      (repair_lawReading_roundtrip_hom_inv laws T R repair).toFun = id := rfl

theorem repair_lawReading_roundtrip_right_inv (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (R : S → S → Prop)
    (repair : RepairQuotient.{u, v, u, u} T (lawObserve laws) R) :
    (repair_lawReading_roundtrip_hom_inv laws T R repair).toFun ∘
      (repair_lawReading_roundtrip_hom laws T R repair).toFun = id := rfl

theorem jointKernel_coarser_of_lawReadingConditions
    (laws : FiniteLawFamily S) (T : OperationSystem S E)
    (R : S → S → Prop) (q : Reading S)
    (h : LawReadingConditions laws T R q) :
    laws.jointKernelReading.CoarserThan q :=
  laws.jointKernel_coarser_of_adequate q h.2.1

theorem jointKernel_factorsThrough_of_lawReadingConditions
    (laws : FiniteLawFamily S) (T : OperationSystem S E)
    (R : S → S → Prop) (q : Reading S)
    (h : LawReadingConditions laws T R q) :
    laws.jointKernelReading.FactorsThrough q :=
  laws.jointKernel_factorsThrough_of_adequate q h.2.1

/-- Stability of the current Law kernel under all named operations. -/
def lawKernelStable (laws : FiniteLawFamily S)
    (T : OperationSystem S E) : Prop :=
  ∀ e x y, laws.Equivalent x y →
    laws.Equivalent (T.step e x) (T.step e y)

theorem behavior_le_lawKernel (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (x y : S)
    (h : (behavior T (lawObserve laws)).setoid.r x y) :
    laws.Equivalent x y :=
  (lawObserve_eq_iff laws x y).mp
    ((behavior_le_kernel T (lawObserve laws)) h)

/-- The future-observation congruence equals the present Law kernel exactly
when that kernel is stable under every named operation. -/
theorem behavior_eq_jointKernel_iff_stable (laws : FiniteLawFamily S)
    (T : OperationSystem S E) :
    (behavior T (lawObserve laws)).setoid = laws.jointKernelSetoid ↔
      lawKernelStable laws T := by
  constructor
  · intro h e x y hxy
    have hb : (behavior T (lawObserve laws)).setoid.r x y := by
      rw [h]
      exact hxy
    have hnext := (behavior T (lawObserve laws)).stable e x y hb
    exact behavior_le_lawKernel laws T _ _ hnext
  · intro hstable
    apply Setoid.ext
    intro x y
    constructor
    · exact behavior_le_lawKernel laws T x y
    · intro hxy
      let c : OperationCongruence T :=
        { setoid := laws.jointKernelSetoid
          stable := hstable }
      have hc : c ≤ behavior T (lawObserve laws) := by
        apply (le_behavior_iff T (lawObserve laws) c).mpr
        intro a b hab
        exact (lawObserve_eq_iff laws a b).mpr hab
      exact hc hxy

/-- Stability is exactly descent of every operation along the existing
joint-kernel Reading. -/
theorem lawKernelStable_iff_jointKernelFactors (laws : FiniteLawFamily S)
    (T : OperationSystem S E) :
    lawKernelStable laws T ↔
      ∀ e, laws.jointKernelReading.Factors
        (fun x => laws.jointKernelReading.read (T.step e x)) := by
  constructor
  · intro hstable e
    apply (laws.jointKernelReading.factors_iff_kernel
      (fun x => laws.jointKernelReading.read (T.step e x))).mpr
    intro x y hxy
    apply (laws.jointKernel_kernel_iff _ _).mpr
    exact hstable e x y ((laws.jointKernel_kernel_iff _ _).mp hxy)
  · intro hfactors e x y hxy
    apply (laws.jointKernel_kernel_iff _ _).mp
    exact ((laws.jointKernelReading.factors_iff_kernel
      (fun z => laws.jointKernelReading.read (T.step e z))).mp
        (hfactors e)) ((laws.jointKernel_kernel_iff _ _).mpr hxy)

/-- GOAL E's three-way criterion for the existing standard Law reading. -/
theorem lawKernel_behavior_stability_descent (laws : FiniteLawFamily S)
    (T : OperationSystem S E) :
    ((behavior T (lawObserve laws)).setoid = laws.jointKernelSetoid ↔
      lawKernelStable laws T) ∧
    (lawKernelStable laws T ↔
      ∀ e, laws.jointKernelReading.Factors
        (fun x => laws.jointKernelReading.read (T.step e x))) :=
  ⟨behavior_eq_jointKernel_iff_stable laws T,
    lawKernelStable_iff_jointKernelFactors laws T⟩

/-- The maximal future-observation quotient as an existing Reading. -/
def betaReading (laws : FiniteLawFamily S)
    (T : OperationSystem S E) : Reading S where
  Target := Quotient (behavior T (lawObserve laws)).setoid
  read := Quotient.mk (behavior T (lawObserve laws)).setoid
  surjective := Quotient.mk_surjective

theorem betaReading_kernel_iff (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (x y : S) :
    (betaReading laws T).Kernel x y ↔
      (behavior T (lawObserve laws)).setoid.r x y := by
  exact Quotient.eq

/-- Every declared Law descends to the future-observation quotient. -/
theorem betaReading_adequate (laws : FiniteLawFamily S)
    (T : OperationSystem S E) : laws.Adequate (betaReading laws T) := by
  apply (laws.adequate_iff_kernel (betaReading laws T)).mpr
  intro x y hxy
  exact behavior_le_lawKernel laws T x y
    ((betaReading_kernel_iff laws T x y).mp hxy)

/-- A specified Law evaluation on the future-observation quotient. -/
def betaLawFactor (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (law : laws.Law) :
    (betaReading laws T).Target → laws.Value law :=
  Quotient.lift (laws.eval law) (by
    intro x y hxy
    exact behavior_le_lawKernel laws T x y hxy law)

@[simp] theorem betaLawFactor_read (laws : FiniteLawFamily S)
    (T : OperationSystem S E) (law : laws.Law) (x : S) :
    betaLawFactor laws T law ((betaReading laws T).read x) =
      laws.eval law x := rfl

/-- The canonical current-Law Reading is coarser than the future-observation
Reading, with the orientation fixed by `Reading.CoarserThan`. -/
theorem jointKernel_coarser_beta (laws : FiniteLawFamily S)
    (T : OperationSystem S E) :
    laws.jointKernelReading.CoarserThan (betaReading laws T) :=
  laws.jointKernel_coarser_of_adequate (betaReading laws T)
    (betaReading_adequate laws T)

theorem jointKernel_factorsThrough_beta (laws : FiniteLawFamily S)
    (T : OperationSystem S E) :
    laws.jointKernelReading.FactorsThrough (betaReading laws T) :=
  laws.jointKernel_factorsThrough_of_adequate (betaReading laws T)
    (betaReading_adequate laws T)

/-- With no operation names, future and present Law equivalence coincide. -/
theorem behavior_eq_jointKernel_of_isEmpty (laws : FiniteLawFamily S)
    (T : OperationSystem S E) [IsEmpty E] :
    (behavior T (lawObserve laws)).setoid = laws.jointKernelSetoid := by
  apply (behavior_eq_jointKernel_iff_stable laws T).mpr
  intro e
  exact isEmptyElim e

/-- The source-commuting comparison with G-103's standard Law quotient when
there are no named operations. -/
def betaJointEquiv_of_isEmpty (laws : FiniteLawFamily S)
    (T : OperationSystem S E) [IsEmpty E] :
    (betaReading laws T).Target ≃ laws.jointKernelReading.Target :=
  Quotient.congrRight (fun x y => by
    rw [behavior_eq_jointKernel_of_isEmpty laws T])

theorem betaJointEquiv_of_isEmpty_comm (laws : FiniteLawFamily S)
    (T : OperationSystem S E) [IsEmpty E] (x : S) :
    betaJointEquiv_of_isEmpty laws T ((betaReading laws T).read x) =
      laws.jointKernelReading.read x := by
  rfl

/-- The empty-operation comparison preserves each original Law evaluation. -/
theorem betaJointEquiv_of_isEmpty_law (laws : FiniteLawFamily S)
    (T : OperationSystem S E) [IsEmpty E] (law : laws.Law)
    (z : (betaReading laws T).Target) :
    laws.jointKernelLawFactor law (betaJointEquiv_of_isEmpty laws T z) =
      betaLawFactor laws T law z := by
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  rw [betaJointEquiv_of_isEmpty_comm]
  rfl

theorem betaJointEquiv_of_isEmpty_unique (laws : FiniteLawFamily S)
    (T : OperationSystem S E) [IsEmpty E]
    (f : (betaReading laws T).Target → laws.jointKernelReading.Target)
    (h : ∀ x, f ((betaReading laws T).read x) =
      laws.jointKernelReading.read x) :
    f = betaJointEquiv_of_isEmpty laws T := by
  funext z
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  exact (h x).trans (betaJointEquiv_of_isEmpty_comm laws T x).symm

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
