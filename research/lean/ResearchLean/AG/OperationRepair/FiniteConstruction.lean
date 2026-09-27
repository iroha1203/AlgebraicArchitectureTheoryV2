import ResearchLean.AG.OperationRepair.FiniteClosure
import ResearchLean.AG.OperationRepair.FiniteBehavior
import ResearchLean.AG.OperationRepair.FiniteRamEnumeration
import ResearchLean.AG.OperationRepair.FiniteRamUpper
import ResearchLean.AG.OperationRepair.FiniteRamDecision
import ResearchLean.AG.OperationRepair.Classification
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max

/-!
# Numbered classes from computed Boolean endpoint tables

The representative of a state is the least numbered state in its computed
equivalence class. Class IDs enumerate the distinct representatives in order.
No state is chosen for an empty input.
-/

namespace AAT.AG.OperationRepair

namespace FiniteConstruction

variable {n m : Nat} {O : Type*} [DecidableEq O]

/-- A Boolean equivalence table with its laws proved from the computation.
This structure is constructed internally, never supplied as a raw input. -/
structure PartitionTable (n : Nat) where
  cells : RelationTable n
  refl : ∀ x, cells.get x x = true
  symm : ∀ x y, cells.get x y = true → cells.get y x = true
  trans : ∀ x y z, cells.get x y = true → cells.get y z = true →
    cells.get x z = true

namespace PartitionTable

variable (p : PartitionTable n)

@[ext] theorem ext {a b : PartitionTable n} (h : a.cells = b.cells) : a = b := by
  cases a with
  | mk ac ar asym atr =>
    cases b with
    | mk bc br bsym btr =>
      cases h
      rfl

def classSet (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun y => p.cells.get y x

theorem self_mem_classSet (x : Fin n) : x ∈ p.classSet x := by
  simp [classSet, p.refl]

/-- The least state number in an equivalence class. -/
def rep (x : Fin n) : Fin n :=
  (p.classSet x).min' ⟨x, p.self_mem_classSet x⟩

theorem rep_related (x : Fin n) : p.cells.get (p.rep x) x = true := by
  have h := Finset.min'_mem (p.classSet x) ⟨x, p.self_mem_classSet x⟩
  simpa [classSet] using h

theorem classSet_eq_of_related {x y : Fin n}
    (hxy : p.cells.get x y = true) : p.classSet x = p.classSet y := by
  ext z
  simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hzx
    exact p.trans z x y hzx hxy
  · intro hzy
    exact p.trans z y x hzy (p.symm x y hxy)

theorem rep_eq_iff {x y : Fin n} :
    p.rep x = p.rep y ↔ p.cells.get x y = true := by
  constructor
  · intro h
    have hx : p.cells.get x (p.rep x) = true :=
      p.symm _ _ (p.rep_related x)
    exact p.trans x (p.rep x) y hx (h ▸ p.rep_related y)
  · intro h
    simp [rep, p.classSet_eq_of_related h]

theorem rep_idempotent (x : Fin n) : p.rep (p.rep x) = p.rep x := by
  exact p.rep_eq_iff.mpr (p.rep_related x)

/-- The distinct least representatives, computed from all input states. -/
def representatives : Finset (Fin n) := Finset.univ.image p.rep

theorem rep_mem_representatives (x : Fin n) : p.rep x ∈ p.representatives := by
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

def classCount : Nat := p.representatives.card

/-- Ordered class numbers and a concrete section table. -/
def orderClasses : Fin p.classCount ≃o p.representatives :=
  Finset.orderIsoOfFin p.representatives rfl

def classSection (c : Fin p.classCount) : Fin n := (p.orderClasses c).val

def quotient (x : Fin n) : Fin p.classCount :=
  p.orderClasses.symm ⟨p.rep x, p.rep_mem_representatives x⟩

theorem section_quotient (x : Fin n) :
    p.classSection (p.quotient x) = p.rep x := by
  simp [classSection, quotient]

theorem quotient_section (c : Fin p.classCount) :
    p.quotient (p.classSection c) = c := by
  apply p.orderClasses.injective
  apply Subtype.ext
  simp only [quotient, classSection, OrderIso.apply_symm_apply]
  change p.rep (p.orderClasses c).val = (p.orderClasses c).val
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp (p.orderClasses c).property
  rw [← hz]
  exact p.rep_idempotent z

theorem quotient_eq_iff (x y : Fin n) :
    p.quotient x = p.quotient y ↔ p.cells.get x y = true := by
  rw [← p.rep_eq_iff]
  constructor
  · intro h
    have h' := congrArg p.classSection h
    simpa [p.section_quotient] using h'
  · intro h
    simp [quotient, h]

theorem quotient_surjective : Function.Surjective p.quotient := by
  intro c
  exact ⟨p.classSection c, p.quotient_section c⟩

/-- A concrete first-isomorphism equivalence using the computed section. -/
def standardEquiv : Quotient (Setoid.ker p.quotient) ≃ Fin p.classCount :=
  Setoid.quotientKerEquivOfRightInverse (f := p.quotient)
    p.classSection p.quotient_section

@[simp] theorem standardEquiv_mk (x : Fin n) :
    p.standardEquiv (Quotient.mk (Setoid.ker p.quotient) x) = p.quotient x := by
  rfl

theorem quotient_section_related (x : Fin n) :
    p.cells.get x (p.classSection (p.quotient x)) = true := by
  rw [p.section_quotient]
  exact p.symm _ _ (p.rep_related x)

end PartitionTable

/-- The lower partition table is assembled from the proved closure loop. -/
def lowerPartition (input : FiniteRepairInput n m O) : PartitionTable n where
  cells := FiniteClosure.lower input
  refl := FiniteClosure.lower_refl input
  symm := fun _ _ h => FiniteClosure.lower_symm input h
  trans := fun _ _ _ h₁ h₂ => FiniteClosure.lower_trans input h₁ h₂

/-- The upper partition table is assembled from the proved stored-word loop. -/
def upperCells (input : FiniteRepairInput n m O) : RelationTable n :=
  FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    (FiniteBehavior.get (FiniteBehavior.upper input) x y).isNone

theorem upperCells_iff (input : FiniteRepairInput n m O) (x y : Fin n) :
    (upperCells input).get x y = true ↔ FiniteBehavior.upperRel input x y := by
  simp [upperCells, RelationTable.get, FiniteBehavior.upperRel]

def upperPartition (input : FiniteRepairInput n m O) : PartitionTable n where
  cells := upperCells input
  refl := by
    intro x
    exact (upperCells_iff input x x).mpr
      ((FiniteBehavior.computedUpper_iff_behavior input x x).mpr
        ((behavior input.system input.observe).setoid.refl x))
  symm := by
    intro x y h
    apply (upperCells_iff input y x).mpr
    exact (FiniteBehavior.computedUpper_iff_behavior input y x).mpr
      (((FiniteBehavior.computedUpper_iff_behavior input x y).mp
        ((upperCells_iff input x y).mp h)).symm)
  trans := by
    intro x y z hxy hyz
    apply (upperCells_iff input x z).mpr
    exact (FiniteBehavior.computedUpper_iff_behavior input x z).mpr
      (((FiniteBehavior.computedUpper_iff_behavior input x y).mp
        ((upperCells_iff input x y).mp hxy)).trans
        ((FiniteBehavior.computedUpper_iff_behavior input y z).mp
          ((upperCells_iff input y z).mp hyz)))

/-- Numbered quotient operation table, from the chosen class section. -/
def quotientOperationTable (input : FiniteRepairInput n m O)
    (p : PartitionTable n) :
    FiniteTable (FiniteTable (Fin p.classCount) p.classCount) m :=
  FiniteTable.ofFn fun e => FiniteTable.ofFn fun c =>
    p.quotient (input.step e (p.classSection c))

/-- Numbered quotient observation table. -/
def quotientObservationTable (input : FiniteRepairInput n m O)
    (p : PartitionTable n) : FiniteTable O p.classCount :=
  FiniteTable.ofFn fun c => input.observe (p.classSection c)

/-- The explicit surjective table from states to class numbers. -/
def quotientMapTable (p : PartitionTable n) :
    FiniteTable (Fin p.classCount) n := FiniteTable.ofFn p.quotient

theorem quotientOperation_comm (input : FiniteRepairInput n m O)
    (p : PartitionTable n)
    (stable : ∀ e x y, p.cells.get x y = true →
      p.cells.get (input.step e x) (input.step e y) = true)
    (e : Fin m) (x : Fin n) :
    (FiniteTable.get (quotientOperationTable input p) e).get (p.quotient x) =
      p.quotient (input.step e x) := by
  simp only [quotientOperationTable, FiniteTable.get_ofFn]
  apply (p.quotient_eq_iff _ _).mpr
  exact p.symm _ _ (stable e x _ (p.quotient_section_related x))

theorem quotientObservation_comm (input : FiniteRepairInput n m O)
    (p : PartitionTable n)
    (compatible : ∀ x y, p.cells.get x y = true →
      input.observe x = input.observe y)
    (x : Fin n) :
    (quotientObservationTable input p).get (p.quotient x) =
      input.observe x := by
  simp only [quotientObservationTable, FiniteTable.get_ofFn]
  exact (compatible x _ (p.quotient_section_related x)).symm

/-- The same numbered standard-quotient equivalence intertwines the
operation induced on classes and the returned operation table. -/
theorem standardEquiv_operation_comm (input : FiniteRepairInput n m O)
    (p : PartitionTable n)
    (stable : ∀ e x y, p.cells.get x y = true →
      p.cells.get (input.step e x) (input.step e y) = true)
    (e : Fin m) (x : Fin n) :
    (FiniteTable.get (quotientOperationTable input p) e).get
      (p.standardEquiv (Quotient.mk (Setoid.ker p.quotient) x)) =
      p.standardEquiv (Quotient.mk (Setoid.ker p.quotient)
        (input.step e x)) := by
  simpa only [p.standardEquiv_mk] using quotientOperation_comm input p stable e x

/-- The same equivalence also intertwines the induced observation. -/
theorem standardEquiv_observation_comm (input : FiniteRepairInput n m O)
    (p : PartitionTable n)
    (compatible : ∀ x y, p.cells.get x y = true →
      input.observe x = input.observe y)
    (x : Fin n) :
    (quotientObservationTable input p).get
      (p.standardEquiv (Quotient.mk (Setoid.ker p.quotient) x)) =
      input.observe x := by
  simpa only [p.standardEquiv_mk] using
    quotientObservation_comm input p compatible x

/-- Scan the original requested pairs, retaining the first already computed
upper-table witness. No search for a new word occurs here. -/
def failureSearchFrom (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    Option (Fin n × Fin n × List (Fin m)) :=
  (FiniteClosure.pairs n).findSome? fun p =>
    if input.wants p.1 p.2 then
      (FiniteBehavior.get upperWords p.1 p.2).map
        (fun word => (p.1, p.2, word))
    else none

def failureSearch (input : FiniteRepairInput n m O) :
    Option (Fin n × Fin n × List (Fin m)) :=
  failureSearchFrom input (FiniteBehavior.upper input)

theorem failureSearch_sound (input : FiniteRepairInput n m O)
    {x y : Fin n} {word : List (Fin m)}
    (h : failureSearch input = some (x, y, word)) :
    input.requestRel x y ∧ word.length < n * n ∧
      FiniteBehavior.separates input x y word := by
  obtain ⟨p, _, hp⟩ := List.exists_of_findSome?_eq_some h
  rcases p with ⟨a, b⟩
  simp only [failureSearch, failureSearchFrom] at h
  by_cases hwant : input.wants a b = true
  · simp only [hwant, ↓reduceIte] at hp
    cases hword : FiniteBehavior.get (FiniteBehavior.upper input) a b with
    | none => simp [hword] at hp
    | some w =>
        have heq : a = x ∧ b = y ∧ w = word := by simpa [hword] using hp
        rcases heq with ⟨rfl, rfl, rfl⟩
        exact ⟨hwant, FiniteBehavior.upper_some_certificate input a b w hword⟩
  · have hf : input.wants a b = false := Bool.eq_false_iff.mpr hwant
    simp [hf] at hp

theorem failureSearch_none (input : FiniteRepairInput n m O)
    (h : failureSearch input = none) :
    ∀ x y, input.requestRel x y →
      (behavior input.system input.observe).setoid.r x y := by
  intro x y hR
  have hpair := (List.findSome?_eq_none_iff.mp h) (x, y)
    (FiniteClosure.mem_pairs x y)
  have hyes : input.wants x y = true := hR
  simp only [failureSearch, failureSearchFrom, hyes, ↓reduceIte] at hpair
  have hnone : FiniteBehavior.get (FiniteBehavior.upper input) x y = none := by
    cases hw : FiniteBehavior.get (FiniteBehavior.upper input) x y with
    | none => rfl
    | some word => simp [hw] at hpair
  exact (FiniteBehavior.computedUpper_iff_behavior input x y).mp hnone

/-- On a successful search, the computed lower relation lies inside the
computed upper relation. -/
theorem lower_le_upper (input : FiniteRepairInput n m O)
    (h : failureSearch input = none) (x y : Fin n)
    (hxy : (lowerPartition input).cells.get x y = true) :
    (upperPartition input).cells.get x y = true := by
  have hgb : generated input.system input.requestRel ≤
      behavior input.system input.observe :=
    (generated_le_behavior_iff input.system input.observe input.requestRel).mpr
      (failureSearch_none input h)
  have hgen : (generated input.system input.requestRel).setoid.r x y := by
    rw [← FiniteClosure.computedLower_eq_generated]
    exact hxy
  exact (upperCells_iff input x y).mpr
    ((FiniteBehavior.computedUpper_iff_behavior input x y).mpr (hgb hgen))

/-- The table from lower class numbers to upper class numbers. -/
def lowerToUpperTable (input : FiniteRepairInput n m O) :
    FiniteTable (Fin (upperPartition input).classCount)
      (lowerPartition input).classCount :=
  FiniteTable.ofFn fun c =>
    (upperPartition input).quotient ((lowerPartition input).classSection c)

theorem lowerToUpper_comm (input : FiniteRepairInput n m O)
    (h : failureSearch input = none) (x : Fin n) :
    (lowerToUpperTable input).get ((lowerPartition input).quotient x) =
      (upperPartition input).quotient x := by
  simp only [lowerToUpperTable, FiniteTable.get_ofFn]
  apply ((upperPartition input).quotient_eq_iff _ _).mpr
  apply lower_le_upper input h
  exact (lowerPartition input).symm _ _
    ((lowerPartition input).quotient_section_related x)

/-- Finite output tables with explicit class numbering and a section. -/
structure NumberedQuotientTables (n m : Nat) (O : Type*) where
  classCount : Nat
  map : FiniteTable (Fin classCount) n
  sectionTable : FiniteTable (Fin n) classCount
  operations : FiniteTable (FiniteTable (Fin classCount) classCount) m
  observations : FiniteTable O classCount

def makeNumberedTables (input : FiniteRepairInput n m O)
    (p : PartitionTable n) : NumberedQuotientTables n m O where
  classCount := p.classCount
  map := quotientMapTable p
  sectionTable := FiniteTable.ofFn p.classSection
  operations := quotientOperationTable input p
  observations := quotientObservationTable input p

structure SuccessTables (n m : Nat) (O : Type*) where
  lower : NumberedQuotientTables n m O
  upper : NumberedQuotientTables n m O
  lowerToUpper : FiniteTable (Fin upper.classCount) lower.classCount

def makeSuccessTables (input : FiniteRepairInput n m O) :
    SuccessTables n m O where
  lower := makeNumberedTables input (lowerPartition input)
  upper := makeNumberedTables input (upperPartition input)
  lowerToUpper := lowerToUpperTable input

def makeSuccessTablesFrom (input : FiniteRepairInput n m O)
    (lowerPart upperPart : PartitionTable n) : SuccessTables n m O where
  lower := makeNumberedTables input lowerPart
  upper := makeNumberedTables input upperPart
  lowerToUpper := FiniteTable.ofFn fun c =>
    upperPart.quotient (lowerPart.classSection c)

/-- Package an already computed lower table; proof fields erase at runtime. -/
def lowerPartitionFrom (input : FiniteRepairInput n m O)
    (cells : RelationTable n) (h : cells = FiniteClosure.lower input) :
    PartitionTable n where
  cells := cells
  refl := by intro x; rw [h]; exact FiniteClosure.lower_refl input x
  symm := by intro x y hxy; rw [h] at hxy ⊢; exact FiniteClosure.lower_symm input hxy
  trans := by
    intro x y z hxy hyz
    rw [h] at hxy hyz ⊢
    exact FiniteClosure.lower_trans input hxy hyz

/-- Package an already computed upper word table into its Boolean partition. -/
def upperPartitionFrom (input : FiniteRepairInput n m O)
    (words : FiniteBehavior.WitnessTable n m)
    (h : words = FiniteBehavior.upper input) : PartitionTable n where
  cells := FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    (FiniteBehavior.get words x y).isNone
  refl := by
    intro x
    rw [h]
    exact (upperPartition input).refl x
  symm := by
    intro x y hxy
    rw [h] at hxy ⊢
    exact (upperPartition input).symm x y hxy
  trans := by
    intro x y z hxy hyz
    rw [h] at hxy hyz ⊢
    exact (upperPartition input).trans x y z hxy hyz

/-- Shared raw endpoints and one success/failure outcome. -/
structure RunOutput (n m : Nat) (O : Type*) where
  lowerCells : RelationTable n
  upperWords : FiniteBehavior.WitnessTable n m
  outcome : Sum (Fin n × Fin n × List (Fin m)) (SuccessTables n m O)

/-- The counted lower value supplies the same proved partition as the
canonical lower table. This identifies the actual table and its proof fields. -/
theorem lowerPartitionFrom_counted_eq (input : FiniteRepairInput n m O) :
    lowerPartitionFrom input (FiniteRamEnumeration.lower input).value
        (FiniteRamEnumeration.lower_value input) =
      lowerPartitionFrom input (FiniteClosure.lower input) rfl := by
  apply PartitionTable.ext
  exact FiniteRamEnumeration.lower_value input

theorem upperPartitionFrom_counted_eq (input : FiniteRepairInput n m O) :
    upperPartitionFrom input (FiniteRamUpper.upper input).value
        (FiniteRamUpper.upper_value input) =
      upperPartitionFrom input (FiniteBehavior.upper input) rfl := by
  apply PartitionTable.ext
  simp [upperPartitionFrom, FiniteRamUpper.upper_value]

theorem countedDecision_value (input : FiniteRepairInput n m O)
    (words : FiniteBehavior.WitnessTable n m) :
    (FiniteRamDecision.decision input words).value =
      failureSearchFrom input words := by
  exact FiniteRamDecision.decision_value input words

/-- One terminating finite program. It computes both endpoints once, then
uses the stored upper witnesses to choose a failure or numbered success. -/
def runRepair (input : FiniteRepairInput n m O) : RunOutput n m O :=
  let lowerCells := (FiniteRamEnumeration.lower input).value
  let upperWords := (FiniteRamUpper.upper input).value
  let lowerPart := lowerPartitionFrom input lowerCells
    (FiniteRamEnumeration.lower_value input)
  let upperPart := upperPartitionFrom input upperWords
    (FiniteRamUpper.upper_value input)
  let decision := FiniteRamDecision.decision input upperWords
  let outcome := match decision.value with
    | some bad => Sum.inl bad
    | none => Sum.inr (makeSuccessTablesFrom input lowerPart upperPart)
  ⟨lowerCells, upperWords, outcome⟩

@[simp] theorem runRepair_lowerCells (input : FiniteRepairInput n m O) :
    (runRepair input).lowerCells = FiniteClosure.lower input :=
  FiniteRamEnumeration.lower_value input

/-- The lower table actually used by `runRepair` is the counted lower value;
its trace has a uniform bound. This concerns the lower stage only. -/
theorem runRepair_lower_counted (input : FiniteRepairInput n m O) :
    (runRepair input).lowerCells =
        (FiniteRamEnumeration.lower input).value ∧
      (FiniteRamEnumeration.lower input).cost ≤
        600 * (m + 1) * (n + 1) ^ 5 := by
  exact ⟨rfl, FiniteRamEnumeration.lower_cost_poly input⟩

@[simp] theorem runRepair_upperWords (input : FiniteRepairInput n m O) :
    (runRepair input).upperWords = FiniteBehavior.upper input :=
  FiniteRamUpper.upper_value input

theorem runRepair_upper_counted (input : FiniteRepairInput n m O) :
    (runRepair input).upperWords = (FiniteRamUpper.upper input).value ∧
      (FiniteRamUpper.upper input).cost ≤
        60 * (m + 1) * (n + 1) ^ 4 := by
  exact ⟨rfl, FiniteRamUpper.upper_cost_le input⟩

theorem runRepair_decision_counted (input : FiniteRepairInput n m O) :
    (FiniteRamDecision.decision input (runRepair input).upperWords).cost ≤
      30 * (n + 1) ^ 2 :=
  FiniteRamDecision.decision_cost_le input _

theorem runRepair_failure (input : FiniteRepairInput n m O)
    (x y : Fin n) (word : List (Fin m))
    (h : (runRepair input).outcome = Sum.inl (x, y, word)) :
    input.requestRel x y ∧ word.length < n * n ∧
      FiniteBehavior.separates input x y word := by
  unfold runRepair at h
  simp only [countedDecision_value, FiniteRamUpper.upper_value] at h
  cases hs : failureSearchFrom input (FiniteBehavior.upper input) with
  | none => simp [hs] at h
  | some bad =>
      simp [hs] at h
      subst bad
      exact failureSearch_sound input hs

theorem runRepair_success_iff (input : FiniteRepairInput n m O) :
    (∃ tables : SuccessTables n m O,
      (runRepair input).outcome = Sum.inr tables) ↔
      ∀ x y, input.requestRel x y →
        (behavior input.system input.observe).setoid.r x y := by
  constructor
  · rintro ⟨tables, htables⟩
    unfold runRepair at htables
    simp only [countedDecision_value, FiniteRamUpper.upper_value] at htables
    cases hs : failureSearchFrom input (FiniteBehavior.upper input) with
    | some bad => simp [hs] at htables
    | none => exact failureSearch_none input hs
  · intro hgood
    by_cases hnone : failureSearch input = none
    · refine ⟨makeSuccessTablesFrom input
        (lowerPartitionFrom input (FiniteClosure.lower input) rfl)
        (upperPartitionFrom input (FiniteBehavior.upper input) rfl), ?_⟩
      change failureSearchFrom input (FiniteBehavior.upper input) = none at hnone
      simp [runRepair, hnone, countedDecision_value,
        FiniteRamUpper.upper_value input,
        lowerPartitionFrom_counted_eq input,
        upperPartitionFrom_counted_eq input]
    · cases hs : failureSearch input with
      | none => contradiction
      | some bad =>
          rcases bad with ⟨x, y, word⟩
          obtain ⟨hr, _, hsep⟩ := failureSearch_sound input hs
          exact False.elim (hsep ((behavior_iff input.system input.observe x y).mp
            (hgood x y hr) word))

/-- The executable branch decision agrees with B's repair existence
classification, with no finite-observation assumption. -/
theorem runRepair_success_iff_repair_exists
    (input : FiniteRepairInput n m O) :
    (∃ tables : SuccessTables n m O,
      (runRepair input).outcome = Sum.inr tables) ↔
      Nonempty (RepairQuotient.{0, 0, _, 0} input.system input.observe
        input.requestRel) := by
  rw [runRepair_success_iff]
  exact (repair_exists_iff_request_behavior input.system input.observe
    input.requestRel).symm

theorem lowerPartitionFrom_eq (input : FiniteRepairInput n m O) :
    lowerPartitionFrom input (FiniteClosure.lower input) rfl =
      lowerPartition input := by
  apply PartitionTable.ext
  rfl

theorem upperPartitionFrom_eq (input : FiniteRepairInput n m O) :
    upperPartitionFrom input (FiniteBehavior.upper input) rfl =
      upperPartition input := by
  apply PartitionTable.ext
  rfl

theorem makeSuccessTablesFrom_eq (input : FiniteRepairInput n m O) :
    makeSuccessTablesFrom input (lowerPartition input) (upperPartition input) =
      makeSuccessTables input := by
  rfl

/-- A success branch contains exactly the numbered tables built from the
two proved endpoint partitions, rather than a selected external quotient. -/
theorem runRepair_success_payload (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    tables = makeSuccessTables input := by
  unfold runRepair at h
  simp only [countedDecision_value, FiniteRamUpper.upper_value] at h
  cases hs : failureSearchFrom input (FiniteBehavior.upper input) with
  | some bad => simp [hs] at h
  | none =>
      simp [hs] at h
      subst tables
      rw [lowerPartitionFrom_counted_eq, lowerPartitionFrom_eq, upperPartitionFrom_eq]
      exact makeSuccessTablesFrom_eq input

theorem success_failureSearch_none (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    failureSearch input = none := by
  unfold runRepair at h
  simp only [countedDecision_value, FiniteRamUpper.upper_value] at h
  cases hs : failureSearchFrom input (FiniteBehavior.upper input) with
  | none => exact hs
  | some bad => simp [hs] at h

theorem lower_observation_compatible (input : FiniteRepairInput n m O)
    (h : failureSearch input = none) (x y : Fin n)
    (hxy : (lowerPartition input).cells.get x y = true) :
    input.observe x = input.observe y := by
  have hUpper := lower_le_upper input h x y hxy
  have hBehavior := (FiniteBehavior.computedUpper_iff_behavior input x y).mp
    ((upperCells_iff input x y).mp hUpper)
  exact behavior_le_kernel input.system input.observe hBehavior

theorem upper_observation_compatible (input : FiniteRepairInput n m O)
    (x y : Fin n) (hxy : (upperPartition input).cells.get x y = true) :
    input.observe x = input.observe y := by
  have hBehavior := (FiniteBehavior.computedUpper_iff_behavior input x y).mp
    ((upperCells_iff input x y).mp hxy)
  exact behavior_le_kernel input.system input.observe hBehavior

theorem upper_operation_stable (input : FiniteRepairInput n m O)
    (e : Fin m) (x y : Fin n)
    (hxy : (upperPartition input).cells.get x y = true) :
    (upperPartition input).cells.get (input.step e x) (input.step e y) = true := by
  apply (upperCells_iff input _ _).mpr
  apply (FiniteBehavior.computedUpper_iff_behavior input _ _).mpr
  exact (behavior input.system input.observe).stable e x y
    ((FiniteBehavior.computedUpper_iff_behavior input x y).mp
      ((upperCells_iff input x y).mp hxy))

theorem success_lower_map_kernel (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) (x y : Fin n) :
    tables.lower.map.get x = tables.lower.map.get y ↔
      (generated input.system input.requestRel).setoid.r x y := by
  rw [runRepair_success_payload input tables h]
  simp only [makeSuccessTables, makeNumberedTables, quotientMapTable,
    FiniteTable.get_ofFn]
  rw [(lowerPartition input).quotient_eq_iff]
  rw [← FiniteClosure.computedLower_eq_generated]
  rfl

theorem success_upper_map_kernel (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) (x y : Fin n) :
    tables.upper.map.get x = tables.upper.map.get y ↔
      (behavior input.system input.observe).setoid.r x y := by
  rw [runRepair_success_payload input tables h]
  simp only [makeSuccessTables, makeNumberedTables, quotientMapTable,
    FiniteTable.get_ofFn]
  rw [(upperPartition input).quotient_eq_iff]
  exact (upperCells_iff input x y).trans
    (FiniteBehavior.computedUpper_iff_behavior input x y)

theorem success_lower_operation_comm (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables)
    (e : Fin m) (x : Fin n) :
    (tables.lower.operations.get e).get (tables.lower.map.get x) =
      tables.lower.map.get (input.step e x) := by
  rw [runRepair_success_payload input tables h]
  simp only [makeSuccessTables, makeNumberedTables, quotientMapTable,
    FiniteTable.get_ofFn]
  exact quotientOperation_comm input (lowerPartition input)
    (fun e x y hxy => FiniteClosure.lower_stable input e hxy) e x

theorem success_upper_operation_comm (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables)
    (e : Fin m) (x : Fin n) :
    (tables.upper.operations.get e).get (tables.upper.map.get x) =
      tables.upper.map.get (input.step e x) := by
  rw [runRepair_success_payload input tables h]
  simp only [makeSuccessTables, makeNumberedTables, quotientMapTable,
    FiniteTable.get_ofFn]
  exact quotientOperation_comm input (upperPartition input)
    (fun e x y hxy => upper_operation_stable input e x y hxy) e x

theorem success_lower_observation_comm (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) (x : Fin n) :
    tables.lower.observations.get (tables.lower.map.get x) = input.observe x := by
  have hnone := success_failureSearch_none input tables h
  rw [runRepair_success_payload input tables h]
  simp only [makeSuccessTables, makeNumberedTables, quotientMapTable,
    FiniteTable.get_ofFn]
  exact quotientObservation_comm input (lowerPartition input)
    (lower_observation_compatible input hnone) x

theorem success_upper_observation_comm (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) (x : Fin n) :
    tables.upper.observations.get (tables.upper.map.get x) = input.observe x := by
  rw [runRepair_success_payload input tables h]
  simp only [makeSuccessTables, makeNumberedTables, quotientMapTable,
    FiniteTable.get_ofFn]
  exact quotientObservation_comm input (upperPartition input)
    (upper_observation_compatible input) x

theorem success_factor_comm (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) (x : Fin n) :
    tables.lowerToUpper.get (tables.lower.map.get x) =
      tables.upper.map.get x := by
  have hnone := success_failureSearch_none input tables h
  rw [runRepair_success_payload input tables h]
  simp only [makeSuccessTables, makeNumberedTables, quotientMapTable,
    FiniteTable.get_ofFn]
  exact lowerToUpper_comm input hnone x

theorem success_lower_map_surjective (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    Function.Surjective (fun x : Fin n => tables.lower.map.get x) := by
  rw [runRepair_success_payload input tables h]
  simpa [makeSuccessTables, makeNumberedTables, quotientMapTable] using
    (lowerPartition input).quotient_surjective

theorem success_upper_map_surjective (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    Function.Surjective (fun x : Fin n => tables.upper.map.get x) := by
  rw [runRepair_success_payload input tables h]
  simpa [makeSuccessTables, makeNumberedTables, quotientMapTable] using
    (upperPartition input).quotient_surjective

theorem success_factor_operation_comm (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables)
    (e : Fin m) (c : Fin tables.lower.classCount) :
    tables.lowerToUpper.get ((tables.lower.operations.get e).get c) =
      (tables.upper.operations.get e).get (tables.lowerToUpper.get c) := by
  obtain ⟨x, hx⟩ := success_lower_map_surjective input tables h c
  change tables.lower.map.get x = c at hx
  rw [← hx, success_lower_operation_comm input tables h,
    success_factor_comm input tables h (input.step e x),
    success_factor_comm input tables h x,
    success_upper_operation_comm input tables h]

theorem success_factor_observation_comm (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables)
    (c : Fin tables.lower.classCount) :
    tables.upper.observations.get (tables.lowerToUpper.get c) =
      tables.lower.observations.get c := by
  obtain ⟨x, hx⟩ := success_lower_map_surjective input tables h c
  rw [← hx, success_factor_comm input tables h,
    success_lower_observation_comm input tables h,
    success_upper_observation_comm input tables h]

/-- The success output itself supplies B's finest repair quotient, with
numbered carrier and the actual returned operation/observation tables. -/
def successLowerRepair (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    RepairQuotient input.system input.observe input.requestRel where
  Target := Fin tables.lower.classCount
  read := fun x => tables.lower.map.get x
  surjective := success_lower_map_surjective input tables h
  step := fun e c => (tables.lower.operations.get e).get c
  observation := fun c => tables.lower.observations.get c
  step_comm := by
    intro e x
    exact (success_lower_operation_comm input tables h e x).symm
  observation_comm := success_lower_observation_comm input tables h
  identifies := by
    intro x y hr
    exact (success_lower_map_kernel input tables h x y).mpr
      (generated_contains input.system hr)

/-- The success output also supplies B's coarsest repair quotient. -/
def successUpperRepair (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    RepairQuotient input.system input.observe input.requestRel where
  Target := Fin tables.upper.classCount
  read := fun x => tables.upper.map.get x
  surjective := success_upper_map_surjective input tables h
  step := fun e c => (tables.upper.operations.get e).get c
  observation := fun c => tables.upper.observations.get c
  step_comm := by
    intro e x
    exact (success_upper_operation_comm input tables h e x).symm
  observation_comm := success_upper_observation_comm input tables h
  identifies := by
    intro x y hr
    exact (success_upper_map_kernel input tables h x y).mpr
      ((failureSearch_none input (success_failureSearch_none input tables h)) x y hr)

/-- The returned factor table is precisely the B morphism from the finest
to the coarsest numbered repair quotient. -/
def successFactorHom (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    RepairHom input.system input.observe input.requestRel
      (successLowerRepair input tables h) (successUpperRepair input tables h) where
  toFun := fun c => tables.lowerToUpper.get c
  source_comm := success_factor_comm input tables h
  step_comm := success_factor_operation_comm input tables h
  observation_comm := success_factor_observation_comm input tables h

theorem successLowerRepair_kernel_eq (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    (successLowerRepair input tables h).kernel =
      generated input.system input.requestRel := by
  apply OperationCongruence.ext
  apply Setoid.ext
  intro x y
  exact success_lower_map_kernel input tables h x y

theorem successUpperRepair_kernel_eq (input : FiniteRepairInput n m O)
    (tables : SuccessTables n m O)
    (h : (runRepair input).outcome = Sum.inr tables) :
    (successUpperRepair input tables h).kernel =
      behavior input.system input.observe := by
  apply OperationCongruence.ext
  apply Setoid.ext
  intro x y
  exact success_upper_map_kernel input tables h x y

/-- Failure is returned exactly when no repair quotient exists, and the
failure branch has the concrete original request pair and short word above. -/
theorem runRepair_failure_iff_no_repair (input : FiniteRepairInput n m O) :
    (∃ x y : Fin n, ∃ word : List (Fin m),
      (runRepair input).outcome = Sum.inl (x, y, word)) ↔
      ¬ Nonempty (RepairQuotient.{0, 0, _, 0} input.system
        input.observe input.requestRel) := by
  constructor
  · rintro ⟨x, y, word, hfail⟩ hexists
    obtain ⟨tables, hsuccess⟩ :=
      (runRepair_success_iff_repair_exists input).mpr hexists
    rw [hfail] at hsuccess
    cases hsuccess
  · intro hno
    cases hres : (runRepair input).outcome with
    | inl bad =>
        rcases bad with ⟨x, y, word⟩
        exact ⟨x, y, word, rfl⟩
    | inr tables =>
        exact False.elim (hno ((runRepair_success_iff_repair_exists input).mp
          ⟨tables, hres⟩))

end FiniteConstruction

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
