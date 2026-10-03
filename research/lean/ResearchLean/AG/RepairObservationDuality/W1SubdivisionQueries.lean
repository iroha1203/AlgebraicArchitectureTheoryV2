import ResearchLean.AG.RepairObservationDuality.W1GeneratedNumericalPlan
import ResearchLean.AG.RepairObservationDuality.W1GeneratedDecisionPlan
import ResearchLean.AG.RepairObservationDuality.PrimitiveOutputMap
import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionCoordinates

/-!
# G-131 E: full subdivision outputs with unchanged actual queries and costs

## Implementation notes

The five numerical values are u,z,v,alpha,beta. Numeric collapse reads
h=beta-alpha. For any known r, extension returns the complete tuple
(u,z,v,r,h+r). Total maps on procedures preserve the actual ordered replies
and costs in both directions. The fixed-r map is not asserted to be a
bijection onto arbitrary split answers. G-130 reconstructs every valid tuple
as an actual supported repair of the same independently specified split tower.
-/
namespace AAT.AG.RepairObservationDuality.W1SubdivisionQueries
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open RelativeRepairComposition W1AffineInput W1Regions W1ActualRepairs W1SubdivisionInput
open W1PhysicalInputs W1NumericalEquation PrimitiveQueries
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

/-- All five original surviving and factor numerical correction values. -/
abbrev SplitCorrections := Fin 5 → ZMod 3

/-- Numeric collapse keeps u,z,v and the entire old h=beta-alpha. -/
def collapse (b : SplitCorrections) : Corrections := ![b 0,b 4 - b 3,b 1,b 2]

/-- Any known full first-factor value extends every whole old numerical answer. -/
def extend (r : ZMod 3) (a : Corrections) : SplitCorrections := ![a 0,a 2,a 3,r,a 1 + r]

/-- Every known-r extension collapses to the full original numerical correction. -/
theorem collapse_extend (r : ZMod 3) (a : Corrections) : collapse (extend r a) = a := by
  ext i
  fin_cases i <;> simp [collapse,extend]

/-- The actual first factor of every full split tuple restores that entire tuple under extension. -/
theorem extend_collapse (b : SplitCorrections) : extend (b 3) (collapse b) = b := by
  ext i
  fin_cases i <;> simp [collapse,extend]

/-- A fully acquired split numerical answer obeys the same independent authored Laws and original masks after numeric collapse. -/
def ValidSplit (p : Permissions) (v : Values) (out : Option SplitCorrections) : Prop :=
  ValidOutput (differential p) (affineRhs rhsLinear 0) v (out.map collapse)

/-- The full split validator has exactly the original whole collapsed equation, including impossibility. -/
theorem validSplit_iff (p : Permissions) (v : Values) (out : Option SplitCorrections) :
    ValidSplit p v out ↔ ValidOutput (differential p) (affineRhs rhsLinear 0) v (out.map collapse) := Iff.rfl

/-- A known-r complete extension satisfies precisely the original independent numerical validator. -/
theorem valid_extend_iff (p : Permissions) (v : Values) (r : ZMod 3) (out : Option Corrections) :
    ValidSplit p v (out.map (extend r)) ↔ ValidOutput (differential p) (affineRhs rhsLinear 0) v out := by
  rw [validSplit_iff]
  cases out with
  | none => rfl
  | some a => simp only [Option.map_some,collapse_extend]

/-- Every valid full split tuple constructs an independent actual supported repair of the original split tower. -/
noncomputable def restore (p : Permissions) (v : Values) (b : SplitCorrections)
    (hb : ValidSplit p v (some b)) : W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p) :=
  let h := (equation_iff p v (collapse b)).mp ((validOutput_some_iff _ _ _ _).mp hb)
  Subdivision.expandSupported (originalTower true (v false) (v true)) chosen (factors (v false) (v true))
    (fixedEdges (allowed p))
    ((nativeParametersEquiv true (v false) (v true) (allowed p)).symm ⟨parameters (collapse b),h⟩)
    ((W1SubdivisionRepairs.middleCoefficient (v false) (v true)).symm (b 3))

/-- Every restored whole split answer has precisely its acquired alpha,beta values at both actual factors. -/
theorem restore_factors (p : Permissions) (v : Values) (b : SplitCorrections)
    (hb : ValidSplit p v (some b)) :
    W1SubdivisionRepairs.middleCoefficient (v false) (v true)
      ((splitTower (v false) (v true)).solutionCorrection (restore p v b hb).1
        (Subdivision.firstEdgeName geometry chosen)) = b 3 ∧
    W1SubdivisionRepairs.middleCoefficient (v false) (v true)
      ((splitTower (v false) (v true)).solutionCorrection (restore p v b hb).1
        (Subdivision.secondEdgeName geometry chosen)) = b 4 := by
  have h := (equation_iff p v (collapse b)).mp ((validOutput_some_iff _ _ _ _).mp hb)
  have he := W1SubdivisionCoordinates.all_pairs (v false) (v true) (allowed p)
    ⟨parameters (collapse b),h⟩ (b 3)
  simpa only [W1NumericalEquation.parameters,collapse,Matrix.cons_val_one,Matrix.cons_val_zero,sub_add_cancel] using he

/-- Every restored surviving original name keeps its entire old correction; both physical inputs remain fixed. -/
theorem restore_old (p : Permissions) (v : Values) (b : SplitCorrections)
    (hb : ValidSplit p v (some b)) (e : EdgeName (K := geometry)) (he : e ≠ chosen) :
    (splitTower (v false) (v true)).solutionCorrection (restore p v b hb).1
      (Subdivision.oldEdgeName geometry chosen e he) =
    (originalTower true (v false) (v true)).solutionCorrection
      ((nativeParametersEquiv true (v false) (v true) (allowed p)).symm
        ⟨parameters (collapse b),(equation_iff p v (collapse b)).mp ((validOutput_some_iff _ _ _ _).mp hb)⟩).1 e :=
  Subdivision.expandSupported_old _ _ _ _ _ _ e he

/-- The actual split original rx operation equals the original full physical rx input. -/
theorem original_rx (X : Inputs) :
    (splitTower (values X false) (values X true)).original.edgeLift
      (Subdivision.oldEdge geometry chosen (name edgeRx)
        (by simp [chosen,name,edgeRx,edgeA,geometry])) = (X false).1 := by
  rw [Subdivision.originalTower_original_edge_old]
  change reference true (values X false) (values X true) (i := ()) (j := ()) edgeRx = _
  exact reference_rx X

/-- The actual split original ry operation equals the original full physical ry input. -/
theorem original_ry (X : Inputs) :
    (splitTower (values X false) (values X true)).original.edgeLift
      (Subdivision.oldEdge geometry chosen (name edgeRy)
        (by simp [chosen,name,edgeRy,edgeA,geometry])) = (X true).1 := by
  rw [Subdivision.originalTower_original_edge_old]
  change reference true (values X false) (values X true) (i := ()) (j := ()) edgeRy = _
  exact reference_ry X

/-- Independent original and split actual repairability agree on every unchanged physical input and original permission subset. -/
theorem actual_solvable_iff (p : Permissions) (v : Values) :
    Nonempty (W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p)) ↔
      Solvable (differential p) (affineRhs rhsLinear 0) v := by
  have ha := actual_iff p (realize v)
  simp only [values_realize] at ha
  have he := (W1SubdivisionRepairs.repairEquiv (v false) (v true) (allowed p)).nonempty_congr
  rw [he,nonempty_prod]
  exact (and_iff_left (inferInstance : Nonempty (ZMod 3))).trans ha

/-- The unchanged Boolean controller decides the same independently specified split actual repairs. -/
theorem decision_valid_iff (p : Permissions) (v : Values) (a : Bool) :
    (a = true ↔ Nonempty (W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p))) ↔
      ValidDecision (differential p) rhsLinear 0 v a := by
  rw [actual_solvable_iff,valid_decision_iff]

/-- The split actual decision optimum preserves the entire original table with no change to the primitive procedure. -/
theorem decision_optimum (p : Permissions) (m : Fin 3) (w : Values) :
    optimum evaluate (values ⁻¹' informationFiber (W1ObservationCosts.known m) (W1ObservationCosts.known m w))
      (fun X a => a = true ↔ Nonempty (W1SubdivisionRepairs.NewRepairs
        (values X false) (values X true) (allowed p))) =
      if p false = true ∨ p true = true then 0 else (2 - m.val : Nat) := by
  have hv : (fun X a => a = true ↔ Nonempty (W1SubdivisionRepairs.NewRepairs
      (values X false) (values X true) (allowed p))) =
      (fun X a => ValidDecision (differential p) rhsLinear 0 (values X) a) := by
    funext X a
    exact propext (decision_valid_iff p (values X) a)
  rw [hv,PrimitiveInputQueries.optimum_eq values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values]
  exact W1GeneratedDecisionPlan.table p m w

/-- Known-r extension maps every old actual controller to a full split controller with identical questions. -/
def extendProcedure (r : ZMod 3) (next : Procedure Bool (ZMod 3) (Option Corrections)) :
    Procedure Bool (ZMod 3) (Option SplitCorrections) := PrimitiveOutputMap.transport (Option.map (extend r)) next

/-- Complete numeric collapse maps every split controller to an original controller with identical questions. -/
def collapseProcedure (next : Procedure Bool (ZMod 3) (Option SplitCorrections)) :
    Procedure Bool (ZMod 3) (Option Corrections) := PrimitiveOutputMap.transport (Option.map collapse) next

/-- Arbitrary full split controllers and known-r original extensions have the same all-adaptive actual-input optimum. -/
theorem optimum_eq (p : Permissions) (F : Set Inputs) (r : ZMod 3) :
    optimum evaluate F (fun X out => ValidSplit p (values X) out) =
      optimum evaluate F (fun X out => ValidOutput (differential p) (affineRhs rhsLinear 0) (values X) out) := by
  apply le_antisymm
  · exact PrimitiveOutputMap.optimum_le evaluate (Option.map (extend r)) F _ _
      (fun X _ out ho => (valid_extend_iff p (values X) r out).mpr ho)
  · exact PrimitiveOutputMap.optimum_le evaluate (Option.map collapse) F _ _
      (fun X _ out ho => (validSplit_iff p (values X) out).mp ho)

/-- Known-r extension preserves the complete actual run, including every repeated original query. -/
theorem extend_run (r : ZMod 3) (next : Procedure Bool (ZMod 3) (Option Corrections))
    (X : Inputs) (hist : History Bool (ZMod 3)) (a : Option Corrections) (qs : List Bool)
    (hr : Run evaluate next X hist a qs) :
    Run evaluate (extendProcedure r next) X hist (a.map (extend r)) qs :=
  PrimitiveOutputMap.run_forward evaluate _ hr

/-- Complete split-output collapse preserves the full actual primitive query trace. -/
theorem collapse_run (next : Procedure Bool (ZMod 3) (Option SplitCorrections))
    (X : Inputs) (hist : History Bool (ZMod 3)) (b : Option SplitCorrections) (qs : List Bool)
    (hr : Run evaluate next X hist b qs) :
    Run evaluate (collapseProcedure next) X hist (b.map collapse) qs :=
  PrimitiveOutputMap.run_forward evaluate _ hr

/-- Every known-r extension of the generated actual numerical plan is total and correct as a complete split-output procedure. -/
theorem generated_correct (p : Permissions) (m : Fin 3) (w : Values) (r : ZMod 3) :
    Correct evaluate (values ⁻¹' informationFiber (W1ObservationCosts.known m) (W1ObservationCosts.known m w))
      (fun X out => ValidSplit p (values X) out)
      (extendProcedure r (W1GeneratedNumericalPlan.procedure p m (W1ObservationCosts.known m w))) :=
  PrimitiveOutputMap.correct evaluate _ _ _ _
    (fun X _ out ho => (valid_extend_iff p (values X) r out).mpr ho)
    (W1GeneratedNumericalPlan.correct p m w)

/-- For every known r the generated full split-output procedure attains the same exact original numerical table. -/
theorem generated_optimal (p : Permissions) (m : Fin 3) (w : Values) (r : ZMod 3) :
    worst evaluate (values ⁻¹' informationFiber (W1ObservationCosts.known m) (W1ObservationCosts.known m w))
      (extendProcedure r (W1GeneratedNumericalPlan.procedure p m (W1ObservationCosts.known m w))) =
      optimum evaluate (values ⁻¹' informationFiber (W1ObservationCosts.known m) (W1ObservationCosts.known m w))
        (fun X out => ValidSplit p (values X) out) ∧
    worst evaluate (values ⁻¹' informationFiber (W1ObservationCosts.known m) (W1ObservationCosts.known m w))
      (extendProcedure r (W1GeneratedNumericalPlan.procedure p m (W1ObservationCosts.known m w))) =
      (2 - m.val : Nat) := by
  change worst _ _ (PrimitiveOutputMap.transport _ _) = _ ∧ worst _ _ (PrimitiveOutputMap.transport _ _) = _
  rw [PrimitiveOutputMap.worst_eq,optimum_eq p _ r]
  exact W1GeneratedNumericalPlan.optimal p m w

end AAT.AG.RepairObservationDuality.W1SubdivisionQueries
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1SubdivisionQueries
