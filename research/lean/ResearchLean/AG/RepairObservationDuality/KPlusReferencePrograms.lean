import ResearchLean.AG.RepairObservationDuality.KPlusNumericalQueries

/-!
# G-131 E: K+ reference programs and the same real faces

Outputs are finite syntax containing only original references, inverses and
compositions. No numerical zero value or hidden query is stored in this AST.
Its interpretation produces the same complete original four-edge map family;
the two authored faces and original fixed maps define correctness independently.
-/
namespace AAT.AG.RepairObservationDuality.KPlusReferencePrograms
open TransportCoherence AbelianLiftingObstruction RelativeRepairComposition NativeAffine
open KPlusInput KPlusActualRepairs PrimitiveQueries
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The exact two available original physical references. -/
inductive InputName where
  | a | b
  deriving DecidableEq
/-- Finite reference-output syntax with no value literals or delayed primitive queries. -/
inductive Expression where
  | ref : InputName → Expression
  | inverse : Expression → Expression
  | compose : Expression → Expression → Expression
  deriving DecidableEq
/-- Both original repairable edges receive finite output syntax. -/
structure Program where
  e : Expression
  c : Expression
  deriving DecidableEq
/-- Interpretation uses precisely the whole original physical a/b operations. -/
def interpret (X : Inputs) : Expression → Op
  | .ref .a => (X false).1
  | .ref .b => (X true).1
  | .inverse t => (interpret X t)⁻¹
  | .compose s t => interpret X s * interpret X t
/-- Basic API: original a reference denotes that same full original physical operation. -/
theorem interpret_a (X : Inputs) : interpret X (.ref .a) = (X false).1 := rfl
/-- Basic API: original b reference denotes that same full original physical operation. -/
theorem interpret_b (X : Inputs) : interpret X (.ref .b) = (X true).1 := rfl
/-- Basic API: AST inverse denotes the inverse of the full interpreted map. -/
theorem interpret_inverse (X : Inputs) (t : Expression) :
    interpret X (.inverse t) = (interpret X t)⁻¹ := rfl
/-- Basic API: AST composition has the original temporal map convention. -/
theorem interpret_compose (X : Inputs) (s t : Expression) :
    interpret X (.compose s t) = interpret X s * interpret X t := rfl
/-- Every interpreted AST keeps the same identity linear part by the whole native kernel laws. -/
theorem interpret_linear (X : Inputs) (t : Expression) : projection (interpret X t) = 1 := by
  induction t with
  | ref i => cases i; exact (X false).2; exact (X true).2
  | inverse t ih => rw [interpret_inverse,map_inv,ih,inv_one]
  | compose s t ihs iht => rw [interpret_compose,map_mul,ihs,iht,one_mul]
/-- The generated syntax is fixed before any physical values or replies are acquired. -/
def program : Program := ⟨.ref .a,.compose (.ref .b) (.inverse (.ref .a))⟩
/-- Basic API: the original e output is the a reference. -/
theorem program_e : program.e = .ref .a := rfl
/-- Basic API: the original c output is b after inverse a. -/
theorem program_c : program.c = .compose (.ref .b) (.inverse (.ref .a)) := rfl
/-- Whole interpreted repairs preserve a/b and replace just the original e/c maps. -/
noncomputable def operations (X : Inputs) (p : Program) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => if e.1 = edgeE then interpret X p.e
    else if e.1 = edgeC then interpret X p.c else reference (values X) e
/-- Basic API: the generated original e map is its full AST interpretation. -/
theorem operations_e (X : Inputs) (p : Program) : operations X p (name edgeE).2.2 = interpret X p.e := by
  simp [operations,name_value]
/-- Basic API: the generated original c map is its full AST interpretation. -/
theorem operations_c (X : Inputs) (p : Program) : operations X p (name edgeC).2.2 = interpret X p.c := by
  simp [operations,name_value,edgeC,edgeE]
/-- Basic API: the same entire fixed original a map is retained. -/
theorem operations_a (X : Inputs) (p : Program) :
    operations X p (name edgeA).2.2 = reference (values X) (name edgeA).2.2 := by
  simp [operations,name_value,edgeA,edgeE,edgeC]
/-- Basic API: the same entire fixed original b map is retained. -/
theorem operations_b (X : Inputs) (p : Program) :
    operations X p (name edgeB).2.2 = reference (values X) (name edgeB).2.2 := by
  simp [operations,name_value,edgeB,edgeE,edgeC]
/-- Every interpreted output has the same linear parts at all original edges. -/
theorem operations_linear (X : Inputs) (p : Program) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    (operations X p e).linear = (reference (values X) e).linear := by
  rw [reference_linear]
  change projection (operations X p e) = 1
  simp only [operations]
  split
  · exact interpret_linear X p.e
  · split
    · exact interpret_linear X p.c
    · exact reference_linear _ _
/-- Output validity is independently the two original real authored face equalities. -/
def ValidProgram (X : Inputs) (p : Program) : Prop :=
  ∀ f : Bool, translation (k := ZMod 2) (comparison f) *
    GroupExtension.pathValue geometry (operations X p) (geometry.twoLeft f) =
      GroupExtension.pathValue geometry (operations X p) (geometry.twoRight f)
/-- Basic API: program validity requires the same two original whole-map equations. -/
theorem valid_iff (X : Inputs) (p : Program) :
    ValidProgram X p ↔ interpret X p.e = (X false).1 ∧
      interpret X p.c * interpret X p.e = (X true).1 := by
  constructor
  · intro h
    have h0 := h false
    have h1 := h true
    rw [comparison_zero,zero_translation,one_mul,left_path_false,right_path] at h0
    change operations X p (name edgeE).2.2 = operations X p (name edgeA).2.2 at h0
    rw [operations_e,operations_a,reference_a] at h0
    rw [comparison_zero,zero_translation,one_mul,left_path_true,right_path] at h1
    change operations X p (name edgeC).2.2 * operations X p (name edgeE).2.2 =
      operations X p (name edgeB).2.2 at h1
    rw [operations_c,operations_e,operations_b,reference_b] at h1
    exact ⟨h0,h1⟩
  · rintro ⟨h0,h1⟩ f
    rw [comparison_zero,zero_translation,one_mul,right_path]
    cases f
    · rw [left_path_false,operations_e]
      change interpret X p.e = operations X p (name edgeA).2.2
      rw [operations_a,reference_a]
      exact h0
    · rw [left_path_true,operations_c,operations_e]
      change interpret X p.c * interpret X p.e = operations X p (name edgeB).2.2
      rw [operations_b,reference_b]
      exact h1
/-- The generated syntax satisfies the same original real faces on every whole physical input. -/
theorem program_valid (X : Inputs) : ValidProgram X program := by
  rw [valid_iff,program_e,program_c,interpret_a,interpret_compose,interpret_inverse,interpret_b,interpret_a]
  exact ⟨rfl,inv_mul_cancel_right _ _⟩
/-- Every independently valid reference output restores the whole original actual repair. -/
noncomputable def restore (X : Inputs) (p : Program) (hp : ValidProgram X p) : RealRepairs (values X) where
  operation := operations X p
  linear := operations_linear X p
  face := hp
  fixed_value e he := by
    rcases he with rfl | rfl
    · exact operations_a X p
    · exact operations_b X p
/-- A deliberately wrong AST has the same allowed syntax and fails the second original face. -/
def badProgram : Program := ⟨.ref .a,.ref .a⟩
/-- The new independent program predicate has positive and negative examples on the same original input. -/
theorem program_examples :
    ValidProgram (realize (fun j => if j then 1 else 0)) program ∧
      ¬ ValidProgram (realize (fun j => if j then 1 else 0)) badProgram := by
  refine ⟨program_valid _,?_⟩
  rw [valid_iff]
  intro h
  have hv := congrArg (fun g : Op => g 0) h.2
  change ((translation (k := ZMod 2) (0 : ZMod 2)) * translation (k := ZMod 2) (0 : ZMod 2)) 0 =
    (translation (k := ZMod 2) (1 : ZMod 2)) 0 at hv
  simp at hv
/-- The reference controller constructs this entire finite syntax using no replies. -/
def procedure : Procedure Bool (ZMod 2) Program := constant program
/-- The generated reference controller terminates and is correct on all original physical inputs. -/
theorem correct : Correct evaluate Set.univ ValidProgram procedure :=
  constant_correct evaluate Set.univ ValidProgram program (fun X _ => program_valid X)
/-- Every original physical input has the empty query trace and the same finite output AST. -/
theorem run (X : Inputs) : Run evaluate procedure X [] program [] := constant_run evaluate X program
/-- The controller's exact worst primitive cost is zero. -/
theorem worst_zero : worst evaluate Set.univ procedure = 0 := worst_constant evaluate Set.univ program
/-- The reference optimum over all correct adaptive original-input procedures is exactly zero. -/
theorem optimum_zero : optimum evaluate Set.univ ValidProgram = 0 :=
  optimum_zero_of_constant evaluate Set.univ ValidProgram program (fun X _ => program_valid X)
/-- Every numeric answer and the zero-query reference program satisfy both same original real faces. -/
theorem same_faces (X : Inputs) (h : Values)
    (he : KPlusNativeEquation.differential h = affineRhs KPlusNativeEquation.rhsLinear 0 (values X))
    (f : Bool) :
    translation (k := ZMod 2) (comparison f) *
      GroupExtension.pathValue geometry (KPlusNativeEquation.restore (values X) h he).operation
        (geometry.twoLeft f) =
      GroupExtension.pathValue geometry (KPlusNativeEquation.restore (values X) h he).operation
        (geometry.twoRight f) ∧
    translation (k := ZMod 2) (comparison f) *
      GroupExtension.pathValue geometry (operations X program) (geometry.twoLeft f) =
      GroupExtension.pathValue geometry (operations X program) (geometry.twoRight f) :=
  ⟨(KPlusNativeEquation.restore (values X) h he).face f,program_valid X f⟩
/-- The output language accounts for the exact original physical numeric/reference optimum difference. -/
theorem optimum_difference :
    optimum evaluate (values ⁻¹' informationFiber KPlusNumericalQueries.known 0)
      (fun X out => ValidOutput KPlusNativeEquation.differential
        (affineRhs KPlusNativeEquation.rhsLinear 0) (values X) out) = 2 ∧
    optimum evaluate Set.univ ValidProgram = 0 :=
  ⟨KPlusNumericalQueries.physical_cost,optimum_zero⟩

end AAT.AG.RepairObservationDuality.KPlusReferencePrograms
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.KPlusReferencePrograms
