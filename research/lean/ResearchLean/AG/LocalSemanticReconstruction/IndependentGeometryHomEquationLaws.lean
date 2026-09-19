import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomObservableNaturality
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreLaws
import Formal.Util.AssertStandardAxioms

/-!
# Equation roles and coordinate preservation from common Hom points

Role, violation, and residual conditions are stated using candidate equation
and observable carriers, primitive responses, and true Hom point pairs. The
selected carrier and image equations are derived from row laws. These point
conditions are equivalent to the native preservation equations for the
independently assembled equation, Atom, object, context, and observable maps.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationLaws

noncomputable section

universe u v

open Site CategoryTheory

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U} {mode : Mode}

/-- A role point is transported along each true equation-index pair. -/
def RolePoints (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (I J : Type u) (i : I) (j : J) (r : EquationRole),
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true →
    (s (.role I i)).down = some r → (t (.role J j)).down = some r

/-- A symbolic violation response is carried to its target response by the observable point graph. -/
def ViolationPoints (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (W : ArchCtx A) (V : ArchCtx B) (I J K L : Type u)
      (i : I) (j : J) (a b : U.Atom) (x : K) (y : L),
    h (.atObjects A B (.context .forward W V)) = true →
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true →
    h (.atom .forward a b) = true →
    (s (.violation W I K i a)).down = some x →
    (t (.violation V J L j b)).down = some y →
    h (.atObjects A B (.observable .forward W V (.edge K L x y))) = true

/-- A residual response additionally follows the independently directed architecture-object graph. -/
def ResidualPoints (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (W : ArchCtx A) (V : ArchCtx B) (M N : ArchitectureObject U) (I J K L : Type u)
      (i : I) (j : J) (a b : U.Atom) (x : K) (y : L),
    h (.atObjects A B (.context .forward W V)) = true → h (.object M N) = true →
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true →
    h (.atom .forward a b) = true →
    (s (.residual W M I K i a)).down = some x →
    (t (.residual V N J L j b)).down = some y →
    h (.atObjects A B (.observable .forward W V (.edge K L x y))) = true

variable {C : ContextPreorderCategory A} {D : ContextPreorderCategory B}
variable (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
variable (hs : IndependentEquationPrimitive.IsTyped C s) (ht : IndependentEquationPrimitive.IsTyped D t)
variable (h : Table.{u, v} U mode)
variable (he : IndependentInverseGraph.IsLawful (IndependentEquationPrimitive.index s)
  (IndependentEquationPrimitive.index t) (InverseRows.equation h A B))

/-- Construct the native equation-index equivalence from the common inverse point rows. -/
def equationEquiv : IndependentEquationPrimitive.index s ≃ IndependentEquationPrimitive.index t :=
  IndependentInverseGraph.assemble _ _ (InverseRows.equation h A B) he

/-- An active forward equation pair identifies the image of the assembled index equivalence. -/
theorem equation_forward_iff (i : IndependentEquationPrimitive.index s) (j : IndependentEquationPrimitive.index t) :
    h (.atObjects A B (.equation .forward
      (.edge (IndependentEquationPrimitive.index s) (IndependentEquationPrimitive.index t) i j))) = true ↔
      equationEquiv s t h he i = j :=
  (IndependentCarrierGraph.graph _ _ _ he.forward.2).edge_eq_true_iff_target_eq i j

include he in
/-- A true equation point activates exactly the selected source and target index carriers. -/
theorem equation_carriers (I J : Type u) (i : I) (j : J)
    (hp : h (.atObjects A B (.equation .forward (.edge I J i j))) = true) :
    I = IndependentEquationPrimitive.index s ∧ J = IndependentEquationPrimitive.index t := by
  classical
  by_contra hn
  exact Bool.noConfusion ((he.forward.1 I J i j (not_and_or.mp hn)).symm.trans hp)

/-- Primitive role preservation gives exactly the native role equation. -/
theorem role_eq_of_points (hp : RolePoints s t h) (i : IndependentEquationPrimitive.index s) :
    IndependentEquationPrimitive.role t ht (equationEquiv s t h he i) =
      IndependentEquationPrimitive.role s hs i := by
  apply Option.some.inj
  exact (Option.some_get _).trans (hp _ _ i (equationEquiv s t h he i)
    (IndependentEquationPrimitive.role s hs i)
    ((equation_forward_iff s t h he i _).2 rfl) (Option.some_get _).symm)

/-- Native role equations imply every candidate-carrier role point after graph typing is applied. -/
theorem role_points_of_eq
    (hp : ∀ i, IndependentEquationPrimitive.role t ht (equationEquiv s t h he i) =
      IndependentEquationPrimitive.role s hs i) : RolePoints s t h := by
  intro I J i j r hij hr
  have hIJ := equation_carriers s t h he I J i j hij
  obtain ⟨rfl, rfl⟩ := hIJ
  have heq := (equation_forward_iff s t h he i j).1 hij
  subst j
  have hi : IndependentEquationPrimitive.role s hs i = r :=
    Option.some.inj ((Option.some_get _).trans hr)
  exact (Option.some_get _).symm.trans (congrArg some ((hp i).trans hi))

/-- All candidate role-point conditions and native role preservation have exactly the same content. -/
theorem role_points_iff : RolePoints s t h ↔
    ∀ i, IndependentEquationPrimitive.role t ht (equationEquiv s t h he i) =
      IndependentEquationPrimitive.role s hs i :=
  ⟨role_eq_of_points s t hs ht h he, role_points_of_eq s t hs ht h he⟩

variable (hls : IndependentEquationPrimitive.IsLawful s hs) (hlt : IndependentEquationPrimitive.IsLawful t ht)
variable (hc : Context.IsLawful C.le D.le (Context.points h A B))
variable (ha : Atom.IsLawful (Atom.upper h))
variable (ho : letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  Observable.IsLawful h (IndependentEquationPrimitive.observableType s)
    (IndependentEquationPrimitive.observableType t))

/-- The actual native symbolic-violation preservation equation for the assembled maps. -/
def NativeViolation : Prop :=
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  ∀ (W : ContextCategoryObject C) (i : IndependentEquationPrimitive.index s) (a : U.Atom),
    Observable.assemble C D h hc _ _ ho W (IndependentEquationPrimitive.violation s hs W.ctx i a) =
      IndependentEquationPrimitive.violation t ht
        (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)
        (equationEquiv s t h he i) (Atom.assemble (Atom.upper h) ha a)

/-- Primitive symbolic-violation points imply native preservation at every context, equation, and Atom. -/
theorem nativeViolation_of_points (hp : ViolationPoints s t h) :
    NativeViolation s t hs ht h he hls hlt hc ha ho := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  intro W i a
  rw [Observable.assemble_eq_atPair]
  apply (Observable.atPair_forward_iff h _ _ ho W.ctx _ (Observable.forward_point C D h hc W) _ _).1
  exact hp W.ctx _ _ _ _ _ i (equationEquiv s t h he i) a (Atom.assemble (Atom.upper h) ha a) _ _
    (Observable.forward_point C D h hc W) ((equation_forward_iff s t h he i _).2 rfl)
    (Atom.edge_assemble (Atom.upper h) ha a) (Option.some_get _).symm (Option.some_get _).symm

/-- Native symbolic-violation preservation recovers every primitive candidate response. -/
theorem violation_points_of_native (hp : NativeViolation s t hs ht h he hls hlt hc ha ho) :
    ViolationPoints s t h := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  intro W V I J K L i j a b x y hWV hij hab hx hy
  obtain ⟨rfl, rfl⟩ := (hs.violation W I K i a).1 (by simp [hx])
  obtain ⟨rfl, rfl⟩ := (ht.violation V J L j b).1 (by simp [hy])
  have hv := ObservableNatural.context_pair_eq h hc W V hWV
  have hj := (equation_forward_iff s t h he i j).1 hij
  have hb := Atom.assemble_eq_of_edge (Atom.upper h) ha hab
  subst V j b
  have hx' : IndependentEquationPrimitive.violation s hs W i a = x :=
    Option.some.inj ((Option.some_get _).trans hx)
  have hy' : IndependentEquationPrimitive.violation t ht _ _ _ = y :=
    Option.some.inj ((Option.some_get _).trans hy)
  have hh := hp ⟨W⟩ i a
  rw [Observable.assemble_eq_atPair] at hh
  apply (Observable.atPair_forward_iff h _ _ ho W _ hWV x y).2
  exact (congrArg (Observable.atPair h _ _ ho W _ hWV) hx').symm.trans (hh.trans hy')

/-- Symbolic-violation point laws and the native preservation equation are equivalent. -/
theorem violation_points_iff : ViolationPoints s t h ↔ NativeViolation s t hs ht h he hls hlt hc ha ho :=
  ⟨nativeViolation_of_points s t hs ht h he hls hlt hc ha ho,
    violation_points_of_native s t hs ht h he hls hlt hc ha ho⟩

variable (hm : CoreLaws.ObjectRows h)

/-- The actual native residual preservation equation includes the directed object action. -/
def NativeResidual : Prop :=
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  ∀ (W : ContextCategoryObject C) (M : ArchitectureObject U)
      (i : IndependentEquationPrimitive.index s) (a : U.Atom),
    Observable.assemble C D h hc _ _ ho W (IndependentEquationPrimitive.residual s hs W.ctx M i a) =
      IndependentEquationPrimitive.residual t ht
        (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)
        (CoreLaws.objectMap h hm M) (equationEquiv s t h he i) (Atom.assemble (Atom.upper h) ha a)

/-- Primitive residual points give native residual preservation for every object. -/
theorem nativeResidual_of_points (hp : ResidualPoints s t h) :
    NativeResidual s t hs ht h he hls hlt hc ha ho hm := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  intro W M i a
  rw [Observable.assemble_eq_atPair]
  apply (Observable.atPair_forward_iff h _ _ ho W.ctx _ (Observable.forward_point C D h hc W) _ _).1
  exact hp W.ctx _ M (CoreLaws.objectMap h hm M) _ _ _ _ i (equationEquiv s t h he i)
    a (Atom.assemble (Atom.upper h) ha a) _ _ (Observable.forward_point C D h hc W)
    ((CoreLaws.objectGraph h hm).edge_target M) ((equation_forward_iff s t h he i _).2 rfl)
    (Atom.edge_assemble (Atom.upper h) ha a) (Option.some_get _).symm (Option.some_get _).symm

/-- Native residual preservation recovers every candidate context, object, index, and carrier instance. -/
theorem residual_points_of_native (hp : NativeResidual s t hs ht h he hls hlt hc ha ho hm) :
    ResidualPoints s t h := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  intro W V M N I J K L i j a b x y hWV hMN hij hab hx hy
  obtain ⟨rfl, rfl⟩ := (hs.residual W M I K i a).1 (by simp [hx])
  obtain ⟨rfl, rfl⟩ := (ht.residual V N J L j b).1 (by simp [hy])
  have hv := ObservableNatural.context_pair_eq h hc W V hWV
  have hn := (CoreLaws.objectGraph h hm).target_eq_of_edge hMN
  have hj := (equation_forward_iff s t h he i j).1 hij
  have hb := Atom.assemble_eq_of_edge (Atom.upper h) ha hab
  subst V N j b
  have hx' : IndependentEquationPrimitive.residual s hs W M i a = x :=
    Option.some.inj ((Option.some_get _).trans hx)
  have hy' : IndependentEquationPrimitive.residual t ht _ _ _ _ = y :=
    Option.some.inj ((Option.some_get _).trans hy)
  have hh := hp ⟨W⟩ M i a
  rw [Observable.assemble_eq_atPair] at hh
  apply (Observable.atPair_forward_iff h _ _ ho W _ hWV x y).2
  exact (congrArg (Observable.atPair h _ _ ho W _ hWV) hx').symm.trans (hh.trans hy')

/-- All primitive residual instances are equivalent to the full native residual preservation equation. -/
theorem residual_points_iff : ResidualPoints s t h ↔ NativeResidual s t hs ht h he hls hlt hc ha ho hm :=
  ⟨nativeResidual_of_points s t hs ht h he hls hlt hc ha ho hm,
    residual_points_of_native s t hs ht h he hls hlt hc ha ho hm⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationLaws

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationLaws
