import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomObservableReadings
import Formal.Util.AssertStandardAxioms

/-!
# Observable restriction naturality from common primitive point pairs

The local condition compares two context graph points, two restriction point
responses, and one input/output observable graph pair. Candidate carrier
activation follows from the existing equation-table typing conditions. The
condition is equivalent to naturality of the reconstructed observable family
at every true context pair; no whole natural transformation is a local field.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ObservableNatural

noncomputable section

universe u v

open Site CategoryTheory

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U} {mode : Mode}

/-- Restriction naturality stated solely with primitive table responses and true Hom pairs. -/
def PointLaws (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (W X : ArchCtx A) (V Y : ArchCtx B) (K L K' L' : Type u)
      (x : L) (y : L') (rx : K) (ry : K'),
    h (.atObjects A B (.context .forward W V)) = true →
    h (.atObjects A B (.context .forward X Y)) = true →
    (s (.restriction W X K L x)).down = some rx →
    (t (.restriction V Y K' L' y)).down = some ry →
    h (.atObjects A B (.observable .forward X Y (.edge L L' x y))) = true →
    h (.atObjects A B (.observable .forward W V (.edge K K' rx ry))) = true

variable {C : ContextPreorderCategory A} {D : ContextPreorderCategory B}
variable (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
variable (hs : IndependentEquationPrimitive.IsTyped C s) (ht : IndependentEquationPrimitive.IsTyped D t)
variable (hls : IndependentEquationPrimitive.IsLawful s hs) (hlt : IndependentEquationPrimitive.IsLawful t ht)
variable (h : Table.{u, v} U mode) (hc : Context.IsLawful C.le D.le (Context.points h A B))

/-- The ring family used by observable assembly is generated from the source's primitive equation rows. -/
def rings (s : IndependentEquationPrimitive.Table A) (hs : IndependentEquationPrimitive.IsTyped C s)
    (hl : IndependentEquationPrimitive.IsLawful s hs) : ∀ W, CommRing (IndependentEquationPrimitive.observableType s W) :=
  fun W => IndependentEquationPrimitive.observableRing s hs W (hl.ring W)

/-- Native restriction naturality at any two true context pairs, using only independently reconstructed fiber maps. -/
def PairNaturality : Prop :=
  letI := rings s hs hls
  letI := rings t ht hlt
  ∀ (ho : Observable.IsLawful h (IndependentEquationPrimitive.observableType s)
      (IndependentEquationPrimitive.observableType t)),
    ∀ (W X : ArchCtx A) (V Y : ArchCtx B) (hWX : C.le W X)
      (hWV : Observable.contextPoints h W V = true) (hXY : Observable.contextPoints h X Y = true)
      (x : IndependentEquationPrimitive.observableType s X),
      Observable.atPair h _ _ ho W V hWV (IndependentEquationPrimitive.restrict s hs hWX x) =
        IndependentEquationPrimitive.restrict t ht
          (hc.forward_mono W X V Y hWV hXY hWX) (Observable.atPair h _ _ ho X Y hXY x)

/-- Primitive restriction point laws imply naturality of each reconstructed observable fiber map. -/
theorem pairNaturality_of_points (hl : PointLaws s t h) : PairNaturality s t hs ht hls hlt h hc := by
  letI := rings s hs hls
  letI := rings t ht hlt
  intro ho W X V Y hWX hWV hXY x
  apply (Observable.atPair_forward_iff h _ _ ho W V hWV _ _).1
  exact hl W X V Y _ _ _ _ x (Observable.atPair h _ _ ho X Y hXY x) _ _ hWV hXY
    (Option.some_get _).symm (Option.some_get _).symm
    ((Observable.atPair_forward_iff h _ _ ho X Y hXY x _).2 rfl)

/-- Native pair naturality gives every primitive instance after candidate carrier activation is derived. -/
theorem points_of_pairNaturality
    (ho : letI := rings s hs hls
      letI := rings t ht hlt
      Observable.IsLawful h (IndependentEquationPrimitive.observableType s)
        (IndependentEquationPrimitive.observableType t))
    (hn : PairNaturality s t hs ht hls hlt h hc) : PointLaws s t h := by
  letI := rings s hs hls
  letI := rings t ht hlt
  intro W X V Y K L K' L' x y rx ry hWV hXY hrx hry hxy
  have has := (hs.restriction W X K L x).1 (by simp [hrx])
  have hat := (ht.restriction V Y K' L' y).1 (by simp [hry])
  obtain ⟨hWX, rfl, rfl⟩ := has
  obtain ⟨_, rfl, rfl⟩ := hat
  have hx : IndependentEquationPrimitive.restrict s hs hWX x = rx := by
    apply Option.some.inj
    exact (Option.some_get _).trans hrx
  have hy : IndependentEquationPrimitive.restrict t ht
      (hc.forward_mono W X V Y hWV hXY hWX) y = ry := by
    apply Option.some.inj
    exact (Option.some_get _).trans hry
  have he := (Observable.atPair_forward_iff h _ _ ho X Y hXY x y).1 hxy
  apply (Observable.atPair_forward_iff h _ _ ho W V hWV rx ry).2
  exact (congrArg (Observable.atPair h _ _ ho W V hWV) hx).symm.trans
    ((hn ho W X V Y hWX hWV hXY x).trans
      ((congrArg (IndependentEquationPrimitive.restrict t ht
        (hc.forward_mono W X V Y hWV hXY hWX)) he).trans hy))

/-- With the independently constructed observable rows, primitive restriction rules are exactly pair naturality. -/
theorem points_iff_pairNaturality
    (ho : letI := rings s hs hls
      letI := rings t ht hlt
      Observable.IsLawful h (IndependentEquationPrimitive.observableType s)
        (IndependentEquationPrimitive.observableType t)) :
    PointLaws s t h ↔ PairNaturality s t hs ht hls hlt h hc :=
  ⟨pairNaturality_of_points s t hs ht hls hlt h hc,
    points_of_pairNaturality s t hs ht hls hlt h hc ho⟩

/-- Restriction naturality of the actual assembled context functor and equation systems. -/
def NativeNaturality : Prop :=
  letI := rings s hs hls
  letI := rings t ht hlt
  ∀ (ho : Observable.IsLawful h (IndependentEquationPrimitive.observableType s)
      (IndependentEquationPrimitive.observableType t)),
    ContextObservableGraphCoherence.IsRingFamilyRestrictionNatural
      (Context.assemble C D (Context.points h A B) hc).functor
      (fun W => IndependentEquationPrimitive.observableType s W.ctx)
      (fun V => IndependentEquationPrimitive.observableType t V.ctx)
      (IndependentEquationPrimitive.assemble s hs hls).restrict
      (IndependentEquationPrimitive.assemble t ht hlt).restrict
      (Observable.assemble C D h hc _ _ ho)

/-- Naturality at true primitive context pairs gives the actual native restriction square. -/
theorem nativeNaturality_of_pairNaturality
    (hn : PairNaturality s t hs ht hls hlt h hc) :
    NativeNaturality s t hs ht hls hlt h hc := by
  letI := rings s hs hls
  letI := rings t ht hlt
  intro ho W X f x
  change Observable.assemble C D h hc _ _ ho W
      (IndependentEquationPrimitive.restrict s hs (leOfHom f) x) =
    IndependentEquationPrimitive.restrict t ht
      (leOfHom ((Context.assemble C D (Context.points h A B) hc).functor.map f))
      (Observable.assemble C D h hc _ _ ho X x)
  rw [Observable.assemble_eq_atPair, Observable.assemble_eq_atPair]
  exact hn ho W.ctx X.ctx _ _ (leOfHom f)
    (Observable.forward_point C D h hc W) (Observable.forward_point C D h hc X) x

/-- Every true primitive context pair is the context chosen by the native functor. -/
theorem context_pair_eq (W : ArchCtx A) (V : ArchCtx B)
    (hp : Observable.contextPoints h W V = true) :
    (((Context.assemble C D (Context.points h A B) hc).functor.obj ⟨W⟩).ctx) = V := by
  exact congrArg ContextCategoryObject.ctx
    ((Context.code C D (Context.points h A B) hc).forwardCode.target_eq_of_edge hp)

/-- Native restriction naturality recovers the square at every true primitive context pair. -/
theorem pairNaturality_of_nativeNaturality
    (hn : NativeNaturality s t hs ht hls hlt h hc) :
    PairNaturality s t hs ht hls hlt h hc := by
  letI := rings s hs hls
  letI := rings t ht hlt
  intro ho W X V Y hWX hWV hXY x
  have hv := context_pair_eq h hc W V hWV
  have hy := context_pair_eq h hc X Y hXY
  subst V Y
  have he := hn ho (homOfLE hWX : (⟨W⟩ : ContextCategoryObject C) ⟶ ⟨X⟩) x
  change Observable.assemble C D h hc _ _ ho ⟨W⟩
      (IndependentEquationPrimitive.restrict s hs hWX x) =
    IndependentEquationPrimitive.restrict t ht (hc.forward_mono W X _ _ hWV hXY hWX)
      (Observable.assemble C D h hc _ _ ho ⟨X⟩ x) at he
  rw [Observable.assemble_eq_atPair, Observable.assemble_eq_atPair] at he
  exact he

/-- Primitive point squares are equivalent to the native restriction-naturality field. -/
theorem points_iff_nativeNaturality
    (ho : letI := rings s hs hls
      letI := rings t ht hlt
      Observable.IsLawful h (IndependentEquationPrimitive.observableType s)
        (IndependentEquationPrimitive.observableType t)) :
    PointLaws s t h ↔ NativeNaturality s t hs ht hls hlt h hc :=
  ⟨fun hp => nativeNaturality_of_pairNaturality s t hs ht hls hlt h hc
      (pairNaturality_of_points s t hs ht hls hlt h hc hp),
    fun hn => points_of_pairNaturality s t hs ht hls hlt h hc ho
      (pairNaturality_of_nativeNaturality s t hs ht hls hlt h hc hn)⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ObservableNatural

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ObservableNatural
