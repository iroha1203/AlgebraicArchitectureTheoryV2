import Formal.AG.Atom.AATCore
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRingPrimitiveReadings
import Formal.Util.AssertStandardAxioms

/-!
# Primitive equation-system readings for the independent G-124 verification

Queries are declared over the architecture object's native context carrier,
before choosing an equation system. Observable rings are read through their
carrier and operation queries. Restriction, violation, and residual responses
are individual values. Ring preservation and the four compatibility equations
construct the native equation system on the chosen context preorder.

## Implementation notes

Observable carrier references activate only their own candidate operations.
Collecting those operations before restriction maps preserves native dependent
ring types. A completed ring or restriction hom as a response would hide these
laws. Circuit admissibility is therefore also expressed by a context/Atom
nonzero-residual witness, with all witness choices kept in propositions.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentEquationPrimitive

universe u

open Site CategoryTheory

variable {U : AtomCarrier.{u}}

/-- Primitive equation queries, independent of the selected index and observable types. -/
inductive Query (A : ArchitectureObject U) where
  /-- Select the equation-index carrier. -/
  | index
  /-- Read the role at one candidate equation index. -/
  | role (I : Type u) (i : I)
  /-- Read one primitive operation or type reference of an observable ring. -/
  | observable (W : ArchCtx A) (q : IndependentRingPrimitive.Carrier.Query.{u})
  /-- Read one restriction value on a candidate source and target observable carrier. -/
  | restriction (W V : ArchCtx A) (K L : Type u) (x : L)
  /-- Read one symbolic violation coordinate. -/
  | violation (W : ArchCtx A) (I K : Type u) (i : I) (a : U.Atom)
  /-- Read one object-dependent residual coordinate. -/
  | residual (W : ArchCtx A) (B : ArchitectureObject U)
      (I K : Type u) (i : I) (a : U.Atom)

/-- Every response is a type reference, a primitive ring value, a role, or one coordinate. -/
def Query.Value {A : ArchitectureObject U} : Query A → Type (u + 1)
  | .index => Type u
  | .role _ _ => ULift.{u + 1} (Option EquationRole)
  | .observable _ q => q.Value
  | .restriction _ _ K _ _ => ULift.{u + 1} (Option K)
  | .violation _ _ K _ _ => ULift.{u + 1} (Option K)
  | .residual _ _ _ K _ _ => ULift.{u + 1} (Option K)

/-- A dependent table of primitive equation readings. -/
abbrev Table (A : ArchitectureObject U) := (q : Query A) → q.Value

variable {A : ArchitectureObject U}

/-- The equation-index carrier selected by one primitive query. -/
abbrev index (t : Table A) : Type u := t .index

/-- The primitive observable-ring table at one context. -/
abbrev observable (t : Table A) (W : ArchCtx A) : IndependentRingPrimitive.Carrier.Table.{u} :=
  fun q => t (.observable W q)

/-- The observable carrier selected at one context. -/
abbrev observableType (t : Table A) (W : ArchCtx A) : Type u :=
  IndependentRingPrimitive.Carrier.carrier (observable t W)

/-- Activation conditions use the original refinement predicate and selected type references. -/
structure IsTyped (C : ContextPreorderCategory A) (t : Table A) : Prop where
  /-- Every observable ring has exactly its own active carrier. -/
  observable : ∀ W, IndependentRingPrimitive.Carrier.IsTyped (observable t W)
  /-- Equation roles are active exactly on the selected index carrier. -/
  role : ∀ I i, (t (.role I i)).down.isSome ↔ I = index t
  /-- A restriction value needs a refinement and the two selected observable carriers. -/
  restriction : ∀ W V K L x, (t (.restriction W V K L x)).down.isSome ↔
    C.le W V ∧ K = observableType t W ∧ L = observableType t V
  /-- Violation values need the selected equation and observable carriers. -/
  violation : ∀ W I K i a, (t (.violation W I K i a)).down.isSome ↔
    I = index t ∧ K = observableType t W
  /-- Residual values use the same carrier activation as violation coordinates. -/
  residual : ∀ W B I K i a, (t (.residual W B I K i a)).down.isSome ↔
    I = index t ∧ K = observableType t W

variable {C : ContextPreorderCategory A}

/-- Collect the selected equation role. -/
def role (t : Table A) (ht : IsTyped C t) (i : index t) : EquationRole :=
  (t (.role _ i)).down.get ((ht.role _ i).2 rfl)

/-- Collect the reverse observable map from its active point responses. -/
def restrict (t : Table A) (ht : IsTyped C t) {W V : ArchCtx A}
    (h : C.le W V) (x : observableType t V) : observableType t W :=
  (t (.restriction W V _ _ x)).down.get ((ht.restriction W V _ _ x).2 ⟨h, rfl, rfl⟩)

/-- Collect one symbolic violation coordinate. -/
def violation (t : Table A) (ht : IsTyped C t) (W : ArchCtx A)
    (i : index t) (a : U.Atom) : observableType t W :=
  (t (.violation W _ _ i a)).down.get ((ht.violation W _ _ i a).2 ⟨rfl, rfl⟩)

/-- Collect one object-dependent residual coordinate. -/
def residual (t : Table A) (ht : IsTyped C t) (W : ArchCtx A) (B : ArchitectureObject U)
    (i : index t) (a : U.Atom) : observableType t W :=
  (t (.residual W B _ _ i a)).down.get ((ht.residual W B _ _ i a).2 ⟨rfl, rfl⟩)

/-- Construct the native observable ring after its primitive equations have been established. -/
def observableRing (t : Table A) (ht : IsTyped C t) (W : ArchCtx A)
    (hr : IndependentRingPrimitive.Carrier.IsLawful (observable t W) (ht.observable W)) :
    CommRing (observableType t W) :=
  IndependentRingPrimitive.assemble
    (IndependentRingPrimitive.Carrier.active (observable t W) (ht.observable W)) hr

/-- The native equation-system laws, expressed entirely through primitive point values. -/
structure IsLawful (t : Table A) (ht : IsTyped C t) : Prop where
  /-- Observable operations satisfy the seven independent ring equations. -/
  ring : ∀ W, IndependentRingPrimitive.Carrier.IsLawful (observable t W) (ht.observable W)
  /-- Each restriction preserves zero, one, addition, and multiplication at points. -/
  restriction : ∀ W V (h : C.le W V),
    letI := observableRing t ht W (ring W)
    letI := observableRing t ht V (ring V)
    IndependentRingPrimitive.Hom.IsLawful (restrict t ht h)
  /-- Identity restriction fixes every observable point. -/
  identity : ∀ W x, restrict t ht (C.refl W) x = x
  /-- Restriction composes at every observable point. -/
  composition : ∀ W V X (h : C.le W V) (g : C.le V X) x,
    restrict t ht (C.trans h g) x = restrict t ht h (restrict t ht g x)
  /-- Symbolic violations commute with restriction at each equation and Atom. -/
  violation : ∀ W V (h : C.le W V) i a,
    restrict t ht h (violation t ht V i a) = violation t ht W i a
  /-- Object-dependent residuals commute with restriction at each equation and Atom. -/
  residual : ∀ W V (h : C.le W V) B i a,
    restrict t ht h (residual t ht V B i a) = residual t ht W B i a

/-- Assemble the complete native equation system from local ring and coordinate equations. -/
def assemble (t : Table A) (ht : IsTyped C t) (hl : IsLawful t ht) :
    ArchitecturalEquationSystem C where
  Index := index t
  role := role t ht
  Observable W := observableType t W.ctx
  observableCommRing W := observableRing t ht W.ctx (hl.ring W.ctx)
  restrict {W V} f := by
    letI := observableRing t ht W.ctx (hl.ring W.ctx)
    letI := observableRing t ht V.ctx (hl.ring V.ctx)
    exact IndependentRingPrimitive.Hom.assemble
      (restrict t ht (leOfHom f)) (hl.restriction W.ctx V.ctx (leOfHom f))
  restrict_id W := hl.identity W.ctx
  restrict_comp f g := hl.composition _ _ _ (leOfHom f) (leOfHom g)
  violationCoordinate W := violation t ht W.ctx
  violationCoordinate_restrict f := hl.violation _ _ (leOfHom f)
  equationResidual W := residual t ht W.ctx
  equationResidual_restrict f := hl.residual _ _ (leOfHom f)

/-- Read a native equation system without retaining whole rings or restriction homs in responses. -/
noncomputable def read (E : ArchitecturalEquationSystem C) : Table A := by
  classical
  intro q
  cases q with
  | index => exact E.Index
  | role I i => exact ⟨if h : I = E.Index then some (E.role (h ▸ i)) else none⟩
  | observable W q =>
    exact IndependentRingPrimitive.Carrier.read ⟨E.Observable ⟨W⟩, E.observableCommRing ⟨W⟩⟩ q
  | restriction W V K L x =>
    exact ⟨if h : C.le W V then
      if hK : K = E.Observable ⟨W⟩ then
        if hL : L = E.Observable ⟨V⟩ then
          some (hK.symm ▸ E.restrict (homOfLE h) (hL ▸ x)) else none
      else none else none⟩
  | violation W I K i a =>
    exact ⟨if hI : I = E.Index then
      if hK : K = E.Observable ⟨W⟩ then
        some (hK.symm ▸ E.violationCoordinate ⟨W⟩ (hI ▸ i) a) else none else none⟩
  | residual W B I K i a =>
    exact ⟨if hI : I = E.Index then
      if hK : K = E.Observable ⟨W⟩ then
        some (hK.symm ▸ E.equationResidual ⟨W⟩ B (hI ▸ i) a) else none else none⟩

/-- Reading the native observable carrier has no dependence on a selected ring presentation. -/
theorem observableType_read (E : ArchitecturalEquationSystem C) (W : ArchCtx A) :
    observableType (read E) W = E.Observable ⟨W⟩ := rfl

/-- Native point readings satisfy all exact activation conditions. -/
theorem read_isTyped (E : ArchitecturalEquationSystem C) : IsTyped C (read E) where
  observable W := IndependentRingPrimitive.Carrier.read_isTyped
    ⟨E.Observable ⟨W⟩, E.observableCommRing ⟨W⟩⟩
  role I i := by
    classical
    by_cases h : I = E.Index <;> simp [read, index, h]
  restriction W V K L x := by
    classical
    by_cases h : C.le W V <;>
      by_cases hK : K = E.Observable ⟨W⟩ <;>
        by_cases hL : L = E.Observable ⟨V⟩ <;>
          simp [read, observableType_read, h, hK, hL]
  violation W I K i a := by
    classical
    by_cases hI : I = E.Index <;> by_cases hK : K = E.Observable ⟨W⟩ <;>
      simp [read, index, observableType_read, hI, hK]
  residual W B I K i a := by
    classical
    by_cases hI : I = E.Index <;> by_cases hK : K = E.Observable ⟨W⟩ <;>
      simp [read, index, observableType_read, hI, hK]

/-- The collected role is the native role at the same equation index. -/
theorem role_read (E : ArchitecturalEquationSystem C) (i : E.Index) :
    role (read E) (read_isTyped E) i = E.role i := by
  simp [role, read, index]

/-- Collected restriction values agree with the original native ring hom at every point. -/
theorem restrict_read (E : ArchitecturalEquationSystem C) {W V : ArchCtx A}
    (h : C.le W V) (x : E.Observable ⟨V⟩) :
    restrict (read E) (read_isTyped E) (W := W) (V := V) h x =
      E.restrict (homOfLE h) x := by
  simp [restrict, read, observableType, observable, IndependentRingPrimitive.Carrier.carrier,
    IndependentRingPrimitive.Carrier.read, h]

/-- The collected restriction function is the native hom's complete point family. -/
theorem restrict_read_function (E : ArchitecturalEquationSystem C) {W V : ArchCtx A}
    (h : C.le W V) :
    restrict (read E) (read_isTyped E) (W := W) (V := V) h =
      fun x => E.restrict (homOfLE h) x := funext (restrict_read E h)

/-- Collected symbolic violation coordinates agree with native evaluations. -/
theorem violation_read (E : ArchitecturalEquationSystem C) (W : ArchCtx A)
    (i : E.Index) (a : U.Atom) :
    violation (read E) (read_isTyped E) W i a = E.violationCoordinate ⟨W⟩ i a := by
  simp [violation, read, index, observableType, observable, IndependentRingPrimitive.Carrier.carrier,
    IndependentRingPrimitive.Carrier.read]

/-- Collected residual coordinates agree with the native object-dependent evaluations. -/
theorem residual_read (E : ArchitecturalEquationSystem C) (W : ArchCtx A)
    (B : ArchitectureObject U) (i : E.Index) (a : U.Atom) :
    residual (read E) (read_isTyped E) W B i a = E.equationResidual ⟨W⟩ B i a := by
  simp [residual, read, index, observableType, observable, IndependentRingPrimitive.Carrier.carrier,
    IndependentRingPrimitive.Carrier.read]

/-- Every reconstructed observable ring is the original complete native ring structure. -/
theorem observableRing_read (E : ArchitecturalEquationSystem C) (W : ArchCtx A)
    (hr : IndependentRingPrimitive.Carrier.IsLawful
      (observable (read E) W) ((read_isTyped E).observable W)) :
    observableRing (read E) (read_isTyped E) W hr = E.observableCommRing ⟨W⟩ := by
  exact (IndependentRingPrimitive.assemble_congr hr
    (IndependentRingPrimitive.read_isLawful (E.observableCommRing ⟨W⟩))
    (IndependentRingPrimitive.Carrier.active_read
      ⟨E.Observable ⟨W⟩, E.observableCommRing ⟨W⟩⟩)).trans
    (IndependentRingPrimitive.assemble_read (E.observableCommRing ⟨W⟩))

/-- All native equation laws generate the independent local preservation equations. -/
theorem read_isLawful (E : ArchitecturalEquationSystem C) : IsLawful (read E) (read_isTyped E) where
  ring W := IndependentRingPrimitive.Carrier.read_isLawful
    ⟨E.Observable ⟨W⟩, E.observableCommRing ⟨W⟩⟩
  restriction W V h := by
    rw [observableRing_read, observableRing_read]
    simpa only [restrict_read_function] using IndependentRingPrimitive.Hom.read_isLawful
      (E.restrict (homOfLE h))
  identity W x := by
    simpa only [restrict_read] using E.restrict_id ⟨W⟩ x
  composition W V X h g x := by
    simpa only [restrict_read] using E.restrict_comp (homOfLE h) (homOfLE g) x
  violation W V h i a := by
    simpa only [restrict_read, violation_read] using E.violationCoordinate_restrict (homOfLE h) i a
  residual W V h B i a := by
    simpa only [restrict_read, residual_read] using E.equationResidual_restrict (homOfLE h) B i a

/-- Native equation systems are determined by every computational field, with their dependencies. -/
theorem equation_ext {E F : ArchitecturalEquationSystem C}
    (hi : E.Index = F.Index) (hr : HEq E.role F.role)
    (ho : E.Observable = F.Observable)
    (hc : HEq E.observableCommRing F.observableCommRing)
    (hf : HEq (@E.restrict) (@F.restrict))
    (hv : HEq E.violationCoordinate F.violationCoordinate)
    (he : HEq E.equationResidual F.equationResidual) : E = F := by
  cases E
  cases F
  cases hi
  cases hr
  cases ho
  cases hc
  cases hf
  cases hv
  cases he
  rfl

/-- Equal source and target ring structures reduce heterogeneous hom equality to point values. -/
theorem ringHom_heq_of_points {K L : Type u}
    (RK SK : CommRing K) (RL SL : CommRing L) (hK : RK = SK) (hL : RL = SL)
    (f : letI := RK; letI := RL; K →+* L)
    (g : letI := SK; letI := SL; K →+* L)
    (h : ∀ x, f x = g x) : HEq f g := by
  cases hK
  cases hL
  apply heq_of_eq
  exact RingHom.ext h

/-- Assemble-after-read recovers every field of the native equation system. -/
theorem assemble_read (E : ArchitecturalEquationSystem C) :
    assemble (read E) (read_isTyped E) (read_isLawful E) = E := by
  apply equation_ext (E := assemble (read E) (read_isTyped E) (read_isLawful E)) (F := E)
  · rfl
  · apply heq_of_eq
    funext i
    exact role_read E i
  · rfl
  · apply heq_of_eq
    funext W
    exact observableRing_read E W.ctx ((read_isLawful E).ring W.ctx)
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro V V' hV
    cases hV
    apply Function.hfunext rfl
    intro f f' hf
    cases hf
    apply ringHom_heq_of_points
      (observableRing (read E) (read_isTyped E) V.ctx ((read_isLawful E).ring V.ctx))
      (E.observableCommRing V)
      (observableRing (read E) (read_isTyped E) W.ctx ((read_isLawful E).ring W.ctx))
      (E.observableCommRing W)
      (observableRing_read E V.ctx ((read_isLawful E).ring V.ctx))
      (observableRing_read E W.ctx ((read_isLawful E).ring W.ctx))
    intro x
    exact restrict_read E (leOfHom f) x
  · apply heq_of_eq
    funext W i a
    exact violation_read E W.ctx i a
  · apply heq_of_eq
    funext W B i a
    exact residual_read E W.ctx B i a

/-- An inactive optional response is uniquely none. -/
theorem option_none {T : Type u} (x : Option T) (h : ¬ x.isSome) : x = none := by
  cases x <;> simp_all

/-- Native assembly followed by reading restores all six query constructors and inactive cases. -/
theorem read_assemble (t : Table A) (ht : IsTyped C t) (hl : IsLawful t ht) :
    read (assemble t ht hl) = t := by
  classical
  funext q
  cases q with
  | index => rfl
  | role I i =>
    apply ULift.ext
    by_cases hI : I = index t
    · subst I
      simp [read, assemble, role, Option.some_get]
    · have hn := option_none _ (mt (ht.role I i).1 hI)
      simp [read, assemble, hI, hn]
  | observable W q =>
    change IndependentRingPrimitive.Carrier.read
      (IndependentRingPrimitive.Carrier.assemble (observable t W) (ht.observable W) (hl.ring W)) q =
        observable t W q
    exact congrFun (IndependentRingPrimitive.Carrier.read_assemble
      (observable t W) (ht.observable W) (hl.ring W)) q
  | restriction W V K L x =>
    apply ULift.ext
    by_cases h : C.le W V
    · by_cases hK : K = observableType t W
      · subst K
        by_cases hL : L = observableType t V
        · subst L
          simp [read, assemble, IndependentRingPrimitive.Hom.assemble, restrict, h, Option.some_get]
        · have hn := option_none _
            (fun hx => hL ((ht.restriction W V (observableType t W) L x).1 hx).2.2)
          simp [read, assemble, h, hL, hn]
      · have hn := option_none _
          (fun hx => hK ((ht.restriction W V K L x).1 hx).2.1)
        simp [read, assemble, hK, hn]
    · have hn := option_none _ (fun hx => h ((ht.restriction W V K L x).1 hx).1)
      simp [read, h, hn]
  | violation W I K i a =>
    apply ULift.ext
    by_cases hI : I = index t
    · subst I
      by_cases hK : K = observableType t W
      · subst K
        simp [read, assemble, violation, Option.some_get]
      · have hn := option_none _ (fun hx => hK ((ht.violation W _ K i a).1 hx).2)
        simp [read, assemble, hK, hn]
    · have hn := option_none _ (fun hx => hI ((ht.violation W I K i a).1 hx).1)
      simp [read, assemble, hI, hn]
  | residual W B I K i a =>
    apply ULift.ext
    by_cases hI : I = index t
    · subst I
      by_cases hK : K = observableType t W
      · subst K
        simp [read, assemble, residual, Option.some_get]
      · have hn := option_none _ (fun hx => hK ((ht.residual W B _ K i a).1 hx).2)
        simp [read, assemble, hK, hn]
    · have hn := option_none _ (fun hx => hI ((ht.residual W B I K i a).1 hx).1)
      simp [read, assemble, hI, hn]

/-- All native equation systems on the context preorder have independent lawful point tables. -/
noncomputable def readingEquiv :
    ArchitecturalEquationSystem C ≃ {t : Table A // ∃ ht : IsTyped C t, IsLawful t ht} where
  toFun E := ⟨read E, read_isTyped E, read_isLawful E⟩
  invFun t := assemble t.val t.property.choose t.property.choose_spec
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property.choose t.property.choose_spec)

/-- Point readings separate complete equation systems, including symbolic and residual coordinates. -/
theorem read_injective : Function.Injective (read (C := C)) := by
  intro E F h
  apply (readingEquiv (C := C)).injective
  exact Subtype.ext h

/-- Remove all restriction responses while preserving rings, roles, and coordinates. -/
def eraseRestrictions (t : Table A) : Table A
  | .restriction _ _ _ _ _ => ⟨none⟩
  | q => t q

/-- Missing the restriction of zero on a reflexive context is rejected by totality. -/
theorem eraseRestrictions_not_typed (E : ArchitecturalEquationSystem C) (W : ArchCtx A) :
    ¬ IsTyped C (eraseRestrictions (read E)) := by
  intro ht
  have h := (ht.restriction W W (E.Observable ⟨W⟩) (E.Observable ⟨W⟩)
    (0 : E.Observable ⟨W⟩)).2 ⟨C.refl W, rfl, rfl⟩
  simp [eraseRestrictions] at h

namespace Circuit

/-- One finite detector code is read at a candidate equation index. -/
inductive Query where
  /-- Read the code at one point of a candidate index carrier. -/
  | code (I : Type u) (i : I)

/-- Circuit responses carry finite syntax only. -/
abbrev Table (U : AtomCarrier.{u}) := Query.{u} → Option (CircuitDetectorCode U)

/-- Exactly the declared equation-index carrier has active circuit responses. -/
def IsTyped (I : Type u) (c : Table U) : Prop :=
  ∀ J j, (c (.code J j)).isSome ↔ J = I

/-- Collect one active finite detector code. -/
def code {I : Type u} (c : Table U) (hc : IsTyped I c) (i : I) : CircuitDetectorCode U :=
  (c (.code I i)).get ((hc I i).2 rfl)

/-- Assemble native circuit syntax from its finite-code responses. -/
def assemble (E : ArchitecturalEquationSystem C) (c : Table U) (hc : IsTyped E.Index c) :
    EquationCircuitReading E := ⟨code c hc⟩

/-- Read native circuit codes with unique inactive responses. -/
noncomputable def read {E : ArchitecturalEquationSystem C} (R : EquationCircuitReading E) :
    Table U := by
  classical
  intro q
  cases q with
  | code I i => exact if h : I = E.Index then some (R.code (h ▸ i)) else none

/-- Native circuit responses meet exact carrier activation. -/
theorem read_isTyped {E : ArchitecturalEquationSystem C} (R : EquationCircuitReading E) :
    IsTyped E.Index (read R) := by
  classical
  intro I i
  by_cases h : I = E.Index <;> simp [read, h]

/-- Collecting a native circuit response returns the same finite code. -/
theorem code_read {E : ArchitecturalEquationSystem C} (R : EquationCircuitReading E)
    (i : E.Index) : code (read R) (read_isTyped R) i = R.code i := by
  simp [code, read]

/-- Every native circuit family is recovered. -/
theorem assemble_read {E : ArchitecturalEquationSystem C} (R : EquationCircuitReading E) :
    assemble E (read R) (read_isTyped R) = R :=
  EquationCircuitReading.ext (funext (code_read R))

/-- Reading the assembled family also recovers all inactive candidate responses. -/
theorem read_assemble (E : ArchitecturalEquationSystem C) (c : Table U)
    (hc : IsTyped E.Index c) : read (assemble E c hc) = c := by
  classical
  funext q
  cases q with
  | code I i =>
    by_cases h : I = E.Index
    · subst I
      simp [read, assemble, code, Option.some_get]
    · have hn := option_none _ (mt (hc I i).1 h)
      simp [read, h, hn]

/-- Every accepted matching finite datum has a context and Atom with nonzero residual. -/
def IsLawful (t : IndependentEquationPrimitive.Table A) (ht : IndependentEquationPrimitive.IsTyped C t)
    (c : Table U) (hc : IsTyped (index t) c) : Prop :=
  ∀ (i : index t) (B : ArchitectureObject U) (d : FiniteCircuitDatum U),
    d.Matches B → (code c hc i).eval d = true →
      ∃ (W : ArchCtx A) (a : U.Atom),
        residual t ht W B i a ≠
          IndependentRingPrimitive.Carrier.active (observable t W) (ht.observable W) .zero

/-- A local nonzero coordinate refutes native residual vanishing. -/
theorem assemble_sound (t : IndependentEquationPrimitive.Table A)
    (ht : IndependentEquationPrimitive.IsTyped C t) (hl : IndependentEquationPrimitive.IsLawful t ht)
    (c : Table U) (hc : IsTyped (index t) c) (hs : IsLawful t ht c hc) :
    (assemble (IndependentEquationPrimitive.assemble t ht hl) c hc).Sound := by
  intro i B d hm ha he
  obtain ⟨W, a, hn⟩ := hs i B d hm ha
  exact hn (he ⟨W⟩ a)

/-- Native soundness supplies a local context and Atom witness, without storing a chosen witness. -/
theorem read_isLawful (E : ArchitecturalEquationSystem C) (R : EquationCircuitReading E)
    (hs : R.Sound) :
    IsLawful (IndependentEquationPrimitive.read E) (IndependentEquationPrimitive.read_isTyped E)
      (read R) (read_isTyped R) := by
  intro i B d hm ha
  change (code (read R) (read_isTyped R) i).eval d = true at ha
  rw [code_read] at ha
  have hn := hs i B d hm ha
  change ¬ (∀ W a, E.equationResidual W B i a = 0) at hn
  push_neg at hn
  obtain ⟨W, a, h⟩ := hn
  refine ⟨W.ctx, a, ?_⟩
  rw [residual_read]
  have hz := congrFun (IndependentRingPrimitive.Carrier.active_read
    ⟨E.Observable W, E.observableCommRing W⟩) IndependentRingPrimitive.Query.zero
  exact hz ▸ h

/-- Soundness of assembled syntax is equivalent to the independent nonzero-witness law. -/
theorem lawful_iff_sound (t : IndependentEquationPrimitive.Table A)
    (ht : IndependentEquationPrimitive.IsTyped C t) (hl : IndependentEquationPrimitive.IsLawful t ht)
    (c : Table U) (hc : IsTyped (index t) c) :
    IsLawful t ht c hc ↔
      (assemble (IndependentEquationPrimitive.assemble t ht hl) c hc).Sound := by
  constructor
  · exact assemble_sound t ht hl c hc
  · intro hs i B d hm ha
    have hn := hs i B d hm ha
    change ¬ (∀ (W : ContextCategoryObject C) a, residual t ht W.ctx B i a = _) at hn
    push_neg at hn
    obtain ⟨W, a, h⟩ := hn
    exact ⟨W.ctx, a, h⟩

end Circuit

end AAT.AG.LocalSemanticReconstruction.IndependentEquationPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentEquationPrimitive
