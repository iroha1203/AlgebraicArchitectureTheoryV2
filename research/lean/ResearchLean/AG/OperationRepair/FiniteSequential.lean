import ResearchLean.AG.OperationRepair.Sequential

/-! Finite iterations of operation-preserving repair quotients. -/
namespace AAT.AG.OperationRepair
universe u v w
variable {S : Type u} {E : Type v} (T : OperationSystem S E)

/-- The union of a finite list of requests. -/
def listRequest (requests : List (S → S → Prop)) (x y : S) : Prop :=
  ∃ R ∈ requests, R x y

@[simp] theorem listRequest_nil :
    listRequest ([] : List (S → S → Prop)) = (fun _ _ => False) := by
  funext x y
  simp [listRequest]

@[simp] theorem listRequest_cons (R : S → S → Prop)
    (requests : List (S → S → Prop)) (x y : S) :
    listRequest (R :: requests) x y ↔ R x y ∨ listRequest requests x y := by
  simp [listRequest]

/-- Adding a request to a finite family joins its generated congruence. -/
theorem generated_listRequest_cons (R : S → S → Prop)
    (requests : List (S → S → Prop)) :
    generated T (listRequest (R :: requests)) =
      generated T (listRequest requests) ⊔ generated T R := by
  apply le_antisymm
  · apply (generated_le_iff T _).mpr
    intro x y h
    rcases (listRequest_cons R requests x y).mp h with hr | hs
    · exact (show generated T R ≤ _ from le_sup_right) (generated_contains T hr)
    · exact (show generated T (listRequest requests) ≤ _ from le_sup_left)
        (generated_contains T hs)
  · apply sup_le
    · apply (generated_le_iff T _).mpr
      intro x y h
      exact generated_contains T ((listRequest_cons R requests x y).mpr (Or.inr h))
    · apply (generated_le_iff T _).mpr
      intro x y h
      exact generated_contains T ((listRequest_cons R requests x y).mpr (Or.inl h))

/-- Literal image of a request under a surjective operation-preserving map. -/
def mappedRequest {Q : Type u} (q : S → Q) (R : S → S → Prop)
    (a b : Q) : Prop := ∃ x y, R x y ∧ q x = a ∧ q y = b

/-- The kernel after adding a request to any surjective operation quotient is
the join of the original kernel with the generated request. -/
theorem generated_mappedRequest_kernel {Q : Type u}
    (U : OperationSystem Q E) (q : S → Q)
    (hsurj : Function.Surjective q)
    (hstep : ∀ e x, q (T.step e x) = U.step e (q x))
    (c : OperationCongruence T) (hker : Setoid.ker q = c.setoid)
    (R : S → S → Prop) :
    Setoid.ker (fun x =>
      Quotient.mk (generated U (mappedRequest q R)).setoid (q x)) =
      (c ⊔ generated T R).setoid := by
  let k := generated U (mappedRequest q R)
  let d : OperationCongruence T := c ⊔ generated T R
  let q' : S → Quotient k.setoid := fun x => Quotient.mk k.setoid (q x)
  let rep : Q → S := fun z => Classical.choose (hsurj z)
  have hrep (z : Q) : q (rep z) = z := Classical.choose_spec (hsurj z)
  let g : Q → Quotient d.setoid := fun z => Quotient.mk d.setoid (rep z)
  have hg (x : S) : g (q x) = Quotient.mk d.setoid x := by
    apply Quotient.sound
    have heq : q (rep (q x)) = q x := hrep (q x)
    exact (show c ≤ d from le_sup_left)
      (show c.setoid.r (rep (q x)) x from hker ▸ heq)
  have hgstep (e : E) (z : Q) : g (U.step e z) =
      (quotientSystem T d).step e (g z) := by
    obtain ⟨x, rfl⟩ := hsurj z
    rw [← hstep e x, hg, hg, quotientSystem_step_mk]
  let kg : OperationCongruence U := {
    setoid := Setoid.ker g
    stable := by
      intro e a b hab
      change g (U.step e a) = g (U.step e b)
      rw [hgstep, hgstep, hab] }
  have hk_le : k ≤ kg := by
    apply (generated_le_iff U kg).mpr
    intro a b hab
    obtain ⟨x, y, hr, rfl, rfl⟩ := hab
    change g (q x) = g (q y)
    rw [hg, hg]
    exact Quotient.sound ((show generated T R ≤ d from le_sup_right)
      (generated_contains T hr))
  apply Setoid.ext
  intro x y
  constructor
  · intro hxy
    have hq : k.setoid.r (q x) (q y) := Quotient.eq.mp hxy
    have hgy : g (q x) = g (q y) := hk_le hq
    rw [hg, hg] at hgy
    exact Quotient.eq.mp hgy
  · intro hxy
    let pull : OperationCongruence T := {
      setoid := Setoid.ker q'
      stable := by
        intro e a b hab
        change q' (T.step e a) = q' (T.step e b)
        change Quotient.mk k.setoid (q (T.step e a)) =
          Quotient.mk k.setoid (q (T.step e b))
        rw [hstep, hstep]
        exact Quotient.sound (k.stable e (q a) (q b) (Quotient.eq.mp hab)) }
    have hc : c ≤ pull := by
      intro a b hab
      have heq : q a = q b := (show (Setoid.ker q).r a b from hker.symm ▸ hab)
      change Quotient.mk k.setoid (q a) = Quotient.mk k.setoid (q b)
      rw [heq]
    have hR : generated T R ≤ pull := by
      apply (generated_le_iff T pull).mpr
      intro a b hab
      change Quotient.mk k.setoid (q a) = Quotient.mk k.setoid (q b)
      exact Quotient.sound (generated_contains U
        (show mappedRequest q R (q a) (q b) from ⟨a, b, hab, rfl, rfl⟩))
    exact (show d ≤ pull from sup_le hc hR) hxy

/-- A concrete sequence of quotient steps, together with its proved kernel
invariant. The constructor below starts from raw operations and requests. -/
structure SequentialStage (requests : List (S → S → Prop)) where
  Carrier : Type u
  system : OperationSystem Carrier E
  read : S → Carrier
  surjective : Function.Surjective read
  step_comm : ∀ e x, read (T.step e x) = system.step e (read x)
  kernel_eq : Setoid.ker read = (generated T (listRequest requests)).setoid

/-- The empty sequence is the original state system. -/
def sequentialBase : SequentialStage T [] where
  Carrier := S
  system := T
  read := id
  surjective := fun x => ⟨x, rfl⟩
  step_comm := by intro e x; rfl
  kernel_eq := by
    have hbot : generated T (listRequest ([] : List (S → S → Prop))) = ⊥ := by
      rw [listRequest_nil, generated_empty]
    rw [hbot]
    let eqC : OperationCongruence T := {
      setoid := Setoid.ker (id : S → S)
      stable := by
        intro e x y h
        change x = y at h
        subst y
        rfl }
    have heqbot : eqC = (⊥ : OperationCongruence T) := by
      apply le_antisymm
      · intro x y h
        change x = y at h
        subst y
        exact (⊥ : OperationCongruence T).setoid.iseqv.refl _
      · exact bot_le
    rw [← heqbot]

/-- Add one actual quotient step using the image of the next raw request
under the composite source map constructed so far. -/
def sequentialExtend {requests : List (S → S → Prop)}
    (st : SequentialStage T requests) (R : S → S → Prop) :
    SequentialStage T (R :: requests) := by
  let k := generated st.system (mappedRequest st.read R)
  refine {
    Carrier := Quotient k.setoid
    system := quotientSystem st.system k
    read := fun x => Quotient.mk k.setoid (st.read x)
    surjective := ?_
    step_comm := ?_
    kernel_eq := ?_ }
  · intro z
    induction z using Quotient.inductionOn with
    | _ a =>
      obtain ⟨x, hx⟩ := st.surjective a
      exact ⟨x, by simp only [hx]⟩
  · intro e x
    rw [st.step_comm]
    rfl
  · rw [generated_listRequest_cons]
    exact generated_mappedRequest_kernel T st.system st.read st.surjective
      st.step_comm (generated T (listRequest requests)) st.kernel_eq R

/-- Execute a finite list by successively quotienting by the image of each
request. The recursion applies the tail first, so every chronological order
is represented by reversing its list. -/
def sequentialList (T : OperationSystem S E) :
    (requests : List (S → S → Prop)) → SequentialStage T requests
  | [] => sequentialBase T
  | R :: rest => sequentialExtend T (sequentialList T rest) R

/-- Every concrete finite sequence is canonically equivalent over `S` to
the quotient by the union of its raw requests. -/
noncomputable def sequentialListEquiv (requests : List (S → S → Prop)) :
    (sequentialList T requests).Carrier ≃
      Quotient (generated T (listRequest requests)).setoid :=
  let st := sequentialList T requests
  (Setoid.quotientKerEquivOfSurjective st.read st.surjective).symm.trans
    (Quotient.congr (Equiv.refl _) (fun a b => by simp only [st.kernel_eq, Equiv.refl_apply]))

@[simp] theorem sequentialListEquiv_read (requests : List (S → S → Prop)) (x : S) :
    sequentialListEquiv T requests ((sequentialList T requests).read x) =
      Quotient.mk (generated T (listRequest requests)).setoid x := by
  simp [sequentialListEquiv, Setoid.quotientKerEquivOfSurjective]
  apply Quotient.sound
  have h := Function.rightInverse_surjInv
    (sequentialList T requests).surjective ((sequentialList T requests).read x)
  exact (sequentialList T requests).kernel_eq.symm ▸ h

/-- The canonical equivalence preserves every named operation. -/
theorem sequentialListEquiv_step (requests : List (S → S → Prop))
    (e : E) (z : (sequentialList T requests).Carrier) :
    sequentialListEquiv T requests
      ((sequentialList T requests).system.step e z) =
    (quotientSystem T (generated T (listRequest requests))).step e
      (sequentialListEquiv T requests z) := by
  obtain ⟨x, rfl⟩ := (sequentialList T requests).surjective z
  rw [← (sequentialList T requests).step_comm, sequentialListEquiv_read,
    sequentialListEquiv_read, quotientSystem_step_mk]

/-- Repairability of a finite request list is exactly repairability of
each member. -/
theorem listRequest_repairable_iff {O : Type w} (observe : S → O)
    (requests : List (S → S → Prop)) :
    generated T (listRequest requests) ≤ behavior T observe ↔
      ∀ R ∈ requests, generated T R ≤ behavior T observe := by
  rw [generated_le_iff]
  constructor
  · intro h R hR
    apply (generated_le_iff T _).mpr
    intro x y hxy
    exact h x y ⟨R, hR, hxy⟩
  · intro h x y hxy
    obtain ⟨R, hR, hxy⟩ := hxy
    exact h R hR (generated_contains T hxy)

/-- Observation induced on the concrete final carrier of any repairable
finite sequence. -/
noncomputable def sequentialObservation {O : Type w} (observe : S → O)
    (requests : List (S → S → Prop))
    (_h : generated T (listRequest requests) ≤ behavior T observe) :
    (sequentialList T requests).Carrier → O :=
  fun z => observe (Function.surjInv (sequentialList T requests).surjective z)

@[simp] theorem sequentialObservation_read {O : Type w} (observe : S → O)
    (requests : List (S → S → Prop))
    (h : generated T (listRequest requests) ≤ behavior T observe) (x : S) :
    sequentialObservation T observe requests h ((sequentialList T requests).read x) =
      observe x := by
  unfold sequentialObservation
  have hs := Function.rightInverse_surjInv
    (sequentialList T requests).surjective ((sequentialList T requests).read x)
  have hk : (generated T (listRequest requests)).setoid.r
      (Function.surjInv (sequentialList T requests).surjective
        ((sequentialList T requests).read x)) x := by
    rw [← (sequentialList T requests).kernel_eq]
    exact hs
  exact (behavior_le_kernel T observe) (h hk)

/-- The finite-sequence comparison preserves the descended observation. -/
theorem sequentialListEquiv_observation {O : Type w} (observe : S → O)
    (requests : List (S → S → Prop))
    (h : generated T (listRequest requests) ≤ behavior T observe)
    (z : (sequentialList T requests).Carrier) :
    quotientObservation T observe (generated T (listRequest requests)) h
      (sequentialListEquiv T requests z) =
    sequentialObservation T observe requests h z := by
  obtain ⟨x, rfl⟩ := (sequentialList T requests).surjective z
  simp only [sequentialListEquiv_read, quotientObservation_mk,
    sequentialObservation_read]

/-- Canonical comparison for any stage with a proved kernel invariant. -/
noncomputable def SequentialStage.canonicalEquiv
    {requests : List (S → S → Prop)} (st : SequentialStage T requests) :
    st.Carrier ≃ Quotient (generated T (listRequest requests)).setoid :=
  (Setoid.quotientKerEquivOfSurjective st.read st.surjective).symm.trans
    (Quotient.congr (Equiv.refl _) (fun a b => by
      simp only [st.kernel_eq, Equiv.refl_apply]))

@[simp] theorem SequentialStage.canonicalEquiv_read
    {requests : List (S → S → Prop)} (st : SequentialStage T requests) (x : S) :
    (SequentialStage.canonicalEquiv T st) (st.read x) =
      Quotient.mk (generated T (listRequest requests)).setoid x := by
  simp [SequentialStage.canonicalEquiv, Setoid.quotientKerEquivOfSurjective]
  apply Quotient.sound
  have h := Function.rightInverse_surjInv st.surjective (st.read x)
  exact st.kernel_eq.symm ▸ h

/-- Canonical comparison from any constructed stage preserves operations. -/
theorem SequentialStage.canonicalEquiv_step
    {requests : List (S → S → Prop)} (st : SequentialStage T requests)
    (e : E) (z : st.Carrier) :
    (SequentialStage.canonicalEquiv T st) (st.system.step e z) =
      (quotientSystem T (generated T (listRequest requests))).step e
        ((SequentialStage.canonicalEquiv T st) z) := by
  obtain ⟨x, rfl⟩ := st.surjective z
  rw [← st.step_comm, SequentialStage.canonicalEquiv_read, SequentialStage.canonicalEquiv_read,
    quotientSystem_step_mk]

/-- The source map determines every comparison between two constructed
stages with the same generated congruence. -/
noncomputable def stageCompare
    {left right : List (S → S → Prop)}
    (a : SequentialStage T left) (b : SequentialStage T right)
    (h : generated T (listRequest left) = generated T (listRequest right)) :
    a.Carrier ≃ b.Carrier :=
  (SequentialStage.canonicalEquiv T a).trans
    ((Quotient.congr (Equiv.refl _) (fun x y => by
      simp only [h, Equiv.refl_apply])).trans (SequentialStage.canonicalEquiv T b).symm)

@[simp] theorem stageCompare_read
    {left right : List (S → S → Prop)}
    (a : SequentialStage T left) (b : SequentialStage T right)
    (h : generated T (listRequest left) = generated T (listRequest right))
    (x : S) :
    stageCompare T a b h (a.read x) = b.read x := by
  apply (SequentialStage.canonicalEquiv T b).injective
  simp [stageCompare, SequentialStage.canonicalEquiv_read]

/-- Any source-commuting comparison is the canonical one. -/
theorem stageCompare_unique
    {left right : List (S → S → Prop)}
    (a : SequentialStage T left) (b : SequentialStage T right)
    (h : generated T (listRequest left) = generated T (listRequest right))
    (f : a.Carrier → b.Carrier) (hf : ∀ x, f (a.read x) = b.read x) :
    f = stageCompare T a b h := by
  funext z
  obtain ⟨x, rfl⟩ := a.surjective z
  exact (hf x).trans (stageCompare_read T a b h x).symm

/-- Composition of finite-stage comparisons equals the direct comparison. -/
theorem stageCompare_coherent
    {aList bList cList : List (S → S → Prop)}
    (a : SequentialStage T aList) (b : SequentialStage T bList)
    (c : SequentialStage T cList)
    (hab : generated T (listRequest aList) = generated T (listRequest bList))
    (hbc : generated T (listRequest bList) = generated T (listRequest cList)) :
    (stageCompare T a b hab).trans (stageCompare T b c hbc) =
      stageCompare T a c (hab.trans hbc) := by
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ := a.surjective z
  simp only [Equiv.trans_apply, stageCompare_read]

/-- Comparisons preserve operations because they commute with the
surjective source maps of the two concrete stage systems. -/
theorem stageCompare_step
    {left right : List (S → S → Prop)}
    (a : SequentialStage T left) (b : SequentialStage T right)
    (h : generated T (listRequest left) = generated T (listRequest right))
    (e : E) (z : a.Carrier) :
    stageCompare T a b h (a.system.step e z) =
      b.system.step e (stageCompare T a b h z) := by
  obtain ⟨x, rfl⟩ := a.surjective z
  rw [← a.step_comm, stageCompare_read, stageCompare_read, b.step_comm]

/-- Observation descended to an arbitrary constructed stage. -/
noncomputable def SequentialStage.observation {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)} (st : SequentialStage T requests)
    (_h : generated T (listRequest requests) ≤ behavior T observe) :
    st.Carrier → O :=
  fun z => observe (Function.surjInv st.surjective z)

@[simp] theorem SequentialStage.observation_read {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)} (st : SequentialStage T requests)
    (h : generated T (listRequest requests) ≤ behavior T observe) (x : S) :
    SequentialStage.observation T observe st h (st.read x) = observe x := by
  unfold SequentialStage.observation
  have hs := Function.rightInverse_surjInv st.surjective (st.read x)
  have hk : (generated T (listRequest requests)).setoid.r
      (Function.surjInv st.surjective (st.read x)) x := by
    rw [← st.kernel_eq]
    exact hs
  exact (behavior_le_kernel T observe) (h hk)

/-- The comparison preserves the descended observation whenever the
common request family is repairable. -/
theorem stageCompare_observation {O : Type w} (observe : S → O)
    {left right : List (S → S → Prop)}
    (a : SequentialStage T left) (b : SequentialStage T right)
    (h : generated T (listRequest left) = generated T (listRequest right))
    (ha : generated T (listRequest left) ≤ behavior T observe)
    (hb : generated T (listRequest right) ≤ behavior T observe)
    (z : a.Carrier) :
    SequentialStage.observation T observe b hb (stageCompare T a b h z) =
      SequentialStage.observation T observe a ha z := by
  obtain ⟨x, rfl⟩ := a.surjective z
  simp only [stageCompare_read, SequentialStage.observation_read]

/-- Extending a repairable stage by a repairable raw request remains
repairable. -/
theorem sequentialExtend_repairable {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)}
    (_st : SequentialStage T requests) (R : S → S → Prop)
    (hcurrent : generated T (listRequest requests) ≤ behavior T observe)
    (hR : generated T R ≤ behavior T observe) :
    generated T (listRequest (R :: requests)) ≤ behavior T observe := by
  rw [generated_listRequest_cons]
  exact sup_le hcurrent hR

/-- At every extension, the image request is repairable with respect to the
observation already descended to the current carrier. -/
theorem sequentialExtend_image_repairable {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)}
    (st : SequentialStage T requests) (R : S → S → Prop)
    (hcurrent : generated T (listRequest requests) ≤ behavior T observe)
    (hR : generated T R ≤ behavior T observe) :
    generated st.system (mappedRequest st.read R) ≤
      behavior st.system (SequentialStage.observation T observe st hcurrent) := by
  apply (le_behavior_iff st.system
    (SequentialStage.observation T observe st hcurrent) _).mpr
  intro a b hab
  obtain ⟨x, rfl⟩ := st.surjective a
  obtain ⟨y, rfl⟩ := st.surjective b
  change SequentialStage.observation T observe st hcurrent (st.read x) =
    SequentialStage.observation T observe st hcurrent (st.read y)
  simp only [SequentialStage.observation_read]
  have hq : (sequentialExtend T st R).read x =
      (sequentialExtend T st R).read y := Quotient.sound hab
  have hk : (generated T (listRequest (R :: requests))).setoid.r x y := by
    rw [← (sequentialExtend T st R).kernel_eq]
    exact hq
  exact (behavior_le_kernel T observe)
    ((sequentialExtend_repairable T observe st R hcurrent hR) hk)

/-- The next stage observation agrees with the current observation on the
actual quotient map of the image-generated congruence. -/
theorem sequentialExtend_observation_comm {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)}
    (st : SequentialStage T requests) (R : S → S → Prop)
    (hcurrent : generated T (listRequest requests) ≤ behavior T observe)
    (hR : generated T R ≤ behavior T observe)
    (a : st.Carrier) :
    SequentialStage.observation T observe (sequentialExtend T st R)
      (sequentialExtend_repairable T observe st R hcurrent hR)
      (Quotient.mk (generated st.system (mappedRequest st.read R)).setoid a) =
    SequentialStage.observation T observe st hcurrent a := by
  obtain ⟨x, rfl⟩ := st.surjective a
  change SequentialStage.observation T observe (sequentialExtend T st R)
    (sequentialExtend_repairable T observe st R hcurrent hR)
    ((sequentialExtend T st R).read x) =
    SequentialStage.observation T observe st hcurrent (st.read x)
  simp only [SequentialStage.observation_read]

/-- A stage constructed from repairable requests. Its observation is obtained
from `SequentialStage.observation`; the kernel and repairability proofs are
built by the base and extension constructors below. -/
structure RepairableSequentialStage {O : Type w} (observe : S → O)
    (requests : List (S → S → Prop)) where
  stage : SequentialStage T requests
  repairable : generated T (listRequest requests) ≤ behavior T observe

/-- The empty stage has its original observation. -/
def repairableSequentialBase {O : Type w} (observe : S → O) :
    RepairableSequentialStage T observe [] where
  stage := sequentialBase T
  repairable := (listRequest_repairable_iff T observe []).mpr (by simp)

/-- Every extension is an actual repair quotient step: its image request is
repairable for the current descended observation. -/
def repairableSequentialExtend {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)}
    (st : RepairableSequentialStage T observe requests)
    (R : S → S → Prop) (hR : generated T R ≤ behavior T observe) :
    RepairableSequentialStage T observe (R :: requests) where
  stage := sequentialExtend T st.stage R
  repairable := sequentialExtend_repairable T observe st.stage R st.repairable hR

/-- The next request's image is repairable against the current stage's
actually descended observation, at every constructed extension. -/
theorem repairableSequentialExtend_image {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)}
    (st : RepairableSequentialStage T observe requests)
    (R : S → S → Prop) (hR : generated T R ≤ behavior T observe) :
    generated st.stage.system (mappedRequest st.stage.read R) ≤
      behavior st.stage.system
        (SequentialStage.observation T observe st.stage st.repairable) :=
  sequentialExtend_image_repairable T observe st.stage R st.repairable hR

/-- The observation of each extension agrees with the previous observation
on that step's actual quotient map. -/
theorem repairableSequentialExtend_observation {O : Type w} (observe : S → O)
    {requests : List (S → S → Prop)}
    (st : RepairableSequentialStage T observe requests)
    (R : S → S → Prop) (hR : generated T R ≤ behavior T observe)
    (a : st.stage.Carrier) :
    SequentialStage.observation T observe
      (repairableSequentialExtend T observe st R hR).stage
      (repairableSequentialExtend T observe st R hR).repairable
      (Quotient.mk (generated st.stage.system
        (mappedRequest st.stage.read R)).setoid a) =
    SequentialStage.observation T observe st.stage st.repairable a :=
  sequentialExtend_observation_comm T observe st.stage R st.repairable hR a

/-- Binary syntax for arbitrary orders and parenthesizations of a finite
family of repair requests. -/
inductive RequestTree (S : Type u) where
  | empty
  | leaf (R : S → S → Prop)
  | branch (left right : RequestTree S)

namespace RequestTree

def leaves : RequestTree S → List (S → S → Prop)
  | .empty => []
  | .leaf R => [R]
  | .branch left right => leaves left ++ leaves right

end RequestTree

/-- Flat leafwise evaluation of a tree. Each leaf adds the image of its raw
request under the composite source map. Grouped brackets are evaluated by
`applyGroupedTree` below. -/
def applyRequestTree : RequestTree S →
    (Σ requests : List (S → S → Prop), SequentialStage T requests) →
      Σ requests : List (S → S → Prop), SequentialStage T requests
  | .empty, start => start
  | .leaf R, ⟨requests, st⟩ => ⟨R :: requests, sequentialExtend T st R⟩
  | .branch left right, start =>
      applyRequestTree right (applyRequestTree left start)

/-- The flat leafwise quotient of a request tree. -/
def treeStage (tree : RequestTree S) :
    Σ requests : List (S → S → Prop), SequentialStage T requests :=
  applyRequestTree T tree ⟨[], sequentialBase T⟩

/-- The accumulated request list of a tree application is a permutation
of its leaves followed by the previous requests. -/
theorem applyRequestTree_perm (tree : RequestTree S)
    (start : Σ requests : List (S → S → Prop), SequentialStage T requests) :
    (applyRequestTree T tree start).1.Perm (tree.leaves.reverse ++ start.1) := by
  induction tree generalizing start with
  | empty => simp [applyRequestTree, RequestTree.leaves]
  | leaf R =>
      cases start with
      | mk requests st => simp [applyRequestTree, RequestTree.leaves]
  | branch left right ihl ihr =>
      have h := (ihr (applyRequestTree T left start)).trans
        (List.Perm.append_left _ (ihl start))
      simpa only [applyRequestTree, RequestTree.leaves, List.reverse_append,
        List.append_assoc] using h

/-- Union of two finite request lists. -/
theorem listRequest_append (left right : List (S → S → Prop))
    (x y : S) :
    listRequest (left ++ right) x y ↔
      listRequest left x y ∨ listRequest right x y := by
  constructor
  · rintro ⟨R, hR, hxy⟩
    rcases List.mem_append.mp hR with hL | hR
    · exact Or.inl ⟨R, hL, hxy⟩
    · exact Or.inr ⟨R, hR, hxy⟩
  · rintro (⟨R, hL, hxy⟩ | ⟨R, hR, hxy⟩)
    · exact ⟨R, List.mem_append.mpr (Or.inl hL), hxy⟩
    · exact ⟨R, List.mem_append.mpr (Or.inr hR), hxy⟩

/-- A genuinely grouped parenthesization: evaluate the left subtree as
nested quotient steps, then quotient once by the union of all requests in the
right subtree. Thus `(a·b)·c` and `a·(b·c)` have different quotient carriers. -/
def applyGroupedTree : RequestTree S →
    (Σ requests : List (S → S → Prop), SequentialStage T requests) →
      Σ requests : List (S → S → Prop), SequentialStage T requests
  | .empty, start => start
  | .leaf R, ⟨requests, st⟩ => ⟨R :: requests, sequentialExtend T st R⟩
  | .branch left right, start =>
      let next := applyGroupedTree left start
      ⟨listRequest right.leaves :: next.1,
        sequentialExtend T next.2 (listRequest right.leaves)⟩

/-- Grouped evaluation carries exactly the union of the leaves and previous
requests, even though its intermediate quotient carriers depend on brackets. -/
theorem applyGroupedTree_request (tree : RequestTree S)
    (start : Σ requests : List (S → S → Prop), SequentialStage T requests) :
    listRequest (applyGroupedTree T tree start).1 =
      listRequest (tree.leaves ++ start.1) := by
  induction tree generalizing start with
  | empty => rfl
  | leaf R =>
      cases start with
      | mk requests st => rfl
  | branch left right ihl ihr =>
      funext x y
      apply propext
      simp only [applyGroupedTree, RequestTree.leaves]
      rw [listRequest_cons, ihl, listRequest_append, listRequest_append,
        listRequest_append]
      tauto

/-- The actual quotient system selected by a grouped binary tree. -/
def groupedTreeStage (tree : RequestTree S) :
    Σ requests : List (S → S → Prop), SequentialStage T requests :=
  applyGroupedTree T tree ⟨[], sequentialBase T⟩

/-- The grouped construction has the union relation of its leaves. -/
theorem groupedTreeStage_request (tree : RequestTree S) :
    listRequest (groupedTreeStage T tree).1 = listRequest tree.leaves := by
  simpa [groupedTreeStage] using
    applyGroupedTree_request T tree ⟨[], sequentialBase T⟩

/-- Permuting a finite list does not change its union relation. -/
theorem listRequest_perm {left right : List (S → S → Prop)}
    (h : left.Perm right) : listRequest left = listRequest right := by
  funext x y
  apply propext
  constructor
  · rintro ⟨R, hR, hxy⟩
    exact ⟨R, h.mem_iff.mp hR, hxy⟩
  · rintro ⟨R, hR, hxy⟩
    exact ⟨R, h.mem_iff.mpr hR, hxy⟩

/-- Execute every branch as a repair quotient, carrying the descended
observation through each stage. The proof argument is exactly repairability
of the raw leaf requests. -/
def applyRepairableGroupedTree {O : Type w} (observe : S → O) :
    (tree : RequestTree S) →
    (start : Σ requests : List (S → S → Prop),
      RepairableSequentialStage T observe requests) →
    (∀ R ∈ tree.leaves, generated T R ≤ behavior T observe) →
      Σ requests : List (S → S → Prop),
        RepairableSequentialStage T observe requests
  | .empty, start, _ => start
  | .leaf R, ⟨requests, st⟩, heach =>
      ⟨R :: requests, repairableSequentialExtend T observe st R
        (heach R (by simp [RequestTree.leaves]))⟩
  | .branch left right, start, heach =>
      let hleft : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe :=
        fun R hR => heach R (by simp [RequestTree.leaves, hR])
      let hright : ∀ R ∈ right.leaves, generated T R ≤ behavior T observe :=
        fun R hR => heach R (by simp [RequestTree.leaves, hR])
      let next := applyRepairableGroupedTree observe left start hleft
      let hblock : generated T (listRequest right.leaves) ≤ behavior T observe :=
        (listRequest_repairable_iff T observe right.leaves).mpr hright
      ⟨listRequest right.leaves :: next.1,
        repairableSequentialExtend T observe next.2
          (listRequest right.leaves) hblock⟩

/-- Every intermediate stage in this evaluation is a repair quotient with
a descended observation and the image-request repairability theorem above. -/
def repairableGroupedTreeStage {O : Type w} (observe : S → O)
    (tree : RequestTree S)
    (heach : ∀ R ∈ tree.leaves, generated T R ≤ behavior T observe) :
    Σ requests : List (S → S → Prop),
      RepairableSequentialStage T observe requests :=
  applyRepairableGroupedTree T observe tree
    ⟨[], repairableSequentialBase T observe⟩ heach

/-- The repair-carrying grouped tree has precisely its leaves' union as
its accumulated request. -/
theorem applyRepairableGroupedTree_request {O : Type w} (observe : S → O)
    (tree : RequestTree S)
    (start : Σ requests : List (S → S → Prop),
      RepairableSequentialStage T observe requests)
    (heach : ∀ R ∈ tree.leaves, generated T R ≤ behavior T observe) :
    listRequest (applyRepairableGroupedTree T observe tree start heach).1 =
      listRequest (tree.leaves ++ start.1) := by
  induction tree generalizing start with
  | empty => rfl
  | leaf R =>
      cases start with
      | mk requests st => rfl
  | branch left right ihl ihr =>
      funext x y
      apply propext
      simp only [applyRepairableGroupedTree, RequestTree.leaves]
      rw [listRequest_cons, ihl, listRequest_append, listRequest_append,
        listRequest_append]
      tauto

/-- The final repair-carrying grouped tree has the same union relation as
its leaves, irrespective of grouping. -/
theorem repairableGroupedTreeStage_request {O : Type w} (observe : S → O)
    (tree : RequestTree S)
    (heach : ∀ R ∈ tree.leaves, generated T R ≤ behavior T observe) :
    listRequest (repairableGroupedTreeStage T observe tree heach).1 =
      listRequest tree.leaves := by
  simpa [repairableGroupedTreeStage] using
    applyRepairableGroupedTree_request T observe tree
      ⟨[], repairableSequentialBase T observe⟩ heach

/-- Grouped trees with permuted leaves generate the same operation
congruence, although their nested quotient carriers may differ. -/
theorem groupedTreeStage_generated_eq_of_perm (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves) :
    generated T (listRequest (groupedTreeStage T left).1) =
      generated T (listRequest (groupedTreeStage T right).1) :=
  congrArg (generated T) ((groupedTreeStage_request T left).trans
    ((listRequest_perm h).trans (groupedTreeStage_request T right).symm))

/-- Canonical comparison of genuinely different grouped nested quotient
systems for any orders and parenthesizations of one finite family. -/
noncomputable def groupedTreeCompare (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves) :
    (groupedTreeStage T left).2.Carrier ≃
      (groupedTreeStage T right).2.Carrier :=
  stageCompare T (groupedTreeStage T left).2 (groupedTreeStage T right).2
    (groupedTreeStage_generated_eq_of_perm T left right h)

@[simp] theorem groupedTreeCompare_read (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves) (x : S) :
    groupedTreeCompare T left right h ((groupedTreeStage T left).2.read x) =
      (groupedTreeStage T right).2.read x :=
  stageCompare_read T (groupedTreeStage T left).2
    (groupedTreeStage T right).2 _ x

/-- Grouped-tree comparisons preserve every descended operation. -/
theorem groupedTreeCompare_step (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves) (e : E)
    (z : (groupedTreeStage T left).2.Carrier) :
    groupedTreeCompare T left right h
      ((groupedTreeStage T left).2.system.step e z) =
    (groupedTreeStage T right).2.system.step e
      (groupedTreeCompare T left right h z) :=
  stageCompare_step T (groupedTreeStage T left).2
    (groupedTreeStage T right).2 _ e z

/-- The source-commuting grouped comparison is unique. -/
theorem groupedTreeCompare_unique (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves)
    (f : (groupedTreeStage T left).2.Carrier →
      (groupedTreeStage T right).2.Carrier)
    (hf : ∀ x, f ((groupedTreeStage T left).2.read x) =
      (groupedTreeStage T right).2.read x) :
    f = groupedTreeCompare T left right h :=
  stageCompare_unique T (groupedTreeStage T left).2
    (groupedTreeStage T right).2 _ f hf

/-- Composing comparisons between grouped parenthesizations gives the
direct comparison, including changes of request order. -/
theorem groupedTreeCompare_coherent (a b c : RequestTree S)
    (hab : a.leaves.Perm b.leaves) (hbc : b.leaves.Perm c.leaves) :
    (groupedTreeCompare T a b hab).trans
      (groupedTreeCompare T b c hbc) =
    groupedTreeCompare T a c (hab.trans hbc) := by
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ := (groupedTreeStage T a).2.surjective z
  simp only [Equiv.trans_apply, groupedTreeCompare_read]

/-- Repairability of a grouped tree is exactly repairability of every leaf. -/
theorem groupedTreeStage_repairable_iff {O : Type w} (observe : S → O)
    (tree : RequestTree S) :
    generated T (listRequest (groupedTreeStage T tree).1) ≤ behavior T observe ↔
      ∀ R ∈ tree.leaves, generated T R ≤ behavior T observe := by
  rw [groupedTreeStage_request]
  exact listRequest_repairable_iff T observe tree.leaves

/-- Grouped-tree comparisons preserve the observation descended at their
final stages under the fixed per-request repairability condition. -/
theorem groupedTreeCompare_observation_of_each {O : Type w}
    (observe : S → O) (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves)
    (heach : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe)
    (z : (groupedTreeStage T left).2.Carrier) :
    SequentialStage.observation T observe (groupedTreeStage T right).2
      ((groupedTreeStage_repairable_iff T observe right).mpr
        (fun R hR => heach R (h.mem_iff.mpr hR)))
      (groupedTreeCompare T left right h z) =
    SequentialStage.observation T observe (groupedTreeStage T left).2
      ((groupedTreeStage_repairable_iff T observe left).mpr heach) z := by
  exact stageCompare_observation T observe (groupedTreeStage T left).2
    (groupedTreeStage T right).2 _ _ _ z

/-- Compare fully repair-carrying grouped trees. Every intermediate
observation and image-request repairability proof is built by the evaluator. -/
noncomputable def repairableGroupedTreeCompare {O : Type w} (observe : S → O)
    (left right : RequestTree S) (h : left.leaves.Perm right.leaves)
    (heach : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe) :
    (repairableGroupedTreeStage T observe left heach).2.stage.Carrier ≃
      (repairableGroupedTreeStage T observe right
        (fun R hR => heach R (h.mem_iff.mpr hR))).2.stage.Carrier :=
  stageCompare T
    (repairableGroupedTreeStage T observe left heach).2.stage
    (repairableGroupedTreeStage T observe right
      (fun R hR => heach R (h.mem_iff.mpr hR))).2.stage
    (congrArg (generated T)
      ((repairableGroupedTreeStage_request T observe left heach).trans
        ((listRequest_perm h).trans
          (repairableGroupedTreeStage_request T observe right
            (fun R hR => heach R (h.mem_iff.mpr hR))).symm)))

@[simp] theorem repairableGroupedTreeCompare_read {O : Type w}
    (observe : S → O) (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves)
    (heach : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe)
    (x : S) :
    repairableGroupedTreeCompare T observe left right h heach
      ((repairableGroupedTreeStage T observe left heach).2.stage.read x) =
    (repairableGroupedTreeStage T observe right
      (fun R hR => heach R (h.mem_iff.mpr hR))).2.stage.read x :=
  stageCompare_read T _ _ _ x

/-- Every comparison between these actual repair quotients preserves their
named operations. -/
theorem repairableGroupedTreeCompare_step {O : Type w}
    (observe : S → O) (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves)
    (heach : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe)
    (e : E) (z : (repairableGroupedTreeStage T observe left heach).2.stage.Carrier) :
    repairableGroupedTreeCompare T observe left right h heach
      ((repairableGroupedTreeStage T observe left heach).2.stage.system.step e z) =
    (repairableGroupedTreeStage T observe right
      (fun R hR => heach R (h.mem_iff.mpr hR))).2.stage.system.step e
      (repairableGroupedTreeCompare T observe left right h heach z) :=
  stageCompare_step T _ _ _ e z

/-- The comparison preserves the observations carried through every stage. -/
theorem repairableGroupedTreeCompare_observation {O : Type w}
    (observe : S → O) (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves)
    (heach : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe)
    (z : (repairableGroupedTreeStage T observe left heach).2.stage.Carrier) :
    SequentialStage.observation T observe
      (repairableGroupedTreeStage T observe right
        (fun R hR => heach R (h.mem_iff.mpr hR))).2.stage
      (repairableGroupedTreeStage T observe right
        (fun R hR => heach R (h.mem_iff.mpr hR))).2.repairable
      (repairableGroupedTreeCompare T observe left right h heach z) =
    SequentialStage.observation T observe
      (repairableGroupedTreeStage T observe left heach).2.stage
      (repairableGroupedTreeStage T observe left heach).2.repairable z :=
  stageCompare_observation T observe _ _ _ _ _ z

/-- Such a comparison is unique from its source square. -/
theorem repairableGroupedTreeCompare_unique {O : Type w}
    (observe : S → O) (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves)
    (heach : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe)
    (f : (repairableGroupedTreeStage T observe left heach).2.stage.Carrier →
      (repairableGroupedTreeStage T observe right
        (fun R hR => heach R (h.mem_iff.mpr hR))).2.stage.Carrier)
    (hf : ∀ x, f ((repairableGroupedTreeStage T observe left heach).2.stage.read x) =
      (repairableGroupedTreeStage T observe right
        (fun R hR => heach R (h.mem_iff.mpr hR))).2.stage.read x) :
    f = repairableGroupedTreeCompare T observe left right h heach :=
  stageCompare_unique T _ _ _ f hf

/-- Comparison composition for actual repair-carrying grouped quotient
systems equals the direct comparison. -/
theorem repairableGroupedTreeCompare_coherent {O : Type w}
    (observe : S → O) (a b c : RequestTree S)
    (hab : a.leaves.Perm b.leaves) (hbc : b.leaves.Perm c.leaves)
    (heach : ∀ R ∈ a.leaves, generated T R ≤ behavior T observe) :
    (repairableGroupedTreeCompare T observe a b hab heach).trans
      (repairableGroupedTreeCompare T observe b c hbc
        (fun R hR => heach R (hab.mem_iff.mpr hR))) =
    repairableGroupedTreeCompare T observe a c (hab.trans hbc) heach := by
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ :=
    (repairableGroupedTreeStage T observe a heach).2.stage.surjective z
  simp only [Equiv.trans_apply, repairableGroupedTreeCompare_read]

/-- Every tree's concrete sequence contains exactly its leaves. -/
theorem treeStage_perm (tree : RequestTree S) :
    (treeStage T tree).1.Perm tree.leaves := by
  have h := applyRequestTree_perm T tree ⟨[], sequentialBase T⟩
  have h' : (treeStage T tree).1.Perm tree.leaves.reverse := by
    simpa only [treeStage, List.append_nil] using h
  exact h'.trans (List.reverse_perm tree.leaves)

/-- Each bracketed sequence has the same union request as its leaves. -/
theorem treeStage_request (tree : RequestTree S) :
    listRequest (treeStage T tree).1 = listRequest tree.leaves :=
  listRequest_perm (treeStage_perm T tree)

/-- Any two flat leafwise orders of one finite family have a canonical
comparison over the original state type. -/
noncomputable def treeCompare (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves) :
    (treeStage T left).2.Carrier ≃ (treeStage T right).2.Carrier :=
  stageCompare T (treeStage T left).2 (treeStage T right).2
    (congrArg (generated T) ((treeStage_request T left).trans
      ((listRequest_perm h).trans (treeStage_request T right).symm)))

@[simp] theorem treeCompare_read (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves) (x : S) :
    treeCompare T left right h ((treeStage T left).2.read x) =
      (treeStage T right).2.read x := by
  exact stageCompare_read T (treeStage T left).2 (treeStage T right).2 _ x

/-- Every comparison between tree-shaped sequences preserves operations. -/
theorem treeCompare_step (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves) (e : E)
    (z : (treeStage T left).2.Carrier) :
    treeCompare T left right h ((treeStage T left).2.system.step e z) =
      (treeStage T right).2.system.step e (treeCompare T left right h z) :=
  stageCompare_step T (treeStage T left).2 (treeStage T right).2 _ e z

/-- Flat leafwise comparisons compose to the direct comparison. -/
theorem treeCompare_coherent (a b c : RequestTree S)
    (hab : a.leaves.Perm b.leaves) (hbc : b.leaves.Perm c.leaves) :
    (treeCompare T a b hab).trans (treeCompare T b c hbc) =
      treeCompare T a c (hab.trans hbc) := by
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ := (treeStage T a).2.surjective z
  simp only [Equiv.trans_apply, treeCompare_read]

/-- Under repairability of the finite family, tree comparisons also preserve
the observations descended at their final stages. -/
theorem treeCompare_observation {O : Type w} (observe : S → O)
    (left right : RequestTree S) (h : left.leaves.Perm right.leaves)
    (hl : generated T (listRequest (treeStage T left).1) ≤ behavior T observe)
    (hr : generated T (listRequest (treeStage T right).1) ≤ behavior T observe)
    (z : (treeStage T left).2.Carrier) :
    SequentialStage.observation T observe (treeStage T right).2 hr
      (treeCompare T left right h z) =
    SequentialStage.observation T observe (treeStage T left).2 hl z :=
  stageCompare_observation T observe (treeStage T left).2
    (treeStage T right).2 _ hl hr z

/-- A tree-shaped sequence is repairable exactly when every leaf request
is repairable. This includes the empty tree. -/
theorem treeStage_repairable_iff {O : Type w} (observe : S → O)
    (tree : RequestTree S) :
    generated T (listRequest (treeStage T tree).1) ≤ behavior T observe ↔
      ∀ R ∈ tree.leaves, generated T R ≤ behavior T observe := by
  rw [treeStage_request]
  exact listRequest_repairable_iff T observe tree.leaves

/-- A source-commuting map between two tree-shaped sequences is their
canonical comparison. -/
theorem treeCompare_unique (left right : RequestTree S)
    (h : left.leaves.Perm right.leaves)
    (f : (treeStage T left).2.Carrier → (treeStage T right).2.Carrier)
    (hf : ∀ x, f ((treeStage T left).2.read x) = (treeStage T right).2.read x) :
    f = treeCompare T left right h :=
  stageCompare_unique T (treeStage T left).2 (treeStage T right).2 _ f hf

/-- Repairability of each raw request suffices for observation preservation
under every order and parenthesization comparison. -/
theorem treeCompare_observation_of_each {O : Type w} (observe : S → O)
    (left right : RequestTree S) (h : left.leaves.Perm right.leaves)
    (heach : ∀ R ∈ left.leaves, generated T R ≤ behavior T observe)
    (z : (treeStage T left).2.Carrier) :
    SequentialStage.observation T observe (treeStage T right).2
      ((treeStage_repairable_iff T observe right).mpr
        (fun R hR => heach R (h.mem_iff.mpr hR)))
      (treeCompare T left right h z) =
    SequentialStage.observation T observe (treeStage T left).2
      ((treeStage_repairable_iff T observe left).mpr heach) z := by
  exact treeCompare_observation T observe left right h _ _ z

/-- Every finite list has a tree presentation, including the empty list. -/
def requestTreeOfList : List (S → S → Prop) → RequestTree S
  | [] => .empty
  | R :: rest => .branch (.leaf R) (requestTreeOfList rest)

@[simp] theorem requestTreeOfList_leaves
    (requests : List (S → S → Prop)) :
    (requestTreeOfList requests).leaves = requests := by
  induction requests with
  | nil => rfl
  | cons R rest ih => simp [requestTreeOfList, RequestTree.leaves, ih]

/-- A finite indexed request family has a concrete tree presentation. -/
noncomputable def indexedFamilyTree {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) : RequestTree S :=
  requestTreeOfList ((Finset.univ.toList).map Rs)

/-- The tree presentation has exactly the union relation of the finite
indexed family, including empty index types. -/
theorem indexedFamilyTree_request_iff {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) (x y : S) :
    listRequest (indexedFamilyTree Rs).leaves x y ↔ requestUnion Rs x y := by
  simp only [indexedFamilyTree, requestTreeOfList_leaves, listRequest, requestUnion]
  constructor
  · rintro ⟨R, hR, hxy⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hR
    exact ⟨i, hxy⟩
  · rintro ⟨i, hxy⟩
    exact ⟨Rs i, List.mem_map.mpr ⟨i, by simp, rfl⟩, hxy⟩

/-- The concrete tree of a finite indexed family has the kernel of the
direct quotient by the union request. -/
theorem indexedFamilyStage_kernel {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) :
    Setoid.ker (treeStage T (indexedFamilyTree Rs)).2.read =
      (generated T (requestUnion Rs)).setoid := by
  have hreq : listRequest (treeStage T (indexedFamilyTree Rs)).1 =
      requestUnion Rs := by
    rw [treeStage_request]
    funext x y
    exact propext (indexedFamilyTree_request_iff Rs x y)
  simpa only [hreq] using (treeStage T (indexedFamilyTree Rs)).2.kernel_eq

/-- Direct comparison from the actual finite sequential quotient to the
quotient by the indexed family union. -/
noncomputable def indexedFamilyEquiv {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) :
    (treeStage T (indexedFamilyTree Rs)).2.Carrier ≃
      Quotient (generated T (requestUnion Rs)).setoid :=
  (Setoid.quotientKerEquivOfSurjective
    (treeStage T (indexedFamilyTree Rs)).2.read
    (treeStage T (indexedFamilyTree Rs)).2.surjective).symm.trans
    (Quotient.congr (Equiv.refl _) (fun x y => by
      simp only [indexedFamilyStage_kernel, Equiv.refl_apply]))

@[simp] theorem indexedFamilyEquiv_read {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) (x : S) :
    indexedFamilyEquiv T Rs ((treeStage T (indexedFamilyTree Rs)).2.read x) =
      Quotient.mk (generated T (requestUnion Rs)).setoid x := by
  simp [indexedFamilyEquiv, Setoid.quotientKerEquivOfSurjective]
  apply Quotient.sound
  have h := Function.rightInverse_surjInv
    (treeStage T (indexedFamilyTree Rs)).2.surjective
    ((treeStage T (indexedFamilyTree Rs)).2.read x)
  exact (indexedFamilyStage_kernel T Rs).symm ▸ h

/-- The direct indexed-family comparison preserves named operations. -/
theorem indexedFamilyEquiv_step {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) (e : E)
    (z : (treeStage T (indexedFamilyTree Rs)).2.Carrier) :
    indexedFamilyEquiv T Rs
      ((treeStage T (indexedFamilyTree Rs)).2.system.step e z) =
    (quotientSystem T (generated T (requestUnion Rs))).step e
      (indexedFamilyEquiv T Rs z) := by
  obtain ⟨x, rfl⟩ := (treeStage T (indexedFamilyTree Rs)).2.surjective z
  rw [← (treeStage T (indexedFamilyTree Rs)).2.step_comm,
    indexedFamilyEquiv_read, indexedFamilyEquiv_read, quotientSystem_step_mk]

/-- Repairability of the indexed union is precisely the premise needed to
descend observation through its concrete sequential construction. -/
theorem indexedFamilyStage_repairable {I : Type w} [Fintype I]
    {O : Type*} (observe : S → O) (Rs : I → S → S → Prop)
    (h : generated T (requestUnion Rs) ≤ behavior T observe) :
    generated T (listRequest (treeStage T (indexedFamilyTree Rs)).1) ≤
      behavior T observe := by
  rw [treeStage_request]
  have hreq : listRequest (indexedFamilyTree Rs).leaves = requestUnion Rs := by
    funext x y
    exact propext (indexedFamilyTree_request_iff Rs x y)
  rwa [hreq]

/-- The direct indexed-family comparison preserves the observation descended
from the same raw input. -/
theorem indexedFamilyEquiv_observation {I : Type w} [Fintype I]
    {O : Type*} (observe : S → O) (Rs : I → S → S → Prop)
    (h : generated T (requestUnion Rs) ≤ behavior T observe)
    (z : (treeStage T (indexedFamilyTree Rs)).2.Carrier) :
    quotientObservation T observe (generated T (requestUnion Rs)) h
      (indexedFamilyEquiv T Rs z) =
    SequentialStage.observation T observe
      (treeStage T (indexedFamilyTree Rs)).2
      (indexedFamilyStage_repairable T observe Rs h) z := by
  obtain ⟨x, rfl⟩ := (treeStage T (indexedFamilyTree Rs)).2.surjective z
  simp only [indexedFamilyEquiv_read, quotientObservation_mk,
    SequentialStage.observation_read]

/-- The source square determines the direct indexed-family comparison. -/
theorem indexedFamilyEquiv_unique {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop)
    (f : (treeStage T (indexedFamilyTree Rs)).2.Carrier →
      Quotient (generated T (requestUnion Rs)).setoid)
    (hf : ∀ x, f ((treeStage T (indexedFamilyTree Rs)).2.read x) =
      Quotient.mk (generated T (requestUnion Rs)).setoid x) :
    f = indexedFamilyEquiv T Rs := by
  funext z
  obtain ⟨x, rfl⟩ := (treeStage T (indexedFamilyTree Rs)).2.surjective z
  exact (hf x).trans (indexedFamilyEquiv_read T Rs x).symm

/-- The genuinely grouped presentation of any finite indexed family has
the kernel of its direct union quotient. -/
theorem groupedIndexedFamilyStage_kernel {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) :
    Setoid.ker (groupedTreeStage T (indexedFamilyTree Rs)).2.read =
      (generated T (requestUnion Rs)).setoid := by
  have hreq : listRequest (groupedTreeStage T (indexedFamilyTree Rs)).1 =
      requestUnion Rs := by
    rw [groupedTreeStage_request]
    funext x y
    exact propext (indexedFamilyTree_request_iff Rs x y)
  simpa only [hreq] using
    (groupedTreeStage T (indexedFamilyTree Rs)).2.kernel_eq

/-- Direct source-commuting equivalence for the grouped indexed-family
presentation, including the empty finite index type. -/
noncomputable def groupedIndexedFamilyEquiv {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) :
    (groupedTreeStage T (indexedFamilyTree Rs)).2.Carrier ≃
      Quotient (generated T (requestUnion Rs)).setoid :=
  (Setoid.quotientKerEquivOfSurjective
    (groupedTreeStage T (indexedFamilyTree Rs)).2.read
    (groupedTreeStage T (indexedFamilyTree Rs)).2.surjective).symm.trans
    (Quotient.congr (Equiv.refl _) (fun x y => by
      simp only [groupedIndexedFamilyStage_kernel, Equiv.refl_apply]))

@[simp] theorem groupedIndexedFamilyEquiv_read {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) (x : S) :
    groupedIndexedFamilyEquiv T Rs
      ((groupedTreeStage T (indexedFamilyTree Rs)).2.read x) =
    Quotient.mk (generated T (requestUnion Rs)).setoid x := by
  simp [groupedIndexedFamilyEquiv, Setoid.quotientKerEquivOfSurjective]
  apply Quotient.sound
  have h := Function.rightInverse_surjInv
    (groupedTreeStage T (indexedFamilyTree Rs)).2.surjective
    ((groupedTreeStage T (indexedFamilyTree Rs)).2.read x)
  exact (groupedIndexedFamilyStage_kernel T Rs).symm ▸ h

/-- The grouped indexed-family direct equivalence preserves operations. -/
theorem groupedIndexedFamilyEquiv_step {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop) (e : E)
    (z : (groupedTreeStage T (indexedFamilyTree Rs)).2.Carrier) :
    groupedIndexedFamilyEquiv T Rs
      ((groupedTreeStage T (indexedFamilyTree Rs)).2.system.step e z) =
    (quotientSystem T (generated T (requestUnion Rs))).step e
      (groupedIndexedFamilyEquiv T Rs z) := by
  obtain ⟨x, rfl⟩ := (groupedTreeStage T (indexedFamilyTree Rs)).2.surjective z
  rw [← (groupedTreeStage T (indexedFamilyTree Rs)).2.step_comm,
    groupedIndexedFamilyEquiv_read, groupedIndexedFamilyEquiv_read,
    quotientSystem_step_mk]

/-- Repairability of the indexed union descends observation to its grouped
sequential quotient. -/
theorem groupedIndexedFamilyStage_repairable {I : Type w} [Fintype I]
    {O : Type*} (observe : S → O) (Rs : I → S → S → Prop)
    (h : generated T (requestUnion Rs) ≤ behavior T observe) :
    generated T (listRequest (groupedTreeStage T (indexedFamilyTree Rs)).1) ≤
      behavior T observe := by
  rw [groupedTreeStage_request]
  have hreq : listRequest (indexedFamilyTree Rs).leaves = requestUnion Rs := by
    funext x y
    exact propext (indexedFamilyTree_request_iff Rs x y)
  rwa [hreq]

/-- The grouped indexed-family comparison preserves the descended
observation under the fixed repairability condition. -/
theorem groupedIndexedFamilyEquiv_observation {I : Type w} [Fintype I]
    {O : Type*} (observe : S → O) (Rs : I → S → S → Prop)
    (h : generated T (requestUnion Rs) ≤ behavior T observe)
    (z : (groupedTreeStage T (indexedFamilyTree Rs)).2.Carrier) :
    quotientObservation T observe (generated T (requestUnion Rs)) h
      (groupedIndexedFamilyEquiv T Rs z) =
    SequentialStage.observation T observe
      (groupedTreeStage T (indexedFamilyTree Rs)).2
      (groupedIndexedFamilyStage_repairable T observe Rs h) z := by
  obtain ⟨x, rfl⟩ := (groupedTreeStage T (indexedFamilyTree Rs)).2.surjective z
  simp only [groupedIndexedFamilyEquiv_read, quotientObservation_mk,
    SequentialStage.observation_read]

/-- The source square determines the direct grouped indexed-family map. -/
theorem groupedIndexedFamilyEquiv_unique {I : Type w} [Fintype I]
    (Rs : I → S → S → Prop)
    (f : (groupedTreeStage T (indexedFamilyTree Rs)).2.Carrier →
      Quotient (generated T (requestUnion Rs)).setoid)
    (hf : ∀ x, f ((groupedTreeStage T (indexedFamilyTree Rs)).2.read x) =
      Quotient.mk (generated T (requestUnion Rs)).setoid x) :
    f = groupedIndexedFamilyEquiv T Rs := by
  funext z
  obtain ⟨x, rfl⟩ := (groupedTreeStage T (indexedFamilyTree Rs)).2.surjective z
  exact (hf x).trans (groupedIndexedFamilyEquiv_read T Rs x).symm

#assert_standard_axioms_only AAT.AG.OperationRepair
end AAT.AG.OperationRepair
