import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRingCarrierGraphs
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for total and inverse graph rows

Every law instance in this module is a formula over explicit Boolean cells.
Wrong-carrier guards use only equality of the supplied carrier references, and
uniqueness uses only equality of the supplied output values.  No completed
graph law or arbitrary proposition is accepted by the syntax.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula

noncomputable section

universe u v w x y z

open IndependentFiniteLawFormula

/-! ## Total function rows -/

namespace CarrierRows

variable {Q : Type w}

def typedSource (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (_α : Type u) (S : Type u) (T : Type v) (x : S) (y : T) :
    BoolFormula.{w, u + 1} Q :=
  .cell (embed (.edge S T x y)) false

def typedTarget (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (_β : Type v) (S : Type u) (T : Type v) (x : S) (y : T) :
    BoolFormula.{w, v + 1} Q :=
  .cell (embed (.edge S T x y)) false

def witness (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) (x : α) (y : β) : BoolFormula.{w, v} Q :=
  .cell (embed (.edge α β x y)) true

def other (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) (x : α) (challenger : β) :
    BoolFormula.{w, v} Q :=
  .cell (embed (.edge α β x challenger)) false

def Instances (table : Q → Bool)
    (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) : Prop :=
  (∀ S T x y, (S ≠ α → (typedSource embed α S T x y).evaluate table) ∧
    (T ≠ β → (typedTarget embed β S T x y).evaluate table)) ∧
  (∀ x : α, ∃ y : β, (witness embed α β x y).evaluate table ∧
    ∀ z : β, z ≠ y → (other embed α β x z).evaluate table)

theorem lawful_iff_instances (table : Q → Bool)
    (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) :
    IndependentCarrierGraph.IsLawful α β (fun q => table (embed q)) ↔
      Instances table embed α β := by
  constructor
  · rintro ⟨htyped, htotal⟩
    constructor
    · intro S T x y
      exact ⟨fun hS => htyped S T x y (Or.inl hS),
        fun hT => htyped S T x y (Or.inr hT)⟩
    · intro x
      obtain ⟨y, hy, hu⟩ := htotal x
      refine ⟨y, hy, ?_⟩
      intro z hzy
      cases hq : table (embed (.edge α β x z)) with
      | false => exact hq
      | true => exact (hzy (hu z hq)).elim
  · rintro ⟨htyped, htotal⟩
    constructor
    · intro S T x y hwrong
      exact hwrong.elim (htyped S T x y).1 (htyped S T x y).2
    · intro x
      obtain ⟨y, hy, hu⟩ := htotal x
      refine ⟨y, hy, ?_⟩
      intro z hz
      by_contra hzy
      have hf := hu z hzy
      exact Bool.noConfusion (hf.symm.trans hz)

end CarrierRows

/-! ## Inverse rows -/

namespace InverseRows

variable {Q : Type w}

def forwardEmbed (embed : IndependentInverseGraph.Query.{u, v} → Q) :
    IndependentCarrierGraph.Query.{u, v} → Q := fun q => embed (.forward q)

def backwardEmbed (embed : IndependentInverseGraph.Query.{u, v} → Q) :
    IndependentCarrierGraph.Query.{v, u} → Q := fun q => embed (.backward q)

def inverse (embed : IndependentInverseGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) (x : α) (y : β) : BoolFormula.{w, 0} Q :=
  .iff (.cell (embed (.forward (.edge α β x y))) true)
    (.cell (embed (.backward (.edge β α y x))) true)

def Instances (table : Q → Bool)
    (embed : IndependentInverseGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) : Prop :=
  CarrierRows.Instances table (forwardEmbed embed) α β ∧
  CarrierRows.Instances table (backwardEmbed embed) β α ∧
  ∀ x y, (inverse embed α β x y).evaluate table

theorem lawful_iff_instances (table : Q → Bool)
    (embed : IndependentInverseGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) :
    IndependentInverseGraph.IsLawful α β (fun q => table (embed q)) ↔
      Instances table embed α β := by
  constructor
  · intro hp
    exact ⟨(CarrierRows.lawful_iff_instances table (forwardEmbed embed) α β).mp hp.forward,
      (CarrierRows.lawful_iff_instances table (backwardEmbed embed) β α).mp hp.backward,
      hp.inverse⟩
  · rintro ⟨hf, hb, hi⟩
    exact {
      forward := (CarrierRows.lawful_iff_instances table (forwardEmbed embed) α β).mpr hf
      backward := (CarrierRows.lawful_iff_instances table (backwardEmbed embed) β α).mpr hb
      inverse := hi }

end InverseRows

/-! ## Rows indexed by an active Boolean graph -/

namespace IndexedRows

variable {Q : Type w}
  {S : I → Type u} {T : J → Type v}

def inactive (index : I → J → Q) (value : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (a : S i) (b : T j) : BoolFormula.{w, 0} Q :=
  .implies (.cell (index i j) false) (.cell (value i j a b) false)

def witness (value : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (a : S i) (b : T j) : BoolFormula.{w, v} Q :=
  .cell (value i j a b) true

def other (value : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (a : S i) (challenger : T j) :
    BoolFormula.{w, v} Q :=
  .cell (value i j a challenger) false

def Instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ i j, S i → T j → Q) : Prop :=
  (∀ i j a b, (inactive index value i j a b).evaluate table) ∧
  (∀ i j, table (index i j) = true → ∀ a, ∃ b,
    (witness value i j a b).evaluate table ∧
    ∀ c, c ≠ b → (other value i j a c).evaluate table)

theorem lawful_iff_instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ i j, S i → T j → Q) :
    IndependentFixedIndexedPointGraph.IsLawful S T
      (fun i j => table (index i j)) (fun i j a b => table (value i j a b)) ↔
      Instances table index value := by
  constructor
  · intro hp
    constructor
    · intro i j a b hij
      exact hp.inactive i j hij a b
    · intro i j hij a
      obtain ⟨b, hb, hu⟩ := hp.active i j hij a
      refine ⟨b, hb, ?_⟩
      intro c hcb
      cases hq : table (value i j a c) with
      | false => exact hq
      | true => exact (hcb (hu c hq)).elim
  · rintro ⟨hinactive, hactive⟩
    constructor
    · intro i j hij a b
      exact hinactive i j a b hij
    · intro i j hij a
      obtain ⟨b, hb, hu⟩ := hactive i j hij a
      refine ⟨b, hb, ?_⟩
      intro c hc
      by_contra hcb
      have hf := hu c hcb
      exact Bool.noConfusion (hf.symm.trans hc)

def inverse (forward backward : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (a : S i) (b : T j) : BoolFormula.{w, 0} Q :=
  .iff (.cell (forward i j a b) true) (.cell (backward i j a b) true)

def InverseInstances (table : Q → Bool) (index : I → J → Q)
    (forward backward : ∀ i j, S i → T j → Q) : Prop :=
  Instances table index forward ∧
  (∀ i j, table (index i j) = true → ∀ b, ∃ a,
    (witness (S := fun j => T j) (T := fun i => S i)
      (fun j i b a => backward i j a b) j i b a).evaluate table ∧
    ∀ c, c ≠ a → (other (S := fun j => T j) (T := fun i => S i)
      (fun j i b a => backward i j a b) j i b c).evaluate table) ∧
  ∀ i j a b, (inverse forward backward i j a b).evaluate table

theorem inverseLaws_iff_instances (table : Q → Bool) (index : I → J → Q)
    (forward backward : ∀ i j, S i → T j → Q) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (fun i j => table (index i j))
      (fun i j a b => table (forward i j a b))
      (fun i j a b => table (backward i j a b)) ↔
      InverseInstances table index forward backward := by
  constructor
  · intro hp
    refine ⟨(lawful_iff_instances table index forward).mp hp.forward, ?_, ?_⟩
    · intro i j hij b
      obtain ⟨a, ha, hu⟩ := hp.backward i j hij b
      refine ⟨a, ha, ?_⟩
      intro c hca
      cases hq : table (backward i j c b) with
      | false => exact hq
      | true => exact (hca (hu c hq)).elim
    · intro i j a b
      exact Bool.eq_iff_iff.mp (hp.inverse i j a b)
  · rintro ⟨hf, hb, hi⟩
    exact {
      forward := (lawful_iff_instances table index forward).mpr hf
      backward := by
        intro i j hij b
        obtain ⟨a, ha, hu⟩ := hb i j hij b
        refine ⟨a, ha, ?_⟩
        intro c hc
        by_contra hca
        have hf := hu c hca
        exact Bool.noConfusion (hf.symm.trans hc)
      inverse := fun i j a b => Bool.eq_iff_iff.mpr (hi i j a b) }

end IndexedRows

/-! ## Candidate indexed directed rows -/

namespace DependentCarrierRows

variable {Q : Type w} {I : Type x} {J : Type y}
  {S : I → Type u} {T : J → Type v}

def inactive (index : I → J → Q)
    (value : ∀ (_i : I) (_j : J), IndependentCarrierGraph.Query.{u, v} → Q)
    (i : I) (j : J) (q : IndependentCarrierGraph.Query.{u, v}) :
    BoolFormula.{w, 0} Q :=
  .implies (.cell (index i j) false) (.cell (value i j q) false)

def Instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ (_i : I) (_j : J), IndependentCarrierGraph.Query.{u, v} → Q)
    (S : I → Type u) (T : J → Type v) : Prop :=
  (∀ i j q, (inactive index value i j q).evaluate table) ∧
  ∀ i j, table (index i j) = true →
    CarrierRows.Instances table (value i j) (S i) (T j)

theorem lawful_iff_instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ (_i : I) (_j : J), IndependentCarrierGraph.Query.{u, v} → Q)
    (S : I → Type u) (T : J → Type v) :
    IndependentIndexedCarrierGraph.IsLawful
      (fun i j => table (index i j)) S T
      (fun q => match q with | .edge i j r => table (value i j r)) ↔
      Instances table index value S T := by
  constructor
  · intro hp
    constructor
    · intro i j q hij
      exact hp.inactive i j hij q
    · intro i j hij
      exact (CarrierRows.lawful_iff_instances table (value i j) (S i) (T j)).mp
        (hp.active i j hij)
  · rintro ⟨hinactive, hactive⟩
    exact {
      inactive := fun i j hij q => hinactive i j q hij
      active := fun i j hij =>
        (CarrierRows.lawful_iff_instances table (value i j) (S i) (T j)).mpr
          (hactive i j hij) }

end DependentCarrierRows

/-! ## Candidate indexed inverse rows -/

namespace DependentInverseRows

variable {Q : Type w} {I : Type x} {J : Type y}
  {S : I → Type u} {T : J → Type v}

def inactive (index : I → J → Q)
    (value : ∀ (_i : I) (_j : J), IndependentInverseGraph.Query.{u, v} → Q)
    (i : I) (j : J) (q : IndependentInverseGraph.Query.{u, v}) :
    BoolFormula.{w, 0} Q :=
  .implies (.cell (index i j) false) (.cell (value i j q) false)

def Instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ (_i : I) (_j : J), IndependentInverseGraph.Query.{u, v} → Q)
    (S : I → Type u) (T : J → Type v) : Prop :=
  (∀ i j q, (inactive index value i j q).evaluate table) ∧
  ∀ i j, table (index i j) = true →
    InverseRows.Instances table (value i j) (S i) (T j)

theorem lawful_iff_instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ (_i : I) (_j : J), IndependentInverseGraph.Query.{u, v} → Q)
    (S : I → Type u) (T : J → Type v) :
    IndependentIndexedInverseGraph.IsLawful
      (fun i j => table (index i j)) S T
      (fun q => match q with | .edge i j r => table (value i j r)) ↔
      Instances table index value S T := by
  constructor
  · intro hp
    constructor
    · intro i j q hij
      exact hp.inactive i j hij q
    · intro i j hij
      exact (InverseRows.lawful_iff_instances table (value i j) (S i) (T j)).mp
        (hp.active i j hij)
  · rintro ⟨hinactive, hactive⟩
    exact {
      inactive := fun i j hij q => hinactive i j q hij
      active := fun i j hij =>
        (InverseRows.lawful_iff_instances table (value i j) (S i) (T j)).mpr
          (hactive i j hij) }

end DependentInverseRows

/-! ## Candidate outer carriers with indexed inverse rows -/

namespace CandidateDependentInverseRows

variable {Q : Type w}

def outerSourceInactive (value : ∀ (I : Type x) (J : Type y) (_i : I) (_j : J),
      IndependentInverseGraph.Query.{u, v} → Q)
    (_selectedI : Type x) (K : Type x) (L : Type y) (k : K) (l : L)
    (q : IndependentInverseGraph.Query.{u, v}) : BoolFormula.{w, x + 1} Q :=
  .cell (value K L k l q) false

def outerTargetInactive (value : ∀ (I : Type x) (J : Type y) (_i : I) (_j : J),
      IndependentInverseGraph.Query.{u, v} → Q)
    (_selectedJ : Type y) (K : Type x) (L : Type y) (k : K) (l : L)
    (q : IndependentInverseGraph.Query.{u, v}) : BoolFormula.{w, y + 1} Q :=
  .cell (value K L k l q) false

def Instances (table : Q → Bool) (I : Type x) (J : Type y)
    (index : I → J → Q)
    (value : ∀ (K : Type x) (L : Type y) (_k : K) (_l : L),
      IndependentInverseGraph.Query.{u, v} → Q)
    (S : I → Type u) (T : J → Type v) : Prop :=
  (∀ K L k l q, K ≠ I → (outerSourceInactive value I K L k l q).evaluate table) ∧
  (∀ K L k l q, L ≠ J → (outerTargetInactive value J K L k l q).evaluate table) ∧
  DependentInverseRows.Instances (I := I) (J := J) table index (value I J) S T

theorem lawful_iff_instances (table : Q → Bool) (I : Type x) (J : Type y)
    (index : I → J → Q)
    (value : ∀ (K : Type x) (L : Type y) (_k : K) (_l : L),
      IndependentInverseGraph.Query.{u, v} → Q)
    (S : I → Type u) (T : J → Type v) :
    IndependentCandidateIndexedInverseGraph.IsLawful I J
      (fun i j => table (index i j)) S T
      (fun q => match q with | .edge K L k l r => table (value K L k l r)) ↔
      Instances table I J index value S T := by
  constructor
  · intro hp
    refine ⟨?_, ?_, ?_⟩
    · intro K L k l q hwrong
      exact hp.inactive K L k l q (Or.inl hwrong)
    · intro K L k l q hwrong
      exact hp.inactive K L k l q (Or.inr hwrong)
    · exact (DependentInverseRows.lawful_iff_instances (I := I) (J := J)
        table index (value I J) S T).mp
        hp.selected
  · rintro ⟨hsource, htarget, hselected⟩
    exact {
      inactive := fun K L k l q hwrong => hwrong.elim
        (hsource K L k l q) (htarget K L k l q)
      selected := (DependentInverseRows.lawful_iff_instances (I := I) (J := J)
        table index (value I J) S T).mpr
        hselected }

end CandidateDependentInverseRows

/-! ## Ring point preservation -/

namespace RingRows

variable {Q : Type w}

def zero (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (s : IndependentRingPrimitive.Table S) (t : IndependentRingPrimitive.Table T) :
    BoolFormula.{w, 0} Q :=
  .cell (embed (.edge S T (s .zero) (t .zero))) true

def one (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (s : IndependentRingPrimitive.Table S) (t : IndependentRingPrimitive.Table T) :
    BoolFormula.{w, 0} Q :=
  .cell (embed (.edge S T (s .one) (t .one))) true

def add (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (s : IndependentRingPrimitive.Table S) (t : IndependentRingPrimitive.Table T)
    (a b : S) (c d : T) : BoolFormula.{w, 0} Q :=
  .implies (.and (.cell (embed (.edge S T a c)) true)
      (.cell (embed (.edge S T b d)) true))
    (.cell (embed (.edge S T (s (.add a b)) (t (.add c d)))) true)

def mul (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (s : IndependentRingPrimitive.Table S) (t : IndependentRingPrimitive.Table T)
    (a b : S) (c d : T) : BoolFormula.{w, 0} Q :=
  .implies (.and (.cell (embed (.edge S T a c)) true)
      (.cell (embed (.edge S T b d)) true))
    (.cell (embed (.edge S T (s (.mul a b)) (t (.mul c d)))) true)

def Instances (table : Q → Bool) (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (s : IndependentRingPrimitive.Table S) (t : IndependentRingPrimitive.Table T) : Prop :=
  (zero embed s t).evaluate table ∧ (one embed s t).evaluate table ∧
  (∀ a b c d, (add embed s t a b c d).evaluate table) ∧
  ∀ a b c d, (mul embed s t a b c d).evaluate table

theorem preserves_iff_instances (table : Q → Bool)
    (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (s : IndependentRingPrimitive.Table S) (t : IndependentRingPrimitive.Table T) :
    IndependentRingCarrierGraph.Preserves s t (fun q => table (embed q)) ↔
      Instances table embed s t := by
  constructor
  · rintro ⟨hz, ho, ha, hm⟩
    refine ⟨hz, ho, ?_, ?_⟩
    · intro a b c d hp
      exact ha a b c d hp.1 hp.2
    · intro a b c d hp
      exact hm a b c d hp.1 hp.2
  · rintro ⟨hz, ho, ha, hm⟩
    refine ⟨hz, ho, ?_, ?_⟩
    · intro a b c d hac hbd
      exact ha a b c d ⟨hac, hbd⟩
    · intro a b c d hac hbd
      exact hm a b c d ⟨hac, hbd⟩

end RingRows

end

end AAT.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula
