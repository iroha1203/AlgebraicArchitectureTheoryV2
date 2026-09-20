import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoverageLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoefficientLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOverlapLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawPointLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRawLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealization
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealization
import Formal.Util.AssertStandardAxioms

/-!
# Finite support for complete geometry Hom law instances

The complete Hom laws are quantified over carriers, points, and witnesses.
The approved local design does not require one finite support for an entire
quantified law.  It requires a finite support after its arguments and any
existence or uniqueness witness have been fixed.  This module makes that
distinction explicit.

`Formula.fixed` is only a metatheoretic support-accounting device for endpoint
facts that do not inspect the Hom table.  It is not a constructor of the local
declaration and cannot store a completed Hom, map, or certificate.  Every
table-dependent atom remains an actual common Hom query in `Formula.cell`.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.LawFinite

noncomputable section

universe u v w x y

open Site

/-! ## A finite Boolean formula over arbitrary query cells -/

/-- Finite propositional expressions whose only table observations are named
Boolean cells.  Fixed endpoint facts carry no Hom-table support. -/
inductive Formula (Q : Type w) where
  | cell (q : Q) (value : Bool)
  | fixed (proposition : Prop)
  | and (left right : Formula Q)
  | or (left right : Formula Q)
  | implies (premise conclusion : Formula Q)
  | iff (left right : Formula Q)

/-- Evaluate a finite formula against an arbitrary Boolean table. -/
def Formula.evaluate {Q : Type w} (table : Q → Bool) : Formula Q → Prop
  | .cell q value => table q = value
  | .fixed proposition => proposition
  | .and left right => left.evaluate table ∧ right.evaluate table
  | .or left right => left.evaluate table ∨ right.evaluate table
  | .implies premise conclusion => premise.evaluate table → conclusion.evaluate table
  | .iff left right => left.evaluate table ↔ right.evaluate table

/-- Constructor-wise support contains exactly the table cells read by a
finite formula. -/
def Formula.support {Q : Type w} : Formula Q → Finset Q
  | .cell q _ => {q}
  | .fixed _ => ∅
  | .and left right
  | .or left right
  | .implies left right
  | .iff left right => by
      classical
      exact left.support ∪ right.support

/-- Agreement on the generated finite support preserves a formula instance
for arbitrary, possibly unlawful, comparison tables. -/
theorem Formula.evaluate_iff_of_support {Q : Type w}
    (first second : Q → Bool) (formula : Formula Q)
    (agree : ∀ q ∈ formula.support, first q = second q) :
    formula.evaluate first ↔ formula.evaluate second := by
  classical
  induction formula with
  | cell q value =>
      change first q = value ↔ second q = value
      rw [agree q (by simp [Formula.support])]
  | fixed proposition => rfl
  | and left right ihLeft ihRight =>
      exact and_congr
        (ihLeft (fun q hq => agree q (by simp [Formula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [Formula.support, hq])))
  | or left right ihLeft ihRight =>
      exact or_congr
        (ihLeft (fun q hq => agree q (by simp [Formula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [Formula.support, hq])))
  | implies premise conclusion ihPremise ihConclusion =>
      exact imp_congr
        (ihPremise (fun q hq => agree q (by simp [Formula.support, hq])))
        (ihConclusion (fun q hq => agree q (by simp [Formula.support, hq])))
  | iff left right ihLeft ihRight =>
      exact iff_congr
        (ihLeft (fun q hq => agree q (by simp [Formula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [Formula.support, hq])))

/-- Every formula support is finite without a finite carrier assumption. -/
theorem Formula.support_finite {Q : Type w} (formula : Formula Q) :
    Finite formula.support := inferInstance

/-! ## Total-function and inverse-row instances -/

/-- One fixed inactive-cell requirement. -/
def inactiveCell {Q : Type w} (guard cell : Q) : Formula Q :=
  .implies (.cell guard false) (.cell cell false)

/-- One supplied totality witness is checked at one cell. -/
def witnessCell {Q : Type w} (cell : Q) : Formula Q := .cell cell true

/-- One fixed uniqueness challenger uses the witness cell and challenger cell. -/
def uniqueCell {Q : Type w} (witness challenger : Q) (same : Prop) : Formula Q :=
  .implies (.and (.cell witness true) (.cell challenger true)) (.fixed same)

/-- One fixed inverse-edge instance uses exactly its two directed cells. -/
def inverseCells {Q : Type w} (forward backward : Q) : Formula Q :=
  .iff (.cell forward true) (.cell backward true)

/-! ## Total-functional and inverse rows as finite formula families -/

namespace CarrierRows

variable {Q : Type w}

/-- One wrong-carrier normalization instance. -/
def typed (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) (S : Type u) (T : Type v) (x : S) (y : T) : Formula Q :=
  .implies (.fixed (S ≠ α ∨ T ≠ β)) (.cell (embed (.edge S T x y)) false)

/-- One selected output witness for one active input row. -/
def witness (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) (x : α) (y : β) : Formula Q :=
  witnessCell (embed (.edge α β x y))

/-- One fixed competitor against a selected output witness. -/
def unique (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) (x : α) (witnessValue challenger : β) : Formula Q :=
  uniqueCell (embed (.edge α β x witnessValue))
    (embed (.edge α β x challenger)) (challenger = witnessValue)

/-- A lawful directed row is a quantified family of finite wrong-carrier,
witness, and fixed-challenger formulas.  No uniform support over all rows is
claimed. -/
def Instances (table : Q → Bool) (embed : IndependentCarrierGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) : Prop :=
  (∀ S T x y, (typed embed α β S T x y).evaluate table) ∧
  (∀ x : α, ∃ y : β, (witness embed α β x y).evaluate table ∧
    ∀ z : β, (unique embed α β x y z).evaluate table)

/-- The native candidate-carrier row law has exactly the finite instances
listed in `Instances`. -/
theorem lawful_iff_instances (table : Q → Bool)
    (embed : IndependentCarrierGraph.Query.{u, v} → Q) (α : Type u) (β : Type v) :
    IndependentCarrierGraph.IsLawful α β (fun q => table (embed q)) ↔
      Instances table embed α β := by
  constructor
  · rintro ⟨htyped, htotal⟩
    constructor
    · intro S T x y hwrong
      exact htyped S T x y hwrong
    · intro x
      obtain ⟨y, hy, hunique⟩ := htotal x
      refine ⟨y, hy, ?_⟩
      intro z hpair
      exact hunique z hpair.2
  · rintro ⟨htyped, htotal⟩
    constructor
    · intro S T x y hwrong
      exact htyped S T x y hwrong
    · intro x
      obtain ⟨y, hy, hunique⟩ := htotal x
      refine ⟨y, hy, ?_⟩
      intro z hz
      exact hunique z ⟨hy, hz⟩

end CarrierRows

namespace InverseRows

variable {Q : Type w}

/-- Embed the forward directed row of an inverse graph. -/
def forwardEmbed (embed : IndependentInverseGraph.Query.{u, v} → Q) :
    IndependentCarrierGraph.Query.{u, v} → Q := fun q => embed (.forward q)

/-- Embed the backward directed row of an inverse graph. -/
def backwardEmbed (embed : IndependentInverseGraph.Query.{u, v} → Q) :
    IndependentCarrierGraph.Query.{v, u} → Q := fun q => embed (.backward q)

/-- One fixed inverse-edge instance. -/
def inverse (embed : IndependentInverseGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) (x : α) (y : β) : Formula Q :=
  inverseCells (embed (.forward (.edge α β x y)))
    (embed (.backward (.edge β α y x)))

/-- All inverse-row obligations, decomposed into finite directed-row and
two-cell inverse instances. -/
def Instances (table : Q → Bool) (embed : IndependentInverseGraph.Query.{u, v} → Q)
    (α : Type u) (β : Type v) : Prop :=
  CarrierRows.Instances table (forwardEmbed embed) α β ∧
  CarrierRows.Instances table (backwardEmbed embed) β α ∧
  ∀ x y, (inverse embed α β x y).evaluate table

/-- Inverse graph lawfulness is exactly its finite instance family. -/
theorem lawful_iff_instances (table : Q → Bool)
    (embed : IndependentInverseGraph.Query.{u, v} → Q) (α : Type u) (β : Type v) :
    IndependentInverseGraph.IsLawful α β (fun q => table (embed q)) ↔
      Instances table embed α β := by
  constructor
  · intro hp
    exact ⟨(CarrierRows.lawful_iff_instances table (forwardEmbed embed) α β).mp hp.forward,
      (CarrierRows.lawful_iff_instances table (backwardEmbed embed) β α).mp hp.backward,
      hp.inverse⟩
  · rintro ⟨hforward, hbackward, hinverse⟩
    exact {
      forward := (CarrierRows.lawful_iff_instances table (forwardEmbed embed) α β).mpr hforward
      backward := (CarrierRows.lawful_iff_instances table (backwardEmbed embed) β α).mpr hbackward
      inverse := hinverse }

end InverseRows

namespace IndexedRows

variable {Q : Type w} {I : Type x} {J : Type y}
  {S : I → Type u} {T : J → Type v}

/-- One inactive dependent-row cell. -/
def inactive (index : I → J → Q) (value : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (x : S i) (y : T j) : Formula Q :=
  inactiveCell (index i j) (value i j x y)

/-- One selected output witness at an active dependent row. -/
def witness (value : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (x : S i) (y : T j) : Formula Q :=
  witnessCell (value i j x y)

/-- One fixed competitor against a selected dependent-row witness. -/
def unique (value : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (x : S i) (witnessValue challenger : T j) : Formula Q :=
  uniqueCell (value i j x witnessValue) (value i j x challenger)
    (challenger = witnessValue)

/-- Finite formula instances for a family of active directed rows. -/
def Instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ i j, S i → T j → Q) : Prop :=
  (∀ i j x y, (inactive index value i j x y).evaluate table) ∧
  (∀ i j, table (index i j) = true → ∀ x, ∃ y,
    (witness value i j x y).evaluate table ∧
    ∀ z, (unique value i j x y z).evaluate table)

/-- Dependent directed row lawfulness is exactly its finite instance family. -/
theorem lawful_iff_instances (table : Q → Bool) (index : I → J → Q)
    (value : ∀ i j, S i → T j → Q) :
    IndependentFixedIndexedPointGraph.IsLawful S T
      (fun i j => table (index i j)) (fun i j x y => table (value i j x y)) ↔
      Instances table index value := by
  constructor
  · intro hp
    constructor
    · intro i j x y hij
      exact hp.inactive i j hij x y
    · intro i j hij x
      obtain ⟨y, hy, hunique⟩ := hp.active i j hij x
      exact ⟨y, hy, fun z hpair => hunique z hpair.2⟩
  · rintro ⟨hinactive, hactive⟩
    constructor
    · intro i j hij x y
      exact hinactive i j x y hij
    · intro i j hij x
      obtain ⟨y, hy, hunique⟩ := hactive i j hij x
      exact ⟨y, hy, fun z hz => hunique z ⟨hy, hz⟩⟩

/-- One fixed equality between the two ordered inverse fiber cells. -/
def inverse (forward backward : ∀ i j, S i → T j → Q)
    (i : I) (j : J) (x : S i) (y : T j) : Formula Q :=
  .iff (.cell (forward i j x y) true) (.cell (backward i j x y) true)

/-- Finite formula instances for inverse dependent rows. -/
def InverseInstances (table : Q → Bool) (index : I → J → Q)
    (forward backward : ∀ i j, S i → T j → Q) : Prop :=
  Instances table index forward ∧
  (∀ i j, table (index i j) = true → ∀ y, ∃ x,
    (witness (S := fun j => T j) (T := fun i => S i)
      (fun j i y x => backward i j x y) j i y x).evaluate table ∧
    ∀ z, (unique (S := fun j => T j) (T := fun i => S i)
      (fun j i y x => backward i j x y) j i y x z).evaluate table) ∧
  ∀ i j x y, (inverse forward backward i j x y).evaluate table

/-- Inverse dependent-row lawfulness is exactly its finite instance family. -/
theorem inverseLaws_iff_instances (table : Q → Bool) (index : I → J → Q)
    (forward backward : ∀ i j, S i → T j → Q) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (fun i j => table (index i j))
      (fun i j x y => table (forward i j x y))
      (fun i j x y => table (backward i j x y)) ↔
      InverseInstances table index forward backward := by
  constructor
  · intro hp
    refine ⟨(lawful_iff_instances table index forward).mp hp.forward, ?_, ?_⟩
    intro i j hij y
    obtain ⟨x, hx, hunique⟩ := hp.backward i j hij y
    exact ⟨x, hx, fun z hpair => hunique z hpair.2⟩
    · intro i j x y
      exact Bool.eq_iff_iff.mp (hp.inverse i j x y)
  · rintro ⟨hforward, hbackward, hinverse⟩
    exact {
      forward := (lawful_iff_instances table index forward).mpr hforward
      backward := by
        intro i j hij y
        obtain ⟨x, hx, hunique⟩ := hbackward i j hij y
        exact ⟨x, hx, fun z hz => hunique z ⟨hx, hz⟩⟩
      inverse := fun i j x y => Bool.eq_iff_iff.mpr (hinverse i j x y) }

end IndexedRows

/-! ## Coverage: all nine preservation instances -/

namespace Coverage

variable {U : AtomCarrier.{u}} {mode : Mode} {A B : ArchitectureObject U}

def requiredSupport (a b : U.Atom) (source target : Prop) :
    Formula (Query.{u, v} U mode) :=
  .implies (.cell (.atom .forward a b) true)
    (.implies (.fixed source) (.fixed target))

def requiredEquation (I J : Type u) (i : I) (j : J) (a b : U.Atom)
    (source target : Prop) : Formula (Query.{u, v} U mode) :=
  .implies (.cell (.atObjects A B (.equation .forward (.edge I J i j))) true)
    (.implies (.cell (.atom .forward a b) true)
      (.implies (.fixed source) (.fixed target)))

def selectedWitness (I J : Type u) (i : I) (j : J) (a b : U.Atom)
    (source target : Prop) : Formula (Query.{u, v} U mode) :=
  requiredEquation (A := A) (B := B) I J i j a b source target

def requiredAxis (K L : Type u) (i : K) (j : L) (source target : Prop) :
    Formula (Query.{u, v} U mode) :=
  .implies (.cell (.signatureAxis (.edge K L i j)) true)
    (.implies (.fixed source) (.fixed target))

def supportVisible (W : ArchCtx A) (V : ArchCtx B) (a b : U.Atom)
    (source target : Prop) : Formula (Query.{u, v} U mode) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atom .forward a b) true)
      (.implies (.fixed source) (.fixed target)))

def equationVisible (W : ArchCtx A) (V : ArchCtx B) (I J : Type u)
    (i : I) (j : J) (a b : U.Atom) (source target : Prop) :
    Formula (Query.{u, v} U mode) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.equation .forward (.edge I J i j))) true)
      (.implies (.cell (.atom .forward a b) true)
        (.implies (.fixed source) (.fixed target))))

def witnessVisible (W : ArchCtx A) (V : ArchCtx B) (I J : Type u)
    (i : I) (j : J) (a b : U.Atom) (source target : Prop) :
    Formula (Query.{u, v} U mode) :=
  equationVisible (A := A) (B := B) W V I J i j a b source target

def axisReadable (W : ArchCtx A) (V : ArchCtx B) (K L : Type u)
    (i : K) (j : L) (source target : Prop) : Formula (Query.{u, v} U mode) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.signatureAxis (.edge K L i j)) true)
      (.implies (.fixed source) (.fixed target)))

def boundaryVisible (W X : ArchCtx A) (V Y : ArchCtx B)
    (source target : Prop) : Formula (Query.{u, v} U mode) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.context .forward X Y)) true)
      (.implies (.fixed source) (.fixed target)))

/-- The nine coverage fields are exactly evaluations of the nine finite
formula families, instance by instance. -/
theorem pointLaws_iff_formulas
    (I J K L : Type u)
    (source : IndependentCoveragePrimitive.Table A)
    (target : IndependentCoveragePrimitive.Table B)
    (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.Coverage.PointLaws I J K L source target h ↔
      (∀ a b, (requiredSupport a b (source (.requiredSupport a))
        (target (.requiredSupport b))).evaluate h) ∧
      (∀ i j a b, (requiredEquation (A := A) (B := B) I J i j a b
        (source (.requiredEquation I i a)) (target (.requiredEquation J j b))).evaluate h) ∧
      (∀ i j a b, (selectedWitness (A := A) (B := B) I J i j a b
        (source (.selectedWitness I i a)) (target (.selectedWitness J j b))).evaluate h) ∧
      (∀ i j, (requiredAxis K L i j (source (.requiredAxis K i))
        (target (.requiredAxis L j))).evaluate h) ∧
      (∀ W V a b, (supportVisible (A := A) (B := B) W V a b
        (source (.supportVisible W a)) (target (.supportVisible V b))).evaluate h) ∧
      (∀ W V i j a b, (equationVisible (A := A) (B := B) W V I J i j a b
        (source (.equationVisible W I i a)) (target (.equationVisible V J j b))).evaluate h) ∧
      (∀ W V i j a b, (witnessVisible (A := A) (B := B) W V I J i j a b
        (source (.witnessVisible W I i a)) (target (.witnessVisible V J j b))).evaluate h) ∧
      (∀ W V i j, (axisReadable (A := A) (B := B) W V K L i j
        (source (.axisReadable W K i)) (target (.axisReadable V L j))).evaluate h) ∧
      (∀ W X V Y, (boundaryVisible (A := A) (B := B) W X V Y
        (source (.boundaryVisible W X)) (target (.boundaryVisible V Y))).evaluate h) := by
  constructor
  · intro hp
    exact ⟨hp.requiredSupport, hp.requiredEquation, hp.selectedWitness,
      hp.requiredAxis, hp.supportVisible, hp.equationVisible,
      hp.witnessVisible, hp.axisReadable, hp.boundaryVisible⟩
  · rintro ⟨hSupport, hEquation, hWitness, hAxis, hSupportVisible,
      hEquationVisible, hWitnessVisible, hAxisReadable, hBoundary⟩
    exact {
      requiredSupport := hSupport
      requiredEquation := hEquation
      selectedWitness := hWitness
      requiredAxis := hAxis
      supportVisible := hSupportVisible
      equationVisible := hEquationVisible
      witnessVisible := hWitnessVisible
      axisReadable := hAxisReadable
      boundaryVisible := hBoundary }

end Coverage

/-! ## Coefficient preservation: zero, one, addition, multiplication -/

namespace Coefficient

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Embed a candidate coefficient edge into the complete common query. -/
def query (q : IndependentCarrierGraph.Query.{v, v}) : Query.{u, v} U mode :=
  .coefficient q

def zero {K L : Type v} (s : IndependentRingPrimitive.Table K)
    (t : IndependentRingPrimitive.Table L) : Formula (Query.{u, v} U mode) :=
  .cell (.coefficient (.edge K L (s .zero) (t .zero))) true

def one {K L : Type v} (s : IndependentRingPrimitive.Table K)
    (t : IndependentRingPrimitive.Table L) : Formula (Query.{u, v} U mode) :=
  .cell (.coefficient (.edge K L (s .one) (t .one))) true

def add {K L : Type v} (s : IndependentRingPrimitive.Table K)
    (t : IndependentRingPrimitive.Table L) (a b : K) (c d : L) :
    Formula (Query.{u, v} U mode) :=
  .implies (.cell (.coefficient (.edge K L a c)) true)
    (.implies (.cell (.coefficient (.edge K L b d)) true)
      (.cell (.coefficient (.edge K L (s (.add a b)) (t (.add c d)))) true))

def mul {K L : Type v} (s : IndependentRingPrimitive.Table K)
    (t : IndependentRingPrimitive.Table L) (a b : K) (c d : L) :
    Formula (Query.{u, v} U mode) :=
  .implies (.cell (.coefficient (.edge K L a c)) true)
    (.implies (.cell (.coefficient (.edge K L b d)) true)
      (.cell (.coefficient (.edge K L (s (.mul a b)) (t (.mul c d)))) true))

/-- The four ring-map clauses are quantified closures of finite common-query
formula instances. -/
theorem preserves_iff_formulas {K L : Type v}
    (s : IndependentRingPrimitive.Table K) (t : IndependentRingPrimitive.Table L)
    (h : Table.{u, v} U mode) :
    IndependentRingCarrierGraph.Preserves s t (coefficient h) ↔
      (zero (U := U) (mode := mode) s t).evaluate h ∧
      (one (U := U) (mode := mode) s t).evaluate h ∧
      (∀ a b c d, (add (U := U) (mode := mode) s t a b c d).evaluate h) ∧
      (∀ a b c d, (mul (U := U) (mode := mode) s t a b c d).evaluate h) := by
  constructor
  · intro hp
    exact ⟨hp.zero, hp.one, hp.add, hp.mul⟩
  · rintro ⟨hzero, hone, hadd, hmul⟩
    exact ⟨hzero, hone, hadd, hmul⟩

/-- Coefficient totality, carrier typing, and the four ring clauses are all
quantified closures of finite formula instances. -/
theorem pointLaws_iff_instances
    (s t : IndependentRingPrimitive.Carrier.Table.{v})
    (hs : IndependentRingPrimitive.Carrier.IsTyped s)
    (ht : IndependentRingPrimitive.Carrier.IsTyped t)
    (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.Coefficient.PointLaws s t hs ht h ↔
      CarrierRows.Instances h (query (U := U) (mode := mode))
        (IndependentRingPrimitive.Carrier.carrier s)
        (IndependentRingPrimitive.Carrier.carrier t) ∧
      (zero (U := U) (mode := mode)
        (IndependentRingPrimitive.Carrier.active s hs)
        (IndependentRingPrimitive.Carrier.active t ht)).evaluate h ∧
      (one (U := U) (mode := mode)
        (IndependentRingPrimitive.Carrier.active s hs)
        (IndependentRingPrimitive.Carrier.active t ht)).evaluate h ∧
      (∀ a b c d, (add (U := U) (mode := mode)
        (IndependentRingPrimitive.Carrier.active s hs)
        (IndependentRingPrimitive.Carrier.active t ht) a b c d).evaluate h) ∧
      (∀ a b c d, (mul (U := U) (mode := mode)
        (IndependentRingPrimitive.Carrier.active s hs)
        (IndependentRingPrimitive.Carrier.active t ht) a b c d).evaluate h) := by
  change (IndependentCarrierGraph.IsLawful _ _ (fun q => h (.coefficient q)) ∧
    IndependentRingCarrierGraph.Preserves _ _ (fun q => h (.coefficient q))) ↔ _
  constructor
  · rintro ⟨hrows, hpreserves⟩
    exact ⟨(CarrierRows.lawful_iff_instances h
      (query (U := U) (mode := mode)) _ _).mp (by simpa [query] using hrows),
      (preserves_iff_formulas _ _ h).mp hpreserves⟩
  · rintro ⟨hrows, hpreserves⟩
    exact ⟨by
      simpa [query] using (CarrierRows.lawful_iff_instances h
        (query (U := U) (mode := mode)) _ _).mpr hrows,
      (preserves_iff_formulas _ _ h).mpr hpreserves⟩

end Coefficient

/-! ## Overlap: one fixed six-guard instance -/

namespace Overlap

variable {U : AtomCarrier.{u}} {mode : Mode} {A B : ArchitectureObject U}

def lawInstance (s : IndependentOverlapCandidate.Table A)
    (t : IndependentOverlapCandidate.Table B)
    (d : IndependentContextPrimitive.Table B)
    (W X Y : ArchCtx A) (base left right : ArchCtx B)
    (R : ArchCtx A) (S T : ArchCtx B) : Formula (Query.{u, v} U mode) :=
  .implies (.cell (.atObjects A B (.context .backward W base)) true)
    (.implies (.cell (.atObjects A B (.context .backward X left)) true)
      (.implies (.cell (.atObjects A B (.context .backward Y right)) true)
        (.implies (.fixed ((s (.matching W X Y R)).down = true))
          (.implies (.fixed ((t (.matching base left right S)).down = true))
            (.implies (.cell (.atObjects A B (.context .forward R T)) true)
              (.and (.fixed (d (.le T S)).down) (.fixed (d (.le S T)).down)))))))

/-- Every fixed overlap preservation instance has the displayed finite common
support; the two target order facts are endpoint cells and add no Hom queries. -/
theorem pointLaws_iff_formulas
    (s : IndependentOverlapCandidate.Table A)
    (t : IndependentOverlapCandidate.Table B)
    (d : IndependentContextPrimitive.Table B)
    (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.Overlap.PointLaws s t d h ↔
      ∀ W X Y base left right R S T,
        (lawInstance (U := U) (mode := mode) s t d W X Y base left right R S T).evaluate h := by
  constructor
  · exact fun hp W X Y base left right R S T => hp W X Y base left right R S T
  · exact fun hp W X Y base left right R S T => hp W X Y base left right R S T

end Overlap

/-! ## Raw point clauses with finite common-query support -/

namespace Raw

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U}

/-- Convert one native inverse-coordinate query to its common-table cell. -/
def explicitCoordinateQuery (W : ArchCtx A) (V : ArchCtx B) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
  | .forward q => .atObjects A B (.raw (.coordinate .forward W V q))
  | .backward q => .atObjects A B (.raw (.coordinate .backward W V
      (IndependentGeometryHomPrimitive.InverseRows.reverse q)))

/-- Convert one native inverse-relation query to its common-table cell. -/
def explicitRelationQuery (W : ArchCtx A) (V : ArchCtx B) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
  | .forward q => .atObjects A B (.raw (.relation .forward W V q))
  | .backward q => .atObjects A B (.raw (.relation .backward W V
      (IndependentGeometryHomPrimitive.InverseRows.reverse q)))

/-- Convert one dependent inverse local-data query to its common-table cell. -/
def explicitLocalDataQuery (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (c : C) (d : D) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
  | .forward q => .atObjects A B (.raw (.localData .forward W V C D c d q))
  | .backward q => .atObjects A B (.raw (.localData .backward W V C D c d
      (IndependentGeometryHomPrimitive.InverseRows.reverse q)))

/-- Active explicit coordinate rows are exactly finite typed/total/inverse
instances over the common Hom query. -/
theorem explicitCoordinateRows_iff_instances (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u) :
    IndependentInverseGraph.IsLawful C D
      (IndependentGeometryHomPrimitive.InverseRows.coordinate h A B W V) ↔
      LawFinite.InverseRows.Instances h
        (explicitCoordinateQuery (U := U) (A := A) (B := B) W V) C D := by
  have hquery : IndependentGeometryHomPrimitive.InverseRows.coordinate h A B W V =
      fun q => h (explicitCoordinateQuery (U := U) (A := A) (B := B) W V q) := by
    funext q
    cases q <;> rfl
  rw [hquery]
  exact LawFinite.InverseRows.lawful_iff_instances h
    (explicitCoordinateQuery (U := U) (A := A) (B := B) W V) C D

/-- Active explicit relation rows have the same finite inverse-row
decomposition. -/
theorem explicitRelationRows_iff_instances (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (I J : Type u) :
    IndependentInverseGraph.IsLawful I J
      (IndependentGeometryHomPrimitive.InverseRows.relation h A B W V) ↔
      LawFinite.InverseRows.Instances h
        (explicitRelationQuery (U := U) (A := A) (B := B) W V) I J := by
  have hquery : IndependentGeometryHomPrimitive.InverseRows.relation h A B W V =
      fun q => h (explicitRelationQuery (U := U) (A := A) (B := B) W V q) := by
    funext q
    cases q <;> rfl
  rw [hquery]
  exact LawFinite.InverseRows.lawful_iff_instances h
    (explicitRelationQuery (U := U) (A := A) (B := B) W V) I J

/-- Active dependent local-data rows also reduce to fixed finite row
instances after all carrier and point witnesses are fixed. -/
theorem explicitLocalDataRows_iff_instances (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u) (c : C) (d : D)
    (L M : Type u) :
    IndependentInverseGraph.IsLawful L M
      (IndependentGeometryHomPrimitive.InverseRows.localData h A B W V C D c d) ↔
      LawFinite.InverseRows.Instances h
        (explicitLocalDataQuery (U := U) (A := A) (B := B) W V C D c d) L M := by
  have hquery : IndependentGeometryHomPrimitive.InverseRows.localData h A B W V C D c d =
      fun q => h (explicitLocalDataQuery (U := U) (A := A) (B := B) W V C D c d q) := by
    funext q
    cases q <;> rfl
  rw [hquery]
  exact LawFinite.InverseRows.lawful_iff_instances h
    (explicitLocalDataQuery (U := U) (A := A) (B := B) W V C D c d) L M

def explicitCoordinateInactive (W : ArchCtx A) (V : ArchCtx B)
    (direction : Direction) (q : IndependentCarrierGraph.Query.{u, u}) :
    Formula (Query.{u, v} U .explicit) :=
  inactiveCell (.atObjects A B (.context .backward W V))
    (.atObjects A B (.raw (.coordinate direction W V q)))

theorem explicitCoordinateInactive_iff (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (direction : Direction)
    (q : IndependentCarrierGraph.Query.{u, u}) :
    (explicitCoordinateInactive (U := U) W V direction q).evaluate h ↔
      h (.atObjects A B (.context .backward W V)) = false →
        h (.atObjects A B (.raw (.coordinate direction W V q))) = false := Iff.rfl

def explicitRelationInactive (W : ArchCtx A) (V : ArchCtx B)
    (direction : Direction) (q : IndependentCarrierGraph.Query.{u, u}) :
    Formula (Query.{u, v} U .explicit) :=
  inactiveCell (.atObjects A B (.context .backward W V))
    (.atObjects A B (.raw (.relation direction W V q)))

theorem explicitRelationInactive_iff (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (direction : Direction)
    (q : IndependentCarrierGraph.Query.{u, u}) :
    (explicitRelationInactive (U := U) W V direction q).evaluate h ↔
      h (.atObjects A B (.context .backward W V)) = false →
        h (.atObjects A B (.raw (.relation direction W V q))) = false := Iff.rfl

def explicitLocalDataInactive (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (c : C) (d : D) (direction : Direction)
    (q : IndependentCarrierGraph.Query.{u, u}) : Formula (Query.{u, v} U .explicit) :=
  .implies
    (.or (.cell (.atObjects A B (.context .backward W V)) false)
      (.cell (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) false))
    (.cell (.atObjects A B (.raw (.localData direction W V C D c d q))) false)

theorem explicitLocalDataInactive_iff (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u) (c : C) (d : D)
    (direction : Direction) (q : IndependentCarrierGraph.Query.{u, u}) :
    (explicitLocalDataInactive (U := U) W V C D c d direction q).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = false ∨
        h (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) = false) →
      h (.atObjects A B (.raw (.localData direction W V C D c d q))) = false := Iff.rfl

def explicitLabel (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (c : C) (d : D) (labelsEqual : Prop) :
    Formula (Query.{u, v} U .explicit) :=
  .implies (.cell (.atObjects A B (.context .backward W V)) true)
    (.implies
      (.cell (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) true)
      (.fixed labelsEqual))

theorem explicitLabel_iff (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u) (c : C) (d : D)
    (labelsEqual : Prop) :
    (explicitLabel (U := U) W V C D c d labelsEqual).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = true →
        h (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) = true →
        labelsEqual) := Iff.rfl

def representativeCoordinate (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .backward W V)) true) (.fixed equal)

theorem representativeCoordinate_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    (representativeCoordinate (U := U) W V equal).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = true → equal) := Iff.rfl

def representativeRelation (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    Formula (Query.{u, v} U .representative) :=
  representativeCoordinate W V equal

theorem representativeRelation_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    (representativeRelation (U := U) W V equal).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = true → equal) := Iff.rfl

def representativeLabel (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    Formula (Query.{u, v} U .representative) :=
  representativeCoordinate W V equal

theorem representativeLabel_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    (representativeLabel (U := U) W V equal).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = true → equal) := Iff.rfl

def representativeLocalData (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    Formula (Query.{u, v} U .representative) :=
  representativeCoordinate W V equal

theorem representativeLocalData_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (equal : Prop) :
    (representativeLocalData (U := U) W V equal).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = true → equal) := Iff.rfl

/-- One fixed strict-coordinate coefficient instance uses one context cell and
one coefficient cell. -/
def representativePolynomial (W : ArchCtx A) (V : ArchCtx B)
    (K L : Type v) (a : K) (b : L) : Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .backward W V)) true)
    (.cell (.coefficient (.edge K L a b)) true)

theorem representativePolynomial_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (K L : Type v) (a : K) (b : L) :
    (representativePolynomial (U := U) W V K L a b).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = true →
        h (.coefficient (.edge K L a b)) = true) := Iff.rfl

/-- A fixed representative image instance adds the second inverse-context
guard but still reads one coefficient point. -/
def representativeImage (W X : ArchCtx A) (V Y : ArchCtx B)
    (K L : Type v) (a : K) (b : L) (readable : Prop) :
    Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .backward W V)) true)
    (.implies (.cell (.atObjects A B (.context .backward X Y)) true)
      (.implies (.fixed readable) (.cell (.coefficient (.edge K L a b)) true)))

/-- Endpoint-only part of a representative image instance. -/
def representativeImageFixed (W X : ArchCtx A) (V Y : ArchCtx B)
    (readable fact : Prop) : Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .backward W V)) true)
    (.implies (.cell (.atObjects A B (.context .backward X Y)) true)
      (.implies (.fixed readable) (.fixed fact)))

theorem representativeImage_iff (h : Table.{u, v} U .representative)
    (W X : ArchCtx A) (V Y : ArchCtx B) (K L : Type v)
    (a : K) (b : L) (readable : Prop) :
    (representativeImage (U := U) W X V Y K L a b readable).evaluate h ↔
      (h (.atObjects A B (.context .backward W V)) = true →
        h (.atObjects A B (.context .backward X Y)) = true → readable →
        h (.coefficient (.edge K L a b)) = true) := Iff.rfl

/-- A representative optional-polynomial clause is a fixed presence fact and,
for each selected pair of sparse values and exponent, one finite coefficient
formula. -/
theorem representativeOptionalPoints_iff_formulas
    (h : Table.{u, v} U .representative) (W : ArchCtx A) (V : ArchCtx B)
    (C : Type u) (K L : Type v) {zk : K} {zl : L}
    (p : Option (IndependentPolynomialExpressions.Sparse C K zk))
    (q : Option (IndependentPolynomialExpressions.Sparse C L zl)) :
    (h (.atObjects A B (.context .backward W V)) = true →
      IndependentPolynomialCoefficientPoints.OptionalPoints
        (fun a b => h (.coefficient (.edge K L a b))) p q) ↔
      (representativeCoordinate (U := U) W V (p.isSome = q.isSome)).evaluate h ∧
      (∀ x y, p = some x → q = some y → ∀ m,
        (representativePolynomial (U := U) W V K L
          (IndependentPolynomialPointTransport.sparseCoefficient x m)
          (IndependentPolynomialPointTransport.sparseCoefficient y m)).evaluate h) := by
  constructor
  · intro hp
    constructor
    · intro hcontext
      exact (hp hcontext).1
    · intro x y hx hy m hcontext
      exact (hp hcontext).2 x y hx hy m
  · rintro ⟨hpresence, hcoefficients⟩ hcontext
    constructor
    · exact hpresence hcontext
    · intro x y hx hy m
      exact hcoefficients x y hx hy m hcontext

/-- A representative variable-image clause adds its second context guard and
readability fact while every fixed exponent still reads one coefficient
cell. -/
theorem representativeOptionalImage_iff_formulas
    (h : Table.{u, v} U .representative)
    (W X : ArchCtx A) (V Y : ArchCtx B) (C : Type u)
    (K L : Type v) {zk : K} {zl : L}
    (p : Option (IndependentPolynomialExpressions.Sparse C K zk))
    (q : Option (IndependentPolynomialExpressions.Sparse C L zl))
    (readable : Prop) :
    (h (.atObjects A B (.context .backward W V)) = true →
      h (.atObjects A B (.context .backward X Y)) = true → readable →
      IndependentPolynomialCoefficientPoints.OptionalPoints
        (fun a b => h (.coefficient (.edge K L a b))) p q) ↔
      (representativeImageFixed (U := U) W X V Y readable
        (p.isSome = q.isSome)).evaluate h ∧
      (∀ x y, p = some x → q = some y → ∀ m,
        (representativeImage (U := U) W X V Y K L
          (IndependentPolynomialPointTransport.sparseCoefficient x m)
          (IndependentPolynomialPointTransport.sparseCoefficient y m) readable).evaluate h) := by
  constructor
  · intro hp
    constructor
    · intro hWV hXY hreadable
      exact (hp hWV hXY hreadable).1
    · intro x y hx hy m hWV hXY hreadable
      exact (hp hWV hXY hreadable).2 x y hx hy m
  · rintro ⟨hpresence, hcoefficients⟩ hWV hXY hreadable
    constructor
    · exact hpresence hWV hXY hreadable
    · intro x y hx hy m
      exact hcoefficients x y hx hy m hWV hXY hreadable

/-- Coordinate cells used by one explicit polynomial monomial comparison. -/
def explicitMonomialSupport (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (m : C →₀ ℕ) (n : D →₀ ℕ) :
    Finset (Query.{u, v} U .explicit) := by
  classical
  exact m.support.biUnion fun c => n.support.image fun d =>
    .atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))

/-- Full common support of one explicit relation-polynomial monomial instance. -/
def explicitPolynomialSupport (W : ArchCtx A) (V : ArchCtx B)
    (C D I J : Type u) (i : I) (j : J)
    (K L : Type v) (a : K) (b : L) (m : C →₀ ℕ) (n : D →₀ ℕ) :
    Finset (Query.{u, v} U .explicit) := by
  classical
  exact {.atObjects A B (.context .backward W V),
      .atObjects A B (.raw (.relation .forward W V (.edge I J i j))),
      .coefficient (.edge K L a b)} ∪ explicitMonomialSupport W V C D m n

/-- Agreement on the explicit polynomial support preserves the fixed
monomial-law instance, including both guards, finite coordinate matching, and
the one coefficient cell. -/
theorem explicitPolynomial_instance_iff_of_support
    (first second : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (C D I J : Type u) (i : I) (j : J)
    (K L : Type v) {zk : K} {zl : L}
    (p : IndependentPolynomialExpressions.Sparse C K zk)
    (p' : IndependentPolynomialExpressions.Sparse D L zl)
    (m : C →₀ ℕ) (n : D →₀ ℕ)
    (agree : ∀ q ∈ explicitPolynomialSupport W V C D I J i j K L
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient p' n) m n,
      first q = second q) :
    (first (.atObjects A B (.context .backward W V)) = true →
      first (.atObjects A B (.raw (.relation .forward W V (.edge I J i j)))) = true →
      IndependentPolynomialPointTransport.MonomialMatch
        (fun c d => first (.atObjects A B
          (.raw (.coordinate .forward W V (.edge C D c d))))) m n →
      first (.coefficient (.edge K L
        (IndependentPolynomialPointTransport.sparseCoefficient p m)
        (IndependentPolynomialPointTransport.sparseCoefficient p' n))) = true) ↔
    (second (.atObjects A B (.context .backward W V)) = true →
      second (.atObjects A B (.raw (.relation .forward W V (.edge I J i j)))) = true →
      IndependentPolynomialPointTransport.MonomialMatch
        (fun c d => second (.atObjects A B
          (.raw (.coordinate .forward W V (.edge C D c d))))) m n →
      second (.coefficient (.edge K L
        (IndependentPolynomialPointTransport.sparseCoefficient p m)
        (IndependentPolynomialPointTransport.sparseCoefficient p' n))) = true) := by
  classical
  have hcontext := agree (.atObjects A B (.context .backward W V)) (by
    simp [explicitPolynomialSupport])
  have hrelation := agree
    (.atObjects A B (.raw (.relation .forward W V (.edge I J i j)))) (by
      simp [explicitPolynomialSupport])
  have hcoefficient := agree (.coefficient (.edge K L
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient p' n))) (by
    simp [explicitPolynomialSupport])
  have hcoordinate : ∀ c ∈ m.support, ∀ d ∈ n.support,
      first (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) =
        second (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) := by
    intro c hc d hd
    apply agree
    have hmonomial :
        (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d))) :
          Query.{u, v} U .explicit) ∈ explicitMonomialSupport W V C D m n := by
      simp only [explicitMonomialSupport, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨c, hc, d, hd, rfl⟩
    simp [explicitPolynomialSupport, hmonomial]
  have hpoint := IndependentPolynomialPointTransport.point_instance_iff_of_cells
    (fun c d => first (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))))
    (fun c d => second (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))))
    (fun x y => first (.coefficient (.edge K L x y)))
    (fun x y => second (.coefficient (.edge K L x y)))
    p p' m n hcoordinate hcoefficient
  constructor
  · intro hfirst hsecondContext hsecondRelation
    apply hpoint.mp
    apply hfirst
    · simpa [hcontext] using hsecondContext
    · simpa [hrelation] using hsecondRelation
  · intro hsecond hfirstContext hfirstRelation
    apply hpoint.mpr
    apply hsecond
    · simpa [hcontext] using hfirstContext
    · simpa [hrelation] using hfirstRelation

/-- Common support of one explicit variable-image monomial instance. -/
def explicitImageSupport (W X : ArchCtx A) (V Y : ArchCtx B)
    (C D E F : Type u) (x : E) (y : F)
    (K L : Type v) (a : K) (b : L) (m : C →₀ ℕ) (n : D →₀ ℕ) :
    Finset (Query.{u, v} U .explicit) := by
  classical
  exact {.atObjects A B (.context .backward W V),
      .atObjects A B (.context .backward X Y),
      .atObjects A B (.raw (.coordinate .forward X Y (.edge E F x y))),
      .coefficient (.edge K L a b)} ∪ explicitMonomialSupport W V C D m n

/-- Agreement on the image-instance support preserves both inverse-context
guards, the selected variable pair, finite monomial matching, and its one
coefficient cell. -/
theorem explicitImage_instance_iff_of_support
    (first second : Table.{u, v} U .explicit)
    (W X : ArchCtx A) (V Y : ArchCtx B) (C D E F : Type u) (x : E) (y : F)
    (K L : Type v) {zk : K} {zl : L}
    (p : IndependentPolynomialExpressions.Sparse C K zk)
    (p' : IndependentPolynomialExpressions.Sparse D L zl)
    (m : C →₀ ℕ) (n : D →₀ ℕ)
    (agree : ∀ q ∈ explicitImageSupport W X V Y C D E F x y K L
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient p' n) m n,
      first q = second q) :
    (first (.atObjects A B (.context .backward W V)) = true →
      first (.atObjects A B (.context .backward X Y)) = true →
      first (.atObjects A B
        (.raw (.coordinate .forward X Y (.edge E F x y)))) = true →
      IndependentPolynomialPointTransport.MonomialMatch
        (fun c d => first (.atObjects A B
          (.raw (.coordinate .forward W V (.edge C D c d))))) m n →
      first (.coefficient (.edge K L
        (IndependentPolynomialPointTransport.sparseCoefficient p m)
        (IndependentPolynomialPointTransport.sparseCoefficient p' n))) = true) ↔
    (second (.atObjects A B (.context .backward W V)) = true →
      second (.atObjects A B (.context .backward X Y)) = true →
      second (.atObjects A B
        (.raw (.coordinate .forward X Y (.edge E F x y)))) = true →
      IndependentPolynomialPointTransport.MonomialMatch
        (fun c d => second (.atObjects A B
          (.raw (.coordinate .forward W V (.edge C D c d))))) m n →
      second (.coefficient (.edge K L
        (IndependentPolynomialPointTransport.sparseCoefficient p m)
        (IndependentPolynomialPointTransport.sparseCoefficient p' n))) = true) := by
  classical
  have hcontextSource := agree (.atObjects A B (.context .backward W V)) (by
    simp [explicitImageSupport])
  have hcontextTarget := agree (.atObjects A B (.context .backward X Y)) (by
    simp [explicitImageSupport])
  have hvariable := agree
    (.atObjects A B (.raw (.coordinate .forward X Y (.edge E F x y)))) (by
      simp [explicitImageSupport])
  have hcoefficient := agree (.coefficient (.edge K L
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient p' n))) (by
    simp [explicitImageSupport])
  have hcoordinate : ∀ c ∈ m.support, ∀ d ∈ n.support,
      first (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) =
        second (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) := by
    intro c hc d hd
    apply agree
    have hmonomial :
        (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d))) :
          Query.{u, v} U .explicit) ∈ explicitMonomialSupport W V C D m n := by
      simp only [explicitMonomialSupport, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨c, hc, d, hd, rfl⟩
    simp [explicitImageSupport, hmonomial]
  have hpoint := IndependentPolynomialPointTransport.point_instance_iff_of_cells
    (fun c d => first (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))))
    (fun c d => second (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))))
    (fun a b => first (.coefficient (.edge K L a b)))
    (fun a b => second (.coefficient (.edge K L a b)))
    p p' m n hcoordinate hcoefficient
  constructor
  · intro hfirst hsecondSource hsecondTarget hsecondVariable
    apply hpoint.mp
    apply hfirst
    · simpa [hcontextSource] using hsecondSource
    · simpa [hcontextTarget] using hsecondTarget
    · simpa [hvariable] using hsecondVariable
  · intro hsecond hfirstSource hfirstTarget hfirstVariable
    apply hpoint.mpr
    apply hsecond
    · simpa [hcontextSource] using hfirstSource
    · simpa [hcontextTarget] using hfirstTarget
    · simpa [hvariable] using hfirstVariable

end Raw

/-! ## Representative and explicit realization instances -/

namespace Realization

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U}

/-- The common forward context cell indexing every realization fiber row. -/
def contextQuery (W : ArchCtx A) (V : ArchCtx B) : Query.{u, v} U mode :=
  .atObjects A B (.context .forward W V)

/-- Representative support point as a complete common query. -/
def representativeSupportQuery (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) : Query.{u, v} U .representative :=
  .atObjects A B (.realization (.representativeSupport W V x y))

/-- Representative axis point as a complete common query. -/
def representativeAxisQuery (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) : Query.{u, v} U .representative :=
  .atObjects A B (.realization (.representativeAxis W V x y))

/-- Representative observable point as a complete common query. -/
def representativeObservableQuery (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) : Query.{u, v} U .representative :=
  .atObjects A B (.realization (.representativeObservable W V x y))

/-- Explicit support point in one of the two retained directions. -/
def explicitSupportQuery (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) : Query.{u, v} U .explicit :=
  .atObjects A B (.realization (.explicitSupport direction W V x y))

/-- Explicit axis point in one of the two retained directions. -/
def explicitAxisQuery (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) : Query.{u, v} U .explicit :=
  .atObjects A B (.realization (.explicitAxis direction W V x y))

/-- Explicit observable point in one of the two retained directions. -/
def explicitObservableQuery (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) : Query.{u, v} U .explicit :=
  .atObjects A B (.realization (.explicitObservable direction W V x y))

/-- Representative support row lawfulness is exactly its finite formula
instances. -/
theorem representativeSupportRows_iff_instances (h : Table.{u, v} U .representative) :
    IndependentFixedIndexedPointGraph.IsLawful
      (fun W : ArchCtx A => W.Support) (fun V : ArchCtx B => V.Support)
      (IndependentGeometryHomPrimitive.RepresentativeRealization.contextPoints h)
      (IndependentGeometryHomPrimitive.RepresentativeRealization.support h) ↔
      IndexedRows.Instances (S := fun W : ArchCtx A => W.Support)
        (T := fun V : ArchCtx B => V.Support) h
        (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
        (representativeSupportQuery (U := U) (A := A) (B := B)) := by
  simpa [contextQuery, representativeSupportQuery,
    IndependentGeometryHomPrimitive.RepresentativeRealization.contextPoints,
    IndependentGeometryHomPrimitive.RepresentativeRealization.support] using
    (IndexedRows.lawful_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
      (representativeSupportQuery (U := U) (A := A) (B := B)))

/-- Representative axis row lawfulness is exactly its finite formula
instances. -/
theorem representativeAxisRows_iff_instances (h : Table.{u, v} U .representative) :
    IndependentFixedIndexedPointGraph.IsLawful
      (fun W : ArchCtx A => W.Axis) (fun V : ArchCtx B => V.Axis)
      (IndependentGeometryHomPrimitive.RepresentativeRealization.contextPoints h)
      (IndependentGeometryHomPrimitive.RepresentativeRealization.axis h) ↔
      IndexedRows.Instances (S := fun W : ArchCtx A => W.Axis)
        (T := fun V : ArchCtx B => V.Axis) h
        (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
        (representativeAxisQuery (U := U) (A := A) (B := B)) := by
  simpa [contextQuery, representativeAxisQuery,
    IndependentGeometryHomPrimitive.RepresentativeRealization.contextPoints,
    IndependentGeometryHomPrimitive.RepresentativeRealization.axis] using
    (IndexedRows.lawful_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
      (representativeAxisQuery (U := U) (A := A) (B := B)))

/-- Representative observable row lawfulness is exactly its finite formula
instances. -/
theorem representativeObservableRows_iff_instances
    (h : Table.{u, v} U .representative) :
    IndependentFixedIndexedPointGraph.IsLawful
      (fun W : ArchCtx A => W.Observable) (fun V : ArchCtx B => V.Observable)
      (IndependentGeometryHomPrimitive.RepresentativeRealization.contextPoints h)
      (IndependentGeometryHomPrimitive.RepresentativeRealization.observable h) ↔
      IndexedRows.Instances (S := fun W : ArchCtx A => W.Observable)
        (T := fun V : ArchCtx B => V.Observable) h
        (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
        (representativeObservableQuery (U := U) (A := A) (B := B)) := by
  simpa [contextQuery, representativeObservableQuery,
    IndependentGeometryHomPrimitive.RepresentativeRealization.contextPoints,
    IndependentGeometryHomPrimitive.RepresentativeRealization.observable] using
    (IndexedRows.lawful_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
      (representativeObservableQuery (U := U) (A := A) (B := B)))

/-- Explicit support inverse rows are exactly their finite instance family. -/
theorem explicitSupportRows_iff_instances (h : Table.{u, v} U .explicit) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (IndependentGeometryHomPrimitive.ExplicitRealization.contextPoints
        (A := A) (B := B) h)
      (IndependentGeometryHomPrimitive.ExplicitRealization.support
        (A := A) (B := B) h .forward)
      (IndependentGeometryHomPrimitive.ExplicitRealization.support
        (A := A) (B := B) h .backward) ↔
      IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Support)
        (T := fun V : ArchCtx B => V.Support) h
        (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
        (explicitSupportQuery (U := U) (A := A) (B := B) .forward)
        (explicitSupportQuery (U := U) (A := A) (B := B) .backward) := by
  simpa [contextQuery, explicitSupportQuery,
    IndependentGeometryHomPrimitive.ExplicitRealization.contextPoints,
    IndependentGeometryHomPrimitive.ExplicitRealization.support] using
    (IndexedRows.inverseLaws_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
      (explicitSupportQuery (U := U) (A := A) (B := B) .forward)
      (explicitSupportQuery (U := U) (A := A) (B := B) .backward))

/-- Explicit axis inverse rows are exactly their finite instance family. -/
theorem explicitAxisRows_iff_instances (h : Table.{u, v} U .explicit) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (IndependentGeometryHomPrimitive.ExplicitRealization.contextPoints
        (A := A) (B := B) h)
      (IndependentGeometryHomPrimitive.ExplicitRealization.axis
        (A := A) (B := B) h .forward)
      (IndependentGeometryHomPrimitive.ExplicitRealization.axis
        (A := A) (B := B) h .backward) ↔
      IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Axis)
        (T := fun V : ArchCtx B => V.Axis) h
        (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
        (explicitAxisQuery (U := U) (A := A) (B := B) .forward)
        (explicitAxisQuery (U := U) (A := A) (B := B) .backward) := by
  simpa [contextQuery, explicitAxisQuery,
    IndependentGeometryHomPrimitive.ExplicitRealization.contextPoints,
    IndependentGeometryHomPrimitive.ExplicitRealization.axis] using
    (IndexedRows.inverseLaws_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
      (explicitAxisQuery (U := U) (A := A) (B := B) .forward)
      (explicitAxisQuery (U := U) (A := A) (B := B) .backward))

/-- Explicit observable inverse rows are exactly their finite instance
family. -/
theorem explicitObservableRows_iff_instances (h : Table.{u, v} U .explicit) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (IndependentGeometryHomPrimitive.ExplicitRealization.contextPoints
        (A := A) (B := B) h)
      (IndependentGeometryHomPrimitive.ExplicitRealization.observable
        (A := A) (B := B) h .forward)
      (IndependentGeometryHomPrimitive.ExplicitRealization.observable
        (A := A) (B := B) h .backward) ↔
      IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Observable)
        (T := fun V : ArchCtx B => V.Observable) h
        (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
        (explicitObservableQuery (U := U) (A := A) (B := B) .forward)
        (explicitObservableQuery (U := U) (A := A) (B := B) .backward) := by
  simpa [contextQuery, explicitObservableQuery,
    IndependentGeometryHomPrimitive.ExplicitRealization.contextPoints,
    IndependentGeometryHomPrimitive.ExplicitRealization.observable] using
    (IndexedRows.inverseLaws_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
      (explicitObservableQuery (U := U) (A := A) (B := B) .forward)
      (explicitObservableQuery (U := U) (A := A) (B := B) .backward))

def representativeInactive (W : ArchCtx A) (V : ArchCtx B)
    (cell : RealizationQuery A B .representative) :
    Formula (Query.{u, v} U .representative) :=
  inactiveCell (.atObjects A B (.context .forward W V)) (.atObjects A B (.realization cell))

def representativeSupportReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) (a b : U.Atom) (source target : Prop) :
    Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.realization (.representativeSupport W V x y))) true)
      (.implies (.cell (.atom .forward a b) true)
        (.implies (.fixed source) (.fixed target))))

def representativeAxisReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) (source target : Prop) :
    Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.realization (.representativeAxis W V x y))) true)
      (.implies (.fixed source) (.fixed target)))

def representativeObservableReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) (source target : Prop) :
    Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.realization (.representativeObservable W V x y))) true)
      (.implies (.fixed source) (.fixed target)))

def representativeNaturality (W X : ArchCtx A) (V Y : ArchCtx B)
    (input output : RealizationQuery A B .representative) (responsesPresent : Prop) :
    Formula (Query.{u, v} U .representative) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.context .forward X Y)) true)
      (.implies (.cell (.atObjects A B (.realization input)) true)
        (.implies (.fixed responsesPresent)
          (.cell (.atObjects A B (.realization output)) true))))

def explicitInactive (W X : ArchCtx A) (V Y : ArchCtx B)
    (cell : RealizationQuery A B .explicit) : Formula (Query.{u, v} U .explicit) :=
  .implies
    (.or (.cell (.atObjects A B (.context .forward W V)) false)
      (.cell (.atObjects A B (.context .forward X Y)) false))
    (.cell (.atObjects A B (.realization cell)) false)

def explicitSupportReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) (a b : U.Atom) (equivalent : Prop) :
    Formula (Query.{u, v} U .explicit) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.realization (.explicitSupport .forward W V x y))) true)
      (.implies (.cell (.atom .forward a b) true) (.fixed equivalent)))

def explicitAxisReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) (equivalent : Prop) : Formula (Query.{u, v} U .explicit) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.realization (.explicitAxis .forward W V x y))) true)
      (.fixed equivalent))

def explicitObservableReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) (equivalent : Prop) :
    Formula (Query.{u, v} U .explicit) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.realization (.explicitObservable .forward W V x y))) true)
      (.fixed equivalent))

/-- One actual-action equality has two context guards, one selected input
fiber cell, the actual-action cell, and the output fiber cell. -/
def explicitAction (W X : ArchCtx A) (V Y : ArchCtx B)
    (input actual output : RealizationQuery A B .explicit) :
    Formula (Query.{u, v} U .explicit) :=
  .implies (.cell (.atObjects A B (.context .forward W V)) true)
    (.implies (.cell (.atObjects A B (.context .forward X Y)) true)
      (.implies (.cell (.atObjects A B (.realization input)) true)
        (.iff (.cell (.atObjects A B (.realization actual)) true)
          (.cell (.atObjects A B (.realization output)) true))))

theorem representativeInactive_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B)
    (cell : RealizationQuery A B .representative) :
    (representativeInactive (U := U) W V cell).evaluate h ↔
      h (.atObjects A B (.context .forward W V)) = false →
        h (.atObjects A B (.realization cell)) = false := Iff.rfl

theorem representativeSupportReads_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (x : W.Support) (y : V.Support)
    (a b : U.Atom) (source target : Prop) :
    (representativeSupportReads (U := U) W V x y a b source target).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.realization (.representativeSupport W V x y))) = true →
        h (.atom .forward a b) = true → source → target) := Iff.rfl

theorem representativeAxisReads_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (x : W.Axis) (y : V.Axis)
    (source target : Prop) :
    (representativeAxisReads (U := U) W V x y source target).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.realization (.representativeAxis W V x y))) = true →
        source → target) := Iff.rfl

theorem representativeObservableReads_iff (h : Table.{u, v} U .representative)
    (W : ArchCtx A) (V : ArchCtx B) (x : W.Observable) (y : V.Observable)
    (source target : Prop) :
    (representativeObservableReads (U := U) W V x y source target).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.realization (.representativeObservable W V x y))) = true →
        source → target) := Iff.rfl

theorem representativeNaturality_iff (h : Table.{u, v} U .representative)
    (W X : ArchCtx A) (V Y : ArchCtx B)
    (input output : RealizationQuery A B .representative) (responsesPresent : Prop) :
    (representativeNaturality (U := U) W X V Y input output responsesPresent).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.context .forward X Y)) = true →
        h (.atObjects A B (.realization input)) = true → responsesPresent →
        h (.atObjects A B (.realization output)) = true) := Iff.rfl

theorem explicitInactive_iff (h : Table.{u, v} U .explicit)
    (W X : ArchCtx A) (V Y : ArchCtx B)
    (cell : RealizationQuery A B .explicit) :
    (explicitInactive (U := U) W X V Y cell).evaluate h ↔
      ((h (.atObjects A B (.context .forward W V)) = false ∨
        h (.atObjects A B (.context .forward X Y)) = false) →
        h (.atObjects A B (.realization cell)) = false) := Iff.rfl

theorem explicitSupportReads_iff (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (x : W.Support) (y : V.Support)
    (a b : U.Atom) (equivalent : Prop) :
    (explicitSupportReads (U := U) W V x y a b equivalent).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.realization (.explicitSupport .forward W V x y))) = true →
        h (.atom .forward a b) = true → equivalent) := Iff.rfl

theorem explicitAxisReads_iff (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (x : W.Axis) (y : V.Axis)
    (equivalent : Prop) :
    (explicitAxisReads (U := U) W V x y equivalent).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.realization (.explicitAxis .forward W V x y))) = true →
        equivalent) := Iff.rfl

theorem explicitObservableReads_iff (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (x : W.Observable) (y : V.Observable)
    (equivalent : Prop) :
    (explicitObservableReads (U := U) W V x y equivalent).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.realization (.explicitObservable .forward W V x y))) = true →
        equivalent) := Iff.rfl

/-- The actual-action equality is supported by the two context cells, one
input fiber cell, the actual-action cell, and the output fiber cell. -/
theorem explicitAction_iff (h : Table.{u, v} U .explicit)
    (W X : ArchCtx A) (V Y : ArchCtx B)
    (input actual output : RealizationQuery A B .explicit) :
    (explicitAction (U := U) W X V Y input actual output).evaluate h ↔
      (h (.atObjects A B (.context .forward W V)) = true →
        h (.atObjects A B (.context .forward X Y)) = true →
        h (.atObjects A B (.realization input)) = true →
        h (.atObjects A B (.realization actual)) =
          h (.atObjects A B (.realization output))) := by
  constructor
  · intro hp hWV hXY hinput
    apply Bool.eq_iff_iff.mpr
    exact hp hWV hXY hinput
  · intro hp hWV hXY hinput
    exact Bool.eq_iff_iff.mp (hp hWV hXY hinput)

end Realization

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.LawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.LawFinite
