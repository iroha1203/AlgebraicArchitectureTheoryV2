import Formal.Arch.Projection
import Formal.Arch.Observation
import Formal.Arch.Obstruction

namespace Formal.Arch

universe u v w

/--
Pointwise LSP condition: if `sub` is viewed through the same abstraction as
`base`, then their observations agree.
-/
def LSPCompatibleAt {Impl : Type u} {Abs : Type v} {Obs : Type w}
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs)
    (base sub : Impl) : Prop :=
  π.expose base = π.expose sub → ObservationallyEquivalent O base sub

/-- Global LSP condition for all implementations sharing an abstraction. -/
def LSPCompatible {Impl : Type u} {Abs : Type v} {Obs : Type w}
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs) : Prop :=
  ∀ {x y : Impl}, π.expose x = π.expose y → ObservationallyEquivalent O x y

/-- Observations factor through abstraction when behavior depends only on `π.expose`. -/
def ObservationFactorsThrough {Impl : Type u} {Abs : Type v} {Obs : Type w}
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs) : Prop :=
  ∃ OAbs : Abs → Obs, ∀ x : Impl, O.observe x = OAbs (π.expose x)

/-- A measured pair has observational divergence when its observations differ. -/
def ObservationallyDivergent {Impl : Type u} {Obs : Type v}
    (O : Observation Impl Obs) (x y : Impl) : Prop :=
  ¬ ObservationallyEquivalent O x y

/-- Candidate ordered implementation pairs in a finite measurement universe. -/
def lspCandidatePairs {Impl : Type u} (implementations : List Impl) :
    List (Impl × Impl) :=
  implementations.flatMap (fun x => implementations.map (fun y => (x, y)))

/--
An LSP obstruction witness: two implementations in the same abstract fiber
whose observations differ.
-/
def LSPObstruction {Impl : Type u} {Abs : Type v} {Obs : Type w}
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs)
    (pair : Impl × Impl) : Prop :=
  π.expose pair.1 = π.expose pair.2 ∧ ObservationallyDivergent O pair.1 pair.2

/-- LSP obstruction witnesses are decidable when abstraction and observation are decidable. -/
instance instDecidablePredLSPObstruction {Impl : Type u} {Abs : Type v} {Obs : Type w}
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs)
    [DecidableEq Abs] [DecidableEq Obs] :
    DecidablePred (LSPObstruction π O) := by
  intro pair
  unfold LSPObstruction ObservationallyDivergent ObservationallyEquivalent
  infer_instance

/-- No LSP obstruction witness exists at implementation-pair level. -/
def NoLSPObstruction {Impl : Type u} {Abs : Type v} {Obs : Type w}
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs) : Prop :=
  ∀ pair : Impl × Impl, ¬ LSPObstruction π O pair

/--
Executable pair-level behavioral divergence.

This is a local count for one measured pair, not a repository-wide score.
-/
def observationalDivergence {Impl : Type u} {Obs : Type v}
    [DecidableEq Obs] (O : Observation Impl Obs) (x y : Impl) : Nat :=
  if O.observe x = O.observe y then 0 else 1

/--
Ordered implementation pairs in the finite measurement universe that share an
abstraction but disagree observationally.

Duplicates in the list intentionally duplicate measured pairs, matching the
other executable signature metrics.
-/
def lspViolationPairs {Impl : Type u} {Abs : Type v} {Obs : Type w}
    [DecidableEq Abs] [DecidableEq Obs]
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs)
    (implementations : List Impl) : List (Impl × Impl) :=
  implementations.flatMap (fun x =>
    (implementations.filter (fun y =>
      decide (π.expose x = π.expose y) && ! decide (O.observe x = O.observe y))).map
        (fun y => (x, y)))

/--
Membership in finite LSP violations is exactly a measured ordered pair whose
abstraction agrees while observations differ.
-/
theorem mem_lspViolationPairs_iff {Impl : Type u} {Abs : Type v} {Obs : Type w}
    [DecidableEq Abs] [DecidableEq Obs]
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs}
    {implementations : List Impl} {pair : Impl × Impl} :
    pair ∈ lspViolationPairs π O implementations ↔
      pair.1 ∈ implementations ∧ pair.2 ∈ implementations ∧
        π.expose pair.1 = π.expose pair.2 ∧ ObservationallyDivergent O pair.1 pair.2 := by
  rcases pair with ⟨x, y⟩
  simp [lspViolationPairs, ObservationallyDivergent, ObservationallyEquivalent]

/--
Membership in candidate LSP witnesses is membership of both implementations in
the finite measurement universe.
-/
theorem mem_lspCandidatePairs_iff {Impl : Type u}
    {implementations : List Impl} {pair : Impl × Impl} :
    pair ∈ lspCandidatePairs implementations ↔
      pair.1 ∈ implementations ∧ pair.2 ∈ implementations := by
  rcases pair with ⟨x, y⟩
  simp [lspCandidatePairs]

/--
The existing finite LSP violation membership is the generic obstruction kernel
specialized to LSP obstruction witnesses.
-/
theorem mem_lspViolationPairs_iff_mem_violatingWitnesses
    {Impl : Type u} {Abs : Type v} {Obs : Type w}
    [DecidableEq Abs] [DecidableEq Obs]
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs}
    {implementations : List Impl} {pair : Impl × Impl} :
    pair ∈ lspViolationPairs π O implementations ↔
      pair ∈ violatingWitnesses (LSPObstruction π O)
        (lspCandidatePairs implementations) := by
  rw [mem_lspViolationPairs_iff, mem_violatingWitnesses_iff,
    mem_lspCandidatePairs_iff]
  unfold LSPObstruction
  constructor
  · rintro ⟨hLeft, hRight, hAbs, hDivergent⟩
    exact ⟨⟨hLeft, hRight⟩, hAbs, hDivergent⟩
  · rintro ⟨⟨hLeft, hRight⟩, hAbs, hDivergent⟩
    exact ⟨hLeft, hRight, hAbs, hDivergent⟩

/-- Executable behavioral extension metric: measured LSP violation count. -/
def lspViolationCount {Impl : Type u} {Abs : Type v} {Obs : Type w}
    [DecidableEq Abs] [DecidableEq Obs]
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs)
    (implementations : List Impl) : Nat :=
  (lspViolationPairs π O implementations).length

/-- Observationally equivalent measured pairs have zero pair-level divergence. -/
theorem observationalDivergence_eq_zero_of_equivalent
    {Impl : Type u} {Obs : Type v} [DecidableEq Obs]
    {O : Observation Impl Obs} {x y : Impl}
    (h : ObservationallyEquivalent O x y) :
    observationalDivergence O x y = 0 := by
  simp [observationalDivergence, ObservationallyEquivalent] at h ⊢
  exact h

/-- Zero pair-level divergence recovers observational equivalence. -/
theorem observationallyEquivalent_of_observationalDivergence_eq_zero
    {Impl : Type u} {Obs : Type v} [DecidableEq Obs]
    {O : Observation Impl Obs} {x y : Impl}
    (h : observationalDivergence O x y = 0) :
    ObservationallyEquivalent O x y := by
  unfold observationalDivergence at h
  by_cases hObs : O.observe x = O.observe y
  · exact hObs
  · simp [hObs] at h

/-- Global LSP implies pointwise LSP. -/
theorem lspAt_of_lsp {Impl : Type u} {Abs : Type v} {Obs : Type w}
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs}
    (h : LSPCompatible π O) (base sub : Impl) :
    LSPCompatibleAt π O base sub := by
  intro hAbs
  exact h hAbs

/-- Any implementation is substitutable for itself. -/
theorem lspCompatibleAt_refl {Impl : Type u} {Abs : Type v} {Obs : Type w}
    (π : InterfaceProjection Impl Abs) (O : Observation Impl Obs) (x : Impl) :
    LSPCompatibleAt π O x x := by
  intro _
  exact ObservationallyEquivalent.refl O x

/-- If LSP holds pointwise from `x` to `y`, the resulting observation equality is symmetric. -/
theorem lspObservation_symm {Impl : Type u} {Abs : Type v} {Obs : Type w}
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs} {x y : Impl}
    (h : LSPCompatibleAt π O x y) (hAbs : π.expose x = π.expose y) :
    ObservationallyEquivalent O y x :=
  ObservationallyEquivalent.symm (h hAbs)

/-- If observation factors through abstraction, implementations sharing an abstraction satisfy LSP. -/
theorem lspCompatible_of_observationFactorsThrough
    {Impl : Type u} {Abs : Type v} {Obs : Type w}
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs}
    (h : ObservationFactorsThrough π O) : LSPCompatible π O := by
  rcases h with ⟨OAbs, hObs⟩
  intro x y hAbs
  calc
    O.observe x = OAbs (π.expose x) := hObs x
    _ = OAbs (π.expose y) := by rw [hAbs]
    _ = O.observe y := (hObs y).symm

/--
LSP compatibility is exactly the absence of LSP obstruction witnesses.
-/
theorem lspCompatible_iff_noLSPObstruction
    {Impl : Type u} {Abs : Type v} {Obs : Type w}
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs} :
    LSPCompatible π O ↔ NoLSPObstruction π O := by
  constructor
  · intro h pair hBad
    exact hBad.2 (h hBad.1)
  · intro h x y hAbs
    by_cases hObs : ObservationallyEquivalent O x y
    · exact hObs
    · exact False.elim (h (x, y) ⟨hAbs, hObs⟩)

/--
If LSP compatibility holds, the finite executable violation count is zero.
-/
theorem lspViolationCount_eq_zero_of_lspCompatible
    {Impl : Type u} {Abs : Type v} {Obs : Type w}
    [DecidableEq Abs] [DecidableEq Obs]
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs}
    (implementations : List Impl) (h : LSPCompatible π O) :
    lspViolationCount π O implementations = 0 := by
  have hNoViolation : ∀ x y : Impl,
      (decide (π.expose x = π.expose y) && ! decide (O.observe x = O.observe y)) = false := by
    intro x y
    by_cases hAbs : π.expose x = π.expose y
    · have hObs : O.observe x = O.observe y := h hAbs
      simp [hAbs, hObs]
    · simp [hAbs]
  induction implementations with
  | nil =>
      simp [lspViolationCount, lspViolationPairs]
  | cons _ _ ih =>
      simp [lspViolationCount, lspViolationPairs, hNoViolation]
      simpa [lspViolationCount, lspViolationPairs, hNoViolation] using ih

/--
If observation factors through abstraction, the finite LSP violation count is
zero.
-/
theorem lspViolationCount_eq_zero_of_observationFactorsThrough
    {Impl : Type u} {Abs : Type v} {Obs : Type w}
    [DecidableEq Abs] [DecidableEq Obs]
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs}
    (implementations : List Impl) (h : ObservationFactorsThrough π O) :
    lspViolationCount π O implementations = 0 :=
  lspViolationCount_eq_zero_of_lspCompatible implementations
    (lspCompatible_of_observationFactorsThrough h)

/--
If every same-abstraction pair is represented in the measurement universe,
zero finite LSP violations imply graph-level LSP compatibility.
-/
theorem lspCompatible_of_lspViolationCount_eq_zero
    {Impl : Type u} {Abs : Type v} {Obs : Type w}
    [DecidableEq Abs] [DecidableEq Obs]
    {π : InterfaceProjection Impl Abs} {O : Observation Impl Obs}
    {implementations : List Impl}
    (hPairClosed : ∀ {x y : Impl}, π.expose x = π.expose y →
      x ∈ implementations ∧ y ∈ implementations)
    (hZero : lspViolationCount π O implementations = 0) :
    LSPCompatible π O := by
  intro x y hAbs
  by_cases hObs : O.observe x = O.observe y
  · exact hObs
  have hClosed := hPairClosed hAbs
  have hMem : (x, y) ∈ lspViolationPairs π O implementations := by
    rw [mem_lspViolationPairs_iff]
    exact ⟨hClosed.1, hClosed.2, hAbs, hObs⟩
  have hPositive : 0 < lspViolationCount π O implementations := by
    unfold lspViolationCount
    exact List.length_pos_of_mem hMem
  exact False.elim ((Nat.ne_of_gt hPositive) hZero)

end Formal.Arch
