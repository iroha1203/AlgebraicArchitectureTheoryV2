import Formal.Arch.Projection
import Formal.Arch.Observation

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

end Formal.Arch
