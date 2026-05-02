namespace Formal.Arch

universe u v

/-- An observation map from implementations to observable behavior. -/
structure Observation (Impl : Type u) (Obs : Type v) where
  observe : Impl → Obs

/-- Observational equivalence induced by an observation map. -/
def ObservationallyEquivalent {Impl : Type u} {Obs : Type v}
    (O : Observation Impl Obs) (x y : Impl) : Prop :=
  O.observe x = O.observe y

namespace ObservationallyEquivalent

/-- Observational equivalence is reflexive. -/
theorem refl {Impl : Type u} {Obs : Type v} (O : Observation Impl Obs) (x : Impl) :
    ObservationallyEquivalent O x x :=
  rfl

/-- Observational equivalence is symmetric. -/
theorem symm {Impl : Type u} {Obs : Type v} {O : Observation Impl Obs} {x y : Impl}
    (h : ObservationallyEquivalent O x y) : ObservationallyEquivalent O y x :=
  Eq.symm h

/-- Observational equivalence is transitive. -/
theorem trans {Impl : Type u} {Obs : Type v} {O : Observation Impl Obs}
    {x y z : Impl}
    (hxy : ObservationallyEquivalent O x y)
    (hyz : ObservationallyEquivalent O y z) :
    ObservationallyEquivalent O x z :=
  Eq.trans hxy hyz

end ObservationallyEquivalent

end Formal.Arch
