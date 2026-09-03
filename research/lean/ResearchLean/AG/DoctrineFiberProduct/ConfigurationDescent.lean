import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization

/-!
# Configuration descent for canonical normalization

This module proves the Type-level configuration descent clause G-116(a).  The
fixed points of the canonical normalization, the universal factorization of
normalization-invariant functions, and the quotient by equal configuration are
all identified with `AtomConfiguration`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open AtomFoundation

/-- The fixed-point type used in G-116(a).  The package `P` is the GOAL input;
the fixed-point equation is the defining subtype condition, not a theorem
premise accepted by a downstream result. -/
def CanonicalNormalizationFixed
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :=
  {object : ArchitectureObject U //
    canonicalObjectNormalization P object = object}

/-- Main equivalence for the fixed-point part of G-116(a).  It is constructed
from the object reading selected by the input package `P`; no fixed point or
inverse is supplied as an argument. -/
noncomputable def canonicalNormalizationFixedEquiv
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    CanonicalNormalizationFixed P ≃ AtomConfiguration U where
  toFun object := object.1.configuration
  invFun configuration :=
    ⟨P.reading.objectReading.object configuration,
      canonicalObjectNormalization_selected P configuration⟩
  left_inv object := by
    apply Subtype.ext
    exact object.2
  right_inv configuration :=
    P.reading.objectReading.configuration_eq configuration

/-- Main universal-factorization theorem for G-116(a).  The package `P`, target
type `Y`, and function `f` are the GOAL inputs.  Normalization invariance is the
left side of the claimed equivalence, rather than an extra certificate. -/
theorem canonicalObjectNormalization_factorization_iff
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (Y : Type v) (f : ArchitectureObject U → Y) :
    f ∘ canonicalObjectNormalization P = f ↔
      ∃! factor : AtomConfiguration U → Y,
        f = factor ∘ ArchitectureObject.configuration := by
  constructor
  · intro invariant
    refine ⟨fun configuration =>
      f (P.reading.objectReading.object configuration), ?_, ?_⟩
    · funext object
      exact (congrFun invariant object).symm
    · intro factor factorization
      funext configuration
      have atSelected := congrFun factorization
        (P.reading.objectReading.object configuration)
      simpa [Function.comp_apply,
        P.reading.objectReading.configuration_eq] using atSelected.symm
  · rintro ⟨factor, factorization, -⟩
    funext object
    calc
      f (canonicalObjectNormalization P object) =
          factor (canonicalObjectNormalization P object).configuration :=
        congrFun factorization (canonicalObjectNormalization P object)
      _ = factor object.configuration := by
        rw [canonicalObjectNormalization_configuration]
      _ = f object := (congrFun factorization object).symm

/-- Equal configuration is the quotient relation in G-116(a).  It is
independent of the package because configuration projection is independent of
`P`; it introduces no additional mathematical premise. -/
def architectureObjectConfigurationSetoid (U : AtomCarrier.{u}) :
    Setoid (ArchitectureObject U) where
  r first second := first.configuration = second.configuration
  iseqv := {
    refl := fun _ => rfl
    symm := fun equality => equality.symm
    trans := fun first second => first.trans second
  }

/-- Main quotient equivalence for G-116(a).  The inverse representative is the
object selected by the input package `P`; quotient soundness proves that the
choice is inverse without accepting a representative certificate. -/
noncomputable def architectureObjectConfigurationQuotientEquiv
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    Quotient (architectureObjectConfigurationSetoid U) ≃
      AtomConfiguration U where
  toFun := Quotient.lift ArchitectureObject.configuration (fun _ _ h => h)
  invFun configuration :=
    Quotient.mk (architectureObjectConfigurationSetoid U)
      (P.reading.objectReading.object configuration)
  left_inv quotient := by
    induction quotient using Quotient.inductionOn with
    | _ object =>
        apply Quotient.sound
        exact P.reading.objectReading.configuration_eq object.configuration
  right_inv configuration :=
    P.reading.objectReading.configuration_eq configuration

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
