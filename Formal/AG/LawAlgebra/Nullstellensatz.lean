import Formal.AG.LawAlgebra.LawfulLocus

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v

open MvPolynomial

namespace Nullstellensatz

variable (E : Type u) (k : Type v) [Field k]

/-- III.定理候補7.2A: Boolean law ideal `I_U(W) + B_W`. -/
def booleanLawIdeal (I : Ideal (MvPolynomial E k)) : Ideal (MvPolynomial E k) :=
  I ⊔ IdempotentCollapse.booleanIdeal E k

/-- III.定理候補7.2A: a point vanishes on an ideal. -/
def VanishesAtIdeal (p : E -> k) (I : Ideal (MvPolynomial E k)) : Prop :=
  ∀ f, f ∈ I -> MvPolynomial.eval p f = 0

/-- III.定理候補7.2A: the Boolean law variety is empty over `k`. -/
def BooleanLawZeroSetEmpty (I : Ideal (MvPolynomial E k)) : Prop :=
  ¬ ∃ p : E -> k, VanishesAtIdeal E k p (booleanLawIdeal E k I)

/--
III.定理候補7.2A: Architecture Nullstellensatz statement.

This is intentionally a statement-only `Prop`, not a proved theorem in PRD-3.
It records the future theorem target: emptiness of the Boolean law zero set is
equivalent to the radical unit certificate.
-/
def ArchitectureNullstellensatzCandidate (I : Ideal (MvPolynomial E k)) : Prop :=
  BooleanLawZeroSetEmpty E k I ↔ (1 : MvPolynomial E k) ∈ (booleanLawIdeal E k I).radical

/-- III.定理候補7.2A: radical unit membership certificate surface. -/
def RadicalUnitCertificate (I : Ideal (MvPolynomial E k)) : Prop :=
  (1 : MvPolynomial E k) ∈ (booleanLawIdeal E k I).radical

/--
III.定義7.2B: an abstract unlawfulness certificate with an explicit display
degree. Later finite examples can instantiate this with concrete polynomial
linear combinations.
-/
structure UnlawfulnessCertificate where
  degree : ℕ
  certifies : Prop

/-- III.定義7.2B: certificate availability by display degree. -/
def HasCertificateAt (certs : Type u) (degreeOf : certs -> ℕ) (d : ℕ) : Prop :=
  ∃ c : certs, degreeOf c ≤ d

/--
III.定義7.2B: NSdepth profile for a chosen generator system.

`depth` is packaged with its minimality proof, so monotonicity can be proved
without choosing a global computable minimization procedure.
-/
structure NSdepthProfile where
  HasCertificateAt : ℕ -> Prop
  depth : ℕ
  depth_hasCertificate : HasCertificateAt depth
  depth_minimal : ∀ d, HasCertificateAt d -> depth ≤ d

namespace NSdepthProfile

/-- III.定義7.2B: the selected Nullstellensatz depth. -/
def NSdepth (P : NSdepthProfile) : ℕ :=
  P.depth

/--
III.命題7.2C: generator extension data preserving every old certificate
display at the same degree.
-/
structure GeneratorExtension (old new : NSdepthProfile) where
  preservesCertificates : ∀ d, old.HasCertificateAt d -> new.HasCertificateAt d

/--
III.命題7.2C: adding generators cannot increase NSdepth, provided old
certificates remain valid in the extended generator system.
-/
theorem NSdepth_mono_of_generatorExtension {old new : NSdepthProfile}
    (h : GeneratorExtension old new) :
    new.NSdepth ≤ old.NSdepth :=
  new.depth_minimal old.depth (h.preservesCertificates old.depth old.depth_hasCertificate)

end NSdepthProfile

end Nullstellensatz

end LawAlgebra
end AAT.AG
