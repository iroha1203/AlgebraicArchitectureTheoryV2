import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Sets
import Formal.Util.AssertStandardAxioms

/-!
# Reconstruction from finite evaluation diagrams

This module proves the first Hom-level assembly result for G-124(A--B).  A
diagram contains finitely many typed evaluation addresses and finitely many
primitive preservation laws whose supports lie in those addresses.  A local
model contains only the corresponding partial table and proofs of those local
laws.  It does not contain a completed global map or an extension certificate.

## Implementation notes

The indexing diagram is deliberately the finite pair `(addresses, laws)`, not
a finite submodel closed under every operation.  Assembly reads a global map
from singleton diagrams.  Each primitive preservation law is recovered from
its own finite support diagram.  Thus the theorem covers exactly preservation
conditions presented by finitely supported typed equations; conditions with a
single witness shared over all addresses require a later G-124 construction.
-/

namespace AAT.AG.LocalSemanticReconstruction

universe u v w s

/-- A typed evaluation address consists of a sort and one source value. -/
abbrev EvaluationAddress (I : Type u) (X : I → Type v) := Σ i, X i

/-- A global typed point map, before any preservation laws are imposed. -/
abbrev GlobalPointMap (I : Type u) (X : I → Type v) (Y : I → Type w) :=
  ∀ i, X i → Y i

/-- The finite table read at the addresses in `S`.

The domain is finite by construction.  The codomain values need not themselves
be finite; G-124(D) adds that independent hypothesis only where effective
finite determination is claimed. -/
abbrev PartialTable {I : Type u} (X : I → Type v) (Y : I → Type w)
    (S : Finset (EvaluationAddress I X)) :=
  ∀ a : {a // a ∈ S}, Y a.1.1

namespace PartialTable

variable {I : Type u} {X : I → Type v} {Y : I → Type w}

/-- Restrict a finite table along inclusion of its address sets. -/
def restrict {S T : Finset (EvaluationAddress I X)} (h : S ⊆ T)
    (table : PartialTable X Y T) : PartialTable X Y S :=
  fun a => table ⟨a.1, h a.2⟩

/-- Read a global point map on a finite address set. -/
def read (f : GlobalPointMap I X Y) (S : Finset (EvaluationAddress I X)) :
    PartialTable X Y S :=
  fun a => f a.1.1 a.1.2

/-- A partial table has a finite input domain. -/
theorem finite_domain (S : Finset (EvaluationAddress I X)) :
    Finite {a // a ∈ S} := by
  classical
  letI : Fintype {a // a ∈ S} := Finset.fintypeCoeSort S
  infer_instance

/-- When every target sort is finite, the finite table value type is finite.

This is stronger than the finite-construction claim used by the general
reconstruction theorem and is exposed separately for later G-124(D) uses. -/
theorem finite_value_type [∀ i, Finite (Y i)]
    (S : Finset (EvaluationAddress I X)) : Finite (PartialTable X Y S) := by
  classical
  letI : Fintype {a // a ∈ S} := Finset.fintypeCoeSort S
  letI (a : {a // a ∈ S}) : Finite (Y a.1.1) := inferInstance
  infer_instance

end PartialTable

/-- A many-sorted finitary operation signature. -/
structure FinitarySignature (I : Type u) where
  /-- Primitive operation symbols. -/
  Operation : Type s
  /-- Every primitive operation has finite arity. -/
  arity : Operation → Nat
  /-- Sort of each input position. -/
  inputSort : ∀ op, Fin (arity op) → I
  /-- Sort of the output. -/
  outputSort : Operation → I

/-- An interpretation of a finitary signature on the target carriers. -/
structure TargetAlgebra {I : Type u} (signature : FinitarySignature.{u, s} I)
    (Y : I → Type w) where
  /-- Interpret one operation using only its finitely many input values. -/
  interpret : ∀ op,
    (∀ j, Y (signature.inputSort op j)) → Y (signature.outputSort op)

/-- A typed term whose leaves are addresses in one explicitly finite support.

The inductive syntax is the locality barrier: a term can inspect only supported
table entries and recursively apply a primitive finitary operation.  In
particular it has no constructor for a global point map, an existential global
extension, or an arbitrary proposition. -/
inductive LocalTerm {I : Type u} (signature : FinitarySignature.{u, s} I)
    (X : I → Type v) (support : Finset (EvaluationAddress I X)) : I → Type (max u v s)
  | variable (a : {a // a ∈ support}) : LocalTerm signature X support a.1.1
  | operation (op : signature.Operation)
      (args : ∀ j, LocalTerm signature X support (signature.inputSort op j)) :
      LocalTerm signature X support (signature.outputSort op)

namespace LocalTerm

variable {I : Type u} {signature : FinitarySignature.{u, s} I}
variable {X : I → Type v} {Y : I → Type w}
variable {support : Finset (EvaluationAddress I X)}

/-- Evaluate a local term from a finite table and the target algebra. -/
def evaluate (algebra : TargetAlgebra signature Y) (table : PartialTable X Y support) :
    {i : I} → LocalTerm signature X support i → Y i
  | _, .variable a => table a
  | _, .operation op args =>
      algebra.interpret op (fun j => evaluate algebra table (args j))

end LocalTerm

/-- One finitely supported typed equation.

Unlike an arbitrary predicate on a finite table, this structure cannot encode
the existence of a completed global map or an extension certificate: its only
semantic assertion is equality of two finite local terms. -/
structure PrimitiveLaw {I : Type u} (signature : FinitarySignature.{u, s} I)
    (X : I → Type v) where
  /-- All evaluations needed to state this one preservation equation. -/
  support : Finset (EvaluationAddress I X)
  /-- The common sort of the two sides. -/
  sort : I
  /-- Left side of the typed equation. -/
  lhs : LocalTerm signature X support sort
  /-- Right side of the typed equation. -/
  rhs : LocalTerm signature X support sort

namespace PrimitiveLaw

variable {I : Type u} {signature : FinitarySignature.{u, s} I}
variable {X : I → Type v} {Y : I → Type w}

/-- Satisfaction is generated only by interpreting the two finite local terms. -/
def Accepts (algebra : TargetAlgebra signature Y) (law : PrimitiveLaw signature X)
    (table : PartialTable X Y law.support) : Prop :=
  law.lhs.evaluate algebra table = law.rhs.evaluate algebra table

end PrimitiveLaw

namespace FiniteEvaluation

variable {I : Type u} {X : I → Type v} {Y : I → Type w}
variable {signature : FinitarySignature.{u, s} I}
variable (algebra : TargetAlgebra signature Y)
variable {K : Type*} (law : K → PrimitiveLaw signature X)

/-- A finite evaluation diagram has finitely many addresses and finitely many
primitive laws, with every selected law supported by the selected addresses. -/
structure Diagram where
  /-- Addresses whose point values are present in this local piece. -/
  addresses : Finset (EvaluationAddress I X)
  /-- Primitive preservation conditions checked in this local piece. -/
  constraints : Finset K
  /-- Every checked condition can be evaluated from the displayed table. -/
  support_subset : ∀ k ∈ constraints, (law k).support ⊆ addresses

namespace Diagram

/-- Inclusion of finite diagrams, separately on addresses and constraints. -/
def LE (d e : Diagram law) : Prop :=
  d.addresses ⊆ e.addresses ∧ d.constraints ⊆ e.constraints

/-- Diagram inclusion is reflexive. -/
theorem le_refl (d : Diagram law) : LE law d d :=
  ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩

/-- Diagram inclusion is transitive. -/
theorem le_trans {d e f : Diagram law} (hde : LE law d e) (hef : LE law e f) :
    LE law d f :=
  ⟨fun _ ha => hef.1 (hde.1 ha), fun _ hk => hef.2 (hde.2 hk)⟩

/-- Finite union is a common enlargement of two evaluation diagrams. -/
noncomputable def union (d e : Diagram law) : Diagram law := by
  classical
  exact
    { addresses := d.addresses ∪ e.addresses
      constraints := d.constraints ∪ e.constraints
      support_subset := by
        intro k hk
        rcases Finset.mem_union.mp hk with hkd | hke
        · exact fun a ha => Finset.mem_union_left _ (d.support_subset k hkd ha)
        · exact fun a ha => Finset.mem_union_right _ (e.support_subset k hke ha) }

/-- The left diagram includes into the finite common enlargement. -/
theorem le_union_left (d e : Diagram law) : LE law d (union law d e) := by
  classical
  constructor <;> intro x hx
  · exact Finset.mem_union_left _ hx
  · exact Finset.mem_union_left _ hx

/-- The right diagram includes into the finite common enlargement. -/
theorem le_union_right (d e : Diagram law) : LE law e (union law d e) := by
  classical
  constructor <;> intro x hx
  · exact Finset.mem_union_right _ hx
  · exact Finset.mem_union_right _ hx

/-- The singleton diagram used to assemble the value at one address. -/
noncomputable def point (a : EvaluationAddress I X) : Diagram law where
  addresses := {a}
  constraints := ∅
  support_subset := by simp

/-- The finite diagram containing exactly one primitive law and its support. -/
noncomputable def ofLaw (k : K) : Diagram law where
  addresses := (law k).support
  constraints := {k}
  support_subset := by
    intro j hj
    have h : j = k := Finset.mem_singleton.mp hj
    subst j
    exact Finset.Subset.rfl

end Diagram

/-- A local model on one finite diagram is a partial table satisfying only the
primitive laws explicitly selected by that diagram. -/
structure LocalModel (d : Diagram law) where
  /-- Point values at the finite address set of `d`. -/
  table : PartialTable X Y d.addresses
  /-- Each selected law holds after restriction to its own finite support. -/
  satisfies : ∀ k (hk : k ∈ d.constraints),
    (law k).Accepts algebra (PartialTable.restrict (d.support_subset k hk) table)

namespace LocalModel

/-- Local models are determined by their finite point tables; law proofs carry
no additional semantic freedom. -/
@[ext]
theorem ext {d : Diagram law} {a b : LocalModel algebra law d} (h : a.table = b.table) :
    a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Restrict a local model along inclusion of finite diagrams. -/
def restrict {d e : Diagram law} (h : Diagram.LE law d e)
    (m : LocalModel algebra law e) : LocalModel algebra law d where
  table := PartialTable.restrict h.1 m.table
  satisfies := by
    intro k hk
    simpa only [PartialTable.restrict] using m.satisfies k (h.2 hk)

/-- Restriction along reflexive diagram inclusion is the identity. -/
@[simp]
theorem restrict_refl (d : Diagram law) (m : LocalModel algebra law d) :
    restrict algebra law (Diagram.le_refl law d) m = m := by
  apply ext
  rfl

/-- Restriction along two inclusions agrees with restriction along their composite. -/
theorem restrict_trans {d e f : Diagram law}
    (hde : Diagram.LE law d e) (hef : Diagram.LE law e f)
    (m : LocalModel algebra law f) :
    restrict algebra law hde (restrict algebra law hef m) =
      restrict algebra law (Diagram.le_trans law hde hef) m := by
  apply ext
  rfl

end LocalModel

/-- An inverse-limit element of local tables: one local model on every finite
diagram, compatible with every diagram inclusion. -/
structure CoherentFamily where
  /-- Local value on each finite evaluation diagram. -/
  value : ∀ d : Diagram law, LocalModel algebra law d
  /-- Restricting a larger local value recovers the smaller one. -/
  coherent : ∀ (d e : Diagram law) (h : Diagram.LE law d e),
    LocalModel.restrict algebra law h (value e) = value d

namespace CoherentFamily

/-- A coherent family is determined by its value on every finite diagram. -/
@[ext]
theorem ext {a b : CoherentFamily algebra law}
    (h : ∀ d, a.value d = b.value d) : a = b := by
  cases a with
  | mk av ac =>
    cases b with
    | mk bv bc =>
      have hv : av = bv := by
        funext d
        exact h d
      subst bv
      rfl

end CoherentFamily

/-- A global point map satisfying every primitive preservation law. -/
structure PreservingMap where
  /-- The complete map assembled from or read into finite evaluations. -/
  toPointMap : GlobalPointMap I X Y
  /-- Every primitive law holds on its explicitly finite support. -/
  preserves : ∀ k,
    (law k).Accepts algebra (PartialTable.read toPointMap (law k).support)

namespace PreservingMap

/-- Preserving maps are determined by their point values. -/
@[ext]
theorem ext {a b : PreservingMap algebra law} (h : a.toPointMap = b.toPointMap) : a = b := by
  cases a
  cases b
  cases h
  rfl

end PreservingMap

/-- Read a preserving global map on every finite evaluation diagram. -/
def read (f : PreservingMap algebra law) : CoherentFamily algebra law where
  value d :=
    { table := PartialTable.read f.toPointMap d.addresses
      satisfies := by
        intro k hk
        simpa only [PartialTable.restrict, PartialTable.read] using f.preserves k }
  coherent := by
    intro d e h
    apply LocalModel.ext
    rfl

/-- Assemble a preserving global map from singleton evaluations in a coherent family.

Preservation is not assumed as a global extension certificate: for each law it
is transported from the local model on that law's finite support diagram. -/
noncomputable def assemble (family : CoherentFamily algebra law) : PreservingMap algebra law where
  toPointMap := fun i x =>
    (family.value (Diagram.point law ⟨i, x⟩)).table
      ⟨⟨i, x⟩, by simp [Diagram.point]⟩
  preserves := by
    intro k
    have hs := (family.value (Diagram.ofLaw law k)).satisfies k (by
      simp [Diagram.ofLaw])
    rw [show PartialTable.read
        (fun i x =>
          (family.value (Diagram.point law ⟨i, x⟩)).table
            ⟨⟨i, x⟩, by simp [Diagram.point]⟩)
        (law k).support =
        PartialTable.restrict
          ((Diagram.ofLaw law k).support_subset k (by simp [Diagram.ofLaw]))
          (family.value (Diagram.ofLaw law k)).table by
      funext a
      have hle : Diagram.LE law (Diagram.point law a.1) (Diagram.ofLaw law k) := by
        constructor
        · exact Finset.singleton_subset_iff.mpr a.2
        · simp [Diagram.point, Diagram.ofLaw]
      have hcoh := family.coherent (Diagram.point law a.1) (Diagram.ofLaw law k) hle
      have htable := congrArg LocalModel.table hcoh
      have hat := congrFun htable ⟨a.1, by simp [Diagram.point]⟩
      simpa only [PartialTable.read, PartialTable.restrict] using hat.symm]
    exact hs

/-- Assembling the finite evaluations read from a global map recovers that map. -/
@[simp]
theorem assemble_read (f : PreservingMap algebra law) :
    assemble algebra law (read algebra law f) = f := by
  apply PreservingMap.ext
  funext i x
  rfl

/-- Reading the global map assembled from a coherent family recovers every
finite local model, including its selected preservation conditions. -/
@[simp]
theorem read_assemble (family : CoherentFamily algebra law) :
    read algebra law (assemble algebra law family) = family := by
  apply CoherentFamily.ext
  intro d
  apply LocalModel.ext
  funext a
  have hle : Diagram.LE law (Diagram.point law a.1) d := by
    constructor
    · exact Finset.singleton_subset_iff.mpr a.2
    · simp [Diagram.point]
  have hcoh := family.coherent (Diagram.point law a.1) d hle
  have htable := congrArg LocalModel.table hcoh
  have hat := congrFun htable ⟨a.1, by simp [Diagram.point]⟩
  simpa only [read, assemble, PartialTable.read, PartialTable.restrict] using hat.symm

/-- Hom-level reconstruction from finite evaluation diagrams.

The forward map is restriction to every finite diagram; the inverse is
singleton assembly.  The two inverse laws separately witness separation and
assembly for all finitely supported primitive preservation conditions. -/
noncomputable def preservingMapEquivCoherentFamily :
    PreservingMap algebra law ≃ CoherentFamily algebra law where
  toFun := read algebra law
  invFun := assemble algebra law
  left_inv := assemble_read algebra law
  right_inv := read_assemble algebra law

end FiniteEvaluation

namespace FiniteEvaluationExample

/-- One unary operation symbol, interpreted below as successor. -/
inductive NatOperation
  | successor

/-- The one-sorted signature containing the unary successor operation. -/
def natSignature : FinitarySignature Unit where
  Operation := NatOperation
  arity := fun _ => 1
  inputSort := fun _ _ => ()
  outputSort := fun _ => ()

/-- Interpret the primitive operation as successor on natural numbers. -/
def natAlgebra : TargetAlgebra natSignature (fun _ => Nat) where
  interpret := fun op args => by
    cases op
    exact Nat.succ (args ⟨0, by simp [natSignature]⟩)

/-- A concrete two-address primitive law: the value at `1` is the successor of
the value at `0`.  It is built only from supported variables and the finitary
successor symbol. -/
noncomputable def natSuccessorLaw :
    PrimitiveLaw natSignature (fun _ => Nat) where
  support := {⟨(), 0⟩, ⟨(), 1⟩}
  sort := ()
  lhs := LocalTerm.variable ⟨⟨(), 1⟩, by simp⟩
  rhs := LocalTerm.operation NatOperation.successor
    (fun _ => LocalTerm.variable ⟨⟨(), 0⟩, by simp⟩)

/-- The identity point map satisfies the concrete successor law. -/
noncomputable def natIdentityPreserving :
    FiniteEvaluation.PreservingMap natAlgebra (fun _ : Unit => natSuccessorLaw) where
  toPointMap := fun _ n => n
  preserves := by
    intro k
    cases k
    rfl

/-- The constant-zero point map violates the same concrete successor law. -/
theorem natConstantZero_rejected :
    ¬natSuccessorLaw.Accepts natAlgebra
      (PartialTable.read (fun _ _ => 0) natSuccessorLaw.support) := by
  simp [PrimitiveLaw.Accepts, natSuccessorLaw, natAlgebra, LocalTerm.evaluate,
    PartialTable.read]

end FiniteEvaluationExample

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
