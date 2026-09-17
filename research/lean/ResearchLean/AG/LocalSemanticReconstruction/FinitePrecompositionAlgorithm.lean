import ResearchLean.AG.LocalSemanticReconstruction.ComponentRestrictionCriteria
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Finite-search extension along an injective index map

For explicitly enumerable finite local indices and decidable equality on the
global indices, this file computes the unique local preimage of a global index
when one exists.  It uses `Finset.choose` under a proved uniqueness condition;
this is finite search, not `Classical.choose`.

The resulting total extension algorithm is correct whenever the supplied index
map is injective.  Boolean injectivity and surjectivity tests expose the two
finite precomposition criteria as executable decisions.  Constructing the
required finite component enumerations from finite graph tables is a separate
graph-specific obligation.
-/

namespace AAT.AG.LocalSemanticReconstruction

namespace FinitePrecomposition

/-- An existing preimage under an injective map is the unique element of the
finite local enumeration mapping to the target. -/
def uniquePreimageProof {A B : Type*} [Fintype A] [DecidableEq B]
    (q : A → B) (hinjective : Function.Injective q) (target : B)
    (hexists : ∃ source, q source = target) :
    ∃! source, source ∈ (Finset.univ : Finset A) ∧ q source = target := by
  obtain ⟨source, hsource⟩ := hexists
  refine ⟨source, ⟨Finset.mem_univ source, hsource⟩, ?_⟩
  intro other hother
  exact hinjective (hother.2.trans hsource.symm)

/-- Compute the unique finite preimage of a target known to lie in the image. -/
def preimageOfInjective {A B : Type*} [Fintype A] [DecidableEq B]
    (q : A → B) (hinjective : Function.Injective q) (target : B)
    (hexists : ∃ source, q source = target) : A :=
  Finset.univ.choose (fun source => q source = target)
    (uniquePreimageProof q hinjective target hexists)

@[simp]
theorem preimageOfInjective_spec {A B : Type*} [Fintype A] [DecidableEq B]
    (q : A → B) (hinjective : Function.Injective q) (target : B)
    (hexists : ∃ source, q source = target) :
    q (preimageOfInjective q hinjective target hexists) = target := by
  exact Finset.choose_property (p := fun source => q source = target)
    (l := Finset.univ) (uniquePreimageProof q hinjective target hexists)

/-- Extend a local family by finite preimage search, using `fallback` outside
the image of an injective index map. -/
def extensionOfInjective {A B Value : Type*} [Fintype A] [DecidableEq B]
    (q : A → B) (hinjective : Function.Injective q)
    (localFamily : A → Value) (fallback : Value) : B → Value :=
  fun target =>
    if hexists : ∃ source, q source = target then
      localFamily (preimageOfInjective q hinjective target hexists)
    else
      fallback

@[simp]
theorem extensionOfInjective_apply {A B Value : Type*}
    [Fintype A] [DecidableEq B]
    (q : A → B) (hinjective : Function.Injective q)
    (localFamily : A → Value) (fallback : Value) (source : A) :
    extensionOfInjective q hinjective localFamily fallback (q source) =
      localFamily source := by
  rw [extensionOfInjective, dif_pos ⟨source, rfl⟩]
  apply congrArg localFamily
  apply hinjective
  exact preimageOfInjective_spec q hinjective (q source) ⟨source, rfl⟩

/-- The computed extension restricts to the original local family. -/
theorem precompose_extensionOfInjective {A B Value : Type*}
    [Fintype A] [DecidableEq B]
    (q : A → B) (hinjective : Function.Injective q)
    (localFamily : A → Value) (fallback : Value) :
    ComponentRestriction.precompose q
        (extensionOfInjective q hinjective localFamily fallback) =
      localFamily := by
  funext source
  exact extensionOfInjective_apply q hinjective localFamily fallback source

/-- A total finite-search extension program.  When `q` is not injective it
returns the constant fallback family; correctness is asserted under the
injectivity condition below. -/
def extension {A B Value : Type*} [Fintype A] [DecidableEq B]
    (q : A → B) (localFamily : A → Value) (fallback : Value) : B → Value :=
  if hinjective : Function.Injective q then
    extensionOfInjective q hinjective localFamily fallback
  else
    fun _ => fallback

/-- Under the graph extension criterion (`q` injective), the total program
computes a global family restricting to the supplied local family. -/
theorem precompose_extension {A B Value : Type*}
    [Fintype A] [DecidableEq B]
    (q : A → B) (localFamily : A → Value) (fallback : Value)
    (hinjective : Function.Injective q) :
    ComponentRestriction.precompose q (extension q localFamily fallback) =
      localFamily := by
  rw [extension, dif_pos hinjective]
  exact precompose_extensionOfInjective q hinjective localFamily fallback

/-- Executable finite test for injectivity of the index map. -/
def injectiveTest {A B : Type*} [Fintype A] [DecidableEq B]
    (q : A → B) : Bool :=
  decide (Function.Injective q)

@[simp]
theorem injectiveTest_eq_true_iff {A B : Type*}
    [Fintype A] [DecidableEq B] (q : A → B) :
    injectiveTest q = true ↔ Function.Injective q := by
  simp [injectiveTest]

/-- Executable finite test for surjectivity of the index map. -/
def surjectiveTest {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    (q : A → B) : Bool :=
  decide (Function.Surjective q)

@[simp]
theorem surjectiveTest_eq_true_iff {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] (q : A → B) :
    surjectiveTest q = true ↔ Function.Surjective q := by
  simp [surjectiveTest]

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePrecomposition

end FinitePrecomposition

end AAT.AG.LocalSemanticReconstruction
