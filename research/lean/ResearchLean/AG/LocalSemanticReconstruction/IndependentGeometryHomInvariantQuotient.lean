import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantWitnesses
import Formal.Util.AssertStandardAxioms

/-!
# Erasing invariant witnesses after primitive coherence

All original common Hom queries survive this quotient. Only auxiliary choices
are erased, after their finite tables satisfy restriction and primitive row
rules. Quotienting individual finite fragments first is not this construction.
The native comparison condition is the existing invariant transport proposition;
it is never used to define a presentation's coherence.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Two presentations agree precisely when every original Hom family agrees. -/
def presentationSetoid (I J : InvariantFamily U) (mode : Mode) :
    Setoid (Presentation.{u, v} I J mode) where
  r p q := p.retained = q.retained
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- Auxiliary proof choices are erased only after constructing coherent presentations. -/
abbrev Local (I J : InvariantFamily U) (mode : Mode) :=
  Quotient (presentationSetoid.{u, v} I J mode)

/-- Assembly depends on the entire retained family and not the auxiliary graph choice. -/
theorem assemblePresentation_congr (I J : InvariantFamily U)
    (p q : Presentation.{u, v} I J mode) (h : p.retained = q.retained) :
    assemblePresentation I J p = assemblePresentation I J q := Subtype.ext h

/-- Assemble the existing invariant property from a local class. -/
def assemble (I J : InvariantFamily U) : Local.{u, v} I J mode → Native I J mode :=
  Quotient.lift (assemblePresentation I J) (assemblePresentation_congr I J)

/-- Native reading chooses an auxiliary representative and immediately erases its choice. -/
def read (I J : InvariantFamily U) (f : Native.{u, v} I J mode) : Local I J mode :=
  Quotient.mk _ (readPresentation I J f)

/-- The first inverse restores every native computational role and its proof-only property. -/
theorem assemble_read (I J : InvariantFamily U) (f : Native.{u, v} I J mode) :
    assemble I J (read I J f) = f := assemble_readPresentation I J f

/-- The second inverse restores the local class without requiring an arbitrary chosen witness. -/
theorem read_assemble (I J : InvariantFamily U) (p : Local.{u, v} I J mode) :
    read I J (assemble I J p) = p := by
  induction p using Quotient.inductionOn with
  | _ p => exact Quotient.sound (show
      (readPresentation I J (assemblePresentation I J p)).retained = p.retained from rfl)

/-- All invariant kinds and arbitrary index families retain exactly their native transport scope. -/
def readingEquiv (I J : InvariantFamily U) :
    Native.{u, v} I J mode ≃ Local I J mode where
  toFun := read I J
  invFun := assemble I J
  left_inv := assemble_read I J
  right_inv := read_assemble I J

/-- Every original finite family is observable after erasing auxiliary choices. -/
def retained (I J : InvariantFamily U) : Local.{u, v} I J mode → Retained I J mode :=
  Quotient.lift Presentation.retained (fun _ _ h => h)

/-- A singleton reading keeps every common query, including context, coefficient, and raw roles. -/
def point (I J : InvariantFamily U) (p : Local.{u, v} I J mode)
    (q : IndependentGeometryHomPrimitive.Query.{u, v} U mode) : Bool :=
  (retained I J p).table q

/-- Reading preserves every original Hom query. -/
theorem point_read (I J : InvariantFamily U) (f : Native.{u, v} I J mode)
    (q : IndependentGeometryHomPrimitive.Query.{u, v} U mode) :
    point I J (read I J f) q = f.val.table q := rfl

/-- Quotient classes inject into the original coherent family; auxiliary graphs add no Homs. -/
theorem retained_injective (I J : InvariantFamily U) :
    Function.Injective (retained.{u, v} (mode := mode) I J) := by
  intro p q h
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q => exact Quotient.sound h

/-- Agreement at every original point identifies local classes. -/
theorem point_ext (I J : InvariantFamily U) (p q : Local.{u, v} I J mode)
    (h : ∀ a, point I J p a = point I J q a) : p = q := by
  apply retained_injective I J
  apply Retained.ext
  have ht : (retained I J p).table = (retained I J q).table := funext h
  have hf := congrArg TagChange.read ht
  simpa only [Retained.table, TagChange.read_assemble] using hf

/-- Each finite reading is still a finite Boolean table. -/
def fragment (I J : InvariantFamily U) (p : Local.{u, v} I J mode)
    (S : Finset (IndependentGeometryHomPrimitive.Query.{u, v} U mode)) : {q // q ∈ S} → Bool :=
  (retained I J p).family.value S

/-- Finite fragment restriction descends unchanged through witness erasure. -/
theorem fragment_coherent (I J : InvariantFamily U) (p : Local.{u, v} I J mode)
    (S T : Finset (IndependentGeometryHomPrimitive.Query.{u, v} U mode)) (h : S ⊆ T) :
    TagChange.LocalTagTable.restrict h (fragment I J p T) = fragment I J p S :=
  (retained I J p).family.coherent S T h

/-- Auxiliary choices with the same retained family always give the same local Hom. -/
theorem auxiliary_choice_independent (I J : InvariantFamily U)
    (p q : Presentation.{u, v} I J mode) (h : p.retained = q.retained) :
    (Quotient.mk _ p : Local I J mode) = Quotient.mk _ q := Quotient.sound h

/-- Erasure never identifies a difference at any original computational role. -/
theorem retained_point_separates (I J : InvariantFamily U)
    (p q : Presentation.{u, v} I J mode)
    (a : IndependentGeometryHomPrimitive.Query.{u, v} U mode)
    (hne : p.retained.table a ≠ q.retained.table a) :
    (Quotient.mk _ p : Local I J mode) ≠ Quotient.mk _ q := by
  intro he
  exact hne (congrArg (fun x => point I J x a) he)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
