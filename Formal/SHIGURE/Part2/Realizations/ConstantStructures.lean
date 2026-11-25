import Formal.SHIGURE.Part2.Realizations.SheafStructures
import Formal.SHIGURE.Part2.Realizations.ZariskiConstants

/-!
# Constant realizations of native structures

Operations, relations and domains of the native structure are interpreted
pointwise on locally constant sections. This gives the constant structures
used in each chart of a Zariski locally split copying realization.

## Implementation notes

Finite typed tuples of locally constant functions are bundled by their
fibres. A topology on every native carrier would add unnecessary data
since the carrier sheaf already uses the discrete notion of local
constancy. Relations are equalizers of their membership functions, and
partial values use the corresponding subtype of native tuples.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S₀ : Type u} {Γ : List S₀}

/-- Each typed variable has a position inside the finite context. -/
private theorem position_lt_length {s : S₀} (i : Var Γ s) : i.position < Γ.length := by
  induction i with
  | here => exact Nat.zero_lt_succ _
  | there _ ih => exact Nat.succ_lt_succ ih

/-- The typed positions of a finite context embed in the set of its list indices. -/
private theorem finitePositions (Γ : List S₀) : Finite ((s : S₀) × Var Γ s) :=
  Finite.of_injective
    (fun i => (⟨i.2.position, position_lt_length i.2⟩ : Fin Γ.length))
    (fun _ _ h => Var.position_injective Γ (congrArg Fin.val h))

variable (S : Scheme.{u})

/-- A tuple of locally constant sections bundles into a locally constant native assignment. -/
private def bundleTuple {T : Scheme.{u}} {M : S₀ → Type u}
    (xs : Assignment (fun s => LocallyConstant T (M s)) Γ) :
    LocallyConstant T (Assignment M Γ) where
  toFun p := ⟨fun i => xs.get i p⟩
  isLocallyConstant := by
    letI := finitePositions Γ
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro a
    have fibre :
        (fun p : T => (⟨fun i => xs.get i p⟩ : Assignment M Γ)) ⁻¹' {a} =
          ⋂ i : (s : S₀) × Var Γ s, (fun p : T => xs.get i.2 p) ⁻¹' {a.get i.2} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro h i
        exact congrArg (fun b : Assignment M Γ => b.get i.2) h
      · intro h
        apply Assignment.ext
        intro s i
        exact h ⟨s, i⟩
    rw [fibre]
    exact isOpen_iInter_of_finite fun i => (xs.get i.2).isLocallyConstant _

/-- Bundling finite tuples of constant carrier sections gives a map of sheaves. -/
def constantTupleMap (M : S₀ → Type u) (Γ : List S₀) :
    sheafTuple (fun s => constantCarrier S (M s)) Γ ⟶ constantCarrier S (Assignment M Γ) :=
  ⟨{ app := fun U => ↾fun xs => bundleTuple (T := U.unop.left) xs
     naturality := by
       intro T U f
       ext xs
       rfl }⟩

/-- Membership in a native subset as a Boolean-valued function. -/
private def membership {X : Type u} (P : Set X) (x : X) : ULift.{u} Bool := by
  classical
  exact ULift.up (decide (x ∈ P))

/-- The subsheaf of constant sections valued in a native subset. -/
def constantPredicate {X : Type u} (P : Set X) : SheafPredicate (constantCarrier S X) :=
  SheafPredicate.equal (constantCarrierMap S (membership P)) (constantCarrierMap S (fun _ => ULift.up true))

/-- A section belongs to the constant predicate precisely when it does so at every point. -/
theorem mem_constantPredicate {X : Type u} (P : Set X) (U : (Over S)ᵒᵖ)
    (x : LocallyConstant U.unop.left X) :
    x ∈ (constantPredicate S P).carrier.obj U ↔ ∀ t : U.unop.left, x t ∈ P := by
  change LocallyConstant.map (membership P) x = LocallyConstant.map (fun _ : X => ULift.up true) x ↔ _
  classical
  constructor
  · intro h t
    have he := congrArg (fun g : LocallyConstant U.unop.left (ULift.{u} Bool) => (g t).down) h
    simpa [membership] using he
  · intro h
    ext t
    simp [membership, h t]

/-- Sections satisfying the constant predicate take values in its subtype. -/
def constantSubtypeMap {X : Type u} (P : Set X) :
    (constantPredicate S P).toSheaf ⟶ constantCarrier S P :=
  ⟨{ app := fun U => ↾fun x =>
       let s : LocallyConstant U.unop.left X := x.val
       LocallyConstant.desc (fun t => ⟨s t, (mem_constantPredicate S P U s).mp x.property t⟩)
         s rfl Subtype.val_injective
     naturality := by
       intro T U f
       ext x
       rfl }⟩

/-- The constant Zariski sheaf structure of a native structure, including partial domains. -/
def constantStructure {sig : Signature.{u}} (A : Structure sig) :
    SheafStructure sig (Scheme.zariskiTopology.over S) where
  carrier s := constantCarrier S (A.carrier s)
  total f := constantTupleMap S A.carrier _ ≫ constantCarrierMap S (A.total f)
  relation r := (constantPredicate S (A.relation r)).preimage (constantTupleMap S A.carrier _)
  partialDomain p := (constantPredicate S (A.partialDomain p)).preimage (constantTupleMap S A.carrier _)
  partialValue p := by
    let f := constantTupleMap S A.carrier (sig.partialArity p).inputs
    let Q := constantPredicate S (A.partialDomain p)
    exact SheafPredicate.mapAlong f (P := Q.preimage f) (Q := Q) le_rfl ≫
      constantSubtypeMap S (A.partialDomain p) ≫ constantCarrierMap S (A.partialValue p)
  quantity q := constantTupleMap S A.carrier _ ≫ constantCarrierMap S (A.quantity q)

/-- A native state is read on each test scheme as a constant section of its carrier. -/
def nativeState {X : Type u} (T : Over S) (x : X) : (constantCarrier S X).val.obj (op T) :=
  LocallyConstant.const T.left x

/-- Restricting a native state as a section preserves its constant value. -/
@[simp]
theorem nativeState_restrict {X : Type u} {T U : Over S} (f : U ⟶ T) (x : X) :
    (constantCarrier S X).val.map f.op (nativeState S T x) = nativeState S U x :=
  rfl

end SHIGURE.Copying
