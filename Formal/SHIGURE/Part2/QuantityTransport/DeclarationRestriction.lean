import Formal.SHIGURE.Part1.SelectedPresentation
import Formal.SHIGURE.Part2.QuantityTransport.Coefficients
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Declaration restriction of quantity Laws

The retained state structure is the restriction along the given
declaration names. A retained equation uses the same coordinate
expression, with each named quantity now indexed by the retained
declarations. The comparison uses the actual quotient maps from §5.4.

## Implementation notes

The domain and Law input types are kept for each retained name.
Traversing the expressions with their support proofs produces the
reindexed sides. This gives equation preservation from the declaration
selection, without requiring a new equality supplied for each Law.
-/

open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.Quantities.Expression

variable {k L M : Type u}

/-- All quantity leaves of the expression use retained declarations. -/
def UsesOnly (keep : L → Prop) : Expression k L → Prop
  | .scalar _ => True
  | .quantity x => keep x
  | .add l r | .mul l r => UsesOnly keep l ∧ UsesOnly keep r
  | .neg t => UsesOnly keep t

/-- Reindex the same expression by the retained declarations. -/
def select (keep : L → Prop) (choose : ∀ x, keep x → M) :
    (t : Expression k L) → t.UsesOnly keep → Expression k M
  | .scalar a, _ => .scalar a
  | .quantity x, h => .quantity (choose x h)
  | .add l r, h => .add (select keep choose l h.1) (select keep choose r h.2)
  | .mul l r, h => .mul (select keep choose l h.1) (select keep choose r h.2)
  | .neg t, h => .neg (select keep choose t h)

/-- Including the retained quantity names into the full list recovers the original expression. -/
theorem rename_select (keep : L → Prop) (choose : ∀ x, keep x → M) (intoFull : M → L)
    (same : ∀ x h, intoFull (choose x h) = x) (t : Expression k L) (h : t.UsesOnly keep) :
    (select keep choose t h).rename intoFull = t := by
  induction t <;> simp [select, rename, *]

end SHIGURE.Quantities.Expression

namespace SHIGURE.Quantities

variable {k : Type u} [CommRing k] {S T : Signature.{u}}
variable {A : Structure T} (P : Presentation k A)
variable (names : SignatureNames S T) (Q : Set P.Quantity) (L : Set P.Law)

/-- Every selected Law retains the quantities used on both sides at all its inputs. -/
def RetainsLawQuantities : Prop :=
  ∀ (l : L) (e : P.Input l.val),
    (P.left l.val e).UsesOnly (fun x => x.1 ∈ Q) ∧
      (P.right l.val e).UsesOnly (fun x => x.1 ∈ Q)

variable (h : RetainsLawQuantities P Q L)

/-- Restrict the state declarations and keep the prescribed quantity and Law names. -/
def restrictQuantityDeclarations : Presentation k (names.restrict A) where
  Quantity := Q
  Domain j := P.Domain j.val
  Law := L
  Input l := P.Input l.val
  left l e := (P.left l.val e).select (fun x => x.1 ∈ Q) (fun x hx => ⟨⟨x.1, hx⟩, x.2⟩) (h l e).1
  right l e := (P.right l.val e).select (fun x => x.1 ∈ Q) (fun x hx => ⟨⟨x.1, hx⟩, x.2⟩) (h l e).2

/-- The comparison of Law algebras for declaration restriction uses the inclusion of
the retained quantity variables and the same equation at each retained input. -/
def declarationLawMap : LawMap (restrictQuantityDeclarations P names Q L h) P where
  name := Subtype.val
  argument _ := id
  law := Subtype.val
  input _ := id
  left l e := Expression.rename_select _ _ _ (fun _ _ => rfl) (P.left l.val e) (h l e).1
  right l e := Expression.rename_select _ _ _ (fun _ _ => rfl) (P.right l.val e) (h l e).2

/-- The declaration restriction map on Law algebras commutes with change to every coefficient algebra. -/
theorem declarationLawMap_baseChange (R : Type u) [CommRing R] [Algebra k R] :
    let F := restrictQuantityDeclarations P names Q L h
    let ι := declarationLawMap P names Q L h
    (baseChangeQuotient (R := k) R P.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  (declarationLawMap P names Q L h).extendedEquationMap_natural R

/-- The same square for the coefficient restriction to the principal open of `r`. -/
theorem declarationLawMap_localization (r : k) :
    let R := Localization.Away r
    let F := restrictQuantityDeclarations P names Q L h
    let ι := declarationLawMap P names Q L h
    (baseChangeQuotient (R := k) R P.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  declarationLawMap_baseChange P names Q L h (Localization.Away r)

end SHIGURE.Quantities
