import Formal.SHIGURE.Part1.ContextDerivedExample
import Formal.SHIGURE.Part1.ContextSelectedCategories

/-! # The omitted constant and its selected model

Forgetting a nullary operation permits an empty carrier. The selected
signature has no name for the omitted operation, and its ordinary model
category contains this empty-carrier structure.
-/

namespace SHIGURE.Chapter3.DerivedNonempty

open DeclarationContext

/-- Keep only the sort and omit the original total constant and the derived Law. -/
def sortOnly : ChapterContext presentation where
  declarations := {Declaration.sort ()}
  closed kept := by
    have h := Set.mem_singleton_iff.mp kept
    subst h
    exact Set.empty_subset _

/-- In the ordinary restriction, there is no remaining operation with a forced value. -/
instance sortOnly_noTotal : IsEmpty sortOnly.restrict.signature.Total := ⟨fun f => by
  have kept : Declaration.total f.val ∈ sortOnly.declarations := f.property
  simp [sortOnly] at kept⟩

/-- The sort remains a typed declaration even when its carrier has no points. -/
def selectedSort : sortOnly.restrict.signature.SortType := ⟨(), Set.mem_singleton _⟩

/-- The selected signature can give the retained sort the empty carrier. -/
def emptyStructure : Structure sortOnly.restrict.signature where
  carrier _ := Empty
  total f := isEmptyElim f
  relation r := nomatch r.val
  partialDomain p := nomatch p.val
  partialValue p := nomatch p.val
  quantity q := nomatch q.val

/-- The empty-carrier interpretation is a model of the actual restricted theory. -/
def emptyModel : ChapterContext.Models sortOnly :=
  ⟨emptyStructure, fun name => by
    have kept : Declaration.law name.val.val ∈ sortOnly.declarations := name.val.property
    simp [sortOnly] at kept⟩

/-- The ordinary model really allows an empty carrier at the retained sort. -/
theorem emptyModel_carrier : emptyModel.obj.carrier selectedSort = Empty :=
  rfl

/-- Keeping the derived Law produces an ordinary selected derivation in the smaller signature. -/
noncomputable def actualRetainedProof (U : ChapterContext presentation)
    (kept : Declaration.law () ∈ U.declarations) :
    let name : U.restrict.laws.LawName := ⟨(), kept⟩
    Derivation U.restrict.theory (U.restrict.laws.statement name).input (U.restrict.laws.statement name).conclusion :=
  U.restrict.derived ⟨(), kept⟩ rfl

end SHIGURE.Chapter3.DerivedNonempty
