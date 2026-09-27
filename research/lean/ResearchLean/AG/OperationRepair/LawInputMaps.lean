import ResearchLean.AG.OperationRepair.PathBridge

/-!
# Input maps for independently specified Law evaluations

The two inputs share Law names and value types but may have different
evaluations. Pointwise preservation of every Law, together with operation
commutation, gives C's input map for the path-generated requests.
-/

namespace AAT.AG.OperationRepair

open AAT.AG.CanonicalResolution

universe u v

variable {S S₂ : Type u} {E : Type v}

/-- Build an existing finite Law family from independently supplied
evaluations with a shared finite index and shared value types. -/
def indexedLaws (Source : Type u) (L : Type u)
    (lawFintype : Fintype L) (Value : L → Type u)
    (valueDecidableEq : ∀ law, DecidableEq (Value law))
    (eval : (law : L) → Source → Value law) : FiniteLawFamily Source where
  Law := L
  lawFintype := lawFintype
  Value := Value
  valueDecidableEq := valueDecidableEq
  eval := eval

/-- C's input morphism for two independently given Law evaluations and the
same finite path-pair list. Neither source map injectivity nor surjectivity
is required. -/
def independentLawPathInputHom
    (L : Type u) (lawFintype : Fintype L)
    (Value : L → Type u)
    (valueDecidableEq : ∀ law, DecidableEq (Value law))
    (eval : (law : L) → S → Value law)
    (eval₂ : (law : L) → S₂ → Value law)
    (T : OperationSystem S E) (T₂ : OperationSystem S₂ E)
    (paths : List (List E × List E)) (map : S → S₂)
    (hstep : ∀ e x, map (T.step e x) = T₂.step e (map x))
    (hlaw : ∀ law x, eval₂ law (map x) = eval law x) :
    InputHom T
      (lawObserve (indexedLaws S L lawFintype Value valueDecidableEq eval))
      (pathRequest T paths) T₂
      (lawObserve (indexedLaws S₂ L lawFintype Value valueDecidableEq eval₂))
      (pathRequest T₂ paths) :=
  pathInputHom T T₂
    (lawObserve (indexedLaws S L lawFintype Value valueDecidableEq eval))
    (lawObserve (indexedLaws S₂ L lawFintype Value valueDecidableEq eval₂))
    paths map hstep (by
      intro x
      funext law
      exact hlaw law x)

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
