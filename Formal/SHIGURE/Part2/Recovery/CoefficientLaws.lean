import Formal.SHIGURE.Part2.Realizations.ZariskiModels

/-!
# Base change of the Zariski interpretation

The relative Zariski topology tests covering on the underlying scheme.
Changing the map to the base keeps both these coverings and the
underlying sections. Thus existential witnesses and disjunctions
continue to use exactly the same local test objects.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S S' : Scheme.{u}} {sig : Signature.{u}}
variable (f : S' ⟶ S)

/-- The same underlying covering sieve compares the two relative sites on a fixed test object. -/
private theorem relativeCover_map_iff {T : Over S'} {P : Sieve T} {Q : Sieve ((Over.map f).obj T)}
    (h : ∀ {U : Over S'} (g : U ⟶ T), P g ↔ Q ((Over.map f).map g)) :
    P ∈ (Scheme.zariskiTopology.over S') T ↔ Q ∈ (Scheme.zariskiTopology.over S) ((Over.map f).obj T) := by
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff]
  have heq : Sieve.overEquiv T P = Sieve.overEquiv ((Over.map f).obj T) Q := by
    ext V g
    rw [Sieve.overEquiv_iff]
    let g' : Over.mk (g ≫ T.hom) ⟶ T := Over.homMk g
    exact (h g').trans (by
      have he := Sieve.overEquiv_symm_iff (Sieve.overEquiv ((Over.map f).obj T) Q) ((Over.map f).map g')
      rw [Equiv.symm_apply_apply] at he
      exact he)
  rw [heq]
  rfl

/-- The atomic interpretation commutes with coefficient restriction on every test. -/
theorem mem_restrictAtom_iff (A : SheafStructure sig (Scheme.zariskiTopology.over S))
    {Γ : List sig.SortType} (p : Atomic sig Γ) (T : Over S')
    (a : (sheafTuple (restrictStructure f A).carrier Γ).val.obj (op T)) :
    a ∈ ((restrictStructure f A).interpretAtom p).carrier.obj (op T) ↔
      a ∈ (A.interpretAtom p).carrier.obj (op ((Over.map f).obj T)) := by
  cases p with
  | eq _ _ => rfl
  | rel _ _ => rfl
  | domain _ _ => rfl
  | graph op args y =>
    cases op with
    | total _ => rfl
    | quantity _ => rfl
    | partialOp p =>
      have h₁ := SheafStructure.mem_partialGraph_iff (restrictStructure f A) p args y (Opposite.op T) a
      have h₂ := SheafStructure.mem_partialGraph_iff A p args y (Opposite.op ((Over.map f).obj T)) a
      exact h₁.trans h₂.symm

/-- Positive formulas commute with coefficient restriction, including the local witnesses. -/
theorem mem_restrictFormula_iff (A : SheafStructure sig (Scheme.zariskiTopology.over S))
    {Γ : List sig.SortType} (p : Formula sig Γ) (T : Over S')
    (a : (sheafTuple (restrictStructure f A).carrier Γ).val.obj (op T)) :
    a ∈ ((restrictStructure f A).interpretFormula p).carrier.obj (op T) ↔
      a ∈ (A.interpretFormula p).carrier.obj (op ((Over.map f).obj T)) := by
  induction p generalizing T with
  | atom p => exact mem_restrictAtom_iff f A p T a
  | truth => exact ⟨fun _ => SheafPredicate.mem_truth _ _, fun _ => SheafPredicate.mem_truth _ _⟩
  | falsehood =>
    simp only [SheafStructure.interpretFormula, SheafPredicate.falsehood, SheafPredicate.mem_ofLocal_iff]
    exact relativeCover_map_iff f (fun _ => Iff.rfl)
  | conj p q hp hq =>
    simp only [SheafStructure.interpretFormula, SheafPredicate.mem_conj_iff]
    exact and_congr (hp T a) (hq T a)
  | disj p q hp hq =>
    simp only [SheafStructure.interpretFormula, SheafPredicate.mem_disj_iff]
    apply relativeCover_map_iff f
    intro U g
    exact or_congr (hp U ((sheafTuple (restrictStructure f A).carrier _).val.map g.op a))
      (hq U ((sheafTuple (restrictStructure f A).carrier _).val.map g.op a))
  | @ex Γ s p ih =>
    simp only [SheafStructure.interpretFormula, SheafPredicate.mem_existsAlong_iff]
    apply relativeCover_map_iff f
    intro U g
    constructor
    · rintro ⟨⟨b, hb⟩, he⟩
      exact ⟨⟨b, (ih U b).mp hb⟩, he⟩
    · rintro ⟨⟨b, hb⟩, he⟩
      exact ⟨⟨b, (ih U b).mpr hb⟩, he⟩

/-- Any coefficient restriction preserves each Law in the actual sheaf interpretation. -/
theorem restrictStructure_holdsLaw (A : SheafStructure sig (Scheme.zariskiTopology.over S))
    (law : Law sig) (h : A.holdsLaw law) : (restrictStructure f A).holdsLaw law := by
  intro U a ha
  exact (mem_restrictFormula_iff f A law.conclusion U.unop a).mpr
    (h (op ((Over.map f).obj U.unop)) ((mem_restrictFormula_iff f A law.input U.unop a).mp ha))

end SHIGURE.Copying
