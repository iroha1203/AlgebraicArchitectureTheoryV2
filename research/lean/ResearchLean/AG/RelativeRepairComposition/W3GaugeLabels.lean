import ResearchLean.AG.RelativeRepairComposition.W3ActualRepairs

/-!
# W3's complete original vertex labels and fixed-vector group

Labels are all original translation vectors at s,t. Empty permission keeps
both actual reference edges and therefore imposes b_t=b_s=T b_t; it does
not fix either physical vertex or identify labels by their action effects.
-/
namespace AAT.AG.RelativeRepairComposition.W3GaugeLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs

/-- Complete actual labels under the original physical and forbidden-edge conditions. -/
abbrev GlobalLabels (sheared : Bool) (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.gaugeLabels geometry (reference sheared) fixedRegion.vertices (fixedEdges S)

/-- Every unrestricted pair of original vertex vectors is a full actual gauge label. -/
def unrestrictedLabel (sheared : Bool) (bs bt : A) : GlobalLabels sheared candidates :=
  ⟨fun v => if (v : Fin 2).val = 0 then bs else bt, by
    constructor
    · intro v hv; exact hv.elim
    · intro e he; rw [fixed_all] at he; exact he.elim⟩

/-- The constructed label keeps its complete original source vector. -/
theorem unrestricted_source (sheared : Bool) (bs bt : A) :
    (unrestrictedLabel sheared bs bt).1 vertexS = bs := rfl

/-- The constructed label keeps its complete original target vector. -/
theorem unrestricted_target (sheared : Bool) (bs bt : A) :
    (unrestrictedLabel sheared bs bt).1 vertexT = bt := rfl

/-- All unrestricted actual labels and the entire A² have additive inverse coordinates. -/
def unrestrictedLabelEquiv (sheared : Bool) : GlobalLabels sheared candidates ≃+ (A × A) where
  toFun b := ⟨b.1 vertexS, b.1 vertexT⟩
  invFun b := unrestrictedLabel sheared b.1 b.2
  left_inv b := by
    apply Subtype.ext
    funext v
    fin_cases v <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Forbidden e retains equality of the two entire original labels. -/
theorem empty_forward (sheared : Bool) (b : GlobalLabels sheared ∅) :
    b.1 vertexT = b.1 vertexS := by
  have h := b.2.2 (name edgeE) (by rw [fixed_empty]; exact Set.mem_univ _)
  exact h

/-- Forbidden f retains the actual full original transport T. -/
theorem empty_return (sheared : Bool) (b : GlobalLabels sheared ∅) :
    b.1 vertexS = linearAction sheared (b.1 vertexT) := by
  have h := b.2.2 (name edgeF) (by rw [fixed_empty]; exact Set.mem_univ _)
  exact h

/-- The entire fixed-vector subgroup of the original loop action. -/
def FixedVectors (sheared : Bool) : AddSubgroup A where
  carrier := {a | linearAction sheared a = a}
  zero_mem' := (linearAction sheared).map_zero
  add_mem' := by intro a b ha hb; change linearAction sheared (a+b)=a+b; rw [map_add,ha,hb]
  neg_mem' := by intro a ha; change linearAction sheared (-a) = -a; rw [map_neg,ha]

/-- Every full fixed vector labels both original vertices without any quotient. -/
def emptyLabel (sheared : Bool) (a : FixedVectors sheared) : GlobalLabels sheared ∅ :=
  ⟨fun _ => a.1, by
    constructor
    · intro v hv; exact hv.elim
    · intro e he
      rcases e with ⟨i,j,e,hs,ht⟩
      cases hs
      cases ht
      fin_cases e
      · rfl
      · exact a.2.symm⟩

/-- Empty-permission full labels and the whole fixed-vector group have both additive inverses. -/
def emptyLabelEquiv (sheared : Bool) : GlobalLabels sheared ∅ ≃+ FixedVectors sheared where
  toFun b := ⟨b.1 vertexS, by
    calc
      linearAction sheared (b.1 vertexS) = linearAction sheared (b.1 vertexT) :=
        congrArg (linearAction sheared) (empty_forward sheared b).symm
      _ = b.1 vertexS := (empty_return sheared b).symm⟩
  invFun a := emptyLabel sheared a
  left_inv b := by
    apply Subtype.ext
    funext v
    fin_cases v
    · rfl
    · exact (empty_forward sheared b).symm
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Restoring a fixed vector keeps it at every original vertex. -/
theorem emptyLabelEquiv_inverse_value (sheared : Bool) (a : FixedVectors sheared)
    (v : geometry.Vertex) : ((emptyLabelEquiv sheared).symm a).1 v = a.1 := rfl

/-- Every actual shear fixed vector has precisely its entire first coordinate free. -/
def shearFixedEquiv : FixedVectors true ≃+ ZMod 3 where
  toFun a := a.1 0
  invFun x := ⟨fun i => if i = 0 then x else 0,
    (shear_fixed_iff _).mpr rfl⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · exact ((shear_fixed_iff a.1).mp a.2).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The identity fixes the entire same original vector space. -/
def identityFixedEquiv : FixedVectors false ≃+ A where
  toFun a := a.1
  invFun a := ⟨a,rfl⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end AAT.AG.RelativeRepairComposition.W3GaugeLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3GaugeLabels
