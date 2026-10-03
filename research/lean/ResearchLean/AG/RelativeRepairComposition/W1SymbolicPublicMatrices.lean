import ResearchLean.AG.RelativeRepairComposition.W1SymbolicPublicStructure

/-! # The same complete original W1 public matrix for every symbolic x,y input
## Implementation notes

Structural coordinates retain all original public names and their complete
basis indices. Each actual F entry is proved equal to the original law's
coefficient on that same column. The common matrix is thus derived from every
actual input, rather than defining the actual matrices from a chosen output.
A comparison after a quotient would omit the required full public matrix.
-/
namespace AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalInterfaces W1SymbolicPublicStructure
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

/-- The entire original face coordinate family, with its complete basis component. -/
abbrev faceIndex (j : Bool) := Σ _f : {f : Bool // f ∈ (regions j).faces ∧ f ∉ fixedRegion.faces}, Fin 1

/-- The entire original edge coordinate family, with its complete basis component. -/
abbrev edgeIndex (j : Bool) := Σ _e : {e : EdgeName (K := geometry) // e ∈ (regions j).edges ∧ e ∉ fixedRegion.edges}, Fin 1

/-- Every original public coordinate retains its original nonprivate edge name. -/
abbrev publicIndex (j : Bool) := {e : edgeIndex j // e.1.1 ∉ ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j}

/-- The actual full F matrix read on the complete structural coordinates. -/
noncomputable def structuralPublicMatrix (x y : ZMod 3) (j : Bool) :
    Matrix (faceIndex j) (publicIndex j) (ZMod 3) := publicMatrix x y j

/-- A retained public name with the full sole basis component, independent of values. -/
def namedPublicIndex (j : Bool) (e : (regions j).edges)
    (hp : e.1 ∉ fixedRegion.edges)
    (hi : e.1 ∉ ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j) : publicIndex j :=
  ⟨⟨⟨e.1,e.2,hp⟩,0⟩,hi⟩

/-- The shared always edge remains public in both original patches. -/
def structuralE (j : Bool) : publicIndex j :=
  namedPublicIndex j ⟨name edgeE, by cases j <;> exact Or.inl rfl⟩
    (by simp [fixedRegion, geometry, name, edgeE, edgeRx, edgeRy]) (shared_e_public j)

/-- The full original b candidate coordinate remains public in both patches. -/
def structuralB (j : Bool) : publicIndex j :=
  namedPublicIndex j ⟨name edgeB, by cases j; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inl rfl))⟩
    (by simp [fixedRegion, geometry, name, edgeB, edgeRx, edgeRy])
    (candidates_public j ⟨name edgeB, Or.inl rfl⟩)

/-- The original c candidate coordinate remains public in V. -/
def structuralC : publicIndex true :=
  namedPublicIndex true ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    (by simp [fixedRegion, geometry, name, edgeC, edgeRx, edgeRy])
    (candidates_public true ⟨name edgeC, Or.inr rfl⟩)

/-- The complete public matrix of the two original laws on every original column. -/
noncomputable def commonPublicMatrix (j : Bool) : Matrix (faceIndex j) (publicIndex j) (ZMod 3) :=
  match j with
  | false => fun _ e => let z : publicIndex false → ZMod 3 := Pi.single e 1; z (structuralE false) + z (structuralB false)
  | true => fun _ e => let z : publicIndex true → ZMod 3 := Pi.single e 1; z (structuralE true) - z (structuralB true) + z structuralC

/-- The actual full public matrix equals the same complete matrix for every symbolic input. -/
theorem public_matrix_eq_common (x y : ZMod 3) (j : Bool) :
    structuralPublicMatrix x y j = commonPublicMatrix j := by
  funext i e
  change FiniteNative.F (originalTower true x y).toTower.localCoefficients (bases true x y)
      (regions j) fixedRegion (ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j)
      (original_linear true x y) (Pi.single e 1) i = commonPublicMatrix j i e
  rcases i with ⟨⟨f,hf,hp⟩,n⟩
  cases j
  · have h : (f : Bool) = false := hf
    subst f
    change Fin 1 at n
    have hn : n = basisIndex true x y () := Subsingleton.elim _ _
    subst n
    rw [left_public x y]
    rfl
  · have h : (f : Bool) = true := hf
    subst f
    change Fin 1 at n
    have hn : n = basisIndex true x y () := Subsingleton.elim _ _
    subst n
    rw [right_public x y]
    rfl

/-- Every original entry of the actual public matrix is reused unchanged across all input values. -/
theorem public_matrix_same (x y : ZMod 3) (j : Bool) :
    structuralPublicMatrix x y j = structuralPublicMatrix 0 0 j :=
  (public_matrix_eq_common x y j).trans (public_matrix_eq_common 0 0 j).symm

end AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices
