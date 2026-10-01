import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteSaturation
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Executable elimination by finite elementary row and column operations

## Implementation notes

The algorithm generates only elementary matrix operations and their inverses.
It diagonalizes the input differential, independently of all right-hand sides
and candidate subsets. Mathlib's diagonalization theorem proves success of the
finite search; it does not supply the searched output or a repair.
-/

namespace AAT.AG.RelativeRepairComposition.FiniteElimination
open Matrix
universe uk un
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {n : Type un} [Fintype n] [DecidableEq n]

/-- A finite carrier is provided as an executable list covering every element. -/
structure Enumeration (A : Type*) where
  values : List A
  complete : ∀ a, a ∈ values

variable (enumK : Enumeration k) (enumN : Enumeration n)

/-- An elementary-operation state retains the matrix and its full inverse. -/
abbrev Operation (n : Type un) (k : Type uk) := Matrix n n k × Matrix n n k

/-- Composition preserves the inverse in reverse order. -/
def compose (g x : Operation n k) : Operation n k := (g.1 * x.1, x.2 * g.2)

/-- The initial operation and its inverse are both the identity. -/
def identity : Operation n k := (1,1)

/-- Finite row/column generators, including the identity for equal indices. -/
def elementary (t : n × n × k) : Operation n k :=
  if h : t.1 ≠ t.2.1 then
    let e : Matrix.TransvectionStruct n k := ⟨t.1,t.2.1,h,t.2.2⟩
    (e.toMatrix,e.inv.toMatrix)
  else identity

/-- The finite list of allowed elementary operations uses only field arithmetic. -/
def generators : List (Operation n k) :=
  enumN.values.flatMap (fun i => enumN.values.flatMap (fun j =>
    enumK.values.map (fun c => elementary (i,j,c))))

omit [Fintype k] [DecidableEq k] [Fintype n] in
/-- Every named nontrivial transvection is an available generator. -/
theorem transvection_mem (t : Matrix.TransvectionStruct n k) :
    (t.toMatrix,t.inv.toMatrix) ∈ generators enumK enumN := by
  apply List.mem_flatMap.mpr
  refine ⟨t.i,enumN.complete t.i,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨t.j,enumN.complete t.j,?_⟩
  apply List.mem_map.mpr
  refine ⟨t.c,enumK.complete t.c,?_⟩
  simp [elementary,t.hij,Matrix.TransvectionStruct.toMatrix]

/-- An operation has the specified two-sided inverse. -/
def Valid (x : Operation n k) : Prop := x.1 * x.2 = 1 ∧ x.2 * x.1 = 1

omit [Fintype k] [DecidableEq k] in
/-- The identity is valid. -/
theorem valid_identity : Valid (identity : Operation n k) := by simp [Valid,identity]

omit [Fintype k] [DecidableEq k] in
/-- Every elementary generator has its computed inverse. -/
theorem valid_elementary (t : n × n × k) : Valid (elementary t) := by
  unfold elementary
  split
  · exact ⟨Matrix.TransvectionStruct.mul_inv _,Matrix.TransvectionStruct.inv_mul _⟩
  · exact valid_identity

omit [Fintype k] [DecidableEq k] in
/-- Matrix multiplication and reverse inverse multiplication preserve validity. -/
theorem valid_compose (g x : Operation n k) (hg : Valid g) (hx : Valid x) :
    Valid (compose g x) := by
  constructor
  · change (g.1 * x.1) * (x.2 * g.2) = 1
    calc
      _ = g.1 * (x.1 * x.2) * g.2 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hx.1,Matrix.mul_one,hg.1]
  · change (x.2 * g.2) * (g.1 * x.1) = 1
    calc
      _ = x.2 * (g.2 * g.1) * x.1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg.2,Matrix.mul_one,hx.2]

/-- Compute the finite set of all elementary products and their inverses. -/
def operations : List (Operation n k) := saturate compose (generators enumK enumN) [identity]

/-- Each computed operation retains a genuine two-sided inverse. -/
theorem operations_valid {x : Operation n k} (hx : x ∈ operations enumK enumN) : Valid x := by
  apply saturate_invariant compose (generators enumK enumN) Valid _ [identity] _ x hx
  · intro g hg x hx
    rcases List.mem_flatMap.mp hg with ⟨i,_,hg⟩
    rcases List.mem_flatMap.mp hg with ⟨j,_,hg⟩
    rcases List.mem_map.mp hg with ⟨c,_,rfl⟩
    exact valid_compose _ _ (valid_elementary (i,j,c)) hx
  · intro x hx
    have he : x = identity := by simpa only [List.mem_singleton] using hx
    subst x
    exact valid_identity

omit [Fintype k] [DecidableEq k] in
/-- A finite transvection word has exactly its original product matrix. -/
theorem foldr_matrix (L : List (Matrix.TransvectionStruct n k)) :
    ((L.map (fun t => (t.toMatrix,t.inv.toMatrix))).foldr compose identity).1 =
      (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => rfl
  | cons t L ih => simpa only [List.map_cons,List.foldr_cons,List.prod_cons,compose] using (congrArg (fun a => t.toMatrix * a) ih)

/-- Every transvection word occurs in the finite computed operation set. -/
theorem word_mem_operations (L : List (Matrix.TransvectionStruct n k)) :
    (L.map (fun t => (t.toMatrix,t.inv.toMatrix))).foldr compose identity ∈ operations enumK enumN := by
  apply foldr_mem_saturate compose (generators enumK enumN) [identity] identity (List.mem_singleton_self _) _
  intro g hg
  rcases List.mem_map.mp hg with ⟨t,_,rfl⟩
  exact transvection_mem enumK enumN t

/-- Every square input reaches diagonal form using computed row and column operations. -/
theorem diagonal_exists (M : Matrix n n k) :
    ∃ p ∈ operations enumK enumN, ∃ q ∈ operations enumK enumN,
      p.1 * M * q.1 = Matrix.diagonal (fun i => (p.1 * M * q.1) i i) := by
  rcases Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L,R,d,h⟩
  refine ⟨_,word_mem_operations enumK enumN L,_,word_mem_operations enumK enumN R,?_⟩
  rw [foldr_matrix,foldr_matrix,h]
  simp

/-- Search the computed row/column operation pairs and retain their complete certificate. -/
def diagonalize (M : Matrix n n k) :
    {pq : Operation n k × Operation n k //
      pq.1 ∈ operations enumK enumN ∧ pq.2 ∈ operations enumK enumN ∧
      pq.1.1 * M * pq.2.1 = Matrix.diagonal (fun i => (pq.1.1 * M * pq.2.1) i i)} := by
  let candidates := (operations enumK enumN).flatMap (fun p => (operations enumK enumN).map (fun q => (p,q)))
  let found := candidates.find? fun pq => decide
    (pq.1.1 * M * pq.2.1 = Matrix.diagonal (fun i => (pq.1.1 * M * pq.2.1) i i))
  have hf : found.isSome = true := by
    rw [List.find?_isSome]
    rcases diagonal_exists enumK enumN M with ⟨p,hp,q,hq,hpq⟩
    exact ⟨(p,q),by simp [candidates,hp,hq],by simpa using hpq⟩
  refine ⟨found.get hf,?_⟩
  have hs := List.find?_some (Option.some_get hf).symm
  have hm := List.mem_of_find?_eq_some (Option.some_get hf).symm
  have hc : (found.get hf).1 ∈ operations enumK enumN ∧ (found.get hf).2 ∈ operations enumK enumN := by
    rcases List.mem_flatMap.mp hm with ⟨p,hp,hq⟩
    rcases List.mem_map.mp hq with ⟨q,hq,hpq⟩
    rw [← hpq]
    exact ⟨hp,hq⟩
  exact ⟨hc.1,hc.2,by simpa [found] using hs⟩

/-- Complete row/column reduction data, generated by the finite algorithm. -/
structure Reduction (M : Matrix n n k) where
  row : Matrix n n k
  rowInv : Matrix n n k
  column : Matrix n n k
  columnInv : Matrix n n k
  value : n → k
  row_inverse : Valid (row,rowInv)
  column_inverse : Valid (column,columnInv)
  diagonal_eq : row * M * column = Matrix.diagonal value

/-- Build every reduction field from the executable searched operations. -/
def reduce (M : Matrix n n k) : Reduction M :=
  let pq := diagonalize enumK enumN M
  { row := pq.1.1.1
    rowInv := pq.1.1.2
    column := pq.1.2.1
    columnInv := pq.1.2.2
    value := fun i => (pq.1.1.1 * M * pq.1.2.1) i i
    row_inverse := operations_valid enumK enumN pq.2.1
    column_inverse := operations_valid enumK enumN pq.2.2.1
    diagonal_eq := pq.2.2.2 }

omit [Fintype k] [DecidableEq k] in
/-- A diagonal scalar matrix has its coordinatewise generalized inverse. -/
theorem diagonal_regular (d : n → k) :
    Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = Matrix.diagonal d := by
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : d i = 0
  · simp [hi]
  · simp [hi]

/-- The linear section matrix is computed from the reduction, with zero at zero pivots. -/
def sectionMatrix (M : Matrix n n k) : Matrix n n k :=
  let R := reduce enumK enumN M
  R.column * Matrix.diagonal (fun i => (R.value i)⁻¹) * R.row

/-- The generated section is a right inverse on the entire image of the input matrix. -/
theorem sectionMatrix_regular (M : Matrix n n k) :
    M * sectionMatrix enumK enumN M * M = M := by
  let R := reduce enumK enumN M
  have h : R.row * (M * sectionMatrix enumK enumN M * M) * R.column =
      R.row * M * R.column := by
    calc
      _ = (R.row * M * R.column) * Matrix.diagonal (fun i => (R.value i)⁻¹) *
          (R.row * M * R.column) := by
            change R.row * (M * (R.column * Matrix.diagonal (fun i => (R.value i)⁻¹) * R.row) * M) * R.column = _
            simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal R.value := by rw [R.diagonal_eq,diagonal_regular]
      _ = _ := R.diagonal_eq.symm
  have h' := congrArg (fun X => R.rowInv * X * R.columnInv) h
  have hr : R.rowInv * R.row = 1 := R.row_inverse.2
  have hc : R.column * R.columnInv = 1 := R.column_inverse.1
  have hh : (R.rowInv * R.row) * (M * sectionMatrix enumK enumN M * M) * (R.column * R.columnInv) =
      (R.rowInv * R.row) * M * (R.column * R.columnInv) := by
    simpa only [Matrix.mul_assoc] using h'
  simpa only [hr,hc,Matrix.one_mul,Matrix.mul_one] using hh

omit [Fintype k] [DecidableEq k] in
/-- The validity predicate exposes exactly both full inverse equations. -/
theorem mem_valid (x : Operation n k) : Valid x ↔ x.1 * x.2 = 1 ∧ x.2 * x.1 = 1 := Iff.rfl

omit [Fintype k] [DecidableEq k] in
/-- Zero matrices on a nonempty coordinate set fail the inverse predicate. -/
theorem not_valid_zero [Nonempty n] : ¬ Valid ((0,0) : Operation n k) := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty n›
  have hh : (0 : k) = 1 := by
    simpa using congrArg (fun X : Matrix n n k => X i i) h.1
  exact zero_ne_one hh

variable {m : Type un} [Fintype m] [DecidableEq m]
variable (enumM : Enumeration m)

/-- Concatenated coordinate lists cover the square extension without changing original indices. -/
def sumEnumeration : Enumeration (m ⊕ n) where
  values := enumM.values.map Sum.inl ++ enumN.values.map Sum.inr
  complete a := by cases a <;> simp [enumM.complete,enumN.complete]

/-- Extend the rectangular differential by zero blocks, retaining its original entries. -/
def squareExtension (D : Matrix m n k) : Matrix (m ⊕ n) (m ⊕ n) k :=
  Matrix.fromBlocks 0 D 0 0

/-- Extract a computable rectangular section from the square reduction. -/
def rectangularSection (D : Matrix m n k) : Matrix n m k :=
  Matrix.toBlocks₂₁ (sectionMatrix enumK (sumEnumeration enumN enumM) (squareExtension D))

/-- The extracted section is a right inverse on the complete original image. -/
theorem rectangularSection_regular (D : Matrix m n k) :
    D * rectangularSection enumK enumN enumM D * D = D := by
  let S := sectionMatrix enumK (sumEnumeration enumN enumM) (squareExtension D)
  have h := sectionMatrix_regular enumK (sumEnumeration enumN enumM) (squareExtension D)
  change squareExtension D * S * squareExtension D = squareExtension D at h
  rw [← Matrix.fromBlocks_toBlocks S] at h
  have hh := congrArg Matrix.toBlocks₁₂ h
  simpa only [squareExtension,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,
    zero_add,add_zero,Matrix.toBlocks_fromBlocks₁₂] using hh

end AAT.AG.RelativeRepairComposition.FiniteElimination

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
