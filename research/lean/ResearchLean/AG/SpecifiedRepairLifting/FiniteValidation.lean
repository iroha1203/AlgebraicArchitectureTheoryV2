import ResearchLean.AG.SpecifiedRepairLifting.FiniteRepresentation

/-! # 原始有限検査の成立例と拒否例

Implementation notes: ここはcycle 8の検査用入力だけをまとめるnamespaceであり、
主定理の構成に使うspineではない。各条件の正負を原始整数表から評価し、
指定Wの同時成立をこの検査例だけで達成したとは扱わない。
-/
namespace AAT.AG.SpecifiedRepairLifting.FiniteValidation
open IntegerElimination PresentedGroups PresentedComplex PresentedProduct FiniteLifting FiniteRepresentation
/-- 検査用の自由整数群表示。 -/
def free (n : ℕ) : Presentation := ⟨n,0,0⟩
/-- 検査用の一生成元一関係表示。 -/
def cyclic (k : ℤ) : Presentation := ⟨1,1,!![k]⟩
/-- 非零d¹を持つ0→Z/4→Z/2という検査用複体。 -/
def torsionComplex : ComplexData := ⟨free 0,cyclic 4,cyclic 2,0,!![1]⟩
/-- 検査用複体の原始恒等比較。 -/
def identityData (C : ComplexData) : ComparisonData C C := ⟨1,1,1⟩
/-- 検査用複体の原始零比較。 -/
def zeroData (C D : ComplexData) : ComparisonData C D := ⟨0,0,0⟩
/-- 非零d⁰を持つ検査用複体。 -/
def firstComplex : ComplexData := ⟨free 1,free 1,free 0,!![1],0⟩
/-- 非零d¹を持つ自由群の検査用複体。 -/
def secondComplex : ComplexData := ⟨free 0,free 1,free 1,0,!![1]⟩

#eval decide (ZeroColumns (cyclic 4) !![4])
#eval decide (¬ ZeroColumns (cyclic 4) !![1])
#eval decide (ComplexValid torsionComplex)
#eval decide (¬ ComplexValid (⟨free 1,free 1,free 1,!![1],!![1]⟩ : ComplexData))
#eval decide (¬ ComplexValid (⟨cyclic 2,cyclic 4,free 0,!![1],0⟩ : ComplexData))
#eval decide (ComparisonValid (identityData torsionComplex))
#eval decide (¬ ComparisonValid (⟨!![0],!![1],0⟩ : ComparisonData firstComplex firstComplex))
#eval decide (¬ ComparisonValid (⟨0,!![1],!![0]⟩ : ComparisonData secondComplex secondComplex))
#eval checkInput torsionComplex torsionComplex (identityData torsionComplex) 0 0
#eval !(checkInput torsionComplex torsionComplex (zeroData _ _) ![1] 0)
#eval !(checkInput torsionComplex torsionComplex (identityData torsionComplex) ![2] 0)
#eval decide (InverseValid (identityData torsionComplex) (identityData torsionComplex))
#eval decide (¬ InverseValid (identityData torsionComplex) (zeroData _ _))
#eval decide (IsoValid (⟨identityData torsionComplex,identityData torsionComplex⟩ : IsoData torsionComplex torsionComplex))
#eval decide (¬ IsoValid (⟨identityData torsionComplex,zeroData _ _⟩ : IsoData torsionComplex torsionComplex))
#eval decide (SquareValid (identityData torsionComplex) (identityData torsionComplex)
  (identityData torsionComplex) (identityData torsionComplex))
#eval decide (¬ SquareValid (identityData torsionComplex) (identityData torsionComplex)
  (zeroData _ _) (identityData torsionComplex))
#eval match finiteSolve torsionComplex torsionComplex (identityData torsionComplex) 0 0 with
  | .inl _ => true
  | .inr _ => false
#eval finiteUnique torsionComplex torsionComplex (identityData torsionComplex) 0 0
#eval match finiteSolve firstComplex firstComplex (identityData firstComplex) ![1] ![1] with
  | .inl x => x ⟨0,by decide⟩ == 1
  | .inr _ => false
#eval finiteUnique firstComplex firstComplex (identityData firstComplex) ![1] ![1]

#eval (checkedSolve torsionComplex torsionComplex (zeroData _ _) ![1] 0).isNone
#eval (checkedSolve torsionComplex torsionComplex (identityData torsionComplex) 0 0).isSome

end AAT.AG.SpecifiedRepairLifting.FiniteValidation

#print axioms AAT.AG.SpecifiedRepairLifting.FiniteValidation.free
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteValidation.cyclic
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteValidation.torsionComplex
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteValidation.identityData
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteValidation.zeroData
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteValidation.firstComplex
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteValidation.secondComplex
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.FiniteValidation
