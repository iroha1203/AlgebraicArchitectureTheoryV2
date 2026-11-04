import ResearchLean.AG.SpecifiedRepairLifting.PresentedGroups

/-! # 二つの元有限表示の直積

Implementation notes: 二つの関係行列をブロック対角に置き、元の二商との
線形同型を代表評価で構成する。これにより二つの補正式を同時に課す射を
一つの有限表示射へ接続する。新しい同値関係を供給せず、入力関係の直積を使う。
-/
namespace AAT.AG.SpecifiedRepairLifting.PresentedProduct
open Matrix IntegerElimination PresentedGroups
/-- 自由座標の後半への整数線形射。 -/
def secondMap (n r : ℕ) : Vec (n+r) →ₗ[ℤ] Vec r where
  toFun := second
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 二原始行列をブロック対角に並べる。 -/
def blockMatrix {m n r s : ℕ} (A : Mat m r) (B : Mat n s) : Mat (m+n) (r+s) :=
  Fin.addCases (fun i => Fin.addCases (A i) (fun _ => 0))
    (fun i => Fin.addCases (fun _ => 0) (B i))
/-- ブロック対角行列の前半の評価。 -/
theorem blockMatrix_first {m n r s : ℕ} (A : Mat m r) (B : Mat n s) (x : Vec (r+s)) :
    first (blockMatrix A B *ᵥ x) = A *ᵥ first x := by
  ext i
  simp [first,blockMatrix,mulVec,dotProduct,Fin.sum_univ_add]
/-- ブロック対角行列の後半の評価。 -/
theorem blockMatrix_second {m n r s : ℕ} (A : Mat m r) (B : Mat n s) (x : Vec (r+s)) :
    second (blockMatrix A B *ᵥ x) = B *ᵥ second x := by
  ext i
  simp [second,blockMatrix,mulVec,dotProduct,Fin.sum_univ_add]
/-- 元関係行列の直積表示。 -/
def product (P Q : Presentation) : Presentation :=
  ⟨P.generators+Q.generators,P.relations+Q.relations,blockMatrix P.matrix Q.matrix⟩
/-- 原始直積座標を二つの元商へ送る。 -/
def pairClass (P Q : Presentation) : Vec (P.generators+Q.generators) →ₗ[ℤ]
    PresentedGroups.Group P × PresentedGroups.Group Q :=
  ((quotientClass P).comp (firstMap _ _)).prod ((quotientClass Q).comp (secondMap _ _))
/-- 直積座標の代表評価。 -/
theorem pairClass_apply (P Q : Presentation) (x : Vec (P.generators+Q.generators)) :
    pairClass P Q x = (quotientClass P (first x),quotientClass Q (second x)) := rfl
/-- 原始直積関係は二つの元商で零となる。 -/
theorem pairClass_relations (P Q : Presentation) : relationSpace (product P Q) ≤
    LinearMap.ker (pairClass P Q) := by
  rintro x ⟨u,rfl⟩
  apply Prod.ext
  · change quotientClass P (first (blockMatrix P.matrix Q.matrix *ᵥ u)) = 0
    rw [blockMatrix_first]
    exact (class_zero_iff P _).mpr ⟨first u,rfl⟩
  · change quotientClass Q (second (blockMatrix P.matrix Q.matrix *ᵥ u)) = 0
    rw [blockMatrix_second]
    exact (class_zero_iff Q _).mpr ⟨second u,rfl⟩
/-- 元直積表示の商から二つの元商への線形射。 -/
def productMap (P Q : Presentation) : PresentedGroups.Group (product P Q) →ₗ[ℤ]
    PresentedGroups.Group P × PresentedGroups.Group Q :=
  (relationSpace (product P Q)).liftQ (pairClass P Q) (pairClass_relations P Q)
/-- 直積商射は同じ原始代表を評価する。 -/
theorem productMap_class (P Q : Presentation) (x : Vec (P.generators+Q.generators)) :
    productMap P Q (quotientClass (product P Q) x) =
      (quotientClass P (first x),quotientClass Q (second x)) := rfl
/-- 二つの元商で零なら原始直積表示の商でも零。 -/
theorem productMap_zero (P Q : Presentation) (x : PresentedGroups.Group (product P Q))
    (hx : productMap P Q x = 0) : x = 0 := by
  obtain ⟨v,rfl⟩ := class_surjective (product P Q) x
  rw [productMap_class] at hx
  obtain ⟨u,hu⟩ := (class_zero_iff P _).mp (congrArg Prod.fst hx)
  obtain ⟨w,hw⟩ := (class_zero_iff Q _).mp (congrArg Prod.snd hx)
  apply (class_zero_iff (product P Q) _).mpr
  refine ⟨join u w,?_⟩
  change blockMatrix P.matrix Q.matrix *ᵥ join u w = v
  rw [← join_parts (blockMatrix P.matrix Q.matrix *ᵥ join u w),blockMatrix_first,
    blockMatrix_second,first_join,second_join,hu,hw,join_parts]
/-- 直積商射は余分な元を同一視しない。 -/
theorem productMap_injective (P Q : Presentation) : Function.Injective (productMap P Q) := by
  intro x y h
  apply sub_eq_zero.mp
  apply productMap_zero P Q
  rw [map_sub,h,sub_self]
/-- 二つの任意の元商元は原始直積表示から復元できる。 -/
theorem productMap_surjective (P Q : Presentation) : Function.Surjective (productMap P Q) := by
  rintro ⟨x,y⟩
  obtain ⟨a,rfl⟩ := class_surjective P x
  obtain ⟨b,rfl⟩ := class_surjective Q y
  exact ⟨quotientClass (product P Q) (join a b), by rw [productMap_class,first_join,second_join]⟩
/-- 原始直積表示と二つの元商群の同型。 -/
noncomputable def productEquiv (P Q : Presentation) : PresentedGroups.Group (product P Q) ≃ₗ[ℤ]
    PresentedGroups.Group P × PresentedGroups.Group Q :=
  LinearEquiv.ofBijective (productMap P Q) ⟨productMap_injective P Q,productMap_surjective P Q⟩
/-- 直積同型は元の二つの代表を保持する。 -/
theorem productEquiv_class (P Q : Presentation) (x : Vec (P.generators+Q.generators)) :
    productEquiv P Q (quotientClass (product P Q) x) =
      (quotientClass P (first x),quotientClass Q (second x)) := rfl
/-- 二つの原始行列を縦に並べる。 -/
def above {m n r : ℕ} (A : Mat m r) (B : Mat n r) : Mat (m+n) r := Fin.addCases A B
/-- 縦連結行列の前半の評価。 -/
theorem above_first {m n r : ℕ} (A : Mat m r) (B : Mat n r) (x : Vec r) :
    first (above A B *ᵥ x) = A *ᵥ x := by
  ext i
  simp [above,first,mulVec]
/-- 縦連結行列の後半の評価。 -/
theorem above_second {m n r : ℕ} (A : Mat m r) (B : Mat n r) (x : Vec r) :
    second (above A B *ᵥ x) = B *ᵥ x := by
  ext i
  simp [above,second,mulVec]
/-- 二つの関係保存から同じ直積表示への射の関係保存を生成する。 -/
theorem above_valid (P Q T : Presentation) (A : Mat Q.generators P.generators)
    (B : Mat T.generators P.generators) (ha : MapValid P Q A) (hb : MapValid P T B) :
    MapValid P (product Q T) (above A B) := by
  apply (mapValid_iff _ _ _).mpr
  intro x hx
  apply productMap_injective Q T
  change productMap Q T (quotientClass (product Q T) (above A B *ᵥ x)) = productMap Q T 0
  rw [productMap_class,map_zero,above_first,above_second]
  exact Prod.ext (relation_preserved P Q A ha hx) (relation_preserved P T B hb hx)
/-- 直積へdecodeした射の二成分は同じ元の二商射。 -/
theorem above_map (P Q T : Presentation) (A : Mat Q.generators P.generators)
    (B : Mat T.generators P.generators) (ha : MapValid P Q A) (hb : MapValid P T B)
    (x : PresentedGroups.Group P) :
    productEquiv Q T (PresentedGroups.map P (product Q T) (above A B) (above_valid P Q T A B ha hb) x) =
      (PresentedGroups.map P Q A ha x,PresentedGroups.map P T B hb x) := by
  obtain ⟨a,rfl⟩ := class_surjective P x
  rw [map_class,productEquiv_class,above_first,above_second,map_class,map_class]

end AAT.AG.SpecifiedRepairLifting.PresentedProduct

#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.secondMap
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.blockMatrix
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.blockMatrix_first
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.blockMatrix_second
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.product
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.pairClass
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.pairClass_apply
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.pairClass_relations
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.productMap
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.productMap_class
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.productMap_zero
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.productMap_injective
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.productMap_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.productEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.productEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.above
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.above_first
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.above_second
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.above_valid
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedProduct.above_map
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.PresentedProduct
