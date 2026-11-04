import ResearchLean.AG.SpecifiedRepairLifting.FiniteLifting

/-! # 原始有限表示同型とCの輸送

Implementation notes: 表示変更は順逆の整数行列を入力とし、関係保存・
cochain則・両合成の恒等性を全列の有限検査で生成する。
同じCの同型平方を使い、特解や出力基底の字面一致を要求しない。
一般平方の保存から反映を推論せず、実際の両逆を生成してから輸送する。
-/
namespace AAT.AG.SpecifiedRepairLifting.FiniteRepresentation
open CategoryTheory Matrix IntegerElimination PresentedGroups PresentedComplex PresentedProduct FiniteLifting

/-- 原始比較の一方の合成が恒等となる三次数の有限検査。 -/
def InverseValid {C D : ComplexData} (f : ComparisonData C D) (g : ComparisonData D C) : Prop :=
  ZeroColumns C.P0 (g.f0*f.f0-1) ∧ ZeroColumns C.P1 (g.f1*f.f1-1) ∧ ZeroColumns C.P2 (g.f2*f.f2-1)
/-- 三次数の逆条件も有限整数演算で決定できる。 -/
instance inverseValidDecidable {C D : ComplexData} (f : ComparisonData C D) (g : ComparisonData D C) :
    Decidable (InverseValid f g) := by unfold InverseValid; infer_instance
/-- 原始合成の有限検査から非負複体の実恒等射を生成する。 -/
theorem comparison_inverse {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (f : ComparisonData C D) (g : ComparisonData D C) (hf : ComparisonValid f) (hg : ComparisonValid g)
    (hi : InverseValid f g) : comparison hc hd f hf ≫ comparison hd hc g hg = 𝟙 (native C hc) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases n with _ | _ | _ | n
  · obtain ⟨a,rfl⟩ := class_surjective C.P0 x
    change PresentedGroups.map D.P0 C.P0 g.f0 hg.1
      (PresentedGroups.map C.P0 D.P0 f.f0 hf.1 (quotientClass C.P0 a)) = quotientClass C.P0 a
    rw [map_class,map_class,mulVec_mulVec]
    simpa only [one_mulVec] using (zeroColumns_sub_iff _ _ _).mp hi.1 a
  · obtain ⟨a,rfl⟩ := class_surjective C.P1 x
    change PresentedGroups.map D.P1 C.P1 g.f1 hg.2.1
      (PresentedGroups.map C.P1 D.P1 f.f1 hf.2.1 (quotientClass C.P1 a)) = quotientClass C.P1 a
    rw [map_class,map_class,mulVec_mulVec]
    simpa only [one_mulVec] using (zeroColumns_sub_iff _ _ _).mp hi.2.1 a
  · obtain ⟨a,rfl⟩ := class_surjective C.P2 x
    change PresentedGroups.map D.P2 C.P2 g.f2 hg.2.2.1
      (PresentedGroups.map C.P2 D.P2 f.f2 hf.2.2.1 (quotientClass C.P2 a)) = quotientClass C.P2 a
    rw [map_class,map_class,mulVec_mulVec]
    simpa only [one_mulVec] using (zeroColumns_sub_iff _ _ _).mp hi.2.2 a
  · exact (native_higher_zero C hc n _).trans (native_higher_zero C hc n _).symm
/-- 表示変更の原始順逆三成分。 -/
structure IsoData (C D : ComplexData) where
  hom : ComparisonData C D
  inv : ComparisonData D C
/-- 表示変更の全関係・cochain・両逆条件を有限検査する。 -/
def IsoValid {C D : ComplexData} (e : IsoData C D) : Prop :=
  ComparisonValid e.hom ∧ ComparisonValid e.inv ∧ InverseValid e.hom e.inv ∧ InverseValid e.inv e.hom
/-- 表示同型の全条件は有限に判定可能。 -/
instance isoValidDecidable {C D : ComplexData} (e : IsoData C D) : Decidable (IsoValid e) := by
  unfold IsoValid
  infer_instance
/-- 原始順逆行列の有限検査からCに渡す実cochain同型を構成する。 -/
def nativeIso {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (e : IsoData C D) (he : IsoValid e) : native C hc ≅ native D hd where
  hom := comparison hc hd e.hom he.1
  inv := comparison hd hc e.inv he.2.1
  hom_inv_id := comparison_inverse hc hd e.hom e.inv he.1 he.2.1 he.2.2.1
  inv_hom_id := comparison_inverse hd hc e.inv e.hom he.2.1 he.1 he.2.2.2
/-- 表示同型の順射は同じ元行列のdecode。 -/
theorem nativeIso_hom {C D : ComplexData} (hc : ComplexValid C) (hd : ComplexValid D)
    (e : IsoData C D) (he : IsoValid e) : (nativeIso hc hd e he).hom = comparison hc hd e.hom he.1 := rfl
/-- 比較平方の三成分を原始整数列で有限検査する。 -/
def SquareValid {C D C' D' : ComplexData} (f : ComparisonData C D) (f' : ComparisonData C' D')
    (a : ComparisonData C C') (b : ComparisonData D D') : Prop :=
  ZeroColumns D'.P0 (b.f0*f.f0-f'.f0*a.f0) ∧
    ZeroColumns D'.P1 (b.f1*f.f1-f'.f1*a.f1) ∧ ZeroColumns D'.P2 (b.f2*f.f2-f'.f2*a.f2)
/-- 比較平方の検査も有限。 -/
instance squareValidDecidable {C D C' D' : ComplexData} (f : ComparisonData C D) (f' : ComparisonData C' D')
    (a : ComparisonData C C') (b : ComparisonData D D') : Decidable (SquareValid f f' a b) := by
  unfold SquareValid
  infer_instance
/-- 有限検査からCが要求する同じcochain平方を生成する。 -/
theorem native_square {C D C' D' : ComplexData}
    (hc : ComplexValid C) (hd : ComplexValid D) (hc' : ComplexValid C') (hd' : ComplexValid D')
    (f : ComparisonData C D) (f' : ComparisonData C' D')
    (a : ComparisonData C C') (b : ComparisonData D D')
    (hf : ComparisonValid f) (hf' : ComparisonValid f') (ha : ComparisonValid a) (hb : ComparisonValid b)
    (hs : SquareValid f f' a b) :
    comparison hc hd f hf ≫ comparison hd hd' b hb = comparison hc hc' a ha ≫ comparison hc' hd' f' hf' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases n with _ | _ | _ | n
  · obtain ⟨v,rfl⟩ := class_surjective C.P0 x
    change PresentedGroups.map D.P0 D'.P0 b.f0 hb.1
      (PresentedGroups.map C.P0 D.P0 f.f0 hf.1 (quotientClass C.P0 v)) =
      PresentedGroups.map C'.P0 D'.P0 f'.f0 hf'.1
        (PresentedGroups.map C.P0 C'.P0 a.f0 ha.1 (quotientClass C.P0 v))
    simp only [map_class,mulVec_mulVec]
    exact (zeroColumns_sub_iff _ _ _).mp hs.1 v
  · obtain ⟨v,rfl⟩ := class_surjective C.P1 x
    change PresentedGroups.map D.P1 D'.P1 b.f1 hb.2.1
      (PresentedGroups.map C.P1 D.P1 f.f1 hf.2.1 (quotientClass C.P1 v)) =
      PresentedGroups.map C'.P1 D'.P1 f'.f1 hf'.2.1
        (PresentedGroups.map C.P1 C'.P1 a.f1 ha.2.1 (quotientClass C.P1 v))
    simp only [map_class,mulVec_mulVec]
    exact (zeroColumns_sub_iff _ _ _).mp hs.2.1 v
  · obtain ⟨v,rfl⟩ := class_surjective C.P2 x
    change PresentedGroups.map D.P2 D'.P2 b.f2 hb.2.2.1
      (PresentedGroups.map C.P2 D.P2 f.f2 hf.2.2.1 (quotientClass C.P2 v)) =
      PresentedGroups.map C'.P2 D'.P2 f'.f2 hf'.2.2.1
        (PresentedGroups.map C.P2 C'.P2 a.f2 ha.2.2.1 (quotientClass C.P2 v))
    simp only [map_class,mulVec_mulVec]
    exact (zeroColumns_sub_iff _ _ _).mp hs.2.2 v
  · exact (native_higher_zero D' hd' n _).trans (native_higher_zero D' hd' n _).symm


/-- 有限検査された一般平方は輸送した原始代表のT0条件も生成する。 -/
theorem transported_input {C D C' D' : ComplexData} (f : ComparisonData C D) (f' : ComparisonData C' D')
    (a : ComparisonData C C') (b : ComparisonData D D')
    (hc' : ComplexValid C') (hd' : ComplexValid D')
    (hf' : ComparisonValid f') (ha : ComparisonValid a) (hb : ComparisonValid b)
    (hs : SquareValid f f' a b) (z : Vec C.P1.generators) (v : Vec D.P0.generators)
    (h : InputValid C D f z v) : InputValid C' D' f' (a.f1 *ᵥ z) (b.f0 *ᵥ v) := by
  refine ⟨hc',hd',hf',?_,?_⟩
  · apply (isZero_correct _ _).mpr
    have he := square_closed (comparison h.1 hc' a ha) (quotientClass C.P1 z) (input_closed C D f z v h)
    rw [comparison_apply1,native_d1_class] at he
    exact he
  · apply (isZero_correct _ _).mpr
    have he := square_compatible (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
      (comparison h.1 hc' a ha) (comparison h.2.1 hd' b hb)
      (native_square h.1 h.2.1 hc' hd' f f' a b h.2.2.1 hf' ha hb hs)
      (quotientClass C.P1 z) (quotientClass D.P0 v) (input_compatible C D f z v h)
    rw [comparison_apply0,comparison_apply1,native_d0_class,comparison_apply1] at he
    simpa only [map_sub,sub_eq_zero] using he

section Transport
variable {C D C' D' : ComplexData} (f : ComparisonData C D) (f' : ComparisonData C' D')
  (eC : IsoData C C') (eD : IsoData D D')
  (hc' : ComplexValid C') (hd' : ComplexValid D') (hf' : ComparisonValid f')
  (heC : IsoValid eC) (heD : IsoValid eD) (hs : SquareValid f f' eC.hom eD.hom)
  (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
/-- 表示同型の有限検査から、Cの同じLift同値を原始代表に接続する。 -/
noncomputable def representationLiftEquiv :
    NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b) ≃
    NonnegativeLift (comparison hc' hd' f' hf')
      (quotientClass C'.P1 (eC.hom.f1 *ᵥ z)) (quotientClass D'.P0 (eD.hom.f0 *ᵥ b)) := by
  have eqv := squareLiftEquiv (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
    (nativeIso h.1 hc' eC heC) (nativeIso h.2.1 hd' eD heD)
    (native_square h.1 h.2.1 hc' hd' f f' eC.hom eD.hom h.2.2.1 hf' heC.1 heD.1 hs)
    (quotientClass C.P1 z) (quotientClass D.P0 b)
  simpa only [nativeIso_hom,comparison_apply1,comparison_apply0] using eqv
include hc' hd' hf' heC heD hs h in
/-- 表示同型時の原始solver可解性は同じCのLift同値に従う。 -/
theorem finiteSolve_representation :
    (∃ x, finiteSolve C D f z b = .inl x) ↔
      ∃ x, finiteSolve C' D' f' (eC.hom.f1 *ᵥ z) (eD.hom.f0 *ᵥ b) = .inl x := by
  rw [finiteSolve_complete C D f z b h,
    finiteSolve_complete C' D' f' _ _ (transported_input f f' eC.hom eD.hom hc' hd' hf' heC.1 heD.1 hs z b h)]
  exact (representationLiftEquiv f f' eC eD hc' hd' hf' heC heD hs z b h).nonempty_congr
include hc' hd' hf' heC heD hs h in
/-- 表示同型時は存在一意性の計算結果も保存する。 -/
theorem finiteUnique_representation :
    finiteUnique C D f z b = finiteUnique C' D' f' (eC.hom.f1 *ᵥ z) (eD.hom.f0 *ᵥ b) := by
  apply Bool.eq_iff_iff.mpr
  rw [finiteUnique_lift C D f z b h,
    finiteUnique_lift C' D' f' _ _ (transported_input f f' eC.hom eD.hom hc' hd' hf' heC.1 heD.1 hs z b h)]
  exact and_congr (representationLiftEquiv f f' eC eD hc' hd' hf' heC heD hs z b h).nonempty_congr
    (representationLiftEquiv f f' eC eD hc' hd' hf' heC heD hs z b h).subsingleton_congr
/-- 二つの計算されたkernel有限表示はCの実kernel同型を介して同型になる。 -/
noncomputable def representationKernelEquiv :
    PresentedGroups.Group (correctionPresentation C D f) ≃+
      PresentedGroups.Group (correctionPresentation C' D' f') :=
  (computedKernelEquiv C D f h.1 h.2.1 h.2.2.1).trans
    ((squareKernelEquiv (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
      (nativeIso h.1 hc' eC heC) (nativeIso h.2.1 hd' eD heD)
      (native_square h.1 h.2.1 hc' hd' f f' eC.hom eD.hom h.2.2.1 hf' heC.1 heD.1 hs)).trans
      (computedKernelEquiv C' D' f' hc' hd' hf').symm)

/-- Cによる表示輸送は元C⁰への同じ行列射を使う。 -/
theorem representationLiftEquiv_val
    (a : NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) :
    (representationLiftEquiv f f' eC eD hc' hd' hf' heC heD hs z b h a).val =
      (comparison h.1 hc' eC.hom heC.1).f 0 a.val := rfl
/-- 計算表示間の同型と実kernel同型が同じ図式をなす。 -/
theorem representationKernelEquiv_comm (t : PresentedGroups.Group (correctionPresentation C D f)) :
    computedKernelEquiv C' D' f' hc' hd' hf'
      (representationKernelEquiv f f' eC eD hc' hd' hf' heC heD hs z b h t) =
    squareKernelEquiv (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
      (nativeIso h.1 hc' eC heC) (nativeIso h.2.1 hd' eD heD)
      (native_square h.1 h.2.1 hc' hd' f f' eC.hom eD.hom h.2.2.1 hf' heC.1 heD.1 hs)
      (computedKernelEquiv C D f h.1 h.2.1 h.2.2.1 t) := by
  exact (computedKernelEquiv C' D' f' hc' hd' hf').apply_symm_apply _
/-- 表示輸送の公開同値はCの同じLift同値に一致する。 -/
theorem representationLiftEquiv_eq_squareLiftEquiv
    (a : NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) :
    representationLiftEquiv f f' eC eD hc' hd' hf' heC heD hs z b h a =
    squareLiftEquiv (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
      (nativeIso h.1 hc' eC heC) (nativeIso h.2.1 hd' eD heD)
      (native_square h.1 h.2.1 hc' hd' f f' eC.hom eD.hom h.2.2.1 hf' heC.1 heD.1 hs)
      (quotientClass C.P1 z) (quotientClass D.P0 b) a := rfl
/-- 計算された核表示の作用もCの同じ作用輸送と可換。 -/
theorem representation_action
    (a : NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b))
    (t : PresentedGroups.Group (correctionPresentation C D f)) :
    representationLiftEquiv f f' eC eD hc' hd' hf' heC heD hs z b h
      (addKernel _ (computedKernelEquiv C D f h.1 h.2.1 h.2.2.1 t) a) =
    addKernel _ (computedKernelEquiv C' D' f' hc' hd' hf'
      (representationKernelEquiv f f' eC eD hc' hd' hf' heC heD hs z b h t))
      (representationLiftEquiv f f' eC eD hc' hd' hf' heC heD hs z b h a) := by
  rw [representationKernelEquiv_comm]
  simp only [representationLiftEquiv_eq_squareLiftEquiv]
  exact squareLiftEquiv_addKernel (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
      (nativeIso h.1 hc' eC heC) (nativeIso h.2.1 hd' eD heD)
      (native_square h.1 h.2.1 hc' hd' f f' eC.hom eD.hom h.2.2.1 hf' heC.1 heD.1 hs)
      (quotientClass C.P1 z) (quotientClass D.P0 b) a (computedKernelEquiv C D f h.1 h.2.1 h.2.2.1 t)

/-- 表示変更時の同じ標準錐障害もCの標準誘導射で輸送される。 -/
theorem representation_obstruction :
    squareObstructionMap (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
      (comparison h.1 hc' eC.hom heC.1) (comparison h.2.1 hd' eD.hom heD.1)
      (native_square h.1 h.2.1 hc' hd' f f' eC.hom eD.hom h.2.2.1 hf' heC.1 heD.1 hs)
      (nonnegativeObstruction (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)
        (input_closed C D f z b h) (input_compatible C D f z b h)) =
    nonnegativeObstruction (comparison hc' hd' f' hf')
      (quotientClass C'.P1 (eC.hom.f1 *ᵥ z)) (quotientClass D'.P0 (eD.hom.f0 *ᵥ b))
      (input_closed C' D' f' _ _ (transported_input f f' eC.hom eD.hom hc' hd' hf' heC.1 heD.1 hs z b h))
      (input_compatible C' D' f' _ _ (transported_input f f' eC.hom eD.hom hc' hd' hf' heC.1 heD.1 hs z b h)) := by
  simpa only [comparison_apply1,comparison_apply0] using
    obstruction_naturality (comparison h.1 h.2.1 f h.2.2.1) (comparison hc' hd' f' hf')
      (comparison h.1 hc' eC.hom heC.1) (comparison h.2.1 hd' eD.hom heD.1)
      (native_square h.1 h.2.1 hc' hd' f f' eC.hom eD.hom h.2.2.1 hf' heC.1 heD.1 hs)
      (quotientClass C.P1 z) (quotientClass D.P0 b) (input_closed C D f z b h) (input_compatible C D f z b h)

end Transport
end AAT.AG.SpecifiedRepairLifting.FiniteRepresentation

#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.InverseValid
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.inverseValidDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.comparison_inverse
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.IsoData
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.IsoValid
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.isoValidDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.nativeIso
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.nativeIso_hom
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.SquareValid
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.squareValidDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.native_square
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.transported_input
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.representationLiftEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.finiteSolve_representation
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.finiteUnique_representation
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.representationKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.representationLiftEquiv_val
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.representationKernelEquiv_comm
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.representation_action
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.representation_obstruction
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteRepresentation.representationLiftEquiv_eq_squareLiftEquiv
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.FiniteRepresentation
