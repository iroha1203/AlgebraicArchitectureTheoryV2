import ResearchLean.AG.SpecifiedRepairLifting.ResidualExact
/-! # 比較の可換正方形に沿う指定補正の輸送

元のcochain射の次数成分で実Liftと実kernelを輸送し、
同じ平方から標準錐の射と余核の射を構成する。
Implementation notes: 実Liftは元の次数0の射で送り、核・余核の輸送はその制限と
商への降下から生成する。障害群の射にはmathlib標準mappingCone.mapとhomologyMapを用い、
両座標の評価からj,pと指定障害の自然性を示す。輸送則を結論fieldとして入力する方式は
構成義務を満たさず、一般平方へ同型条件を加える方式はCの量化を縮めるため採らない。
同型の逆向きだけは元のcochain逆射から別に構成し、両逆を検証する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.SpecifiedRepairLifting
open CochainComplex
universe w
variable {C D C' D' : CochainComplex (ModuleCat.{w} ℤ) ℕ}
variable (f : C ⟶ D) (f' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D')
variable (h : f ≫ β = α ≫ f')
/-- 可換平方の各次数で元の値が一致する。 -/
theorem square_component (h : f ≫ β = α ≫ f') (i : ℕ) (x : C.X i) : β.f i (f.f i x) = f'.f i (α.f i x) :=
  congrArg (fun g : C ⟶ D' => g.f i x) h
/-- cochain射による元の閉性の保存。 -/
theorem square_closed (z : C.X 1) (hz : C.d 1 2 z = 0) : C'.d 1 2 (α.f 1 z) = 0 := by
  have hd := congrArg (fun g : C.X 1 ⟶ C'.X 2 => g z) (α.comm 1 2)
  change C'.d 1 2 (α.f 1 z) = α.f 2 (C.d 1 2 z) at hd
  simpa only [hz, map_zero] using hd
/-- 同じ平方が指定補正の適合等式を保存する。 -/
theorem square_compatible (h : f ≫ β = α ≫ f') (z : C.X 1) (b : D.X 0) (hb : D.d 0 1 b = f.f 1 z) :
    D'.d 0 1 (β.f 0 b) = f'.f 1 (α.f 1 z) := by
  have hd := congrArg (fun g : D.X 0 ⟶ D'.X 1 => g b) (β.comm 0 1)
  change D'.d 0 1 (β.f 0 b) = β.f 1 (D.d 0 1 b) at hd
  rw [hb, square_component f f' α β h] at hd
  exact hd
/-- 元の補正をα⁰で送り、厳密な二等式を保存する。 -/
def squareLiftMap {z : C.X 1} {b : D.X 0} (a : NonnegativeLift f z b) :
    NonnegativeLift f' (α.f 1 z) (β.f 0 b) :=
  ⟨α.f 0 a.val, by
    have hd := congrArg (fun g : C.X 0 ⟶ C'.X 1 => g a.val) (α.comm 0 1)
    change C'.d 0 1 (α.f 0 a.val) = α.f 1 (C.d 0 1 a.val) at hd
    simpa only [a.property.1] using hd,
    by rw [← square_component f f' α β h, a.property.2]⟩
/-- 輸送した補正の値は元のα⁰の値。 -/
@[simp] theorem squareLiftMap_val {z : C.X 1} {b : D.X 0} (a : NonnegativeLift f z b) :
    (squareLiftMap f f' α β h a).val = α.f 0 a.val := rfl
/-- cochain射の零次cycleへの実制限。 -/
def zeroCyclesMap (α : C ⟶ C') : zeroCycles C →+ zeroCycles C' where
  toFun a := ⟨α.f 0 a.val, by
    have ha : C.d 0 1 a.val = 0 := a.property
    have hd := congrArg (fun g : C.X 0 ⟶ C'.X 1 => g a.val) (α.comm 0 1)
    change C'.d 0 1 (α.f 0 a.val) = α.f 1 (C.d 0 1 a.val) at hd
    change C'.d 0 1 (α.f 0 a.val) = 0
    simpa only [ha, map_zero] using hd⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a a' := Subtype.ext (map_add _ a.val a'.val)
/-- 零次cycleの比較も同じ平方で可換になる。 -/
theorem cycleComparison_square (h : f ≫ β = α ≫ f') (a : zeroCycles C) :
    zeroCyclesMap β (cycleComparison f a) = cycleComparison f' (zeroCyclesMap α a) :=
  Subtype.ext (square_component f f' α β h 0 a.val)
/-- 同じ平方から実kernelの加法写像を生成する。 -/
def squareKernelMap : CorrectionKernel f →+ CorrectionKernel f' where
  toFun a := ⟨zeroCyclesMap α a.val, by
    change cycleComparison f' (zeroCyclesMap α a.val) = 0
    rw [← cycleComparison_square f f' α β h, a.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a a' := Subtype.ext (map_add _ a.val a'.val)
/-- 解への実作用は同じkernel輸送と可換になる。 -/
theorem squareLiftMap_addKernel {z : C.X 1} {b : D.X 0}
    (a : NonnegativeLift f z b) (k : CorrectionKernel f) :
    squareLiftMap f f' α β h (addKernel f k a) =
      addKernel f' (squareKernelMap f f' α β h k) (squareLiftMap f f' α β h a) :=
  Subtype.ext (map_add (α.f 0).hom a.val k.val.val)
/-- 任意二解の差の輸送も同じ差から生成される。 -/
theorem squareLiftMap_difference {z : C.X 1} {b : D.X 0}
    (a a' : NonnegativeLift f z b) :
    squareKernelMap f f' α β h (liftDifference f a a') =
      liftDifference f' (squareLiftMap f f' α β h a) (squareLiftMap f f' α β h a') := by
  apply Subtype.ext
  apply Subtype.ext
  exact map_sub (α.f 0).hom a.val a'.val
/-- 同じ平方から実余核の加法写像を生成する。 -/
def squareCokernelMap : CorrectionCokernel f →+ CorrectionCokernel f' :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (cycleComparison f').range).comp (zeroCyclesMap β))
    (by
      rintro b ⟨a,rfl⟩
      change (QuotientAddGroup.mk (zeroCyclesMap β (cycleComparison f a)) : CorrectionCokernel f') = 0
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      exact ⟨zeroCyclesMap α a, (cycleComparison_square f f' α β h a).symm⟩)
/-- 余核輸送は全ての実代表にβ⁰を作用させる。 -/
@[simp] theorem squareCokernelMap_mk (b : zeroCycles D) :
    squareCokernelMap f f' α β h (QuotientAddGroup.mk' _ b) =
      QuotientAddGroup.mk' _ (zeroCyclesMap β b) := rfl
/-- 元の可換平方を標準零延長の可換平方へ送る。 -/
theorem zeroExtension_square (h : f ≫ β = α ≫ f') :
    zeroExtensionMap C D f ≫ zeroExtensionMap D D' β =
      zeroExtensionMap C C' α ≫ zeroExtensionMap C' D' f' := by
  unfold zeroExtensionMap
  rw [← extendMap_comp, ← extendMap_comp, h]
/-- Cの錐写像はmathlib標準mappingCone.mapそのもの。 -/
def squareConeMap : mappingCone (zeroExtensionMap C D f) ⟶ mappingCone (zeroExtensionMap C' D' f') :=
  mappingCone.map _ _ (zeroExtensionMap C C' α) (zeroExtensionMap D D' β)
    (zeroExtension_square f f' α β h)

/-- 標準錐写像の座標は元のβ⁰とα¹の同じ値。 -/
theorem squareConeMap_coordinates (x : (mappingCone (zeroExtensionMap C D f)).X 0) :
    nonnegativeConeCoordinateEquiv f' ((squareConeMap f f' α β h).f 0 x) =
      (β.f 0 (nonnegativeConeCoordinateEquiv f x).1,
        α.f 1 (nonnegativeConeCoordinateEquiv f x).2) := by
  have hc := coneCoordinateEquiv_map (zeroExtensionMap C D f) (zeroExtensionMap C' D' f')
    (zeroExtensionMap C C' α) (zeroExtensionMap D D' β) (zeroExtension_square f f' α β h) 0 x
  change coneCoordinateEquiv (zeroExtensionMap C' D' f') 0
    ((squareConeMap f f' α β h).f 0 x) =
      ((zeroExtensionMap D D' β).f 0 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 x).1,
        (zeroExtensionMap C C' α).f 1 (coneCoordinateEquiv (zeroExtensionMap C D f) 0 x).2) at hc
  apply Prod.ext
  · change zeroExtensionEquiv D' 0
      (coneCoordinateEquiv (zeroExtensionMap C' D' f') 0
        ((squareConeMap f f' α β h).f 0 x)).1 = _
    rw [hc]
    exact zeroExtensionEquiv_map D D' β 0 _
  · change zeroExtensionEquiv C' 1
      (coneCoordinateEquiv (zeroExtensionMap C' D' f') 0
        ((squareConeMap f f' α β h).f 0 x)).2 = _
    rw [hc]
    exact zeroExtensionEquiv_map C C' α 1 _
/-- 同じ標準錐写像の実cycleへの制限。 -/
def squareConeCycleMap := moduleCycleMap ((shortComplexFunctor _ _ 0).map (squareConeMap f f' α β h))
/-- 標準錐のH⁰に誘導された射。 -/
def squareObstructionMap : (mappingCone (zeroExtensionMap C D f)).homology 0 →+
    (mappingCone (zeroExtensionMap C' D' f')).homology 0 :=
  (homologyMap (squareConeMap f f' α β h) 0).hom.toAddMonoidHom
/-- 同じ標準誘導射は全ての元cycleの類を保存する。 -/
theorem squareObstructionMap_class
    (c : LinearMap.ker ((mappingCone (zeroExtensionMap C D f)).sc 0).g.hom) :
    squareObstructionMap f f' α β h (moduleCycleClass _ c) =
      moduleCycleClass _ (squareConeCycleMap f f' α β h c) :=
  moduleCycleClass_naturality _ c
/-- 指定入力から生成したcycleは同じ平方で厳密に輸送される。 -/
theorem squareConeCycleMap_specified (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    squareConeCycleMap f f' α β h (nonnegativeSpecifiedCycle f z b hz hb) =
      nonnegativeSpecifiedCycle f' (α.f 1 z) (β.f 0 b)
        (square_closed α z hz) (square_compatible f f' α β h z b hb) := by
  apply Subtype.ext
  apply (nonnegativeConeCoordinateEquiv f').injective
  change nonnegativeConeCoordinateEquiv f'
    ((squareConeMap f f' α β h).f 0 (nonnegativeSpecifiedCycle f z b hz hb).val) = _
  rw [squareConeMap_coordinates, nonnegativeSpecifiedCycle_coordinates, nonnegativeSpecifiedCycle_coordinates]
  simp only [map_neg]
/-- Cの障害自然性。一般平方で同じ障害を同じ指定値の障害へ送る。 -/
theorem obstruction_naturality (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    squareObstructionMap f f' α β h (nonnegativeObstruction f z b hz hb) =
      nonnegativeObstruction f' (α.f 1 z) (β.f 0 b)
        (square_closed α z hz) (square_compatible f f' α β h z b hb) := by
  rw [← nonnegativeSpecifiedCycle_class, squareObstructionMap_class,
    squareConeCycleMap_specified, nonnegativeSpecifiedCycle_class]
/-- 一般平方では障害零性を保存する。反映は仮定しない。 -/
theorem obstruction_zero_preserved (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z)
    (ho : nonnegativeObstruction f z b hz hb = 0) :
    nonnegativeObstruction f' (α.f 1 z) (β.f 0 b)
      (square_closed α z hz) (square_compatible f f' α β h z b hb) = 0 := by
  rw [← obstruction_naturality f f' α β h z b hz hb, ho, map_zero]

/-- 短完全列のjは余核と標準錐の同じ輸送と可換。 -/
theorem cokernelInclusion_naturality (q : CorrectionCokernel f) :
    squareObstructionMap f f' α β h (cokernelInclusion f q) =
      cokernelInclusion f' (squareCokernelMap f f' α β h q) := by
  obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (cycleComparison f).range q
  change squareObstructionMap f f' α β h (moduleCycleClass _ (zeroCycleToCone f b)) =
    moduleCycleClass _ (zeroCycleToCone f' (zeroCyclesMap β b))
  rw [squareObstructionMap_class]
  congr 1
  apply Subtype.ext
  apply (nonnegativeConeCoordinateEquiv f').injective
  change nonnegativeConeCoordinateEquiv f' ((squareConeMap f f' α β h).f 0 (zeroCycleToCone f b).val) = _
  rw [squareConeMap_coordinates, zeroCycleToCone_coordinates, zeroCycleToCone_coordinates]
  simp only [map_zero]
  rfl
/-- 短完全列のpは元の標準H¹αと標準錐輸送に自然。 -/
theorem coneProjection_naturality (x : (mappingCone (zeroExtensionMap C D f)).homology 0) :
    coneProjection f' (squareObstructionMap f f' α β h x) = homologyMap α 1 (coneProjection f x) := by
  obtain ⟨c,rfl⟩ := moduleCycleClass_surjective ((mappingCone (zeroExtensionMap C D f)).sc 0) x
  rw [squareObstructionMap_class, coneProjection_class, coneProjection_class]
  change moduleCycleClass _ _ = ShortComplex.homologyMap ((shortComplexFunctor _ _ 1).map α) _
  rw [moduleCycleClass_naturality]
  congr 1
  apply Subtype.ext
  exact congrArg Prod.snd (squareConeMap_coordinates f f' α β h c.val)
/-- 元のH¹比較のkernelも同じ標準H¹αで輸送する。 -/
def squareH1KernelMap : (homologyMap f 1).hom.toAddMonoidHom.ker →+
    (homologyMap f' 1).hom.toAddMonoidHom.ker where
  toFun y := ⟨homologyMap α 1 y.val, by
    have hc := congrArg (fun g : C ⟶ D' => homologyMap g 1 y.val) h
    simp only [homologyMap_comp, ModuleCat.comp_apply] at hc
    have hy : homologyMap f 1 y.val = 0 := y.property
    change homologyMap f' 1 (homologyMap α 1 y.val) = 0
    rw [hy, map_zero] at hc
    exact hc.symm⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
/-- 実kernelを終域とするpの自然性。 -/
theorem coneKernelProjection_naturality (x : (mappingCone (zeroExtensionMap C D f)).homology 0) :
    coneKernelProjection f' (squareObstructionMap f f' α β h x) =
      squareH1KernelMap f f' α β h (coneKernelProjection f x) :=
  Subtype.ext (coneProjection_naturality f f' α β h x)
/-- 輸送した元補正の補正式。 -/
theorem square_correction (a₀ : C.X 0) (z : C.X 1) (ha₀ : C.d 0 1 a₀ = z) :
    C'.d 0 1 (α.f 0 a₀) = α.f 1 z := by
  have hd := congrArg (fun g : C.X 0 ⟶ C'.X 1 => g a₀) (α.comm 0 1)
  change C'.d 0 1 (α.f 0 a₀) = α.f 1 (C.d 0 1 a₀) at hd
  simpa only [ha₀] using hd
/-- 残差の余核類も同じ平方と輸送した元補正に自然。 -/
theorem residualClass_naturality (z : C.X 1) (b : D.X 0) (a₀ : C.X 0)
    (ha₀ : C.d 0 1 a₀ = z) (hb : D.d 0 1 b = f.f 1 z) :
    squareCokernelMap f f' α β h (residualClass f z b a₀ ha₀ hb) =
      residualClass f' (α.f 1 z) (β.f 0 b) (α.f 0 a₀)
        (square_correction α a₀ z ha₀) (square_compatible f f' α β h z b hb) := by
  apply congrArg (QuotientAddGroup.mk' (cycleComparison f').range)
  apply Subtype.ext
  change β.f 0 (b - f.f 0 a₀) = β.f 0 b - f'.f 0 (α.f 0 a₀)
  rw [map_sub, square_component f f' α β h]

/-- 恒等平方は元の補正をそのまま保つ。 -/
theorem squareLiftMap_id {z : C.X 1} {b : D.X 0} (a : NonnegativeLift f z b) :
    squareLiftMap f f (𝟙 C) (𝟙 D) (by simp) a = a := rfl
/-- 恒等平方は実kernelの恒等写像を与える。 -/
theorem squareKernelMap_id : squareKernelMap f f (𝟙 C) (𝟙 D) (by simp) = AddMonoidHom.id _ := by
  ext a
  rfl
/-- 恒等平方は実余核の恒等写像を与える。 -/
theorem squareCokernelMap_id : squareCokernelMap f f (𝟙 C) (𝟙 D) (by simp) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (cycleComparison f).range q
  rfl
/-- 恒等平方の標準錐写像は標準錐の恒等射。 -/
theorem squareConeMap_id : squareConeMap f f (𝟙 C) (𝟙 D) (by simp) = 𝟙 _ := by
  unfold squareConeMap zeroExtensionMap
  simp only [extendMap_id, mappingCone.map_id]
/-- 恒等平方は標準H⁰でも恒等写像になる。 -/
theorem squareObstructionMap_id : squareObstructionMap f f (𝟙 C) (𝟙 D) (by simp) = AddMonoidHom.id _ := by
  unfold squareObstructionMap
  rw [squareConeMap_id, homologyMap_id]
  rfl
/-- 恒等平方は元のH¹kernelでも恒等写像になる。 -/
theorem squareH1KernelMap_id : squareH1KernelMap f f (𝟙 C) (𝟙 D) (by simp) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change homologyMap (𝟙 C) 1 x.val = x.val
  rw [homologyMap_id]
  rfl

variable {C'' D'' : CochainComplex (ModuleCat.{w} ℤ) ℕ}
variable (f'' : C'' ⟶ D'') (α' : C' ⟶ C'') (β' : D' ⟶ D'') (h' : f' ≫ β' = α' ≫ f'')
/-- 元の二平方の合成もcochain射として可換。 -/
theorem square_composite_comm (h : f ≫ β = α ≫ f') (h' : f' ≫ β' = α' ≫ f'') :
    f ≫ (β ≫ β') = (α ≫ α') ≫ f'' := by
  rw [← Category.assoc, h, Category.assoc, h', Category.assoc]
/-- 合成平方による元補正の輸送は逐次輸送と一致。 -/
theorem squareLiftMap_comp {z : C.X 1} {b : D.X 0} (a : NonnegativeLift f z b) :
    squareLiftMap f f'' (α ≫ α') (β ≫ β') (square_composite_comm f f' α β f'' α' β' h h') a =
      squareLiftMap f' f'' α' β' h' (squareLiftMap f f' α β h a) := rfl
/-- 実kernelの輸送は平方の合成を保存する。 -/
theorem squareKernelMap_comp :
    squareKernelMap f f'' (α ≫ α') (β ≫ β') (square_composite_comm f f' α β f'' α' β' h h') =
      (squareKernelMap f' f'' α' β' h').comp (squareKernelMap f f' α β h) := by
  ext a
  rfl
/-- 実余核の輸送は平方の合成を保存する。 -/
theorem squareCokernelMap_comp :
    squareCokernelMap f f'' (α ≫ α') (β ≫ β') (square_composite_comm f f' α β f'' α' β' h h') =
      (squareCokernelMap f' f'' α' β' h').comp (squareCokernelMap f f' α β h) := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (cycleComparison f).range q
  rfl
/-- 標準錐の射も平方の合成を保存する。 -/
theorem squareConeMap_comp :
    squareConeMap f f'' (α ≫ α') (β ≫ β') (square_composite_comm f f' α β f'' α' β' h h') =
      squareConeMap f f' α β h ≫ squareConeMap f' f'' α' β' h' := by
  unfold squareConeMap zeroExtensionMap
  simp only [extendMap_comp]
  apply mappingCone.map_comp
/-- 標準障害群の射も平方の合成を保存する。 -/
theorem squareObstructionMap_comp :
    squareObstructionMap f f'' (α ≫ α') (β ≫ β') (square_composite_comm f f' α β f'' α' β' h h') =
      (squareObstructionMap f' f'' α' β' h').comp (squareObstructionMap f f' α β h) := by
  unfold squareObstructionMap
  rw [squareConeMap_comp, homologyMap_comp]
  rfl
/-- 元のH¹kernelの輸送も平方の合成を保存する。 -/
theorem squareH1KernelMap_comp :
    squareH1KernelMap f f'' (α ≫ α') (β ≫ β') (square_composite_comm f f' α β f'' α' β' h h') =
      (squareH1KernelMap f' f'' α' β' h').comp (squareH1KernelMap f f' α β h) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change homologyMap (α ≫ α') 1 x.val = homologyMap α' 1 (homologyMap α 1 x.val)
  rw [homologyMap_comp]
  rfl

section Isomorphisms
variable (eC : C ≅ C') (eD : D ≅ D') (he : f ≫ eD.hom = eC.hom ≫ f')
/-- cochain同型の次数成分の一方の復元則。 -/
theorem complexIso_hom_inv (eC : C ≅ C') (i : ℕ) (x : C.X i) :
    eC.inv.f i (eC.hom.f i x) = x := congrArg (fun g : C ⟶ C => g.f i x) eC.hom_inv_id
/-- cochain同型の次数成分の他方の復元則。 -/
theorem complexIso_inv_hom (eC : C ≅ C') (i : ℕ) (x : C'.X i) :
    eC.hom.f i (eC.inv.f i x) = x := congrArg (fun g : C' ⟶ C' => g.f i x) eC.inv_hom_id
/-- 同型平方の逆射も元のcochain射と可換。 -/
theorem square_inverse_comm (he : f ≫ eD.hom = eC.hom ≫ f') :
    f' ≫ eD.inv = eC.inv ≫ f := by
  calc
    f' ≫ eD.inv = eC.inv ≫ (eC.hom ≫ f') ≫ eD.inv := by simp
    _ = eC.inv ≫ (f ≫ eD.hom) ≫ eD.inv := by rw [he]
    _ = eC.inv ≫ f := by simp
/-- cochain同型平方は元の厳密Lift全体の両方向同値を与える。 -/
def squareLiftEquiv (z : C.X 1) (b : D.X 0) :
    NonnegativeLift f z b ≃ NonnegativeLift f' (eC.hom.f 1 z) (eD.hom.f 0 b) where
  toFun := squareLiftMap f f' eC.hom eD.hom he
  invFun a := ⟨eC.inv.f 0 a.val, by
    have hd := congrArg (fun g : C'.X 0 ⟶ C.X 1 => g a.val) (eC.inv.comm 0 1)
    change C.d 0 1 (eC.inv.f 0 a.val) = eC.inv.f 1 (C'.d 0 1 a.val) at hd
    rw [a.property.1, complexIso_hom_inv] at hd
    exact hd,
    by
      rw [← square_component f' f eC.inv eD.inv (square_inverse_comm f f' eC eD he),
        a.property.2, complexIso_hom_inv]⟩
  left_inv a := Subtype.ext (complexIso_hom_inv eC 0 a.val)
  right_inv a := Subtype.ext (complexIso_inv_hom eC 0 a.val)
/-- 同型平方は実kernelの群同型を与える。 -/
def squareKernelEquiv : CorrectionKernel f ≃+ CorrectionKernel f' where
  toFun := squareKernelMap f f' eC.hom eD.hom he
  invFun := squareKernelMap f' f eC.inv eD.inv (square_inverse_comm f f' eC eD he)
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact complexIso_hom_inv eC 0 a.val.val
  right_inv a := by apply Subtype.ext; apply Subtype.ext; exact complexIso_inv_hom eC 0 a.val.val
  map_add' a a' := map_add (squareKernelMap f f' eC.hom eD.hom he) a a'
/-- 同型平方は実余核の群同型を与える。 -/
def squareCokernelEquiv : CorrectionCokernel f ≃+ CorrectionCokernel f' where
  toFun := squareCokernelMap f f' eC.hom eD.hom he
  invFun := squareCokernelMap f' f eC.inv eD.inv (square_inverse_comm f f' eC eD he)
  left_inv q := by
    obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (cycleComparison f).range q
    apply congrArg (QuotientAddGroup.mk' (cycleComparison f).range)
    apply Subtype.ext
    exact complexIso_hom_inv eD 0 b.val
  right_inv q := by
    obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (cycleComparison f').range q
    apply congrArg (QuotientAddGroup.mk' (cycleComparison f').range)
    apply Subtype.ext
    exact complexIso_inv_hom eD 0 b.val
  map_add' q q' := map_add (squareCokernelMap f f' eC.hom eD.hom he) q q'
/-- 同型平方から生成する標準錐そのもののcochain同型。 -/
def squareConeIso : mappingCone (zeroExtensionMap C D f) ≅ mappingCone (zeroExtensionMap C' D' f') where
  hom := squareConeMap f f' eC.hom eD.hom he
  inv := squareConeMap f' f eC.inv eD.inv (square_inverse_comm f f' eC eD he)
  hom_inv_id := by
    rw [← squareConeMap_comp]
    simp only [eC.hom_inv_id, eD.hom_inv_id, squareConeMap_id]
  inv_hom_id := by
    rw [← squareConeMap_comp]
    simp only [eC.inv_hom_id, eD.inv_hom_id, squareConeMap_id]
/-- 同型平方による障害群の群同型は標準homology同型から生成する。 -/
def squareObstructionEquiv : (mappingCone (zeroExtensionMap C D f)).homology 0 ≃+
    (mappingCone (zeroExtensionMap C' D' f')).homology 0 :=
  (homologyMapIso (squareConeIso f f' eC eD he) 0).toLinearEquiv.toAddEquiv
/-- 同型の障害群同値は一般平方で構成した同じ射。 -/
@[simp] theorem squareObstructionEquiv_apply
    (x : (mappingCone (zeroExtensionMap C D f)).homology 0) :
    squareObstructionEquiv f f' eC eD he x = squareObstructionMap f f' eC.hom eD.hom he x := rfl
/-- 同型平方の実解同値とkernel同型は元の作用を保つ。 -/
theorem squareLiftEquiv_addKernel (z : C.X 1) (b : D.X 0)
    (a : NonnegativeLift f z b) (k : CorrectionKernel f) :
    squareLiftEquiv f f' eC eD he z b (addKernel f k a) =
      addKernel f' (squareKernelEquiv f f' eC eD he k) (squareLiftEquiv f f' eC eD he z b a) :=
  squareLiftMap_addKernel f f' eC.hom eD.hom he a k
/-- 同型のときだけ、対応する指定障害の零性を両方向に同定する。 -/
theorem obstruction_zero_iff_of_iso (z : C.X 1) (b : D.X 0)
    (hz : C.d 1 2 z = 0) (hb : D.d 0 1 b = f.f 1 z) :
    nonnegativeObstruction f z b hz hb = 0 ↔
      nonnegativeObstruction f' (eC.hom.f 1 z) (eD.hom.f 0 b)
        (square_closed eC.hom z hz) (square_compatible f f' eC.hom eD.hom he z b hb) = 0 := by
  rw [← obstruction_naturality f f' eC.hom eD.hom he z b hz hb]
  exact (map_eq_zero_iff (squareObstructionEquiv f f' eC eD he)
    (squareObstructionEquiv f f' eC eD he).injective).symm
/-- 同型平方は厳密な指定持ち上げの存在を両方向に保存する。 -/
theorem lift_nonempty_iff_of_iso (he : f ≫ eD.hom = eC.hom ≫ f') (z : C.X 1) (b : D.X 0) :
    Nonempty (NonnegativeLift f z b) ↔
      Nonempty (NonnegativeLift f' (eC.hom.f 1 z) (eD.hom.f 0 b)) :=
  (squareLiftEquiv f f' eC eD he z b).nonempty_congr
/-- 同型平方は元の標準H¹kernelにも群同型を与える。 -/
def squareH1KernelEquiv : (homologyMap f 1).hom.toAddMonoidHom.ker ≃+
    (homologyMap f' 1).hom.toAddMonoidHom.ker where
  toFun := squareH1KernelMap f f' eC.hom eD.hom he
  invFun := squareH1KernelMap f' f eC.inv eD.inv (square_inverse_comm f f' eC eD he)
  left_inv x := by
    apply Subtype.ext
    change (homologyMap eC.hom 1 ≫ homologyMap eC.inv 1) x.val = x.val
    rw [← homologyMap_comp, eC.hom_inv_id, homologyMap_id]
    rfl
  right_inv x := by
    apply Subtype.ext
    change (homologyMap eC.inv 1 ≫ homologyMap eC.hom 1) x.val = x.val
    rw [← homologyMap_comp, eC.inv_hom_id, homologyMap_id]
    rfl
  map_add' x y := map_add (squareH1KernelMap f f' eC.hom eD.hom he) x y
end Isomorphisms

/-- 原始整数複体の符号反転は非自明なcochain自己同型。 -/
def integerNegationIso : integerZeroDifferential ≅ integerZeroDifferential where
  hom := -𝟙 _
  inv := -𝟙 _
  hom_inv_id := by simp
  inv_hom_id := by simp
/-- 同じ零比較の実補正1は同型輸送で−1へ移る。 -/
theorem integer_negation_lift :
    (squareLiftEquiv (0 : integerZeroDifferential ⟶ integerZeroDifferential) 0
      integerNegationIso integerNegationIso (by simp) 0 0 (integerZeroLift 1)).val = (-1 : ℤ) := by
  rfl
/-- 一般平方による非零障害の消滅。零性反映を誤って要求しないための実例。 -/
theorem integer_square_nonreflection :
    nonnegativeObstruction (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      (0 : ℤ) (1 : ℤ) (map_zero _) zero_comparison_compatible ≠ 0 ∧
    squareObstructionMap 0 (𝟙 integerZeroDifferential) 0 (𝟙 _) (by simp)
      (nonnegativeObstruction (0 : integerZeroDifferential ⟶ integerZeroDifferential)
        (0 : ℤ) (1 : ℤ) (map_zero _) zero_comparison_compatible) = 0 := by
  refine ⟨zero_comparison_obstruction_ne_zero, ?_⟩
  rw [obstruction_naturality, nonnegativeObstruction_zero_iff_lift]
  refine ⟨⟨(1 : ℤ), ?_, rfl⟩⟩
  rw [integerZeroDifferential_d]
  rfl

end AAT.AG.SpecifiedRepairLifting
#print axioms AAT.AG.SpecifiedRepairLifting.square_component
#print axioms AAT.AG.SpecifiedRepairLifting.square_closed
#print axioms AAT.AG.SpecifiedRepairLifting.square_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftMap
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftMap_val
#print axioms AAT.AG.SpecifiedRepairLifting.zeroCyclesMap
#print axioms AAT.AG.SpecifiedRepairLifting.cycleComparison_square
#print axioms AAT.AG.SpecifiedRepairLifting.squareKernelMap
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftMap_addKernel
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftMap_difference
#print axioms AAT.AG.SpecifiedRepairLifting.squareCokernelMap
#print axioms AAT.AG.SpecifiedRepairLifting.squareCokernelMap_mk
#print axioms AAT.AG.SpecifiedRepairLifting.zeroExtension_square
#print axioms AAT.AG.SpecifiedRepairLifting.squareConeMap
#print axioms AAT.AG.SpecifiedRepairLifting.squareConeMap_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.squareConeCycleMap
#print axioms AAT.AG.SpecifiedRepairLifting.squareObstructionMap
#print axioms AAT.AG.SpecifiedRepairLifting.squareObstructionMap_class
#print axioms AAT.AG.SpecifiedRepairLifting.squareConeCycleMap_specified
#print axioms AAT.AG.SpecifiedRepairLifting.obstruction_naturality
#print axioms AAT.AG.SpecifiedRepairLifting.obstruction_zero_preserved
#print axioms AAT.AG.SpecifiedRepairLifting.cokernelInclusion_naturality
#print axioms AAT.AG.SpecifiedRepairLifting.coneProjection_naturality
#print axioms AAT.AG.SpecifiedRepairLifting.squareH1KernelMap
#print axioms AAT.AG.SpecifiedRepairLifting.coneKernelProjection_naturality
#print axioms AAT.AG.SpecifiedRepairLifting.square_correction
#print axioms AAT.AG.SpecifiedRepairLifting.residualClass_naturality
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftMap_id
#print axioms AAT.AG.SpecifiedRepairLifting.squareKernelMap_id
#print axioms AAT.AG.SpecifiedRepairLifting.squareCokernelMap_id
#print axioms AAT.AG.SpecifiedRepairLifting.squareConeMap_id
#print axioms AAT.AG.SpecifiedRepairLifting.squareObstructionMap_id
#print axioms AAT.AG.SpecifiedRepairLifting.squareH1KernelMap_id
#print axioms AAT.AG.SpecifiedRepairLifting.square_composite_comm
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftMap_comp
#print axioms AAT.AG.SpecifiedRepairLifting.squareKernelMap_comp
#print axioms AAT.AG.SpecifiedRepairLifting.squareCokernelMap_comp
#print axioms AAT.AG.SpecifiedRepairLifting.squareConeMap_comp
#print axioms AAT.AG.SpecifiedRepairLifting.squareObstructionMap_comp
#print axioms AAT.AG.SpecifiedRepairLifting.squareH1KernelMap_comp
#print axioms AAT.AG.SpecifiedRepairLifting.complexIso_hom_inv
#print axioms AAT.AG.SpecifiedRepairLifting.complexIso_inv_hom
#print axioms AAT.AG.SpecifiedRepairLifting.square_inverse_comm
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.squareKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.squareCokernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.squareConeIso
#print axioms AAT.AG.SpecifiedRepairLifting.squareObstructionEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.squareObstructionEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.squareLiftEquiv_addKernel
#print axioms AAT.AG.SpecifiedRepairLifting.obstruction_zero_iff_of_iso
#print axioms AAT.AG.SpecifiedRepairLifting.lift_nonempty_iff_of_iso
#print axioms AAT.AG.SpecifiedRepairLifting.squareH1KernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.integerNegationIso
#print axioms AAT.AG.SpecifiedRepairLifting.integer_negation_lift
#print axioms AAT.AG.SpecifiedRepairLifting.integer_square_nonreflection
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting
