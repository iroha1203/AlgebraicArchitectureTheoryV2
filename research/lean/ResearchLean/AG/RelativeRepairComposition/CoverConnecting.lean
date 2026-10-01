import ResearchLean.AG.RelativeRepairComposition.CoverCohomology

/-!
# Original cycle values of the native connecting morphism

The connecting morphism comes from the accepted short exact sequence of native
complexes. Its value is proved from an actual lift and its actual differential;
no connecting-map certificate is supplied as input.
## Implementation notes

G-130 B uses mathlib native connecting morphisms. Morphisms from the free
cyclic group recover their values on whole original cycle representatives.
ULift retains the original arbitrary coefficient universe; no finite or
singleton coefficient specialization supplies the sign computation.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory
universe u uI
namespace CohomologyClass
/-- A point of a full abelian group defines the morphism from the free cyclic group. -/
def point {A : Ab.{u}} (x : A) : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A :=
  AddCommGrpCat.ofHom ((zmultiplesHom A x).comp AddEquiv.ulift.toAddMonoidHom)
/-- Evaluation at the free generator returns the original point. -/
theorem point_one {A : Ab.{u}} (x : A) : point x (ULift.up (1 : ℤ)) = x := one_zsmul x
/-- Point morphisms commute with every actual additive map. -/
theorem point_comp {A B : Ab.{u}} (f : A ⟶ B) (x : A) : point x ≫ f = point (f x) := by
  apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
  intro n
  change f (n.down • x) = n.down • f x
  exact map_zsmul f.hom n.down x
/-- The zero point gives the zero morphism. -/
theorem point_zero {A : Ab.{u}} : point (0 : A) = 0 := by
  apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
  intro n
  exact zsmul_zero n.down

variable (S : ShortComplex Ab.{u})
/-- The original cycle value gives an actual cycle morphism. -/
theorem point_cycle (z : S.g.hom.ker) : point z.1 ≫ S.g = 0 := by
  rw [point_comp,z.2,point_zero]
/-- Lifting an original cycle point returns its full native cycle. -/
theorem lift_point_value (z : S.g.hom.ker) :
    S.liftCycles (point z.1) (point_cycle S z) (ULift.up (1 : ℤ)) = S.abCyclesIso.inv z := by
  apply (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance
  rw [S.abCyclesIso_inv_apply_iCycles]
  have hh := congrArg (fun f => f (ULift.up (1 : ℤ)))
    (S.liftCycles_i (point z.1) (point_cycle S z))
  change S.iCycles (S.liftCycles (point z.1) (point_cycle S z) (ULift.up (1 : ℤ))) =
    point z.1 (ULift.up (1 : ℤ)) at hh
  rw [point_one] at hh
  exact hh
/-- The lifted original point has exactly its native homology class. -/
theorem class_point_value (z : S.g.hom.ker) :
    S.homologyπ (S.liftCycles (point z.1) (point_cycle S z) (ULift.up (1 : ℤ))) =
      classHom S z := by
  rw [lift_point_value]
  rfl

variable {S T : ShortComplex Ab.{u}}
/-- A native short-complex map retains its actual cycle values. -/
noncomputable def cycleMap (φ : S ⟶ T) : S.g.hom.ker →+ T.g.hom.ker where
  toFun z := ⟨φ.τ₂ z.1,by
    change T.g (φ.τ₂ z.1) = 0
    have hh := congrArg (fun f => f z.1) φ.comm₂₃
    change T.g (φ.τ₂ z.1) = φ.τ₃ (S.g z.1) at hh
    rw [z.2,map_zero] at hh
    exact hh⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
/-- Native cycle functoriality preserves the entire original cycle. -/
theorem cycles_map_value (φ : S ⟶ T) (z : S.g.hom.ker) :
    ShortComplex.cyclesMap φ (S.abCyclesIso.inv z) = T.abCyclesIso.inv (cycleMap φ z) := by
  apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
  rw [T.abCyclesIso_inv_apply_iCycles]
  have hh := congrArg (fun f => f (S.abCyclesIso.inv z)) (ShortComplex.cyclesMap_i φ)
  change T.iCycles (ShortComplex.cyclesMap φ (S.abCyclesIso.inv z)) =
    φ.τ₂ (S.iCycles (S.abCyclesIso.inv z)) at hh
  rw [S.abCyclesIso_inv_apply_iCycles] at hh
  exact hh
/-- Native homology maps send each full original cycle to its actual mapped cycle class. -/
theorem class_naturality (φ : S ⟶ T) (z : S.g.hom.ker) :
    ShortComplex.homologyMap φ (classHom S z) = classHom T (cycleMap φ z) := by
  have hh := congrArg (fun f => f (S.abCyclesIso.inv z)) (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (S.homologyπ (S.abCyclesIso.inv z)) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.abCyclesIso.inv z)) at hh
  rw [cycles_map_value] at hh
  exact hh

variable (K : HomologicalComplex Ab.{u} (ComplexShape.up ℕ)) (i : ℕ)
/-- Native complex cycle lifting retains the same original class. -/
theorem complex_class_point (z : (K.sc i).g.hom.ker) (j : ℕ)
    (hj : (ComplexShape.up ℕ).next i = j) (hz : point z.1 ≫ K.d i j = 0) :
    K.homologyπ i (K.liftCycles (point z.1) j hj hz (ULift.up (1 : ℤ))) =
      classHom (K.sc i) z := by
  have hv : K.liftCycles (point z.1) j hj hz (ULift.up (1 : ℤ)) =
      (K.sc i).abCyclesIso.inv z := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    change (K.sc i).iCycles _ = (K.sc i).iCycles ((K.sc i).abCyclesIso.inv z)
    rw [(K.sc i).abCyclesIso_inv_apply_iCycles]
    have hh := congrArg (fun f => f (ULift.up (1 : ℤ))) (K.liftCycles_i (point z.1) j hj hz)
    change K.iCycles i (K.liftCycles (point z.1) j hj hz (ULift.up (1 : ℤ))) =
      point z.1 (ULift.up (1 : ℤ)) at hh
    rw [point_one] at hh
    exact hh
  rw [hv]
  rfl
end CohomologyClass

namespace CoverConnecting
variable {S : ShortComplex (CochainComplex Ab.{u} ℕ)}
variable (hS : S.ShortExact) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j)
/-- The native connecting map sends a lifted cycle to its actual global differential class. -/
theorem connecting_class (z : (S.X₃.sc i).g.hom.ker)
    (a : S.X₂.X i) (ha : S.g.f i a = z.1)
    (c : (S.X₁.sc j).g.hom.ker) (hc : S.f.f j c.1 = S.X₂.d i j a) :
    hS.δ i j hij (CohomologyClass.classHom (S.X₃.sc i) z) =
      CohomologyClass.classHom (S.X₁.sc j) c := by
  have hn : (ComplexShape.up ℕ).next i = j := (ComplexShape.up ℕ).next_eq' hij
  have hz : CohomologyClass.point z.1 ≫ S.X₃.d i j = 0 := by
    rw [← hn]
    exact CohomologyClass.point_cycle (S.X₃.sc i) z
  have ha' : CohomologyClass.point a ≫ S.g.f i = CohomologyClass.point z.1 := by
    rw [CohomologyClass.point_comp,ha]
  have hc' : CohomologyClass.point c.1 ≫ S.f.f j =
      CohomologyClass.point a ≫ S.X₂.d i j := by
    rw [CohomologyClass.point_comp,CohomologyClass.point_comp]
    exact congrArg (fun x : S.X₂.X j => CohomologyClass.point x) hc
  have hh := hS.δ_eq i j hij
    (CohomologyClass.point z.1) hz (CohomologyClass.point a) ha'
    (CohomologyClass.point c.1) hc' ((ComplexShape.up ℕ).next j) rfl
  have hv := congrArg (fun f => f (ULift.up (1 : ℤ))) hh
  dsimp only [ConcreteCategory.comp_apply] at hv
  exact (congrArg (fun x => hS.δ i j hij x)
    (CohomologyClass.complex_class_point S.X₃ i z j hn hz).symm).trans
      (hv.trans (CohomologyClass.complex_class_point S.X₁ j c _ _ _))
end CoverConnecting
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
