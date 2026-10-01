import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import ResearchLean.AG.RelativeRepairComposition.NativeFixedRegions
import ResearchLean.AG.RelativeRepairComposition.RelativeFamilies
import ResearchLean.AG.RelativeRepairComposition.ClosedCovers

/-!
# Relative cochains on a closed cover

## Implementation notes

Families keep original names, while native equivalences identify them with the
kernels on the full restricted presentation and its original fixed intersection.
Differentials are the accepted original-index differentials, with relative
membership generated from closedness. All extension sections are degreewise.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
variable {K : FiniteTransportPresentation.{uG}}
namespace RelativeCover
variable (M : LocalCoefficients.{uG,uA} K) (U P : ClosedRegion K)

/-- Relative original-index families in degree 0 on U, vanishing on the same P cells. -/
abbrev C0 := Family.relative M.A U.vertices P.vertices

/-- Relative original-index families in degree 1 on U, vanishing on the same P cells. -/
abbrev C1 := Family.relative (fun e : EdgeName (K := K) => M.A e.2.1) U.edges P.edges

/-- Relative original-index families in degree 2 on U, vanishing on the same P cells. -/
abbrev C2 := Family.relative (fun f => M.A (K.twoTarget f)) U.faces P.faces

/-- Relative original-index families in degree 3 on U, vanishing on the same P cells. -/
abbrev C3 := Family.relative (fun t => M.A (K.threeTarget t)) U.triples P.triples

/-- Reindex degree 0 to the relative kernel on the complete native restricted presentation. -/
noncomputable def native0 : C0 M U P ≃+
    RelativeComplex.relativeC0 (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) where
  toFun b := ⟨b.1,(ClosedRegion.native_relative_zero_iff U P M b.1).mpr b.2⟩
  invFun b := ⟨b.1,(ClosedRegion.native_relative_zero_iff U P M b.1).mp b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Reindex degree 2 to the relative kernel on the complete native restricted presentation. -/
noncomputable def native2 : C2 M U P ≃+
    RelativeComplex.relativeC2 (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) where
  toFun b := ⟨b.1,(ClosedRegion.native_relative_two_iff U P M b.1).mpr b.2⟩
  invFun b := ⟨b.1,(ClosedRegion.native_relative_two_iff U P M b.1).mp b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Reindex degree 3 to the relative kernel on the complete native restricted presentation. -/
noncomputable def native3 : C3 M U P ≃+
    RelativeComplex.relativeC3 (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) where
  toFun b := ⟨b.1,(ClosedRegion.native_relative_three_iff U P M b.1).mpr b.2⟩
  invFun b := ⟨b.1,(ClosedRegion.native_relative_three_iff U P M b.1).mp b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Degree one retains each original edge name through the full edge-name equivalence. -/
noncomputable def native1 : C1 M U P ≃+
    RelativeComplex.relativeC1 (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) where
  toFun h := ⟨(ClosedRegion.nativeC1Equiv U M).symm h.1, by
    apply (ClosedRegion.native_relative_one_iff U P M _).mpr
    rw [AddEquiv.apply_symm_apply]
    exact h.2⟩
  invFun h := ⟨ClosedRegion.nativeC1Equiv U M h.1,
    (ClosedRegion.native_relative_one_iff U P M h.1).mp h.2⟩
  left_inv h := Subtype.ext ((ClosedRegion.nativeC1Equiv U M).apply_symm_apply h.1)
  right_inv h := Subtype.ext ((ClosedRegion.nativeC1Equiv U M).symm_apply_apply h.1)
  map_add' _ _ := rfl

/-- The native degree-one coordinate uses the inverse original edge-name reindexing. -/
theorem native1_val (h : C1 M U P) :
    (native1 M U P h).1 = (ClosedRegion.nativeC1Equiv U M).symm h.1 := rfl

/-- Relative degree-zero membership is generated from native closedness. -/
theorem d0_mem (b : C0 M U P) : ClosedRegion.d0Hom M U b.1 ∈ C1 M U P := by
  have hz := RelativeComplex.d0_mem_relative
    (ClosedRegion.restrictCoefficients U M) (ClosedRegion.nativeIntersection U P) (native0 M U P b)
  have hv := (ClosedRegion.native_relative_one_iff U P M _).mp hz
  rw [ClosedRegion.native_d0_eq] at hv
  exact hv

/-- Relative degree-one membership is generated from the same full native face paths. -/
theorem d1_mem (b : C1 M U P) : ClosedRegion.d1Hom M U b.1 ∈ C2 M U P := by
  have hz := RelativeComplex.d1_mem_relative
    (ClosedRegion.restrictCoefficients U M) (ClosedRegion.nativeIntersection U P) (native1 M U P b)
  have hv := (ClosedRegion.native_relative_two_iff U P M _).mp hz
  rw [native1_val, ClosedRegion.native_d1_eq] at hv
  exact hv

/-- Relative degree-two membership is generated from both full native three-cell routes. -/
theorem d2_mem (b : C2 M U P) : ClosedRegion.d2Hom M U b.1 ∈ C3 M U P := by
  have hz := RelativeComplex.d2_mem_relative
    (ClosedRegion.restrictCoefficients U M) (ClosedRegion.nativeIntersection U P) (native2 M U P b)
  have hv := (ClosedRegion.native_relative_three_iff U P M _).mp hz
  rw [ClosedRegion.native_d2_eq] at hv
  exact hv

/-- The original d0 with its same-fixed-part relative codomain. -/
noncomputable def d0 : C0 M U P →+ C1 M U P where
  toFun b := ⟨ClosedRegion.d0Hom M U b.1,d0_mem M U P b⟩
  map_zero' := Subtype.ext (map_zero (ClosedRegion.d0Hom M U))
  map_add' b c := Subtype.ext (map_add (ClosedRegion.d0Hom M U) b.1 c.1)

/-- Values of the relative d0 are the accepted original-index differential. -/
theorem d0_val (b : C0 M U P) :
    (d0 M U P b).1 = ClosedRegion.d0Hom M U b.1 := rfl

/-- The original d1 with its same-fixed-part relative codomain. -/
noncomputable def d1 : C1 M U P →+ C2 M U P where
  toFun b := ⟨ClosedRegion.d1Hom M U b.1,d1_mem M U P b⟩
  map_zero' := Subtype.ext (map_zero (ClosedRegion.d1Hom M U))
  map_add' b c := Subtype.ext (map_add (ClosedRegion.d1Hom M U) b.1 c.1)

/-- Values of the relative d1 are the accepted original-index differential. -/
theorem d1_val (b : C1 M U P) :
    (d1 M U P b).1 = ClosedRegion.d1Hom M U b.1 := rfl

/-- The original d2 with its same-fixed-part relative codomain. -/
noncomputable def d2 : C2 M U P →+ C3 M U P where
  toFun b := ⟨ClosedRegion.d2Hom M U b.1,d2_mem M U P b⟩
  map_zero' := Subtype.ext (map_zero (ClosedRegion.d2Hom M U))
  map_add' b c := Subtype.ext (map_add (ClosedRegion.d2Hom M U) b.1 c.1)

/-- Values of the relative d2 are the accepted original-index differential. -/
theorem d2_val (b : C2 M U P) :
    (d2 M U P b).1 = ClosedRegion.d2Hom M U b.1 := rfl

/-- The same original relative differential squares to zero in degree 0. -/
theorem d1_d0 (b : C0 M U P) : d1 M U P (d0 M U P b) = 0 :=
  Subtype.ext (ClosedRegion.d1_d0 M U b.1)

/-- The same original relative differential squares to zero in degree 1. -/
theorem d2_d1 (b : C1 M U P) : d2 M U P (d1 M U P b) = 0 :=
  Subtype.ext (ClosedRegion.d2_d1 M U b.1)


variable {U V : ClosedRegion K}

/-- Restrict the same fixed-part relative degree-0 families along original-cell inclusion. -/
def r0 (h : ClosedRegion.Inclusion V U) : C0 M U P →+ C0 M V P :=
  Family.relativeRestrict M.A P.vertices h.vertices

/-- Relative degree-0 restriction retains the full original included family. -/
theorem r0_val (h : ClosedRegion.Inclusion V U) (b : C0 M U P) :
    (r0 M P h b).1 = ClosedRegion.r0Between M h b.1 := rfl

/-- Restrict the same fixed-part relative degree-1 families along original-cell inclusion. -/
def r1 (h : ClosedRegion.Inclusion V U) : C1 M U P →+ C1 M V P :=
  Family.relativeRestrict (fun e : EdgeName (K := K) => M.A e.2.1) P.edges h.edges

/-- Relative degree-1 restriction retains the full original included family. -/
theorem r1_val (h : ClosedRegion.Inclusion V U) (b : C1 M U P) :
    (r1 M P h b).1 = ClosedRegion.r1Between M h b.1 := rfl

/-- Restrict the same fixed-part relative degree-2 families along original-cell inclusion. -/
def r2 (h : ClosedRegion.Inclusion V U) : C2 M U P →+ C2 M V P :=
  Family.relativeRestrict (fun f => M.A (K.twoTarget f)) P.faces h.faces

/-- Relative degree-2 restriction retains the full original included family. -/
theorem r2_val (h : ClosedRegion.Inclusion V U) (b : C2 M U P) :
    (r2 M P h b).1 = ClosedRegion.r2Between M h b.1 := rfl

/-- Restrict the same fixed-part relative degree-3 families along original-cell inclusion. -/
def r3 (h : ClosedRegion.Inclusion V U) : C3 M U P →+ C3 M V P :=
  Family.relativeRestrict (fun t => M.A (K.threeTarget t)) P.triples h.triples

/-- Relative degree-3 restriction retains the full original included family. -/
theorem r3_val (h : ClosedRegion.Inclusion V U) (b : C3 M U P) :
    (r3 M P h b).1 = ClosedRegion.r3Between M h b.1 := rfl

/-- Relative restriction and the same original d0 commute as full homomorphisms. -/
theorem r_d0 (h : ClosedRegion.Inclusion V U) (b : C0 M U P) :
    r1 M P h (d0 M U P b) = d0 M V P (r0 M P h b) :=
  Subtype.ext (ClosedRegion.inclusion_d0 M h b.1)

/-- Relative restriction and the same original d1 commute as full homomorphisms. -/
theorem r_d1 (h : ClosedRegion.Inclusion V U) (b : C1 M U P) :
    r2 M P h (d1 M U P b) = d1 M V P (r1 M P h b) :=
  Subtype.ext (ClosedRegion.inclusion_d1 M h b.1)

/-- Relative restriction and the same original d2 commute as full homomorphisms. -/
theorem r_d2 (h : ClosedRegion.Inclusion V U) (b : C2 M U P) :
    r3 M P h (d2 M U P b) = d2 M V P (r2 M P h b) :=
  Subtype.ext (ClosedRegion.inclusion_d2 M h b.1)

variable (U V : ClosedRegion K)

/-- Degree-0 diagonal of the same original relative cover restrictions. -/
def diagonal0 : C0 M ClosedRegion.all P →+ C0 M U P × C0 M V P :=
  Family.coverDiagonal M.A U.vertices V.vertices P.vertices

/-- Degree-0 first-minus-second difference on the full original overlap. -/
def difference0 : C0 M U P × C0 M V P →+ C0 M (ClosedRegion.inter U V) P :=
  Family.coverDifference M.A U.vertices V.vertices P.vertices

/-- The diagonal uses the same relative restriction homomorphisms. -/
theorem diagonal0_eq : diagonal0 M P U V =
    (r0 M P (ClosedRegion.toAll U)).prod (r0 M P (ClosedRegion.toAll V)) := rfl

/-- The overlap difference uses the same full relative restrictions. -/
theorem difference0_eq : difference0 M P U V =
    (r0 M P (ClosedRegion.interLeft U V)).comp (AddMonoidHom.fst _ _) -
    (r0 M P (ClosedRegion.interRight U V)).comp (AddMonoidHom.snd _ _) := rfl

/-- Equal original cover restrictions have zero degree-0 difference. -/
theorem difference0_diagonal0 (b : C0 M ClosedRegion.all P) :
    difference0 M P U V (diagonal0 M P U V b) = 0 :=
  Family.cover_difference_diagonal M.A U.vertices V.vertices P.vertices b

/-- Degree-0 cover restriction is injective on all original relative values. -/
theorem diagonal0_injective (hc : ClosedRegion.Cover U V) :
    Function.Injective (diagonal0 M P U V) :=
  Family.cover_diagonal_injective M.A U.vertices V.vertices P.vertices hc.vertices

/-- Every relative overlap value is an actual degree-0 difference of local families. -/
theorem difference0_surjective : Function.Surjective (difference0 M P U V) :=
  Family.cover_difference_surjective M.A U.vertices V.vertices P.vertices

/-- Degree-0 exactness is generated by gluing every original value, keeping fixed P. -/
theorem degree0_exact (hc : ClosedRegion.Cover U V) :
    Function.Exact (diagonal0 M P U V) (difference0 M P U V) :=
  Family.cover_exact M.A U.vertices V.vertices P.vertices hc.vertices

/-- Degree-1 diagonal of the same original relative cover restrictions. -/
def diagonal1 : C1 M ClosedRegion.all P →+ C1 M U P × C1 M V P :=
  Family.coverDiagonal (fun e : EdgeName (K := K) => M.A e.2.1) U.edges V.edges P.edges

/-- Degree-1 first-minus-second difference on the full original overlap. -/
def difference1 : C1 M U P × C1 M V P →+ C1 M (ClosedRegion.inter U V) P :=
  Family.coverDifference (fun e : EdgeName (K := K) => M.A e.2.1) U.edges V.edges P.edges

/-- The diagonal uses the same relative restriction homomorphisms. -/
theorem diagonal1_eq : diagonal1 M P U V =
    (r1 M P (ClosedRegion.toAll U)).prod (r1 M P (ClosedRegion.toAll V)) := rfl

/-- The overlap difference uses the same full relative restrictions. -/
theorem difference1_eq : difference1 M P U V =
    (r1 M P (ClosedRegion.interLeft U V)).comp (AddMonoidHom.fst _ _) -
    (r1 M P (ClosedRegion.interRight U V)).comp (AddMonoidHom.snd _ _) := rfl

/-- Equal original cover restrictions have zero degree-1 difference. -/
theorem difference1_diagonal1 (b : C1 M ClosedRegion.all P) :
    difference1 M P U V (diagonal1 M P U V b) = 0 :=
  Family.cover_difference_diagonal (fun e : EdgeName (K := K) => M.A e.2.1) U.edges V.edges P.edges b

/-- Degree-1 cover restriction is injective on all original relative values. -/
theorem diagonal1_injective (hc : ClosedRegion.Cover U V) :
    Function.Injective (diagonal1 M P U V) :=
  Family.cover_diagonal_injective (fun e : EdgeName (K := K) => M.A e.2.1) U.edges V.edges P.edges hc.edges

/-- Every relative overlap value is an actual degree-1 difference of local families. -/
theorem difference1_surjective : Function.Surjective (difference1 M P U V) :=
  Family.cover_difference_surjective (fun e : EdgeName (K := K) => M.A e.2.1) U.edges V.edges P.edges

/-- Degree-1 exactness is generated by gluing every original value, keeping fixed P. -/
theorem degree1_exact (hc : ClosedRegion.Cover U V) :
    Function.Exact (diagonal1 M P U V) (difference1 M P U V) :=
  Family.cover_exact (fun e : EdgeName (K := K) => M.A e.2.1) U.edges V.edges P.edges hc.edges

/-- Degree-2 diagonal of the same original relative cover restrictions. -/
def diagonal2 : C2 M ClosedRegion.all P →+ C2 M U P × C2 M V P :=
  Family.coverDiagonal (fun f => M.A (K.twoTarget f)) U.faces V.faces P.faces

/-- Degree-2 first-minus-second difference on the full original overlap. -/
def difference2 : C2 M U P × C2 M V P →+ C2 M (ClosedRegion.inter U V) P :=
  Family.coverDifference (fun f => M.A (K.twoTarget f)) U.faces V.faces P.faces

/-- The diagonal uses the same relative restriction homomorphisms. -/
theorem diagonal2_eq : diagonal2 M P U V =
    (r2 M P (ClosedRegion.toAll U)).prod (r2 M P (ClosedRegion.toAll V)) := rfl

/-- The overlap difference uses the same full relative restrictions. -/
theorem difference2_eq : difference2 M P U V =
    (r2 M P (ClosedRegion.interLeft U V)).comp (AddMonoidHom.fst _ _) -
    (r2 M P (ClosedRegion.interRight U V)).comp (AddMonoidHom.snd _ _) := rfl

/-- Equal original cover restrictions have zero degree-2 difference. -/
theorem difference2_diagonal2 (b : C2 M ClosedRegion.all P) :
    difference2 M P U V (diagonal2 M P U V b) = 0 :=
  Family.cover_difference_diagonal (fun f => M.A (K.twoTarget f)) U.faces V.faces P.faces b

/-- Degree-2 cover restriction is injective on all original relative values. -/
theorem diagonal2_injective (hc : ClosedRegion.Cover U V) :
    Function.Injective (diagonal2 M P U V) :=
  Family.cover_diagonal_injective (fun f => M.A (K.twoTarget f)) U.faces V.faces P.faces hc.faces

/-- Every relative overlap value is an actual degree-2 difference of local families. -/
theorem difference2_surjective : Function.Surjective (difference2 M P U V) :=
  Family.cover_difference_surjective (fun f => M.A (K.twoTarget f)) U.faces V.faces P.faces

/-- Degree-2 exactness is generated by gluing every original value, keeping fixed P. -/
theorem degree2_exact (hc : ClosedRegion.Cover U V) :
    Function.Exact (diagonal2 M P U V) (difference2 M P U V) :=
  Family.cover_exact (fun f => M.A (K.twoTarget f)) U.faces V.faces P.faces hc.faces

/-- Degree-3 diagonal of the same original relative cover restrictions. -/
def diagonal3 : C3 M ClosedRegion.all P →+ C3 M U P × C3 M V P :=
  Family.coverDiagonal (fun t => M.A (K.threeTarget t)) U.triples V.triples P.triples

/-- Degree-3 first-minus-second difference on the full original overlap. -/
def difference3 : C3 M U P × C3 M V P →+ C3 M (ClosedRegion.inter U V) P :=
  Family.coverDifference (fun t => M.A (K.threeTarget t)) U.triples V.triples P.triples

/-- The diagonal uses the same relative restriction homomorphisms. -/
theorem diagonal3_eq : diagonal3 M P U V =
    (r3 M P (ClosedRegion.toAll U)).prod (r3 M P (ClosedRegion.toAll V)) := rfl

/-- The overlap difference uses the same full relative restrictions. -/
theorem difference3_eq : difference3 M P U V =
    (r3 M P (ClosedRegion.interLeft U V)).comp (AddMonoidHom.fst _ _) -
    (r3 M P (ClosedRegion.interRight U V)).comp (AddMonoidHom.snd _ _) := rfl

/-- Equal original cover restrictions have zero degree-3 difference. -/
theorem difference3_diagonal3 (b : C3 M ClosedRegion.all P) :
    difference3 M P U V (diagonal3 M P U V b) = 0 :=
  Family.cover_difference_diagonal (fun t => M.A (K.threeTarget t)) U.triples V.triples P.triples b

/-- Degree-3 cover restriction is injective on all original relative values. -/
theorem diagonal3_injective (hc : ClosedRegion.Cover U V) :
    Function.Injective (diagonal3 M P U V) :=
  Family.cover_diagonal_injective (fun t => M.A (K.threeTarget t)) U.triples V.triples P.triples hc.triples

/-- Every relative overlap value is an actual degree-3 difference of local families. -/
theorem difference3_surjective : Function.Surjective (difference3 M P U V) :=
  Family.cover_difference_surjective (fun t => M.A (K.threeTarget t)) U.triples V.triples P.triples

/-- Degree-3 exactness is generated by gluing every original value, keeping fixed P. -/
theorem degree3_exact (hc : ClosedRegion.Cover U V) :
    Function.Exact (diagonal3 M P U V) (difference3 M P U V) :=
  Family.cover_exact (fun t => M.A (K.threeTarget t)) U.triples V.triples P.triples hc.triples

/-- The product differential on both local relative degree-0 families. -/
noncomputable def pairD0 : C0 M U P × C0 M V P →+
    C1 M U P × C1 M V P :=
  ((d0 M U P).comp (AddMonoidHom.fst _ _)).prod
    ((d0 M V P).comp (AddMonoidHom.snd _ _))

/-- The cover diagonal commutes with the complete original d0. -/
theorem diagonal_d0 (b : C0 M ClosedRegion.all P) :
    diagonal1 M P U V (d0 M ClosedRegion.all P b) =
      pairD0 M P U V (diagonal0 M P U V b) :=
  Prod.ext (r_d0 M P (ClosedRegion.toAll U) b) (r_d0 M P (ClosedRegion.toAll V) b)

/-- The same first-minus-second overlap map commutes with full d0. -/
theorem difference_d0 (b : C0 M U P × C0 M V P) :
    difference1 M P U V (pairD0 M P U V b) =
      d0 M (ClosedRegion.inter U V) P (difference0 M P U V b) := by
  rw [difference1_eq,difference0_eq]
  change r1 M P (ClosedRegion.interLeft U V) (d0 M U P b.1) -
    r1 M P (ClosedRegion.interRight U V) (d0 M V P b.2) =
    d0 M (ClosedRegion.inter U V) P
      (r0 M P (ClosedRegion.interLeft U V) b.1 - r0 M P (ClosedRegion.interRight U V) b.2)
  rw [r_d0,r_d0,map_sub]

/-- The product differential on both local relative degree-1 families. -/
noncomputable def pairD1 : C1 M U P × C1 M V P →+
    C2 M U P × C2 M V P :=
  ((d1 M U P).comp (AddMonoidHom.fst _ _)).prod
    ((d1 M V P).comp (AddMonoidHom.snd _ _))

/-- The cover diagonal commutes with the complete original d1. -/
theorem diagonal_d1 (b : C1 M ClosedRegion.all P) :
    diagonal2 M P U V (d1 M ClosedRegion.all P b) =
      pairD1 M P U V (diagonal1 M P U V b) :=
  Prod.ext (r_d1 M P (ClosedRegion.toAll U) b) (r_d1 M P (ClosedRegion.toAll V) b)

/-- The same first-minus-second overlap map commutes with full d1. -/
theorem difference_d1 (b : C1 M U P × C1 M V P) :
    difference2 M P U V (pairD1 M P U V b) =
      d1 M (ClosedRegion.inter U V) P (difference1 M P U V b) := by
  rw [difference2_eq,difference1_eq]
  change r2 M P (ClosedRegion.interLeft U V) (d1 M U P b.1) -
    r2 M P (ClosedRegion.interRight U V) (d1 M V P b.2) =
    d1 M (ClosedRegion.inter U V) P
      (r1 M P (ClosedRegion.interLeft U V) b.1 - r1 M P (ClosedRegion.interRight U V) b.2)
  rw [r_d1,r_d1,map_sub]

/-- The product differential on both local relative degree-2 families. -/
noncomputable def pairD2 : C2 M U P × C2 M V P →+
    C3 M U P × C3 M V P :=
  ((d2 M U P).comp (AddMonoidHom.fst _ _)).prod
    ((d2 M V P).comp (AddMonoidHom.snd _ _))

/-- The cover diagonal commutes with the complete original d2. -/
theorem diagonal_d2 (b : C2 M ClosedRegion.all P) :
    diagonal3 M P U V (d2 M ClosedRegion.all P b) =
      pairD2 M P U V (diagonal2 M P U V b) :=
  Prod.ext (r_d2 M P (ClosedRegion.toAll U) b) (r_d2 M P (ClosedRegion.toAll V) b)

/-- The same first-minus-second overlap map commutes with full d2. -/
theorem difference_d2 (b : C2 M U P × C2 M V P) :
    difference3 M P U V (pairD2 M P U V b) =
      d2 M (ClosedRegion.inter U V) P (difference2 M P U V b) := by
  rw [difference3_eq,difference2_eq]
  change r3 M P (ClosedRegion.interLeft U V) (d2 M U P b.1) -
    r3 M P (ClosedRegion.interRight U V) (d2 M V P b.2) =
    d2 M (ClosedRegion.inter U V) P
      (r2 M P (ClosedRegion.interLeft U V) b.1 - r2 M P (ClosedRegion.interRight U V) b.2)
  rw [r_d2,r_d2,map_sub]

/-- Original relative coefficient groups in degrees zero through three. -/
def cochainObject : ℕ → Ab
  | 0 => AddCommGrpCat.of (C0 M U P)
  | 1 => AddCommGrpCat.of (C1 M U P)
  | 2 => AddCommGrpCat.of (C2 M U P)
  | 3 => AddCommGrpCat.of (C3 M U P)
  | _ => AddCommGrpCat.of PUnit

/-- The same three relative differentials, zero beyond the original three-cells. -/
noncomputable def cochainDifferential : ∀ n : ℕ,
    cochainObject M P U n ⟶ cochainObject M P U (n + 1)
  | 0 => AddCommGrpCat.ofHom (d0 M U P)
  | 1 => AddCommGrpCat.ofHom (d1 M U P)
  | 2 => AddCommGrpCat.ofHom (d2 M U P)
  | _ + 3 => 0

/-- The same original-index relative groups form a native four-term cochain complex. -/
noncomputable def cochainComplex : CochainComplex Ab ℕ :=
  CochainComplex.of (cochainObject M P U) (cochainDifferential M P U) (by
    intro n
    rcases n with _ | _ | n
    · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
      exact d1_d0 M U P
    · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
      exact d2_d1 M U P
    · cases n <;> rfl)

/-- Degreewise pairs of both local relative coefficient groups. -/
def pairObject : ℕ → Ab
  | 0 => AddCommGrpCat.of (C0 M U P × C0 M V P)
  | 1 => AddCommGrpCat.of (C1 M U P × C1 M V P)
  | 2 => AddCommGrpCat.of (C2 M U P × C2 M V P)
  | 3 => AddCommGrpCat.of (C3 M U P × C3 M V P)
  | _ => AddCommGrpCat.of PUnit

/-- Product of the actual local relative differentials. -/
noncomputable def pairDifferential : ∀ n : ℕ,
    pairObject M P U V n ⟶ pairObject M P U V (n + 1)
  | 0 => AddCommGrpCat.ofHom (pairD0 M P U V)
  | 1 => AddCommGrpCat.ofHom (pairD1 M P U V)
  | 2 => AddCommGrpCat.ofHom (pairD2 M P U V)
  | _ + 3 => 0

/-- The full local pairs form a native cochain complex with their product differential. -/
noncomputable def pairComplex : CochainComplex Ab ℕ :=
  CochainComplex.of (pairObject M P U V) (pairDifferential M P U V) (by
    intro n
    rcases n with _ | _ | n
    · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
      exact Prod.ext (d1_d0 M U P b.1) (d1_d0 M V P b.2)
    · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
      exact Prod.ext (d2_d1 M U P b.1) (d2_d1 M V P b.2)
    · cases n <;> rfl)

/-- The same cover diagonal on each original degree. -/
def diagonalComponent : ∀ n : ℕ,
    cochainObject M P ClosedRegion.all n ⟶ pairObject M P U V n
  | 0 => AddCommGrpCat.ofHom (diagonal0 M P U V)
  | 1 => AddCommGrpCat.ofHom (diagonal1 M P U V)
  | 2 => AddCommGrpCat.ofHom (diagonal2 M P U V)
  | 3 => AddCommGrpCat.ofHom (diagonal3 M P U V)
  | _ + 4 => 𝟙 _

/-- The same first-minus-second difference on each original degree. -/
def differenceComponent : ∀ n : ℕ,
    pairObject M P U V n ⟶ cochainObject M P (ClosedRegion.inter U V) n
  | 0 => AddCommGrpCat.ofHom (difference0 M P U V)
  | 1 => AddCommGrpCat.ofHom (difference1 M P U V)
  | 2 => AddCommGrpCat.ofHom (difference2 M P U V)
  | 3 => AddCommGrpCat.ofHom (difference3 M P U V)
  | _ + 4 => 𝟙 _

/-- Original cover restriction commutes with the entire native differential. -/
theorem diagonal_component_comm (n : ℕ) :
    diagonalComponent M P U V n ≫ pairDifferential M P U V n =
      cochainDifferential M P ClosedRegion.all n ≫ diagonalComponent M P U V (n+1) := by
  rcases n with _ | _ | _ | n
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (diagonal_d0 M P U V b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (diagonal_d1 M P U V b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (diagonal_d2 M P U V b).symm
  · change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [Limits.comp_zero,Limits.zero_comp]

/-- The overlap difference commutes with the entire native differential. -/
theorem difference_component_comm (n : ℕ) :
    differenceComponent M P U V n ≫ cochainDifferential M P (ClosedRegion.inter U V) n =
      pairDifferential M P U V n ≫ differenceComponent M P U V (n+1) := by
  rcases n with _ | _ | _ | n
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (difference_d0 M P U V b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (difference_d1 M P U V b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (difference_d2 M P U V b).symm
  · change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [Limits.comp_zero,Limits.zero_comp]

/-- The diagonal is a native map of the same complete relative complexes. -/
noncomputable def diagonalMap : cochainComplex M P ClosedRegion.all ⟶ pairComplex M P U V :=
  CochainComplex.ofHom _ _ _ _ _ _ (diagonalComponent M P U V)
    (diagonal_component_comm M P U V)

/-- The overlap difference is a native map of the same complete relative complexes. -/
noncomputable def differenceMap : pairComplex M P U V ⟶ cochainComplex M P (ClosedRegion.inter U V) :=
  CochainComplex.ofHom _ _ _ _ _ _ (differenceComponent M P U V)
    (difference_component_comm M P U V)

/-- The overlap difference of a global restriction vanishes in every native degree. -/
theorem diagonal_map_difference_map : diagonalMap M P U V ≫ differenceMap M P U V = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  rcases n with _ | _ | _ | _ | n
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact difference0_diagonal0 M P U V
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact difference1_diagonal1 M P U V
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact difference2_diagonal2 M P U V
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact difference3_diagonal3 M P U V
  · rfl

/-- Native short complex of same-fixed-part global, local-pair and overlap cochains. -/
noncomputable def coverShortComplex : ShortComplex (CochainComplex Ab ℕ) where
  X₁ := cochainComplex M P ClosedRegion.all
  X₂ := pairComplex M P U V
  X₃ := cochainComplex M P (ClosedRegion.inter U V)
  f := diagonalMap M P U V
  g := differenceMap M P U V
  zero := diagonal_map_difference_map M P U V

/-- Degree 0 of the native cover short complex is short exact by original-value gluing. -/
theorem cover_short_exact_degree0 (hc : ClosedRegion.Cover U V) :
    ((coverShortComplex M P U V).map (HomologicalComplex.eval Ab (ComplexShape.up ℕ) 0)).ShortExact where
  exact := (ShortComplex.ab_exact_iff_function_exact _).mpr (degree0_exact M P U V hc)
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (diagonal0_injective M P U V hc)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (difference0_surjective M P U V)

/-- Degree 1 of the native cover short complex is short exact by original-value gluing. -/
theorem cover_short_exact_degree1 (hc : ClosedRegion.Cover U V) :
    ((coverShortComplex M P U V).map (HomologicalComplex.eval Ab (ComplexShape.up ℕ) 1)).ShortExact where
  exact := (ShortComplex.ab_exact_iff_function_exact _).mpr (degree1_exact M P U V hc)
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (diagonal1_injective M P U V hc)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (difference1_surjective M P U V)

/-- Degree 2 of the native cover short complex is short exact by original-value gluing. -/
theorem cover_short_exact_degree2 (hc : ClosedRegion.Cover U V) :
    ((coverShortComplex M P U V).map (HomologicalComplex.eval Ab (ComplexShape.up ℕ) 2)).ShortExact where
  exact := (ShortComplex.ab_exact_iff_function_exact _).mpr (degree2_exact M P U V hc)
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (diagonal2_injective M P U V hc)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (difference2_surjective M P U V)

/-- Degree 3 of the native cover short complex is short exact by original-value gluing. -/
theorem cover_short_exact_degree3 (hc : ClosedRegion.Cover U V) :
    ((coverShortComplex M P U V).map (HomologicalComplex.eval Ab (ComplexShape.up ℕ) 3)).ShortExact where
  exact := (ShortComplex.ab_exact_iff_function_exact _).mpr (degree3_exact M P U V hc)
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (diagonal3_injective M P U V hc)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (difference3_surjective M P U V)

/-- The complete native relative cover sequence is short exact at every degree. -/
theorem cover_short_exact (hc : ClosedRegion.Cover U V) :
    (coverShortComplex M P U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  rcases n with _ | _ | _ | _ | n
  · exact cover_short_exact_degree0 M P U V hc
  · exact cover_short_exact_degree1 M P U V hc
  · exact cover_short_exact_degree2 M P U V hc
  · exact cover_short_exact_degree3 M P U V hc
  · refine {exact := ?_,mono_f := ?_,epi_g := ?_}
    · apply (ShortComplex.ab_exact_iff_function_exact _).mpr
      intro b
      constructor
      · intro _; exact ⟨b,rfl⟩
      · intro _; rfl
    · apply (AddCommGrpCat.mono_iff_injective _).mpr
      exact Function.injective_id
    · apply (AddCommGrpCat.epi_iff_surjective _).mpr
      exact Function.surjective_id

/-- Native supported degree zero with all candidates allowed is the same fixed-part kernel. -/
noncomputable def nativeSupported0 : C0 M U P ≃+
    RelativeComplex.C0Group (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅ :=
  (native0 M U P).trans (AddEquiv.addSubgroupCongr
    (RelativeComplex.C0Group_all _ _ ∅).symm)

/-- Native supported degree one with all candidates allowed is the same fixed-part kernel. -/
noncomputable def nativeSupported1 : C1 M U P ≃+
    RelativeComplex.C1Group (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅ :=
  (native1 M U P).trans (AddEquiv.addSubgroupCongr
    (RelativeComplex.C1Group_all _ _ ∅).symm)

/-- The native degree-zero comparison preserves every original vertex value. -/
theorem native_supported0_val (b : C0 M U P) : (nativeSupported0 M P U b).1 = b.1 := rfl

/-- The native degree-one comparison retains every original edge through reindexing. -/
theorem native_supported1_val (b : C1 M U P) :
    (nativeSupported1 M P U b).1 = (ClosedRegion.nativeC1Equiv U M).symm b.1 := rfl

/-- The full supported native degree-zero differential agrees under the original-index comparison. -/
theorem native_supported_d0 (b : C0 M U P) :
    nativeSupported1 M P U (d0 M U P b) =
      RelativeComplex.d0Supported (ClosedRegion.restrictCoefficients U M)
        (ClosedRegion.nativeIntersection U P) ∅ ∅ (nativeSupported0 M P U b) := by
  apply Subtype.ext
  change (ClosedRegion.nativeC1Equiv U M).symm (ClosedRegion.d0Hom M U b.1) =
    AbelianLiftingObstruction.d0 (ClosedRegion.restrictCoefficients U M) b.1
  apply (ClosedRegion.nativeC1Equiv U M).injective
  simpa only [AddEquiv.apply_symm_apply] using (ClosedRegion.native_d0_eq U M b.1).symm

/-- The full supported native face differential agrees under the same edge reindexing. -/
theorem native_supported_d1 (b : C1 M U P) :
    native2 M U P (d1 M U P b) =
      RelativeComplex.d1Supported (ClosedRegion.restrictCoefficients U M)
        (ClosedRegion.nativeIntersection U P) ∅ ∅ (nativeSupported1 M P U b) := by
  apply Subtype.ext
  exact (ClosedRegion.native_d1_eq U M b.1).symm

/-- Both complete three-cell routes give the same native relative differential. -/
theorem native_supported_d2 (b : C2 M U P) :
    native3 M U P (d2 M U P b) =
      RelativeComplex.d2Relative (ClosedRegion.restrictCoefficients U M)
        (ClosedRegion.nativeIntersection U P) (native2 M U P b) := by
  apply Subtype.ext
  exact (ClosedRegion.native_d2_eq U M b.1).symm

/-- Native degree isomorphisms to the accepted full relative complex on the original restricted tower. -/
noncomputable def nativeComponentIso : ∀ n : ℕ, cochainObject M P U n ≅
    RelativeComplex.cochainObject (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅ n
  | 0 => (nativeSupported0 M P U).toAddCommGrpIso
  | 1 => (nativeSupported1 M P U).toAddCommGrpIso
  | 2 => (native2 M U P).toAddCommGrpIso
  | 3 => (native3 M U P).toAddCommGrpIso
  | _ + 4 => Iso.refl _

/-- Every native degree isomorphism commutes with the same complete relative differential. -/
theorem native_component_comm (n : ℕ) :
    (nativeComponentIso M P U n).hom ≫
      RelativeComplex.cochainDifferential (ClosedRegion.restrictCoefficients U M)
        (ClosedRegion.nativeIntersection U P) ∅ ∅ n =
    cochainDifferential M P U n ≫ (nativeComponentIso M P U (n+1)).hom := by
  rcases n with _ | _ | _ | n
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (native_supported_d0 M P U b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (native_supported_d1 M P U b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (native_supported_d2 M P U b).symm
  · change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [Limits.comp_zero,Limits.zero_comp]

/-- The whole native complex is isomorphic to the accepted relative complex of the actual restricted presentation. -/
noncomputable def nativeComplexIso : cochainComplex M P U ≅
    RelativeComplex.cochainComplex (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅ :=
  HomologicalComplex.Hom.isoOfComponents (nativeComponentIso M P U) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    simpa only [cochainComplex, RelativeComplex.cochainComplex, CochainComplex.of_d] using
      native_component_comm M P U i)

/-- Full original degree-0 relative families are the kernel on the original presentation itself. -/
def original0 : C0 M ClosedRegion.all P ≃+ RelativeComplex.relativeC0 M P :=
  Family.univRelativeEquiv M.A P.vertices

/-- Restricting the original degree-0 comparison back to all cells retains the complete family. -/
theorem original0_restrict (b : C0 M ClosedRegion.all P) :
    ClosedRegion.r0 M ClosedRegion.all (original0 M P b).1 = b.1 := by
  funext i
  rfl

/-- Full original degree-1 relative families are the kernel on the original presentation itself. -/
def original1 : C1 M ClosedRegion.all P ≃+ RelativeComplex.relativeC1 M P :=
  Family.univRelativeEquiv (fun e : EdgeName (K := K) => M.A e.2.1) P.edges

/-- Restricting the original degree-1 comparison back to all cells retains the complete family. -/
theorem original1_restrict (b : C1 M ClosedRegion.all P) :
    ClosedRegion.r1 M ClosedRegion.all (original1 M P b).1 = b.1 := by
  funext i
  rfl

/-- Full original degree-2 relative families are the kernel on the original presentation itself. -/
def original2 : C2 M ClosedRegion.all P ≃+ RelativeComplex.relativeC2 M P :=
  Family.univRelativeEquiv (fun f => M.A (K.twoTarget f)) P.faces

/-- Restricting the original degree-2 comparison back to all cells retains the complete family. -/
theorem original2_restrict (b : C2 M ClosedRegion.all P) :
    ClosedRegion.r2 M ClosedRegion.all (original2 M P b).1 = b.1 := by
  funext i
  rfl

/-- Full original degree-3 relative families are the kernel on the original presentation itself. -/
def original3 : C3 M ClosedRegion.all P ≃+ RelativeComplex.relativeC3 M P :=
  Family.univRelativeEquiv (fun t => M.A (K.threeTarget t)) P.triples

/-- Restricting the original degree-3 comparison back to all cells retains the complete family. -/
theorem original3_restrict (b : C3 M ClosedRegion.all P) :
    ClosedRegion.r3 M ClosedRegion.all (original3 M P b).1 = b.1 := by
  funext i
  rfl

/-- The degree-0 comparison preserves the actual original differential, not only its restriction. -/
theorem original_d0 (b : C0 M ClosedRegion.all P) :
    original1 M P (d0 M ClosedRegion.all P b) =
      ⟨AbelianLiftingObstruction.d0 M (original0 M P b).1,
        RelativeComplex.d0_mem_relative M P (original0 M P b)⟩ := by
  apply Subtype.ext
  apply Family.restrict_univ_injective (fun e : EdgeName (K := K) => M.A e.2.1)
  change ClosedRegion.r1 M ClosedRegion.all (original1 M P (d0 M ClosedRegion.all P b)).1 =
    ClosedRegion.r1 M ClosedRegion.all (AbelianLiftingObstruction.d0 M (original0 M P b).1)
  rw [original1_restrict,ClosedRegion.r_d0,original0_restrict]
  rfl

/-- The degree-1 comparison preserves the actual original differential, not only its restriction. -/
theorem original_d1 (b : C1 M ClosedRegion.all P) :
    original2 M P (d1 M ClosedRegion.all P b) =
      ⟨AbelianLiftingObstruction.d1 M (original1 M P b).1,
        RelativeComplex.d1_mem_relative M P (original1 M P b)⟩ := by
  apply Subtype.ext
  apply Family.restrict_univ_injective (fun f => M.A (K.twoTarget f))
  change ClosedRegion.r2 M ClosedRegion.all (original2 M P (d1 M ClosedRegion.all P b)).1 =
    ClosedRegion.r2 M ClosedRegion.all (AbelianLiftingObstruction.d1 M (original1 M P b).1)
  rw [original2_restrict,ClosedRegion.r_d1,original1_restrict]
  rfl

/-- The degree-2 comparison preserves the actual original differential, not only its restriction. -/
theorem original_d2 (b : C2 M ClosedRegion.all P) :
    original3 M P (d2 M ClosedRegion.all P b) =
      ⟨AbelianLiftingObstruction.d2 M (original2 M P b).1,
        RelativeComplex.d2_mem_relative M P (original2 M P b)⟩ := by
  apply Subtype.ext
  apply Family.restrict_univ_injective (fun t => M.A (K.threeTarget t))
  change ClosedRegion.r3 M ClosedRegion.all (original3 M P (d2 M ClosedRegion.all P b)).1 =
    ClosedRegion.r3 M ClosedRegion.all (AbelianLiftingObstruction.d2 M (original2 M P b).1)
  rw [original3_restrict,ClosedRegion.r_d2,original2_restrict]
  rfl

/-- The original supported degree 0, with all candidates allowed, retains the original relative kernel. -/
def originalSupported0 : C0 M ClosedRegion.all P ≃+ RelativeComplex.C0Group M P ∅ ∅ :=
  (original0 M P).trans (AddEquiv.addSubgroupCongr (RelativeComplex.C0Group_all M P ∅).symm)

/-- The original supported degree 1, with all candidates allowed, retains the original relative kernel. -/
def originalSupported1 : C1 M ClosedRegion.all P ≃+ RelativeComplex.C1Group M P ∅ ∅ :=
  (original1 M P).trans (AddEquiv.addSubgroupCongr (RelativeComplex.C1Group_all M P ∅).symm)

/-- The complete original supported degree-0 differential is preserved by reindexing all cells. -/
theorem original_supported_d0 (b : C0 M ClosedRegion.all P) :
    originalSupported1 M P (d0 M ClosedRegion.all P b) =
      RelativeComplex.d0Supported M P ∅ ∅ (originalSupported0 M P b) := by
  apply Subtype.ext
  exact congrArg (fun z : RelativeComplex.relativeC1 M P => z.1) (original_d0 M P b)

/-- The complete original supported degree-1 differential is preserved by reindexing all cells. -/
theorem original_supported_d1 (b : C1 M ClosedRegion.all P) :
    original2 M P (d1 M ClosedRegion.all P b) =
      RelativeComplex.d1Supported M P ∅ ∅ (originalSupported1 M P b) := by
  apply Subtype.ext
  exact congrArg Subtype.val (original_d1 M P b)

/-- The complete original supported degree-2 differential is preserved by reindexing all cells. -/
theorem original_supported_d2 (b : C2 M ClosedRegion.all P) :
    original3 M P (d2 M ClosedRegion.all P b) =
      RelativeComplex.d2Relative M P (original2 M P b) := by
  apply Subtype.ext
  exact congrArg Subtype.val (original_d2 M P b)

/-- Components of the direct isomorphism to the accepted original K relative complex. -/
noncomputable def originalComponentIso : ∀ n : ℕ,
    cochainObject M P ClosedRegion.all n ≅ RelativeComplex.cochainObject M P ∅ ∅ n
  | 0 => (originalSupported0 M P).toAddCommGrpIso
  | 1 => (originalSupported1 M P).toAddCommGrpIso
  | 2 => (original2 M P).toAddCommGrpIso
  | 3 => (original3 M P).toAddCommGrpIso
  | _ + 4 => Iso.refl _

/-- The direct original-K comparison commutes with all three differentials. -/
theorem original_component_comm (n : ℕ) :
    (originalComponentIso M P n).hom ≫ RelativeComplex.cochainDifferential M P ∅ ∅ n =
      cochainDifferential M P ClosedRegion.all n ≫ (originalComponentIso M P (n+1)).hom := by
  rcases n with _ | _ | _ | n
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (original_supported_d0 M P b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (original_supported_d1 M P b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (original_supported_d2 M P b).symm
  · change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [Limits.comp_zero,Limits.zero_comp]

/-- The complete global original-index complex is directly isomorphic to the accepted original-K relative complex. -/
noncomputable def originalComplexIso : cochainComplex M P ClosedRegion.all ≅
    RelativeComplex.cochainComplex M P ∅ ∅ :=
  HomologicalComplex.Hom.isoOfComponents (originalComponentIso M P) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    simpa only [cochainComplex, RelativeComplex.cochainComplex, CochainComplex.of_d] using
      original_component_comm M P i)

/-- The native cover sequence starts with the accepted relative complex of the original K. -/
noncomputable def originalCoverShortComplex : ShortComplex (CochainComplex Ab ℕ) where
  X₁ := RelativeComplex.cochainComplex M P ∅ ∅
  X₂ := pairComplex M P U V
  X₃ := cochainComplex M P (ClosedRegion.inter U V)
  f := (originalComplexIso M P).inv ≫ diagonalMap M P U V
  g := differenceMap M P U V
  zero := by rw [Category.assoc,diagonal_map_difference_map,Limits.comp_zero]

/-- Direct comparison of the entire cover sequence, including both native maps. -/
noncomputable def originalCoverIso : originalCoverShortComplex M P U V ≅ coverShortComplex M P U V :=
  ShortComplex.isoMk (originalComplexIso M P).symm (Iso.refl _) (Iso.refl _)
    (by
      change (originalComplexIso M P).inv ≫ diagonalMap M P U V =
        ((originalComplexIso M P).inv ≫ diagonalMap M P U V) ≫ 𝟙 _
      rw [Category.comp_id])
    (by
      change 𝟙 _ ≫ differenceMap M P U V = differenceMap M P U V ≫ 𝟙 _
      rw [Category.id_comp,Category.comp_id])

/-- G-130 B: the same original-K relative complex has the native short exact closed-cover sequence. -/
theorem original_cover_short_exact (hc : ClosedRegion.Cover U V) :
    (originalCoverShortComplex M P U V).ShortExact :=
  ShortComplex.shortExact_of_iso (originalCoverIso M P U V).symm (cover_short_exact M P U V hc)
end RelativeCover
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
