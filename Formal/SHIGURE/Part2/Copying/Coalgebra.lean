import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Copying coalgebras

Construction 4.2 and the coalgebra side of Theorem 4.3.

## Implementation notes

The direct sum of copies of the coefficient ring is mathlib's `Finsupp` module.
Its existing coalgebra instance provides the copying and counit maps. The
finite support of each coefficient row is part of the underlying module.

Scalar extension is computed by the free-module tensor equivalence, which is
then lifted to a coalgebra map by checking the state basis. A second
presentation of the extended coalgebra would duplicate this module computation.
-/

open scoped BigOperators TensorProduct
open Coalgebra TensorProduct

noncomputable section

namespace SHIGURE.Copying

variable (R : Type*) [CommRing R]

/-- The free copying coalgebra of Construction 4.2 on an arbitrary set of states. -/
abbrev CopyCoalgebra (X : Type*) := X →₀ R

/-- The state basis of the free module in Construction 4.2. -/
def stateBasis (X : Type*) : Module.Basis X R (CopyCoalgebra R X) :=
  Finsupp.basisSingleOne

/-- The state vector of Construction 4.2. Simplify to the coefficient row with a single entry 1. -/
@[simp]
theorem stateBasis_apply {X : Type*} (x : X) :
    stateBasis R X x = Finsupp.single x 1 :=
  rfl

/-- The comultiplication formula on states in Construction 4.2.
Simplify the comultiplication of a state to its tensor square. -/
@[simp]
theorem comul_stateBasis {X : Type*} (x : X) :
    comul (R := R) (stateBasis R X x) = stateBasis R X x ⊗ₜ[R] stateBasis R X x := by
  simp

/-- The counit formula on states in Construction 4.2. Simplify the counit of a state to 1. -/
@[simp]
theorem counit_stateBasis {X : Type*} (x : X) :
    counit (R := R) (stateBasis R X x) = 1 := by
  simp

/-- Construction 4.2 linearizes a function of states as a coalgebra map. -/
def mapStates {X Y : Type*} (f : X → Y) : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y where
  toLinearMap := Finsupp.lmapDomain R R f
  counit_comp := by
    apply (stateBasis R X).ext
    intro x
    simp [Finsupp.lmapDomain_apply]
  map_comp_comul := by
    apply (stateBasis R X).ext
    intro x
    simp [Finsupp.lmapDomain_apply]

/-- The linearization of a function in Construction 4.2 sends each state vector to
the vector of its image. Simplify on state vectors. -/
@[simp]
theorem mapStates_stateBasis {X Y : Type*} (f : X → Y) (x : X) :
    mapStates R f (stateBasis R X x) = stateBasis R Y (f x) := by
  change Finsupp.lmapDomain R R f (stateBasis R X x) = _
  simp [Finsupp.lmapDomain_apply]

/-- A linear map between copying coalgebras is determined by its values on states. -/
theorem hom_ext {X Y : Type*} {f g : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y}
    (h : ∀ x, f (stateBasis R X x) = g (stateBasis R X x)) : f = g := by
  apply CoalgHom.ext
  exact LinearMap.congr_fun ((stateBasis R X).ext h)

/-- Simplify the linearization of the identity state function to the identity coalgebra map
in Construction 4.2. -/
@[simp]
theorem mapStates_id (X : Type*) : mapStates R (id : X → X) = CoalgHom.id R _ := by
  apply hom_ext R
  intro x
  simp only [mapStates_stateBasis, CoalgHom.id_apply, id_eq]

/-- Construction 4.2 sends composition of state functions to composition of coalgebra maps.
Simplify the linearization of the composite to the composite of the linearizations. -/
@[simp]
theorem mapStates_comp {X Y Z : Type*} (f : X → Y) (g : Y → Z) :
    mapStates R (g ∘ f) = (mapStates R g).comp (mapStates R f) := by
  apply hom_ext R
  intro x
  simp only [mapStates_stateBasis, CoalgHom.comp_apply, Function.comp_apply]

variable {R}

/-- The coefficient formula for the counit on the finite support, used in Theorem 4.3. -/
theorem counit_eq_sum {Y : Type*} (a : CopyCoalgebra R Y) :
    counit (R := R) a = a.sum (fun _ r => r) := by
  change Finsupp.lsum R (fun _ : Y => counit (R := R) (A := R)) a = _
  rw [Finsupp.lsum_apply]
  rfl

/-- The coordinate equivalence used to read the comultiplication in Theorem 4.3. -/
def tensorCoefficients (X Y : Type*) :
    (CopyCoalgebra R X ⊗[R] CopyCoalgebra R Y) ≃ₗ[R] CopyCoalgebra R (X × Y) :=
  finsuppTensorFinsuppLid R R X Y

/-- The coordinate of a pure tensor used in Theorem 4.3.
Simplify it to the product of the corresponding entries. -/
@[simp]
theorem tensorCoefficients_tmul_apply {X Y : Type*} (a : CopyCoalgebra R X)
    (b : CopyCoalgebra R Y) (x : X) (y : Y) :
    tensorCoefficients X Y (a ⊗ₜ[R] b) (x, y) = a x * b y := by
  simp [tensorCoefficients, smul_eq_mul]

/-- In the coordinates of Theorem 4.3, the comultiplication has the original coefficients
on the diagonal and zero off the diagonal. -/
theorem tensorCoefficients_comul_apply {Y : Type*} [DecidableEq Y]
    (a : CopyCoalgebra R Y) (y z : Y) :
    tensorCoefficients Y Y (comul (R := R) a) (y, z) =
      if y = z then a y else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply, ha, hb]
    split <;> simp
  | single i r =>
    rw [Finsupp.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
    simp only [Finsupp.lsingle_apply, tensorCoefficients_tmul_apply, Finsupp.single_apply]
    by_cases h : y = z <;> by_cases hi : i = y <;> simp_all [eq_comm]

/-- A row of a copying map in Theorem 4.3, with finite support and the equations (4.1). -/
def IsCopyRow {Y : Type*} (a : CopyCoalgebra R Y) : Prop :=
  (∀ y, IsIdempotentElem (a y)) ∧ (Pairwise fun y z => a y * a z = 0) ∧
    a.sum (fun _ r => r) = 1

/-- The algebraic step of Theorem 4.3. The equations (4.1) are equivalent to being group-like
in the free copying coalgebra. -/
theorem isGroupLikeElem_iff_isCopyRow {Y : Type*} (a : CopyCoalgebra R Y) :
    IsGroupLikeElem R a ↔ IsCopyRow a := by
  classical
  rw [isGroupLikeElem_iff, counit_eq_sum]
  constructor
  · rintro ⟨hsum, hcomul⟩
    refine ⟨fun y => ?_, fun y z hne => ?_, hsum⟩
    · have h := congrArg (fun t => tensorCoefficients Y Y t (y, y)) hcomul
      simpa [tensorCoefficients_comul_apply, IsIdempotentElem] using h.symm
    · have h := congrArg (fun t => tensorCoefficients Y Y t (y, z)) hcomul
      simpa [tensorCoefficients_comul_apply, hne] using h.symm
  · rintro ⟨hidem, hortho, hsum⟩
    refine ⟨hsum, (tensorCoefficients Y Y).injective ?_⟩
    ext ⟨y, z⟩
    simp only [tensorCoefficients_comul_apply, tensorCoefficients_tmul_apply]
    by_cases h : y = z
    · subst z
      simpa using (hidem y).symm
    · simp [h, hortho h]

/-- Construction 4.2 identifies the basis of the product of state sets with pure
tensors of the two state bases. Simplify the inverse coordinate map on one state. -/
@[simp]
theorem tensorCoefficients_symm_stateBasis {X Y : Type*} (x : X) (y : Y) :
    (tensorCoefficients (R := R) X Y).symm (stateBasis R (X × Y) (x, y)) =
      stateBasis R X x ⊗ₜ[R] stateBasis R Y y := by
  simpa only [tensorCoefficients, stateBasis_apply, one_smul] using
    (finsuppTensorFinsuppLid_symm_single_smul R R X Y (x, y) 1 1)

/-- The coalgebra morphism on which the tensor isomorphism of Construction 4.2 is based. -/
private def productCoalgebraMap (X Y : Type*) :
    CopyCoalgebra R (X × Y) →ₗc[R] CopyCoalgebra R X ⊗[R] CopyCoalgebra R Y where
  toLinearMap := (tensorCoefficients X Y).symm.toLinearMap
  counit_comp := by
    apply (stateBasis R (X × Y)).ext
    rintro ⟨x, y⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorCoefficients_symm_stateBasis,
      TensorProduct.counit_tmul, counit_stateBasis, one_smul]
  map_comp_comul := by
    apply (stateBasis R (X × Y)).ext
    rintro ⟨x, y⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, comul_stateBasis, TensorProduct.map_tmul,
      tensorCoefficients_symm_stateBasis, TensorProduct.comul_tmul,
      AlgebraTensorModule.tensorTensorTensorComm_tmul]

/-- Construction 4.2 sends a product of state sets to a tensor product of copying coalgebras. -/
def productCoalgebraEquiv (X Y : Type*) :
    CopyCoalgebra R (X × Y) ≃ₗc[R] CopyCoalgebra R X ⊗[R] CopyCoalgebra R Y :=
  CoalgEquiv.ofBijective (f := productCoalgebraMap X Y)
    (tensorCoefficients (R := R) X Y).symm.bijective

/-- The formula on state vectors for the product in Construction 4.2. Simplify to the pure tensor. -/
@[simp]
theorem productCoalgebraEquiv_stateBasis {X Y : Type*} (x : X) (y : Y) :
    productCoalgebraEquiv X Y (stateBasis R (X × Y) (x, y)) =
      stateBasis R X x ⊗ₜ[R] stateBasis R Y y :=
  tensorCoefficients_symm_stateBasis x y

/-- The single state of the empty product in Construction 4.2 gives the coefficient coalgebra. -/
def unitCoalgebraEquiv : CopyCoalgebra R PUnit ≃ₗc[R] R := by
  let f : CopyCoalgebra R PUnit →ₗc[R] R := Coalgebra.counitCoalgHom R _
  refine CoalgEquiv.ofBijective (f := f) ⟨?_, ?_⟩
  · intro a b hab
    apply Finsupp.ext
    intro i
    cases i
    have ha : ∀ (v : CopyCoalgebra R PUnit), f v = v PUnit.unit := by
      intro v
      simp [f, counit_eq_sum, Finsupp.sum_fintype]
    exact (ha a).symm.trans (hab.trans (ha b))
  · intro r
    exact ⟨Finsupp.single PUnit.unit r, by simp [f]⟩

/-- The empty product equivalence in Construction 4.2 simplifies to the counit. -/
@[simp]
theorem unitCoalgebraEquiv_apply (a : CopyCoalgebra R PUnit) :
    unitCoalgebraEquiv a = counit (R := R) a :=
  rfl

/-- The empty product equivalence sends the unique state basis vector to the unit. -/
@[simp]
theorem unitCoalgebraEquiv_stateBasis :
    unitCoalgebraEquiv (stateBasis R PUnit PUnit.unit) = 1 := by
  rw [unitCoalgebraEquiv_apply, counit_stateBasis]

/-- Over the zero ring every copying module in Theorem 4.3 is a zero module. -/
theorem subsingleton_copyCoalgebra (X : Type*) [Subsingleton R] :
    Subsingleton (CopyCoalgebra R X) :=
  inferInstance

/-- A coefficient family of Theorem 4.3 is an arbitrary family of finite-support rows satisfying
the equations (4.1). -/
abbrev CopyRows (R X Y : Type*) [CommRing R] :=
  {a : X → CopyCoalgebra R Y // ∀ x, IsCopyRow (a x)}

/-- Extend coefficient rows satisfying (4.1) to the corresponding coalgebra map of Theorem 4.3. -/
def mapOfRows {X Y : Type*} (a : CopyRows R X Y) : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y where
  toLinearMap := (stateBasis R X).constr R a.val
  counit_comp := by
    apply (stateBasis R X).ext
    intro x
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, counit_stateBasis]
    exact ((isGroupLikeElem_iff_isCopyRow _).mpr (a.property x)).counit_eq_one
  map_comp_comul := by
    apply (stateBasis R X).ext
    intro x
    simp only [LinearMap.comp_apply, comul_stateBasis, TensorProduct.map_tmul, Module.Basis.constr_basis]
    exact ((isGroupLikeElem_iff_isCopyRow _).mpr (a.property x)).comul_eq_tmul_self.symm

/-- The basis formula for `mapOfRows` in Theorem 4.3. Simplify to the chosen row. -/
@[simp]
theorem mapOfRows_stateBasis {X Y : Type*} (a : CopyRows R X Y) (x : X) :
    mapOfRows a (stateBasis R X x) = a.val x :=
  (stateBasis R X).constr_basis R a.val x

/-- The coalgebra half of Theorem 4.3. Every copying coalgebra morphism is uniquely
specified by its coefficient rows. -/
def coalgebraRowsEquiv (X Y : Type*) :
    (CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) ≃ CopyRows R X Y where
  toFun f := ⟨fun x => f (stateBasis R X x), fun x =>
    (isGroupLikeElem_iff_isCopyRow _).mp <|
      IsGroupLikeElem.map f ⟨counit_stateBasis R x, comul_stateBasis R x⟩⟩
  invFun := mapOfRows
  left_inv _ := hom_ext R fun _ => mapOfRows_stateBasis _ _
  right_inv a := Subtype.ext <| funext <| mapOfRows_stateBasis a

/-- The forward coordinate formula for the coalgebra half of Theorem 4.3.
Simplify a row to the image of its corresponding state vector. -/
@[simp]
theorem coalgebraRowsEquiv_apply {X Y : Type*} (f : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y)
    (x : X) : ((coalgebraRowsEquiv X Y) f).val x = f (stateBasis R X x) :=
  rfl

/-- The finite linear combination inducing the coalgebra map of Theorem 4.3. -/
theorem mapOfRows_apply {X Y : Type*} (a : CopyRows R X Y) (v : CopyCoalgebra R X) :
    mapOfRows a v = v.sum (fun x r => r • a.val x) := by
  change (stateBasis R X).constr R a.val v = _
  rw [Module.Basis.constr_apply]
  rfl

/-- The rows of the identity in Theorem 4.3. Simplify to the unit coefficient at the source. -/
@[simp]
theorem coalgebraRowsEquiv_id {X : Type*} (x : X) :
    ((coalgebraRowsEquiv X X) (CoalgHom.id R _)).val x = Finsupp.single x 1 :=
  rfl

/-- Composition in the coalgebra half of Theorem 4.3 is the finite linear combination of the
second rows with coefficients from the first row. -/
theorem coalgebraRowsEquiv_comp {X Y Z : Type*} (f : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y)
    (g : CopyCoalgebra R Y →ₗc[R] CopyCoalgebra R Z) (x : X) :
    ((coalgebraRowsEquiv X Z) (g.comp f)).val x =
      (((coalgebraRowsEquiv X Y) f).val x).sum
        (fun y r => r • ((coalgebraRowsEquiv Y Z) g).val y) := by
  have h := mapOfRows_apply ((coalgebraRowsEquiv Y Z) g) (f (stateBasis R X x))
  change (coalgebraRowsEquiv Y Z).symm ((coalgebraRowsEquiv Y Z) g) (f (stateBasis R X x)) = _ at h
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- In the nonzero case of Theorem 4.3, counit 1 forces a nonzero coefficient. If the only
idempotents are 0 and 1, this forces a unit coefficient, and orthogonality forces uniqueness. -/
private theorem exists_unique_unit_entry {Y : Type*} [Nontrivial R]
    (h01 : ∀ r : R, IsIdempotentElem r → r = 0 ∨ r = 1)
    {a : CopyCoalgebra R Y} (ha : IsCopyRow a) : ∃! y, a y = 1 := by
  have hex : ∃ y, a y = 1 := by
    by_contra! h
    have hz : a = 0 := Finsupp.ext fun y =>
      (h01 (a y) (ha.1 y)).resolve_right (h y)
    have hs := ha.2.2
    simp [hz] at hs
  obtain ⟨y, hy⟩ := hex
  refine ⟨y, hy, fun z hz => ?_⟩
  by_contra hne
  have h := ha.2.1 hne
  simp [hz, hy] at h

/-- An orthogonal row with a unit entry is that state vector. This is the reconstruction used
for the nonzero case of Theorem 4.3. -/
private theorem row_eq_stateBasis {Y : Type*} {a : CopyCoalgebra R Y} (ha : IsCopyRow a)
    {y : Y} (hy : a y = 1) : a = stateBasis R Y y := by
  classical
  apply Finsupp.ext
  intro z
  by_cases hzy : z = y
  · subst z
    simpa using hy
  · have h : a z * a y = 0 := ha.2.1 hzy
    rw [hy, mul_one] at h
    simpa [Finsupp.single_apply, Ne.symm hzy] using h

/-- Under the nonzero and idempotent hypotheses of Theorem 4.3, all copying coalgebra maps
are obtained uniquely by linearizing functions of the states. -/
def stateMapsEquiv (X Y : Type*) [Nontrivial R]
    (h01 : ∀ r : R, IsIdempotentElem r → r = 0 ∨ r = 1) :
    (X → Y) ≃ (CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) := by
  classical
  refine Equiv.ofBijective (mapStates R) ⟨?_, ?_⟩
  · intro f g h
    funext x
    have hs : stateBasis R Y (f x) = stateBasis R Y (g x) := by
      rw [← mapStates_stateBasis R f x, ← mapStates_stateBasis R g x, h]
    by_contra hne
    have hcoeff : (stateBasis R Y (f x)) (f x) = (stateBasis R Y (g x)) (f x) :=
      congrArg (fun v : CopyCoalgebra R Y => v (f x)) hs
    simp [Ne.symm hne] at hcoeff
  · intro f
    let a := (coalgebraRowsEquiv X Y) f
    let y (x : X) := Classical.choose (exists_unique_unit_entry h01 (a.property x))
    refine ⟨y, hom_ext R fun x => ?_⟩
    rw [mapStates_stateBasis]
    exact (row_eq_stateBasis (a.property x)
      (Classical.choose_spec (exists_unique_unit_entry h01 (a.property x))).1).symm

/-- With no source states, the row type of Theorem 4.3 has one element. -/
def emptySourceRows (X Y : Type*) [IsEmpty X] : Unique (CopyRows R X Y) where
  default := ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  uniq _ := Subtype.ext (funext fun x => isEmptyElim x)

/-- A nonzero coefficient ring and a nonempty source cannot have a copying map
to an empty set of states in Theorem 4.3. -/
theorem isEmpty_rows_of_isEmpty_target (X Y : Type*) [Nonempty X] [IsEmpty Y] [Nontrivial R] :
    IsEmpty (CopyRows R X Y) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have h := (a.property x).2.2
  have ha : a.val x = 0 := Finsupp.ext fun y => isEmptyElim y
  simp [ha] at h

/-- With zero coefficients the row type in Theorem 4.3 has one element for every pair of
state sets. The zero row has counit 1 because 0 equals 1 in the coefficient ring. -/
def zeroRingRows (X Y : Type*) [Subsingleton R] : Unique (CopyRows R X Y) where
  default := ⟨fun _ => 0, fun _ => ⟨fun _ => .zero, fun _ _ _ => by simp,
    by simp [Subsingleton.elim (0 : R) 1]⟩⟩
  uniq a := Subtype.ext <| funext fun x => Finsupp.ext fun y => Subsingleton.elim _ _

/-- The image of a single state satisfies equation (4.1) in Theorem 4.3. -/
theorem isCopyRow_stateBasis {Y : Type*} (y : Y) : IsCopyRow (stateBasis R Y y) :=
  (isGroupLikeElem_iff_isCopyRow _).mp ⟨counit_stateBasis R y, comul_stateBasis R y⟩

/-- The zero row satisfies equation (4.1) precisely when the coefficient ring is zero.
This identifies the role of the sum equation in Theorem 4.3. -/
theorem isCopyRow_zero_iff (Y : Type*) :
    IsCopyRow (0 : CopyCoalgebra R Y) ↔ (0 : R) = 1 := by
  simp [IsCopyRow, Pairwise, IsIdempotentElem]

/-- From an empty state set, the coalgebra morphisms in Theorem 4.3 have one element. -/
def emptySourceCoalgebraMaps (X Y : Type*) [IsEmpty X] :
    Unique (CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) :=
  letI := emptySourceRows (R := R) X Y
  (coalgebraRowsEquiv X Y).unique

/-- Over a nonzero ring a nonempty state set has no coalgebra map to the empty state set. -/
theorem isEmpty_coalgebraMaps_of_isEmpty_target (X Y : Type*) [Nonempty X] [IsEmpty Y]
    [Nontrivial R] : IsEmpty (CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) :=
  ⟨fun f => (isEmpty_rows_of_isEmpty_target (R := R) X Y).false ((coalgebraRowsEquiv X Y) f)⟩

/-- Over the zero ring the coalgebra morphisms in Theorem 4.3 have one element. -/
def zeroRingCoalgebraMaps (X Y : Type*) [Subsingleton R] :
    Unique (CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) :=
  letI := zeroRingRows (R := R) X Y
  (coalgebraRowsEquiv X Y).unique

section BaseChange

variable {S : Type*} [CommRing S]

/-- The finite coefficients of a row in Theorem 4.3 can be changed along any ring map. -/
def mapRowCoefficients {Y : Type*} (f : R →+* S) (a : CopyCoalgebra R Y) :
    CopyCoalgebra S Y :=
  Finsupp.mapRange f f.map_zero a

/-- The scalar formula for `mapRowCoefficients`. Simplify by changing one coefficient. -/
@[simp]
theorem mapRowCoefficients_apply {Y : Type*} (f : R →+* S) (a : CopyCoalgebra R Y) (y : Y) :
    mapRowCoefficients f a y = f (a y) :=
  rfl

/-- A ring map preserves the equations of a coefficient row in Theorem 4.3. -/
theorem isCopyRow_mapRowCoefficients {Y : Type*} (f : R →+* S) {a : CopyCoalgebra R Y}
    (ha : IsCopyRow a) : IsCopyRow (mapRowCoefficients f a) := by
  refine ⟨fun y => (ha.1 y).map f, fun y z hne => ?_, ?_⟩
  · simp only [mapRowCoefficients_apply, ← map_mul]
    exact (congrArg f (ha.2.1 hne)).trans f.map_zero
  · unfold mapRowCoefficients
    rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← map_finsuppSum, ha.2.2, map_one]

/-- The new coefficient family of Theorem 4.3 is obtained by applying the ring map in each row. -/
def mapRows {X Y : Type*} (f : R →+* S) (a : CopyRows R X Y) : CopyRows S X Y :=
  ⟨fun x => mapRowCoefficients f (a.val x), fun x => isCopyRow_mapRowCoefficients f (a.property x)⟩

variable (S) [Algebra R S]

/-- Extending scalars on the free state module gives the free state module over the new ring. -/
def copyBaseChangeLinear (X : Type*) : (S ⊗[R] CopyCoalgebra R X) ≃ₗ[S] CopyCoalgebra S X := by
  classical
  exact finsuppScalarRight R S S X

/-- The unit tensor formula for scalar extension of a state module. Simplify to the row with
each coefficient changed by the algebra map. -/
@[simp]
theorem copyBaseChangeLinear_one_tmul {X : Type*} (a : CopyCoalgebra R X) :
    copyBaseChangeLinear S X ((1 : S) ⊗ₜ[R] a) = mapRowCoefficients (algebraMap R S) a := by
  apply Finsupp.ext
  intro x
  simp [copyBaseChangeLinear, Algebra.smul_def]

/-- A state basis is taken to the state basis by the coefficient comparison of Theorem 4.3.
Simplify the unit tensor of a state. -/
@[simp]
theorem copyBaseChangeLinear_one_tmul_stateBasis {X : Type*} (x : X) :
    copyBaseChangeLinear S X ((1 : S) ⊗ₜ[R] stateBasis R X x) = stateBasis S X x := by
  classical
  apply Finsupp.ext
  intro y
  by_cases h : x = y <;> simp [h]

/-- The scalar extension equivalence of the free state module preserves the copying coalgebra. -/
def copyBaseChangeEquiv (X : Type*) :
    (S ⊗[R] CopyCoalgebra R X) ≃ₗc[S] CopyCoalgebra S X := by
  let φ : (S ⊗[R] CopyCoalgebra R X) →ₗc[S] CopyCoalgebra S X :=
    { toLinearMap := (copyBaseChangeLinear S X).toLinearMap
      counit_comp := by
        apply ((stateBasis R X).baseChange S).ext
        intro x
        simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply, LinearEquiv.coe_coe,
          copyBaseChangeLinear_one_tmul_stateBasis, counit_stateBasis, TensorProduct.counit_tmul,
          CommSemiring.counit_apply, one_smul]
      map_comp_comul := by
        apply ((stateBasis R X).baseChange S).ext
        intro x
        simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply, LinearEquiv.coe_coe,
          copyBaseChangeLinear_one_tmul_stateBasis, TensorProduct.comul_tmul, comul_stateBasis,
          CommSemiring.comul_apply, AlgebraTensorModule.tensorTensorTensorComm_tmul,
          TensorProduct.map_tmul] }
  exact CoalgEquiv.ofBijective (f := φ) (copyBaseChangeLinear S X).bijective

/-- The scalar extension of coalgebras in Theorem 4.3 has the stated free-module
comparison as its underlying map. Simplify to that linear equivalence. -/
@[simp]
theorem copyBaseChangeEquiv_apply (X : Type*) (a : S ⊗[R] CopyCoalgebra R X) :
    copyBaseChangeEquiv S X a = copyBaseChangeLinear S X a :=
  rfl

/-- In Theorem 4.3, changing coefficients of the rows then extending linearly agrees with
scalar extension of the original coalgebra map under the two free-module comparisons. -/
theorem mapOfRows_mapRows_baseChange {X Y : Type*} (a : CopyRows R X Y) :
    (mapOfRows (mapRows (algebraMap R S) a)).toLinearMap.comp (copyBaseChangeLinear S X).toLinearMap =
      (copyBaseChangeLinear S Y).toLinearMap.comp ((mapOfRows a).toLinearMap.baseChange S) := by
  apply ((stateBasis R X).baseChange S).ext
  intro x
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul]
  change mapOfRows (mapRows (algebraMap R S) a)
      (copyBaseChangeLinear S X ((1 : S) ⊗ₜ[R] stateBasis R X x)) =
    copyBaseChangeLinear S Y ((1 : S) ⊗ₜ[R] mapOfRows a (stateBasis R X x))
  rw [copyBaseChangeLinear_one_tmul_stateBasis, mapOfRows_stateBasis, mapOfRows_stateBasis,
    copyBaseChangeLinear_one_tmul]
  rfl

/-- Theorem 4.3. Changing the coefficients of a row commutes with scalar extension
as an equality of coalgebra morphisms. -/
theorem mapOfRows_mapRows_baseChange_coalg {X Y : Type*} (a : CopyRows R X Y) :
    (mapOfRows (mapRows (algebraMap R S) a)).comp (copyBaseChangeEquiv S X).toCoalgHom =
      (copyBaseChangeEquiv S Y).toCoalgHom.comp
        (Coalgebra.TensorProduct.map (R := R) (S := S) (CoalgHom.id S S) (mapOfRows a)) := by
  apply CoalgHom.coe_linearMap_injective
  simpa only [CoalgHom.comp_toLinearMap, Coalgebra.TensorProduct.map_toLinearMap,
    CoalgHom.id_toLinearMap, LinearMap.baseChange] using mapOfRows_mapRows_baseChange S a

end BaseChange

end SHIGURE.Copying
