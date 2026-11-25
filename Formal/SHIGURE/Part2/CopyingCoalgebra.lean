import Formal.SHIGURE.Part2.Copying.RowsAndLabels
import Formal.SHIGURE.Part2.Copying.BooleanExample

/-!
# Copying morphisms in coalgebras and schemes

Construction 4.2, Theorem 4.3 and Example 4.4. The two kinds of morphism agree
through the finite coefficient rows of equation (4.1).
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped BigOperators

noncomputable section

namespace SHIGURE.Copying

universe u

variable {R : Type u} [CommRing R] {X Y Z : Type u}

/-- A constant scheme of states over the spectrum of the coefficient ring. -/
abbrev CopyScheme (R : Type u) [CommRing R] (X : Type u) :=
  constantSchemeOver (Spec (CommRingCat.of R)) X

/-- The row of labels on the affine copy corresponding to a source state. -/
def sourceLabels (f : CopyScheme R X ⟶ CopyScheme R Y) (x : X) :
    LocallyConstant (Spec (CommRingCat.of R)) Y :=
  constantPointLabelsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of R)))) Y
    (constantMapsPointsEquiv (Spec (CommRingCat.of R)) X Y f x)

/-- The scheme side of Theorem 4.3. View a morphism on each source copy, read the
locally constant labels, and identify their finite fibres by the clopen equivalence. -/
def schemeRowsEquiv (X Y : Type u) :
    (CopyScheme R X ⟶ CopyScheme R Y) ≃ CopyRows R X Y :=
  (constantMapsPointsEquiv (Spec (CommRingCat.of R)) X Y).trans <|
    (Equiv.piCongrRight fun _ => (constantPointLabelsEquiv
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) Y).trans affineLabelsRowsEquiv).trans
      { toFun := fun f => ⟨fun x => (f x).val, fun x => (f x).property⟩
        invFun := fun a x => ⟨a.val x, a.property x⟩
        left_inv := fun f => funext fun x => Subtype.eta (f x) _
        right_inv := fun _ => rfl }

/-- Theorem 4.3 compares the two geometries through the same row of coefficients. -/
def copyingHomEquiv (X Y : Type u) :
    (CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) ≃ (CopyScheme R X ⟶ CopyScheme R Y) :=
  (coalgebraRowsEquiv X Y).trans (schemeRowsEquiv X Y).symm

/-- The coefficient of a scheme map corresponds to the clopen fibre of the chosen label. -/
theorem mem_basicOpen_schemeRows (f : CopyScheme R X ⟶ CopyScheme R Y)
    (x : X) (y : Y) (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.basicOpen (((schemeRowsEquiv X Y) f).val x y) ↔
      stateLabel (f.left (stateInclusion (Spec (CommRingCat.of R)) X x p)) = y :=
  mem_basicOpen_labelIdempotent (sourceLabels f x) y p

/-- The comparison in Theorem 4.3 preserves the row itself. -/
@[simp]
theorem schemeRowsEquiv_copyingHomEquiv (f : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) :
    (schemeRowsEquiv X Y) (copyingHomEquiv X Y f) = (coalgebraRowsEquiv X Y) f :=
  (schemeRowsEquiv X Y).apply_symm_apply _

/-- The two sides of Theorem 4.3 agree on composition of arbitrary arrows. -/
theorem copyingHomEquiv_comp (f : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y)
    (g : CopyCoalgebra R Y →ₗc[R] CopyCoalgebra R Z) :
    copyingHomEquiv X Z (g.comp f) = copyingHomEquiv X Y f ≫ copyingHomEquiv Y Z g := by
  let F := copyingHomEquiv X Y f
  let G := copyingHomEquiv Y Z g
  apply (schemeRowsEquiv X Z).injective
  rw [schemeRowsEquiv_copyingHomEquiv]
  let A := (schemeRowsEquiv X Y) F
  let B := (schemeRowsEquiv Y Z) G
  let C := (schemeRowsEquiv X Z) (F ≫ G)
  let D := (coalgebraRowsEquiv X Z) (g.comp f)
  have hA : A = (coalgebraRowsEquiv X Y) f := schemeRowsEquiv_copyingHomEquiv f
  have hB : B = (coalgebraRowsEquiv Y Z) g := schemeRowsEquiv_copyingHomEquiv g
  change D = C
  apply Subtype.ext
  funext x
  apply Finsupp.ext
  intro z
  apply idempotent_eq_of_basicOpen_iff (D.property x |>.1 z) (C.property x |>.1 z)
  intro p
  let y := labelOfRow ⟨A.val x, A.property x⟩ p
  have hy : y = stateLabel (F.left (stateInclusion (Spec (CommRingCat.of R)) X x p)) :=
    (labelOfRow_eq_iff ⟨A.val x, A.property x⟩ p _).mpr ((mem_basicOpen_schemeRows F x _ p).mpr rfl)
  have hp : F.left (stateInclusion (Spec (CommRingCat.of R)) X x p) =
      stateInclusion (Spec (CommRingCat.of R)) Y y p := by
    rw [hy]
    exact image_stateInclusion_eq F x p
  have hD : D.val x z = (A.val x).sum (fun j r => r * B.val j z) := by
    change ((coalgebraRowsEquiv X Z) (g.comp f)).val x z = _
    rw [coalgebraRowsEquiv_comp, Finsupp.sum_apply, ← hA, ← hB]
    rfl
  calc
    p ∈ PrimeSpectrum.basicOpen (D.val x z) ↔ p ∈ PrimeSpectrum.basicOpen (B.val y z) := by
      rw [hD]
      exact mem_basicOpen_row_sum ⟨A.val x, A.property x⟩ (fun j => B.val j z) p
    _ ↔ stateLabel (G.left (stateInclusion (Spec (CommRingCat.of R)) Y y p)) = z :=
      mem_basicOpen_schemeRows G y z p
    _ ↔ p ∈ PrimeSpectrum.basicOpen (C.val x z) := by
      rw [← hp]
      exact (mem_basicOpen_schemeRows (F ≫ G) x z p).symm

/-- The comparison in Theorem 4.3 takes the linearization of a function to the induced
constant-scheme map of Construction 4.2. -/
theorem copyingHomEquiv_mapStates (f : X → Y) :
    copyingHomEquiv X Y (mapStates R f) = mapStateSchemes (Spec (CommRingCat.of R)) f := by
  classical
  let a := (schemeRowsEquiv X Y) (mapStateSchemes (Spec (CommRingCat.of R)) f)
  let b := (coalgebraRowsEquiv X Y) (mapStates R f)
  apply (schemeRowsEquiv X Y).injective
  rw [schemeRowsEquiv_copyingHomEquiv]
  apply Subtype.ext
  funext x
  apply Finsupp.ext
  intro y
  apply idempotent_eq_of_basicOpen_iff (b.property x |>.1 y) (a.property x |>.1 y)
  intro p
  have ha : p ∈ PrimeSpectrum.basicOpen (a.val x y) ↔ f x = y := by
    rw [mem_basicOpen_schemeRows, stateLabel_mapStateSchemes, stateLabel_inclusion]
  rw [ha]
  change p ∈ PrimeSpectrum.basicOpen (((coalgebraRowsEquiv X Y) (mapStates R f)).val x y) ↔ _
  rw [coalgebraRowsEquiv_apply, mapStates_stateBasis, stateBasis_apply]
  by_cases he : f x = y <;> simp [he]

/-- The comparison in Theorem 4.3 preserves the identity arrow. -/
theorem copyingHomEquiv_id :
    copyingHomEquiv X X (CoalgHom.id R _) = 𝟙 (CopyScheme R X) := by
  rw [← mapStates_id R X, copyingHomEquiv_mapStates, mapStateSchemes_id]

/-- Coefficient change of a scheme map in Theorem 4.3 applies the ring map in each row. -/
theorem schemeRowsEquiv_changeBase {S : Type u} [CommRing S] (g : R →+* S)
    (f : CopyScheme R X ⟶ CopyScheme R Y) :
    (schemeRowsEquiv X Y) (changeConstantMapBase (Spec.map (CommRingCat.ofHom g)) f) =
      mapRows g ((schemeRowsEquiv X Y) f) := by
  let β := Spec.map (CommRingCat.ofHom g)
  let F := changeConstantMapBase β f
  let A := (schemeRowsEquiv X Y) F
  let B := (schemeRowsEquiv X Y) f
  let C := mapRows g B
  change A = C
  apply Subtype.ext
  funext x
  apply Finsupp.ext
  intro y
  apply idempotent_eq_of_basicOpen_iff (A.property x |>.1 y) (C.property x |>.1 y)
  intro p
  have hp := congrArg (fun h : Spec (CommRingCat.of S) ⟶ constantScheme (Spec (CommRingCat.of R)) X =>
    h p) (stateInclusion_mapConstantBase β X x)
  change mapConstantBase β X (stateInclusion (Spec (CommRingCat.of S)) X x p) =
    stateInclusion (Spec (CommRingCat.of R)) X x (β p) at hp
  calc
    p ∈ PrimeSpectrum.basicOpen (A.val x y) ↔
        stateLabel (F.left (stateInclusion (Spec (CommRingCat.of S)) X x p)) = y :=
      mem_basicOpen_schemeRows F x y p
    _ ↔ stateLabel (f.left (stateInclusion (Spec (CommRingCat.of R)) X x (β p))) = y := by
      rw [show F = changeConstantMapBase β f from rfl, stateLabel_changeConstantMapBase, hp]
    _ ↔ β p ∈ PrimeSpectrum.basicOpen (B.val x y) := (mem_basicOpen_schemeRows f x y (β p)).symm
    _ ↔ p ∈ PrimeSpectrum.basicOpen (C.val x y) := by
      change PrimeSpectrum.comap g p ∈ PrimeSpectrum.basicOpen (B.val x y) ↔
        p ∈ PrimeSpectrum.basicOpen (g (B.val x y))
      rfl

/-- The comparison of Theorem 4.3 commutes with change of coefficient ring on all arrows. -/
theorem copyingHomEquiv_changeBase {S : Type u} [CommRing S] (g : R →+* S)
    (f : CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) :
    copyingHomEquiv X Y (mapOfRows (mapRows g ((coalgebraRowsEquiv X Y) f))) =
      changeConstantMapBase (Spec.map (CommRingCat.ofHom g)) (copyingHomEquiv X Y f) := by
  apply (schemeRowsEquiv X Y).injective
  rw [schemeRowsEquiv_copyingHomEquiv, schemeRowsEquiv_changeBase, schemeRowsEquiv_copyingHomEquiv]
  exact (coalgebraRowsEquiv X Y).apply_symm_apply _

/-- A nontrivial coefficient ring with only trivial idempotents recovers the set of functions
on the scheme side of Theorem 4.3. -/
def stateSchemeMapsEquiv [Nontrivial R]
    (h01 : ∀ r : R, IsIdempotentElem r → r = 0 ∨ r = 1) :
    (X → Y) ≃ (CopyScheme R X ⟶ CopyScheme R Y) :=
  (stateMapsEquiv X Y h01).trans (copyingHomEquiv X Y)

/-- Every choice of target admits a unique arrow from the empty state scheme in Theorem 4.3. -/
def emptySourceSchemeMaps [IsEmpty X] : Unique (CopyScheme R X ⟶ CopyScheme R Y) :=
  letI := emptySourceRows (R := R) X Y
  (schemeRowsEquiv X Y).unique

/-- No arrow to the empty state scheme exists from a nonempty state set over a nonzero ring. -/
theorem isEmpty_schemeMaps_of_isEmpty_target [Nonempty X] [IsEmpty Y] [Nontrivial R] :
    IsEmpty (CopyScheme R X ⟶ CopyScheme R Y) :=
  ⟨fun f => (isEmpty_rows_of_isEmpty_target (R := R) X Y).false ((schemeRowsEquiv X Y) f)⟩

/-- Over the zero ring there is a unique arrow between any two state schemes in Theorem 4.3. -/
def zeroRingSchemeMaps [Subsingleton R] : Unique (CopyScheme R X ⟶ CopyScheme R Y) :=
  letI := zeroRingRows (R := R) X Y
  (schemeRowsEquiv X Y).unique

end SHIGURE.Copying
