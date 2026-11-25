import Formal.SHIGURE.Part2.Profiles.Charts

/-!
# Composition of support-profile charts

The second part of Theorem 4.6 computes the composite of two copying maps in
the profile obtained by taking the finite unions of their allowed outputs.

## Implementation notes

Composition of the copying maps supplies the equations and associativity
of the composite rows. Defining the rows by the finite sum first would
repeat both proofs. The coordinate formula and the finite support bound
are then obtained separately.
-/

open scoped BigOperators

noncomputable section

namespace SHIGURE.Copying.SupportProfile

universe u

variable {X Y Z W : Type u} {R : Type u} [CommRing R]

/-- The profile of the composite in equation (4.2). -/
def compProfile (F : SupportProfile X Y) (H : SupportProfile Y Z) : SupportProfile X Z := by
  classical
  exact fun x => (F x).biUnion H

/-- The row support of the composite grows monotonically in either profile. -/
theorem compProfile_mono {F F' : SupportProfile X Y} {H H' : SupportProfile Y Z}
    (hF : F ≤ F') (hH : H ≤ H') : compProfile F H ≤ compProfile F' H' := by
  classical
  intro x z hz
  obtain ⟨y, hy, hz⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_biUnion.mpr ⟨y, hF x hy, hH y hz⟩

/-- The two composite profiles for a triple of charts agree pointwise. -/
theorem compProfile_assoc (F : SupportProfile X Y) (H : SupportProfile Y Z) (J : SupportProfile Z W) :
    compProfile (compProfile F H) J = compProfile F (compProfile H J) := by
  classical
  funext x
  ext w
  simp only [compProfile, Finset.mem_biUnion]
  constructor
  · rintro ⟨z, ⟨y, hy, hz⟩, hw⟩
    exact ⟨y, hy, z, hz, hw⟩
  · rintro ⟨y, hy, z, hz, hw⟩
    exact ⟨z, ⟨y, hy, hz⟩, hw⟩

variable {F : SupportProfile X Y} {H : SupportProfile Y Z} {J : SupportProfile Z W}

/-- Equation (4.2) follows by expanding the composite on a state basis and extending the sum to the allowed support. -/
private theorem composite_coeff (a : F.RowsAt R) (b : H.RowsAt R) (x : X) (z : Z) :
    ((coalgebraRowsEquiv X Z) ((mapOfRows b.val).comp (mapOfRows a.val))).val x z =
      ∑ y ∈ F x, a.val.val x y * b.val.val y z := by
  have h := coalgebraRowsEquiv_comp (mapOfRows a.val) (mapOfRows b.val) x
  change ((coalgebraRowsEquiv X Z) ((mapOfRows b.val).comp (mapOfRows a.val))).val x =
    (((coalgebraRowsEquiv X Y) ((coalgebraRowsEquiv X Y).symm a.val)).val x).sum
      (fun y r => r • ((coalgebraRowsEquiv Y Z) ((coalgebraRowsEquiv Y Z).symm b.val)).val y) at h
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [h, Finsupp.sum_of_support_subset _ (a.property x) (fun y r => r • b.val.val y)
      (fun y _ => zero_smul R (b.val.val y)),
    Finsupp.finset_sum_apply]
  rfl

/-- The actual composite of the copying maps gives the rows in the composite profile. -/
def compRows (a : F.RowsAt R) (b : H.RowsAt R) : (compProfile F H).RowsAt R :=
  ⟨(coalgebraRowsEquiv X Z) ((mapOfRows b.val).comp (mapOfRows a.val)), by
    classical
    intro x z hz
    by_contra hn
    apply (Finsupp.mem_support_iff.mp hz)
    rw [composite_coeff]
    apply Finset.sum_eq_zero
    intro y hy
    have hb : z ∉ (b.val.val y).support :=
      fun hb => hn (Finset.mem_biUnion.mpr ⟨y, hy, b.property y hb⟩)
    rw [Finsupp.notMem_support_iff.mp hb, mul_zero]⟩

/-- The coefficients of the composite are the finite sums in equation (4.2). -/
theorem compRows_apply (a : F.RowsAt R) (b : H.RowsAt R) (x : X) (z : Z) :
    (compRows a b).val.val x z = ∑ y ∈ F x, a.val.val x y * b.val.val y z :=
  composite_coeff a b x z

/-- Composition agrees with the native composition of the represented copying maps. -/
theorem mapOfRows_compRows (a : F.RowsAt R) (b : H.RowsAt R) :
    mapOfRows (compRows a b).val = (mapOfRows b.val).comp (mapOfRows a.val) :=
  (coalgebraRowsEquiv X Z).symm_apply_apply _

/-- Enlarging the input profiles leaves all coefficients of the composite unchanged. -/
theorem compRows_enlarge {F' : SupportProfile X Y} {H' : SupportProfile Y Z}
    (hF : F ≤ F') (hH : H ≤ H') (a : F.RowsAt R) (b : H.RowsAt R) :
    compRows (enlargeRows hF a) (enlargeRows hH b) =
      enlargeRows (compProfile_mono hF hH) (compRows a b) :=
  Subtype.ext rfl

/-- Associativity holds for bounded coefficient rows, with the same coefficients at both profiles. -/
theorem compRows_assoc (a : F.RowsAt R) (b : H.RowsAt R) (c : J.RowsAt R) :
    (compRows (compRows a b) c).val = (compRows a (compRows b c)).val := by
  apply (coalgebraRowsEquiv X W).symm.injective
  change mapOfRows (compRows (compRows a b) c).val = mapOfRows (compRows a (compRows b c)).val
  rw [mapOfRows_compRows, mapOfRows_compRows, mapOfRows_compRows, mapOfRows_compRows]
  exact (CoalgHom.comp_assoc (mapOfRows c.val) (mapOfRows b.val) (mapOfRows a.val)).symm

/-- The identity profile has exactly its source as its allowed output. -/
def identityProfile (X : Type u) : SupportProfile X X :=
  fun x => {x}

/-- The identity profile is a left unit for profile composition. -/
theorem compProfile_identity_source (F : SupportProfile X Y) :
    compProfile (identityProfile X) F = F := by
  classical
  funext x
  exact Finset.singleton_biUnion

/-- The identity profile is a right unit for profile composition. -/
theorem compProfile_identity_target (F : SupportProfile X Y) :
    compProfile F (identityProfile Y) = F := by
  funext x
  classical
  exact Finset.biUnion_singleton_eq_self

/-- The identity map has unit coefficients at the source in its identity profile. -/
def identityRows (R X : Type u) [CommRing R] : (identityProfile X).RowsAt R :=
  ⟨(coalgebraRowsEquiv X X) (CoalgHom.id R _),
    fun x => by rw [coalgebraRowsEquiv_id]; exact Finsupp.support_single_subset⟩

/-- The rows of the identity represent the native coalgebra identity. -/
theorem mapOfRows_identityRows (R X : Type u) [CommRing R] :
    mapOfRows (identityRows R X).val = CoalgHom.id R (CopyCoalgebra R X) :=
  (coalgebraRowsEquiv X X).symm_apply_apply _

/-- Composition of bounded rows with the identity on the source preserves their coefficients. -/
theorem compRows_identity_source (a : F.RowsAt R) :
    (compRows (identityRows R X) a).val = a.val := by
  apply (coalgebraRowsEquiv X Y).symm.injective
  change mapOfRows (compRows (identityRows R X) a).val = mapOfRows a.val
  rw [mapOfRows_compRows, mapOfRows_identityRows, CoalgHom.comp_id]

/-- Composition of bounded rows with the identity on the target preserves their coefficients. -/
theorem compRows_identity_target (a : F.RowsAt R) :
    (compRows a (identityRows R Y)).val = a.val := by
  apply (coalgebraRowsEquiv X Y).symm.injective
  change mapOfRows (compRows a (identityRows R Y)).val = mapOfRows a.val
  rw [mapOfRows_compRows, mapOfRows_identityRows, CoalgHom.id_comp]

variable {k S : Type u} [CommRing k] [CommRing S] [Algebra k R] [Algebra k S]

/-- The composition of bounded rows commutes with coefficients changing along an algebra map. -/
theorem compRows_natural (g : R →ₐ[k] S) (a : F.RowsAt R) (b : H.RowsAt R) :
    mapCoefficients g (compRows a b) = compRows (mapCoefficients g a) (mapCoefficients g b) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  apply Finsupp.ext
  intro z
  change mapRowCoefficients g.toRingHom ((compRows a b).val.val x) z =
    (compRows (mapCoefficients g a) (mapCoefficients g b)).val.val x z
  rw [mapRowCoefficients_apply, compRows_apply, compRows_apply, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  change g (a.val.val x y * b.val.val y z) =
    mapRowCoefficients g.toRingHom (a.val.val x) y * mapRowCoefficients g.toRingHom (b.val.val y) z
  simp only [mapRowCoefficients_apply, map_mul]
  rfl

end SHIGURE.Copying.SupportProfile
