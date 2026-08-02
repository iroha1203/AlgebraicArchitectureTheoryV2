import ResearchLean.AG.AtomFoundation.Doctrine

/-!
# Canonical Atom transport laws

This module exposes the functoriality and equivalence-cancellation laws needed
to transport a complete core reading.  Every equality is derived directly from
the direct-image definitions in `Formal.AG.ReadingFunctoriality.Core`; no target
family, configuration, or upper lift is accepted as input.
-/

namespace AAT.AG.AtomFoundation

universe u

/-- Direct-image transport of an Atom family along the identity is trivial. -/
@[simp]
theorem atomFamily_transport_id {U : AtomCarrier.{u}}
    (F : AtomFamily U) :
    F.transport _root_.id = F := by
  ext target
  constructor
  · rintro ⟨source, hsource, rfl⟩
    exact hsource
  · intro htarget
    exact ⟨target, htarget, rfl⟩

/-- Direct-image transport of Atom families respects function composition. -/
theorem atomFamily_transport_comp {U : AtomCarrier.{u}}
    (F : AtomFamily U) (f g : U.Atom → U.Atom) :
    (F.transport f).transport g = F.transport (g ∘ f) := by
  ext target
  constructor
  · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
    exact ⟨source, hsource, rfl⟩
  · rintro ⟨source, hsource, rfl⟩
    exact ⟨f source, ⟨source, hsource, rfl⟩, rfl⟩

/-- Transport by an equivalence and then its inverse recovers the family. -/
@[simp]
theorem atomFamily_transport_equiv_symm {U : AtomCarrier.{u}}
    (F : AtomFamily U) (e : U.Atom ≃ U.Atom) :
    (F.transport e).transport e.symm = F := by
  rw [atomFamily_transport_comp]
  have hmap :
      (e.symm : U.Atom → U.Atom) ∘ (e : U.Atom → U.Atom) = _root_.id := by
    funext atom
    exact e.symm_apply_apply atom
  rw [hmap, atomFamily_transport_id]

/-- Transport by an inverse equivalence and then the equivalence recovers the family. -/
@[simp]
theorem atomFamily_transport_symm_equiv {U : AtomCarrier.{u}}
    (F : AtomFamily U) (e : U.Atom ≃ U.Atom) :
    (F.transport e.symm).transport e = F := by
  rw [atomFamily_transport_comp]
  have hmap :
      (e : U.Atom → U.Atom) ∘ (e.symm : U.Atom → U.Atom) = _root_.id := by
    funext atom
    exact e.apply_symm_apply atom
  rw [hmap, atomFamily_transport_id]

/-- Direct-image transport of a configuration along the identity is trivial. -/
@[simp]
theorem atomConfiguration_transport_id {U : AtomCarrier.{u}}
    (C : AtomConfiguration U) :
    C.transport _root_.id = C := by
  ext
  · constructor
    · rintro ⟨source, hsource, rfl⟩
      exact hsource
    · intro htarget
      exact ⟨_, htarget, rfl⟩
  · constructor
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact h
    · intro h
      exact ⟨_, _, h, rfl, rfl⟩
  · constructor
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact h
    · intro h
      exact ⟨_, _, h, rfl, rfl⟩

/-- Direct-image transport of configurations respects function composition. -/
theorem atomConfiguration_transport_comp {U : AtomCarrier.{u}}
    (C : AtomConfiguration U) (f g : U.Atom → U.Atom) :
    (C.transport f).transport g = C.transport (g ∘ f) := by
  ext
  · constructor
    · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, rfl⟩
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨f source, ⟨source, hsource, rfl⟩, rfl⟩
  · constructor
    · rintro ⟨middle₁, middle₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨source₁, source₂, h, rfl, rfl⟩
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact ⟨f source₁, f source₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
  · constructor
    · rintro ⟨middle₁, middle₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨source₁, source₂, h, rfl, rfl⟩
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact ⟨f source₁, f source₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩

/-- Transport by an equivalence and then its inverse recovers the configuration. -/
@[simp]
theorem atomConfiguration_transport_equiv_symm {U : AtomCarrier.{u}}
    (C : AtomConfiguration U) (e : U.Atom ≃ U.Atom) :
    (C.transport e).transport e.symm = C := by
  rw [atomConfiguration_transport_comp]
  have hmap :
      (e.symm : U.Atom → U.Atom) ∘ (e : U.Atom → U.Atom) = _root_.id := by
    funext atom
    exact e.symm_apply_apply atom
  rw [hmap, atomConfiguration_transport_id]

/-- Transport by an inverse equivalence and then the equivalence recovers the configuration. -/
@[simp]
theorem atomConfiguration_transport_symm_equiv {U : AtomCarrier.{u}}
    (C : AtomConfiguration U) (e : U.Atom ≃ U.Atom) :
    (C.transport e.symm).transport e = C := by
  rw [atomConfiguration_transport_comp]
  have hmap :
      (e : U.Atom → U.Atom) ∘ (e.symm : U.Atom → U.Atom) = _root_.id := by
    funext atom
    exact e.apply_symm_apply atom
  rw [hmap, atomConfiguration_transport_id]

/-- Family support is preserved by direct-image configuration transport. -/
theorem familySupported_transport {U : AtomCarrier.{u}}
    (C : AtomConfiguration U) (f : U.Atom → U.Atom)
    (hC : C.FamilySupported) :
    (C.transport f).FamilySupported := by
  constructor
  · rintro target₁ target₂ ⟨source₁, source₂, hrelation, rfl, rfl⟩
    have hsource := hC.1 hrelation
    exact
      ⟨⟨source₁, hsource.1, rfl⟩,
        ⟨source₂, hsource.2, rfl⟩⟩
  · rintro target₁ target₂ ⟨source₁, source₂, hidentification, rfl, rfl⟩
    have hsource := hC.2 hidentification
    exact
      ⟨⟨source₁, hsource.1, rfl⟩,
        ⟨source₂, hsource.2, rfl⟩⟩

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
