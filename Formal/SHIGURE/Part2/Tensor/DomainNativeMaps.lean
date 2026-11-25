import Formal.SHIGURE.Part2.Tensor.DomainUnit
import Formal.SHIGURE.Part2.Tensor.NativeMaps

/-!
# Recovering linear arrows of structures with specified domains

The component over the base ring is read through the unit on the entire
diagram. On carriers it is the original linear recovery from the unit
algebra map. Equality of carrier maps then determines equality of arrows
with all the relation and partial-value preservation conditions.
-/

open CategoryTheory SHIGURE.TensorRealization

universe u

noncomputable section

namespace SHIGURE.TensorDomainStructure

variable {k : Type u} [CommRing k] {sig : Signature.{u}}
variable {A B D : Diagrams k sig}

/-- Natural families whose components preserve the entire interpreted diagrams. -/
structure NaturalDomainHom (hA : A.AdmitsBaseChange) (hB : B.AdmitsBaseChange) where
  /-- Each component preserves the full primitive diagrams at these coefficients. -/
  app (R : Type u) [CommRing R] [Algebra k R] :
    (show Diagrams R sig from extend R A hA) ⟶ (show Diagrams R sig from extend R B hB)
  /-- The carrier arrows commute with all coefficient maps. -/
  natural {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) (s : sig.SortType) (x : (extend R A hA).carrier s) :
    mapCoefficients f (((app R).val s).hom x) = ((app S).val s).hom (mapCoefficients f x)

namespace NaturalDomainHom

variable {hA : A.AdmitsBaseChange} {hB : B.AdmitsBaseChange} {hD : D.AdmitsBaseChange}

/-- The total operations and quantities give the underlying natural family. -/
def forget (f : NaturalDomainHom hA hB) : NaturalTensorHom A.toTensorStructure B.toTensorStructure where
  app R := forgetHom (f.app R)
  natural := f.natural

/-- The family components determine the whole family with no additional choice of domain factors. -/
@[ext]
theorem ext {f g : NaturalDomainHom hA hB} (h : ∀ (R : Type u) [CommRing R] [Algebra k R],
    f.app R = g.app R) : f = g := by
  cases f
  cases g
  congr
  funext R _ _
  exact h R

/-- Extend the entire native preserving arrow over every coefficient algebra. -/
def ofNative (hA : A.AdmitsBaseChange) (hB : B.AdmitsBaseChange) (f : A ⟶ B) :
    NaturalDomainHom hA hB where
  app R := extendHom R hA hB f
  natural := by
    intro R S _ _ _ _ g s x
    rw [extendHom_onSort R hA hB f s, extendHom_onSort S hA hB f s]
    exact LinearMap.rTensor_baseChange g x (f.val s).hom

/-- Read the base component through the domain-preserving unit isomorphisms. -/
def native (f : NaturalDomainHom hA hB) : A ⟶ B :=
  (domainScalarUnit A hA).inv ≫ f.app k ≫ (domainScalarUnit B hB).hom

private theorem native_onSort (f : NaturalDomainHom hA hB) (s : sig.SortType) :
    ((f.native.val s).hom) = f.forget.native.onSort s := rfl

/-- The recovered arrow gives back the original family at every coefficient, including all domains. -/
theorem ofNative_native (f : NaturalDomainHom hA hB) : ofNative hA hB f.native = f := by
  apply NaturalDomainHom.ext
  intro R _ _
  apply hom_ext
  intro s
  change ((extendHom R hA hB f.native).val s).hom = ((f.app R).val s).hom
  rw [extendHom_onSort, native_onSort]
  exact congrArg (fun h : (extendStructure k R A.toTensorStructure) ⟶
    (extendStructure k R B.toTensorStructure) => h.onSort s)
    (congrArg (fun t : NaturalTensorHom A.toTensorStructure B.toTensorStructure => t.app R)
      f.forget.ofNative_native)

/-- Reading the extended family at the base recovers the native arrow. -/
theorem native_ofNative (f : A ⟶ B) : (ofNative hA hB f).native = f := by
  apply hom_ext
  intro s
  rw [native_onSort]
  exact congrArg (fun g : A.toTensorStructure ⟶ B.toTensorStructure => g.onSort s)
    (NaturalTensorHom.native_ofNative (forgetHom f))

/-- The identity family preserves the full diagrams at each coefficient. -/
def id (hA : A.AdmitsBaseChange) : NaturalDomainHom hA hA where
  app R := 𝟙 (show Diagrams R sig from extend R A hA)
  natural _ _ _ := rfl

/-- The pointwise composite preserves the full diagrams at each coefficient. -/
def comp (f : NaturalDomainHom hA hB) (g : NaturalDomainHom hB hD) : NaturalDomainHom hA hD where
  app R := f.app R ≫ g.app R
  natural := by
    intro R S _ _ _ _ a s x
    change mapCoefficients a (((g.app R).val s).hom (((f.app R).val s).hom x)) =
      ((g.app S).val s).hom (((f.app S).val s).hom (mapCoefficients a x))
    rw [g.natural, f.natural]

/-- Extension takes the identity to the identity family. -/
theorem ofNative_id : ofNative hA hA (𝟙 A) = id hA := by
  apply NaturalDomainHom.ext
  intro R _ _
  exact extendHom_id R hA

/-- Extension takes composition to the componentwise composition of families. -/
theorem ofNative_comp (f : A ⟶ B) (g : B ⟶ D) :
    ofNative hA hD (f ≫ g) = (ofNative hA hB f).comp (ofNative hB hD g) := by
  apply NaturalDomainHom.ext
  intro R _ _
  exact extendHom_comp R hA hB hD f g

/-- The natural-family comparison of Proposition 4.13 for the full primitive diagrams. -/
def nativeEquiv (hA : A.AdmitsBaseChange) (hB : B.AdmitsBaseChange) :
    (A ⟶ B) ≃ NaturalDomainHom hA hB :=
  ⟨ofNative hA hB, native, native_ofNative, ofNative_native⟩

end NaturalDomainHom
end SHIGURE.TensorDomainStructure
