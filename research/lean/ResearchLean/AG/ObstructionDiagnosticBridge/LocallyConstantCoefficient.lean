import ResearchLean.AG.ObstructionDiagnosticBridge.CoefficientComparison
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Algebra.Category.Grp.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Locally constant presentation coefficients

This module constructs the topological coefficient sheaf selected by the
G-125 paper design.  On an open set `W`, its sections are locally constant
functions `W → M_R`, where `M_R` is the derived presentation group.  The
restriction maps are pullback along inclusions.

The underlying type-valued presheaf is identified with Mathlib's sheaf of
continuous maps to the discrete space `M_R`; hence its sheaf condition is
proved rather than supplied.  On every nonempty preconnected open, evaluation
at one point gives the additive equivalence with `M_R` used by the normalized
cochain model, and restriction between such opens is the identity in these
coordinates.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution ResolutionInvariance

universe u

namespace GeneratorPresentation

variable {Source : Type u} {laws : FiniteLawFamily Source}

/-- Locally constant `M_R`-valued sections on one open set. -/
abbrev LocallyConstantSection (P : GeneratorPresentation laws)
    (X : TopCat.{u}) (W : Opens X) :=
  LocallyConstant W P.PresentationGroup

/-- The additive presheaf of locally constant `M_R`-valued functions. -/
def locallyConstantAddCommGrpPresheaf (P : GeneratorPresentation laws)
    (X : TopCat.{u}) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (P.LocallyConstantSection X W.unop)
  map {W V} inclusion := AddCommGrpCat.ofHom {
    toFun := LocallyConstant.comap ((Opens.toTopCat X).map inclusion.unop).hom
    map_zero' := rfl
    map_add' := by intro left right; rfl
  }
  map_id W := by
    apply AddCommGrpCat.hom_ext
    rfl
  map_comp {W V Z} first second := by
    apply AddCommGrpCat.hom_ext
    rfl

/-- Read a locally constant function as a continuous map to discrete `M_R`. -/
def locallyConstantToContinuous (P : GeneratorPresentation laws)
    (X : TopCat.{u}) (W : Opens X) :
    P.LocallyConstantSection X W →
      (TopCat.presheafToTop X (TopCat.discrete.obj P.PresentationGroup)).obj (op W) :=
  fun localValue => by
    letI : TopologicalSpace P.PresentationGroup := ⊥
    exact TopCat.ofHom ⟨localValue, localValue.isLocallyConstant.continuous⟩

/-- A continuous map to discrete `M_R` is locally constant. -/
def continuousToLocallyConstant (P : GeneratorPresentation laws)
    (X : TopCat.{u}) (W : Opens X) :
    (TopCat.presheafToTop X (TopCat.discrete.obj P.PresentationGroup)).obj (op W) →
      P.LocallyConstantSection X W :=
  fun continuousValue => by
    letI : TopologicalSpace P.PresentationGroup := ⊥
    exact ⟨fun point => continuousValue.hom point,
      (IsLocallyConstant.iff_continuous (fun point => continuousValue.hom point)).2
        continuousValue.hom.continuous⟩

/-- Locally constant sections are exactly continuous maps to discrete `M_R`. -/
def locallyConstantContinuousEquiv (P : GeneratorPresentation laws)
    (X : TopCat.{u}) (W : Opens X) :
    P.LocallyConstantSection X W ≃
      (TopCat.presheafToTop X (TopCat.discrete.obj P.PresentationGroup)).obj (op W) where
  toFun := P.locallyConstantToContinuous X W
  invFun := P.continuousToLocallyConstant X W
  left_inv _ := rfl
  right_inv continuousValue := by
    apply TopCat.hom_ext
    rfl

/-- Presheaf-level identification with Mathlib's continuous-map sheaf. -/
def locallyConstantPresheafIso (P : GeneratorPresentation laws)
    (X : TopCat.{u}) :
    P.locallyConstantAddCommGrpPresheaf X ⋙ forget AddCommGrpCat.{u} ≅
      TopCat.presheafToTop X (TopCat.discrete.obj P.PresentationGroup) :=
  NatIso.ofComponents
    (fun W => (P.locallyConstantContinuousEquiv X W.unop).toIso)
    (fun {W V} inclusion => by
      ext localValue
      apply TopCat.hom_ext
      rfl)

/-- The locally constant presentation presheaf satisfies the sheaf condition. -/
theorem locallyConstantAddCommGrpPresheaf_isSheaf
    (P : GeneratorPresentation laws) (X : TopCat.{u}) :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (P.locallyConstantAddCommGrpPresheaf X ⋙ forget AddCommGrpCat.{u}) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).1
  exact TopCat.Presheaf.isSheaf_of_iso (P.locallyConstantPresheafIso X).symm
    (TopCat.sheafToTop (X := X)
      (TopCat.discrete.obj P.PresentationGroup)).cond

/-- On a nonempty preconnected open, evaluation identifies sections with `M_R`. -/
def locallyConstantSectionEquiv (P : GeneratorPresentation laws)
    (X : TopCat.{u}) (W : Opens X) [Nonempty W] [PreconnectedSpace W] :
    P.LocallyConstantSection X W ≃+ P.PresentationGroup where
  toFun localValue := localValue (Classical.choice inferInstance)
  invFun value := LocallyConstant.const W value
  left_inv localValue := by
    apply LocallyConstant.ext
    intro point
    exact localValue.apply_eq_of_preconnectedSpace _ _
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Restriction between nonempty preconnected opens is the identity in evaluation coordinates. -/
theorem locallyConstantSectionEquiv_restriction
    (P : GeneratorPresentation laws) (X : TopCat.{u})
    (W V : Opens X) [Nonempty W] [PreconnectedSpace W]
    [Nonempty V] [PreconnectedSpace V] (inclusion : C(V, W))
    (localValue : P.LocallyConstantSection X W) :
    P.locallyConstantSectionEquiv X V (LocallyConstant.comap inclusion localValue) =
      P.locallyConstantSectionEquiv X W localValue := by
  change localValue (inclusion (Classical.choice inferInstance)) =
    localValue (Classical.choice inferInstance)
  exact localValue.apply_eq_of_preconnectedSpace _ _

end GeneratorPresentation

#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge

end AAT.AG.ObstructionDiagnosticBridge
