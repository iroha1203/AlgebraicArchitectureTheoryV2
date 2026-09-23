import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import ResearchLean.AG.FullGeometryNormalization.SemanticExactBarBetaProjection
import ResearchLean.AG.FullGeometryNormalization.SemanticCoreMateIso

/-! # Core image of the semantic selected comparison -/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory CategoryTheory.Idempotents AtomFoundation GeometryTransport
open CrossStageCoherence DoctrineFiberProduct TransportCoherence

set_option maxHeartbeats 3000000

private theorem idem_of_iso_transport
    {C : Type*} [Category C] {X Y : C} (i : X ≅ Y)
    (p : X ⟶ X) (q : Y ⟶ Y) (hp : p ≫ p = p)
    (h : p ≫ i.hom = i.hom ≫ q) : q ≫ q = q := by
  apply (cancel_epi i.hom).1
  calc
    i.hom ≫ (q ≫ q) = (i.hom ≫ q) ≫ q := by rw [Category.assoc]
    _ = (p ≫ i.hom) ≫ q := by rw [h]
    _ = p ≫ (i.hom ≫ q) := by rw [Category.assoc]
    _ = p ≫ (p ≫ i.hom) := by rw [h]
    _ = (p ≫ p) ≫ i.hom := by rw [Category.assoc]
    _ = p ≫ i.hom := by rw [hp]
    _ = i.hom ≫ q := h

/-- The independent global core target projector is idempotent. -/
theorem semanticExactBarTargetGlobalCoreProjectorAt_idem
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq ≫
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq =
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq := by
  apply idem_of_iso_transport
    (semanticDerivedViaBaseCoreIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    ((geometryFiberProjection input.square.northeast).map
      (semanticExactBarDAt input interpretation z omega k g endpoint_eq))
    (semanticExactBarTargetGlobalCoreProjectorAt
      input interpretation z omega endpoint_eq)
  · rw [← Functor.map_comp, semanticExactBarDAt_idem]
  · exact semanticExactBarDAt_projection
      input interpretation z omega k g endpoint_eq

/-- Source core projector, conjugate to the cochain-selected target projector. -/
noncomputable def semanticExactBarCoreEAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    (exact_bottom_semantic_global_reindex_functor input.square.left ⋙
      coreFiberTransportFunctor input.square.top).obj
        (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq) ⟶
    (exact_bottom_semantic_global_reindex_functor input.square.left ⋙
      coreFiberTransportFunctor input.square.top).obj
        (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq) :=
  let m := (semanticCoreBeckChevalleyMate input).app
    (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)
  letI : IsIso m := semanticCoreBeckChevalleyMate_app_isIso input _
  m ≫ semanticExactBarTargetGlobalCoreProjectorAt
    input interpretation z omega endpoint_eq ≫ inv m

/-- Third projection square of (6.25): the conjugate source projector. -/
theorem semanticExactBarEAt_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (geometryFiberProjection input.square.northeast).map
        (semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback) ≫
      (semanticDerivedDirectCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom =
    (semanticDerivedDirectCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom ≫
      semanticExactBarCoreEAt input interpretation z omega endpoint_eq := by
  let F := geometryFiberProjection input.square.northeast
  let a := semanticDerivedBarAlphaIsoAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq square_isPullback
  let jD := semanticDerivedDirectCoreIsoAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq
  let jV := semanticDerivedViaBaseCoreIsoAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq
  let m := (semanticCoreBeckChevalleyMate input).app
    (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)
  let d := semanticExactBarDAt input interpretation z omega k g endpoint_eq
  let D := semanticExactBarTargetGlobalCoreProjectorAt
    input interpretation z omega endpoint_eq
  letI : IsIso m := semanticCoreBeckChevalleyMate_app_isIso input _
  have hAlpha : F.map a.hom ≫ jV.hom = jD.hom ≫ m :=
    semanticDerivedBarAlphaIsoAt_projection input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq square_isPullback
  have hD : F.map d ≫ jV.hom = jV.hom ≫ D :=
    semanticExactBarDAt_projection input interpretation z omega k g endpoint_eq
  have hInv : F.map a.inv ≫ jD.hom = jV.hom ≫ inv m := by
    apply (cancel_epi (F.map a.hom)).1
    calc
      F.map a.hom ≫ (F.map a.inv ≫ jD.hom) =
          F.map (a.hom ≫ a.inv) ≫ jD.hom := by
            rw [← Category.assoc, ← Functor.map_comp]
      _ = jD.hom := by simp
      _ = (jD.hom ≫ m) ≫ inv m := by simp
      _ = F.map a.hom ≫ (jV.hom ≫ inv m) := by
        rw [← hAlpha, Category.assoc]
  change F.map (a.hom ≫ d ≫ a.inv) ≫ jD.hom =
    jD.hom ≫ (m ≫ D ≫ inv m)
  simp only [Functor.map_comp, Category.assoc]
  rw [hInv]
  rw [← Category.assoc (F.map d) jV.hom (inv m), hD]
  calc
    F.map a.hom ≫ (jV.hom ≫ D) ≫ inv m =
        ((F.map a.hom ≫ jV.hom) ≫ D) ≫ inv m := by
          simp only [Category.assoc]
    _ = ((jD.hom ≫ m) ≫ D) ≫ inv m := by rw [hAlpha]
    _ = jD.hom ≫ m ≫ D ≫ inv m := by simp only [Category.assoc]

section CoreImage

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) = input.square.southwest)
include k g

/-- The independent source core projector is idempotent. -/
theorem semanticExactBarCoreEAt_idem :
    semanticExactBarCoreEAt input interpretation z omega endpoint_eq ≫
      semanticExactBarCoreEAt input interpretation z omega endpoint_eq =
    semanticExactBarCoreEAt input interpretation z omega endpoint_eq := by
  let m := (semanticCoreBeckChevalleyMate input).app
    (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)
  let D := semanticExactBarTargetGlobalCoreProjectorAt
    input interpretation z omega endpoint_eq
  letI : IsIso m := semanticCoreBeckChevalleyMate_app_isIso input _
  have hD : D ≫ D = D :=
    semanticExactBarTargetGlobalCoreProjectorAt_idem
      input interpretation z omega k g endpoint_eq
  change (m ≫ D ≫ inv m) ≫ (m ≫ D ≫ inv m) = m ≫ D ≫ inv m
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← Category.assoc D D (inv m), hD]

/-- The independent core beta is absorbed by its source image. -/
theorem semanticExactBarCoreBetaAt_source_factorization :
    semanticExactBarCoreEAt input interpretation z omega endpoint_eq ≫
      semanticExactBarCoreBetaAt input interpretation z omega endpoint_eq =
    semanticExactBarCoreBetaAt input interpretation z omega endpoint_eq := by
  let m := (semanticCoreBeckChevalleyMate input).app
    (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)
  let D := semanticExactBarTargetGlobalCoreProjectorAt
    input interpretation z omega endpoint_eq
  letI : IsIso m := semanticCoreBeckChevalleyMate_app_isIso input _
  have hD : D ≫ D = D :=
    semanticExactBarTargetGlobalCoreProjectorAt_idem
      input interpretation z omega k g endpoint_eq
  change (m ≫ D ≫ inv m) ≫ (m ≫ D) = m ≫ D
  simp [Category.assoc, hD]

/-- The independent core beta is absorbed by its target image. -/
theorem semanticExactBarCoreBetaAt_target_factorization :
    semanticExactBarCoreBetaAt input interpretation z omega endpoint_eq ≫
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq =
    semanticExactBarCoreBetaAt input interpretation z omega endpoint_eq := by
  change ((semanticCoreBeckChevalleyMate input).app
      (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq) ≫
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq) ≫
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq =
    (semanticCoreBeckChevalleyMate input).app
      (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq) ≫
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq
  rw [Category.assoc,
    semanticExactBarTargetGlobalCoreProjectorAt_idem
      input interpretation z omega k g endpoint_eq]

/-- Core source image of the selected comparison. -/
noncomputable def semanticExactBarCoreESourceKaroubiAt :
    Karoubi (CoreFiber input.square.northeast) where
  X := (exact_bottom_semantic_global_reindex_functor input.square.left ⋙
    coreFiberTransportFunctor input.square.top).obj
      (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)
  p := semanticExactBarCoreEAt input interpretation z omega endpoint_eq
  idem := semanticExactBarCoreEAt_idem
    input interpretation z omega k g endpoint_eq

/-- Core target image of the selected comparison. -/
noncomputable def semanticExactBarCoreDTargetKaroubiAt :
    Karoubi (CoreFiber input.square.northeast) where
  X := semanticExactBarViaGlobalCoreAt input interpretation z endpoint_eq
  p := semanticExactBarTargetGlobalCoreProjectorAt
    input interpretation z omega endpoint_eq
  idem := semanticExactBarTargetGlobalCoreProjectorAt_idem
    input interpretation z omega k g endpoint_eq

/-- The independent selected core beta induces an isomorphism of its images. -/
noncomputable def semanticExactBarCoreBetaKaroubiIsoAt :
    semanticExactBarCoreESourceKaroubiAt
        input interpretation z omega k g endpoint_eq ≅
      semanticExactBarCoreDTargetKaroubiAt
        input interpretation z omega k g endpoint_eq := by
  let m := (semanticCoreBeckChevalleyMate input).app
    (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)
  let D := semanticExactBarTargetGlobalCoreProjectorAt
    input interpretation z omega endpoint_eq
  letI : IsIso m := semanticCoreBeckChevalleyMate_app_isIso input _
  have hD : D ≫ D = D :=
    semanticExactBarTargetGlobalCoreProjectorAt_idem
      input interpretation z omega k g endpoint_eq
  refine
    { hom :=
        { f := semanticExactBarCoreBetaAt
            input interpretation z omega endpoint_eq
          comm := by
            change (m ≫ D ≫ inv m) ≫ (m ≫ D) ≫ D = m ≫ D
            simp [Category.assoc, hD] }
      inv :=
        { f := D ≫ inv m
          comm := by
            change D ≫ (D ≫ inv m) ≫ (m ≫ D ≫ inv m) = D ≫ inv m
            simp [Category.assoc, hD] }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Karoubi.Hom.ext
    change (m ≫ D) ≫ (D ≫ inv m) = m ≫ D ≫ inv m
    simp only [Category.assoc]
    rw [← Category.assoc D D (inv m), hD]
  · apply Karoubi.Hom.ext
    change (D ≫ inv m) ≫ (m ≫ D) = D
    simp [Category.assoc, hD]

end CoreImage

/-- Project every northeast geometric image and its arrows to the core. -/
noncomputable def semanticExactNortheastKaroubiProjection
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    Karoubi (GeomFiber.{u, v} input.square.northeast) ⥤
      Karoubi (CoreFiber input.square.northeast) :=
  (functorExtension₂ _ _).obj
    (geometryFiberProjection input.square.northeast)

private noncomputable def karoubiIsoOfUnderlyingIso
    {C : Type u} [Category.{v} C] (P Q : Karoubi C)
    (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q := by
  have hInv : Q.p ≫ e.inv = e.inv ≫ P.p := by
    apply (cancel_mono e.hom).1
    calc
      (Q.p ≫ e.inv) ≫ e.hom = Q.p := by simp
      _ = e.inv ≫ (e.hom ≫ Q.p) := by simp
      _ = e.inv ≫ (P.p ≫ e.hom) := by rw [h]
      _ = (e.inv ≫ P.p) ≫ e.hom := by simp
  refine
    { hom :=
        { f := P.p ≫ e.hom
          comm := by
            simp only [← Category.assoc]
            rw [P.idem, h]
            simp only [Category.assoc, Q.idem] }
      inv :=
        { f := Q.p ≫ e.inv
          comm := by
            simp only [← Category.assoc]
            rw [Q.idem, hInv]
            simp only [Category.assoc, P.idem] }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f, Karoubi.id_f]
    rw [h]
    simp only [Category.assoc]
    rw [← Category.assoc Q.p Q.p e.inv, Q.idem, hInv]
    simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  · apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f, Karoubi.id_f]
    rw [hInv]
    simp only [Category.assoc]
    rw [← Category.assoc P.p P.p e.hom, P.idem, h]
    simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]

section ProjectionAlignment

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) = input.square.southwest)
variable (square_isPullback : IsPullback input.square.left input.square.top
  input.square.bottom input.square.right)

/-- The image isomorphism obtained by projecting the actual geometry image. -/
noncomputable def semanticExactBarBetaProjectedKaroubiIsoAt :
    (semanticExactNortheastKaroubiProjection input).obj
        (semanticExactBarESourceKaroubiAt input interpretation z omega k g
          endpoint_eq square_isPullback) ≅
      (semanticExactNortheastKaroubiProjection input).obj
        (semanticExactBarDTargetKaroubiAt input interpretation z omega k g
          endpoint_eq) :=
  (semanticExactNortheastKaroubiProjection input).mapIso
    (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g
      endpoint_eq square_isPullback)

/-- The source endpoint comparison restricted to its Karoubi images. -/
noncomputable def semanticExactBarESourceKaroubiProjectionIsoAt :
    (semanticExactNortheastKaroubiProjection input).obj
        (semanticExactBarESourceKaroubiAt input interpretation z omega k g
          endpoint_eq square_isPullback) ≅
      semanticExactBarCoreESourceKaroubiAt
        input interpretation z omega k g endpoint_eq :=
  karoubiIsoOfUnderlyingIso _ _
    (semanticDerivedDirectCoreIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (by
      change
        (geometryFiberProjection input.square.northeast).map
            (semanticExactBarEAt input interpretation z omega k g endpoint_eq
              square_isPullback) ≫
          (semanticDerivedDirectCoreIsoAt input
            (semanticExactBarSourceCoreAt input interpretation z)
            k g endpoint_eq).hom =
        (semanticDerivedDirectCoreIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq).hom ≫
        semanticExactBarCoreEAt input interpretation z omega endpoint_eq
      exact semanticExactBarEAt_projection
        input interpretation z omega k g endpoint_eq square_isPullback)

/-- The target endpoint comparison restricted to its Karoubi images. -/
noncomputable def semanticExactBarDTargetKaroubiProjectionIsoAt :
    (semanticExactNortheastKaroubiProjection input).obj
        (semanticExactBarDTargetKaroubiAt input interpretation z omega k g
          endpoint_eq) ≅
      semanticExactBarCoreDTargetKaroubiAt
        input interpretation z omega k g endpoint_eq :=
  karoubiIsoOfUnderlyingIso _ _
    (semanticDerivedViaBaseCoreIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (by
      change
        (geometryFiberProjection input.square.northeast).map
            (semanticExactBarDAt input interpretation z omega k g endpoint_eq) ≫
          (semanticDerivedViaBaseCoreIsoAt input
            (semanticExactBarSourceCoreAt input interpretation z)
            k g endpoint_eq).hom =
        (semanticDerivedViaBaseCoreIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq).hom ≫
        semanticExactBarTargetGlobalCoreProjectorAt
          input interpretation z omega endpoint_eq
      exact semanticExactBarDAt_projection
        input interpretation z omega k g endpoint_eq)

/-- Proposition 6.17: the projected geometry image comparison is the
independently generated core image comparison after the two endpoint
isomorphisms. -/
noncomputable def semanticExactBarBetaKaroubiProjectionAlignmentAt :
    Arrow.mk (semanticExactBarBetaProjectedKaroubiIsoAt
        input interpretation z omega k g endpoint_eq square_isPullback).hom ≅
      Arrow.mk (semanticExactBarCoreBetaKaroubiIsoAt
        input interpretation z omega k g endpoint_eq).hom :=
  Arrow.isoMk
    (semanticExactBarESourceKaroubiProjectionIsoAt
      input interpretation z omega k g endpoint_eq square_isPullback)
    (semanticExactBarDTargetKaroubiProjectionIsoAt
      input interpretation z omega k g endpoint_eq)
    (by
      apply Karoubi.Hom.ext
      symm
      let F := geometryFiberProjection input.square.northeast
      let barBeta := semanticExactBarBetaAt input interpretation z omega k g
        endpoint_eq square_isPullback
      let jD := semanticDerivedDirectCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq
      let jV := semanticDerivedViaBaseCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq
      let coreBeta := semanticExactBarCoreBetaAt
        input interpretation z omega endpoint_eq
      let sourceP := ((semanticExactNortheastKaroubiProjection input).obj
        (semanticExactBarESourceKaroubiAt input interpretation z omega k g
          endpoint_eq square_isPullback)).p
      let targetP := ((semanticExactNortheastKaroubiProjection input).obj
        (semanticExactBarDTargetKaroubiAt input interpretation z omega k g
          endpoint_eq)).p
      have hProj : F.map barBeta ≫ jV.hom = jD.hom ≫ coreBeta :=
        semanticExactBarBetaAt_projection input interpretation z omega k g
          endpoint_eq square_isPullback
      have hSource : sourceP ≫ F.map barBeta = F.map barBeta := by
        have h := Karoubi.p_comp
          (semanticExactBarBetaProjectedKaroubiIsoAt
            input interpretation z omega k g endpoint_eq
            square_isPullback).hom
        change sourceP ≫ F.map barBeta = F.map barBeta at h
        exact h
      have hTarget : F.map barBeta ≫ targetP = F.map barBeta := by
        have h := Karoubi.comp_p
          (semanticExactBarBetaProjectedKaroubiIsoAt
            input interpretation z omega k g endpoint_eq
            square_isPullback).hom
        change F.map barBeta ≫ targetP = F.map barBeta at h
        exact h
      change F.map barBeta ≫ (targetP ≫ jV.hom) =
        (sourceP ≫ jD.hom) ≫ coreBeta
      calc
        F.map barBeta ≫ (targetP ≫ jV.hom) =
            (F.map barBeta ≫ targetP) ≫ jV.hom := by rw [Category.assoc]
        _ = F.map barBeta ≫ jV.hom := by rw [hTarget]
        _ = sourceP ≫ (F.map barBeta ≫ jV.hom) := by
          rw [← Category.assoc, hSource]
        _ = sourceP ≫ (jD.hom ≫ coreBeta) := by rw [hProj]
        _ = (sourceP ≫ jD.hom) ≫ coreBeta := by rw [Category.assoc])

end ProjectionAlignment

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
