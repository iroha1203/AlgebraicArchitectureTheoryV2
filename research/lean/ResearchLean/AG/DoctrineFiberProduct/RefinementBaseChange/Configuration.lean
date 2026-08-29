import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChangeSchema

/-!
# Raw refinement base-change configurations

The G-114 revision-3 input is deliberately unpointed.  A compatible pair of
sources is selected only after the exact cospan and refinement have been fixed;
all pointed endpoints and both pullbacks are then generated from that choice.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-- An unpointed exact cospan together with an unpointed refinement of its first leg. -/
structure RefinementBCConfiguration (U : AtomCarrier.{u}) where
  /-- Refined first endpoint. -/
  sOnePrime : ExtractionDoctrine U
  /-- Original first endpoint. -/
  sOne : ExtractionDoctrine U
  /-- Second endpoint. -/
  sTwo : ExtractionDoctrine U
  /-- Bottom doctrine. -/
  bottom : ExtractionDoctrine U
  /-- First exact cospan leg. -/
  fst : ExactDoctrineHom sOne bottom
  /-- Second exact cospan leg. -/
  snd : ExactDoctrineHom sTwo bottom
  /-- Unpointed forward refinement. -/
  refinement : RefinementDoctrineHom sOnePrime sOne

namespace RefinementBCConfiguration

/-- A source pair on which the refined and second exact legs meet at the bottom. -/
structure CompatibleSource (C : RefinementBCConfiguration U) where
  /-- Selected source in the refined endpoint. -/
  sourcePrime : C.sOnePrime.Source
  /-- Selected source in the second endpoint. -/
  sourceTwo : C.sTwo.Source
  /-- Compatibility at the bottom doctrine. -/
  bottom_eq :
    C.fst.sourceMap (C.refinement.sourceMap sourcePrime) =
      C.snd.sourceMap sourceTwo

/-- Canonically selected source in the original first endpoint. -/
def sourceOneAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    C.sOne.Source := C.refinement.sourceMap p.sourcePrime

/-- Canonically selected common source in the bottom doctrine. -/
def bottomSourceAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    C.bottom.Source := C.fst.sourceMap (C.sourceOneAt p)

/-- Repointed refined endpoint. -/
def sourcePointAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    ExtractionInstance U := ⟨C.sOnePrime, p.sourcePrime⟩

/-- Repointed original first endpoint; this is the target of the base refinement. -/
def targetPointAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    ExtractionInstance U := ⟨C.sOne, C.sourceOneAt p⟩

/-- Repointed second endpoint. -/
def secondPointAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    ExtractionInstance U := ⟨C.sTwo, p.sourceTwo⟩

/-- Repointed bottom endpoint. -/
def bottomPointAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    ExtractionInstance U := ⟨C.bottom, C.bottomSourceAt p⟩

/-- The first exact leg after canonical repointing. -/
def fstAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    C.targetPointAt p ⟶ C.bottomPointAt p where
  doctrineHom := C.fst
  source_eq := rfl

/-- The second exact leg after canonical repointing. -/
def sndAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    C.secondPointAt p ⟶ C.bottomPointAt p where
  doctrineHom := C.snd
  source_eq := p.bottom_eq.symm

/-- The base refinement after canonical repointing. -/
def baseRefinementAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    PointedRefinementHom (C.sourcePointAt p) (C.targetPointAt p) where
  doctrineHom := C.refinement
  source_eq := rfl

/-- Revision-1's pointed schema, generated rather than supplied. -/
def pointedConfigurationAt (C : RefinementBCConfiguration U)
    (p : CompatibleSource C) : LegacyRefinementBCConfiguration U where
  DOnePrime := C.sourcePointAt p
  DOne := C.targetPointAt p
  DTwo := C.secondPointAt p
  Base := C.bottomPointAt p
  sigmaOne := C.fstAt p
  sigmaTwo := C.sndAt p
  refinement := C.baseRefinementAt p

/-- Generated mixed pullback source endpoint. -/
def pullbackSourceAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    ExtractionInstance U := (C.pointedConfigurationAt p).pulled

/-- Generated exact pullback target endpoint. -/
def pullbackTargetAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    ExtractionInstance U := (C.pointedConfigurationAt p).pullback

/-- Generated pulled refinement. -/
def pulledRefinementAt (C : RefinementBCConfiguration U) (p : CompatibleSource C) :
    PointedRefinementHom (C.pullbackSourceAt p) (C.pullbackTargetAt p) :=
  (C.pointedConfigurationAt p).pulledRefinement

/-- The generated forward square commutes for every compatible source. -/
theorem pulled_square_commutes_at (C : RefinementBCConfiguration U)
    (p : CompatibleSource C) :
    (C.pointedConfigurationAt p).pulledRefinement.comp
        (PointedRefinementHom.ofExact (C.pointedConfigurationAt p).pullbackFst) =
      (PointedRefinementHom.ofExact (C.pointedConfigurationAt p).pulledFst).comp
        (C.baseRefinementAt p) :=
  (C.pointedConfigurationAt p).pulled_square_commutes

end RefinementBCConfiguration

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
