import Formal.SHIGURE.Part2.Recovery.RelativePullbackSite

/-!
# Sheaf charts on the Zariski cover of a coefficient scheme

Each chart has its own relative Zariski site. Transition isomorphisms
are given on the actual fiber products of the open immersions.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} (C : Scheme.OpenCover.{u} S)

/-- The overlap of two cover members is their actual fiber product. -/
abbrev CoverOverlap (i j : C.I₀) := pullback (C.f i) (C.f j)

/-- Local sheaves with isomorphisms on each overlap. -/
structure SheafCharts where
  /-- The local sheaf on its own relative site. -/
  chart (i : C.I₀) : ZariskiSheaf (C.X i)
  /-- Compare the two restrictions to their actual overlap. -/
  transition (i j : C.I₀) :
    (Scheme.zariskiTopology.overMapPullback (Type u) (pullback.fst (C.f i) (C.f j))).obj (chart i) ≅
      (Scheme.zariskiTopology.overMapPullback (Type u) (pullback.snd (C.f i) (C.f j))).obj (chart j)

end SHIGURE.Copying
