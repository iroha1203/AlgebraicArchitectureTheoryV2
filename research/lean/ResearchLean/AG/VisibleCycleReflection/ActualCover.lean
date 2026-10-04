import ResearchLean.AG.VisibleCycleReflection.OpenSupportContinuity
import ResearchLean.AG.ObstructionDiagnosticBridge.FaceEmptyCechNormalization
import Formal.Util.AssertStandardAxioms

/-!
# G-132: complete geometric nerve and the actual AAT Cech cover

## Implementation notes

Edges are ordered chart pairs with a nonempty actual intersection. Faces retain
ordered triples and their actual nonempty intersection, before T0 proves that
this complete index is empty. Target supports are independent sets on q.Target.
The construction uses all chart pairs; it never selects overlaps from target
visibility or a desired reflection conclusion.
-/

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace AAT.AG.VisibleCycleReflection

open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge

universe u

variable {Source X I : Type u} [TopologicalSpace X] [LinearOrder I]
variable {q : Reading Source}

/-- T0's geometric data; all properties are exactly the input cover hypotheses. -/
structure GeometricCover (X I : Type u) [TopologicalSpace X] [LinearOrder I] where
  patch : I → Opens X
  covers : ∀ x : X, ∃ i, x ∈ patch i
  chartNonempty : ∀ i, (patch i : Set X).Nonempty
  chartPreconnected : ∀ i, IsPreconnected (patch i : Set X)
  overlapPreconnected : ∀ i j, i < j →
    ((patch i ⊓ patch j : Opens X) : Set X).Nonempty →
    IsPreconnected ((patch i ⊓ patch j : Opens X) : Set X)
  tripleEmpty : ∀ i j k, i < j → j < k →
    ¬ ((patch i ⊓ patch j ⊓ patch k : Opens X) : Set X).Nonempty

namespace GeometricCover

variable (K : GeometricCover X I)

/-- A's complete oriented edge index, with intersection existence as proof data. -/
abbrev Edge := {ij : I × I // ij.1 < ij.2 ∧
  ((K.patch ij.1 ⊓ K.patch ij.2 : Opens X) : Set X).Nonempty}

/-- A's complete geometric face index, defined before applying triple emptiness. -/
abbrev Face := {ijk : I × I × I // ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2 ∧
  ((K.patch ijk.1 ⊓ K.patch ijk.2.1 ⊓ K.patch ijk.2.2 : Opens X) : Set X).Nonempty}

/-- T0 implies emptiness of the complete geometric face index. -/
instance faceIsEmpty : IsEmpty K.Face where
  false f := K.tripleEmpty f.val.1 f.val.2.1 f.val.2.2 f.property.1
    f.property.2.1 f.property.2.2

/-- A's complete nerve, built from actual intersections. -/
def nerve : Cohomology.CoverNerve where
  Chart := I
  EdgeComponent := K.Edge
  FaceComponent := K.Face
  edgeLeft e := e.val.1
  edgeRight e := e.val.2
  faceEdge0 f := isEmptyElim f
  faceEdge1 f := isEmptyElim f
  faceEdge2 f := isEmptyElim f
  edgeOverlapComponent e := ((K.patch e.val.1 ⊓ K.patch e.val.2 : Opens X) : Set X).Nonempty
  faceTripleOverlapComponent f := ((K.patch f.val.1 ⊓ K.patch f.val.2.1 ⊓ K.patch f.val.2.2 : Opens X) : Set X).Nonempty
  edgeOverlapComponent_holds e := e.property.2
  faceTripleOverlapComponent_holds f := f.property.2.2

/-- Completeness API: every nonempty ordered overlap gives one nerve edge. -/
def edgeOfOverlap (i j : I) (hij : i < j)
    (h : ((K.patch i ⊓ K.patch j : Opens X) : Set X).Nonempty) : K.Edge :=
  ⟨(i, j), hij, h⟩

/-- Edge uniqueness API: intersection witnesses do not duplicate an edge. -/
theorem edge_eq_of_endpoints {e f : K.Edge}
    (hl : e.val.1 = f.val.1) (hr : e.val.2 = f.val.2) : e = f :=
  Subtype.ext (Prod.ext hl hr)

/-- The actual open overlap used by the complete edge index. -/
def overlap (e : K.Edge) : Opens X := K.patch e.val.1 ⊓ K.patch e.val.2

/-- A's target-supported nerve has the same cells and independently supplied T_i. -/
def supportedNerve [Fintype I] (target : I → Set q.Target)
    (hne : ∀ i, (target i).Nonempty) : TargetSupportedNerve q where
  nerve := K.nerve
  chartFintype := show Fintype I from inferInstance
  edgeFintype := Fintype.ofFinite K.Edge
  faceFintype := show Fintype K.Face from Fintype.ofIsEmpty
  chartSupport := target
  chartSupport_nonempty := hne
  faceEdge0_left f := isEmptyElim (show K.Face from f)
  faceEdge0_right f := isEmptyElim (show K.Face from f)
  faceEdge1_right f := isEmptyElim (show K.Face from f)

/-- A: the supported nerve retains the proved empty complete face index. -/
instance supportedNerveFaceIsEmpty [Fintype I] (target : I → Set q.Target)
    (hne : ∀ i, (target i).Nonempty) :
    IsEmpty (K.supportedNerve target hne).nerve.FaceComponent := K.faceIsEmpty

/-- K1 API: target overlap remains distinct from the actual geometric overlap. -/
@[simp]
theorem supportedNerve_edgeSupport [Fintype I] (target : I → Set q.Target)
    (hne : ∀ i, (target i).Nonempty) (e : K.Edge) :
    (K.supportedNerve target hne).edgeSupport e = target e.val.1 ∩ target e.val.2 := rfl

variable {laws : FiniteLawFamily Source} (P : GeneratorPresentation laws)

/-- A's actual chart cover on the constructed primitive-input site is admissible. -/
theorem coverage_admissible [Nonempty I] :
    Site.AdmissibleCover (OpenSupport.coverageRequirements P)
      (OpenSupport.overlap P) (OpenSupport.coverageFamily P K.patch) :=
  OpenSupport.coverageFamily_admissible P K.patch K.covers

/-- A's actual Cech cover is constructed from every actual chart and overlap. -/
def actualCechCover [Fintype I] (target : I → Set q.Target)
    (hne : ∀ i, (target i).Nonempty) :
    GeneratorPresentation.FaceEmptyAATCechCover (K.supportedNerve target hne)
      (OpenSupport.contextOpenSupport (Space := X) P) where
  base := Site.ContextCategoryObject.of (OpenSupport.contextPreorder P)
    (OpenSupport.openContext P ⊤)
  chartContext i := Site.ContextCategoryObject.of (OpenSupport.contextPreorder P)
    (OpenSupport.openContext P (K.patch i))
  edgeContext e := Site.ContextCategoryObject.of (OpenSupport.contextPreorder P)
    (OpenSupport.openContext P (K.overlap e))
  inclusion _ := homOfLE (OpenSupport.openContext_le P le_top)
  edgeLeftRestriction _ := homOfLE (OpenSupport.openContext_le P inf_le_left)
  edgeRightRestriction _ := homOfLE (OpenSupport.openContext_le P inf_le_right)
  chartSupportNonempty i := by
    change Nonempty (OpenSupport.contextSupport P (OpenSupport.openContext P (K.patch i)))
    rw [OpenSupport.contextSupport_openContext]
    exact K.chartNonempty i |>.to_subtype
  chartSupportPreconnected i := by
    change PreconnectedSpace (OpenSupport.contextSupport P (OpenSupport.openContext P (K.patch i)))
    rw [OpenSupport.contextSupport_openContext]
    exact Subtype.preconnectedSpace (K.chartPreconnected i)
  edgeSupportNonempty e := by
    change Nonempty (OpenSupport.contextSupport P (OpenSupport.openContext P (K.overlap e)))
    rw [OpenSupport.contextSupport_openContext]
    exact e.property.2.to_subtype
  edgeSupportPreconnected e := by
    change PreconnectedSpace (OpenSupport.contextSupport P (OpenSupport.openContext P (K.overlap e)))
    rw [OpenSupport.contextSupport_openContext]
    exact Subtype.preconnectedSpace (K.overlapPreconnected e.val.1 e.val.2 e.property.1 e.property.2)

end GeometricCover
end AAT.AG.VisibleCycleReflection

#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
