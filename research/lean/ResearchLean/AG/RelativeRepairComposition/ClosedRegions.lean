import ResearchLean.AG.RelativeRepairComposition.SupportedRepairs

/-!
# Closed original cell regions and restriction of the original differentials

Incidence includes both face paths and every face, prefix and suffix of the
three-cell rewriting sequences. Coefficients retain their original indices and
transports. Zero extension is only a degreewise auxiliary map; the chain-map
statements are proved for restriction using the closure conditions.
-/

namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uG uA
variable {K : FiniteTransportPresentation.{uG}}

/-- All original edge occurrences in a typed path. -/
def pathEdges : {i j : K.Vertex} → K.Path i j → Set (EdgeName (K := K))
  | _, _, .nil _ => ∅
  | _, _, .cons e w => {⟨_,_,e⟩} ∪ pathEdges w

/-- Original face names in a typed pasting. -/
def pastingFaces {i j : K.Vertex} {w z : K.Path i j} :
    RewritePasting K.toFiniteTransportTwoPresentation w z → Set K.TwoCell
  | .nil _ => ∅
  | .cons step tail => {step.face.cell} ∪ pastingFaces tail

/-- Edges of the prefix and suffix in every typed rewriting context. -/
def pastingContextEdges {i j : K.Vertex} {w z : K.Path i j} :
    RewritePasting K.toFiniteTransportTwoPresentation w z → Set (EdgeName (K := K))
  | .nil _ => ∅
  | .cons step tail => pathEdges step.face.incoming ∪ pathEdges step.face.outgoing ∪
      pastingContextEdges tail

/-- Subsets of the original cells closed under their full geometric incidence. -/
structure ClosedRegion (K : FiniteTransportPresentation.{uG}) where
  vertices : Set K.Vertex
  edges : Set (EdgeName (K := K))
  faces : Set K.TwoCell
  triples : Set K.ThreeCell
  edge_closed : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2.1 ∈ vertices
  face_closed : ∀ f ∈ faces,
    K.twoSource f ∈ vertices ∧ K.twoTarget f ∈ vertices ∧
    pathEdges (K.twoLeft f) ⊆ edges ∧ pathEdges (K.twoRight f) ⊆ edges
  triple_closed : ∀ s ∈ triples,
    K.threeSource s ∈ vertices ∧ K.threeTarget s ∈ vertices ∧
    pathEdges (K.threeStart s) ⊆ edges ∧ pathEdges (K.threeFinish s) ⊆ edges ∧
    pastingFaces (K.threeLeft s) ⊆ faces ∧ pastingFaces (K.threeRight s) ⊆ faces ∧
    pastingContextEdges (K.threeLeft s) ⊆ edges ∧
    pastingContextEdges (K.threeRight s) ⊆ edges

variable (M : LocalCoefficients.{uG,uA} K)

/-- Edgewise agreement on a path determines its original correction. -/
theorem pathCorrection_congr_on (h k : C1 M) {i j : K.Vertex} (w : K.Path i j)
    (hk : ∀ e ∈ pathEdges w, h e = k e) : pathCorrection M h w = pathCorrection M k w := by
  induction w with
  | nil v => rfl
  | cons e tail ih =>
    rw [pathCorrection_cons, pathCorrection_cons, hk _ (Or.inl rfl),
      ih (fun a ha => hk a (Or.inr ha))]

/-- Facewise agreement determines the original typed pasting correction. -/
theorem pastingCorrection_congr_on (h k : C2 M) {i j : K.Vertex}
    {w z : K.Path i j} (P : RewritePasting K.toFiniteTransportTwoPresentation w z)
    (hk : ∀ f ∈ pastingFaces P, h f = k f) :
    pastingCorrection M h P = pastingCorrection M k P := by
  induction P with
  | nil w => rfl
  | cons step tail ih =>
    have hf : faceCorrection M h step.face = faceCorrection M k step.face := by
      cases step with
      | mk face hb ha =>
        cases face with
        | mk f incoming outgoing orient =>
          have he := hk f (Or.inl rfl)
          cases orient <;> simp only [faceCorrection, he]
    rw [pastingCorrection, pastingCorrection, hf, ih (fun f hf => hk f (Or.inr hf))]

namespace Family
universe uI uB
variable {I : Type uI} (A : I → Type uB) [∀ i, AddCommGroup (A i)]
/-- Restriction of dependent coefficient families to the same original indices. -/
def restrict (s : Set I) : (∀ i, A i) →+ (∀ i : s, A i.1) where
  toFun b i := b i.1
  map_zero' := rfl
  map_add' _ _ := rfl
/-- Degreewise zero extension, without a chain-map assertion. -/
noncomputable def extend (s : Set I) : (∀ i : s, A i.1) →+ (∀ i, A i) := by
  classical
  exact {
    toFun := fun b i => if hi : i ∈ s then b ⟨i,hi⟩ else 0
    map_zero' := by funext i; split <;> rfl
    map_add' := by
      intro b c
      funext i
      by_cases hi : i ∈ s <;> simp [hi] }
/-- The extension has exactly the original value on the chosen subset. -/
theorem extend_on (s : Set I) (b : ∀ i : s, A i.1) (i : I) (hi : i ∈ s) :
    extend A s b i = b ⟨i,hi⟩ := by
  classical
  simp [extend, hi]
/-- Restriction after degreewise extension is identity. -/
theorem restrict_extend (s : Set I) (b : ∀ i : s, A i.1) :
    restrict A s (extend A s b) = b := by
  funext i
  exact extend_on A s b i.1 i.2
end Family

namespace ClosedRegion
variable (U : ClosedRegion K)
/-- Original coefficients on the selected vertices. -/
abbrev C0 := ∀ v : U.vertices, M.A v.1
/-- Original terminal coefficients on the selected edges. -/
abbrev C1 := ∀ e : U.edges, M.A e.1.2.1
/-- Original terminal coefficients on the selected faces. -/
abbrev C2 := ∀ f : U.faces, M.A (K.twoTarget f.1)
/-- Original terminal coefficients on the selected 3-cells. -/
abbrev C3 := ∀ s : U.triples, M.A (K.threeTarget s.1)
/-- Restriction in degree zero. -/
def r0 := Family.restrict M.A U.vertices
/-- Restriction in degree one. -/
def r1 := Family.restrict (fun e : EdgeName (K := K) => M.A e.2.1) U.edges
/-- Restriction in degree two. -/
def r2 := Family.restrict (fun f => M.A (K.twoTarget f)) U.faces
/-- Restriction in degree three. -/
def r3 := Family.restrict (fun s => M.A (K.threeTarget s)) U.triples
/-- Zero extension in degree zero. -/
noncomputable def e0 := Family.extend M.A U.vertices
/-- Zero extension in degree one. -/
noncomputable def e1 := Family.extend (fun e : EdgeName (K := K) => M.A e.2.1) U.edges
/-- Zero extension in degree two. -/
noncomputable def e2 := Family.extend (fun f => M.A (K.twoTarget f)) U.faces
/-- The original d0 on selected endpoints. -/
noncomputable def d0Hom : C0 M U →+ C1 M U :=
  (r1 M U).comp ((AbelianLiftingObstruction.d0Hom M).comp (e0 M U))
/-- The original d1 on selected face paths. -/
noncomputable def d1Hom : C1 M U →+ C2 M U :=
  (r2 M U).comp ((AbelianLiftingObstruction.d1Hom M).comp (e1 M U))
/-- The original d2 on selected typed pastings. -/
noncomputable def d2Hom : C2 M U →+ C3 M U :=
  (r3 M U).comp ((AbelianLiftingObstruction.d2Hom M).comp (e2 M U))
/-- Restriction commutes with d0 by closure of the same endpoints. -/
theorem r_d0 (b : AbelianLiftingObstruction.C0 M) :
    r1 M U (d0 M b) = d0Hom M U (r0 M U b) := by
  funext e
  rcases e with ⟨⟨i,j,e⟩,he⟩
  change b j - M.edge e (b i) =
    e0 M U (r0 M U b) j - M.edge e (e0 M U (r0 M U b) i)
  change b j - M.edge e (b i) =
    Family.extend M.A U.vertices (r0 M U b) j -
      M.edge e (Family.extend M.A U.vertices (r0 M U b) i)
  rw [Family.extend_on M.A _ _ j (U.edge_closed _ he).2,
    Family.extend_on M.A _ _ i (U.edge_closed _ he).1]
  rfl
/-- Restriction commutes with d1 by closure of both original face paths. -/
theorem r_d1 (h : AbelianLiftingObstruction.C1 M) :
    r2 M U (d1 M h) = d1Hom M U (r1 M U h) := by
  funext f
  change pathCorrection M h (K.twoLeft f.1) - pathCorrection M h (K.twoRight f.1) =
    pathCorrection M (e1 M U (r1 M U h)) (K.twoLeft f.1) -
      pathCorrection M (e1 M U (r1 M U h)) (K.twoRight f.1)
  congr 1
  · apply pathCorrection_congr_on M
    intro e he
    exact (Family.extend_on (fun e : EdgeName (K := K) => M.A e.2.1)
      U.edges (r1 M U h) e ((U.face_closed _ f.2).2.2.1 he)).symm
  · apply pathCorrection_congr_on M
    intro e he
    exact (Family.extend_on (fun e : EdgeName (K := K) => M.A e.2.1)
      U.edges (r1 M U h) e ((U.face_closed _ f.2).2.2.2 he)).symm
/-- Restriction commutes with d2 by closure of all original pasting faces. -/
theorem r_d2 (c : AbelianLiftingObstruction.C2 M) :
    r3 M U (d2 M c) = d2Hom M U (r2 M U c) := by
  funext s
  change pastingCorrection M c (K.threeLeft s.1) - pastingCorrection M c (K.threeRight s.1) =
    pastingCorrection M (e2 M U (r2 M U c)) (K.threeLeft s.1) -
      pastingCorrection M (e2 M U (r2 M U c)) (K.threeRight s.1)
  congr 1
  · apply pastingCorrection_congr_on M
    intro f hf
    exact (Family.extend_on (fun f => M.A (K.twoTarget f)) U.faces
      (r2 M U c) f ((U.triple_closed _ s.2).2.2.2.2.1 hf)).symm
  · apply pastingCorrection_congr_on M
    intro f hf
    exact (Family.extend_on (fun f => M.A (K.twoTarget f)) U.faces
      (r2 M U c) f ((U.triple_closed _ s.2).2.2.2.2.2.1 hf)).symm
/-- The restricted differential still squares to zero in degrees zero and one. -/
theorem d1_d0 (b : C0 M U) : d1Hom M U (d0Hom M U b) = 0 := by
  have hr := r_d0 M U (e0 M U b)
  have hi : r0 M U (e0 M U b) = b := Family.restrict_extend _ _ _
  rw [hi] at hr
  rw [← hr, ← r_d1, AbelianLiftingObstruction.d1_d0, map_zero]
/-- The restricted differential still squares to zero in degrees one and two. -/
theorem d2_d1 (h : C1 M U) : d2Hom M U (d1Hom M U h) = 0 := by
  have hr := r_d1 M U (e1 M U h)
  have hi : r1 M U (e1 M U h) = h := Family.restrict_extend _ _ _
  rw [hi] at hr
  rw [← hr, ← r_d2, AbelianLiftingObstruction.d2_d1, map_zero]
end ClosedRegion
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
