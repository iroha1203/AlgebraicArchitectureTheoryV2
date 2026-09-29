import ResearchLean.AG.AbelianLiftingObstruction.LocalCoefficients

/-!
# Cochains of the finite presentation with local coefficients

G-129 A3: the groups use all vertices, edges, faces, and 3-cells of the same
presentation. Path correction counts each occurrence of an edge, including a
repeated generator; the empty path has zero correction.

## Implementation notes

Dependent products preserve the endpoint group of every generator. The path
formula is recursive because a list of untyped edges would discard endpoints.
-/

namespace AAT.AG.AbelianLiftingObstruction

open TransportCoherence

universe uG uA

variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K)

/-- G-129 A3: vertex cochains. -/
abbrev C0 := ∀ v : K.Vertex, M.A v

/-- G-129 A3: edge cochains, with values at the terminal vertex. -/
abbrev C1 := (e : Σ i : K.Vertex, Σ j : K.Vertex, K.Edge i j) → M.A e.2.1

/-- G-129 A3: face cochains, with values at the terminal vertex. -/
abbrev C2 := ∀ f : K.TwoCell, M.A (K.twoTarget f)

/-- G-129 A3: 3-cell cochains, with values at the terminal vertex. -/
abbrev C3 := ∀ s : K.ThreeCell, M.A (K.threeTarget s)

/-- G-129 A3: total correction of a path, with one term per edge occurrence. -/
def pathCorrection (h : C1 M) :
    ∀ {i j : K.Vertex}, K.Path i j → M.A j
  | _, _, .nil _ => 0
  | _, _, .cons e tail => M.pathTransport tail (h ⟨_, _, e⟩) + pathCorrection h tail

/-- API: correction of an empty path is zero. -/
@[simp] theorem pathCorrection_nil (h : C1 M) (v : K.Vertex) :
    pathCorrection M h (PresentedPath.nil v) = 0 := rfl

/-- API: a cons path counts its first edge and the remaining path separately. -/
@[simp] theorem pathCorrection_cons (h : C1 M) {i j k : K.Vertex}
    (e : K.Edge i j) (w : K.Path j k) :
    pathCorrection M h (PresentedPath.cons e w) =
      M.pathTransport w (h ⟨i, j, e⟩) + pathCorrection M h w := rfl

/-- G-129 A3: corrections concatenate using transport of the first part. -/
theorem pathCorrection_append (h : C1 M) {i j k : K.Vertex}
    (w : K.Path i j) (z : K.Path j k) :
    pathCorrection M h (w.append z) =
      M.pathTransport z (pathCorrection M h w) + pathCorrection M h z := by
  induction w with
  | nil _ => simp only [PresentedPath.append, pathCorrection_nil,
      map_zero, zero_add]
  | cons e tail ih =>
      simp only [PresentedPath.append, pathCorrection_cons, ih,
        M.pathTransport_append, AddEquiv.trans_apply, map_add]
      abel

/-- G-129 A3: vertex gauge differential on an actual edge. -/
def d0 (b : C0 M) : C1 M :=
  fun ⟨i, j, e⟩ => b j - M.edge e (b i)

/-- G-129 A3: the vertex differential telescopes along every finite path. -/
theorem pathCorrection_d0 (b : C0 M) {i j : K.Vertex} (w : K.Path i j) :
    pathCorrection M (d0 M b) w = b j - M.pathTransport w (b i) := by
  induction w with
  | nil _ => simp
  | cons e tail ih =>
      simp only [pathCorrection_cons, d0, ih, M.pathTransport_cons,
        AddEquiv.trans_apply, map_sub]
      abel

/-- G-129 A3: face differential using the authored left and right paths. -/
def d1 (h : C1 M) : C2 M :=
  fun f => pathCorrection M h (K.twoLeft f) - pathCorrection M h (K.twoRight f)

/-- G-129 A3: the face differential kills every vertex coboundary. -/
theorem d1_d0 (b : C0 M) : d1 M (d0 M b) = 0 := by
  funext f
  simp only [d1, pathCorrection_d0]
  rw [M.transport_face f]
  exact sub_self _

/-- The signed value of a face at the end of a whiskered rewrite. -/
def faceCorrection (c : C2 M) {source target : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation source target) : M.A target :=
  match f.orientation with
  | .forward => M.pathTransport f.outgoing (c f.cell)
  | .backward => -M.pathTransport f.outgoing (c f.cell)

/-- Sum of signed, transported face values over a typed rewrite pasting. -/
def pastingCorrection (c : C2 M) {source target : K.Vertex}
    {before after : K.Path source target} :
    RewritePasting K.toFiniteTransportTwoPresentation before after → M.A target
  | .nil _ => 0
  | .cons step tail => faceCorrection M c step.face + pastingCorrection c tail

/-- G-129 A3: compare the two authored pastings of each 3-cell. -/
def d2 (c : C2 M) : C3 M :=
  fun s => pastingCorrection M c (K.threeLeft s) -
    pastingCorrection M c (K.threeRight s)

/-- G-129 A3: a whiskered face changes path correction by its transported local difference. -/
private theorem pathCorrection_whisker (h : C1 M)
    {source a b target : K.Vertex}
    (incoming : K.Path source a) (left right : K.Path a b)
    (outgoing : K.Path b target)
    (heq : M.pathTransport left = M.pathTransport right) :
    pathCorrection M h (incoming.append (left.append outgoing)) -
      pathCorrection M h (incoming.append (right.append outgoing)) =
      M.pathTransport outgoing (pathCorrection M h left - pathCorrection M h right) := by
  simp only [pathCorrection_append, M.pathTransport_append,
    AddEquiv.trans_apply, map_sub]
  rw [heq]
  abel

/-- G-129 A3: an oriented rewrite evaluates `d¹h` as the change of its two paths. -/
theorem faceCorrection_d1 (h : C1 M) {source target : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation source target) :
    faceCorrection M (d1 M h) f =
      pathCorrection M h f.before - pathCorrection M h f.after := by
  cases f with
  | mk cell incoming outgoing orientation =>
      cases orientation with
      | forward =>
          simp only [faceCorrection, d1, WhiskeredFace.before,
            WhiskeredFace.after, WhiskeredFace.localBefore,
            WhiskeredFace.localAfter]
          exact (pathCorrection_whisker M h incoming (K.twoLeft cell)
            (K.twoRight cell) outgoing (M.transport_face cell)).symm
      | backward =>
          simp only [faceCorrection, d1, WhiskeredFace.before,
            WhiskeredFace.after, WhiskeredFace.localBefore,
            WhiskeredFace.localAfter]
          have hforward := pathCorrection_whisker M h incoming (K.twoLeft cell)
            (K.twoRight cell) outgoing (M.transport_face cell)
          rw [← hforward]
          abel

/-- G-129 A3: all intermediate paths cancel in a typed rewrite pasting. -/
theorem pastingCorrection_d1 (h : C1 M) {source target : K.Vertex}
    {before after : K.Path source target}
    (P : RewritePasting K.toFiniteTransportTwoPresentation before after) :
    pastingCorrection M (d1 M h) P =
      pathCorrection M h before - pathCorrection M h after := by
  induction P with
  | nil _ => simp [pastingCorrection]
  | cons step tail ih =>
      rcases step with ⟨face, rfl, rfl⟩
      simp only [pastingCorrection, faceCorrection_d1, ih]
      abel

/-- G-129 A3: the two pastings of a 3-cell yield the same telescoping difference. -/
theorem d2_d1 (h : C1 M) : d2 M (d1 M h) = 0 := by
  funext s
  simp only [d2, pastingCorrection_d1]
  exact sub_self _

/-- API: the vertex differential preserves addition. -/
theorem d0_add (b c : C0 M) : d0 M (b + c) = d0 M b + d0 M c := by
  funext ⟨i, j, e⟩
  simp only [d0, Pi.add_apply, map_add]
  abel

/-- API: path correction preserves addition of edge cochains. -/
theorem pathCorrection_add (h k : C1 M) {i j : K.Vertex} (w : K.Path i j) :
    pathCorrection M (h + k) w = pathCorrection M h w + pathCorrection M k w := by
  induction w with
  | nil _ => simp only [pathCorrection_nil, add_zero]
  | cons e tail ih =>
      simp only [pathCorrection_cons, Pi.add_apply, map_add, ih]
      abel

/-- API: the face differential preserves addition. -/
theorem d1_add (h k : C1 M) : d1 M (h + k) = d1 M h + d1 M k := by
  funext f
  simp only [d1, pathCorrection_add, Pi.add_apply]
  abel

/-- API: oriented face evaluation preserves addition. -/
theorem faceCorrection_add (c d : C2 M) {source target : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation source target) :
    faceCorrection M (c + d) f = faceCorrection M c f + faceCorrection M d f := by
  cases f with
  | mk cell incoming outgoing orientation =>
      cases orientation with
      | forward => simp only [faceCorrection, Pi.add_apply, map_add]
      | backward =>
          simp only [faceCorrection, Pi.add_apply, map_add]
          abel

/-- API: a typed pasting evaluates cochains additively. -/
theorem pastingCorrection_add (c d : C2 M) {source target : K.Vertex}
    {before after : K.Path source target}
    (P : RewritePasting K.toFiniteTransportTwoPresentation before after) :
    pastingCorrection M (c + d) P =
      pastingCorrection M c P + pastingCorrection M d P := by
  induction P with
  | nil _ => simp only [pastingCorrection, add_zero]
  | cons step tail ih =>
      simp only [pastingCorrection, faceCorrection_add, ih]
      abel

/-- API: the 3-cell differential preserves addition. -/
theorem d2_add (c d : C2 M) : d2 M (c + d) = d2 M c + d2 M d := by
  funext s
  simp only [d2, pastingCorrection_add, Pi.add_apply]
  abel

/-- G-129 A3: the vertex differential as an additive homomorphism. -/
def d0Hom : C0 M →+ C1 M where
  toFun := d0 M
  map_zero' := by
    have h := d0_add M (0 : C0 M) (0 : C0 M)
    have h' : d0 M (0 : C0 M) + d0 M 0 = d0 M 0 + 0 := by
      simpa only [zero_add, add_zero] using h.symm
    exact add_left_cancel h'
  map_add' := d0_add M

/-- G-129 A3: the face differential as an additive homomorphism. -/
def d1Hom : C1 M →+ C2 M where
  toFun := d1 M
  map_zero' := by
    have h := d1_add M (0 : C1 M) (0 : C1 M)
    have h' : d1 M (0 : C1 M) + d1 M 0 = d1 M 0 + 0 := by
      simpa only [zero_add, add_zero] using h.symm
    exact add_left_cancel h'
  map_add' := d1_add M

/-- G-129 A3: the 3-cell differential as an additive homomorphism. -/
def d2Hom : C2 M →+ C3 M where
  toFun := d2 M
  map_zero' := by
    have h := d2_add M (0 : C2 M) (0 : C2 M)
    have h' : d2 M (0 : C2 M) + d2 M 0 = d2 M 0 + 0 := by
      simpa only [zero_add, add_zero] using h.symm
    exact add_left_cancel h'
  map_add' := d2_add M

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
