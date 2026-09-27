import ResearchLean.AG.ProtocolHolonomy.FiniteDirectDecision
import Formal.Util.AssertStandardAxioms

/-!
# Finite simultaneous C1 root decision

For supplied root paths, explicit finite tables enumerate candidate root maps.
The test checks both inverse laws and every original named-edge loop equation
(C1), then reconstructs an original A1 lift through C2. This does not use the
direct A1 table test. An executable construction of root paths from the input
finite graph remains a separate E obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)
  (R : RootedPaths Q) (g : FixedFGraphAutomorphism Q)

/-- Candidate forward/inverse tables satisfy the simultaneous C1 equations
at the roots on every original named edge. -/
def ValidRootCandidate (f : D.CandidateMaps g) : Prop :=
  (∀ (x : Q.Vertex) (y : D.Fiber x), f.2 x (f.1 x y) = y) ∧
  (∀ (x : Q.Vertex) (y : D.Fiber (g.vertex x)), f.1 x (f.2 x y) = y) ∧
  (∀ (e : Q.Edge)
      (z : D.Fiber (R.root (fixedFComponentMk Q (Q.source e)))),
    f.1 (R.root (fixedFComponentMk Q (Q.source e)))
      (D.transport (R.edgeLoop e) z) =
    D.transport (renameSigned g (R.edgeLoop e))
      (f.1 (R.root (fixedFComponentMk Q (Q.source e))) z))

/-- A passing C1 table constructs actual root equivalences and all their
named-edge equations, without taking a vertexwise lift as input. -/
def rootSolutionsOfValidCandidate (f : D.CandidateMaps g)
    (hf : D.ValidRootCandidate R g f) : D.RootSolutions R g where
  rootFiber j :=
    { toFun := f.1 (R.root j)
      invFun := f.2 (R.root j)
      left_inv := hf.1 (R.root j)
      right_inv := hf.2.1 (R.root j) }
  edge_holonomy := by
    intro j e he
    cases he
    apply Equiv.ext
    intro z
    simpa [RootedPaths.edgeLoop, RootedPaths.edgeLoopAt,
      Equiv.trans_apply] using hf.2.2 e z

/-- Every original A1 lift gives a table that passes the C1 test. -/
theorem validRootCandidate_of_lift (a : D.Lift g) :
    D.ValidRootCandidate R g
      (⟨fun x => a.fiber x, fun x => (a.fiber x).symm⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact (a.fiber x).symm_apply_apply y
  · intro x y
    exact (a.fiber x).apply_symm_apply y
  · intro e z
    have h := a.signed_path_naturality D (R.edgeLoop e)
    have hz := congrArg (fun k => k z) h
    simpa only [Equiv.trans_apply] using hz

section Finite

variable [Fintype Q.Vertex] [Fintype Q.Edge]
  [∀ x : Q.Vertex, Fintype (D.Fiber x)]
  [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- C1 and inverse-table validity are decidable finite quantifications. -/
instance validRootCandidateDecidable (f : D.CandidateMaps g) :
    Decidable (D.ValidRootCandidate R g f) := by
  unfold ValidRootCandidate
  infer_instance

/-- Exhaustively test C1 on an explicit candidate list. -/
def searchRootCandidates :
    List (D.CandidateMaps g) →
      Option {f : D.CandidateMaps g // D.ValidRootCandidate R g f}
  | [] => none
  | f :: fs =>
      if hf : D.ValidRootCandidate R g f then some ⟨f, hf⟩
      else searchRootCandidates fs

/-- A negative C1 search excludes every listed candidate. -/
theorem searchRootCandidates_none (l : List (D.CandidateMaps g))
    (h : D.searchRootCandidates R g l = none) :
    ∀ f ∈ l, ¬ D.ValidRootCandidate R g f := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : D.ValidRootCandidate R g a
      · simp [searchRootCandidates, ha] at h
      · have htail : D.searchRootCandidates R g l = none := by
          simpa [searchRootCandidates, ha] using h
        intro f hf hv
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hmem
        · exact ha hv
        · exact ih htail f hmem hv

/-- The C1-selected table reconstructs an original A1 lift by C2. -/
def findRootLiftOnCandidates
    (candidates : List (D.CandidateMaps g)) : Option (D.Lift g) :=
  (D.searchRootCandidates R g candidates).map
    (fun hit => (D.rootSolutionsOfValidCandidate R g hit.1 hit.2).toLift D R)

/-- On a complete list, C1 failure excludes every original A1 lift. -/
theorem findRootLiftOnCandidates_none
    (candidates : List (D.CandidateMaps g))
    (hcovers : ∀ f : D.CandidateMaps g, f ∈ candidates)
    (h : D.findRootLiftOnCandidates R g candidates = none) :
    IsEmpty (D.Lift g) := by
  constructor
  intro a
  have hv : D.ValidRootCandidate R g
      (⟨fun x => a.fiber x, fun x => (a.fiber x).symm⟩) :=
    D.validRootCandidate_of_lift R g a
  have hsearch : D.searchRootCandidates R g candidates = none := by
    unfold findRootLiftOnCandidates at h
    cases hs : D.searchRootCandidates R g candidates with
    | none => rfl
    | some hit => simp [hs] at h
  exact (D.searchRootCandidates_none R g _ hsearch _ (hcovers _)) hv

/-- C1 search succeeds exactly when the original lift fiber is inhabited. -/
theorem findRootLiftOnCandidates_isSome_iff
    (candidates : List (D.CandidateMaps g))
    (hcovers : ∀ f : D.CandidateMaps g, f ∈ candidates) :
    (D.findRootLiftOnCandidates R g candidates).isSome = true ↔
      Nonempty (D.Lift g) := by
  constructor
  · intro h
    cases hs : D.findRootLiftOnCandidates R g candidates with
    | none => simp [hs] at h
    | some a => exact ⟨a⟩
  · rintro ⟨a⟩
    cases hs : D.findRootLiftOnCandidates R g candidates with
    | some b => rfl
    | none => exact (D.findRootLiftOnCandidates_none R g candidates hcovers hs).false a |>.elim

end Finite

section ExplicitTables

variable [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
  [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- The explicit finite input lists run the simultaneous C1 search and
return a C2 reconstruction on success. -/
def findRootLift
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    Option (D.Lift g) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ x : Q.Vertex, Fintype (D.Fiber x) :=
    fun x => (fibers x).toFintype
  exact D.findRootLiftOnCandidates R g
    (D.allCandidateMaps g vertices fibers).values

/-- Negative C1 search proves nonexistence of an original lift. -/
theorem findRootLift_none
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x))
    (h : D.findRootLift R g vertices edges fibers = none) :
    IsEmpty (D.Lift g) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ x : Q.Vertex, Fintype (D.Fiber x) :=
    fun x => (fibers x).toFintype
  exact D.findRootLiftOnCandidates_none R g
    (D.allCandidateMaps g vertices fibers).values
    (D.allCandidateMaps g vertices fibers).complete h

/-- Finite C1 decision matches the original lift fiber in both directions. -/
theorem findRootLift_isSome_iff
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    (D.findRootLift R g vertices edges fibers).isSome = true ↔
      Nonempty (D.Lift g) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ x : Q.Vertex, Fintype (D.Fiber x) :=
    fun x => (fibers x).toFintype
  exact D.findRootLiftOnCandidates_isSome_iff R g
    (D.allCandidateMaps g vertices fibers).values
    (D.allCandidateMaps g vertices fibers).complete

/-- The same decision is exactly the existence test for C1 root solutions. -/
theorem findRootLift_isSome_iff_rootSolutions
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    (D.findRootLift R g vertices edges fibers).isSome = true ↔
      Nonempty (D.RootSolutions R g) := by
  constructor
  · intro h
    obtain ⟨a⟩ := (D.findRootLift_isSome_iff R g vertices edges fibers).mp h
    exact ⟨a.toRootSolutions D R⟩
  · rintro ⟨b⟩
    exact (D.findRootLift_isSome_iff R g vertices edges fibers).mpr
      ⟨b.toLift D R⟩

end ExplicitTables
end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootSolutionsOfValidCandidate
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.validRootCandidate_of_lift
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.searchRootCandidates_none
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findRootLift
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findRootLift_none
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findRootLift_isSome_iff
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findRootLift_isSome_iff_rootSolutions

private def smokeQ : AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := PUnit
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private def smokeR : AAT.AG.ProtocolHolonomy.RootedPaths smokeQ where
  root := fun _ => PUnit.unit
  root_component := by
    intro j
    have h := Quotient.out_eq j
    have he : Quotient.out j = PUnit.unit := by
      cases Quotient.out j
      rfl
    simpa [he] using h
  path := by
    intro j x hx
    cases x
    exact AAT.AG.ProtocolHolonomy.signedNil smokeQ PUnit.unit
  path_root := by
    intro j
    rfl

private def smokeD : AAT.AG.ProtocolHolonomy.ReversibleData.{0, 0, 0} smokeQ where
  Fiber := fun _ => Bool
  edgeEquiv := Empty.elim

private def smokeVertices : AAT.AG.ProtocolHolonomy.ExplicitEnumeration smokeQ.Vertex where
  values := [PUnit.unit]
  complete := by intro x; cases x; simp

private def smokeEdges : AAT.AG.ProtocolHolonomy.ExplicitEnumeration smokeQ.Edge where
  values := []
  complete := by intro x; exact Empty.elim x

private def smokeFibers :
    ∀ x, AAT.AG.ProtocolHolonomy.ExplicitEnumeration (smokeD.Fiber x) :=
  fun _ => { values := [false, true], complete := by intro x; cases x <;> simp }

private instance : DecidableEq smokeQ.Vertex := by
  unfold smokeQ
  infer_instance

private instance : DecidableEq smokeQ.Edge := by
  unfold smokeQ
  infer_instance

private instance (x : smokeQ.Vertex) : DecidableEq (smokeD.Fiber x) := by
  unfold smokeD
  infer_instance

#eval (smokeD.findRootLift smokeR 1 smokeVertices smokeEdges smokeFibers).isSome
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
