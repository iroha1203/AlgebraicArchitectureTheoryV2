import ResearchLean.AG.ProtocolHolonomy.LiftRootReconstruction
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Pi
import Formal.Util.AssertStandardAxioms

/-!
# Direct finite-table decision for original A1 lifts

Explicit vertex and fiber enumerations generate every vertexwise forward and
inverse function table. A finite test checks both inverse laws and the
original A1 named-edge square. The search is executable. Constructing the
finite named forest and the B1/B2/C1-based procedure remain separate
obligations of GOAL E.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- A concrete enumeration supplied as a finite input table. -/
structure ExplicitEnumeration (α : Type u) where
  values : List α
  complete : ∀ a : α, a ∈ values

namespace ExplicitEnumeration

/-- Build finite quantification from the supplied list and equality decision. -/
def toFintype {α : Type u} [DecidableEq α]
    (E : ExplicitEnumeration α) : Fintype α :=
  ⟨E.values.toFinset, fun a => List.mem_toFinset.mpr (E.complete a)⟩

/-- Enumerate all dependent functions using concrete input lists. -/
def pi {ι : Type u} {α : ι → Type v} [DecidableEq ι]
    (indices : ExplicitEnumeration ι)
    (values : ∀ i, ExplicitEnumeration (α i)) :
    ExplicitEnumeration ((i : ι) → α i) where
  values := (List.pi indices.values (fun i => (values i).values)).map
    (fun f i => f i (indices.complete i))
  complete := by
    intro f
    apply List.mem_map.mpr
    refine ⟨(fun i _ => f i), ?_, ?_⟩
    · apply (List.mem_pi _ _).mpr
      intro i hi
      exact (values i).complete (f i)
    · funext i
      rfl

/-- Enumerate ordered pairs by a terminating list product. -/
def product {α : Type u} {β : Type v}
    (a : ExplicitEnumeration α) (b : ExplicitEnumeration β) :
    ExplicitEnumeration (α × β) where
  values := a.values.product b.values
  complete := by
    rintro ⟨x, y⟩
    exact List.mem_product.mpr ⟨a.complete x, b.complete y⟩

end ExplicitEnumeration

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)
  (g : FixedFGraphAutomorphism Q)

/-- Forward and inverse function tables on every original vertex fiber. -/
abbrev CandidateMaps : Type _ :=
  ((x : Q.Vertex) → D.Fiber x → D.Fiber (g.vertex x)) ×
    ((x : Q.Vertex) → D.Fiber (g.vertex x) → D.Fiber x)

/-- Exactly the bijective original A1 edge-square conditions. -/
def ValidCandidate (f : D.CandidateMaps g) : Prop :=
  (∀ (x : Q.Vertex) (y : D.Fiber x), f.2 x (f.1 x y) = y) ∧
  (∀ (x : Q.Vertex) (y : D.Fiber (g.vertex x)), f.1 x (f.2 x y) = y) ∧
  (∀ (e : Q.Edge) (x : D.Fiber (Q.source e)),
    f.1 (Q.target e) (D.edgeEquiv e x) =
      D.renamedEdgeEquiv g e (f.1 (Q.source e) x))

/-- An accepted table is a genuine lift of the original reversible data. -/
def liftOfValidCandidate (f : D.CandidateMaps g)
    (hf : D.ValidCandidate g f) : D.Lift g where
  fiber x :=
    { toFun := f.1 x
      invFun := f.2 x
      left_inv := hf.1 x
      right_inv := hf.2.1 x }
  edge_naturality := hf.2.2

/-- Every original A1 lift supplies a valid forward table. -/
theorem validCandidate_of_lift (a : D.Lift g) :
    D.ValidCandidate g
      (⟨fun x => a.fiber x, fun x => (a.fiber x).symm⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact (a.fiber x).symm_apply_apply y
  · intro x y
    exact (a.fiber x).apply_symm_apply y
  · exact a.edge_naturality

section Finite

variable [Fintype Q.Vertex] [Fintype Q.Edge]
  [∀ x : Q.Vertex, Fintype (D.Fiber x)]
  [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- The input finite tables induce a decidable A1 validity test. -/
instance validCandidateDecidable (f : D.CandidateMaps g) :
    Decidable (D.ValidCandidate g f) := by
  unfold ValidCandidate
  infer_instance

/-- Exhaustive recursion through supplied finite candidate tables. -/
def searchCandidates :
    List (D.CandidateMaps g) →
      Option {f : D.CandidateMaps g // D.ValidCandidate g f}
  | [] => none
  | f :: fs =>
      if hf : D.ValidCandidate g f then some ⟨f, hf⟩
      else searchCandidates fs

/-- Absence of a hit excludes every table in the searched list. -/
theorem searchCandidates_none (l : List (D.CandidateMaps g))
    (h : D.searchCandidates g l = none) :
    ∀ f ∈ l, ¬ D.ValidCandidate g f := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : D.ValidCandidate g a
      · simp [searchCandidates, ha] at h
      · have htail : D.searchCandidates g l = none := by
          simpa [searchCandidates, ha] using h
        intro f hf hv
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hmem
        · exact ha hv
        · exact ih htail f hmem hv

/-- Search an explicit list and return only genuine original lifts. -/
def findDirectLiftOnCandidates (candidates : List (D.CandidateMaps g)) :
    Option (D.Lift g) :=
  (D.searchCandidates g candidates).map
    (fun hit => D.liftOfValidCandidate g hit.1 hit.2)

/-- When the list covers every forward/inverse table, a negative result
excludes every independently defined original A1 lift. -/
theorem findDirectLiftOnCandidates_none
    (candidates : List (D.CandidateMaps g))
    (hcovers : ∀ f : D.CandidateMaps g, f ∈ candidates)
    (h : D.findDirectLiftOnCandidates g candidates = none) : IsEmpty (D.Lift g) := by
  constructor
  intro a
  have hv : D.ValidCandidate g
      (⟨fun x => a.fiber x, fun x => (a.fiber x).symm⟩) :=
    D.validCandidate_of_lift g a
  have hsearch : D.searchCandidates g candidates = none := by
    unfold findDirectLiftOnCandidates at h
    cases hs : D.searchCandidates g candidates with
    | none => rfl
    | some hit => simp [hs] at h
  have hmem : (⟨fun x => a.fiber x, fun x => (a.fiber x).symm⟩ :
      D.CandidateMaps g) ∈ candidates := hcovers _
  exact (D.searchCandidates_none g _ hsearch _ hmem) hv

/-- For a complete explicit candidate list, search succeeds exactly when
the independently defined A1 lift fiber is inhabited. -/
theorem findDirectLiftOnCandidates_isSome_iff
    (candidates : List (D.CandidateMaps g))
    (hcovers : ∀ f : D.CandidateMaps g, f ∈ candidates) :
    (D.findDirectLiftOnCandidates g candidates).isSome = true ↔
      Nonempty (D.Lift g) := by
  constructor
  · intro h
    cases hs : D.findDirectLiftOnCandidates g candidates with
    | none => simp [hs] at h
    | some a => exact ⟨a⟩
  · rintro ⟨a⟩
    cases hs : D.findDirectLiftOnCandidates g candidates with
    | some b => rfl
    | none => exact (D.findDirectLiftOnCandidates_none g candidates hcovers hs).false a |>.elim

end Finite

section ExplicitTables

variable [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
  [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- All forward/inverse vertex tables obtained from exactly the supplied
vertex and fiber enumerations. -/
def allCandidateMaps
    (vertices : ExplicitEnumeration Q.Vertex)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    ExplicitEnumeration (D.CandidateMaps g) :=
  (ExplicitEnumeration.pi vertices
    (fun x => ExplicitEnumeration.pi (fibers x)
      (fun _ => fibers (g.vertex x)))).product
    (ExplicitEnumeration.pi vertices
      (fun x => ExplicitEnumeration.pi (fibers (g.vertex x))
        (fun _ => fibers x)))

/-- The input tables themselves produce the full candidate list and a
terminating original A1 lift search. -/
def findDirectLift
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    Option (D.Lift g) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ x : Q.Vertex, Fintype (D.Fiber x) :=
    fun x => (fibers x).toFintype
  exact D.findDirectLiftOnCandidates g (D.allCandidateMaps g vertices fibers).values

/-- A negative executable answer excludes every independently defined
original A1 lift. -/
theorem findDirectLift_none
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x))
    (h : D.findDirectLift g vertices edges fibers = none) :
    IsEmpty (D.Lift g) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ x : Q.Vertex, Fintype (D.Fiber x) :=
    fun x => (fibers x).toFintype
  exact D.findDirectLiftOnCandidates_none g
    (D.allCandidateMaps g vertices fibers).values
    (D.allCandidateMaps g vertices fibers).complete h

/-- The finite procedure succeeds exactly for the original A1 lift fiber. -/
theorem findDirectLift_isSome_iff
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    (D.findDirectLift g vertices edges fibers).isSome = true ↔
      Nonempty (D.Lift g) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ x : Q.Vertex, Fintype (D.Fiber x) :=
    fun x => (fibers x).toFintype
  exact D.findDirectLiftOnCandidates_isSome_iff g
    (D.allCandidateMaps g vertices fibers).values
    (D.allCandidateMaps g vertices fibers).complete

end ExplicitTables
end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftOfValidCandidate
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.validCandidate_of_lift
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.searchCandidates_none
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findDirectLiftOnCandidates_none
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findDirectLiftOnCandidates_isSome_iff
#print axioms AAT.AG.ProtocolHolonomy.ExplicitEnumeration.pi
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.allCandidateMaps
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findDirectLift
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findDirectLift_none
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findDirectLift_isSome_iff
private def testQ : AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := PUnit
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private def testD : AAT.AG.ProtocolHolonomy.ReversibleData.{0, 0, 0} testQ where
  Fiber := fun _ => Bool
  edgeEquiv := Empty.elim

private def testVertices : AAT.AG.ProtocolHolonomy.ExplicitEnumeration testQ.Vertex where
  values := [PUnit.unit]
  complete := by intro x; cases x; simp

private def testEdges : AAT.AG.ProtocolHolonomy.ExplicitEnumeration testQ.Edge where
  values := []
  complete := by intro x; exact Empty.elim x

private def testFibers : ∀ x, AAT.AG.ProtocolHolonomy.ExplicitEnumeration (testD.Fiber x) :=
  fun _ => { values := [false, true], complete := by intro x; cases x <;> simp }

private instance : DecidableEq testQ.Vertex := by
  unfold testQ
  infer_instance

private instance : DecidableEq testQ.Edge := by
  unfold testQ
  infer_instance

private instance (x : testQ.Vertex) : DecidableEq (testD.Fiber x) := by
  unfold testD
  infer_instance

#eval (testD.findDirectLift 1 testVertices testEdges testFibers).isSome
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
