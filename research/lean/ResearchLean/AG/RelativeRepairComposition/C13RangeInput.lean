import ResearchLean.AG.RelativeRepairComposition.OriginalFiniteRepair
import ResearchLean.AG.AbelianLiftingObstruction.GroupExtension
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.TransferInstance

/-! # A nonzero original F2 face with a fixed edge and a full candidate kernel -/
namespace AAT.AG.RelativeRepairComposition.C13RangeInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction

/-- One vertex, two original named loops, one authored equality face, and no triples. -/
def geometry : FiniteTransportPresentation where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Bool
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Unit
  twoCellFintype := inferInstance
  twoSource := fun _ => ()
  twoTarget := fun _ => ()
  twoLeft := fun _ => .cons false (.nil ())
  twoRight := fun _ => .cons true (.nil ())
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun f => nomatch f
  threeTarget := fun f => nomatch f
  threeStart := fun f => nomatch f
  threeFinish := fun f => nomatch f
  threeLeft := fun f => nomatch f
  threeRight := fun f => nomatch f

/-- Equality on original loop names is the concrete Bool equality. -/
instance edgeEquality {i j : geometry.Vertex} : DecidableEq (geometry.Edge i j) :=
  inferInstanceAs (DecidableEq Bool)

/-- Original group elements are the two translations of F₂. -/
abbrev E := Multiplicative (ZMod 2)
/-- The projection forgets translation while retaining the original arrows. -/
def projection : E →* PUnit.{1} := 1
/-- The full actual kernel is abelian since all original translations commute. -/
theorem kernel_comm (a b : projection.ker) : a * b = b * a := mul_comm a b
/-- The fixed original core is the unique lower arrow. -/
def core : ∀ {i j : geometry.Vertex}, geometry.Edge i j → PUnit.{1} := fun _ => 1
/-- The false reference loop translates by one; the true reference loop translates by zero. -/
def reference : ∀ {i j : geometry.Vertex}, geometry.Edge i j → E :=
  fun e => if (e : Bool) = true then 1 else Multiplicative.ofAdd 1
/-- Both original lifts project to the same fixed core. -/
theorem projects {i j : geometry.Vertex} (e : geometry.Edge i j) :
    projection (reference e) = core e := rfl
/-- The fixed lower core satisfies the original single face. -/
theorem relations (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry core (geometry.twoLeft f) =
      GroupExtension.pathValue geometry core (geometry.twoRight f) := Subsingleton.elim _ _
/-- Strongness, transport and full kernel conditions are generated from actual inputs. -/
noncomputable abbrev tower :=
  GroupExtension.input geometry projection kernel_comm core reference projects relations

/-- The original whole projection kernel is the entire group of two translations. -/
def fullKernel : projection.ker ≃* E where
  toFun a := a.1
  invFun e := ⟨e,rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The same full actual native kernel is the additive F2 coefficient space. -/
noncomputable def coefficient (v : geometry.Vertex) : tower.toTower.localCoefficients.A v ≃+ ZMod 2 :=
  ((GroupExtension.kernelEquiv projection).symm.trans fullKernel).toAdditive

/-- Scalar multiplication is transferred on the entire original native kernel. -/
noncomputable instance originalModule (v : geometry.Vertex) :
    Module (ZMod 2) (tower.toTower.localCoefficients.A v) := (coefficient v).module (ZMod 2)

/-- Every original transport is identity because all the original translations commute. -/
theorem edge_identity {i j : geometry.Vertex} (e : geometry.Edge i j)
    (x : tower.toTower.localCoefficients.A i) : tower.toTower.localCoefficients.edge e x = x := by
  obtain ⟨a,ha⟩ := (GroupExtension.kernelEquiv projection).surjective (Additive.toMul x)
  have hx : x = Additive.ofMul (GroupExtension.kernelEquiv projection a) :=
    congrArg Additive.ofMul ha.symm
  rw [hx]
  have hc : GroupExtension.conjugation projection (reference e) a = a := by
    apply Subtype.ext
    change reference e * a.1 * (reference e)⁻¹ = a.1
    rw [mul_comm (reference e) a.1,mul_assoc,mul_inv_cancel,mul_one]
  have ht := GroupExtension.transport_kernelEquiv projection (reference e) a
  rw [hc] at ht
  change Additive.ofMul (kernelTransportHom (GroupExtension.projection projection)
    (GroupExtension.terminal PUnit.{1}) (tower.toTower.upper.edgeLift e)
    (tower.toTower.upper.edgeStrong e) (tower.toTower.lowerStrong e)
    (GroupExtension.kernelEquiv projection a)) = _
  simpa only [GroupExtension.input_edge_value] using congrArg Additive.ofMul ht

/-- Original full transports are linear on the full native kernels. -/
theorem linear {i j : geometry.Vertex} (e : geometry.Edge i j) (t : ZMod 2)
    (x : tower.toTower.localCoefficients.A i) :
    tower.toTower.localCoefficients.edge e (t • x) = t • tower.toTower.localCoefficients.edge e x := by
  rw [edge_identity,edge_identity]

/-- The physical fixed part includes the original false loop and both of its endpoints. -/
def fixed : ClosedRegion geometry where
  vertices := Set.univ
  edges := {e | e.2.2 = false}
  faces := ∅
  triples := ∅
  edge_closed _ _ := ⟨trivial,trivial⟩
  face_closed _ h := False.elim h
  triple_closed t _ := Empty.elim t

/-- The true loop is the one original candidate. -/
def candidates : Set (EdgeName (K := geometry)) := {e | e.2.2 = true}

/-- No original candidate is physically fixed. -/
theorem outside (e : EdgeName (K := geometry)) (he : e ∈ candidates) : e ∉ fixed.edges := by
  intro hf
  have h : true = false := he.symm.trans hf
  exact Bool.noConfusion h

/-- No physically fixed face condition is added to the actual input. -/
theorem fixed_coherent (f : geometry.TwoCell) (hf : f ∈ fixed.faces) :
    tower.toTower.upper.pathLift (geometry.twoLeft f) ≫ FiberAut.hom (tower.comparator f) =
      tower.toTower.upper.pathLift (geometry.twoRight f) := False.elim hf

end AAT.AG.RelativeRepairComposition.C13RangeInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C13RangeInput
