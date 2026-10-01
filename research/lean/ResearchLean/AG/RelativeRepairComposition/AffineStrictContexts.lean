import ResearchLean.AG.RelativeRepairComposition.AffineContextGenerated

/-!
# Literal original affine operation agreement in every external context

Strict gluing data consist of independent complete repairs on both original
inputs whose actual operations on every named shared edge are equal. Their
face laws, full three-cell input, fixed cells and whole allowed ranges are the
original ones. Correction equality is derived from these actual operations.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {W : FiniteTransportPresentation.{uG}}
variable {LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k A}
variable {cW : W.TwoCell → A} {PW : ClosedRegion W} {CW : Set (EdgeName (K := W))}
variable (I E : AffineContextInput W LW RW cW PW CW)
variable {S : Set (EdgeName (K := W))} (a : I.Range S) (b : E.Range S)

/-- Independent complete actual repairs with literal equality of each original shared real edge. -/
def StrictRepairs :=
  {p : I.Repairs a × E.Repairs b // ∀ {i j : W.Vertex} (e : W.Edge i j),
    p.1.operation (I.embedding.edge e) = p.2.operation (E.embedding.edge e)}

/-- Equal complete correction vectors are equivalent to literal shared original operation equality. -/
theorem boundary_eq_iff (s : I.Repairs a) (t : E.Repairs b) :
    I.boundary a s = E.boundary b t ↔
      ∀ {i j : W.Vertex} (e : W.Edge i j),
        s.operation (I.embedding.edge e) = t.operation (E.embedding.edge e) := by
  constructor
  · intro h i j e
    have hi := real_correction_restore W RW cW (fixedEdgesForRange PW.edges CW S)
      (I.sharedRepair a s) e
    have he := real_correction_restore W RW cW (fixedEdgesForRange PW.edges CW S)
      (E.sharedRepair b t) e
    have hv := congrFun h (⟨i,j,e⟩ : EdgeName (K := W))
    change s.operation (I.embedding.edge e) =
      translation (k := k) (I.boundary a s ⟨i,j,e⟩) * RW e at hi
    change t.operation (E.embedding.edge e) =
      translation (k := k) (E.boundary b t ⟨i,j,e⟩) * RW e at he
    exact hi.trans ((congrArg (fun v => translation (k := k) v * RW e) hv).trans he.symm)
  · intro h
    funext ⟨i,j,e⟩
    change ((s.operation (I.embedding.edge e)) * (RW e)⁻¹) 0 =
      ((t.operation (E.embedding.edge e)) * (RW e)⁻¹) 0
    rw [h e]

/-- Full actual strict-gluing objects and full correction pairs have inverse object maps. -/
def strictRepairEquiv : StrictRepairs I E a b ≃
    ContextRelations.StrictJoin (I.boundary a) (E.boundary b) where
  toFun p := ⟨p.1,(I.boundary_eq_iff E a b p.1.1 p.1.2).mpr p.2⟩
  invFun p := ⟨p.1,(I.boundary_eq_iff E a b p.1.1 p.1.2).mp p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual strict gluing exists precisely when the two full independently realized ranges intersect. -/
theorem strict_repairs_nonempty : Nonempty (StrictRepairs I E a b) ↔
    (Set.range (I.boundary a) ∩ Set.range (E.boundary b)).Nonempty :=
  (I.strictRepairEquiv E a b).nonempty_congr.trans
    (ContextRelations.strict_join_nonempty (I.boundary a) (E.boundary b))

/-- Every whole actual external context has the same literal strict-gluing existence outcome
exactly when the full actual boundary relations agree. -/
theorem contextual_strict_actual (J : AffineContextInput W LW RW cW PW CW) (c : J.Range S) :
    (∀ env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S,
      Nonempty (StrictRepairs I env.1 a env.2) ↔ Nonempty (StrictRepairs J env.1 c env.2)) ↔
        Set.range (I.boundary a) = Set.range (J.boundary c) := by
  simpa only [strict_repairs_nonempty,ContextRelations.strict_join_nonempty] using
    I.contextual_actual_ranges J a c

end AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
