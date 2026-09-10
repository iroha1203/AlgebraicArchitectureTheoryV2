import ResearchLean.AG.ComparisonInformationLoss.ObservationKernel

/-!
# Transport of observation kernels and pointed cosets

This file proves G-120(A2).  An isomorphism of observation diagrams transports
the kernel, its compatible part, observation fibers, and the pointed left-coset
set.  The constructions are compatible with identity and composition.

Implementation notes: the hypotheses are packaged in `ObservationEquiv` so
that identity and composition are mathematical operations on the same data.
The structure contains only the two group equivalences and the two commuting
conditions required by G-120(A); it carries none of the conclusions.  Fibers
are represented as subtypes of their defining predicates, while the quotient
transport is built directly from mathlib's general left-coset quotient rather
than imposing a normality condition.
-/

namespace AAT.AG.ComparisonInformationLoss

universe uQ uR uQ' uR' uQ'' uR''

variable {Q : Type uQ} {R : Type uR} [Group Q] [Group R]
variable {Q' : Type uQ'} {R' : Type uR'} [Group Q'] [Group R']
variable {Q'' : Type uQ''} {R'' : Type uR''} [Group Q''] [Group R'']

/-- G-120(A)'s input isomorphism between two observation diagrams.  The first
field transports changes, the second transports observations, and the two
proof fields are exactly `O' φ = ψ O` and `φ(Gamma) = Gamma'` from the fixed
target. -/
structure ObservationEquiv (O : Q →* R) (Gamma : Subgroup Q)
    (O' : Q' →* R') (Gamma' : Subgroup Q') where
  changeEquiv : Q ≃* Q'
  observationEquiv : R ≃* R'
  observation_comm : ∀ q : Q, O' (changeEquiv q) = observationEquiv (O q)
  compatible_map : Subgroup.map changeEquiv.toMonoidHom Gamma = Gamma'

namespace ObservationEquiv

variable {O : Q →* R} {Gamma : Subgroup Q}
variable {O' : Q' →* R'} {Gamma' : Subgroup Q'}
variable {O'' : Q'' →* R''} {Gamma'' : Subgroup Q''}

/-- Identity observation-diagram equivalence.  This is the identity input for
the coherence part of G-120(A2). -/
def refl (O : Q →* R) (Gamma : Subgroup Q) : ObservationEquiv O Gamma O Gamma where
  changeEquiv := MulEquiv.refl Q
  observationEquiv := MulEquiv.refl R
  observation_comm := fun _ => rfl
  compatible_map := Subgroup.map_id Gamma

/-- Composition of observation-diagram equivalences.  Its commuting laws are
obtained by using the two input squares in sequence, so no transport conclusion
is stored as additional data. -/
def trans (e : ObservationEquiv O Gamma O' Gamma')
    (f : ObservationEquiv O' Gamma' O'' Gamma'') :
    ObservationEquiv O Gamma O'' Gamma'' where
  changeEquiv := e.changeEquiv.trans f.changeEquiv
  observationEquiv := e.observationEquiv.trans f.observationEquiv
  observation_comm := fun q => by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, f.observation_comm, e.observation_comm]
  compatible_map := by
    change Subgroup.map
      (f.changeEquiv.toMonoidHom.comp e.changeEquiv.toMonoidHom) Gamma = Gamma''
    rw [← Subgroup.map_map, e.compatible_map, f.compatible_map]

/-- Membership is transported and reflected by the change equivalence.  This
is the subgroup-membership API used by the compatible-kernel and compatible-
fiber constructions in G-120(A2). -/
theorem mem_compatible_iff (e : ObservationEquiv O Gamma O' Gamma') (q : Q) :
    e.changeEquiv q ∈ Gamma' ↔ q ∈ Gamma := by
  let phi := e.changeEquiv
  have hmap : Subgroup.map phi.toMonoidHom Gamma = Gamma' := e.compatible_map
  change phi q ∈ Gamma' ↔ q ∈ Gamma
  rw [← hmap]
  constructor
  · rintro ⟨q', hq', hqq'⟩
    simpa using (show q' = q from e.changeEquiv.injective hqq') ▸ hq'
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- The group equivalence between observation kernels induced by G-120(A)'s
commuting square.  Kernel membership is derived from `observation_comm`; it is
not supplied as a separate certificate. -/
def kernelEquiv (e : ObservationEquiv O Gamma O' Gamma') : O.ker ≃* O'.ker where
  toFun k := ⟨e.changeEquiv (k : Q), by
    rw [MonoidHom.mem_ker, e.observation_comm, MonoidHom.mem_ker.mp k.property, map_one]⟩
  invFun k' := ⟨e.changeEquiv.symm k', by
    rw [MonoidHom.mem_ker]
    apply e.observationEquiv.injective
    rw [← e.observation_comm, e.changeEquiv.apply_symm_apply,
      MonoidHom.mem_ker.mp k'.property, map_one]⟩
  left_inv k := Subtype.ext (e.changeEquiv.symm_apply_apply k)
  right_inv k := Subtype.ext (e.changeEquiv.apply_symm_apply k)
  map_mul' a b := Subtype.ext (map_mul e.changeEquiv (a : Q) (b : Q))

/-- Evaluation rule for the kernel transport on underlying change elements. -/
@[simp]
theorem kernelEquiv_coe (e : ObservationEquiv O Gamma O' Gamma') (k : O.ker) :
    (e.kernelEquiv k : Q') = e.changeEquiv (k : Q) :=
  rfl

/-- The compatible part of the kernel is transported by the induced kernel
equivalence.  Membership follows from `compatible_map`, not from a stored
compatibility conclusion. -/
def compatibleKernelEquiv (e : ObservationEquiv O Gamma O' Gamma') :
    compatibleKernel O Gamma ≃* compatibleKernel O' Gamma' where
  toFun k := ⟨e.kernelEquiv (k : O.ker),
    (e.mem_compatible_iff (k : Q)).mpr k.property⟩
  invFun k' := ⟨e.kernelEquiv.symm k', by
    apply (e.mem_compatible_iff (e.changeEquiv.symm (k' : Q'))).mp
    have hk' : (k' : O'.ker) ∈ compatibleKernel O' Gamma' := k'.property
    have hkGamma : (k' : Q') ∈ Gamma' :=
      (mem_compatibleKernel_iff O' Gamma' _).mp hk'
    simpa only [e.changeEquiv.apply_symm_apply] using hkGamma⟩
  left_inv k := Subtype.ext (e.kernelEquiv.symm_apply_apply k)
  right_inv k := Subtype.ext (e.kernelEquiv.apply_symm_apply k)
  map_mul' a b := Subtype.ext
    (map_mul e.kernelEquiv (a : O.ker) (b : O.ker))

/-- Evaluation rule for the compatible-kernel transport. -/
@[simp]
theorem compatibleKernelEquiv_coe (e : ObservationEquiv O Gamma O' Gamma')
    (k : compatibleKernel O Gamma) :
    ((e.compatibleKernelEquiv k : compatibleKernel O' Gamma') : O'.ker) =
      e.kernelEquiv k :=
  rfl

/-- Transport of the observation fiber over `gamma`.  The inverse direction
uses injectivity of the observation equivalence to reflect the commuting
square. -/
def fiberEquiv (e : ObservationEquiv O Gamma O' Gamma') (gamma : Q) :
    {q : Q // O q = O gamma} ≃
      {q' : Q' // O' q' = O' (e.changeEquiv gamma)} where
  toFun q := ⟨e.changeEquiv q, by
    rw [e.observation_comm, e.observation_comm, q.property]⟩
  invFun q' := ⟨e.changeEquiv.symm q', by
    apply e.observationEquiv.injective
    calc
      e.observationEquiv (O (e.changeEquiv.symm q')) =
          O' (e.changeEquiv (e.changeEquiv.symm q')) :=
        (e.observation_comm _).symm
      _ = O' q' := by rw [e.changeEquiv.apply_symm_apply]
      _ = O' (e.changeEquiv gamma) := q'.property
      _ = e.observationEquiv (O gamma) := e.observation_comm gamma⟩
  left_inv q := Subtype.ext (e.changeEquiv.symm_apply_apply q)
  right_inv q := Subtype.ext (e.changeEquiv.apply_symm_apply q)

/-- Evaluation rule for the observation-fiber transport. -/
@[simp]
theorem fiberEquiv_coe (e : ObservationEquiv O Gamma O' Gamma') (gamma : Q)
    (q : {q : Q // O q = O gamma}) :
    (e.fiberEquiv gamma q : Q') = e.changeEquiv q :=
  rfl

/-- Transport of the compatible part of an observation fiber.  Both the fiber
equation and compatible membership are reconstructed from the two commuting
conditions in `ObservationEquiv`. -/
def compatibleFiberEquiv (e : ObservationEquiv O Gamma O' Gamma') (gamma : Q) :
    {q : Q // O q = O gamma ∧ q ∈ Gamma} ≃
      {q' : Q' // O' q' = O' (e.changeEquiv gamma) ∧ q' ∈ Gamma'} where
  toFun q := ⟨e.changeEquiv q, by
    exact ⟨by rw [e.observation_comm, e.observation_comm, q.property.1],
      (e.mem_compatible_iff q).mpr q.property.2⟩⟩
  invFun q' := ⟨e.changeEquiv.symm q', by
    constructor
    · apply e.observationEquiv.injective
      calc
        e.observationEquiv (O (e.changeEquiv.symm q')) =
            O' (e.changeEquiv (e.changeEquiv.symm q')) :=
          (e.observation_comm _).symm
        _ = O' q' := by rw [e.changeEquiv.apply_symm_apply]
        _ = O' (e.changeEquiv gamma) := q'.property.1
        _ = e.observationEquiv (O gamma) := e.observation_comm gamma
    · apply (e.mem_compatible_iff (e.changeEquiv.symm q')).mp
      simpa using q'.property.2⟩
  left_inv q := Subtype.ext (e.changeEquiv.symm_apply_apply q)
  right_inv q := Subtype.ext (e.changeEquiv.apply_symm_apply q)

/-- Evaluation rule for compatible-fiber transport. -/
@[simp]
theorem compatibleFiberEquiv_coe (e : ObservationEquiv O Gamma O' Gamma') (gamma : Q)
    (q : {q : Q // O q = O gamma ∧ q ∈ Gamma}) :
    (e.compatibleFiberEquiv gamma q : Q') = e.changeEquiv q :=
  rfl

/-- G-120(A)'s pointed left-coset equivalence.  A representative `kL` is sent
to `φ(k)L'`; well-definedness uses the transported compatible-kernel
membership, with no normality assumption. -/
def quotientEquiv (e : ObservationEquiv O Gamma O' Gamma') :
    O.ker ⧸ compatibleKernel O Gamma ≃ O'.ker ⧸ compatibleKernel O' Gamma' where
  toFun := Quotient.map' e.kernelEquiv fun a b hab => by
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    apply (mem_compatibleKernel_iff O' Gamma' _).mpr
    apply (e.mem_compatible_iff ((((a : O.ker)⁻¹ * b : O.ker) : Q))).mpr
    exact (mem_compatibleKernel_iff O Gamma _).mp
      (QuotientGroup.leftRel_apply.mp hab)
  invFun := Quotient.map' e.kernelEquiv.symm fun a b hab => by
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    apply (mem_compatibleKernel_iff O Gamma _).mpr
    apply (e.mem_compatible_iff
      (e.changeEquiv.symm ((((a : O'.ker)⁻¹ * b : O'.ker) : Q')))).mp
    simpa using (mem_compatibleKernel_iff O' Gamma' _).mp
      (QuotientGroup.leftRel_apply.mp hab)
  left_inv x := QuotientGroup.induction_on x fun k => by
    simp only [Quotient.map'_mk'']
    exact congrArg QuotientGroup.mk (e.kernelEquiv.symm_apply_apply k)
  right_inv x := QuotientGroup.induction_on x fun k => by
    simp only [Quotient.map'_mk'']
    exact congrArg QuotientGroup.mk (e.kernelEquiv.apply_symm_apply k)

/-- Representative evaluation for the pointed quotient transport. -/
@[simp]
theorem quotientEquiv_mk (e : ObservationEquiv O Gamma O' Gamma') (k : O.ker) :
    e.quotientEquiv (QuotientGroup.mk k) = QuotientGroup.mk (e.kernelEquiv k) :=
  rfl

/-- The pointed quotient transport preserves the distinguished basepoint. -/
@[simp]
theorem quotientEquiv_basepoint (e : ObservationEquiv O Gamma O' Gamma') :
    e.quotientEquiv (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
  rw [quotientEquiv_mk, map_one]

/-- Kernel transport for the identity observation diagram is the identity. -/
theorem kernelEquiv_refl (O : Q →* R) (Gamma : Subgroup Q) :
    (refl O Gamma).kernelEquiv = MulEquiv.refl O.ker := by
  ext k
  rfl

/-- Kernel transport respects composition of observation-diagram
equivalences. -/
theorem kernelEquiv_trans (e : ObservationEquiv O Gamma O' Gamma')
    (f : ObservationEquiv O' Gamma' O'' Gamma'') :
    (e.trans f).kernelEquiv = e.kernelEquiv.trans f.kernelEquiv := by
  ext k
  rfl

/-- Compatible-kernel transport for the identity diagram is the identity
group equivalence. -/
theorem compatibleKernelEquiv_refl (O : Q →* R) (Gamma : Subgroup Q) :
    (refl O Gamma).compatibleKernelEquiv = MulEquiv.refl (compatibleKernel O Gamma) := by
  ext k
  rfl

/-- Compatible-kernel transport respects composition. -/
theorem compatibleKernelEquiv_trans (e : ObservationEquiv O Gamma O' Gamma')
    (f : ObservationEquiv O' Gamma' O'' Gamma'') :
    (e.trans f).compatibleKernelEquiv =
      e.compatibleKernelEquiv.trans f.compatibleKernelEquiv := by
  ext k
  rfl

/-- Fiber transport for the identity diagram is the identity equivalence. -/
theorem fiberEquiv_refl (O : Q →* R) (Gamma : Subgroup Q) (gamma : Q) :
    (refl O Gamma).fiberEquiv gamma = Equiv.refl _ := by
  ext q
  rfl

/-- Fiber transport respects composition. -/
theorem fiberEquiv_trans (e : ObservationEquiv O Gamma O' Gamma')
    (f : ObservationEquiv O' Gamma' O'' Gamma'') (gamma : Q) :
    (e.trans f).fiberEquiv gamma =
      (e.fiberEquiv gamma).trans (f.fiberEquiv (e.changeEquiv gamma)) := by
  ext q
  rfl

/-- Compatible-fiber transport for the identity diagram is the identity. -/
theorem compatibleFiberEquiv_refl (O : Q →* R) (Gamma : Subgroup Q) (gamma : Q) :
    (refl O Gamma).compatibleFiberEquiv gamma = Equiv.refl _ := by
  ext q
  rfl

/-- Compatible-fiber transport respects composition. -/
theorem compatibleFiberEquiv_trans (e : ObservationEquiv O Gamma O' Gamma')
    (f : ObservationEquiv O' Gamma' O'' Gamma'') (gamma : Q) :
    (e.trans f).compatibleFiberEquiv gamma =
      (e.compatibleFiberEquiv gamma).trans
        (f.compatibleFiberEquiv (e.changeEquiv gamma)) := by
  ext q
  rfl

/-- Pointed left-coset transport for the identity diagram is the identity
equivalence. -/
theorem quotientEquiv_refl (O : Q →* R) (Gamma : Subgroup Q) :
    (refl O Gamma).quotientEquiv = Equiv.refl _ := by
  ext x
  refine QuotientGroup.induction_on x (fun k => ?_)
  rfl

/-- Pointed left-coset transport respects composition of observation diagrams. -/
theorem quotientEquiv_trans (e : ObservationEquiv O Gamma O' Gamma')
    (f : ObservationEquiv O' Gamma' O'' Gamma'') :
    (e.trans f).quotientEquiv = e.quotientEquiv.trans f.quotientEquiv := by
  ext x
  refine QuotientGroup.induction_on x (fun k => ?_)
  rfl

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss.ObservationEquiv

end ObservationEquiv

end AAT.AG.ComparisonInformationLoss
