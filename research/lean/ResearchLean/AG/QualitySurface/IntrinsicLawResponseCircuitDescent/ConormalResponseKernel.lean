import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ConormalJacobian

/-!
# Full conormal-response kernel

This file proves that preservation of a law ideal is exactly the kernel of the
full conormal response.  The preservation condition is derived from vanishing
on every class in `I / I²`; it is not supplied as part of the operation data.

The generic result is then instantiated on the J1b chart and overlap ambient
derivations and the J2 quotient-valued derivations.
-/

namespace ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent

universe uk uA uOp uChart uState uBefore uAfter

namespace QuotientValuedDerivation

variable {k : Type uk} {A : Type uA}
variable [Field k] [CommRing A] [Algebra k A]

/-- An ambient derivation preserves an ideal exactly when its full conormal
response after coefficient quotient vanishes. -/
theorem mapsTo_iff_conormalResponse_quotientDerivation_eq_zero
    (I : Ideal A) (d : Derivation k A A) :
    Set.MapsTo d I I ↔
      conormalResponse I (quotientDerivation I d) = 0 := by
  constructor
  · intro h
    ext c
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective c
    rw [conormalResponse_toCotangent, quotientDerivation_apply,
      LinearMap.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h x.property)
  · intro h x hx
    have hzero := DFunLike.congr_fun h (I.toCotangent ⟨x, hx⟩)
    rw [conormalResponse_toCotangent, quotientDerivation_apply,
      LinearMap.zero_apply] at hzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

end QuotientValuedDerivation

namespace ArchitectureOperationPresentation

variable {k : Type uk} {A : Type uA} {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [CommRing A] [Algebra k A]
variable [Fintype Op] [Fintype Chart]

/-- On a selected chart, ideal preservation is exactly the kernel of the full
chart conormal Jacobian. -/
theorem chartDerivation_mapsTo_iff_conormalJacobian_eq_zero
    (P : ArchitectureOperationPresentation k A Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A)
    (op : Op) (i : Chart) :
    Set.MapsTo (P.chartDerivation G op i) (G.chartLawIdeal I i)
        (G.chartLawIdeal I i) ↔
      G.chartConormalJacobian I i (P.chartQuotientDerivation G I op i) = 0 := by
  simpa [TypedLocalizationGeometry.chartConormalJacobian,
    chartQuotientDerivation] using
    (QuotientValuedDerivation.mapsTo_iff_conormalResponse_quotientDerivation_eq_zero
      (k := k) (G.chartLawIdeal I i) (P.chartDerivation G op i))

/-- On a selected overlap, ideal preservation is exactly the kernel of the
full overlap conormal Jacobian. -/
theorem overlapDerivation_mapsTo_iff_conormalJacobian_eq_zero
    (P : ArchitectureOperationPresentation k A Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A)
    (op : Op) (i j : Chart) :
    Set.MapsTo (P.overlapDerivation G op i j) (G.overlapLawIdeal I i j)
        (G.overlapLawIdeal I i j) ↔
      G.overlapConormalJacobian I i j
        (P.overlapQuotientDerivation G I op i j) = 0 := by
  simpa [TypedLocalizationGeometry.overlapConormalJacobian,
    overlapQuotientDerivation] using
    (QuotientValuedDerivation.mapsTo_iff_conormalResponse_quotientDerivation_eq_zero
      (k := k) (G.overlapLawIdeal I i j) (P.overlapDerivation G op i j))

end ArchitectureOperationPresentation

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.QuotientValuedDerivation

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ArchitectureOperationPresentation

end ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent
