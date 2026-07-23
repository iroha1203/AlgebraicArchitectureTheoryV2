import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ConormalJacobian

/-!
# Labeled conormal generation

Required `(lawIndex, atom)` labels already determine every generator of the
obstruction ideal.  This file transports that ideal-span statement to the full
conormal module and proves that vanishing on every labeled class is equivalent
to vanishing of the full conormal response.
-/

namespace ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent

universe u uR uk uChart

namespace LawGeneratedLabeledConormal

open AAT.AG AAT.AG.LawAlgebra

/-- If elements generate an ideal, their canonical classes generate its full
conormal module over the law quotient. -/
theorem cotangent_span_top_of_ideal_span
    {R : Type uR} [CommRing R] (I : Ideal R) {ι : Type u}
    (g : ι → I)
    (hspan : Ideal.span (Set.range fun i ↦ (g i : R)) = I) :
    Submodule.span (R ⧸ I) (Set.range fun i ↦ I.toCotangent (g i)) = ⊤ := by
  have hsubtype : Submodule.span R (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective I.subtype_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have himage :
        I.subtype '' Set.range g = Set.range (fun i ↦ (g i : R)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, rfl⟩
    rw [himage]
    exact hspan
  have hambient :
      Submodule.span R (Set.range fun i ↦ I.toCotangent (g i)) = ⊤ := by
    calc
      _ = Submodule.map I.toCotangent (Submodule.span R (Set.range g)) := by
        rw [Submodule.map_span]
        congr 1
        ext x
        simp
      _ = ⊤ := by
        rw [hsubtype, Submodule.map_top, I.toCotangent_range]
  exact Submodule.span_eq_top_of_span_eq_top R (R ⧸ I) _ hambient

variable {U : AtomCarrier.{u}} {Arch : ArchitectureObject U}
variable {S : Site.AATSite Arch}

/-- The required law/Atom witness values generate the existing obstruction
ideal; no representative generator family is supplied. -/
theorem span_requiredGeneratorWitness_eq_obstructionIdeal
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category) :
    Ideal.span (Set.range fun e : RequiredGeneratorLabel E ↦
      (requiredGeneratorWitness E W e : E.Observable W)) =
        E.obstructionIdeal W := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨e, rfl⟩
    exact (requiredGeneratorWitness E W e).property
  · change (E.selectedWitnessIdealFamily W).localObstructionIdeal ≤ _
    rw [ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff]
    intro lawIndex hrequired
    change Ideal.span (Set.range (E.violationCoordinate W lawIndex)) ≤ _
    apply Ideal.span_le.mpr
    rintro x ⟨atom, rfl⟩
    apply Ideal.subset_span
    exact ⟨(⟨lawIndex, hrequired⟩, atom), rfl⟩

/-- Required labeled classes generate the full objectwise conormal module. -/
theorem requiredGeneratorConormal_span_top
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category) :
    Submodule.span (E.Observable W ⧸ E.obstructionIdeal W)
        (Set.range (requiredGeneratorConormal E W)) = ⊤ := by
  exact cotangent_span_top_of_ideal_span (E.obstructionIdeal W)
    (requiredGeneratorWitness E W)
    (span_requiredGeneratorWitness_eq_obstructionIdeal E W)

section TypedLocalization

variable {k : Type uk} {Chart : Type uChart}
variable [Field k] [Fintype Chart]
variable (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
variable [Algebra k (E.Observable W)]

/-- The transported required witnesses generate each chart law ideal. -/
theorem span_chartRequiredGeneratorWitness_eq_chartLawIdeal
    (G : TypedLocalizationGeometry k (E.Observable W) Chart) (i : Chart) :
    Ideal.span (Set.range fun e : RequiredGeneratorLabel E ↦
      (chartRequiredGeneratorWitness E W G e i : G.chartRing i)) =
        G.chartLawIdeal (E.obstructionIdeal W) i := by
  let f := algebraMap (E.Observable W) (G.chartRing i)
  calc
    _ = Ideal.span (f '' Set.range fun e : RequiredGeneratorLabel E ↦
        (requiredGeneratorWitness E W e : E.Observable W)) := by
      congr 1
      ext x
      simp [f, chartRequiredGeneratorWitness, requiredGeneratorWitness]
    _ = Ideal.map f (Ideal.span (Set.range fun e : RequiredGeneratorLabel E ↦
        (requiredGeneratorWitness E W e : E.Observable W))) := by
      rw [Ideal.map_span]
    _ = Ideal.map f (E.obstructionIdeal W) := congrArg (Ideal.map f)
      (span_requiredGeneratorWitness_eq_obstructionIdeal E W)
    _ = _ := rfl

/-- The transported required witnesses generate each overlap law ideal. -/
theorem span_overlapRequiredGeneratorWitness_eq_overlapLawIdeal
    (G : TypedLocalizationGeometry k (E.Observable W) Chart) (i j : Chart) :
    Ideal.span (Set.range fun e : RequiredGeneratorLabel E ↦
      (overlapRequiredGeneratorWitness E W G e i j : G.overlapRing i j)) =
        G.overlapLawIdeal (E.obstructionIdeal W) i j := by
  let f := algebraMap (E.Observable W) (G.overlapRing i j)
  calc
    _ = Ideal.span (f '' Set.range fun e : RequiredGeneratorLabel E ↦
        (requiredGeneratorWitness E W e : E.Observable W)) := by
      congr 1
      ext x
      simp [f, overlapRequiredGeneratorWitness, requiredGeneratorWitness]
    _ = Ideal.map f (Ideal.span (Set.range fun e : RequiredGeneratorLabel E ↦
        (requiredGeneratorWitness E W e : E.Observable W))) := by
      rw [Ideal.map_span]
    _ = Ideal.map f (E.obstructionIdeal W) := congrArg (Ideal.map f)
      (span_requiredGeneratorWitness_eq_obstructionIdeal E W)
    _ = _ := rfl

/-- Required labeled chart classes generate the full chart conormal module. -/
theorem chartLabeledConormal_span_top
    (G : TypedLocalizationGeometry k (E.Observable W) Chart) (i : Chart) :
    Submodule.span (G.chartLawQuotient (E.obstructionIdeal W) i)
        (Set.range fun e : RequiredGeneratorLabel E ↦
          chartLabeledConormal E W G e i) = ⊤ := by
  exact cotangent_span_top_of_ideal_span
    (G.chartLawIdeal (E.obstructionIdeal W) i)
    (fun e ↦ chartRequiredGeneratorWitness E W G e i)
    (span_chartRequiredGeneratorWitness_eq_chartLawIdeal E W G i)

/-- Required labeled overlap classes generate the full overlap conormal module. -/
theorem overlapLabeledConormal_span_top
    (G : TypedLocalizationGeometry k (E.Observable W) Chart) (i j : Chart) :
    Submodule.span (G.overlapLawQuotient (E.obstructionIdeal W) i j)
        (Set.range fun e : RequiredGeneratorLabel E ↦
          overlapLabeledConormal E W G e i j) = ⊤ := by
  exact cotangent_span_top_of_ideal_span
    (G.overlapLawIdeal (E.obstructionIdeal W) i j)
    (fun e ↦ overlapRequiredGeneratorWitness E W G e i j)
    (span_overlapRequiredGeneratorWitness_eq_overlapLawIdeal E W G i j)

end TypedLocalization

end LawGeneratedLabeledConormal

namespace QuotientValuedDerivation

open AAT.AG AAT.AG.LawAlgebra LawGeneratedLabeledConormal

variable {U : AtomCarrier.{u}} {Arch : ArchitectureObject U}
variable {S : Site.AATSite Arch}
variable {k : Type uk} [Field k]

/-- A quotient-valued derivation has zero response on every required label
exactly when its full conormal response is zero. -/
theorem allLabeledResponses_zero_iff_conormalResponse_eq_zero
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
    [Algebra k (E.Observable W)]
    (d : Derivation k (E.Observable W)
      (E.Observable W ⧸ E.obstructionIdeal W)) :
    (∀ e : RequiredGeneratorLabel E,
      conormalResponse (E.obstructionIdeal W) d
        (requiredGeneratorConormal E W e) = 0) ↔
      conormalResponse (E.obstructionIdeal W) d = 0 := by
  constructor
  · intro h
    rw [← LinearMap.ker_eq_top]
    apply top_unique
    rw [← LawGeneratedLabeledConormal.requiredGeneratorConormal_span_top E W]
    apply Submodule.span_le.mpr
    rintro c ⟨e, rfl⟩
    change conormalResponse (E.obstructionIdeal W) d
      (requiredGeneratorConormal E W e) = 0
    exact h e
  · intro h e
    rw [h]
    exact LinearMap.zero_apply _

section TypedLocalization

variable {Chart : Type uChart} [Fintype Chart]

/-- On a typed chart, vanishing on every required label is equivalent to
vanishing of the full chart conormal Jacobian. -/
theorem allChartLabeledResponses_zero_iff_conormalJacobian_eq_zero
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
    [Algebra k (E.Observable W)]
    (G : TypedLocalizationGeometry k (E.Observable W) Chart) (i : Chart)
    (d : Derivation k (G.chartRing i)
      (G.chartLawQuotient (E.obstructionIdeal W) i)) :
    (∀ e : RequiredGeneratorLabel E,
      G.chartConormalJacobian (E.obstructionIdeal W) i d
        (chartLabeledConormal E W G e i) = 0) ↔
      G.chartConormalJacobian (E.obstructionIdeal W) i d = 0 := by
  constructor
  · intro h
    rw [← LinearMap.ker_eq_top]
    apply top_unique
    rw [← chartLabeledConormal_span_top E W G i]
    apply Submodule.span_le.mpr
    rintro c ⟨e, rfl⟩
    change G.chartConormalJacobian (E.obstructionIdeal W) i d
      (chartLabeledConormal E W G e i) = 0
    exact h e
  · intro h e
    rw [h]
    exact LinearMap.zero_apply _

/-- On a typed overlap, vanishing on every required label is equivalent to
vanishing of the full overlap conormal Jacobian. -/
theorem allOverlapLabeledResponses_zero_iff_conormalJacobian_eq_zero
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
    [Algebra k (E.Observable W)]
    (G : TypedLocalizationGeometry k (E.Observable W) Chart) (i j : Chart)
    (d : Derivation k (G.overlapRing i j)
      (G.overlapLawQuotient (E.obstructionIdeal W) i j)) :
    (∀ e : RequiredGeneratorLabel E,
      G.overlapConormalJacobian (E.obstructionIdeal W) i j d
        (overlapLabeledConormal E W G e i j) = 0) ↔
      G.overlapConormalJacobian (E.obstructionIdeal W) i j d = 0 := by
  constructor
  · intro h
    rw [← LinearMap.ker_eq_top]
    apply top_unique
    rw [← overlapLabeledConormal_span_top E W G i j]
    apply Submodule.span_le.mpr
    rintro c ⟨e, rfl⟩
    change G.overlapConormalJacobian (E.obstructionIdeal W) i j d
      (overlapLabeledConormal E W G e i j) = 0
    exact h e
  · intro h e
    rw [h]
    exact LinearMap.zero_apply _

end TypedLocalization

end QuotientValuedDerivation

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.LawGeneratedLabeledConormal

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.QuotientValuedDerivation

end ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent
