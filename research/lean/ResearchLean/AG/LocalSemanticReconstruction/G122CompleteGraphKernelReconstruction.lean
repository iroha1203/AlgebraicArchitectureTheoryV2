import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation
import ResearchLean.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition
import Formal.Util.AssertStandardAxioms

/-!
# Complete graph determination of the full G-122 source-kernel coordinates

For the fixed G-122 `barAlpha`, every raw comparison is already reconstructed
by a full direct normalization-kernel coordinate and a normalized source
automorphism.  This module reads the actual source automorphism through the
complete total-functional graph bundle and proves that those graphs separate
all raw comparisons and all accepted source-kernel codes.

Thus equality of the complete total-functional graph data determines the
accepted coordinates, while the existing coordinate assembly retains both
inverse laws.  The result does not claim that an arbitrary graph bundle is
coherent or assemblable.

## Implementation notes

The graph reading is applied to the source automorphism supplied by the
accepted raw-comparison equivalence.  Reading the entire raw comparison as an
opaque value was rejected because it would hide the computational separation
inside the input.  The source map is instead separated component by component,
and injectivity of the accepted equivalence transports that result back to raw
comparisons and their full source-kernel coordinates.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open AAT.AG.RealizationReconstruction

noncomputable section

namespace G122CompleteGraphKernelReconstruction

open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open CompleteGeometryFunctionGraphSeparation
open G122FullSourceKernelExactDecomposition

/-- Complete graph reading of the actual source automorphism of a fixed raw
comparison. -/
noncomputable def readRawComparisonGraphs (raw : RawComparison) :=
  readCompleteMapGraphs (rawComparisonSourceMulEquiv raw).hom.hom

/-- Complete graph readings jointly separate all fixed raw comparisons. -/
theorem readRawComparisonGraphs_injective :
    Function.Injective readRawComparisonGraphs := by
  intro first second graph_eq
  apply rawComparisonSourceMulEquiv.injective
  apply Iso.ext
  apply CategoryTheory.InducedCategory.hom_ext
  exact readCompleteMapGraphs_injective graph_eq

/-- Equality of complete graph readings determines the accepted full direct
normalization-kernel coordinates. -/
theorem readSourceKernel_eq_of_graph_eq {first second : RawComparison}
    (graph_eq : readRawComparisonGraphs first =
      readRawComparisonGraphs second) :
    readSourceKernel first = readSourceKernel second := by
  exact congrArg readSourceKernel
    (readRawComparisonGraphs_injective graph_eq)

/-- Complete graph equality of assembled coordinate codes is exactly equality
of the codes themselves.  The reverse direction uses no selected preimage. -/
theorem assembledGraphs_eq_iff (first second : FullSourceKernelCode) :
    readRawComparisonGraphs (assembleSourceKernel first) =
        readRawComparisonGraphs (assembleSourceKernel second) ↔
      first = second := by
  constructor
  · intro graph_eq
    have coordinate_eq := readSourceKernel_eq_of_graph_eq graph_eq
    exact (readSourceKernel_assembleSourceKernel first).symm.trans
      (coordinate_eq.trans (readSourceKernel_assembleSourceKernel second))
  · intro code_eq
    cases code_eq
    rfl

/-- Reading complete graphs after the accepted two-sided source-kernel
reconstruction returns the graphs of the original raw comparison. -/
theorem graphs_assembleSourceKernel_readSourceKernel (raw : RawComparison) :
    readRawComparisonGraphs
        (assembleSourceKernel (readSourceKernel raw)) =
      readRawComparisonGraphs raw := by
  rw [assembleSourceKernel_readSourceKernel]

/-- The accepted source-kernel coordinates are recovered after assembly, now
with complete graph separation available on the assembled comparison. -/
theorem readSourceKernel_assembleSourceKernel_with_graph_separation
    (code : FullSourceKernelCode) :
    readSourceKernel (assembleSourceKernel code) = code ∧
      ∀ candidate : FullSourceKernelCode,
        readRawComparisonGraphs (assembleSourceKernel candidate) =
            readRawComparisonGraphs (assembleSourceKernel code) →
          candidate = code := by
  constructor
  · exact readSourceKernel_assembleSourceKernel code
  · intro candidate graph_eq
    exact (assembledGraphs_eq_iff candidate code).mp graph_eq

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122CompleteGraphKernelReconstruction

end G122CompleteGraphKernelReconstruction

end

end AAT.AG.LocalSemanticReconstruction
