import Formal.AG.SemanticRepair.Conormal.LawGeneratedIdealPowerSequence
import Formal.AG.SemanticRepair.Conormal.LawGeneratedIdealPowerShortExact
import Formal.AG.SemanticRepair.Conormal.LawGeneratedIdealPowerLiftedSheafification
import Formal.AG.SemanticRepair.Conormal.LawGeneratedRingSheaf
import Formal.AG.SemanticRepair.Conormal.LawGeneratedConormalIdealSheaf
import Formal.AG.SemanticRepair.Conormal.LawGeneratedConormalComparison
import Formal.AG.SemanticRepair.Conormal.LawGeneratedLargeCoefficientCech
import Formal.AG.SemanticRepair.Conormal.LawGeneratedLargeCoefficientH0
import Formal.AG.SemanticRepair.Conormal.LawGeneratedLargeConormalDescent
import Formal.AG.SemanticRepair.Conormal.LawGeneratedSemanticFirstOrderRepair
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleSite
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleTopology
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleLawCore
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleRawConormalSheaf
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleConormalSheafification
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleTupleProfile
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleSquareZeroH1
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleConormalH1Pair
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCirclePrimitiveAtlas
import Formal.AG.SemanticRepair.Conormal.LawGeneratedConormalFirstOrderDescentPackage

/-!
G-07 conormal first-order descent distillation (Issue #3757 tree, C6 #3767).

Aggregator for the law-generated first-order conormal specialization distilled
from `research/lean/ResearchLean/AG/QualitySurface/` (G-aat-quality-surface-07)
into the mainline, restated and reproved in-body per the distillation
discipline (`docs/aat/guideline.md` 移植 ≠ import):

* ideal-power sequence and short exactness of the law-generated
  `0 → I/I² → O/I² → O/I → 0` (`LawGeneratedIdealPowerSequence`,
  `LawGeneratedIdealPowerShortExact`, `LawGeneratedIdealPowerLiftedSheafification`);
* internal quotient-ring/module sheaves and the canonical comparison
  (`LawGeneratedRingSheaf`, `LawGeneratedConormalIdealSheaf`,
  `LawGeneratedConormalComparison`);
* the large-coefficient canonical-tuple Čech complex over finite-poset cover
  geometry, its `H⁰`, and the local-lift descent engine with connecting class,
  choice independence, corrected-lift amalgamation, and the
  zero-iff-global-lift equivalence (`LawGeneratedLargeCoefficientCech`,
  `LawGeneratedLargeCoefficientH0`, `LawGeneratedLargeConormalDescent`);
* the semantic first-order repair representation and its constructive
  equivalence with actual global `O/I²` lifts
  (`LawGeneratedSemanticFirstOrderRepair`);
* the Boolean-circle law-generated zero/nonzero conormal witness pair
  (`LawGeneratedBooleanCircle*`), the conormal-route nonvacuity witness kept
  distinct from the C7 general SAGA circle witness (例10.2/付録B.9);
* the closing package theorem `lawGeneratedConormalFirstOrderDescent_package`
  (`LawGeneratedConormalFirstOrderDescentPackage`).

The Čech layer imports only the generic `Formal.AG.Cohomology.CochainComparison`
hub and `Formal.AG.Site.FinitePosetGeometry`; nothing in this subtree imports
the SAGA-specific route (`Formal.AG.SemanticRepair.Saga`), and the SAGA route
does not import this subtree (Part X 定理6.3/7.6 の一般 comparison を
instantiate しない非循環規律).
-/
