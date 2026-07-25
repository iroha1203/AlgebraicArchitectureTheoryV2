import Formal.AG.SemanticRepair.Saga.Cover
import Formal.AG.SemanticRepair.Saga.CechThreeTerm
import Formal.AG.SemanticRepair.Saga.Presentation
import Formal.AG.SemanticRepair.Saga.OrderedComparison
import Formal.AG.SemanticRepair.Saga.PartIVBridge
import Formal.AG.SemanticRepair.Saga.EquationLift
import Formal.AG.SemanticRepair.Saga.RepairTorsor
import Formal.AG.SemanticRepair.Saga.Exactness
import Formal.AG.SemanticRepair.Saga.EquationRealization
import Formal.AG.SemanticRepair.Saga.EquationProduction
import Formal.AG.SemanticRepair.Saga.KappaComparison
import Formal.AG.SemanticRepair.Saga.TrueSheafDescent
import Formal.AG.SemanticRepair.Saga.CircleWitness
import Formal.AG.SemanticRepair.Saga.DescentWitness

/-!
Part X SAGA route (Issue #3757 tree, C1 #3762).

Aggregator for the revised Part X formalization: monomorphic ordered cover and
intersection diagram (§1–§2), increasing three-term Čech complex with
Lemma 2.2 and Definition 2.3 `H¹`, semantic repair presentation and `M_sem`
(§3, Proposition 3.3, Definition 3.4), and the Lemma 2.1A comparison with the
Part IV ordered-tuple model, including the connection to
`Cohomology.CoverRelativeCechComplex`.

Issue #3734 adds the equation-system production route
(`Saga.EquationProduction`): the Proposition 6.1A restriction-compatibility of
the selected assignment is discharged by proof for support-Atom factored
selections, the produced `χ^E` value is definitionally the Part III
Theorem 11.4 generated interpretation of the displayed defect (with the
restriction face traced through `restrict_defect` /
`obstructionQuotientRestrict_mk`), the
Definition 5.3 typical-example route is named over the generated `Q_E`
(`LiftFiberData.equationLiftSystem`, an alias of the C2 engine, exercised by
the degenerate generated self-lift fiber `equationSelfLiftFiber`), and
`SagaEquationPacket.ofProduction` fixes the Theorem 1.1 bundle assembly
surface (its first concrete instance is the C7.5 descent packet below — see
its claim boundary).  `P_E` and its local lift atlas stay selected, per the §1
Theorem 1.1 input 6 and the Definition 5.3 closing classification, as do the
remaining selected inputs.

C7 (#3768) adds the 例10.2/付録B.9 independently generated circle comparison
witness (`Saga.CircleWitness`): a monomorphic 4-cycle cover on which the
presentation-generated `M_sem ≅ F₂` and the obstruction-quotient-generated
`Q_E = ℤ/(2)` fire Theorem 6.3/7.6 with `κ_*([r_sem]) = [r_E]` and both
classes nonzero; the comparison `Φ` runs between carriers of distinct type
formers, so it is not a same-carrier identity (a meta-level carrier
condition — the #3718 negative condition).

C7.5 (#3803) adds the zero-class descent witness (`Saga.DescentWitness`),
the dual of C7 on the same 4-cycle context lattice: coverage requirements
under which the 4-chart cover is admissible give a constructed
`TopologicalMonomorphicCover` and a classified topology, the untwisted state
systems satisfy the sheaf condition, the residual cochains generated from the
`(1,0,0,0)` atlases are not identically zero while both classes vanish, and
Theorem 8.2 / Corollary 8.3 / Theorem 1.1 fire on an actual global repair.
The packet is assembled through `SagaEquationPacket.ofProduction` (its first
concrete instance) with the nonzero-base-reading `LiftFiberData`
(`B_E = F₂`, `b ≡ 1`), so the Definition 5.3 typical-example route fires
nondegenerately.
-/
