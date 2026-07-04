# 代数幾何 AAT Lean proof obligation 台帳

この文書は、現行 AAT 数学本文と `Formal/AG` の対応を追跡する分割台帳である。
PRD-1〜10 の本文ラベル、Lean status、future proof obligation、explicit non-goal を
古典 AAT / downstream 台帳や研究ループ台帳から分離して管理する。分割全体の入口は
[証明義務と実証仮説](proof_obligations.md) を参照する。

## AG版AAT PRD-1 / 第I部 Atom・対象・法則

PRD-1 は `docs/aat/lean_ag_part_1_atoms_objects_laws_prd.md` で管理する。
Issue [#1913](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1913)
では `Formal/AG` の bootstrap と `I.定義1.1` の Atom carrier entrypoint を追加した。
Issue [#1918](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1918)
では A0-A8 を structure field として束ね、A3 ext 補題と A8 一意性 theorem を追加した。
Issue [#1922](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1922)
では命題A9の観測不完全性と存在一意性の分離を有限例 theorem として追加した。
Issue [#1926](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1926)
では AtomFamily、support、axis restriction、payload compatibility relation に相対化された
compatibility、origin marker、monotone inference closure と
closure 特徴付け3補題を追加した。
Issue [#1931](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1931)
では AtomConfiguration、Molecule、Subconfiguration と前順序補題を追加した。
Issue [#1936](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1936)
では ArchitectureObject、GeneratedObject、ObjectEquivalence、Atom-Origin theorem を追加した。
Issue [#1939](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1939)
では FunctionInvariant、PredicateInvariant、InvariantFamily、等式形 / 順序形 preservation を追加した。
Issue [#1942](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1942)
では Law、LawUniverse、Lawfulness、三述語 `SemanticLawful` /
`NoRequiredObstruction` / `RequiredSignatureAxesZero` を追加した。
Issue [#1945](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1945)
では Obstruction、ObstructionCircuit、ObstructionValuation、値域構造、
zero-reflecting aggregation と Nat / Bool / 非負 weight の finite-list theorem を追加した。
Issue [#1948](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1948)
では soundness / completeness 仮定から定理9.3 Lawfulness-Zero Obstruction 本体を証明した。
Issue [#1951](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1951)
では witness completeness / axis exactness / coverage / selected reading exactness を明示仮定として、
定理9.3 後段の三読み一致を証明した。
Issue [#1953](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1953)
では Object Algebra、Operation、ArchitectureSignature、Operation Reading の六役割 predicate を追加した。
Issue [#1955](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1955)
では AtomAxiomSystem と R1-R7 / AC12 の component を束ねる AAT Core theorem package を追加し、
`#print axioms` で `AATCorePackage.exists_ofComponents` / `ofComponents` /
`algebra_object` が追加公理に依存しないことを確認した。
Issue [#1957](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1957)
では finite Atom universe、例8.3 / 例8.4 の obstruction circuit、定理9.3 の finite example theorem、
AAT Core への handoff を追加した。
Issue [#1959](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1959)
では `Formal/AG` 全体の placeholder / unsafe scan、`Formal.Arch` import scan、
および R11 台帳同期を最終確認した。

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `I.定義1.1` Atom carrier | `defined only`. `Formal/AG/Atom/Atom.lean` が `AAT.AG.AtomRecord`, `AAT.AG.AtomCarrier`, `AAT.AG.AtomCarrier.record` を持つ。 | concrete graph / category / algebra / diagram / state transition instance はまだ proved claim ではない。 |
| `I.公理A0-A8` Atom system package | `defined only` / `proved` for A3 and A8 accessors. `Formal/AG/Atom/Axioms.lean` が `AAT.AG.AtomAxiomSystem`, `AAT.AG.AtomAxiomSystem.ext`, `AAT.AG.ExtractionDoctrine.atomize_unique`, `AAT.AG.AtomAxiomSystem.doctrine_family_unique` を持つ。 | concrete graph / category / algebra / diagram / state transition instance は後続 PRD に残る。 |
| `I.命題A9` 観測不完全性と存在一意性 | `defined only` / `proved`. `Formal/AG/Atom/Observation.lean` が `ObservationModel`, `ObservationProjection`, `ReconstructionAttempt`, `no_exact_reconstruction_of_nonInjective`, `A9Example.projection`, `A9Example.reconstruction`, `A9Example.noninjective_atom_observation`, `A9Example.unobserved_atom_exists`, `A9Example.noninjective_family_observation`, `A9Example.reconstruction_not_exact`, `A9Example.canonical_family_unique`, `A9Example.observation_incompleteness_coexists_with_a8` を持つ。 | A9 は observation incompleteness と A8 一意性の分離であり、Lawfulness theorem への追加接続は主張しない。 |
| `I.定義3.1-3.5` AtomFamily / closure | `defined only` / `proved`. `Formal/AG/Atom/Family.lean` が `AtomFamily`, `AtomFamily.Subset`, `AtomFamily.support`, `AtomFamily.restrictAxis`, `AtomFamily.Compatible`, `AtomFamily.EqCompatible`, `AtomFamily.AtomOrigin`, `AtomFamily.OriginMarked`, `AtomFamily.InferenceSystem`, `AtomFamily.IsClosed`, `AtomFamily.closure`, `AtomFamily.support_of_mem`, `AtomFamily.restrictAxis_subset`, `AtomFamily.restrictAxis_axis`, `AtomFamily.subset_closure`, `AtomFamily.closure_isClosed`, `AtomFamily.closure_minimal` を持つ。 | compatibility は選択された payload compatibility relation に相対化され、closure 3補題は monotone inference system に相対化される。 |
| `I.定義4.1 / 4.2 / 4.4` Configuration / Molecule / Subconfiguration | `defined only` / `proved`. `Formal/AG/Atom/Configuration.lean` が `AtomConfiguration`, `AtomConfiguration.Subconfiguration`, `AtomConfiguration.FamilySupported`, `AtomConfiguration.Molecule`, `AtomConfiguration.Subconfiguration.refl`, `AtomConfiguration.Subconfiguration.trans`, `AtomConfiguration.Subconfiguration.preorder`, `AtomConfiguration.Molecule.family_subset_parent`, `AtomConfiguration.Molecule.finite_marker` を持つ。 | relation / identification は Atom pair predicate として抽象化し、family support は `FamilySupported` predicate として分離する。graph / category / algebra / diagram への concrete structure maps は後続 Issue に残る。 |
| `I.定義5.1 / 5.2 / 命題5.3 / 定義5.4` ArchitectureObject / GeneratedObject / Atom-Origin / ObjectEquivalence | `defined only` / `proved`. `Formal/AG/Atom/ArchitectureObject.lean` が `ArchitectureObject`, `ArchitectureObject.GeneratedObject`, `ArchitectureObject.ObjectEquivalence`, `ArchitectureObject.atom_origin`, `ArchitectureObject.generated_family_eq`, `ArchitectureObject.generated_family_subset`, `ArchitectureObject.ObjectEquivalence.configuration_equivalent`, `ArchitectureObject.ObjectEquivalence.structure_maps_preserved`, `ArchitectureObject.ObjectEquivalence.selected_quantities_preserved` を持つ。 | structure maps `S` と selected quantities `Q` は抽象 carrier として記録し、graph / category / algebra / diagram / state transition への concrete interpretation は後続 PRD に残す。 |
| `I.定義6.1-6.3` Invariant / InvariantFamily / Preservation | `defined only` / `proved`. `Formal/AG/Atom/Invariant.lean` が `FunctionInvariant`, `PredicateInvariant`, `Invariant`, `InvariantFamily`, `Invariant.EqualityPreserved`, `Invariant.OrderPreserved`, `Invariant.PredicatePreserved`, `Invariant.equalityPreserved_apply`, `Invariant.orderPreserved_apply`, `Invariant.predicatePreserved_apply`, `InvariantFamily.get`, `InvariantFamily.get_eq` を持つ。 | preservation は selected source / target ArchitectureObject と selected value order に相対化される。 |
| `I.定義7.1-7.3` Law / LawUniverse / Lawfulness | `defined only` / `proved`. `Formal/AG/Atom/Law.lean` が `Law`, `LawRole`, `LawWitnessFamily`, `SignatureAxes`, `LawUniverse`, `LawUniverse.Required`, `LawUniverse.Optional`, `LawUniverse.Derived`, `Lawfulness`, `SemanticLawful`, `NoRequiredObstruction`, `RequiredSignatureAxesZero`, `lawfulness_required_holds`, `semanticLawful_iff_lawfulness`, `noRequiredObstruction_no_bad_witness`, `requiredSignatureAxesZero_axis` を持つ。 | required law satisfaction、selected witness absence、selected signature axes zero は定義として分離する。 |
| `I.定義8.1 / 8.2 / 8.5` Obstruction / ObstructionCircuit / ObstructionValuation | `defined only` / `proved`. `Formal/AG/Atom/Obstruction.lean` が `Obstruction`, `ObstructionCircuit`, `ObstructionValueDomain`, `ObstructionValuation`, `ZeroReflectingAggregation`, `ZeroReflectingListAggregation`, `LawUniverse.RequiredIndex`, `FiniteIndexEnumeration`, `ZeroReflectingListAggregation.toIndexed`, `omegaU`, `omegaU_zero_iff_required`, `ObstructionCircuit.relation_supported_holds`, `ObstructionCircuit.finite_marker`, `ObstructionCircuit.law_failure_holds`, `ObstructionValueDomain.nat`, `ObstructionValueDomain.bool`, `ObstructionValueDomain.NonnegativeWeight`, `ObstructionValueDomain.nonnegativeWeight`, `ObstructionAggregation.natSum_eq_zero_iff`, `ObstructionAggregation.boolOr_eq_false_iff`, `ObstructionAggregation.weightSup_eq_zero_iff`, `ObstructionAggregation.natSumListAggregation`, `ObstructionAggregation.boolOrListAggregation`, `ObstructionAggregation.weightSupListAggregation` を持つ。 | obstruction valuation は required law / selected aggregation に相対化される。finite-list aggregation は explicit covering enumeration により selected finite index aggregation へ持ち上げる。 |
| `I.命題9.1 / 9.2 / 定理9.3` Lawfulness-Zero Obstruction 本体 | `defined only` / `proved`. `Formal/AG/Atom/LawfulnessZero.lean` が `ObstructionSound`, `ObstructionComplete`, `law_holds_iff_omega_zero`, `lawfulness_iff_omegaU_zero` を持つ。 | soundness / completeness / zero-reflecting aggregation は theorem 引数として明示される。 |
| `I.定理9.3 後段` 三読み一致 | `defined only` / `proved`. `Formal/AG/Atom/ThreeReading.lean` が `ThreeReadingAgreementAssumptions`, `ThreeReadingAgreementAssumptions.semanticLawful_iff_noRequiredObstruction`, `ThreeReadingAgreementAssumptions.noRequiredObstruction_iff_requiredSignatureAxesZero`, `ThreeReadingAgreementAssumptions.semanticLawful_iff_requiredSignatureAxesZero`, `ThreeReadingAgreementAssumptions.threeReadingAgreement` を持つ。 | witness completeness、axis exactness、coverage、selected reading exactness は package field として明示される。 |
| `I.定義10.1-10.3 / 命題10.4` Object Algebra / Operation / Signature / Operation Reading | `defined only` / `proved`. `Formal/AG/Atom/ObjectAlgebra.lean` が `Operation`, `ArchitectureSignature`, `ObjectAlgebra`, `OperationRole`, `Operation.PreservesFunctionInvariant`, `Operation.PreservesPredicateInvariant`, `Operation.ReflectsObstruction`, `Operation.RepairsObstruction`, `Operation.ExtendsAtomFamily`, `Operation.SynthesizesLawfulObject`, `Operation.TranslatesRepresentation`, `ObjectAlgebra.operation_source_object`, `ObjectAlgebra.operation_target_object` と accessor theorem を持つ。 | これは R9 前半の語彙固定であり、定理10.5 AAT Core theorem package は下行で扱う。 |
| `I.定理10.5` AAT Core theorem package | `defined only` / `proved`. `Formal/AG/Atom/AATCore.lean` が `AATCorePackage`, `AATCorePackage.ofComponents`, `AATCorePackage.exists_ofComponents`, configuration-family / object-configuration 整合性 theorem、各 component accessor theorem を持つ。`#print axioms` では `exists_ofComponents`, `ofComponents`, `algebra_object` が追加公理に依存しない。 | これは selected component を singleton ObjectAlgebra に束ねる theorem package であり、obstruction circuit component の一致は `exists_ofComponents` 内では heterogeneous equality として読む。concrete graph / category / algebra / diagram / state transition instance は後続 Issue に残る。 |
| R10 finite model / 例8.3 / 例8.4 / 定理9.3 example theorem | `defined only` / `proved`. `Formal/AG/Examples/FiniteModel.lean` が `FiniteAtom`, `carrier`, `axiomSystem`, `finite_atom_exists`, `hasCycleWitness`, `cycleObstructionCircuit`, `substitutionObstructionCircuit`, `noCycleValuation`, `finite_lawfulness_iff_omega_zero`, `corePackage` を持つ。 | finite model は component / depends / contract / substitution atoms を持つ selected example universe として扱う。NoCycle / substitution failure と valuation は selected relation witness に相対化される。第II部以降の concrete graph / category / algebra / diagram / state transition instance は後続 Issue に残る。 |

第I部 PRD-1 の証明対象ラベルは次の状態で閉じる。

| 証明対象ラベル | Lean status |
| --- | --- |
| `I.命題A9` | `proved` |
| `I.命題5.3` | `proved` |
| `I.命題9.1 / 9.2 / 定理9.3` | `proved` |
| `I.定理9.3 後段` | `proved` |
| `I.定理10.5` | `proved` |
| `I.例8.3 / 例8.4 / 定理9.3 example` | `proved` |

AC15 scan status: `rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal/AG Formal/AG.lean`
と `rg -n "Formal\.Arch|import Formal\.Arch" Formal/AG Formal/AG.lean` は no matches である。

## AG版AAT PRD-2 / 第II部 Architecture Geometry・Site・Sheaf

PRD-2 は `docs/aat/lean_ag_part_2_sites_sheaves_prd.md` で管理する。
Issue [#1962](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1962)
では `Formal/AG/Site` の初期 entrypoint を追加し、PRD-1 の
`AATCorePackage` に依存する prerequisite package を置いた。
Issue [#1964](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1964)
では Architecture Context の最小モデルと §5 の context morphism role predicate を追加した。
Issue [#1966](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1966)
では Context Category、finite-meet preorder / quotient-poset package、readable equivalence quotient、
pullback / overlap 仮定 package、pullback lifting property、meet-pullback 補題を追加した。
Issue [#1968](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1968)
では Coverage Family と admissible cover の5条件を追加した。
Issue [#1970](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1970)
では admissible cover から生成される `J_U` と Mathlib `Coverage.toGrothendieck` bridge を追加した。
Issue [#1972](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1972)
では U-adequate cover と補題7.2A Witness-Closure Cover を追加した。
Issue [#1974](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1974)
では AAT Site と Architecture Geometry package を追加した。
Issue [#1976](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1976)
では presheaf、sheaf condition bridge、名前付き sheaf family package を追加した。
Issue [#1978](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1978)
では gluing data、descent、sheaf-descent 補題、sheafification comparison / gap を追加した。
Issue [#1980](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1980)
では finite poset AAT site regime、cover-relative Čech complex vocabulary、命題7.2C の finite / high-degree vanishing surface を追加した。
Issue [#1983](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1983)
では AAT sheaf category entrypoint `AATSh` と Mathlib / AAT sheaf bridge を追加した。
Issue [#1985](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1985)
では PRD-1 finite model 上の singleton site example、singleton admissible cover、
witness-closure adequate cover、selected finite poset regime、top cover membership、
degree 0 nerve dimension、positive degree Čech vanishing theorem を追加した。
Issue [#1993](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1993)
では `Formal/AG` の禁止語 / `Formal.Arch` import 監査と、第II部 theorem index /
proof obligation ledger の最終同期を確認した。
Issue [#1996](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1996)
では finite poset Čech cochain を coefficient presheaf の overlap section product として読み直し、
face restriction による selected differential、`d ∘ d = 0`、cocycle kernel、previous differential
image としての boundary predicate、その image を zero と同一視する selected kernel/image quotient
cohomology、nerve dimension 上の高次 cochain / cohomology vanishing surface を追加した。

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `II.R0` Part I prerequisites / Formal/AG/Site entrypoint | `defined only` / `proved`. `Formal/AG/Site/Basic.lean` が `AAT.AG.Site.PartIPrerequisites` と accessor theorem を持つ。 | 第II部外の一般 obstruction ideal / cohomology は扱わない。 |
| `II.定義3.1 / §5.1-5.4` Architecture Context と射 role | `defined only` / `proved`. `Formal/AG/Site/Context.lean` が `MinimalContext`, `ArchitectureContext`, `ContextMorphism`、restriction / projection / refinement / base change role predicate と accessor theorem を持つ。 | 全 runtime / source observation context の完全列挙は主張しない。 |
| `II.定義4.1 / 命題4.2 / 仮定4.3` Context Category と meet-pullback | `defined only` / `proved`. `Formal/AG/Site/ContextCategory.lean` が readable morphism 付き preorder-category package、finite meet、readable equivalence quotient、quotient object 上の finite-meet poset package、pullback / overlap package、pullback lifting property、meet-overlap 補題を持つ。 | 任意の concrete context universe が finite meet を持つとは主張しない。 |
| `II.定義6.1 / 定義7.1前半` Coverage Family と admissible cover | `defined only` / `proved`. `Formal/AG/Site/Coverage.lean` が coverage family `{ W_i -> W }`、selected law universe / selected reading を実引数に取る required support / witness / axis、overlap package に相対化した witness / boundary visibility、admissible cover の5条件と accessor theorem を持つ。 | cover の選択と visibility 前提は入力 package 側の責務として残る。 |
| `II.定義7.1後半 / R4` `J_U` と Mathlib bridge | `defined only` / `proved`. `Formal/AG/Site/Topology.lean` が context preorder の Mathlib thin category wrapper、admissible cover generated precoverage、`AATGrothendieckTopology`、identity/top cover、base-change stability、transitivity、admissible generated cover membership、明示 pullback / base-change 前提下の `Coverage.toGrothendieck` bridge theorem を持つ。 | `Coverage.toGrothendieck` bridge は明示 pullback / base-change stability assumptions に相対化される。 |
| `II.定義7.2 / 補題7.2A` U-adequate cover と witness-closure | `defined only` / `proved under explicit WitnessClosureCover package assumptions`. `Formal/AG/Site/Adequate.lean` が U-adequate cover、selected reading 上の witness ideal predicate とその restriction 保存、witness-closure cover construction package、補題7.2A `witnessClosureCover_uAdequate` を持つ。 | witness-closure cover package の seed / witness support / boundary visibility は明示前提であり、自動構成の完全性は主張しない。 |
| `II.定義8.1 / 定義2.1` AAT Site と Architecture Geometry | `defined only` / `proved`. `Formal/AG/Site/Geometry.lean` が `AATSite`、`AATSite.topology`、`ArchitectureGeometry`、PRD-1 core object との accessor theorem を持つ。 | 第III部以降の law algebra sheaf / obstruction ideal sheaf は扱わない。 |
| `II.定義9.1 / 定義10.1 / 定義10.2` Presheaf と sheaf condition | `defined only` / `proved`. `Formal/AG/Site/Sheaf.lean` が `AATPresheaf`、raw presheaf signature、`AATSheafCondition`、Mathlib `Presieve.IsSheaf` bridge、`AATSheaf`、`At / Law / Sig / State / Eff / Auth / Sem / Trace` の `ArchitectureSheafFamily` を持つ。 | named sheaf family は carrier package であり、各 law algebra sheaf の具体構成は第II部では主張しない。 |
| `II.定義11.1 / 定義11.2 / 定義12.1` Gluing / Descent / Sheafification Gap | `defined only` / `proved`. `Formal/AG/Site/Descent.lean` が `AATLocalSectionFamily`、`AATOverlapAgreement`、`AATCocycleCondition`、`AATGluingData`、`AATDescent`、`AATSheafConditionFor.descent`、`AATSheafCondition.descent`、`AATSheaf.descent`、`AATSheafificationComparison`、`AATSheafificationGap` を持つ。 | 一般 site の sheafification 構成は比較 / gap package に留める。 |
| `II.定義7.2B / 命題7.2C` Finite Poset Regime と Čech computation | `defined only` / `proved`. `Formal/AG/Site/FinitePoset.lean` が selected finite context poset 付き `FinitePosetAATSiteRegime`、`FinitePosetCechSimplex`、overlap object / coefficient section、coefficient presheaf の section product としての `FinitePosetCechCochain`、face restriction data、selected alternating-combination surface、`d ∘ d = 0` 付き `FinitePosetCechComplex`、cocycle kernel、previous differential image としての `FinitePosetCechBoundaryImage`、その image を zero と同一視する selected kernel/image quotient cohomology、`FinitePosetNerveDimension`、finite summand theorem、nerve dimension 上の cochain / cocycle / cohomology vanishing theorem を持つ。 | 一般 site の Čech complex、sheaf cohomology 計算、Leray 条件は主張しない。cohomology quotient relation は Type-valued coefficient surface に相対化した selected finite relation であり、一般の abelian sheaf cohomology との一致は主張しない。 |
| `II.§13 / R10` AAT sheaf category | `defined only` / `proved`. `Formal/AG/Site/SheafCategory.lean` が `AATSh`、`AATSh.toPresheafFunctor`、`AATSh.underlyingPresheaf`、`AATSh.presieve_isSheaf`、`AATSh.aatSheafCondition`、`AATSh.toAATSheaf` を持つ。 | law algebra sheaf の具体構成、topos 内部論理は扱わない。 |
| `II.R11 finite model examples` | `defined only` / `proved`. `Formal/AG/Examples/FiniteModel.lean` が PRD-1 finite model 上の singleton site、singleton admissible cover、witness-closure adequate cover、selected finite poset regime、top cover membership、degree 0 nerve dimension、positive degree Čech vanishing theorem を持つ。 | 非 singleton の finite poset site example は主張しない。 |

第II部 PRD-2 の証明対象ラベルは次の最終状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `II.命題4.2` | `proved` |
| `II.仮定4.3 meet-pullback` | `proved` |
| `II.定義7.1 J_U topology axioms` | `proved` |
| `II.定義7.1 Coverage.toGrothendieck bridge` | `proved under explicit pullback / base-change stability assumptions` |
| `II.補題7.2A` | `proved under explicit WitnessClosureCover package assumptions` |
| `II.定義8.1 AAT Site` | `defined only` / `proved` |
| `II.定義2.1 Architecture Geometry` | `defined only` / `proved` |
| `II.定義10.1 sheaf condition bridge` | `proved` |
| `II.定義11.1-12.1 sheaf-descent` | `proved` |
| `II.命題7.2C` | `proved` |
| `II.R11 finite model examples` | `proved` |

## AG版AAT PRD-3 / 第III部 Law Algebra・Obstruction Ideal・Lawful Locus

Tracking Issue [#1998](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1998)。
Issue [#1999](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1999)
では `Formal/AG/LawAlgebra` entrypoint、context 相対 coordinate family、
coefficient-valued coordinate reading、`FreeCommAlg_k(Coord_X(W))` から
Mathlib `MvPolynomial` への definitional bridge を追加した。
Issue [#2001](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2001)
では structural relation family、`J_struct`、raw ambient law algebra quotient、
restriction-stability 仮定 package、quotient 降下補題、明示法則付き raw ambient
presheaf bridge を追加した。
Issue [#2003](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2003)
では universe-lifted commutative `k`-algebra-valued presheaf、Law Algebra
Sheaf sheafification bridge、条件4.5 presentation-stability 仮定 package を追加した。
Issue [#2005](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2005)
では law-indexed violation witness family、law witness ideal、ideal / point /
canonical section pullback に沿った primary ideal-vanishing encoding、
no-cancellation 付き defect representative reading を追加した。
Issue [#2007](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2007)
では finite idempotent coordinate algebra
`k[x_e | e in E] / <x_e^2 - x_e>` を Boolean point product
`(E -> Bool) -> k` に collapse する `AlgEquiv`、全 module の
projective / flat surface、Mathlib `Tor` API による higher Tor 消滅、
ideal square の top 条件、`Ω_{A/k}=0` を追加した。
Issue [#2009](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2009)
では square-free witness regime、monomial obstruction ideal、
`Finset` ベースの abstract simplicial complex、Stanley-Reisner ideal、
`I_Ob = I_Delta`、minimal reduction exact ideal equality / radical equality、
minimal generator support と minimal forbidden support の一致、face と
admissible support の一致を追加した。
Issue [#2014](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2014)
では selected law witness ideal family、local obstruction ideal の sum 表示、
restriction compatibility 補題、sheaf-image construction と local sum 表示の
一致条件を追加した。
Issue [#2016](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2016)
では lawful locus `V(I_Ob)`、section pullback に沿った lawfulness、
factorization through lawful locus package、lawfulness と factorization の同値を追加した。
Issue [#2018](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2018)
では Architecture Nullstellensatz candidate を statement-only `Prop` として置き、
NSdepth profile と generator extension による monotonicity theorem を追加した。
Issue [#2020](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2020)
では `Spec_AAT` decoration、`h_W^U`、raw affine chart representability、
仮定8.4の sheafified chart presentation と representability 系を追加した。
Issue [#2023](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2023)
では既存 `Site.AATSh S` object と `LawAlgebraSheafPackage S k` に相対化された
ringed AAT topos、chart compatibility 7条件、Architecture Scheme の
Mathlib `LocallyRingedSpace` forgetful bridge、Scheme Gluing data、`O_X^U(W)` と
glued global sections の comparison を含む affine 復帰条件を明示仮定 package として追加した。
Issue [#2025](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2025)
では Lawfulness-Ideal Correspondence の7点明示仮定 package、`Lawful_U(s)` /
`s^* I_Ob^U = 0` / factorization through `Flat_U(X)` / PRD-1 `omegaU = 0` /
PRD-1 `RequiredSignatureAxesZero` の5項同値 edge theorem と theorem package を追加した。
Issue [#2027](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2027)
では例5.6E Stanley-Reisner chart、例7.2D concrete certificate / NSdepth、
cycle witness coordinate `c_ABC` の selected ideal `I_cycle = <c_ABC>`、
acyclic / cyclic pullback lawful locus、定理11.1 の acyclic / cyclic finite
correspondence package を example theorem として追加した。
Issue [#2029](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2029)
では R14 final ledger として `Formal/AG` の forbidden token / import boundary
scan、`lake build`、Lean theorem index / proof obligation ledger の最終一致確認を扱う。

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `III.R14` final verification | `verified`. `lake build`、`git diff --check`、hidden / bidirectional Unicode scan、`Formal/AG` forbidden token scan、`Formal.AG` import boundary scan を実行し、第III部 final ledger を最終実装と照合した。 | R14 は検証と台帳同期であり、新しい Lean theorem claim は追加しない。 |
| `III.R0` Formal/AG/LawAlgebra entrypoint | `defined only`. `Formal/AG/LawAlgebra.lean` が `Coordinate`、`AmbientAlgebra`、`StructuralRelation`、`StructureSheaf`、`WitnessIdeal`、`IdempotentCollapse`、`StanleyReisner`、`ObstructionIdeal`、`LawfulLocus`、`Nullstellensatz`、`AffineChart`、`Scheme`、`Correspondence`、`FiniteExamples` を束ね、`Formal/AG.lean` から import される。 | R14 final ledger は実装済み宣言と検証結果を照合する台帳作業であり、新しい theorem claim は追加しない。 |
| `III.定義3.1` Coordinate | `defined only` / `proved`. `Formal/AG/LawAlgebra/Coordinate.lean` が `CoordinateLabel`, `ArchitectureCoordinate`, `CoordinateFamily`, `CoordinateReading` と accessor theorem を持つ。 | coordinate は abstract local data reading であり、source observation completeness や concrete runtime coordinate の全列挙は主張しない。 |
| `III.定義4.1` Free Typed Commutative Algebra | `defined only` / `proved`. `Formal/AG/LawAlgebra/AmbientAlgebra.lean` が `FreeCommAlg`, `FreeTypedCommAlg`, `FreeTypedCommAlg.eq_mvPolynomial`, `FreeTypedCommAlg.coordVar`, `FreeTypedCommAlg.coordVar_eq_X` を持つ。 | ambient stage では law witness equation を quotient しない。 |
| `III.定義4.2 / 定義4.3 / 条件4.4 / 定義10.1` Structural Relation / Raw Ambient Algebra / Ring Restriction | `defined only` / `proved`. `Formal/AG/LawAlgebra/StructuralRelation.lean` が `StructuralRelationFamily`, `RelStruct`, `JStruct`, `RawAmbientLawAlgebra`, `TypedCoordinateRestriction`, `RestrictionStableStructuralRelations`, quotient descent lemma、明示 identity / composition law を持つ `RawAmbientPresheafBridge` を持つ。 | law witness equation は ambient stage では quotient しない。scheme-level atlas は R11 で別 package として追加済み。 |
| `III.定義2.1 / 条件4.5` Law Algebra Sheaf と Presentation Stability | `defined only` / `proved`. `Formal/AG/LawAlgebra/StructureSheaf.lean` が `AATCommAlgCat`, `AlgebraValuedAATPresheaf`, `LawAlgebraSheaf`, `RawAmbientAlgebraPresheafBridge`, `LawAlgebraSheafificationBridge`, `PresentationStableAATSite`, `LawAlgebraSheafPackage` と accessor theorem を持つ。raw ambient restriction と presheaf map の自然性、canonical map の sheafification universal property、selected generator / relation の canonical preservation を明示する。 | `O_X^U = (O_raw^U)^+` は selected sheafification bridge として扱う。一般 site の algebra-valued sheafification 理論は新規証明しない。scheme-level atlas は R11 で別 package として追加済み。 |
| `III.定義5.1 / 定義5.2 / 定義5.3` Violation Witness Family / Law Witness Ideal / Defect Section | `defined only` / `proved for accessor lemma`. `Formal/AG/LawAlgebra/WitnessIdeal.lean` が law-indexed `ViolationWitnessFamily`, `LawWitnessIdeal`, `LawWitnessPoint`, `LawWitnessIdealVanishesAtIdeal`, `LawWitnessIdealVanishesAtPoint`, `LawWitnessSectionPullback`, `DefectRepresentativeReading` と coordinate membership / no-cancellation accessor theorem を持つ。 | primary encoding は `I_L(W) ⊆ p` と canonical `O_raw^U(W) -> O_X^U(W)` bridge 経由の `s^* I_L = 0` であり、代表元 `δ_L` の vanishing は no-cancellation 条件つきの secondary reading としてだけ扱う。 |
| `III.補題5.6A` Idempotent Coordinate Collapse | `proved`. `Formal/AG/LawAlgebra/IdempotentCollapse.lean` が `IdempotentAlgebra = MvPolynomial E k ⧸ booleanIdeal E k`、`quotientAlgEquivPi : IdempotentAlgebra E k ≃ₐ[k] (BoolPoint E -> k)`、全 module projective / flat、higher Tor zero、ideal square top condition、Kähler differential subsingleton を持つ。 | `I/I²=0` は Lean では quotient-zero と同値な `ideal_square_comap_eq_top` として公開する。 |
| `III.定義5.6B / 定理5.6C / 系5.6D` Square-Free Witness Regime / Stanley-Reisner Obstruction Theorem / Obstruction Invariants | `defined only` / `proved`. `Formal/AG/LawAlgebra/StanleyReisner.lean` が `squareFreeMonomial`, `SquareFreeWitnessRegime`, `obstructionIdeal`, `AbstractSimplicialComplex`, `delta`, `stanleyReisnerIdeal`, `coordinateSubspaceArrangement`, `flatChart`, `obstructionIdeal_eq_stanleyReisnerIdeal`, `obstructionIdeal_eq_stanleyReisnerIdeal_of_minimal`, `minimalReduction_obstructionIdeal_eq`, `radical_minimalReduction_obstructionIdeal_eq`, `face_iff_admissibleSupport`, `minimalGeneratorSupport_iff_minimalForbidden` を持つ。 | ここでの obstruction ideal は square-free local monomial regime の ideal であり、R7 の obstruction ideal sheaf ではない。lawful locus / lawful section factorization は後続 R8 に残る。 |
| `III.定義6.1 / 定義6.2 / 定義10.2` Local Obstruction Ideal / Obstruction Ideal Sheaf / Ideal Restriction | `defined only` / `proved under explicit restriction-compatibility and sheaf-image agreement assumptions`. `Formal/AG/LawAlgebra/ObstructionIdeal.lean` が `SelectedLawWitnessIdealFamily`, `selectedElementSet`, `localObstructionIdeal`, `witnessIdeal_le_localObstructionIdeal`, `localObstructionIdeal_le_iff`, `RestrictionCompatible`, `map_localObstructionIdeal_le`, `SheafImageConstruction`, `imageIdeal_eq_localObstructionIdeal`, `localObstructionIdeal_eq_imageIdeal` を持つ。 | selected laws と sheaf-image 表示の一致範囲は明示仮定として扱う。scheme / gluing surface は R11 で追加済み。 |
| `III.定義7.1 / 定義7.2` Lawful Locus / Lawful Section | `defined only` / `proved`. `Formal/AG/LawAlgebra/LawfulLocus.lean` が `lawfulLocus`, `localLawfulLocus`, `LawfulSectionData`, `pulledObstructionIdeal`, `Lawful`, `FactorsThroughLawfulLocus`, `lawful_iff_pulledObstructionIdeal_eq_bot`, `factorsThroughLawfulLocus_of_lawful`, `lawful_of_factorsThroughLawfulLocus`, `lawful_iff_factorsThroughLawfulLocus`, `LocalLawfulSectionData` を持つ。 | factorization は R8 境界で obstruction-ideal vanishing と同値な package として扱う。scheme-level map object と gluing surface は R11 で追加済み。 |
| `III.定理候補7.2A / 定義7.2B / 命題7.2C` Architecture Nullstellensatz / NSdepth | `future proof obligation` / `defined only` / `proved`. `Formal/AG/LawAlgebra/Nullstellensatz.lean` が `booleanLawIdeal`, `VanishesAtIdeal`, `BooleanLawZeroSetEmpty`, `ArchitectureNullstellensatzCandidate`, `RadicalUnitCertificate`, `UnlawfulnessCertificate`, `HasCertificateAt`, `NSdepthProfile`, `NSdepth`, `GeneratorExtension`, `NSdepth_mono_of_generatorExtension` を持つ。定理候補7.2A は Lean 上では statement-only `Prop` surface としてコンパイルされ、証明済み theorem へは昇格していない。 | 定理候補7.2A の証明は future proof obligation として残す。Nullstellensatz 証明昇格は別作業。scheme / gluing surface は R11 で追加済み。 |
| `III.定義8.1 / 定義8.2 / 定義8.5 / 定理8.3 / 仮定8.4` Affine AAT Chart / Representability | `defined only` / `proved for raw quotient representability and under selected presentation assumptions`. `Formal/AG/LawAlgebra/AffineChart.lean` が `SpecAAT`, `pointSpace`, `localLawfulChart`, `AffineAATChart`, `hWU`, selected hom surface の `rawAffineChartRepresentability`, typed-coordinate / structural-relation quotient package の `RawAffinePresentation`, `CoordinateAssignment`, `assignmentAlgHom`, `assignmentAlgHom_X`, `SatisfiesStructuralRelations`, `hWUConfiguration`, `assignmentAlgHom_eq_zero_of_mem_JStruct`, `quotientAlgHomOfConfiguration`, `quotientAlgHomOfConfiguration_mk`, `configurationOfQuotientAlgHom`, `rawQuotientRepresentability`, `hWUConfigurationRepresentability`, `SheafifiedChartPresentation`, `sheafifiedChartRepresentability` を持つ。 | `Spec_AAT` は ordinary `PrimeSpectrum` と decoration の package として扱う。`hWU` は selected raw algebra hom surface、`hWUConfiguration` は typed coordinate assignment と structural relation satisfaction の surface、`rawQuotientRepresentability` は `MvPolynomial.aeval` と `Ideal.Quotient.liftₐ` による raw quotient algebra hom 対応である。Architecture Nullstellensatz 7.2A の証明昇格、scheme-level gluing の一般論、`Formal/Arch` 接続は扱わない。 |
| `III.定義9.1 / 定義9.2 / 定義9.3 / 定義10.3` Ringed AAT Topos / Architecture Scheme / Scheme Gluing | `defined only` / `proved for forgetful bridge`. `Formal/AG/LawAlgebra/Scheme.lean` が `RingedAATTopos`, `ChartCompatibility`, `ArchitectureScheme`, `SchemeGluingData`, `AffineReturnConditions`、既存 `Site.AATSh S` / `LawAlgebraSheafPackage S k` への接続、Mathlib `LocallyRingedSpace` forgetful bridge theorem を持つ。 | decorated gluing の一般論は主張しない。単一 affine chart への復帰は `AffineReturnConditions` の明示仮定として扱う。 |
| `III.定理11.1` Lawfulness-Ideal Correspondence | `proved under explicit correspondence assumptions`. `Formal/AG/LawAlgebra/Correspondence.lean` が `LawfulnessIdealCorrespondenceAssumptions`, `LawfulnessIdealCorrespondencePackage`, `lawful_iff_pulledObstructionIdeal_eq_bot`, `pulledObstructionIdeal_eq_bot_iff_factorsThroughLawfulLocus`, `factorsThroughLawfulLocus_iff_omegaU_zero`, `omegaU_zero_iff_requiredSignatureAxesZero`, `lawfulnessIdealCorrespondence` を持つ。 | obstruction soundness / completeness、axis exactness、witness coverage、U-adequate cover、`Ob_U` sheaf descent、ring restriction compatibility は明示仮定として扱う。Nullstellensatz 7.2A の証明昇格は主張しない。 |
| `III.例5.6E / 例7.2D / R13 finite examples` | `proved examples`. `Formal/AG/LawAlgebra/FiniteExamples.lean` が Stanley-Reisner chart、`I_Ob = <xy>`、faces/nonfaces、`1 = x - (x - 1)` concrete certificate から生成される `NSdepth = 1` profile、cycle witness coordinate `c_ABC` と `I_cycle = <c_ABC>`、acyclic / cyclic pullback lawful locus の点あり/なし、定理11.1 の acyclic / cyclic finite package を持つ。 | examples は selected finite surfaces であり、Nullstellensatz 7.2A の一般証明や全 finite graph の分類は主張しない。 |

第III部 PRD-3 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `III.R14 final verification` | `verified ledger / no new theorem claim` |
| `III.R0` | `defined only` |
| `III.定義3.1` | `defined only` / `proved` |
| `III.定義4.1` | `defined only` / `proved` |
| `III.定義4.2 / 定義4.3 / 定義10.1` | `defined only` / `proved` |
| `III.条件4.4` | `proved under explicit restriction-stability and presheaf-law assumptions` |
| `III.定義2.1 / 条件4.5` | `proved under explicit sheafification-bridge and presentation-stability assumptions` |
| `III.定義5.1 / 定義5.2 / 定義5.3` | `defined only` / `proved for accessor lemma` |
| `III.補題5.6A` | `proved` |
| `III.定義5.6B` | `defined only` / `proved for support lemmas` |
| `III.定理5.6C` | `proved` |
| `III.系5.6D` | `proved` |
| `III.定義6.1 / 定義6.2 / 定義10.2` | `defined only` / `proved under explicit restriction-compatibility and sheaf-image agreement assumptions` |
| `III.定義7.1 / 定義7.2` | `defined only` / `proved` |
| `III.定理候補7.2A` | `future proof obligation` / Lean surface is `statement only` |
| `III.定義7.2B` | `defined only` |
| `III.命題7.2C` | `proved` |
| `III.定義8.1 / 定義8.2 / 定義8.5` | `defined only` / `proved for typed configuration accessors` |
| `III.定理8.3 / 仮定8.4` | `proved for raw quotient representability and under selected presentation assumptions` |
| `III.定義9.1 / 定義9.2 / 定義9.3` | `defined only` / `proved for forgetful bridge` |
| `III.定義10.3` | `defined only under explicit affine-return assumptions` |
| `III.定理11.1` | `proved under explicit correspondence assumptions` |
| `III.R13 finite model examples` | `proved examples` |

## AG版AAT Lean形式化 PRD-4 / 第IV部 Obstruction Cohomology

File: `Formal/AG/Cohomology.lean`, `Formal/AG/Cohomology/Basic.lean`,
`Formal/AG/Cohomology/ObstructionSheaf.lean`,
`Formal/AG/Cohomology/CechComplex.lean`,
`Formal/AG/Cohomology/Cohomology.lean`,
`Formal/AG/Cohomology/FinitePosetComparison.lean`,
`Formal/AG/Cohomology/GluingMismatch.lean`,
`Formal/AG/Cohomology/LocalFlatnessGap.lean`,
`Formal/AG/Cohomology/BoundaryHolonomy.lean`,
`Formal/AG/Cohomology/BoundaryResidue.lean`,
`Formal/AG/Cohomology/HigherOverlap.lean`,
`Formal/AG/Cohomology/FlatnessCriterion.lean`,
`Formal/AG/Cohomology/CoverNerve.lean`,
`Formal/AG/Cohomology/FiniteExamples.lean`,
`Formal/AG/Cohomology/PeriodStokes.lean`,
`Formal/AG/Cohomology/Aggregation.lean`.

PRD-4 [第IV部 Obstruction Cohomology](lean_ag_part_4_obstruction_cohomology_prd.md)
は AC1/R0 と AC2/R1 から着手している。Issue
[#2042](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2042)
では `Formal/AG/Cohomology` の bootstrap entrypoint を追加した。Issue
[#2044](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2044)
では obstruction coefficient sheaf と標準 obstruction package を追加した。Issue
[#2047](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2047)
では一般 cover-relative Cech complex surface と条件付き cohomology notation を追加した。Issue
[#2049](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2049)
では PRD-2 finite-poset Cech surface との比較 target を追加した。Issue
[#2051](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2051)
では gluing mismatch、pseudo-torsor normalized cocycle、descent obstruction class を追加した。Issue
[#2054](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2054)
では hidden coupling class と Local Flatness Gap theorem を追加した。Issue
[#2056](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2056)
では 2-chart connecting homomorphism と boundary holonomy を追加した。Issue
[#2058](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2058)
では明示仮定ブロック下の Boundary Residue theorem を追加した。Issue
[#2060](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2060)
では `H^2` coherence failure と五項完全列 statement を追加した。Issue
[#2062](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2062)
では Cohomological Flatness Criterion と Local-to-Global Flatness corollary を追加した。
Issue
[#2064](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2064)
では cover nerve と、明示的な有限次元 accounting data 下の定理12.2 / 系12.3 /
定理12.4 / 系12.5 を追加した。
Issue
[#2066](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2066)
では擬円周 boundary model の finite golden example を追加した。
Issue
[#2070](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2070)
では period pairing、Stokes theorem、extension holonomy accounting convention を追加した。
Issue
[#2072](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2072)
では aggregation map、comparison map、定理候補14.2 statement、scale-stable debt を追加した。

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `IV.R0` Formal/AG/Cohomology entrypoint | `defined only` / `proved accessor`. `Formal/AG/Cohomology/Basic.lean` が `PartIVPrerequisites`、`sitePrerequisites`、`selectedAffineChart`、`site_architectureObject_eq` を持ち、PRD-2 `Site` と PRD-3 `LawAlgebra` への依存を明示する。 | obstruction sheaf、Cech complex、cohomology group は R0 では定義しない。 |
| `IV.定義2.1 / 定義2.2` Obstruction coefficient sheaf | `defined only`. `Formal/AG/Cohomology/ObstructionSheaf.lean` が `ObstructionSheaf`、`Ob_U`、`ModuleObstructionSheaf`、`OXModuleOb_U` を持つ。 | Type-valued sheaf carrier と additive/module structure の surface であり、Cech cochain や sheaf cohomology 計算はまだ主張しない。 |
| `IV.定義2.4` Canonical Obstruction Package | `defined only` / `proved accessor`. `Def_U` は PRD-3 `SelectedLawWitnessIdealFamily.localObstructionIdeal`、`ConDef_U` は Mathlib `Ideal.Cotangent` による `I_U/I_U^2`、`PushforwardConDef` は `i_* ConDef_U` の selected carrier boundary、`DerOb_U` は type-signature-only placeholder として扱う。 | cotangent complex、`Ext^1`、derived category、`DerOb_U` の内部構成は第V部へ委譲する。 |
| `IV.定義3.1-3.3` General cover-relative Cech complex | `defined only` / `proved accessor`. `Formal/AG/Cohomology/CechComplex.lean` が `CoverRelativeCechCover`、`CoverRelativeCechCochain`、`CoverRelativeCechComplex`、`faceRestrictionTerm`、`d_eq_alternatingFaceCombination`、`d_comp_d_eq_zero`、`FinitePosetComparisonTarget` を持つ。 | differential は face restriction term の selected alternating face-combination に一致する package として扱う。finite poset Cech との比較は `FinitePosetComparison.lean` の明示 comparison data で読む。 |
| `IV.定義4.1` Cover-relative and conditional cohomology notation | `defined only` / `proved accessor`. `CechCocycle`、`CechCoboundarySetoidSucc`、`CechCohomologySucc`、`CoverRelativeHn`、`CechToSheafComparisonHypothesis`、`RefinementSystemHypothesis`、`ConditionalSpaceCohomology`、`HnX_eq_coverRelative` を持つ。 | `H^n(X, Ob_U)` は比較仮定または refinement system を持つ条件付き notation に限る。無条件 sheaf cohomology は構成しない。 |
| `IV.R2 / AC4` PRD-2 finite-poset comparison | `proved under explicit comparison data`. `Formal/AG/Cohomology/FinitePosetComparison.lean` が `finitePosetCoverRelativeCover`、`FinitePosetCechComparisonData`、`generalComplex`、`comparisonTarget`、`cochain_to_from`、`differential_compatible`、`cohomology_target_eq`、`cohomology_to_from`、`cohomology_from_to` を持つ。 | PRD-2 Type-valued coefficient surface と PRD-4 additive obstruction sheaf surface の同一視、加法構造、cochain equivalence、cohomology quotient relation、cohomology map round-trip laws は明示 data として扱う。任意の finite-poset regime がその data を自動的に持つとは主張しない。 |
| `IV.定義5.1-5.3 / 原則5.2A` Gluing mismatch and descent class | `defined only` / `proved accessor`. `Formal/AG/Cohomology/GluingMismatch.lean` が `LocalFlatnessData`、`RestrictedLocalLawfulSection`、`GluingMismatchData`、`PseudoTorsorNormalizedMismatch`、`readMismatch_gluingMismatch`、`triple_mismatch_sum_zero`、`gluingMismatch_cocycle`、`descentObstructionClass` を持つ。 | restriction と Čech differential compatibility は selected package の明示 field に相対化する。descent class の非零性、coboundary 判定、global lawful section の不存在は R5 以降に残す。 |
| `IV.定義6.1 / 6.2 / 定理7.1` Hidden coupling and Local Flatness Gap | `proved under explicit compatibility data`. `Formal/AG/Cohomology/LocalFlatnessGap.lean` が `HiddenCouplingData`、`hiddenCouplingCocycle`、`hiddenCouplingClass`、`CompatibleGlobalLawfulSection`、`GlobalSectionCoboundarySoundness`、`hiddenCouplingClass_eq_zero`、`LocalFlatnessGapHypotheses`、`localFlatnessGap_no_globalLawfulSection` を持つ。 | global compatible lawful section は statement-level object として分離し、global section から coboundary witness を得る soundness は明示 hypothesis として扱う。hidden coupling class の具体的非零例、一般 descent theorem、R6 Boundary Residue はまだ主張しない。 |
| `IV.定義8.1-8.3 / 9.1` Boundary holonomy | `defined only` / `proved accessor`. `Formal/AG/Cohomology/BoundaryHolonomy.lean` が `TwoChartFeatureExtensionCover`、`BoundaryCoefficient`、`CoreCoefficient`、`FeatureCoefficient`、`BoundaryMismatchSection`、`TwoChartCechBoundaryComplex`、`d0`、`d0_apply`、`TwoChartConnectingHomomorphism`、`deltaCocycle`、`deltaClass`、`deltaH1`、`deltaH1_eq_deltaClass`、`boundaryHolonomy`、`boundaryHolonomy_eq_delta` を持つ。 | `C' = C_core ∪ F` と `B = C_core ∩ F` は selected 2-chart cover data として扱い、`C^0 = Ob(C_core) × Ob(F)`、`C^1 = Ob(B)`、`d^0 = s_F|_B - s_core|_B` を concrete Čech surface として記録する。connecting homomorphism は既存 cover-relative Čech complex 上の selected cochain map と selected class-level map であり、この AC8 surface 自体は derived Mayer-Vietoris triangle や Boundary Residue theorem / 定理9.2 を主張しない。 |
| `IV.定理9.2` Boundary Residue theorem | `proved under explicit Boundary Residue hypotheses`. `Formal/AG/Cohomology/BoundaryResidue.lean` が `BoundaryHolonomyVanishes`、`BoundaryResidueHypotheses`、`boundaryResidueSoundness`、`boundaryResidueCompleteness`、`globallyUFlat`、`boundaryResidueTheorem`、`globallyUFlat_of_boundaryHolonomy_zero`、`boundaryHolonomy_zero_of_globallyUFlat` を持つ。 | `C_core / F` の U-flatness、boundary witness coverage、axis exactness、boundary-exact 係数、ring restriction compatibility、effective torsor/module descent、holonomy completeness、NoHigherBoundaryObstruction は明示 field として扱い、soundness / completeness data はこれらの witness を受け取る。仮定なしの global flatness criterion や derived Mayer-Vietoris triangle は主張しない。 |
| `IV.定義10.1 / 定理候補10.4` H2 coherence failure and five-term statement | `statement only` / `defined only` / `proved accessor`. `Formal/AG/Cohomology/HigherOverlap.lean` が `TripleOverlapCoherenceFailure`、`hCocycle`、`hClass`、`LowDegreeFiveTermData`、`FiveTermExact`、`FiveTermStatement`、`fiveTermExact_of_statement` を持つ。 | triple-overlap coherence failure は degree-two Čech cocycle と `H^2` class として扱う。定理候補10.4 は既存 cover-relative Čech complex に相対化された finite-cover Čech filtration provenance 付きの低次五項完全列 statement に限定し、スペクトル系列一般論と証明は主張しない。 |
| `IV.定理11.1 / 系11.2` Cohomological Flatness Criterion | `proved under explicit Cohomological Flatness hypotheses`. `Formal/AG/Cohomology/FlatnessCriterion.lean` が `H1ClassVanishes`、`GluingObstructionClass`、`EffectiveAbelianObstructionTorsor`、`CohomologicalFlatnessCriterionHypotheses`、`cohomologicalFlatnessCriterion`、`adjustedGlobalLawfulSection_of_h1Class_zero`、`noAdjustedGlobalLawfulSection_of_h1Class_nonzero`、`localToGlobalFlatness` を持つ。 | local flatness、abelian coefficients、cocycle `g`、effective torsor、U-adequate cover、soundness / completeness、axis exactness、witness coverage、descent、effective adjustment は明示 field として扱う。torsor triviality を経由して `[g]=0` と調整後の大域 lawful section の同値を読む。abelianized class から non-abelian torsor の自明性が復元できるとは主張しない。 |
| `IV.定義12.1 / 定理12.2 / 系12.3 / 定理12.4 / 系12.5` Cover nerve and topological debt accounting | `proved under explicit finite-dimensional accounting data`. `Formal/AG/Cohomology/CoverNerve.lean` が `CoverNerve`、`ParallelEdgeComponents`、`ParallelFaceComponents`、`edge_component_selected`、`face_component_selected`、`FiniteDimensionalNerveCohomologyData`、`topologicalDebtCapacity`、`ConstantCoefficientNerveReading`、`h1_equiv`、`dimSpace_eq_dimNerve`、`dimH1_eq_b1`、`ForestCoverGluingData`、`localGluingSufficiency`、`localGluingSufficiency_subsingleton`、`EulerCochainAccounting`、`eulerAccounting`、`ShapeStalkPreservingRefactor`、`chi_invariant_under_refactor` を持つ。 | cover nerve は chart / pairwise-overlap component / triple-overlap component の明示 structure であり、多重 component を許す。rank-nullity lower bound、constant coefficient nerve reading、forest vanishing、Euler invariance は、有限 poset regime、有限次元 `k`-linear coefficient data、selected `k`-linear comparison、tree-induction absorption、shape/stalk-preserving refactor data に相対化する。forest vanishing は selected `H^1` の各 class が `0` になる theorem として扱う。任意 cover の無条件計算定理や一般 spectral sequence は主張しない。 |
| `IV.R10(a) / AC13` Pseudo-circle golden example | `proved finite example under explicit cover-relative H1 witness`. `Formal/AG/Cohomology/FiniteExamples.lean` が `FiniteExamples.PseudoCircleGolden.Chart`、`BoundaryEdge`、`coverNerve`、`each_chart_lawful`、`h0_witness_counting_sees_no_obstruction`、`boundaryCocycle`、`boundaryCocycle_AB_nonzero`、`CoverRelativeH1NonzeroWitness`、`concreteClass_nonzero`、`no_global_lawful_section_by_localFlatnessGap`、`pseudoCircle_h0_invisible_h1_obstructed` を持つ。 | 擬円周例は ArchSig v0.4.0 R14 golden fixture に対応する selected finite surface として扱う。H0 的 witness count は zero、finite boundary cocycle は visibly nonzero。actual cover-relative `K.CoverRelativeHn 1` の nonzero hidden coupling class は `CoverRelativeH1NonzeroWitness` として明示し、既存 `localFlatnessGap_no_globalLawfulSection` を呼んで compatible global lawful section が存在しないことを示す。ArchSig fixture JSON の検証、定理9.2 両方向例、forest / cycle nerve 例は AC14 に残す。 |
| `IV.R10(b)(c) / AC14` Boundary Residue and nerve finite examples | `proved finite examples under explicit packages`. `Formal/AG/Cohomology/FiniteExamples.lean` が `BoundaryResidueGolden.zero_boundaryResidue_glues`、`nonzero_boundaryResidue_blocks_gluing`、`boundaryResidue_two_direction_example`、`NerveGolden.forestCoverNerve`、`forestCoverGluingData`、`forestCover_H1_zero`、`cycleCoverNerve`、`cycleConstantCoefficientReading`、`cycleNerve_dimH1_eq_b1` を持つ。 | Boundary Residue 両方向例は既存 `BoundaryResidueHypotheses` に相対化し、`delta(b)=0` から global U-flat、`delta(b)≠0` から global U-flat 不在を読む。forest/cycle nerve 例は AC12 の `ForestCoverGluingData` と `ConstantCoefficientNerveReading` を finite selected examples として instantiate する。任意 cover の一般計算や ArchSig fixture JSON 検証は主張しない。 |
| `IV.定義13.1 / 定理13.2 / 定義13.4` Period Stokes and holonomy accounting | `proved under explicit pairing/accounting data`. `Formal/AG/Cohomology/PeriodStokes.lean` が `FiniteCechChainComplex`、`boundaryOp`、`boundary_comp_zero`、`CechCochainChainPairing`、`pair`、`StokesCompatiblePairing`、`cechStokes`、`ConnectingBoundaryRepresentative`、`connectingStokes`、`ExtensionHolonomyAccounting`、`kappa_U_additive`、`kappa_U_zero` を持つ。 | Stokes theorem は selected chain complex、cochain-chain pairing、Stokes-compatible condition に相対化する。connecting formula は selected connecting representative と boundary pairing compatibility に相対化する。定義13.4 は `kappa_U` の加法性を defining property とする会計規約であり、定理13.2 から自動的に従う系ではない。 |
| `IV.定義14.1 / 定理候補14.2 / 定義14.3` Aggregation and scale-stable debt | `statement only` / `defined only` / `proved accessor`. `Formal/AG/Cohomology/Aggregation.lean` が `FiniteSiteMorphism`、`PushforwardObstructionSheaf`、`HigherDirectImageCech`、`AggregationComparisonMap`、`InComparisonImage`、`AggregationFiveTermStatement`、`ScaleStableDebt`、`in_comparison_image` を持つ。 | finite site morphism、pushforward、higher direct image は selected statement surface として扱う。定理候補14.2 は五項完全列形の statement-only package であり、証明や spectral sequence 構成は主張しない。scale-stable debt は selected aggregation family 全体で comparison image に入ることとして定義する。 |

第IV部 PRD-4 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `IV.R0` | `defined only` / `proved accessor` |
| `IV.定義2.1 / 定義2.2` | `defined only` |
| `IV.定義2.4 Def_U / ConDef_U` | `defined only` / `proved accessor` |
| `IV.定義2.4 DerOb_U` | `defined only` / `type-signature-only placeholder` |
| `IV.定義3.1-3.3 / R2` | `defined only` / `proved d_comp_d accessor`; PRD-2 finite-poset comparison target and selected cohomology round-trip laws are `proved under explicit comparison data` |
| `IV.定義4.1 / R3` | `defined only` / `proved accessor under explicit comparison or refinement assumptions` |
| `IV.定義5.1-5.3 / R4` | `defined only` / `proved pseudo-torsor cocycle accessor under explicit normalization data` |
| `IV.定理7.1` | `proved under explicit compatibility data` |
| `IV.定義8.1-8.3 / 9.1` | `defined only` / `proved accessor` |
| `IV.定理9.2` | `proved under explicit Boundary Residue hypotheses` |
| `IV.定義10.1 / 定理候補10.4` | `statement only` / `defined only` / `proved accessor` |
| `IV.定理11.1 / 系11.2` | `proved under explicit Cohomological Flatness hypotheses` |
| `IV.定理12.2 / 系12.3 / 定理12.4 / 系12.5` | `proved under explicit finite-dimensional accounting data` |
| `IV.R10(a) / AC13` | `proved finite example under explicit cover-relative H1 witness` |
| `IV.R10(b)(c) / AC14` | `proved finite examples under explicit packages` |
| `IV.定義13.1 / 定理13.2 / 定義13.4` | `proved under explicit pairing/accounting data` |
| `IV.定義14.1 / 定理候補14.2 / 定義14.3` | `statement only` / `defined only` / `proved accessor` |
| `IV.定理候補10.4 / 定理候補14.2` | `future proof obligation` |

## AG版AAT Lean形式化 PRD-5 / 第V部 Derived Law Geometry と Repair

File: `Formal/AG/Derived.lean`, `Formal/AG/Derived/LawfulLoci.lean`,
`Formal/AG/Derived/Koszul.lean`, `Formal/AG/Derived/Intersection.lean`,
`Formal/AG/Derived/FreeResolution.lean`, `Formal/AG/Derived/TaylorResolution.lean`,
`Formal/AG/Derived/Transversality.lean`, `Formal/AG/Derived/RepairProfile.lean`,
`Formal/AG/Derived/Counterexample.lean`, `Formal/AG/Derived/Transfer.lean`,
`Formal/AG/Derived/StructurallyLawfulRepair.lean`, `Formal/AG/Derived/HilbertSeries.lean`,
`Formal/AG/Derived/WellFoundedRepair.lean`, `Formal/AG/Examples/DerivedPart5.lean`.

PRD-5 [第V部 Derived Law Geometry と Repair](lean_ag_part_5_derived_law_geometry_repair_prd.md)
は Issue [#2076](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2076)
で tracking している。Issue
[#2077](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2077)
では `Formal/AG/Derived` の entrypoint と、PRD-3 の lawful locus surface を再利用した
`I_U` / `I_V` 記法、law universe pair、classical joint lawful locus
`V(I_U + I_V)` を追加した。
Issue
[#2079](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2079)
では selected finite generators に相対化した chart-level Koszul surface、
derived lawful locus、truncation accessor を追加した。
Issue
[#2081](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2081)
では selected derived tensor complex を持つ chart-level derived intersection、
Mathlib `Tor` object への selected bridge に相対化した `LawConflict_i`、
`LawConflict_0 = O/(I_U + I_V)` accessor、および selected global /
hypercohomology notation carrier を追加した。
Issue
[#2084](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2084)
では selected finite free resolution、selected tensor-complex Tor computation、
Taylor complex surface、monomial law conflict regime、命題5.5 calculation package
の carrier / accessor surface を追加した。
Issue
[#2085](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2085)
では Mathlib `ProjectiveResolution.isoLeftDerivedObj` による
`Tor_i(A/I_U,A/I_V)` 計算 theorem、Mathlib projective resolution と Taylor complex
surface を結ぶ `TaylorMathlibResolution`、および命題5.5 theorem package を追加した。
Issue
[#2121](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2121)
では Taylor resolution と命題5.5 の GAP2 として、selected Prop field の
projection だけに留まらない `DirectTaylorResolutionPackage` と
`Proposition55DirectTheoremPackage` を追加し、selected finite-free exactness から
Taylor quotient-resolution を読み、right Taylor Mathlib resolution から Tor 計算と
lcm multidegree reading を直接束ねる theorem surface を公開した。
Issue
[#2090](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2090)
では selected law-conflict / Mathlib Tor vanishing predicate、定理6.1 の
derived non-transversality theorem、および定理7.3 の selected transversality
criterion package を追加した。
Issue
[#2092](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2092)
では repair comparison profile、pullback / probe repair profile、conflict
comparison profile、repair path、および ideal-order / valuation / rank / support
の代表 profile を追加した。
Issue
[#2096](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2096)
では命題9.2の shared-witness counterexample として、`s_t(x)=1`、
`s_t(xy)=1-t`、`s_t(xz)=t` の section 計算、endpoint residue の
`1 -> 0` / `0 -> 1`、U-axis 改善が V-axis 非増加を含意しない witness、
明示 principal-resolution Tor 非零 certificate、および一般化族の shared witness
support surface を追加した。
Issue
[#2098](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2098)
では transferred obstruction、transfer pairing data、pairing-based transfer
package、generic transfer package を追加し、定理10.5 と定理10.6 を
明示 support-localized / pairing-justified hypothesis と `tau_kappa` 非零に
相対化して証明した。
Issue
[#2101](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2101)
では structurally lawful repair と低次 `i = 1` reading を、selected
obstruction decrease、required lawful loci reachability、selected conflict
non-increase、transfer zero-or-controlled の component package として追加した。
Issue
[#2104](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2104)
では Hilbert series carrier、graded monomial conflict regime、短完全列加法性、
shifted free module reading、finite complex Euler characteristic package、
定理12.2の denominator-cleared conflict identity package、および interference
series を追加した。
Issue
[#2106](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2106)
では well-founded repair comparison profile、sound repair step evidence、
定理13.3の infinite repair sequence exclusion、定理13.4の finite sound synthesis
package、および第V部 finite examples を追加した。
Issue
[#2109](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2109)
では R12 の最終 scan と台帳同期を行い、`Formal/AG` 全体に
`axiom` / `admit` / `sorry` / `unsafe` がないこと、`Formal/AG.lean` が
第V部 entrypoint と finite examples を import すること、両台帳が第V部の
最終 Lean surface と residual boundary に一致することを確認した。
Issue
[#2120](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2120)
では共有 witness `I_U=<xy>` / `I_V=<xz>` の G5 Hilbert-series audit を
degree `0..9` の finite-window 検算から全次数係数恒等式へ昇格し、そこから
denominator-cleared identity と identity package を直接構成した。
Issue
[#2122](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2122)
では定理7.3の GAP2 として、任意の selected equivalence field ではなく、
selected derived tensor surface の `H0 ≃ O/(I_U+I_V)` と正次数 Mathlib Tor
消滅を束ねる concrete agreement reading を追加し、LawConflict vanishing /
Mathlib Tor vanishing との同値から criterion package を構成できるようにした。
Issue
[#2123](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2123)
では命題9.2 / 例5.6 の GAP2 として、actual Mathlib Tor class の非零性を
直接 field に持つ certificate だけでなく、selected shifted-kernel quotient の非零
class と Mathlib `Tor_1` への explicit linear equivalence から非零 Tor class を
構成する direct kernel-quotient calculation surface を追加した。一般化族も
selected index package から support / lcm / residue counterexample extension を
読む package surface に補強した。
PRD 本体の checkbox は prd-loop の不変条件として編集せず、達成状態はこの台帳と
tracking Issue [#2076](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2076)
で管理する。

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `V.R0` Formal/AG/Derived entrypoint | `defined only`. `Formal/AG/Derived.lean` が `Formal/AG/Derived/LawfulLoci.lean`、`Formal/AG/Derived/Koszul.lean`、`Formal/AG/Derived/Intersection.lean`、`Formal/AG/Derived/FreeResolution.lean`、`Formal/AG/Derived/TaylorResolution.lean`、`Formal/AG/Derived/Transversality.lean`、`Formal/AG/Derived/RepairProfile.lean`、`Formal/AG/Derived/Counterexample.lean`、`Formal/AG/Derived/Transfer.lean`、`Formal/AG/Derived/StructurallyLawfulRepair.lean`、`Formal/AG/Derived/HilbertSeries.lean`、`Formal/AG/Derived/WellFoundedRepair.lean` を束ね、`Formal/AG.lean` から import される。第V部 finite examples は `Formal/AG/Examples/DerivedPart5.lean` として `Formal/AG.lean` から import される。 | 余接複体 `L_{Flat/X}` と `Ext^1` は別 future obligation として残す。 |
| `V.定義2.1 / 定義3.1` Lawful loci and classical joint locus | `defined only` / `proved accessor`. `LawUniverseReading`、`LawUniversePair`、`LawUniversePair.I_U`、`I_V`、`flatU`、`flatV`、`classicalJointIdeal`、`classicalJointLawfulLocus`、`flatU_eq_lawfulLocus`、`flatV_eq_lawfulLocus`、`classicalJointLawfulLocus_eq_zeroLocus`、`classicalJointLawfulLocus_eq_flatU_inter_flatV` を持つ。 | この行では classical joint locus までを扱う。derived lawful locus、`LawConflict_i`、`Tor_i`、derived non-transversality は後続行で管理する。 |
| `V.定義2.3 / 原則2.4` Koszul complex and derived lawful locus truncation | `defined only` / `proved accessor`. `Koszul.SelectedGeneratorFamily`、`SelectedGeneratorFamily.generatedIdeal`、`firstTerm`、`d1`、`d1_mem_generatedIdeal`、`KoszulComplex`、`C0`、`C1`、`d1`、`zeroHomologyIdeal`、`zeroHomology`、`zeroHomologyIdeal_eq`、`zeroHomology_eq_classicalQuotient`、`zeroHomologyAlgEquivClassicalQuotient`、`zeroHomologyRingEquivClassicalQuotient`、`DerivedLawfulLocus`、`structureSheafComplex`、`truncation`、`truncation_eq_classicalQuotient`、`truncationAlgEquivClassicalQuotient`、`truncationRingEquivClassicalQuotient`、`truncationIdeal_eq`、`truncation_locus_eq_classical` を持つ。 | chart-level selected finite generator surface であり、derived category 一般論、higher Koszul homology、Tor、generator choice independence は R3 以降または future boundary に残す。 |
| `V.定義4.1 / 5.1 / 5.2` Derived intersection and LawConflict bridge | `defined only` / `proved accessor`. `Intersection.classicalJointQuotient`、`mathlibTor`、`SelectedDerivedTensorComplex`、`SelectedDerivedTensorComplex.C0`、`homology0`、`homology0LinearEquivClassicalJoint`、`ChartDerivedIntersection`、`ChartDerivedIntersection.classicalQuotient`、`structureSheafComplex`、`homology0LinearEquivClassicalJoint`、`SelectedTorBridge`、`SelectedTorBridge.torLinearEquivMathlib`、`SelectedTorBridge.LawConflict`、`LawConflict₁`、`lawConflict_eq_tor`、`lawConflictLinearEquivMathlibTor`、`lawConflict0AlgEquivClassicalJoint`、`lawConflict0RingEquivClassicalJoint`、`LawConflictPackage`、`LawConflictPackage.LawConflict`、`LawConflictPackage.LawConflict₁`、`LawConflictPackage.lawConflict_eq_tor`、`LawConflictPackage.lawConflictLinearEquivMathlibTor`、`LawConflictPackage.lawConflict0AlgEquivClassicalJoint`、`LawConflictPackage.lawConflict0RingEquivClassicalJoint`、`SelectedGlobalLawConflictReading`、`SelectedGlobalLawConflictReading.H0`、`H0LawConflict₁`、`h0LinearEquivSelectedLawConflict`、`hypercohomology`、`LawfulLoci.LawUniversePair.DerivedIntersectionFor`、`LawfulLoci.LawUniversePair.derivedIntersection` を持つ。 | selected complex / bridge / global notation data に相対化しており、Cech-to-sheaf comparison、global cohomology 計算は R5 以降に残す。 |
| `V.R4 / 定義5.4 / 命題5.5` Monomial conflict calculation | `proved under explicit Mathlib projective-resolution / Taylor identification data`. `FreeResolution.SelectedFiniteFreeResolution`、`SelectedFiniteFreeResolution.termLinearEquivFree_certificate`、`exact_certificate`、`SelectedTensorComplex`、`SelectedTensorComplex.homology`、`tensorOfResolution_certificate`、`FiniteFreeResolutionTorComputation`、`mathlibTorLinearEquivTensorHomology`、`tensorHomologyLinearEquivMathlibTor`、`FreeResolution.MathlibResolution.quotientModule`、`tensorAppliedComplex`、`torIsoProjectiveResolutionHomology`、`FiniteFreeMathlibResolution`、`FiniteFreeMathlibResolution.termIsoFree_certificate`、`torIsoTensorHomology`、`tensorHomologyIsoTor`、`TaylorResolution.SquareFreeMonomialIdealPresentation`、`generatedIdeal_eq`、`squareFree_certificate`、`MonomialLawConflictRegime`、`lcmSupport`、`lcmSupport_eq_union`、`left_forbiddenSupport_subset_lcmSupport`、`right_forbiddenSupport_subset_lcmSupport`、`mem_lcmSupport_iff`、`TaylorComplex`、`TaylorComplex.resolvesQuotient_certificate`、`d_comp_d_certificate`、`multidegree_union_eq`、`multidegree_pair_eq_union`、`TaylorSelectedFreeResolutionData`、`TaylorSelectedFreeResolutionData.termLinearEquivSelectedResolution`、`differentialCompatible_certificate`、`resolvesQuotient_from_selectedResolution`、`TaylorMathlibResolution`、`TaylorMathlibResolution.identifiesTaylorTerms_certificate`、`identifiesTaylorDifferentials_certificate`、`taylorResolution_certificate`、`mathlibResolutionTorIsoTensorHomology`、`DirectTaylorResolutionPackage`、`DirectTaylorResolutionPackage.selectedTaylor_resolvesQuotient_from_exact`、`mathlibTaylor_resolvesQuotient_from_selectedExact`、`taylorResolution_theorem`、`differential_square_zero`、`MonomialConflictCalculation`、`computesLawConflict_certificate`、`lawConflictLinearEquivTensorHomology`、`lcm_multidegree_eq_union`、`Proposition55TheoremPackage`、`Proposition55TheoremPackage.computesLawConflict_certificate`、`taylorResolution_certificates`、`taylor_differentials_square_zero`、`lawConflictIsoRightMathlibResolutionTensorHomology`、`rightMathlibResolutionTensorHomologyIsoLawConflict`、`lcm_multidegree_eq_union`、`left_forbiddenSupport_subset_lcmSupport`、`right_forbiddenSupport_subset_lcmSupport`、`mem_lcmSupport_iff`、`ComputedTorAndLcmSupport`、`torComputationAndLcmSupport`、`Proposition55DirectTheoremPackage`、`Proposition55DirectTheoremPackage.taylorResolution_theorems`、`taylor_differentials_square_zero`、`lawConflictIsoRightMathlibResolutionTensorHomology`、`rightMathlibResolutionTensorHomologyIsoLawConflict`、`lcm_multidegree_eq_union`、`left_forbiddenSupport_subset_lcmSupport`、`right_forbiddenSupport_subset_lcmSupport`、`mem_lcmSupport_iff`、`ComputedTorAndLcmSupport`、`torComputationAndLcmSupport` を持つ。 | Mathlib `Tor` は second tensor factor を left-deriveするため、selected right Taylor package に付随する Mathlib finite-free resolution から `Tor_i(A/I_U,A/I_V)` を計算する。Taylor complex が quotient resolution であることは、selected finite-free resolution の exactness から `resolvesQuotient_from_selectedResolution` と `DirectTaylorResolutionPackage.mathlibTaylor_resolvesQuotient_from_selectedExact` で読む theorem surface、および `TaylorMathlibResolution` の Mathlib projective-resolution identification data に相対化する。命題5.5 は legacy selected calculation package に加え、`Proposition55DirectTheoremPackage` により separate `computesLawConflict` Prop field なしで right Taylor Mathlib resolution の Tor iso と lcm multidegree union reading を束ねる。R4 package 単体では Scarf complex、lcm-lattice resolution、minimality、concrete Tor nonzero examples、transversality theorem までは主張しない。 |
| `V.定理6.1 / 定義7.1-7.4 / 定理7.3` Derived transversality | `proved under explicit selected transversality criterion data`. `Transversality.LawConflictVanishes`、`PositiveLawConflictVanishing`、`LawConflictNonzero`、`FirstLawConflictNonzero`、`DerivedNonTransverse`、`MathlibTorVanishes`、`PositiveMathlibTorVanishing`、`Transversality.LawConflictPackage.derivedNonTransverse_of_firstLawConflictNonzero`、`not_positiveLawConflictVanishing_of_firstLawConflictNonzero`、`lawConflictVanishes_iff_mathlibTorVanishes`、`positiveLawConflictVanishing_iff_mathlibTorVanishing`、`not_positiveMathlibTorVanishing_of_firstLawConflictNonzero`、`DerivedTransversalityCriterion`、`SelectedClassicalAgreementData`、`SelectedDerivedTensorClassicalAgreement`、`SelectedDerivedTensorClassicalAgreement.iff_positiveMathlibTorVanishing`、`iff_positiveLawConflictVanishing`、`of_positiveLawConflictVanishing`、`positiveLawConflictVanishing`、`of_positiveMathlibTorVanishing`、`toDerivedTransversalityCriterion`、`toSelectedClassicalAgreementData`、`SelectedClassicalAgreementData.toDerivedTransversalityCriterion`、`classicalAgreement_of_positiveLawConflictVanishing`、`positiveLawConflictVanishing_of_classicalAgreement`、`DerivedTransversalityCriterion.criterion_positiveTorVanishing_iff_classicalAgreement`、`positiveLawConflictVanishing_iff_classicalAgreement` を持つ。 | 定理7.3 は selected `classicalAgreement` statement を、正次数 Mathlib Tor 消滅の明示 equivalence data だけでなく selected LawConflict vanishing data から構成できる criterion surface として読む。GAP2 の concrete agreement reading では selected derived tensor surface の `H0 ≃ O/(I_U+I_V)` と正次数 Mathlib Tor 消滅を束ね、LawConflict bridge を通じて同値を返す。global derived category 一般論、Cech-to-sheaf comparison、global cohomology 計算、certificate-free concrete Tor nonzero examples は主張しない。 |
| `V.定義8.1-8.4` Repair profile and repair path | `defined only` / `proved accessor`. `RepairProfile.RepairComparisonLevel`、`RepairComparisonProfile`、`RepairComparisonProfile.sectionLe`、`geometryLe`、`sectionComparison_of_improves`、`geometryComparison_of_improves`、`idealOrderRepairProfile`、`valuationRepairProfile`、`rankRepairProfile`、`supportRepairProfile`、`RepairKind`、`PullbackRepairProfile`、`PullbackRepairProfile.IsInternal`、`IsGeometric`、`pullbackObstructionComparison_certificate`、`probeComparison_certificate`、`geometryImproves_certificate`、`ConflictComparisonProfile`、`ConflictComparisonProfile.selectedDegree_positive`、`comparisonMap_ordered_certificate`、`doesNotIncreaseSelectedConflict_certificate`、`RepairPathKind`、`UAxisObstructionDecreases`、`RepairPath`、`RepairPath.decreasesUAxis_certificate`、`uAxisDecrease_certificate`、`sectionComparison_of_uAxisDecrease` を持つ。 | repair comparison / pullback / conflict comparison は selected profile data に相対化する。profile-independent repair theorem、global monotone repair guarantee は主張しない。 |
| `V.命題9.2` Shared-witness repair counterexample | `proved under explicit principal-resolution kernel quotient / Tor bridge data`. `Counterexample.SharedWitnessCoord`、`SharedWitnessCoord.ChartRing`、`PathRing`、`xy`、`xz`、`idealU`、`idealV`、`pathAssignment`、`sectionFamily`、`section_x`、`section_xy`、`section_xz`、`sharedWitness_fixed_to_one`、`ResidueEndpointPath`、`ResidueEndpointPath.sharedWitness`、`sharedWitness_uStart`、`sharedWitness_uEnd`、`sharedWitness_vStart`、`sharedWitness_vEnd`、`UImproves`、`VNonIncreasing`、`VWorsens`、`sharedWitness_UImproves`、`sharedWitness_VWorsens`、`sharedWitness_not_VNonIncreasing`、`sharedWitness_UImproves_and_not_VNonIncreasing`、`SharedWitnessTorNonzeroCertificate`、`SharedWitnessTorNonzeroCertificate.principalResolutionCalculation_certificate`、`mathlibTor1_nonzero`、`SharedWitnessPrincipalResolutionCalculation`、`shiftedKernelRepresentative_certificate`、`tensorDifferentialKillsRepresentative_certificate`、`notTensorBoundary_certificate`、`toTorNonzeroCertificate`、`mathlibTor1_nonzero_of_principalResolutionCalculation`、`SharedWitnessPrincipalKernelQuotientCalculation`、`shiftedKernelClass_nonzero`、`SharedWitnessPrincipalKernelQuotientCalculation.tensorDifferentialKillsRepresentative_certificate`、`SharedWitnessPrincipalKernelQuotientCalculation.notTensorBoundary_certificate`、`mathlibTorClass`、`mathlibTorClass_ne_zero`、`toPrincipalResolutionCalculation`、`mathlibTor1_nonzero_of_kernelQuotientCalculation`、`GeneralizedCoord`、`GeneralizedCoord.leftSupport`、`rightSupport`、`sharedWitness_mem_leftSupport`、`sharedWitness_mem_rightSupport`、`lcmSupport`、`lcmSupport_eq_union`、`sharedWitness_mem_lcmSupport`、`sharedWitness_mem_bothSupports`、`generalized_sharedWitness_u_improves_not_v_nonincreasing`、`generalized_sharedWitness_counterexample_surface`、`GeneralizedSharedWitnessCounterexample`、`ofIndices`、`sharedWitness_in_both_supports`、`sharedWitness_in_lcmSupport`、`u_improves_not_v_nonincreasing`、`counterexample_extension_surface`、`SharedWitnessRepairCounterexample`、`SharedWitnessRepairCounterexample.ofPrincipalResolutionCalculation`、`ofKernelQuotientCalculation`、`u_residue_path`、`v_residue_path`、`u_improves_not_v_nonincreasing`、`tor1_nonzero` を持つ。 | residue 計算と U/V endpoint 非含意は concrete に証明する。`Tor_1(R/<xy>,R/<xz>) != 0` は selected shifted-kernel quotient の非零 class と Mathlib `Tor_1` への explicit linear equivalence から `mathlibTorClass_ne_zero` と `mathlibTor1_nonzero_of_kernelQuotientCalculation` で読む。完全な certificate-free Mathlib Tor class 構成や global principal-resolution theorem は主張しない。一般化族は `<x y_i>` / `<x z_j>` の selected index package から support / lcm support / U 改善 / V 非単調の counterexample extension surface を公開する。この path は `x |-> 1` のため support-localized transfer の例ではない。 |
| `V.定義10.1 / 定義10.4 / 定理10.5 / 定理10.6` Transfer pairing | `proved under explicit transfer-pairing data`. `Transfer.TransferredObstruction`、`TransferredObstruction.HasNontrivialResidue`、`TransferPairingData`、`TransferPairingData.transferResidue`、`HasNontrivialTransferredResidue`、`supportLocalized_or_pairingJustified`、`PairingBasedTransferPackage`、`PairingBasedTransferPackage.pairingBasedTransfer`、`records_supportLocalized_or_pairingJustified`、`transferredObstruction`、`transferredObstruction_nontrivial`、`ProperSubspace`、`GenericTransferPackage`、`GenericTransferPackage.transferZeroDirections`、`tauKappa_nonzero`、`transferZeroDirections_proper`、`nonzeroTransferredResidue_of_not_mem_kernel`、`transferZeroDirections_contained_in_proper_subspace` を持つ。 | 定理10.5 は selected direction / conflict class / transfer residue / pairing と、support-localized または pairing-justified hypothesis に相対化する。`LawConflict_1 != 0` だけから arbitrary direction の transfer は結論しない。定理10.6 は固定した `kappa` から得る linear map `tau_kappa` に相対化し、非零なら kernel が top ではないことを proper subspace として読む。 |
| `V.定義11.1` Structurally lawful repair | `defined only` / `proved accessor`. `RepairCriterion.StructurallyLawfulRepair`、`StructurallyLawfulRepair.selectedObstructionDecreases_certificate`、`requiredLawfulLociReachable_certificate`、`conflictNonIncreasingSelectedDegrees_certificate`、`transferZeroOrControlled_certificate`、`uAxisDecrease_certificate`、`selectedConflictProfileDoesNotIncrease`、`LowDegreeStructurallyLawfulRepair`、`LowDegreeStructurallyLawfulRepair.degreeOne_certificate`、`degreeOne_positive`、`selectedObstructionDecreases_certificate`、`transferZeroOrControlled_certificate` を持つ。 | structurally lawful repair は `P_U` と `Q_{U,V}` と transfer-control reading に相対化された package であり、Hilbert series theorem、well-founded synthesis、global repair success はまだ主張しない。 |
| `V.定義12.1 / 定理12.2` Hilbert series conflict accounting | `proved under explicit Hilbert-series / Euler-characteristic data`. `HilbertSeriesTheory.HilbertSeries`、`HilbertSeries.ext`、`HilbertSeries.ofNatCoefficients`、`HilbertSeries.zero_coeff`、`add_coeff`、`sub_coeff`、`HilbertSeries.shift`、`GradedMonomialConflictRegime`、`GradedMonomialConflictRegime.homogeneousMonomialIdeals_certificate`、`DegreewiseShortExactPackage`、`DegreewiseShortExactPackage.hilbertSeries_additivity`、`DegreewiseShiftedFreePackage`、`DegreewiseShiftedFreePackage.shiftedFree_eq_rank_smul_shift`、`DegreewiseEulerCharacteristicPackage`、`DegreewiseEulerCharacteristicPackage.eulerCharacteristic_eq`、`HilbertSeriesShortExactPackage`、`HilbertSeriesShortExactPackage.additivity_certificate`、`ShiftedFreeHilbertSeriesPackage`、`ShiftedFreeHilbertSeriesPackage.shiftedFree_certificate`、`FiniteComplexEulerCharacteristicPackage`、`FiniteComplexEulerCharacteristicPackage.eulerCharacteristic_certificate`、`HilbertSeriesConflictIdentityPackage`、`HilbertSeriesConflictIdentityPackage.denominatorClearedIdentity_certificate`、`eulerCharacteristic_certificate`、`interferenceSeries`、`interferenceSeries_coeff`、`HilbertSeriesConflictCoefficientIdentityPackage`、`HilbertSeriesConflictCoefficientIdentityPackage.denominatorClearedIdentity_of_coefficients`、`HilbertSeriesConflictCoefficientIdentityPackage.toIdentityPackage`、`HilbertSeriesFiniteWindowConflictAuditPackage`、`HilbertSeriesFiniteWindowConflictAuditPackage.coefficientIdentity_certificate` を持つ。`Formal/AG/Examples/DerivedPart5.lean` 側では `sharedWitnessG5_all_degree_coefficient_identity` と `sharedWitnessG5_denominatorClearedIdentity` が concrete shared-witness G5 identity を全次数で証明し、`sharedWitnessG5CoefficientIdentityPackage` / `sharedWitnessG5IdentityPackage` が package surface を返す。 | Hilbert series は degree-wise coefficient reading として扱い、有理関数表示は主張しない。定理12.2 は selected graded monomial regime と Euler-characteristic package に相対化し、全次数の係数等式から denominator-cleared identity を復元する theorem surface として読む。finite example では全次数 theorem を主 surface とし、有限 degree window は派生 audit として残す。 |
| `V.定義13.1 / 定義13.2 / 定理13.3 / 定理13.4` Well-founded repair | `proved under explicit well-founded repair profile / finite synthesis data`. `WellFoundedRepair.RepairComparisonProfile`、`RepairComparisonProfile.step_decreases_certificate`、`InfiniteRepairSequence`、`no_infinite_repair_sequence`、`SoundRepairStepEvidence`、`SoundRepairStepEvidence.sound_or_certificate`、`SynthesisOutput`、`SoundRepairSynthesisPackage`、`finite_trace_certificate`、`emitsOnlySoundStepsOrNoSolutionCertificate_certificate`、`output_cleared_or_noSolution` を持つ。 | 定理13.3 は selected step relation が well-founded comparison で下降することに相対化する。定理13.4 は finite `List` trace と cleared / no-solution output package に相対化し、solver completeness、global repair optimality、全 law universe 同時改善は主張しない。 |
| `V.R11 finite examples` | `proved examples under explicit certificates / selected audit data`. `Formal/AG/Examples/DerivedPart5.lean` が `Example56TorCalculation`、`Example56TorCalculation.ofPrincipalKernelCalculation`、`Example56TorCalculation.tor1_nonzero`、`Example56DirectTorCalculation`、`Example56DirectTorCalculation.tor1_nonzero`、`toExample56TorCalculation`、`sharedWitness_numeric_residue_path`、`sharedWitness_numeric_u_improves_not_v_nonincreasing`、`sharedWitnessAmbientCoeff`、`sharedWitnessQuotientCoeff`、`sharedWitnessJointCoeff`、`sharedWitnessTorOneCoeff`、`sharedWitnessAmbientHilbertSeries`、`sharedWitnessQuotientHilbertSeries`、`sharedWitnessJointHilbertSeries`、`sharedWitnessTorOneHilbertSeries`、`sharedWitnessConflictAlternatingSeries`、`sharedWitnessHilbertRegime`、`sharedWitnessAmbientCoeff_two`、`sharedWitnessQuotientCoeff_two`、`sharedWitnessJointCoeff_two`、`sharedWitnessTorOneCoeff_three`、`sharedWitnessConflictAlternatingCoeff`、`sharedWitnessConflictAlternatingCoeff_closed`、`sharedWitnessG5_all_degree_coefficient_identity`、`sharedWitnessG5_denominatorClearedIdentity`、`sharedWitnessG5CoefficientIdentityPackage`、`sharedWitnessG5IdentityPackage`、`sharedWitnessG5_window_identity`、`sharedWitnessG5WindowAuditPackage`、`sharedWitnessG5_window_interference_zero`、`smallRepairProfile`、`smallRepair_step_two_one`、`smallRepair_step_one_zero`、`smallRepair_no_infinite_sequence`、`smallRepairClearedSynthesis`、`smallRepairCleared_trace_length`、`smallRepairCleared_output`、`smallRepairNoSolutionSynthesis`、`smallRepairNoSolution_output` を持つ。 | 例5.6 Tor 非零は direct package `Example56DirectTorCalculation` により selected principal kernel quotient calculation から読む。G5 数値例は `I_U=<xy>` / `I_V=<xz>` の concrete coefficient data から全次数係数恒等式と denominator-cleared identity を証明し、degree `0..9` の finite-window audit は全次数 theorem から従う検算 surface として残す。有理関数展開や一般 monomial Hilbert series 計算は主張しない。 |
| `V.R12 final ledger / scan` | `proved final ledger sync`. `rg -n "\b(axiom\|admit\|sorry\|unsafe)\b" Formal/AG Formal/AG.lean` は no match。`Formal/AG.lean` は `Formal.AG.Derived` と `Formal.AG.Examples.DerivedPart5` を import し、`lake build` 対象に入る。 | R12 は台帳・検証の完了確認であり、新しい数学 claim は追加しない。余接複体 `L_{Flat/X}` と `Ext^1` は未割当 future proof obligation のまま維持する。 |
| `IV.定義2.4 DerOb_U` の内部構成 | `future proof obligation` / `unassigned`. PRD-5 R0/R1 では触らず、PRD-5 本文が展開する chart-level Koszul / Tor 構成とは別境界として維持する。 | 余接複体 `L_{Flat/X}` と `Ext^1` の一般形式化は PRD-5 の現在 scope では実装しない。 |

第V部 PRD-5 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `V.R0` | `defined only` |
| `V.定義2.1 / 定義3.1` | `defined only` / `proved accessor` |
| `V.定義2.3 / 原則2.4` | `defined only` / `proved accessor` |
| `V.定義4.1 / 5.1 / 5.2` | `defined only` / `proved accessor` |
| `V.命題5.5` | `proved under explicit Mathlib projective-resolution / Taylor identification data` |
| `V.定理6.1 / 定理7.3` | `proved under explicit selected transversality criterion data` |
| `V.定義8.1-8.4` | `defined only` / `proved accessor` |
| `V.命題9.2` | `proved under explicit principal-resolution kernel quotient / Tor bridge data` |
| `V.定理10.5 / 定理10.6` | `proved under explicit transfer-pairing data` |
| `V.定義11.1` | `defined only` / `proved accessor` |
| `V.定理12.2` | `proved under explicit Hilbert-series / Euler-characteristic data` |
| `V.定理13.3 / 定理13.4` | `proved under explicit well-founded repair profile / finite synthesis data` |
| `V.R11 finite examples` | `proved examples under explicit certificates / selected audit data` |
| `V.R12 final ledger / scan` | `proved final ledger sync` |

## AG版AAT Lean形式化 PRD-6 / 第VI部 Singularity・Monodromy・Stack

PRD-6 は tracking Issue [#2128](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2128)
で管理する。初回実装 Issue [#2129](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2129)
では AC1/R0 と AC2/R1 を対象にし、`Formal/AG/SingularityMonodromyStack` の entrypoint と
architecture stratum / reading parameter を追加した。Issue [#2131](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2131)
では AC3-AC4/R2 を対象にし、cotangent / tangent deformation-obstruction interface と
smooth / singular / normal cone reading を追加した。Issue [#2133](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2133)
では AC5-AC8/R3 を対象にし、singularity theorem、square-zero lifting obstruction、
Kuranishi data / statement、singular boundary、GodObject reading を追加した。Issue [#2135](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2135)
では AC9/R4 を対象にし、operation graph、finite operation path、endpoint equivalence、
operation loop を追加した。Issue [#2137](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2137)
では AC10/R5 を対象にし、finite homotopy generator family、presentation two-complex、
presented architecture fundamental group package、selected-relator quotient universal property を追加した。Issue [#2140](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2140)
では AC11/R6 を対象にし、monodromy action、finite Gauss-Manin system、
monodromy debt predicate、measured square monodromy、AMI weighted-sum data を追加した。Issue [#2142](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2142)
では AC12-AC14/R7 を対象にし、Transport Descent Criterion、Square Monodromy Nonfillability、
Monodromy Debt theorem を selected transport / axis / debt interface に相対化して証明した。Issue [#2144](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2144)
では AC15/R8 を対象にし、Refactor groupoid と Operation-Invariant Galois Correspondence を
selected refactor groupoid / invariant preservation relation に相対化して証明した。Issue [#2146](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2146)
では AC16/R9 を対象にし、ArchitectureStack と AlgebraicArchitectureStack predicate を
selected base / architecture presheaf / explicit descent data に相対化して定義した。Issue [#2148](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2148)
では AC17/R10 を対象にし、`Ess_U(X) = [X^U / Ref_U]` を selected action groupoid /
architecture presheaf / descent predicate に相対化して定義した。Issue [#2150](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2150)
では AC18-AC19/R11 を対象にし、DecompositionStack、gerbe obstruction、banded abelian bridge、
No Canonical Decomposition theorem を explicit selected gerbe soundness interface に相対化して定義・証明した。Issue [#2152](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2152)
では AC20-AC23/R12-R13 を対象にし、Part VI finite witness examples と最終台帳整備、
`Formal/AG` 全体の `axiom` / `admit` / `sorry` / `unsafe` scan を閉じる。PRD 本体の checkbox は prd-loop の
不変条件として編集せず、達成状態は tracking Issue とこの台帳で同期する。

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `VI.R0` Formal/AG/SingularityMonodromyStack entrypoint | `defined only`. `Formal/AG/SingularityMonodromyStack.lean` が `Stratum.lean`、`CotangentInterface.lean`、`SmoothSingular.lean`、`SingularityTheorems.lean`、`Kuranishi.lean`、`OperationCategory.lean`、`OperationHomotopy.lean`、`Monodromy.lean`、`MonodromyTheorems.lean`、`RefactorGalois.lean`、`ArchitectureStack.lean`、`CodebaseEssence.lean`、`DecompositionGerbe.lean` を束ね、`Formal/AG.lean` が `Formal.AG.SingularityMonodromyStack` と `Formal.AG.Examples.SingularityMonodromyStackPart6` を import する。PRD-3 `LawAlgebra`、PRD-4 `Cohomology`、PRD-5 `Derived` の後段 module として build 対象に入る。 | Part VI entrypoint は最終 build 対象に入っている。残る一般理論境界は個別 future proof obligation 行に分離する。 |
| `VI.定義2.1 / 原則2.2` Architecture Stratum and reading parameter | `defined only` / `proved accessor`. `StratumRole`、`StratumReadingParameter`、`StratumReadingParameter.coverageTopology`、`lawUniverse_eq`、`selectedCoeff_eq`、`ArchitectureStratum`、`ArchitectureStratum.Mem`、`mem_iff`、`selectedSubobject_holds`、`locallyClosed_holds`、`decorationCompatible_holds`、`readingCompatible_holds` を持つ。 | stratum は selected carrier / compatibility certificate として置く。一般 stratification theory は主張しない。 |
| `VI.定義3.1 / 定義3.2` Cotangent and tangent interface | `defined only` / `proved accessor`. `CotangentData`、`CotangentData.baseMap_eq`、`TangentData`、`TangentData.zeroObstruction_eq` を持つ。 | selected interface であり、一般余接複体構成、RHom 一般構成、Ext 一般理論は主張しない。 |
| `VI.定義4.1 / 定義5.1 / 定義5.2` Smooth, singular, normal cone reading | `defined only` / `proved under explicit selected effectiveness/soundness interface`. `DeformationObstructionTheory`、`not_liftFill_of_ob_ne_zero`、`liftFill_of_ob_eq_zero`、`USmooth`、`USingular`、`USmooth.obstruction_eq_zero`、`USmooth.liftFill`、`uSmooth_of_all_obstruction_zero`、`uSmooth_iff_all_obstruction_zero`、`not_uSmooth_of_uSingular`、`NormalConeReading`、`NormalConeReading.lawfulLocus_eq_flatU_holds`、`NormalConeReading.obstructionIdealCarrier_eq_I_U_holds`、`StructuralRepairDirection`、`selected_pointsTowardVanishing_holds` を持つ。 | deformation-obstruction theory は selected test / obstruction map / effectiveness / soundness に相対化する。normal cone reading は PRD-3 の `Flat_U` / `I_U` に型レベルで接続する。一般 deformation theory は主張しない。 |
| `VI.定理6.1 / 定理6.2 / 系6.5` Singularity theorem and square-zero obstruction | `proved under explicit selected deformation-obstruction interface`. `FirstOrderObstructionWitness`、`architectureSingularityCriterion`、`SquareZeroExtensionData`、`squareZeroLiftingObstruction`、`lift_of_obstruction_zero`、`liftTorsor_of_obstruction_zero`、`automorphisms_of_obstruction_zero`、`BoundaryObstructionFamily`、`USingularBoundary`、`singularBoundary` を持つ。 | 非零 selected obstruction class から selected singularity / lift failure / singular boundary を読む。H1 一般計算、Ext 一般構成、全 deformation の obstruction は主張しない。 |
| `VI.定義6.3 / 定理候補6.4 / 定義7.1` Kuranishi and GodObject reading | `defined only` / `statement only` / `proved accessor`. `KuranishiData`、`KuranishiLocalModelStatement`、`nonzero_not_lawful_lift`、`GodObject`、`singular_holds`、`multipleLawLociNonTransverse_holds` を持つ。 | Kuranishi Local Model は statement carrier であり一般証明はしない。GodObject は `USingular` と PRD-5 `DerivedNonTransverse` に相対化し、size / line count / dependency count では定義しない。 |
| `VI.定義8.1 / 定義8.2 / 定義9.1 / 定義9.2` Operation category, path, endpoint, loop | `defined only` / `proved path algebra`. `OperationCategoryData`、`SelectedOperation`、`selectedState_eq`、`OperationPath`、`OperationPath.id`、`OperationPath.concat`、`concat_nil`、`nil_concat`、`concat_assoc`、`RefactorEndpointReading`、`refactorEquivalent_refl`、`refactorEquivalent_symm`、`refactorEquivalent_trans`、`preservesSelectedInvariants_holds`、`preservesSelectedEssence_holds`、`EndpointEquivalentPath`、`OperationLoop`、`OperationLoop.identity`、`endpoint_equivalent_holds` を持つ。 | operation path は selected operation graph 上の law-universe certificate 付き dependent finite path。endpoint equivalence から selected invariant / essence preservation が certificate として得られる。形式的逆元から reverse architecture operation の存在は主張しない。 |
| `VI.定義9.3 / 定義9.4 / 定義9.5` Operation homotopy presentation and `pi_1^AAT` | `defined only` / `proved selected quotient universal property`. `HomotopyGeneratorFamily`、`pathCellFintype`、`loopRelatorFintype`、`pathCell_commonEndpoints`、`relator_based_holds`、`PresentationTwoComplex`、`vertices_read_states`、`twoCells_read_generators`、`FormalEdgeStep`、`FreeEdgeWord`、`PresentedArchitectureFundamentalGroup`、`relator_maps_to_identity_holds`、`pathCellRelator_selected_holds`、`loopRelator_selected_holds`、`relator_generated_by_selected_generator_holds`、`quotient_universal_property` を持つ。 | `pi_1^AAT` は selected operation graph、finite homotopy generator family、presentation two-complex、base state に相対化された quotient carrier / group package として扱う。relator は selected path-cell / loop-relator 由来であることを certificate として持つ。未選択の operation、未選択の semantic equivalence、未構成 path は含めない。形式的 inverse edge は reverse architecture operation の存在を主張しない。 |
| `VI.定義10.1 / 定義10.2 / 定義10.3 / 定義10.4 / 定義10.6` Monodromy action, Gauss-Manin, measured square, AMI | `defined only` / `proved accessor`. `MonodromyCoefficientObject`、`CoefficientAutomorphism`、`CoefficientAutomorphism.id`、`CoefficientAutomorphism.comp`、`MonodromyAction`、`Mon_gamma`、`mon_gamma_eq_rho`、`rho_one_holds`、`rho_mul_holds`、`obstructionMonodromy`、`MonodromyDebt`、`monodromyDebt_iff`、`FiniteGaussManinSystem`、`transport_id_holds`、`transport_comp_holds`、`LoopMonodromy`、`loopMonodromy_eq_transport`、`MeasuredSquareMonodromy`、`mu_eq_defect_holds`、`boundaryTransport_eq_monodromy_holds`、`axis_detects_of_mu_zero`、`ArchitecturalMonodromyIndex`、`value_eq_weighted_sum_holds`、`weight_positive_holds` を持つ。 | monodromy は selected representation data が与えられた場合だけ定義される。finite Gauss-Manin は finite object family / selected finite-dimensional fiber / selected linear path transport に相対化する。measured square monodromy は boundary transport が selected `Mon_gamma` であることを certificate として持つ。AMI は selected axis / finite measured square family / positive weight の data であり、measurement verdict や DistanceValue には接続しない。 |
| `VI.定理10.5 / 定理10.7 / 定理11.1` Transport descent, square nonfillability, monodromy debt | `proved under explicit selected transport / axis / debt interface`. `TransportDescentProblem`、`transport_descent_criterion`、`factorsThroughQuotient_of_relationBoundaryZero`、`relationBoundaryZero_of_factorsThroughQuotient`、`SquareMonodromyFillingProblem`、`squareMonodromy_nonfillability`、`HiddenArchitectureDebtReading`、`monodromy_debt_theorem`、`hiddenDebt_of_nonidentity_obstructionMonodromy` を持つ。 | Transport descent は selected square monodromy defects zero と relator-killing condition の同値を detecting-axis package として明示し、R5 quotient universal property で quotient factorization へ接続する。Square nonfillability は selected axis filling が `mu = 0` を要求する場合の refutation。Debt theorem は endpoint equivalence と nonidentity obstruction monodromy を hidden debt predicate へ読む。detecting axis completeness の無条件証明、未選択 square / axis / transport への拡張、measurement verdict は主張しない。 |
| `VI.定義12.1 / 定義12.3 / 定理12.4` Refactor groupoid and operation-invariant Galois | `defined only` / `proved selected operation-invariant Galois connection`. `RefactorGroupoid`、`hom_refactorEquivalent`、`id_refactorEquivalent`、`inv_refactorEquivalent`、`comp_refactorEquivalent`、`RefactorMorphismFamily`、`RefactorSubgroupoid`、`SubGpd`、`RefactorMorphismFamilySubset`、`OperationInvariantGaloisData`、`id_preserves`、`inv_preserves`、`comp_preserves`、`InvFam`、`InvFamSubset`、`Ops`、`Inv`、`OpsSubgpd`、`InvSubgpd`、`SubGpdSubset`、`operationInvariantGaloisCorrespondence`、`operationInvariantGaloisCorrespondence_subgpd`、`subset_ops_of_invFamSubset_inv`、`invFamSubset_inv_of_subset_ops`、`RefactorMorphism`、`OpsSet`、`InvSet`、`operationInvariantGaloisCorrespondence_set`、`operationInvariant_galoisConnection` を持つ。 | Refactor groupoid は selected object / morphism family と groupoid laws の package。Galois theorem は identity / inverse / composition で閉じる selected preservation relation に対して `SubGpd(Ref_U(X))` 上の `G <= Ops(I) iff I <= Inv(G)` を証明し、OrderDual を使って Mathlib `GaloisConnection` へ bridge する。未選択 operation / invariant universe、束同型、完全分類、stack 一般論は主張しない。 |
| `VI.定義13.1 / 定義13.3` Architecture stack and algebraic architecture stack | `defined only` / `proved accessor`. `ArchitectureStackBase`、`ArchitecturePresheaf`、`pullbackObj_eq`、`pullbackIso_holds`、`LocalArchitectureObjects`、`ArchitectureDescentDatum`、`EffectiveArchitectureDescent`、`ArchitectureStack`、`effectiveDescent_holds`、`cocycleCondition_holds`、`AlgebraicArchitectureStackData`、`AlgebraicArchitectureStack`、`representableDiagonal_holds`、`atlasAdmissible_holds`、`obstructionIdealsDescend_holds`、`lawSheavesDescend_holds`、`signatureSheavesDescend_holds`、`structureSheavesDescend_holds` を持つ。 | Architecture stack は selected base / restriction identity and composition / groupoid-valued architecture presheaf / local objects / overlap isomorphisms / cocycle / effective descent predicate として扱う。cocycle と effective descent は selected overlap / triple / local comparison data に相対化する。AlgebraicArchitectureStack は representable diagonal、ArchitectureScheme atlas、selected structure descent の explicit data。一般 algebraic stack theory、stackification、未選択 descent completeness は主張しない。 |
| `VI.定義14.1 / 原則14.2` Codebase essence quotient stack | `defined only` / `proved accessor`. `CodebaseRefactorArrow`、`sourceObject`、`targetObject`、`identity`、`inverse`、`comp`、source / target accessor theorem、`CodebaseEssenceAction` と law / obstruction / signature / structure sheaf compatibility accessor、`CodebaseEssencePresentation` と local iso -> refactor arrow reading、`CodebaseEssenceQuotientStack`、`CodebaseEssence`、`Ess_U` を持つ。 | `Ess_U(X) = [X^U / Ref_U]` は selected refactor action groupoid、architecture presheaf、descent predicate、presentation reading の explicit data として扱う。source text identity や graph isomorphism ではなく selected geometry modulo refactor equivalence であることを certificate として持つ。quotient stack 一般論、stackification、全 codebase semantics の完全性は主張しない。 |
| `VI.定義15.1 / 定義16.1 / 定理16.2` Decomposition stack and gerbe obstruction | `defined only` / `proved under explicit selected gerbe soundness interface`. `DecompositionEquivalenceKind`、`DecompositionGroupoid`、`homKind`、`id_kind_defined`、`inverseHom`、`compHom`、`DecompositionPresheaf`、`Dec_U`、`Equiv`、`restrictObject_eq`、`DecompositionStack`、`overlapCompatible_holds`、`effectiveDescent_holds`、`GerbeObstructionData`、`gerbeClassValue`、`gerbeClass_ne_zero`、`autSheafDefined_holds`、`nonAbelianReading_holds`、`BandedAbelianGerbeBridge`、`representsGerbeClass_holds`、`abelianBridgeOnlyWhenBanded_holds`、`NoCanonicalDecompositionData`、`localDecompositionsExist_holds`、`noCanonicalDecomposition` を持つ。 | `Dec_U(X)` は selected local context ごとの admissible decomposition groupoid-valued stack。gerbe obstruction は abstract pointed non-abelian class と selected nonzero predicate。banded case は PRD-4 conditional `H^2(X,A)` surface に bridge するだけで、non-abelian gerbe cohomology 一般論は主張しない。定理16.2 は explicit soundness `globalCanonicalDecomposition -> gerbeClass = 0` に相対化する。 |
| `VI.R12 finite examples` Part VI finite witness examples | `proved example theorem`. `Formal/AG/Examples/SingularityMonodromyStackPart6.lean` が `SingularBoundaryToyModel`、`verifies_singular_boundary`、`OperationSquareToyModel`、`verifies_square_nonfillability`、`TransportDescentToyModel`、`zero_case_descends`、`nonzero_case_not_descend`、`RefactorGaloisToyModel`、`verifies_galois_connection`、`DecompositionGerbeToyModel`、`verifies_no_canonical_decomposition` を持つ。 | R12 examples は finite selected witness package として、既存 Part VI theorem API を検証する。第VII部 golden examples への calibration や全 concrete codebase extraction は扱わない。 |
| `CotangentComplexGeneralConstruction` | `future proof obligation` / `unassigned` | PRD-6 では `CotangentData` interface の後続実装に留め、一般余接複体構成は証明しない。 |
| `RHomGeneralConstruction` | `future proof obligation` / `unassigned` | PRD-6 では tangent interface の field として扱い、RHom 一般構成は証明しない。 |
| `AlgebraicStackGeneralTheory` | `future proof obligation` / `unassigned` | PRD-6 では ArchitectureStack / AlgebraicArchitectureStack predicate を AAT 側 data として扱い、algebraic stack 一般論は証明しない。 |
| `NonAbelianGerbeCohomologyGeneralTheory` | `future proof obligation` / `unassigned` | PRD-6 では non-abelian gerbe obstruction を abstract class として扱い、一般 non-abelian gerbe cohomology は証明しない。 |

第VI部 PRD-6 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `VI.R0` | `defined only` |
| `VI.定義2.1 / 原則2.2` | `defined only` / `proved accessor` |
| `VI.定義3.1-5.2` | `defined only` / `proved under explicit selected effectiveness/soundness interface` |
| `VI.定理6.1 / 定理6.2 / 系6.5` | `proved under explicit selected deformation-obstruction interface` |
| `VI.定義6.3 / 定理候補6.4 / 定義7.1` | `defined only` / `statement only` / `proved accessor` |
| `VI.定義8.1-9.2` | `defined only` / `proved path algebra` |
| `VI.定義9.3-9.5` | `defined only` / `proved selected quotient universal property` |
| `VI.定義10.1-10.4 / 10.6` | `defined only` / `proved accessor` |
| `VI.定理10.5 / 定理10.7 / 定理11.1` | `proved under explicit selected transport / axis / debt interface` |
| `VI.定義12.1 / 定義12.3 / 定理12.4` | `defined only` / `proved selected operation-invariant Galois connection` |
| `VI.定義13.1 / 定義13.3` | `defined only` / `proved accessor` |
| `VI.定義14.1 / 原則14.2` | `defined only` / `proved accessor` |
| `VI.定義15.1 / 定義16.1 / 定理16.2` | `defined only` / `proved under explicit selected gerbe soundness interface` |
| `VI.R12 finite examples` | `proved example theorem` |

## AG版AAT Lean形式化 PRD-7 / 第VII部 Representation・Periods・Analysis

PRD-7 は tracking Issue [#2157](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2157)
で管理する。初回実装 Issue [#2158](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2158)
では AC1/R0 を対象にし、`Formal/AG/RepresentationAnalysis` の entrypoint と
先行 PRD-3〜6 依存確認 surface を追加した。PRD 本体の checkbox は prd-loop の
不変条件として編集せず、達成状態は tracking Issue とこの台帳で同期する。
Issue [#2162](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2162)
では AC2/R1 を対象にし、`AATSch p`、selected morphism interface、
optional fiber product data、functor-like `AnalyticRepresentation` を追加した。
Issue [#2165](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2165)
では AC3/R2 を対象にし、indexed `RepresentationFamily`、selected structural /
analytic notion package、reflection assumption package、preservation / reflection /
conservative / faithful predicate を追加した。
Issue [#2168](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2168)
では AC4/R3 を対象にし、finite directed graph target、selected graph
representation profile、adjacency / incidence / transition matrix、matrix
representation target / profile を追加した。
Issue [#2171](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2171)
では AC5/R3 を対象にし、dependency-axis graph reading selection、cycle witness
exactness、structural dependency obstruction zero を束ねる assumption package の下で、
命題3.4 Acyclicity Preservation を証明した。
Issue [#2174](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2174)
では AC6/R3 を対象にし、selected counted walk と adjacency matrix powers の reading
contract、acyclic finite graph の card cutoff から `∃ N, A^N = 0` を導く theorem
を追加した。
Issue [#2177](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2177)
では AC7/R4 を対象にし、representation reading、broad period convention、
strict period data、strict obstruction period、period family surface を追加した。
Issue [#2179](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2179)
では AC8/R4 を対象にし、PRD-4 の finite Cech chain / cochain / pairing と
finite poset comparison data を第VII部の strict period surface へ接続した。
Issue [#2181](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2181)
では AC9/R5 を対象にし、同じ graph reading と異なる semantic / effect reading を
持つ有限 witness から Period Separation を証明した。
Issue [#2183](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2183)
では AC10/R6 を対象にし、PRD-1 signature axes / `omegaU` に相対化した
signature / curvature reading、PRD-3 Lawfulness-Ideal Correspondence 下の
zero-curvature / lawful-factorization 補題、および PRD-4 gluing obstruction class /
PRD-5 LawConflict package への selected reading handle を追加した。
Issue [#2186](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2186)
では AC11/R7 を対象にし、metric enrichment data、`DistanceValue`、selected
partial-order interface、measured support / unmeasured support / scalar payload
report を分離する aggregation boundary 補題を追加した。
Issue [#2188](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2188)
では AC12/R8 を対象にし、operation distance、`d_op(A,F)` を読む
flat-candidate cost certificate と selected infimum interface に相対化した
distance to flatness、distance-zero reflection predicate、selected obstruction
measure、finite-support obstruction mass interface を追加した。
Issue [#2190](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2190)
では AC13/R9 を対象にし、AC12 context 上の repair route、shortest /
safest / structural / stable repair profile reading、selected margin reading、
architectural Dehn function interface、selected comparable pair に相対化した
bi-Lipschitz representation profile を追加した。
Issue [#2192](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2192)
では AC14/R9 を対象にし、path length、endpoint distance bound、
margin definition、selected boundary distance triangle inequality、
safe-region boundary separation を明示仮定にした定理12.5 Margin Stability を
証明した。
Issue [#2194](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2194)
では AC15/R9 を対象にし、observation map の selected Lipschitz bound、
filling generator cost / filling cost comparison、および正の Lipschitz 定数に
相対化した定理12.7 Observation Gap Lower Bound を証明した。
Issue [#2196](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2196)
では AC16/R10 を対象にし、PRD-6 の stratum / tangent / normal cone /
lifting failure / monodromy action data を第VII部の analytic reading として束ねる
`SingularityProfile` と `MonodromyIndex` を追加した。
Issue [#2198](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2198)
では AC17/R11 を対象にし、`AnalyticReadingContext`、`CompletenessSpectrum`、
`UDetectingRepresentationFamily` を追加した。
Issue [#2201](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2201)
では AC18/R11 を対象にし、U-detecting representation family と明示
adequacy / exactness / coefficient discipline assumptions の下で定理15.4
Representation Conservativity under Adequacy を証明した。
Issue [#2203](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2203)
では AC19/R12 を対象にし、PRD-1〜7 の tower と reading layer を束ねる
`AATSynthesisAssumptions` / `AATSynthesisPackage` と定理16.1
Algebraic-Geometric AAT Synthesis を追加した。
Issue [#2206](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2206)
では AC20/R13 を対象にし、graph/matrix、period separation、pseudo-circle strict
period、margin stability、observation gap、detecting representation の selected
finite examples を `Formal/AG/Examples/RepresentationAnalysisPart7.lean` に追加した。

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `VII.R0` Formal/AG/RepresentationAnalysis entrypoint | `defined only` / `proved accessor`. `Formal/AG/RepresentationAnalysis.lean` が `Bootstrap.lean`、`AATSch.lean`、`PreservationReflection.lean`、`GraphMatrix.lean`、`Period.lean`、`FiniteHomology.lean`、`PeriodSeparation.lean`、`SignatureCurvature.lean`、`Metric.lean`、`DistanceFlatnessMass.lean`、`RepairMarginDehn.lean`、`AnalyticContext.lean`、`Synthesis.lean` を束ね、`Formal/AG.lean` が `Formal.AG.RepresentationAnalysis` と `Formal.AG.Examples.RepresentationAnalysisPart7` を import する。`UsesArchitectureScheme`、`UsesCoverRelativeCechComplex`、`UsesRepairComparisonProfile`、`UsesArchitectureStratum` が PRD-3 `LawAlgebra`、PRD-4 `Cohomology`、PRD-5 `Derived`、PRD-6 `SingularityMonodromyStack` の concrete Lean 型を参照する。`currentDependencyStatus` と accessor theorem 群は、現時点で先行依存が available であることを保持する。`PartVIINoMeasurementVerdictBoundary` は、第VII部が reading layer であり measurement verdict を導入しない境界を保持する。 | AC1 scaffold と R13 selected examples は build 対象に入った。AC2/R1、AC3/R2、AC4/R3、AC7/R4、AC8/R4、AC9/R5、AC10/R6、AC11/R7、AC12/R8、AC13/R9、AC18/R11、AC19/R12、AC20/R13 は別行で扱う。 |
| `VII.定義2.1` AATSch and AnalyticRepresentation | `defined only` / `proved accessor`. `AATSchReadingParameter` が PRD-3 `ArchitectureScheme` 上の selected scheme morphism interface、identity、composition、Atom label / law / obstruction ideal / signature / interpretation map readings を保持する。`AATSch` は fixed parameter `p` に相対化した decorated scheme、`AATSchMorphism` は selected compatibility certificates を持つ morphism、`AATSchIdentityData` / `AATSchCompositionData` は selected identity / composition data を保持する。`AATSchFiberProductData` は underlying pullback と decoration pullback compatibility が与えられた場合だけ存在する optional surface として置く。`AnalyticRepresentation` は target category interface、object map、morphism map、identity / composition law fields を持つ functor-like data として定義する。 | Mathlib `CategoryTheory.Functor` への本格 bridge は後続 Issue で扱う。 |
| `VII.定義3.1 / 定義4.1-4.3` Representation family and preservation / reflection | `defined only` / `proved accessor`. `RepresentationFamily` は indexed target family と `AnalyticRepresentation` family を束ね、`Read` / `Rep` accessor を持つ。`RepresentationNotions` は selected structural zero / obstruction / iso / morphism equality と analytic zero / obstruction / iso / mapped morphism equality を family に相対化して保持する。`ReflectionAssumptions` は coverage、witness completeness、axis exactness、coefficient discipline を明示し、reflection predicate は `A.Holds` を受ける場合だけ使える。`ZeroPreserving` / `ZeroReflecting`、`ObstructionPreserving` / `ObstructionReflecting`、`IsoPreserving` / `IsoReflecting`、`MorphismEqPreserving` / `MorphismEqReflecting`、`Conservative`、`Faithful` を定義する。 | reflection assumption はこの PRD step では discharge しない。定理15.4 conservativity under adequacy は後続 Issue で扱う。 |
| `VII.定義3.3 / 定義3.5` Graph and Matrix representation | `defined only` / `proved accessor`. `FiniteDirectedGraphTarget` は fixed carrier 上の finite vertex / edge、source / target、selected relation label を保持する。`GraphRepresentationProfile` は selected relation data を graph edge へ写し、`AnalyticRepresentation` へ橋渡しする。`adjacencyMatrix`、`incidenceMatrix`、`transitionMatrix`、`MatrixRepresentationTarget`、`MatrixRepresentationProfile` は matrix reading target を定義し、canonical graph-derived matrix package と accessor theorem を持つ。 | AC4 は定義 surface まで。R13 graph / matrix selected finite examples は別行で実装済み。 |
| `VII.命題3.4` Acyclicity Preservation | `proved`. `DependencyAcyclicityProfile` は dependency-axis graph reading selection、graph cycle から selected cycle obstruction witness への exactness、structural dependency obstruction zero が selected cycle obstruction witness を排除する仮定を束ねる。`DependencyAcyclicityProfile.acyclicityPreservation` は、これらの仮定から `FiniteDirectedGraphTarget.Acyclic (P.graphOf X)` を証明する。 | theorem は片方向 exactness assumption に相対化される。R13 dependency DAG acyclicity example は別行で実装済み。 |
| `VII.命題3.6` Matrix Walk Reading | `proved`. `CountedDirectedWalk` は selected edge multiplicity を保持する length-indexed walk witness を与える。`matrixWalkCount` は selected adjacency relation 上の length-`n` walk count を標準再帰で定義し、`adjacencyMatrixPower_apply_eq_matrixWalkCount` が `(adjacencyMatrixPower G n) i j = matrixWalkCount G n i j` を証明する。`matrixWalkCount_pos_iff_countedDirectedWalk` は positive count と concrete counted walk witness を結ぶ。`CountedDirectedWalk.vertices_nodup_of_acyclic` と `length_lt_card_of_acyclic` により、acyclic graph では `Fintype.card Vertex` cutoff の walk count が 0 になり、`adjacencyMatrixPower_eq_zero_at_card_of_acyclic` と `exists_adjacencyMatrixPower_eq_zero_of_acyclic` が `A^N = 0` と `∃ N, A^N = 0` を導く。`MatrixWalkReadingProfile.matrixWalkReading` は selected count がこの再帰 count と一致する profile の下で matrix power entry が selected count を読むことを証明する。 | R13 matrix walk / nilpotence selected finite examples は別行で実装済み。 |
| `VII.定義5.1-5.3` Period reading and period family | `defined only` / `proved accessor`. `RepresentationFamily.RepresentationReading` は `Read_R(X)` の入口を与え、`BroadPeriodConvention` は broad period alias が明示的 convention の下でだけ使えることを記録する。`StrictPeriodData` は coefficient object、cohomology class、homology model、cycle、additive target、trace / evaluation、boundary / coboundary compatibility を保持し、`strictObstructionPeriod` を selected evaluation として読む。`PeriodFamily` は selected representation readings の family surface と `PeriodSet` を定義する。 | R13 pseudo-circle strict-period data example は別行で実装済み。 |
| `VII.定義5.2A` Finite poset / Cech homology model | `proved under explicit finite Cech data and selected pairing-invariance assumptions`. `FiniteCechStrictPeriodRepresentative` が selected cover-relative Cech complex、finite Cech chain complex、cochain-chain pairing、cohomology class、class-representing cocycle、closed cycle、boundary / coboundary compatibility を束ねる。`FiniteCechBoundary.cech_d_comp_d_eq_zero` と `FiniteCechBoundary.boundary_comp_zero` が PRD-4 の `d²=0` / `∂²=0` accessor を第VII部 surface で再公開する。`toStrictPeriodData` と `toStrictPeriodData_strictObstructionPeriod` が AC7 の `StrictPeriodData` へ接続し、`FiniteCechStrictPeriodRepresentativeCompatibility.strictObstructionPeriod_wellDefined` が cohomology-class representative、cycle-closedness、coefficient / boundary / coboundary compatibility、および selected pairing-invariance package の下で strict period representative well-definedness を証明する。`FinitePosetCechStrictPeriodContext` は PRD-4 `FinitePosetCechComparisonData.generalComplex` と selected finite-poset chain / pairing provenance を使う有限 poset 特化 bridge である。 | theorem は selected finite Cech / finite poset comparison data と明示 compatibility package に相対化される。一般 singular homology、canonical realization、pseudo-circle strict period 計算例はここでは主張しない。 |
| `VII.定理6.1 / 例6.2` Period Separation | `proved under selected finite witness`. `PeriodSeparationReadingFamily` が graph / semantic / effect broad reading を持つ selected reading family を定義し、`RepresentationFamily.toPeriodSeparationReadingFamily` と `RepresentationFamilyPeriodSeparationWitness.periodSeparation` が既存 `RepresentationFamily` の selected graph / semantic / effect indices から Period Separation を読む bridge を与える。`PeriodSeparationExample62` は finite card accessors を持つ `X` と `Y` の同一 graph reading、異なる semantic reading、異なる effect reading を証明し、`PeriodSeparationExample62.periodSeparation_theorem6_1` がこの witness から Period Separation を証明する。 | 定理は selected finite witness に相対化される。任意の graph representation の一般不完全性、全 semantic / effect universe の分離、一般 conservativity 否定は主張しない。 |
| `VII.定義7.1 / 7.2` Signature / Curvature Reading | `defined handles` / `proved under explicit zero-reflecting aggregation and correspondence assumptions`. `SignatureReadingProfile` は PRD-1 `SignatureAxes` から selected-axis reading を定義し、`RequiredSignatureReadingZero` と `RequiredSignatureAxesZero` の同値を証明する。`CurvatureReadingProfile` は PRD-1 `omegaU` を curvature reading として読み、zero curvature と aggregate obstruction valuation zero、および required obstruction values zero の同値を証明する。`SignatureCurvatureLawfulFactorizationContext` は PRD-3 `LawfulnessIdealCorrespondenceAssumptions` を theorem 引数に取り、zero curvature、selected signature reading zero、PRD-1 required signature axes zero、`FactorsThroughLawfulLocus` の対応を証明する。`GluingObstructionCurvatureReading` と `LawConflictCurvatureReading` は PRD-4 gluing obstruction class と PRD-5 LawConflict package への selected reading handle を与える。 | theorem は selected correspondence package と explicit reading certificates に相対化される。一般 cohomology comparison、new Tor computation、任意 curvature scalar の completeness は主張しない。 |
| `VII.定義8.1 / 9.1 / 9.2` Metric AAT and DistanceValue | `defined only` / `proved aggregation boundary`. `DistanceValue` は measured payload、measured zero、unmeasured、unavailable、incomparable、infinite を constructor で分ける enriched value object として定義する。`DistanceValuePartialOrder` は selected partial-order interface を保持する。`DistanceAggregationProfile` と `ScalarDistanceAggregationProfile` は scalar aggregate、measured support、unmeasured support、unmeasured support report、per-axis measured scalar payload を別 field として保持し、`unmeasuredSupport_not_measuredZero` / `not_mem_measuredSupport_of_mem_unmeasuredSupport` / `unmeasuredReport_not_measuredZero` / `measuredScalar_eq_none_of_mem_unmeasuredReport` で unmeasured を zero、measured support、measured scalar payload に潰さないことを証明する。`MetricAAT` は Atom metric、configuration metric、signature metric、operation cost、path length、homotopy filling cost、obstruction measure、representation metric を束ねる metric enrichment surface である。 | metric は reading enrichment であり、lawfulness / flatness / distance-to-flatness / obstruction mass / repair margin を定義しない。一般 measure theory、infimum theory、distance-zero reflection は後続 R8/R9/R11 の明示仮定に残す。 |
| `VII.定義10.1 / 10.2 / 11.1 / 11.2` Distance to Flatness and Obstruction Mass | `defined only` / `proved accessor`. `OperationDistanceProfile` は selected operation path cost / path length / homotopy filling cost に相対化した `d_op(A,B)` reading を持つ。`CostInfimumDomain` と `DistanceToFlatnessProfile` は selected flat candidate `F` の cost が `d_op(A,F)` を読む certificate、selected flat candidate family 上の `dist_flat_U(A)` infimum reading、GLB certificate を持つ。`dist_flat_U(A)=0 -> factorization` は theorem ではなく `DistanceZeroReflectsFactorization` predicate としてだけ定義する。`SelectedObstructionMeasure` は `mu_Ob` / `mu_I` と selected support を保持し、`FiniteSupportObstructionMass` は evaluation point ごとの finite support list、finite sum、finite integral interface、`Mass_U(A)` を保持する。 | 一般 measure theory、canonical infimum theory、距離ゼロからの lawfulness / flatness reflection は主張しない。distance-zero reflection が必要な後続定理では明示 predicate として渡す。 |
| `VII.定義12.1-12.4 / 12.6 / 12.8` Repair route / margin / Dehn / bi-Lipschitz representation | `defined only` / `proved accessor`. `RepairRoute` は AC12 `DistanceFlatnessMassContext` 上の selected flat candidate、operation path、route cost、PRD-3 lawful-locus factorization certificate を保持する。`RepairProfileReading` は shortest / safest / structural / stable repair profile を selected predicate と certificate として保持し、structural は normal-cone reading carrier、stable は cohomology / derived conflict / monodromy-debt control reading carrier を記録する。`MarginProfile` は selected safe region と unsafe boundary までの distance reading、`ArchitecturalDehnProfile` は selected presentation two-complex reading と filling-area bound、`BiLipschitzRepresentationProfile` は selected comparable state pair 上の lower / upper bound を保持する。 | 定理12.5 Margin Stability と定理12.7 Observation Gap Lower Bound は別行で証明済み。global repair optimality、universal Dehn function completeness、全 state pair の metric completeness、measurement verdict は主張しない。 |
| `VII.定理12.5` Margin Stability | `proved under explicit margin assumptions`. `MarginStabilityProfile` は selected margin profile に対して start / endpoint、path length、endpoint distance、margin budget、`M.Margin start = measured marginBudget`、selected boundary distance の Nat reading、start safe、`endpointDistance <= pathLength < marginBudget`、margin lower bound、selected boundary distance triangle inequality、boundary self-distance zero、safe-region / boundary separation を明示仮定として保持する。`endpointDistance_lt_margin` が strict margin bound を合成し、`marginBudget_reads_margin_holds` が margin definition certificate を公開し、`marginStability_no_boundary_crossing` が selected boundary を越えないことを contradiction proof で証明し、`marginStability_endpoint_safe` が endpoint が selected safe region に残ることを証明する。 | theorem は selected margin profile と明示仮定に相対化される。任意 metric 空間の一般三角不等式、global repair success、global safety guarantee、measurement verdict は主張しない。 |
| `VII.定理12.7` Observation Gap Lower Bound | `proved under explicit Lipschitz filling assumptions`. `ObservationGapLowerBoundProfile` は selected paths `P,Q`、pair loop `P . Q^{-1}`、selected filler、observation gap、filling generator cost、filling cost、positive Lipschitz constant、`observationGap <= L * generatorCost`、`generatorCost <= fillCost`、および explicit quotient-style lower-bound predicate を保持する。`observationGap_le_lipschitz_fillCost` が `observationGap <= L * fillCost` を証明し、`observationGap_div_lipschitz_le_fillCost` が selected loop / filler について `observationGap / L <= fillCost` を Nat 除算の床関数 reading として証明する。`quotientLowerBound_certificate` は明示 predicate に相対化して downstream の quotient-style reading を返す。 | theorem は selected Lipschitz / filling assumptions と正の Lipschitz 定数に相対化される。一般 Dehn function completeness、全 filling universe の最適性、任意 observation map の Lipschitz 性、measurement verdict は主張しない。 |
| `VII.定義13.1 / 13.2` SingularityProfile and MonodromyIndex | `defined only` / `proved accessor`. `SingularityProfile` は PRD-6 の `ArchitectureStratum`、`CotangentData`、`TangentData`、`DeformationObstructionTheory`、`NormalConeReading` を parameter に持ち、selected point、非零 obstruction による lifting failure、normal cone 上の derived conflict concentration、repair difficulty reading、measurement verdict reserved carrier を束ねる。`MonodromyIndex` は PRD-6 の `MonodromyAction` と selected loop `gamma` に相対化され、`Mon_gamma`、obstruction / semantic / effect action、period change、loop residue bound、finite `ArchitecturalMonodromyIndex` reading、measurement verdict reserved carrier を束ねる。 | analytic reading layer であり、一般 deformation theory、一般 normal cone construction、全 loop universe の measurement verdict は主張しない。 |
| `VII.定義14.1 / 15.1 / 15.3` AnalyticReadingContext / CompletenessSpectrum / UDetecting | `defined only` / `proved accessor`. `CompletenessSpectrum` は reading / preserving / reflecting / conservative / faithful / complete-for-selected-purpose の selected label を定義する。`UDetectingRepresentationFamily` は selected obstruction class `alpha` について全 selected representation reading が analytic zero なら `WitnessZero_U alpha` を返す package である。`AnalyticReadingContext` は Atom vocabulary、law universe、coverage topology、coefficient sheaf、representation family、distance / obstruction mass profile、selected witness family、selected signature axes、U-detecting package、later theorem 用の adequacy / exactness / coefficient discipline props を束ねる。 | AC17 では adequacy / exactness / discipline を証明済みに昇格せず、定理15.4 は AC18 の別行で証明済み。measurement verdict、全 representation universe の completeness、外部 artifact validation は主張しない。 |
| `VII.定理15.4` Representation Conservativity under Adequacy | `proved under explicit adequacy and witness-exactness assumptions`. `RepresentationConservativityUnderAdequacy` は selected `AnalyticReadingContext` に対し、coverage adequacy、witness exactness、axis exactness、coefficient discipline、`WitnessZero_U alpha -> alpha = zeroClass` を明示 field として持つ。`representation_conservativity_under_adequacy` は全 selected representation reading が analytic zero の selected obstruction class `alpha` について、U-detecting で `WitnessZero_U alpha` を得て、explicit exactness field により `alpha = zeroClass` を証明する。 | theorem は selected obstruction class と明示 assumptions に相対化される。全 representation universe の completeness、任意 obstruction universe の完全検出、measurement verdict、外部 artifact validation は主張しない。 |
| `VII.定理16.1` Algebraic-Geometric AAT Synthesis | `proved theorem package`. `AATSynthesisAssumptions` は `Site.PartIPrerequisites`、`ArchitectureGeometry`、`AATSite`、`RingedAATTopos`、`ArchitectureScheme`、scheme atlas としての `AffineAATChart` family、`LawfulLocus` / `LawfulSectionData`、cover-relative Cech obstruction cohomology、`RepairComparisonProfile`、PRD-6 `ArchitectureStratum`、第VII部 `AnalyticReadingContext` を明示前提として束ねる。`AATSynthesisPackage` は同 tower を theorem package として保持し、`ringedAATTopos_is_scheme_ringedTopos` と `affineAATCharts_are_scheme_charts` が scheme 側 topoi / atlas との coherence を公開する。`AATSynthesisAssumptions.toPackage` と `algebraicGeometricAATSynthesis` が package 構成と selected site、scheme coherence、lawful locus、obstruction cohomology、derived geometry、singularity stack、analytic reading の保持を証明する。 | theorem は構成済み predecessor tower と selected reading context に相対化される。measurement verdict、外部 artifact validation、全 representation universe の completeness は主張しない。 |
| `VII.R13 finite examples` graph/matrix toy model, period separation, pseudo-circle strict period, margin stability, observation gap, detecting representation | `proved selected examples`. `Formal/AG/Examples/RepresentationAnalysisPart7.lean` が `dependencyDAG` / `dependencyDAGMatrix`、`dependencyDAG_walkCount_ab_positive`、`dependencyDAG_matrixWalkReading_ab`、`dependencyDAG_nilpotent_at_card`、`periodSeparation_toy_model`、`pseudoCircleSyncChain`、`pseudoCircleAsyncChain`、`pseudoCircle_sync_async_shared_boundary`、`pseudoCircle_cycle_boundary_zero`、`pseudoCircleStrictPeriodRepresentative`、`pseudoCircle_strictPeriodRepresentative_eq_one`、`pseudoCircle_strictPeriodData_reads_representative`、`marginStability_toy_endpoint_safe`、`marginStability_toy_no_boundary_crossing`、`observationGap_toy_lipschitz_bound`、`observationGap_toy_div_lipschitz_lower_bound`、`observationGap_toy_quotient_certificate`、`toyDetectingFamily`、`toyAnalyticReadingContext`、`detectingRepresentation_toy_syncGap_not_all_zero`、`detectingRepresentation_toy_semanticGap_not_all_zero`、`detectingRepresentation_toy_all_zero_imp_zero`、`detectingRepresentation_toy_zero_conservative` を持つ。 | examples は selected finite witness surfaces であり、一般 graph/matrix completeness、一般 singular homology realization、measurement verdict、外部 artifact validation は主張しない。 |

第VII部 PRD-7 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `VII.R0` | `defined only` / `proved accessor` |
| `VII.定義2.1` `AATSch p` / `AnalyticRepresentation` | `defined only` / `proved accessor` |
| `VII.定義3.1 / 4.1-4.3` representation family and preservation / reflection | `defined only` / `proved accessor` |
| `VII.定義3.3 / 3.5` graph representation and matrix representation | `defined only` / `proved accessor` |
| `VII.命題3.4` Acyclicity Preservation | `proved` |
| `VII.命題3.6` Matrix Walk Reading | `proved` |
| `VII.定義5.1-5.3` broad / strict period and period family | `defined only` / `proved accessor` |
| `VII.定義5.2A` finite poset / Cech homology model | `proved under explicit finite Cech data and selected pairing-invariance assumptions` |
| `VII.定理6.1 / 例6.2` Period Separation | `proved under selected finite witness` |
| `VII.定義7.1 / 7.2` signature / curvature reading | `defined handles` / `proved under explicit zero-reflecting aggregation and correspondence assumptions` |
| `VII.定義8.1 / 9.1 / 9.2` Metric AAT and DistanceValue | `defined only` / `proved aggregation boundary` |
| `VII.定義10.1-11.2` operation distance / distance to flatness / selected obstruction measure / obstruction mass | `defined only` / `proved accessor` |
| `VII.定義12.1-12.4 / 12.6 / 12.8` repair route / repair profiles / margin / Dehn / bi-Lipschitz representation | `defined only` / `proved accessor` |
| `VII.定理12.5` Margin Stability | `proved under explicit margin assumptions` |
| `VII.定理12.7` Observation Gap Lower Bound | `proved under explicit Lipschitz filling assumptions` |
| `VII.定義13.1 / 13.2` SingularityProfile and MonodromyIndex | `defined only` / `proved accessor` |
| `VII.定義14.1 / 15.1 / 15.3` analytic context / completeness spectrum / U-detecting representation family | `defined only` / `proved accessor` |
| `VII.定理15.4` Representation Conservativity under Adequacy | `proved under explicit adequacy and witness-exactness assumptions` |
| `VII.定理16.1` Algebraic-Geometric AAT Synthesis | `proved theorem package` |
| `VII.R13 finite examples` graph/matrix toy model, pseudo-circle period, margin, observation gap, detecting representation, and golden-example packaging beyond the AC9 selected period-separation witness | `proved selected examples` |
| `GeneralSingularHomologyRealization` | `future proof obligation` / explicit non-goal for PRD-7 |
| `GeneralMeasureTheoryForObstructionMass` | `future proof obligation` / explicit non-goal for PRD-7 |
| `CompleteMetricReflectionFromDistanceZero` | `future proof obligation` / explicit non-goal for PRD-7 |

## AAT Algebraic-Geometric Part VIII Measurement Theory Lean status

Tracking Issue: [#2210](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2210).
Initial implementation Issue: [#2211](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2211).

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `VIII.R0` Formal/AG/Measurement entrypoint | `defined only` / `proved accessor`. `Formal/AG/Measurement.lean` が `Bootstrap.lean`、`Profile.lean`、`Verdict.lean`、`FiniteRegime.lean`、`Computability.lean`、`SquareFreeRepair.lean`、`Stability.lean`、`RefactorTransport.lean`、`CellularLaplacian.lean`、`Hodge.lean`、`LawConflict.lean`、`SupportTransfer.lean`、`Packet.lean`、`GAGA.lean`、`Examples.lean` を束ね、`Formal/AG.lean` が `Formal.AG.Measurement` を import する。`UsesAATSite`、`UsesArchitectureScheme`、`UsesCoverRelativeCechComplex`、`UsesRepairComparisonProfile`、`UsesArchitectureStratum`、`UsesAnalyticReadingContext` が PRD-2〜7 の concrete Lean 型を参照する。`currentDependencyStatus` と accessor theorem 群は、現時点で先行依存が available であることを保持する。 | R11 finite examples は selected fixture として build 対象に入った。 |
| `VIII.定義2.1 / R1` Measurement Profile and Measured_M | `defined only` / `proved accessor`. `MeasurementProfile` が selected site、cover、coefficient、effective interface、obstruction object、law universe、witness variables、obstruction ideal、representation family、domain、certificate、method、scope、zero / nonzero / undecided / not-computed predicates を profile-relative fields として保持する。`MeasurementProfile.Measured_M` は `InScope`、selected method、certificate reference を持つ bounded predicate surface であり、`measured_inScope`、`measured_method`、`measured_certificate` が accessor として存在する。 | `Zero` と `NonZero` が補集合であることは仮定しない。 |
| `VIII.定義3.1 / 原則3.2 / 定義3.3 / R1` Measurement Verdict discipline | `defined only` / `proved constructor disjointness`. `MeasurementVerdict` が `measured_zero`、`measured_nonzero`、`unmeasured`、`unknown`、`not_computed` を依存 payload 付き constructor として分離する。`VerdictData`、`StructuralVerdict`、`AnalyticReading` は structural verdict と analytic reading を別型として保持する。`MeasurementVerdict.unmeasured_ne_measured_zero`、`unknown_ne_measured_nonzero`、`not_computed_ne_unmeasured` が constructor disjointness を sorry なしで証明する。 | analytic value から structural verdict への暗黙変換は置かない。unmeasured を zero、unknown を nonzero として読む theorem は置かない。 |
| `VIII.定義4.1 / R2` Finite Measurement Regime and EffCoeff | `defined only` / `proved accessor`. `Formal/AG/Measurement/FiniteRegime.lean` が `EffCoeff` と `FiniteMeasurementRegime` を追加し、kernel / image / quotient / ideal-membership / finite presentation / resolution の selected object と certificate、および finite site、finite cover、effective coefficient、explicit restriction maps、finite witnesses、finitely generated obstruction ideal、selected finite resolutions、zero / nonzero predicate certificate fields を保持する。`FiniteMeasurementRegime.finiteSite_holds`、`finiteCover_holds`、`effectiveCoefficient_holds`、`finiteWitnessVariables_holds`、`selectedFiniteResolutions_holds` が accessor として存在する。 | 任意の係数圏の決定可能性や algorithm completeness は主張しない。 |
| `VIII.定理4.2 / R2` Finite AAT Computability | `proved theorem package construction`. `Formal/AG/Measurement/Computability.lean` が `FiniteCechComplexRepresentation`、`FiniteCocycleRepresentative`、`FiniteVerdictComputationObject`、`FiniteSquareFreeObstructionIdeal`、`FiniteStanleyReisnerComplex`、`FiniteMonomialTorComplex`、`FiniteConflictSupport`、`FiniteAATComputability`、`finiteAATComputabilityPackage`、`finiteAATComputability` を追加し、selected invariants が finite linear algebra / finitely presented module / finite combinatorics / finite resolution reduction object へ落ちる theorem package を構成する。 | theorem は selected finite regime と supplied finite objects に相対化される。Scarf / arbitrary minimal resolution、新規 Tor algorithm、全 coefficient universe の計算可能性は主張しない。 |
| `VIII.定義5.1 / 定理5.2 / 定義5.4 / 定理候補5.5 / R3` Square-Free Repair and Alexander Dual | `defined only` / `proved theorem package construction` / `theorem candidate statement-only`. `Formal/AG/Measurement/SquareFreeRepair.lean` が `UsesSquareFreeWitnessRegime`、`SquareFreeRepairRegime`、`AlexanderDualComplex`、`MinimalVertexCover`、`MinimalWitnessHittingSet`、`MinimalRepairHittingSet`、`StanleyReisnerAlexanderDualRepair`、`stanleyReisnerAlexanderDualRepairPackage`、`stanleyReisner_alexanderDual_repair`、`DiscreteMorseRepairReading`、`MorseLowerBoundForStructuralRepairCandidate` を追加する。`SquareFreeRepairRegime` は `sourceWitnessRegime : UsesSquareFreeWitnessRegime M.WitnessVariables` と profile witness lift / source-reading certificate を持ち、PRD-3 square-free witness regime を measurement profile に持ち上げる。定理5.2 package は obstruction ideal / Stanley-Reisner ideal、minimal generators / minimal forbidden supports、minimal vertex covers / witness hitting sets、Alexander dual generators / minimal repair hitting sets の selected certificate を保持する。 | minimal repair hitting set は combinatorial target であり actual architecture repair operation semantics ではない。Morse lower bound は operation semantics compatibility / legality / side-effect profile を仮定に持つ candidate statement に留める。 |
| `VIII.定義6.1 / 定義6.2 / 定理候補6.3 / 定理候補6.5 / R4` Witness Perturbation and Stability Candidates | `defined only` / `proved accessor` / `theorem candidate statement-only`. `Formal/AG/Measurement/Stability.lean` が `witnessSymmetricDifferenceCardinality`、`WitnessPerturbationProfile`、`WitnessPerturbationProfile.symmetricDifferenceCardinality`、`WitnessPerturbationProfile.d_wit_eq_symmetricDifferenceCardinality_holds`、`WitnessUpdateKind`、`FiniteComplexUpdateReading`、`PersistenceProfile`、`ZigzagArrowDirection`、`ZigzagArrow`、`ZigzagProfile`、`FiniteCechStabilityCandidate`、`MonotoneWitnessStabilityCandidate`、`StabilityMeasurementBoundary`、`StabilityMeasurementBoundary.noCertifiedStableMeasurementWithoutTheorem_holds` を追加する。`d_wit` は finite forbidden-support family の symmetric-difference cardinality として certificate つきで保持され、single update / face insertion / face deletion / collapse / anticollapse は finite complex update data として読む。定理候補6.3 / 6.5 は Lipschitz / bottleneck bound の Prop 文形だけを保持する。 | persistence / zigzag / monotone witness stability は証明しない。candidate stability statement や barcode reading を certified stable measurement verdict へ自動昇格しない。 |
| `VIII.定義7.1 / 定義7.2 / 定理7.3 / R5` Refactor Transport and Zero Invariance | `defined only` / `proved theorem package construction`. `Formal/AG/Measurement/RefactorTransport.lean` が `RefactorMorphism`、`RefactorMorphism.lawCompatible_holds`、`coefficientCompatible_holds`、`PullbackObstructionClass`、`PullbackObstructionClass.cechPullbackReading_holds`、`pushforwardRequiresExtraStructure_holds`、`RefactorEquivalenceAssumptions`、`RefactorInvarianceUnderEquivalence`、`RefactorInvarianceUnderEquivalence.zero_iff_pullback_zero`、`source_zero_of_target_zero`、`target_zero_of_source_zero`、`refactorInvarianceUnderEquivalencePackage`、`refactorInvarianceUnderEquivalence` を追加する。定理7.3 package は selected finite site equivalence、ringed ambient iso、coefficient iso、law ideal pullback iso、witness / axis preservation に相対化された `zeroPreserved` / `zeroReflected` law から、target obstruction class と exact pullback source class の `Zero` predicate equivalence を構成する。 | syntax-level refactor、external rewrite、任意 profile morphism の preservation は主張しない。pushforward は finite map / trace map / aggregation rule などの追加構造がある場合だけの boundary として残す。 |
| `VIII.定義8.1-8.3 / 定理8.5 / 定理8.6 / 系8.7 / 定義8.8 / 定義8.9 / 定理候補8.10 / R6` Cellular Laplacian, Hodge, and Harmonic Debt | `defined only` / `proved theorem package construction` / `theorem candidate statement-only`. `Formal/AG/Measurement/CellularLaplacian.lean` が `CellularMeasurementModel`、`CellularMeasurementModel.finiteCells_holds`、`finiteDimensionalCochains_holds`、`differentialSquaresZero_holds`、`SheafLaplacianReading`、`SheafLaplacianReading.laplacian_eq_formula_holds`、`DistanceToFlatnessReading`、`DistanceToFlatnessReading.residual_eq_norm_d0_holds`、`distanceZeroDoesNotImplyLawful_holds` を追加する。`Formal/AG/Measurement/Hodge.lean` が `FiniteHodgeDecompositionData`、`FiniteHodgeDecomposition`、`FiniteHodgeDecomposition.kernel_reads_laplacian_holds_of_package`、`decomposition_maps_read_cochain_holds_of_package`、`decomposition_holds_of_package`、`harmonic_cohomology_holds_of_package`、`cohomology_equiv_harmonic_holds_of_package`、`finiteHodgeDecompositionPackage`、`finiteHodgeDecomposition`、`HarmonicDebtMinimalityData`、`HarmonicDebtMinimality`、`HarmonicDebtMinimality.minimum_reads_correction_residual_holds_of_package`、`harmonic_debt_eq_harmonic_norm_holds_of_package`、`minimization_holds_of_package`、`harmonicDebtMinimalityPackage`、`harmonicDebtMinimality`、`EssentialRepairLowerBoundData`、`EssentialRepairLowerBound`、`EssentialRepairLowerBound.lower_bound_reads_harmonic_debt_over_L_holds_of_package`、`lowerBound_holds_of_package`、`essentialRepairLowerBoundPackage`、`essentialRepairLowerBound`、`SpectralGapReading`、`CurvatureTransferSpectrum`、`SpectralHotspotReadingCandidate` を追加する。Hodge / harmonic debt / repair lower bound は explicit finite inner-product cochain model data に相対化された theorem package construction として扱う。 | 一般 Hilbert complex、infinite-dimensional analytic theory、near-flatness から lawfulness、Perron-Frobenius / spectral hotspot theorem は主張しない。 |
| `VIII.定義9.1 / 定理候補9.2 / R7` Common Ambient Pair and LawConflict Measurement | `defined only` / `proved accessor` / `theorem candidate statement-only`. `Formal/AG/Measurement/LawConflict.lean` が `CommonAmbientPair`、`CommonAmbientPair.commonRingedSite_holds`、`lawIdealsInCommonAmbient_holds`、`coefficientsCompatible_holds`、`noComparisonWithoutCommonAmbient_holds`、`LawConflictMeasurement`、`LawConflictMeasurement.lawConflictTorReading_holds`、`selectedClassSupportReading_holds`、`commonAmbientRequired_holds`、`FlatBaseChangeCandidate`、`FlatBaseChangeCandidate.affineBaseChangeStatement_shape_holds`、`sheafBaseChangeStatement_shape_holds`、`candidateOnly_holds` を追加する。LawConflict は selected common ambient pair と coefficient compatibility に相対化された Tor reading として扱い、flat base change は affine / sheaf-ringing-site の statement shape だけを保持する theorem candidate として扱う。 | 異なる topology / coefficient ring / ambient scheme の law ideals を comparison morphism なしに比較しない。一般 Tor base-change theorem、non-flat base change preservation、support pullback 未指定での conflict support comparison は主張しない。 |
| `VIII.定義10.1 / 定義10.2 / 定理10.3 / 定理候補10.4 / 定義10.6 / 定理候補10.7 / R8` Support-Localized Transfer and Wasserstein Cost | `defined only` / `proved theorem package construction` / `theorem candidate statement-only`. `Formal/AG/Measurement/SupportTransfer.lean` が `SupportLocalizedRepairPath`、`SupportLocalizedRepairPath.pathImageIntersectsSupport_holds`、`directionSupportIntersectsConflict_holds`、`TransferMeasurementPairing`、`TransferMeasurementPairing.selectedResidue_eq_pairing_holds`、`detectingPairingRequiredForNecessity_holds`、`SupportLocalizedTransfer`、`SupportLocalizedTransfer.nontrivial_transferred_residue_of_pairing`、`supportLocalizedTransferPackage`、`supportLocalizedTransfer`、`TransferLowerBoundCandidate`、`WassersteinTransferCostReading`、`WassersteinTransferCostReading.finiteSupportGraph_holds`、`costReadsFinitePlan_holds`、`WassersteinTransferLowerBoundCandidate`、`WassersteinTransferLowerBoundCandidate.lowerBoundStatement_shape_holds`、`candidateOnly_holds` を追加する。定理10.3 は selected nontrivial pairing residue から selected repair direction の nontrivial transferred residue を返す one-way sufficient-condition theorem package として構成する。 | transfer theorem は necessary condition ではなく、detecting pairing は追加仮定に残す。定理候補10.4 / 10.7 は statement-only であり、一般 optimal transport theory、一般 Wasserstein lower-bound theorem、finite graph 外の measure theory は主張しない。 |
| `VIII.定義11.1 / 原則11.2 / 定理12.1 / R9` Measurement Packet and Finite Measurement Synthesis | `defined only` / `proved theorem package construction`. `Formal/AG/Measurement/Packet.lean` が `ComputedInvariants`、`ComputedInvariants.finiteInvariantHandles_holds`、`AnalyticReadings`、`AnalyticReadings.analyticReadingsSeparatedFromVerdict_holds`、`MeasurementAssumptions`、`MeasurementNonConclusions`、`MeasurementNonConclusions.candidateDependentReadingsSeparated_holds`、`MeasurementPacketData`、`boundedMeasurementStatement`、`boundedMeasurementStatement_cert`、`MeasurementPacket`、`MeasurementPacket.boundedMathematicalMeasurement_holds`、`certifiedSeparatedFromCandidate_holds`、`measurementPacketOfData`、`FiniteMeasurementSynthesis`、`FiniteMeasurementSynthesis.bounded_packet_holds_of_package`、`certified_candidate_separation_holds_of_package`、`finiteMeasurementSynthesisPackage`、`finiteMeasurementSynthesis` を追加する。raw packet data は structural verdict、computed invariants、analytic readings、certified readings、candidate interfaces、conditional readings、assumptions、non-conclusions を分離して保持し、定理12.1 は explicit finite assumptions と separation certificates から bounded packet を構成する theorem package として扱う。 | packet は unselected laws、unmeasured support、unprovided coefficient data、undecided predicates を結論しない。candidate-dependent readings は certified verdict に昇格しない。 |
| `VIII.定理12.3 / 原則12.4 / R10` AAT-GAGA Finite Measurement Comparison | `defined only` / `proved theorem package construction`. `Formal/AG/Measurement/GAGA.lean` が `AATGAGACertifiedFields`、`AATGAGACertifiedFields.hodgeComparisonCertified_holds`、`derivedConflictAccountingCertified_holds`、`AATGAGACandidateInterfaces`、`AATGAGACandidateInterfaces.candidateInterfacesSeparatedFromCertified_holds`、`AATGAGAComparisonAssumptions`、`AATGAGABoundary`、`AATGAGABoundary.noExternalDataSourceFidelity_holds`、`candidateDependentFieldsNotCertified_holds`、`AATGAGAComparisonData`、`aatGAGAComparisonStatement`、`aatGAGAComparisonStatement_cert`、`AATGAGAComparisonPacket`、`AATGAGAComparisonPacket.finiteProfileComparison_holds`、`certifiedCandidateSeparation_holds`、`aatGAGAComparisonPacketOfData`、`AATGAGAFiniteMeasurementComparison`、`AATGAGAFiniteMeasurementComparison.finite_profile_comparison_holds_of_package`、`candidate_interfaces_separated_holds_of_package`、`aatGAGAFiniteMeasurementComparisonPackage`、`aatGAGAFiniteMeasurementComparison` を追加する。certified fields と candidate-interface fields を分離し、定理12.3 は raw comparison data から finite measurement regime / finite cover / inner-product coefficient sheaf / cellular cochain model / square-free regime / common ambient / stability distance と comparison maps、および certified fields 全体と boundary certificates に相対化された finite-profile comparison packet を構成する theorem package として扱う。 | `GAGA` は external data source、external procedure、任意 law universe、外部忠実性を主張しない。candidate-dependent fields は certified conclusion に昇格しない。 |
| `VIII.R11 finite examples` | `proved selected finite examples`. `Formal/AG/Measurement/Examples.lean` が `PseudoCircleMeasurementDomain`、`SquareFreeSupportVertex`、`SquareFreeRepairTarget`、`TinyMeasurementSite`、`LowDegreeCochain`、`TransferResidueFlag`、`pseudoCircleMeasurementProfile`、`pseudoCircleBoundaryCocycleVerdict`、`pseudoCircle_unmeasuredAxis_not_zero`、`squareFreeHittingSet_q_hits_forbiddenSupports`、`squareFreeHittingSet_pr_hits_forbiddenSupports`、`squareFreeRepairRegime`、`squareFreeMinimalRepairHittingSets`、`squareFreeRepairExamplePackage`、`squareFree_singletonQ_minimalRepairHittingSet`、`squareFree_pairPR_minimalRepairHittingSet`、`tinyFiniteMeasurementRegime`、`finiteComputabilityExamplePackage`、`finiteComputabilityExample_verified`、`refactorInvarianceExamplePackage`、`lowDegreeHodgePackage`、`lowDegreeHarmonicDebtPackage`、`supportTransferExamplePackage`、`measurementPacketExampleSynthesis`、`gagaComparisonExamplePackage`、`RefactorInvarianceFiniteExample`、`CellularHodgeFiniteExample`、`SupportLocalizedTransferFiniteExample`、`MeasurementPacketGAGAFiniteExample`、`measurementPacketGAGAExample_certifiedCandidateSeparated`、`PartVIIIFiniteExampleSuite`、`PartVIIIFiniteExampleSuite.CoversR11`、`partVIIIFiniteExampleSuite_complete` を追加する。R11(a)-(g) を selected finite fixture として検証し、R11(b)-(g) は既存 Part VIII theorem package を concrete instance として持つ。`{q}` と `{p,r}` が selected minimal repair hitting set であることを証明し、Part IX static measurement fixtures として再利用できる aggregate suite を保持する。 | finite examples は selected fixture surface であり、外部 extraction、actual repair operation semantics、一般 Hodge theory、一般 transfer necessary condition、外部 GAGA fidelity は主張しない。 |

第VIII部 PRD-8 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `VIII.R0` | `defined only` / `proved accessor` |
| `VIII.定義2.1 / R1` Measurement Profile and `Measured_M` | `defined only` / `proved accessor` |
| `VIII.定義3.1 / 原則3.2 / 定義3.3 / R1` Measurement Verdict discipline | `defined only` / `proved constructor disjointness` |
| `VIII.定義4.1 / R2` Finite Measurement Regime and `EffCoeff` | `defined only` / `proved accessor` |
| `VIII.定理4.2` Finite AAT Computability | `proved theorem package construction` |
| `VIII.定義5.1 / 定理5.2 / 定義5.4 / 定理候補5.5 / R3` Square-Free Repair / Alexander Dual / Discrete Morse | `defined only` / `proved theorem package construction` / `theorem candidate statement-only` |
| `VIII.定義6.1 / 定義6.2 / 定理候補6.3 / 定理候補6.5 / R4` Witness Perturbation / Persistence / Stability Candidates | `defined only` / `proved accessor` / `theorem candidate statement-only` |
| `VIII.定義7.1 / 定義7.2 / 定理7.3 / R5` Refactor Morphism / Pullback / Invariance | `defined only` / `proved theorem package construction` |
| `VIII.定義8.1-8.3 / 定理8.5 / 定理8.6 / 系8.7 / 定義8.8 / 定義8.9 / 定理候補8.10 / R6` Cellular Laplacian / Hodge / Harmonic Debt | `defined only` / `proved theorem package construction` / `theorem candidate statement-only` |
| `VIII.定義9.1 / 定理候補9.2 / R7` Common Ambient Pair / LawConflict Measurement / Flat Base Change Candidate | `defined only` / `proved accessor` / `theorem candidate statement-only` |
| `VIII.定義10.1 / 定義10.2 / 定理10.3 / 定理候補10.4 / 定義10.6 / 定理候補10.7 / R8` Support-Localized Transfer / Wasserstein Cost | `defined only` / `proved theorem package construction` / `theorem candidate statement-only` |
| `VIII.定義11.1 / 原則11.2 / 定理12.1 / R9` Measurement Packet / Finite Measurement Synthesis | `defined only` / `proved theorem package construction` |
| `VIII.定理12.3 / 原則12.4 / R10` AAT-GAGA Finite Measurement Comparison | `defined only` / `proved theorem package construction` |
| `VIII.R11 finite examples` pseudo-circle measurement, square-free hitting set, finite computability, refactor invariance, cellular Hodge, support transfer, packet / GAGA separation | `proved selected finite examples` |
| `GeneralPersistenceStability` / `GeneralZigzagStability` / `GeneralFlatBaseChangeForLawConflict` / `GeneralPerronFrobeniusHotspot` / `GeneralOptimalTransportTheory` / `AnalyticSmallnessImpliesLawfulness` | `future proof obligation` / explicit non-goal for PRD-8 |

## AAT Algebraic-Geometric Part IX Evolution Geometry Lean status

Tracking Issue: [#2280](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2280).
Initial implementation Issue: [#2281](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2281).
R2 temporal site / coefficient Issue: [#2289](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2289).
R3 state transition / temporal law Issue: [#2295](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2295).
R4 temporal mismatch / class Issue: [#2303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2303).
R5 replay descent / temporal descent criterion Issue: [#2307](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2307).
R6 evolution functional / dissipative policy Issue: [#2311](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2311).
R7 finite dissipation stopping Issue: [#2316](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2316).
R8 AAT Lyapunov reading Issue: [#2320](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2320).
R9 force / integrability obstruction candidate Issue: [#2322](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2322).
R10 finite temporal examples Issue: [#2324](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2324).
R11 final ledger / no-sorry scan Issue: [#2326](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2326).

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `IX.R0` Formal/AG/Evolution entrypoint | `defined only` / `proved accessor`. `Formal/AG/Evolution.lean` が `Bootstrap.lean`、`TraceCategory.lean`、`Profile.lean`、`TemporalProductSite.lean`、`TemporalCoefficient.lean`、`StateTransition.lean`、`TemporalLaw.lean`、`TemporalObstruction.lean`、`ReplayDescent.lean`、`Dissipation.lean`、`FiniteDissipation.lean`、`Lyapunov.lean`、`Force.lean` を束ね、`Formal/AG.lean` が `Formal.AG.Evolution` と `Formal.AG.Examples.EvolutionPart9` を import する。`UsesAATSite`、`UsesArchitectureScheme`、`UsesCoverRelativeCechComplex`、`UsesRepairComparisonProfile`、`UsesArchitectureStratum`、`UsesAnalyticReadingContext`、`UsesMeasurementProfile` が PRD-2〜8 の concrete Lean 型を参照する。`currentDependencyStatus` と accessor theorem 群は、現時点で先行依存が available であることを保持する。 | finite examples は R10 selected fixture として別行で扱う。 |
| `IX.§1 / 定義2.1 / R1` EvolutionProfile / TraceCategory / EvolutionGeometry | `defined only` / `proved accessor`. `TraceCategory` が selected trace object、selected transition、identity、composition、identity law、associativity law を保持する。`TraceCategory.FiniteRegime` が finite object / hom と selected arrow family の identity / composition closure を保持する。`EvolutionProfile` が base geometry、measurement profile、selected trace、selected operations、selected state family、selected temporal laws、selected coefficient profile を束ねる。`EvolutionGeometry` が selected trace から base geometry への functor-like surface を持ち、`map_identity` と `map_composition` が accessor theorem として存在する。 | 未選択 event、外部 runtime、実時間、任意 future path への zero / lawful / safe / forecast は主張しない。 |
| `IX.§3 / R2` TemporalSite / TemporalCover / TempCoeff_A | `defined only` / `proved accessor`. `TemporalSite` が selected finite trace regime と selected finite-poset AAT site regime を束ね、`TemporalSite.Point` を trace/context pair として読み、`IncidenceLeg` / `idLeg` / `compLeg` で selected product-incidence leg を保持する。`TemporalCover` が trace arrow と architecture context order witness を持ち、`TemporalCoverToSiteCover`、`TemporalCechBridge`、`FinitePosetTemporalCechBridge` が temporal cover を PRD-4 cover-relative Čech complex と PRD-2 finite-poset comparison package に接続する。`TemporalCoefficient` / `TempCoeff_A` が selected coefficient profile、obstruction sheaf、pointwise additive temporal fiber、incidence leg restriction map、identity / composition law、obstruction sheaf section comparisonを保持し、`FiniteTemporalCoefficientRegime` が PRD-8 finite measurement regime / effective coefficient interface に接続する。 | Temporal site は selected finite product/incidence surface であり、一般 product-site theory や外部 runtime time を主張しない。 |
| `IX.§3 / R3` StateTransitionPresheaf / TemporalLaw | `defined only` / `proved accessor`. `StateTransitionPresheaf` が selected temporal point 上の state carrier、local transition category surface、context restriction、selected trace transport、identity / composition functoriality、context/trace commutative squareを保持する。`StateTransitionSheaf` が temporal cover 上の selected descent predicate と overlap compatibility predicate を保持する。`TemporalLawKind` と `TemporalLaw` が selected `St_A` と `Tr_E` に相対化された law vocabulary、incidence witness、state equation、transition predicate、descent predicateを保持する。 | 一般 sheafification、外部 runtime trace、実時間、任意 future path forecast は主張しない。 |
| `IX.§3.4 / R4` TemporalMismatch / TemporalCocycle / TemporalClass | `defined only` / `proved accessor`. `TemporalMismatch` が selected temporal law、`TempCoeff_A`、temporal Čech bridge に相対化された cochain package を保持する。`TemporalCocycle` が selected mismatch の zero-differential witness を保持し、PRD-4 `CechCocycle` subtype へ読む accessor を持つ。`TemporalClass` が mismatch cocycle から selected cover-relative cohomology class を読む package を保持する。`ConcreteTemporalObstructionClass` は selected class と explicit nonzero predicate を引数に取る。 | 非零 cohomology group だけから concrete temporal failure は主張しない。 |
| `IX.§4 / R5` ReplayDescentData / Temporal Descent Criterion | `defined only` / `proved theorem package`. `ReplayDescentData` が temporal cover と selected trace arrow 上の local replay map、degree-one mismatch cochain、law support certificate を保持し、`ReplayDescentData.mismatch` が R4 `TemporalMismatch` へ読む。`ReplayMismatchCocycle` が zero-differential witness を保持し、`EffectiveTemporalAdjustment` が zero-cochain correction と adjusted mismatch equation `m(adjust(c,r)) = m(r) - d c` を保持する。`TemporalDescentCriterion.temporal_descent_criterion` は mismatch cocycle、selected temporal class、`temporalClass.cohomologyClass = r.zeroMismatchClass`、effective adjustment、`adjustment.adjustedData` の compatibility から `Nonempty r.GlobalReplayTransition` を返す。 | Temporal Descent Criterion は片方向であり、global replay から class vanishing への逆向きは主張しない。 |
| `IX.§5.1-5.2 / R6` EvolutionFunctional / DissipativePolicy / SelectedEvolutionPath | `defined only` / `proved accessor`. `EvolutionFunctional` が selected measurement profile に相対化された ordered value reading `Phi_M` と representative reading predicates を保持する。`DissipativePolicy` が selected step universe、source / target temporal states、selected incidence leg、selected step certificate、non-increase certificate を保持する。`TerminalState` は terminal predicate と lawful predicate を分離し、`StrictlyDissipativeOutsideTerminal` が terminal 外 strict decrease を保持する。`SelectedEvolutionPath` が隣接 step の target point/state と次 source point/state の continuity を持つ finite selected path と path-wise non-increase / strict-decrease predicates を持ち、policy から path-wise theorem を読む。 | terminal state が lawful であることや future path forecast は主張しない。 |
| `IX.定理5.3 / R7` Finite Dissipation Stopping | `proved theorem package`. `InfiniteSelectedEvolutionPath` が隣接 step continuity を持つ infinite selected path を保持し、`FiniteDissipationStopping.no_infinite_nonterminal_path` が well-founded value order と terminal 外 strict decrease から infinite selected path staying outside terminal states の不存在を証明する。`SelectedEvolutionPath.maximal_path_reaches_terminal` は endpoint executable と endpoint maximality から finite selected path が terminal source state に到達することを証明する。 | terminal state が lawful であること、global executability、unselected future path forecast は主張しない。 |
| `IX.§6.1 / R8` AAT Lyapunov Reading | `defined only` / `proved accessor`. `AATLyapunovReading` が selected finite evolution profile scope、policy non-increase、selected obstruction-zero 近傍の minimum predicate、terminal lawfulness boundary、no-forecast boundary を保持する。`selected_path_monotone` が selected path 上の non-increase を証明し、`selected_path_strict_before_terminal` と `no_infinite_loop_before_terminal` が strict / finite stopping package から terminal 前の strict decrease と infinite loop/path 不存在を読む。`HarmonicMassLyapunovInstance` は PRD-8 harmonic-mass reading hook を selected state value に接続する。 | 未選択 transition、未構成 state space、任意 future path forecast は主張しない。 |
| `IX.定義7.1 / 定理候補7.2 / R9` Force / Force Integrability Obstruction Candidate | `defined only` / `statement-only candidate` / `proved accessor`. `Force` が selected incidence leg に沿う temporal state morphism と source/target state witness を保持する。`IntegrableForce` は `ForceIntegrationData` の `Nonempty` として local law data が selected global temporal law data へ descent / integration できる evidence predicate を読む。`ForceMismatchClass` が force 由来の degree-one temporal mismatch class、trace product site fixed 境界、mismatch construction soundness 境界を保持する。`ForceIntegrabilityObstructionCandidate` は selected nonzero obstruction、coefficient exactness、witness coverage、temporal descent detecting、local-to-global descent control を明示仮定にし、`candidate_not_integrable_of_obstruction` はその candidate field を読む。 | theorem candidate は future proof obligation として残し、一般 force integrability theorem は証明しない。未選択 transition、未構成 state space、任意 future path forecast は主張しない。 |
| `IX.R10 finite temporal examples` | `proved examples` / `selected finite fixtures`. `Formal/AG/Examples/EvolutionPart9.lean` が two-step trace、finite temporal site/state presheaf、singleton temporal coefficient / Čech bridge、zero replay descent fixture、pseudo-circle nonzero replay mismatch、finite dissipation stopping、non-lawful terminal boundary、harmonic Lyapunov reading、force mismatch class / obstruction candidate assumption fixture を持つ。`zeroReplayTemporalDescentCriterion` と `replay_zero_theorem42_global_transition_exists` が R5 の theorem-4.2 package から global replay transition を読み、`twoStep_dissipation_reaches_terminal_by_theorem53` が R7 の finite-path theorem 5.3 package から terminal reachability を読む。`toyForceMismatchClass` と `force_candidate_selected_nonzero` が R9 の `ForceMismatchClass` surface と selected nonzero assumption fixture を接続し、`finite_temporal_examples_verified` が R10(a)-(g) の aggregate witness を束ねる。 | selected finite fixtures に限る。一般 temporal semantics、nonzero replay からの global failure、full `ForceIntegrabilityObstructionCandidate` instance、一般 force integrability theorem、未選択 transition、任意 future path forecast は主張しない。 |
| `IX.R11 final ledger / no-sorry scan` | `proved final ledger sync`. `Formal/AG.lean` が `Formal.AG.Evolution` と `Formal.AG.Examples.EvolutionPart9` を import し、Part IX tower と finite examples を aggregate build 対象に含める。R11 validation で `Formal/AG` 全体の `axiom` / `admit` / `sorry` / `unsafe` scan が no match であることを確認し、`lean_theorem_index_ag_aat.md` と `proof_obligations_ag_aat.md` の第IX部 rows を最終実装と同期する。 | validation は Lean source と docs ledger の一致確認であり、PRD 外の source observation、runtime forecast、ArchMap / ArchSig / FieldSig 完全性は主張しない。 |

第IX部 PRD-9 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `IX.R0` | `defined only` / `proved accessor` |
| `IX.§1 / 定義2.1 / R1` EvolutionProfile / TraceCategory / EvolutionGeometry | `defined only` / `proved accessor` |
| `IX.TemporalSite` / `TempCoeff_A` / finite temporal coefficient bridge | `defined only` / `proved accessor` |
| `StateTransitionPresheaf` / `TemporalLaw` | `defined only` / `proved accessor` |
| `TemporalMismatch` / `TemporalCocycle` / `TemporalClass` | `defined only` / `proved accessor` |
| `ReplayDescentData` / `Temporal Descent Criterion` | `defined only` / `proved theorem package` |
| `EvolutionFunctional` / `DissipativePolicy` / `SelectedEvolutionPath` | `defined only` / `proved accessor` |
| `Finite Dissipation Stopping` | `proved theorem package` |
| `AATLyapunovReading` | `defined only` / `proved accessor` |
| `Force` / `IntegrableForce` / `ForceMismatchClass` | `defined only` / `proved accessor` |
| `ForceIntegrabilityObstructionCandidate` | `statement-only candidate` / `future proof obligation` |
| `Part IX finite examples` | `proved examples` / `selected finite fixtures` |
| `Part IX final ledger / no-sorry scan` | `proved final ledger sync` |
| `GeneralTraceSemantics` | `future proof obligation` / explicit non-goal for PRD-9 |
| `ExternalRuntimeForecast` | `future proof obligation` / explicit non-goal for PRD-9 |
| `AllFuturePathSafety` | `future proof obligation` / explicit non-goal for PRD-9 |
| `UnselectedEventCompleteness` | `future proof obligation` / explicit non-goal for PRD-9 |
| `TerminalStateImpliesLawfulWithoutObstructionAssumptions` | `future proof obligation` / explicit non-goal for PRD-9 |
| `GeneralForceIntegrabilityTheorem` | `future proof obligation` / explicit non-goal for PRD-9 |

## AAT Algebraic-Geometric Part X Semantic Repair Descent (SAGA) Lean status

Tracking Issue: [#2910](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2910).
Implementation Issues: R0 [#2911](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2911);
R1 [#2913](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2913),
[#2915](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2915),
[#2917](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2917),
[#2919](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2919);
R2 [#2921](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2921);
R3 [#2923](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2923),
[#2925](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2925);
R4 [#2927](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2927),
[#2929](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2929);
R5 [#2931](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2931);
R6 [#2933](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2933);
R7 [#2935](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2935),
[#2937](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2937);
R8 [#2939](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2939);
R9 [#2941](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2941),
[#2943](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2943);
R10 [#2946](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2946);
R11 [#2948](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2948),
[#2950](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2950).

| 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- |
| `X.R0` Semantic Repair entrypoint / bootstrap | `defined only` / `proved accessor`. `Formal/AG/SemanticRepair.lean` が `Bootstrap.lean`、`Projection.lean`、`GluingComplex.lean`、`Examples.lean`、`AdditiveH1.lean`、`SiteCech.lean`、`H1Comparison.lean`、`SagaComparison.lean`、`Boundary.lean` を束ね、`Formal/AG.lean` が `Formal.AG.SemanticRepair` と `Formal.AG.Examples.SemanticRepairPart10` を import する。 | semantic repair は selected semantic atom projection と selected finite cover surface に相対化される。 |
| `X.§4` Additive Cech H1 and true-sheaf boundary relation | `defined only` / `proved theorem package construction`. `SemanticRepairCoverCechData`、`SemanticRepairAdditiveCechH1Data`、`SemanticRepairCoverH1BoundaryRelationAbelianData`、`SemanticRepairCoverH1BoundaryRelationAdditiveData`、`TrueSheafConditionCertificate`、`semanticRepairAdditiveH1Zero_iff_boundary`、`globalRepairCoherent_iff_additiveH1Zero` が selected bounded cover data 上の additive H1 zero と global semantic repair coherence の同値を証明する。 | true-sheaf certificate は cover membership と ambient sheaf condition を保持する明示 data であり、certificate-free に生成しない。 |
| `X.§6` Atom-generated site / cover-relative Čech bridge | `proved theorem package construction`. `atomGeneratedCoverage_generates_AATGrothendieckTopology`、`selectedAATSiteTopology_eq_atomGeneratedGrothendieckTopology`、`SemanticRepairCoverRelativeCoverBridge`、`SemanticRepairCover.toCoverRelativeCechCover`、zero-simplex incidence no-go / constructive boundary、`coverNerve_typedComponent_adequacy`、`aatSheafCondition_coverMembership_descent_effectiveGluing` を持つ。 | cover-relative Čech cover への bridge は selected zero-simplex incidence と selected cover membership に相対化され、bare cover bridge だけから incidence は作らない。 |
| `X.定義7.1 / 定理7.2` H1 comparison | `proved theorem package construction`. `SemanticRepairAdditiveH1Surface` は finite-free semantic additive H1 surface として定義され、`SemanticRepairCoverRelativeH1Comparison` と `SemanticRepairCoverRelativeCochainRealization.toH1Comparison` から `semanticRepairAdditiveH1_equiv_coverRelativeH1`、`semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero`、`semanticRepairAdditiveH1_coverRelativeH1_comparison_package` を証明する。 | comparison structure は degree-wise equivalence と differential compatibility だけを保持し、zero conclusion、global coherence、descent、law-grounded conclusion を field として持たない。 |
| `X.定理7.3` Grounded Global Gluing | `proved theorem package construction`. `SemanticRepairCoverH1BoundaryRelationAdditiveData.toAdditiveH1Surface` と `boundedAdditiveH1Zero_iff_surfaceH1Zero` で §4 bounded additive H1 と theorem-7.2 finite-free H1 surface を接続し、`SemanticRepairGroundedGlobalGluingPackage` / `trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package` が sheaf condition、descent、unique global section、H1 comparison package、`GlobalSemanticRepairCoherent ↔ CoverRelativeResidualH1Zero`、bounded additive H1 zero equivalence、later obstruction vanishings を返す。 | theorem は selected true-sheaf certificate、selected gluing data、selected cochain comparisonを前提にする。full sheaf cohomology comparison や refinement/naturality は主張しない。 |
| `X.定理7.5` Generated End-to-End SAGA packet | `proved theorem package construction`. `SemanticRepairGeneratedLawDependentConclusions` が law-equation grounding 由来の結論1〜3を保持し、`SemanticRepairGeneratedLawIndependentConclusions` が theorem 7.3 由来の結論4〜10を保持する。`SemanticRepairGeneratedEndToEndSAGAPacket` と `lawEquation_constructs_groundedComparisonPacket` は `LawEquationDefectSource.lawEquation_grounding_packet` と theorem 7.3 package を合成し、law 依存境界を statement 構造で分離する。 | law-equation grounding は degree-zero conclusion group だけに依存し、descent / H1 / global coherence / higher vanishing は theorem 7.3 側の selected certificate と comparison から出る。Cycle 332 の巨大 route は本体へそのまま移植しない。 |
| `X.定理8.1 / 8.2 / 8.4 / 8.5` Boundary theorems | `proved boundary theorem package construction`. `GeneratedSourceC0PointwiseZero`、`GeneratedSourceC0CechZero`、`GeneratedSourceC0ZeroPackage`、`displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage` が law fulfillment から degree-zero zero readings を構成する。`generatedSAGA_lawIndependentConclusions_withoutLawPremise` は law premise なしで theorem 7.5 の law-independent conclusion group を構成する。`SemanticRepairTypedComparisonTarget` / `SemanticRepairTypedZeroComparison` と `SemanticRepairRefinementZeroComparison` は comparison / refinement を explicit data とし、empty target と coarse-zero/fine-nonzero の no-go を証明する。 | §8 theorem は zero preservation や law-independent conclusion を explicit selected data から読む。typed target、refinement comparison、cover-relative H1 comparison、cochain realization を無条件に構成しない。意味8.3 の conormal coefficient open question は R11/AC19 の future proof obligation 登録対象として残す。 |
| `X.例9.1` Lawful Firing Instance | `proved lawful firing instance`. `Formal/AG/Examples/SemanticRepairPart10.lean` が singleton quotient presheaf の `quotientIsSheaf` を theorem として放電し、`lawfulObject_noCycleLaw`、`defectSource.DisplayedRequiredLawsHoldOn`、`trueSheafCertificate`、`h1Comparison` から `lawfulFiring_endToEndPacket` と `lawfulFiring_generatedSourceC0Zero` を構成する。 | 例9.1 は lawful zero firing witness であり、circle nerve 非零 class / transfer packet は例9.2 の別 witness で扱う。一般 quotient sheaf comparison は explicit data なしに構成しない。 |
| `X.例9.2` Circle Nerve Nonzero Class | `proved nonzero circle-nerve transfer instance`. `Formal/AG/Examples/SemanticRepairPart10.lean` が selected witness site、`circleF2IsSheaf`、`circleObstructionSheaf`、three-edge `circleSimplex` / `circleFace`、`circleD0`、`circleCoverRelativeComplex`、semantic residual `1 : ZMod 2`、cover-relative residual class、`circleSemanticH1_nonzero`、`circleCoverRelativeH1_nonzero`、`circleH1Comparison`、`circleNerve_nonzeroClassTransfer_packet` を持つ。 | 例9.2 の nerve は supplied simplicial data であり、chart intersections から生成されたとは主張しない。comparison は identity comparison に限る。degenerate witness site 上の instance であり、atom-generated nonzero instance や非恒等 comparison の transfer は future hardening に残す。 |
| `X.R10 final ledger / no-sorry scan` | `proved final ledger sync`. `Formal/AG.lean` が `Formal.AG.SemanticRepair` と `Formal.AG.Examples.SemanticRepairPart10` を import し、Part X semantic repair tower と examples を default `lake build` 対象に含める。AC18 validation で `Formal/AG` から `Formal/AG/Research/` と `Formal/AG/Research.lean` を除いた範囲の `axiom` / `admit` / `sorry` / `unsafe` scan、および `Formal.AG.Research` import scan が no match であることを確認する。 | validation は Lean source と docs ledger の一致確認であり、PRD 外の completeness claim は主張しない。 |
| `PartXArbitraryGrothendieckSiteGeneralization` | `future proof obligation` / explicit non-goal for PRD-10. | Part X theorem は selected AAT site / selected semantic repair cover / selected cover membership に相対化される。任意 Grothendieck site への無条件一般化は主張しない。 |
| `PartXFullSheafCohomologyIdentification` | `future proof obligation` / explicit non-goal for PRD-10. | Part X は cover-relative Čech H1 と selected comparison data を読む。full sheaf cohomology との無条件同一視は主張しない。 |
| `PartXUnboundedDerivedStackyUniversality` | `future proof obligation` / explicit non-goal for PRD-10. | Part X は bounded selected additive / cover-relative surface に留まる。unbounded derived、infinity-stack、nonabelian、stacky universality は主張しない。 |
| `PartXUnconditionalRefinementNaturality` | `future proof obligation` / explicit non-goal for PRD-10. | refinement zero preservation は explicit comparison / refinement data の下でのみ読む。無条件 refinement naturality は主張しない。 |
| `PartXBoundaryIdentityComparison` | `boundary note` / explicit non-goal for PRD-10. | 例9.2 の theorem 7.2 transfer packet は identity comparison 上の非零 class transfer として発火する。非恒等 comparison を通じた非零転送 instance は主張しない。 |
| `PartXBoundarySelectedCircleNerve` | `boundary note` / explicit non-goal for PRD-10. | 例9.2 は selected three-edge circle nerve の supplied simplicial data を使う。chart 交叉から生成された nerve や atom-generated nonzero instance は主張しない。 |
| `PartXBoundaryDegenerateWitnessSite` | `boundary note` / explicit non-goal for PRD-10. | finite witness site は singleton contexts を使う degenerate witness site である。一般 finite site / nondegenerate cover での nonzero class firing は主張しない。 |
| `PartXBoundaryLawEquationAmbientRows` | `boundary note` / explicit non-goal for PRD-10. | law-equation surface の cover geometry / coefficient geometry / semantic site / pointwise atom-law choices は supplied ambient data として扱う。ambient rows を theorem conclusion として生成したとは主張しない。 |
| `PartXConormalCoefficientOpenQuestion` | `future proof obligation` / meaning 8.3 open question. | 相異なる非零の lawful reading が非自明に貼り合う係数としての conormal `I_U/I_U²` reading は未形式化の open question として残し、PRD-10 では形式化しない。 |

第X部 PRD-10 の証明対象ラベルは次の現在状態である。

| 証明対象ラベル | Lean status |
| --- | --- |
| `X.R0` Semantic Repair entrypoint / bootstrap | `defined only` / `proved accessor` |
| `X.§4` additive Cech H1 / true-sheaf boundary relation | `defined only` / `proved theorem package construction` |
| `X.§6` atom-generated site / cover-relative Čech bridge | `proved theorem package construction` |
| `X.定義7.1 / 定理7.2` semantic additive H1 / cover-relative H1 comparison | `proved theorem package construction` |
| `X.定理7.3` Grounded Global Gluing | `proved theorem package construction` |
| `X.定理7.5` Generated End-to-End SAGA packet | `proved theorem package construction` |
| `X.定理8.1 / 8.2 / 8.4 / 8.5` Boundary theorems | `proved boundary theorem package construction` |
| `X.例9.1` Lawful Firing Instance | `proved lawful firing instance` |
| `X.例9.2` Circle Nerve Nonzero Class | `proved nonzero circle-nerve transfer instance` |
| `X.R10 final ledger / no-sorry scan` | `proved final ledger sync` |
| `PartXArbitraryGrothendieckSiteGeneralization` | `future proof obligation` / explicit non-goal for PRD-10 |
| `PartXFullSheafCohomologyIdentification` | `future proof obligation` / explicit non-goal for PRD-10 |
| `PartXUnboundedDerivedStackyUniversality` | `future proof obligation` / explicit non-goal for PRD-10 |
| `PartXUnconditionalRefinementNaturality` | `future proof obligation` / explicit non-goal for PRD-10 |
| `PartXBoundaryIdentityComparison` | `boundary note` / explicit non-goal for PRD-10 |
| `PartXBoundarySelectedCircleNerve` | `boundary note` / explicit non-goal for PRD-10 |
| `PartXBoundaryDegenerateWitnessSite` | `boundary note` / explicit non-goal for PRD-10 |
| `PartXBoundaryLawEquationAmbientRows` | `boundary note` / explicit non-goal for PRD-10 |
| `PartXConormalCoefficientOpenQuestion` | `future proof obligation` / meaning 8.3 open question |
