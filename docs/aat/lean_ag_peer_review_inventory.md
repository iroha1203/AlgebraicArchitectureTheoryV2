# AG Lean PRD-R peer-review hardening inventory

この台帳は `docs/aat/lean_ag_peer_review_hardening_prd.md` R0 の棚卸し記録である。
対象は `Formal/AG` 本体であり、`Formal/AG/Research/**` は evidence として凍結する。
本台帳は分類台帳であり、この PR では Lean 宣言の削除・rename・シグネチャ変更を行わない。

## R0 status vocabulary

PRD-R 以降、AG theorem index と proof obligation 台帳の theorem 系 status は次の正規化タグを併記して読む。

| R0 tag | 読み | 既存 status からの移行 |
| --- | --- | --- |
| `proved` | 実証明。仮定は明示的で、結論そのものを仮定 package の field から取り出していないもの。 | `proved`, `proved theorem package construction`, `proved boundary theorem package construction`, `proved examples`, `proved selected finite examples`, `proved final ledger sync` のうち、台帳本文が実証明または検証同期として説明しているもの。 |
| `packaged (assumption-relative)` | 仮定 record / certificate / selected package の field 合成から得る帰結。Lean 上は theorem/package が存在しても、査読上の「無条件 proved」には数えない。 | `proved under explicit ... assumptions`, `proved accessor`, `proved theorem package` のうち結論 field・accessor・selected assumptions を読むもの。 |
| `statement-only` | 型・candidate surface はあるが、証明済み theorem として数えないもの。 | `statement-only candidate`, `theorem candidate statement-only`, `statement only` と明示された candidate。 |

`defined only`、standalone `future proof obligation`、`empirical hypothesis`、explicit non-goal、boundary note は三分化の対象外である。
`statement-only candidate` と同じ行に `future proof obligation` が併記されている場合は candidate surface だけを
`statement-only` とし、未証明 obligation としての残タスク性は別に残す。

## Mechanical extraction layer

実行 commit: `7ea490128178d033f969b023f3cca8928999ac7a`

対象:

```bash
Formal/AG --glob '!Formal/AG/Research/**'
```

機械抽出層は次の `rg` パターンで固定する。

| Pattern | Count | R0 reading |
| --- | ---: | --- |
| `^\s*[A-Za-z0-9_]+\s*:\s*Prop\b` | 415 | `Prop` field / argument candidate。PRD 表に載る対象は昇格・実質化・宣言・削除へ分類し、その他は後続 R0 refinement の監査対象として残す。 |
| `_holds\b\|_cert\b` | 1208 | certificate/accessor surface。結論 field theorem か実述語 witness かをレビュー層で分ける。 |
| `\bNonempty\b` | 48 | `Nonempty` だけを返す theorem/package candidate。空型 package と witness package を分ける。 |
| `native_decide` | 6 | R1 で全廃する kernel axiom audit gap。 |
| `comparisonName\s*:\s*String` | 1 | R0(d) 候補。semantic payload になっていない表示名 field。 |
| `\bHEq\b` | 8 | AATCore / comparison provenance 周辺の review target。 |
| `∃\s*_,\s*True` | 0 | 現 pattern では no match。`Nonempty` / explicit `True` field 側で追跡する。 |
| combined pattern | 1685 | 上記を一つの alternation で数えた重複除去後のヒット行数。同一行が複数 pattern に該当するため、個別 count の単純和とは一致しない。 |

`native_decide` の全件:

| File | Count | R0 classification |
| --- | ---: | --- |
| `Formal/AG/Cohomology/FiniteExamples.lean` | 1 | R1 で昇格。 |
| `Formal/AG/Examples/DerivedPart5.lean` | 3 | R1 で昇格。 |
| `Formal/AG/Examples/EvolutionPart9.lean` | 2 | R1 で昇格。 |

## Research reference freeze list

抽出コマンド:

```bash
rg -o 'AAT\.AG\.[A-Za-z0-9_.]+' Formal/AG/Research/ --glob '*.lean' | \
  sed 's/^.*AAT\.AG\./AAT.AG./' | sort -u
```

現時点の本体参照は 84 unique names である。以下の全件を PRD-R の削除・rename・シグネチャ変更対象から除外し、必要な補強は additive に行う。末尾 `.` を含む行は namespace prefix としての抽出結果であり、その prefix 配下の既存参照も凍結対象に含める。

| # | Extracted Research reference |
| ---: | --- |
| 1 | `AAT.AG.ArchitectureObject` |
| 2 | `AAT.AG.ArchitectureSignature` |
| 3 | `AAT.AG.AtomCarrier.` |
| 4 | `AAT.AG.AtomConfiguration` |
| 5 | `AAT.AG.Cohomology.CoverNerve.` |
| 6 | `AAT.AG.Cohomology.CoverNerve.edge_component_selected` |
| 7 | `AAT.AG.Cohomology.CoverNerve.face_component_selected` |
| 8 | `AAT.AG.Cohomology.CoverRelativeCechCochain` |
| 9 | `AAT.AG.Cohomology.CoverRelativeCechComplex` |
| 10 | `AAT.AG.Cohomology.CoverRelativeCechComplex.d` |
| 11 | `AAT.AG.Cohomology.CoverRelativeCechComplex.faceRestrictionTerm` |
| 12 | `AAT.AG.Cohomology.CoverRelativeCechCover` |
| 13 | `AAT.AG.Cohomology.FinitePosetCechComparisonData` |
| 14 | `AAT.AG.Cohomology.FinitePosetCechComparisonData.differential_compatible` |
| 15 | `AAT.AG.Cohomology.ObstructionSheaf` |
| 16 | `AAT.AG.Cohomology.finitePosetCoverRelativeCover` |
| 17 | `AAT.AG.FiniteModel.FiniteAtom` |
| 18 | `AAT.AG.FiniteModel.FiniteAtom.componentA` |
| 19 | `AAT.AG.FiniteModel.allFamily` |
| 20 | `AAT.AG.FiniteModel.carrier` |
| 21 | `AAT.AG.FiniteModel.carrier.Atom` |
| 22 | `AAT.AG.FiniteModel.lawUniverse_required` |
| 23 | `AAT.AG.FiniteModel.noCycleLaw.holds` |
| 24 | `AAT.AG.FiniteModel.objectOfConfiguration` |
| 25 | `AAT.AG.FiniteModel.site` |
| 26 | `AAT.AG.FiniteModel.site.category` |
| 27 | `AAT.AG.FiniteModel.site.lawUniverse.Index` |
| 28 | `AAT.AG.FiniteModel.site.overlap` |
| 29 | `AAT.AG.FiniteModel.site.requirements` |
| 30 | `AAT.AG.FiniteModel.siteAdequacyRequirements` |
| 31 | `AAT.AG.FiniteModel.siteBase` |
| 32 | `AAT.AG.FiniteModel.siteContext` |
| 33 | `AAT.AG.FiniteModel.siteContextPreorder` |
| 34 | `AAT.AG.FiniteModel.siteSingletonCover` |
| 35 | `AAT.AG.FiniteModel.siteSingletonCover_uAdequate` |
| 36 | `AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.` |
| 37 | `AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.RestrictionCompatible` |
| 38 | `AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff` |
| 39 | `AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.map_localObstructionIdeal_le` |
| 40 | `AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.witnessIdeal_le_localObstructionIdeal` |
| 41 | `AAT.AG.LawUniverse` |
| 42 | `AAT.AG.Lawfulness` |
| 43 | `AAT.AG.Site.AATCocycleCondition` |
| 44 | `AAT.AG.Site.AATCoverageFamily` |
| 45 | `AAT.AG.Site.AATCoverageFamily.presieve` |
| 46 | `AAT.AG.Site.AATDescent` |
| 47 | `AAT.AG.Site.AATDescent.exists_global` |
| 48 | `AAT.AG.Site.AATGlobalSectionRealizes` |
| 49 | `AAT.AG.Site.AATGluingData` |
| 50 | `AAT.AG.Site.AATGluingData.cocycle` |
| 51 | `AAT.AG.Site.AATGrothendieckTopology` |
| 52 | `AAT.AG.Site.AATGrothendieckTopology.generate_mem` |
| 53 | `AAT.AG.Site.AATLocalSectionFamily` |
| 54 | `AAT.AG.Site.AATOverlapAgreement` |
| 55 | `AAT.AG.Site.AATPresheaf` |
| 56 | `AAT.AG.Site.AATSheaf` |
| 57 | `AAT.AG.Site.AATSheaf.toPresheaf` |
| 58 | `AAT.AG.Site.AATSheafCondition` |
| 59 | `AAT.AG.Site.AATSheafCondition.cover` |
| 60 | `AAT.AG.Site.AATSheafCondition.iff_presieve_isSheaf` |
| 61 | `AAT.AG.Site.AATSheafConditionFor` |
| 62 | `AAT.AG.Site.AATSheafConditionFor.descent` |
| 63 | `AAT.AG.Site.AATSite` |
| 64 | `AAT.AG.Site.AATSite.topology` |
| 65 | `AAT.AG.Site.AATSite.topology_eq` |
| 66 | `AAT.AG.Site.ArchCtx` |
| 67 | `AAT.AG.Site.ContextCategoryObject` |
| 68 | `AAT.AG.Site.ContextCategoryObject.of` |
| 69 | `AAT.AG.Site.ContextOverlapPullback` |
| 70 | `AAT.AG.Site.ContextPreorderCategory` |
| 71 | `AAT.AG.Site.CoverageRequirements` |
| 72 | `AAT.AG.Site.FinitePosetAATSiteRegime` |
| 73 | `AAT.AG.Site.FinitePosetCechAdditiveData` |
| 74 | `AAT.AG.Site.FinitePosetCechCochain` |
| 75 | `AAT.AG.Site.FinitePosetCechComplex` |
| 76 | `AAT.AG.Site.FinitePosetCechFaceData` |
| 77 | `AAT.AG.Site.FinitePosetCechFaceRestriction` |
| 78 | `AAT.AG.Site.FinitePosetCechOverlapObject` |
| 79 | `AAT.AG.Site.FinitePosetCechSection` |
| 80 | `AAT.AG.Site.FinitePosetCechSimplex` |
| 81 | `AAT.AG.Site.FinitePosetCechZeroCochain` |
| 82 | `AAT.AG.Site.UAdequacyRequirements` |
| 83 | `AAT.AG.Site.UAdequateCover` |
| 84 | `AAT.AG.lawfulness_required_holds` |

## Review layer scan record

レビュー層では PRD-R の補強対象表 I-* から IX-* を全件走査対象とした。
走査対象ファイルは PRD-R 表に明記された本体ファイル、および二台帳の対応行である。
X-1 / X-2 は任意 hardening であり、PRD-R の完了条件には含めない。
`Target` が basename のみの場合も PRD-R の対応 ID で一意化して読み、後続 Issue では
`Old PRD AC reclassification` 表または PRD-R 表の full path を実装対象として使う。

走査済み本体ファイル:

```text
Formal/AG/Atom/ThreeReading.lean
Formal/AG/Atom/AATCore.lean
Formal/AG/Atom/Configuration.lean
Formal/AG/Atom/Obstruction.lean
Formal/AG/Atom/Law.lean
Formal/AG/Site/Adequate.lean
Formal/AG/Site/ContextCategory.lean
Formal/AG/Site/Context.lean
Formal/AG/Site/FinitePoset.lean
Formal/AG/Examples/FiniteModel.lean
Formal/AG/Site/Topology.lean
Formal/AG/LawAlgebra/Correspondence.lean
Formal/AG/LawAlgebra/LawfulLocus.lean
Formal/AG/LawAlgebra/StructureSheaf.lean
Formal/AG/LawAlgebra/Scheme.lean
Formal/AG/LawAlgebra/Nullstellensatz.lean
Formal/AG/Cohomology/CechComplex.lean
Formal/AG/Cohomology/FiniteExamples.lean
Formal/AG/Cohomology/LocalFlatnessGap.lean
Formal/AG/Cohomology/FlatnessCriterion.lean
Formal/AG/Cohomology/CoverNerve.lean
Formal/AG/Cohomology/ObstructionSheaf.lean
Formal/AG/Cohomology/BoundaryResidue.lean
Formal/AG/Cohomology/PeriodStokes.lean
Formal/AG/Derived/Counterexample.lean
Formal/AG/Derived/Intersection.lean
Formal/AG/Derived/TaylorResolution.lean
Formal/AG/Derived/FreeResolution.lean
Formal/AG/Derived/HilbertSeries.lean
Formal/AG/Examples/DerivedPart5.lean
Formal/AG/Examples/SingularityMonodromyStackPart6.lean
Formal/AG/SingularityMonodromyStack/OperationHomotopy.lean
Formal/AG/SingularityMonodromyStack/ArchitectureStack.lean
Formal/AG/SingularityMonodromyStack/CotangentInterface.lean
Formal/AG/SingularityMonodromyStack/Kuranishi.lean
Formal/AG/SingularityMonodromyStack/DecompositionGerbe.lean
Formal/AG/RepresentationAnalysis/Synthesis.lean
Formal/AG/RepresentationAnalysis/AATSch.lean
Formal/AG/RepresentationAnalysis/FiniteHomology.lean
Formal/AG/RepresentationAnalysis/AnalyticContext.lean
Formal/AG/RepresentationAnalysis/DistanceFlatnessMass.lean
Formal/AG/RepresentationAnalysis/GraphMatrix.lean
Formal/AG/Measurement/Hodge.lean
Formal/AG/Measurement/SquareFreeRepair.lean
Formal/AG/Measurement/FiniteRegime.lean
Formal/AG/Measurement/Computability.lean
Formal/AG/Measurement/LawConflict.lean
Formal/AG/Measurement/Packet.lean
Formal/AG/Measurement/GAGA.lean
Formal/AG/Measurement/Examples.lean
Formal/AG/Evolution/ReplayDescent.lean
Formal/AG/Evolution/Force.lean
Formal/AG/Evolution/TemporalProductSite.lean
Formal/AG/Evolution/TemporalLaw.lean
Formal/AG/Examples/EvolutionPart9.lean
docs/aat/lean_theorem_index_ag_aat.md
docs/aat/proof_obligations_ag_aat.md
```

| ID | Target | R0 classification | Reason / next owner |
| --- | --- | --- | --- |
| I-1 | `ThreeReading.lean` 定理9.3後段 | 昇格 | theorem conclusion が assumption package field。law-indexed witness family と finite firing が必要。 |
| I-2 | `AATCore.lean` 定理10.5 | 昇格 | selected components を束ねる package で、S から標準塔を構成していない。 |
| I-3 | `Configuration.lean` / `Obstruction.lean` finite marker | 実質化 | `finite : Prop` 系を `Set.Finite` / `Finite` へ接続する。 |
| I-4 | `Law.lean` unused assumptions | 宣言 | R2 で Research 参照が確認されたため削除せず、selected 公理スロットとして凍結する。必要な load-bearing reading は I-1 の concrete required-law API へ移す。 |
| II-1 | `Adequate.lean` 補題7.2A | 昇格 | R3 で seed-side support / axis assumptions から witness support と seed overlap を閉じる additive theorem を追加済み。 |
| II-2 | `ContextCategory.lean` 命題4.2 | 昇格 | R3 で restriction-morphism preorder、componentwise product meet、readable-equivalence quotient finite-meet poset construction を追加済み。 |
| II-3 | `Context.lean` morphism roles | 実質化 | R3 で `MinimalContext` の support reading を `A.configuration.family` に接続し、旧 free Prop role slots を `ContextMorphism` 外部の support / axis / observable / non-generation concrete predicate へ置換済み。 |
| II-4 | `FinitePoset.lean` 命題7.2C | 昇格 | R3 で PRD-10 標準複体 route を II-4 evidence へ接続済み。旧 selected data 版は packaged compatibility surface として明示。 |
| II-5 | `Examples/FiniteModel.lean` Part II examples | 発火 | singleton / True 例から 2 patch + overlap finite site へ進める。 |
| II-6 | `Topology.lean` Mathlib coverage bridge | 発火 | meet 付き thin site instance で bridge theorem を発火させる。 |
| III-1 | `Correspondence.lean` 定理11.1 | 昇格 | witnessCoverage field 依存を witness ideal family へ接続する。 |
| III-2 | `LawfulLocus.lean` factorization | 昇格 | B項目。消滅から zeroLocus への片方向を theorem 化し、逆向き radical gap は非主張へ。 |
| III-3 | `StructureSheaf.lean` sheafification bridge | 昇格 | B項目。Mathlib `HasSheafify` 製造補題が未実装。 |
| III-4 | `Scheme.lean` chart compatibility | 実質化 | 3成分無関係 / freedom Prop を affine `Spec` 例または整合条件へ接続する。 |
| III-5 | `Nullstellensatz.lean` NSdepth | 実質化 | B項目。任意 Nat predicate から生成系表示次数へ。 |
| IV-1 | `CechComplex.lean` | 昇格 | differential / d^2=0 field と Type-valued Hn を additive quotient H1 へ接続する。 |
| IV-2 | `FiniteExamples.lean` pseudo circle | 発火 | PRD-10 circle nonzero H1 を Part IV 語彙で発火させる。 |
| IV-3 | `LocalFlatnessGap.lean` 定理7.1 | 昇格 | lawful section / coboundary soundness を具体化する。 |
| IV-4 | `FlatnessCriterion.lean` 定理11.1 | 昇格 | C0 torsor と vanishing equivalence を finite regime で証明する。 |
| IV-5 | `CoverNerve.lean` 12.* | 昇格 | rank-nullity / nerve chain complex / forest induction を実装する。 |
| IV-6 | `Formal/AG/Cohomology/ObstructionSheaf.lean` `DerOb_U` | 昇格 | opaque placeholder。naive cotangent complex definition へ進める。実装中に不可能と判明した場合は PRD 停止条件に従い、削除や未形式化化は別判断にする。 |
| IV-7 | `BoundaryResidue.lean` / `PeriodStokes.lean` | 実質化 | globally U-flat と stokes を supplied field から実述語へ。 |
| IV-8 | `ObstructionSheaf.lean` Type-valued sheaf | 実質化 | AddCommGrpCat constructor 側を正とし既存 surface は凍結。 |
| V-1 | `Counterexample.lean` Tor1 nonzero | 昇格 | certificate assumption から principal resolution calculation へ。 |
| V-2 | `Intersection.lean` Tor0 bridge | 昇格 | Tor zero / quotient tensor bridge と canonical instance。 |
| V-3 | `TaylorResolution.lean` | 昇格 | 2生成 Taylor complex を実構成し一般形は packaged。 |
| V-4 | `FreeResolution.lean` exact field | 実質化 | `Function.Exact` predicate へ。 |
| V-5 | mislabeled / content-free theorems | 削除 | finite_trace_certificate 等。必要なら正しい theorem へ差し替え。 |
| V-6 | `HilbertSeries.lean` | 実質化 | `PowerSeries` または monomial basis count へ接続する。 |
| VI-1 | Part VI toy models | 発火 | empty `TransportDescentToyModel` を分割し 5 concrete instances を作る。 |
| VI-2 | `OperationHomotopy.lean` pi1 | 昇格 | `PresentedGroup` と universal property へ。 |
| VI-3 | `ArchitectureStack.lean` | 実質化 | triple-overlap restriction と cocycle equality を実装する。 |
| VI-4 | `CotangentInterface.lean` / `Kuranishi.lean` | 実質化 | cotangent data と IV-6 `DerOb_U` を接続する。 |
| VI-5 | `Formal/AG/SingularityMonodromyStack/DecompositionGerbe.lean` | 宣言 | B項目。現 R0 では soundness / nonzero が supplied boundary であることを公理的境界として明示し、昇格可能性は後続 Issue の判断に残す。 |
| VII-1 | `Synthesis.lean` theorem 16.1 | 発火 | finite model から complete assumptions instance を構成する。 |
| VII-2 | `AATSch.lean` | 実質化 | morphism compatibility を fixed predicate へ移し category / functor bridge を作る。 |
| VII-3 | `FiniteHomology.lean` strict period | 昇格 | concrete pairing の coboundary invariance。 |
| VII-4 | `AnalyticContext.lean` theorem 15.4 | 実質化 | adequacy assumptions を load-bearing 化し zeroClass を actual zero へ。 |
| VII-5 | `DistanceFlatnessMass.lean` | 実質化 | fake GLB を `iInf` / actual GLB へ。 |
| VII-6 | `GraphMatrix.lean` walk count | 昇格 | B項目。existence iff から card equality へ。 |
| VIII-1 | `Hodge.lean` 8.5/8.6/8.7 | 昇格 | finite inner-product complex theorem。PRD-R 最重要昇格。 |
| VIII-2 | `SquareFreeRepair.lean` theorem 5.2 | 昇格 | PRD-3 Stanley-Reisner asset と Alexander dual / hitting set proof へ。 |
| VIII-3 | `FiniteRegime.lean` / `Computability.lean` | 実質化 | `Finite` / `Fintype` predicates と finite cochain lemma。 |
| VIII-4 | `LawConflict.lean` | 実質化 | Derived `LawConflictPackage` へ接続する。 |
| VIII-5 | `Packet.lean` / `GAGA.lean` | 実質化 | certified fields を theorem package 型へ。 |
| VIII-6 | `Examples.lean` | 発火 | Hodge / refactor / 5.2 fixtures を nontrivial finite examples へ。 |
| IX-1 | `ReplayDescent.lean` theorem 4.2 | 昇格 | torsor action / gluing operation / mismatch calculation。 |
| IX-2 | `Force.lean` candidate 7.2 | 実質化 | `IntegrableForce` を real interface にし candidate を inhabitable にする。 |
| IX-3 | temporal product cohomology | 昇格 | finite poset x two-point trace incidence complex。 |
| IX-4 | `TemporalLaw.lean` definition 3.3 | 実質化 | kind-specific canonical constructors and equations。 |
| IX-5 | `Examples/EvolutionPart9.lean` | 発火 | nondegenerate replay / PRD-10 circle instance connection。 |

## Old PRD AC reclassification

旧 PRD 1-9 の acceptance criteria は、PRD-R では次のように再判定する。

| PRD | AC item | Reclassified AC text | R0 tag | Evidence |
| --- | --- | --- | --- | --- |
| PRD-1 | AC11 | 旧 `ThreeReadingAgreementAssumptions` 版は explicit package field 由来。PRD-R R2 で required-law concrete counterpart が証明済み。 | `proved` / `packaged (assumption-relative)` | `Formal/AG/Atom/ThreeReading.lean`, `concreteThreeReadingAgreement`, `ThreeReadingAgreementAssumptions.*` |
| PRD-1 | AC13 | 旧 `exists_ofComponents` は selected components を束ねる theorem package。PRD-R R2 で `AtomTowerRealization` と HEq-free counterpart が証明済み。 | `proved` / `packaged (assumption-relative)` | `Formal/AG/Atom/AATCore.lean`, `exists_ofAxiomRealization_noHEq`, `AATCorePackage.*` |
| PRD-2 | AC5 | PRD-R R3 で seed-side support / axis coverage、required witness support、seed-overlap boundary visibility から closed admissible cover と `U`-adequacy を構成する additive counterpart を証明済み。旧 `WitnessClosureCover` 版は Research-compatible packaged surface として残る。 | `proved` / `packaged (assumption-relative)` | `Formal/AG/Site/Adequate.lean`, `SeedWitnessClosureCover.toAATCoverageFamily_admissible`, `SeedWitnessClosureCover.uAdequate`, `witnessClosureCover_uAdequate` |
| PRD-2 | AC11 | finite model examples は singleton / selected finite-poset fixture に相対化される。 | `packaged (assumption-relative)` | `Formal/AG/Examples/FiniteModel.lean`, `siteSingletonCover_uAdequate` |
| PRD-3 | AC12 | Nullstellensatz candidate は statement surface に留まり、証明済み theorem ではない。 | `statement-only` | `Formal/AG/LawAlgebra/Nullstellensatz.lean`, `ArchitectureNullstellensatzCandidate` |
| PRD-3 | AC18 | 定理11.1 Lawfulness-Ideal Correspondence は selected witness / coverage package に相対化される。 | `packaged (assumption-relative)` | `Formal/AG/LawAlgebra/Correspondence.lean` |
| PRD-4 | AC3 / AC4 | Čech complex / finite-poset comparison は selected complex data と explicit d^2 field に相対化される。 | `packaged (assumption-relative)` | `Formal/AG/Cohomology/CechComplex.lean`, `Formal/AG/Cohomology/FinitePosetComparison.lean` |
| PRD-4 | AC11 / AC13 | flatness criterion and pseudo-circle H1 example are package/fixture-relative. | `packaged (assumption-relative)` | `Formal/AG/Cohomology/FlatnessCriterion.lean`, `Formal/AG/Cohomology/FiniteExamples.lean`, `CoverRelativeH1NonzeroWitness` |
| PRD-5 | AC5 / AC6 | finite free / Taylor resolution exactness contains package assumptions to be hardened. | `packaged (assumption-relative)` | `Formal/AG/Derived/TaylorResolution.lean`, `Formal/AG/Derived/FreeResolution.lean` |
| PRD-5 | AC16 | 例5.6 `Tor1` nonzero fixture is certificate-relative. | `packaged (assumption-relative)` | `Formal/AG/Derived/Counterexample.lean`, `Example56TorCalculation` |
| PRD-6 | AC10 | `pi1^AAT` universal property needs `PresentedGroup` hardening. | `packaged (assumption-relative)` | `Formal/AG/SingularityMonodromyStack/OperationHomotopy.lean` |
| PRD-6 | AC20 | five finite toy models are not concrete firing instances under PRD-R. | `packaged (assumption-relative)` | `Formal/AG/Examples/SingularityMonodromyStackPart6.lean`, `TransportDescentToyModel` |
| PRD-7 | AC8 | strict period well-definedness is selected finite homology data relative. | `packaged (assumption-relative)` | `Formal/AG/RepresentationAnalysis/FiniteHomology.lean` |
| PRD-7 | AC19 | AAT synthesis theorem is package-relative and lacks finite model firing. | `packaged (assumption-relative)` | `Formal/AG/RepresentationAnalysis/Synthesis.lean`, `AATSynthesisPackage` |
| PRD-8 | AC8 / AC14 / AC15 | theorem 5.2 and Hodge theorem package are certified-field/package relative. | `packaged (assumption-relative)` | `Formal/AG/Measurement/SquareFreeRepair.lean`, `Formal/AG/Measurement/Hodge.lean` |
| PRD-8 | AC9 / AC10 / AC16 / AC17 | stability / spectral / base-change candidates remain statement-only. | `statement-only` | `Formal/AG/Measurement/Stability.lean`, `Formal/AG/Measurement/Hodge.lean`, `Formal/AG/Measurement/LawConflict.lean` |
| PRD-9 | AC13 | theorem 4.2 Temporal Descent Criterion is selected temporal package relative. | `packaged (assumption-relative)` | `Formal/AG/Evolution/ReplayDescent.lean`, `TemporalDescentCriterion` |
| PRD-9 | AC20 | finite temporal examples include selected / degenerate fixtures and force candidate assumptions. | `packaged (assumption-relative)` / `statement-only` | `Formal/AG/Examples/EvolutionPart9.lean`, `ForceCandidateFixture`; `Formal/AG/Evolution/Force.lean`, `ForceIntegrabilityObstructionCandidate` |

## R0 completion note

This R0 pass does not claim that every mechanical hit has been repaired.
It fixes the audit surface and assigns the PRD-R table items to one of the four actions.
Repair work starts in R1 and R2-R10 child issues.

## R1 kernel axiom guard

R1 removes all `native_decide` occurrences from `Formal/AG` and adds
`Formal/AG/AxiomAudit.lean` as the kernel-level audit entrypoint.

CI command:

```bash
lake env lean Formal/AG/AxiomAudit.lean
```

R1 tracked declarations:

| Audit wrapper | Source declaration | Allowed axiom set |
| --- | --- | --- |
| `AAT.AG.AxiomAudit.boundaryCocycleNonzero` | `AAT.AG.Cohomology.FiniteExamples.PseudoCircleGolden.boundaryCocycle_AB_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.derivedG5AllDegree` | `AAT.AG.FiniteModel.DerivedPart5.sharedWitnessG5_all_degree_coefficient_identity` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.temporalPseudoCircleNonzero` | `AAT.AG.Examples.EvolutionPart9.pseudoCircleMismatch_ab_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.forceCandidateConcreteNonzero` | `AAT.AG.Examples.EvolutionPart9.forceCandidateFixture.concreteObstruction_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.concreteThreeReadingAgreementRequiredLaw` | `AAT.AG.concreteThreeReadingAgreement` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteAcyclicConcreteThreeReadingAgreement` | `AAT.AG.FiniteModel.acyclic_concreteThreeReadingAgreement` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteCyclicConcreteThreeReadingFires` | `AAT.AG.FiniteModel.object_concreteThreeReadingAgreement_fires` | `propext` |
| `AAT.AG.AxiomAudit.finiteCorePackageFromAxiomRealizationNoHEq` | `AAT.AG.FiniteModel.corePackageFromAxiomRealization_exists_noHEq` | `propext` |
| `AAT.AG.AxiomAudit.finiteSeedWitnessClosureAdmissible` | `AAT.AG.FiniteModel.siteSeedWitnessClosureCover_admissible` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteSeedWitnessClosureUAdequate` | `AAT.AG.FiniteModel.siteSeedWitnessClosureCover_uAdequate` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteRestrictionQuotientFiniteMeetPoset` | `AAT.AG.FiniteModel.siteRestrictionQuotientFiniteMeetPosetCategory_fromFiniteMeet` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteContextMorphismRolesConcrete` | `AAT.AG.FiniteModel.siteContextIdentityMorphism_rolesConcrete` | `propext` |
| `AAT.AG.AxiomAudit.canonicalTupleStandardFinitePosetCechComplexDComp` | `AAT.AG.Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex_differential_comp` | `propext`, `Classical.choice`, `Quot.sound` |

The audit list is intentionally additive. Later PRD-R hardening PRs must add
new wrappers when they promote theorem-package or firing-instance declarations
into the kernel-audited surface.

## R2 Atom hardening

R2 closes the Part I PRD-R items additively, preserving Research-imported
surfaces while adding concrete theorem counterparts.

| ID | Disposition | New evidence |
| --- | --- | --- |
| I-1 | 昇格 | `Formal/AG/Atom/ThreeReading.lean` adds `requiredLawWitnessFamily`, `requiredLawSignatureAxes`, `semanticLawful_iff_noRequiredObstruction_requiredLawWitness`, `semanticLawful_iff_requiredSignatureAxesZero_requiredLawAxes`, `noRequiredObstruction_iff_requiredSignatureAxesZero_requiredLaw`, and `concreteThreeReadingAgreement`. These theorems are proved from the required-law predicates themselves, not from `ThreeReadingAgreementAssumptions` fields. |
| I-1 firing | 発火 | `Formal/AG/Examples/FiniteModel.lean` adds `concreteNoCycleWitnessFamily`, `concreteNoCycleSignatureAxes`, `acyclic_concreteThreeReadingAgreement`, and `object_concreteThreeReadingAgreement_fires`. The cyclic object has an actual required-law bad witness; the acyclic object has no such witness. |
| I-2 | 昇格 | `AATCorePackage.AtomTowerRealization`, `ofAxiomRealization`, `exists_ofComponents_noHEq`, and `exists_ofAxiomRealization_noHEq` expose the `AtomAxiomSystem.configurationOf` bridge and provide HEq-free core existence statements. |
| I-2 firing | 発火 | `FiniteModel.atomTowerRealization`, `corePackageFromAxiomRealization`, and `corePackageFromAxiomRealization_exists_noHEq` instantiate the bridge on the finite Part I model. |
| I-3 | 実質化 | `AtomFamily.ListFinite`, `AtomConfiguration.Molecule.ListFinite`, and `ObstructionCircuit.ListFinite` provide explicit list-cover finite-support predicates. `FiniteModel.allFamily_listFinite`, `cycleObstructionCircuit_listFinite`, and `substitutionObstructionCircuit_listFinite` provide concrete finite support. |
| I-4 | 宣言 | `LawUniverse.coverageAssumptions` and `LawUniverse.exactnessAssumptions` remain frozen because `Formal/AG/Research` imports them directly. R2 does not use them for the concrete three-reading theorem; they remain selected assumption slots for the legacy packaged surface. |

## R3 Site adequacy hardening

R3 closes PRD-R II-1 additively. It preserves the existing
`WitnessClosureCover` surface and adds a seed-driven construction layer whose
support and axis assumptions live only on the seed index.

| ID | Disposition | New evidence |
| --- | --- | --- |
| II-1 | 昇格 | `Formal/AG/Site/Adequate.lean` adds `SeedWitnessClosureCover`, `SeedWitnessClosureCover.toWitnessClosureCover`, `SeedWitnessClosureCover.toAATCoverageFamily`, `SeedWitnessClosureCover.toAATCoverageFamily_admissible`, and `SeedWitnessClosureCover.uAdequate`. Required witness support and seed overlaps generate the closed index; the legacy `WitnessClosureCover` theorem remains the packaged compatibility surface. |
| II-1 firing | 発火 | `Formal/AG/Examples/FiniteModel.lean` adds `siteSeedWitnessClosureCover`, `siteSeedWitnessClosureCover_admissible`, and `siteSeedWitnessClosureCover_uAdequate` on the finite singleton site. |
| II-1 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteSeedWitnessClosureAdmissible` and `finiteSeedWitnessClosureUAdequate`, both guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| II-2 | 昇格 | `Formal/AG/Site/ContextCategory.lean` adds `contextMorphismPreorderCategory`, `productContextFiniteMeet`, `quotientLe`, `quotientMeet`, `quotientLe_wellDefined`, `quotientMeet_wellDefined`, `quotientFiniteMeetPosetCategoryOf`, and `minimalContextQuotientFiniteMeetPosetCategory_fromFiniteMeet`. The quotient poset is now constructed from preorder + finite-meet data, while the old `minimalContextQuotientFiniteMeetPosetCategory` remains a packaged compatibility surface. |
| II-2 firing | 発火 | `Formal/AG/Examples/FiniteModel.lean` adds `siteRestrictionQuotientFiniteMeetPosetCategory` and `siteRestrictionQuotientFiniteMeetPosetCategory_fromFiniteMeet` for the finite model's canonical restriction preorder. |
| II-2 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteRestrictionQuotientFiniteMeetPoset`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| II-3 | 実質化 | `Formal/AG/Site/Context.lean` makes `MinimalContext.supportReads_objectFamily` load-bearing and replaces the old free Prop role slots with external concrete predicates: `SupportMapPreservesReads`, `AxisMapPreservesReads`, `ObservableRestrictionFunctorial`, `SupportMapNonGenerating`, `AxisMapForgetsOnlyReadableAxes`, `SupportMapReflectsReads`, `AxisMapReflectsReads`, `SupportMapRefinesReads`, `AxisMapRefinesReads`, `BaseChangeCompatibleReads`, and `ContextMorphism.ConcreteRestriction` / `ConcreteProjection` / `ConcreteRefinement` / `ConcreteBaseChange`. |
| II-3 firing | 発火 | `Formal/AG/Examples/FiniteModel.lean` adds `siteContext_supportReads_objectFamily` and `siteContextIdentityMorphism_rolesConcrete`, showing the finite singleton context and its identity morphism satisfy the concrete restriction / projection / refinement / base-change roles. |
| II-3 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteContextMorphismRolesConcrete`, guarded at `propext`. |
| II-4 | 昇格 | `Formal/AG/Site/FinitePosetGeometry.lean` and `Formal/AG/Cohomology/FinitePosetStandardComplex.lean` expose the PRD-10 standard route: coefficient-free cover geometry, canonical tuple nerve, simplicial face action, standard alternating differential, double-face cancellation, `standardFinitePosetCechComplex`, and `canonicalTupleStandardFinitePosetCechComplex`. The old selected-data complex remains a packaged compatibility surface; the canonical tuple route provides the generated `d ∘ d = 0` theorem. |
| II-4 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `canonicalTupleStandardFinitePosetCechComplexDComp`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
