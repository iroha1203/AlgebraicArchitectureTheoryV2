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
| `^\s*[A-Za-z0-9_]+\s*:\s*Prop\b` | 415 | Pattern-level classification: `Prop` field / argument candidate は、PRD 表 item に対応するものを item-level に昇格・実質化・宣言・削除へ分類し、それ以外の theorem 系 row は三分化 overlay で `packaged (assumption-relative)` / `statement-only` / `defined only` boundary として分類する。 |
| `_holds\b\|_cert\b` | 1208 | Pattern-level classification: certificate/accessor surface。結論 field theorem は `packaged (assumption-relative)`、実述語 witness / finite firing は `proved`、candidate certificate は `statement-only` として二台帳 overlay と review layer 表で読む。 |
| `\bNonempty\b` | 48 | Pattern-level classification: `Nonempty` package candidate。空型 package は AC5/AC12/AC18 の item-level 補強で inhabitable selected fixture に置換し、witness package は selected finite fixture / packaged boundary として分類する。 |
| `native_decide` | 6 | R1 で全廃する kernel axiom audit gap。 |
| `comparisonName\s*:\s*String` | 1 | 表示名だけを持つ notation hypothesis field。`CechToSheafComparisonHypothesis` の semantic payload は `computesSpaceCohomology : Prop` とその proof であり、`comparisonName` 自体は theorem evidence ではない。 |
| `\bHEq\b` | 8 | AATCore / comparison provenance 周辺の review target。 |
| `∃\s*_,\s*True` | 0 | 現 pattern では no match。`Nonempty` / explicit `True` field 側で追跡する。 |
| combined pattern | 1685 | 上記を一つの alternation で数えた重複除去後のヒット行数。同一行が複数 pattern に該当するため、個別 count の単純和とは一致しない。 |

AC1/AC2 reproducibility note: the 1685 mechanical-hit lines are not copied into
this document one row at a time. They are classified by the pattern-level rules
above, by the Research freeze list, by the review-layer item table I-* through
IX-*, and by the row-level status overlay in `lean_theorem_index_ag_aat.md` and
`proof_obligations_ag_aat.md`. A theorem-row status in either AG ledger is read
through the R0 vocabulary table at the top of this inventory: actual theorem /
finite firing surfaces are `proved`; assumption/certificate/accessor packages
are `packaged (assumption-relative)`; candidate theorem statements are
`statement-only`; non-theorem carriers remain `defined only` or explicit future
proof obligations. This is the PRD-R AC1/AC2 classification ledger.

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
| II-2 | `ContextCategory.lean` 命題4.2 | 未達・降格記録 | R3 で restriction-morphism preorder、componentwise product meet、readable-equivalence quotient finite-meet poset construction は追加済み。ただしレビューで指摘された「命題4.2の空定理 / 昇格ラベル過大表示」は #3100 では未解消として降格記録する。旧 supplied package / accessor surface を theorem-grade completion evidence と数えない。 |
| II-3 | `Context.lean` morphism roles | 実質化 | R3 で `MinimalContext` の support reading を `A.configuration.family` に接続し、旧 free Prop role slots を `ContextMorphism` 外部の support / axis / observable / non-generation concrete predicate へ置換済み。 |
| II-4 | `FinitePoset.lean` 命題7.2C | 昇格 | R3 で PRD-10 標準複体 route を II-4 evidence へ接続済み。旧 selected data 版は packaged compatibility surface として明示。 |
| II-5 | `Examples/FiniteModel.lean` Part II examples | 発火 | singleton / True 例から 2 patch + overlap finite site へ進める。 |
| II-6 | `Topology.lean` Mathlib coverage bridge | 発火 | R3 で singleton finite equality-thin site の `HasPullbacks` / `IsStableUnderBaseChange` instance と bridge firing theorem を追加済み。 |
| III-1 | `Correspondence.lean` 定理11.1 | 昇格 | R4 で `SelectedLawWitnessIdealFamily.localObstructionIdeal` / selected witness ideals / PRD-10 R5 `LawEquation` への片方向 bridge と finite firing theorem を追加済み。旧 `witnessCoverage` package は compatibility surface として残る。 |
| III-2 | `LawfulLocus.lean` factorization | 昇格 | R4 で `PrimeSpectrum.comap` による section prime map と、消滅から zeroLocus image containment への片方向 theorem を追加済み。逆向き radical gap は非主張として台帳化。 |
| III-3 | `StructureSheaf.lean` sheafification bridge | 昇格 | R4 で明示 `HasSheafify` 仮定下の Mathlib sheafification universal property theorem と `LawAlgebraSheafificationBridge` constructor を追加済み。`AATCommAlgCat` の無条件 instance は非主張として残す。 |
| III-4 | `Scheme.lean` chart compatibility | 実質化 | R4 で単一 affine chart の Mathlib `Spec` locally ringed space reading、identity self-chart compatibility witness、single-affine `ArchitectureScheme` constructor を追加済み。一般 atlas gluing / Mathlib open immersion theorem は非主張として残す。 |
| III-5 | `Nullstellensatz.lean` NSdepth | 実質化 | R4 で selected generator family、finite linear-combination unit certificate、display degree、generator-backed `NSdepthProfile` への forgetful bridge、concrete `NSdepth = 1` firing を追加済み。一般 Nullstellensatz 証明・radical algorithm completeness は非主張として残す。 |
| IV-1 | `CechComplex.lean` | 昇格 | R5 で `d ∘ d = 0` を使う additive cocycle / coboundary subgroup、additive `H^1 = Z^1/B^1` surface、class vanishing iff coboundary、legacy quotient relation との bridge theorem を追加済み。 |
| IV-2 | `FiniteExamples.lean` pseudo circle | 発火 | R5 で Part IV pseudo-circle 用 `PartIVCircleNonzeroH1Firing` package と、PRD-10 circle nonzero H1 instance からの firing theorem を追加済み。 |
| IV-3 | `LocalFlatnessGap.lean` 定理7.1 | 昇格 | R5 で finite overlap-wise global lawful restriction/coboundary soundness から coboundary soundness package と theorem 7.1 へ入る bridge を追加済み。一般 descent theorem は非主張として残す。 |
| IV-4 | `FlatnessCriterion.lean` 定理11.1 | 昇格 | R5 で additive `H^1` vanishing と `∃ t, g = d⁰t` の同値、および concrete finite `C⁰` adjustment surface `g - d⁰t = 0` から finite adjusted global lawful-section condition への同値 route を追加済み。一般 site 版は packaged theorem として残す。 |
| IV-5 | `CoverNerve.lean` 12.* | 昇格 | R5 で finite cochain complex `ker d1 / im d0` からの rank-nullity lower bound と、finite forest edge-support absorption certificate からの selected `H^1 = 0` theorem を追加済み。旧 selected data 版は compatibility surface として残す。 |
| IV-6 | `Formal/AG/Cohomology/ObstructionSheaf.lean` `DerOb_U` | 昇格 | R5 で opaque placeholder を除去し、`ConDef_U = I_U/I_U^2` と係数 module `M` からなる selected naive cotangent-coefficient carrier として透明化済み。一般 cotangent complex / derived category / `Ext^1` 構成は非主張として残す。 |
| IV-7 | `BoundaryResidue.lean` / `PeriodStokes.lean` | 昇格 / 13.2 alias整理 | `TwoChartGloballyUFlat D b` を `∃ s, b.b_U = d0 s ∧ d0 s = 0` に強め、単なる `∃ s, d0 s = 0` ではなく selected boundary mismatch に相対化した。`TwoChartBoundaryResolved` は `b_U = d0 s` の解消 predicate として残し、global U-flatness はその zero-boundary 強化として読む。`HolonomyKernelExactAtBoundary`、`DeltaKillsTwoChartBoundaries`、`boundaryResolved_of_boundaryHolonomy_zero_of_kernelExact` / `boundaryHolonomy_zero_of_boundaryResolved_of_deltaKillsBoundaries` / `not_boundaryResolved_of_boundaryHolonomy_nonzero_of_deltaKillsBoundaries` と `AxiomAudit.boundaryResidueTwoChartBoundaryResolved*` により、holonomy completeness/soundness 側を `BoundaryResidueHypotheses` の free field ではなく `ker(deltaH1) <= im(d0)` / `deltaH1 ∘ d0 = 0` の concrete exactness predicate から読む route に昇格した。13.2 の `finiteIntervalConnectingStokes_basis` は `finiteIntervalStokes_basis` の改名 alias なので、AxiomAudit では `finiteIntervalStokesBasis` だけを監査し、2 theorem と数えない。任意 cover の自動 Stokes 構成と derived Mayer-Vietoris triangle は PRD-R IV-7 の外側の非主張境界として残す。 |
| IV-8 | `ObstructionSheaf.lean` Type-valued sheaf | 実質化 | AddCommGrpCat constructor 側を正とし既存 surface は凍結。 |
| V-1 | `Counterexample.lean` Tor1 nonzero | 実装済み(#3098) | `k = ZMod 2`、`R=(ZMod 2)[x,y,z]` に固定し、`principalProjectiveResolutionV2`、`[y] ⊗ 1` の cycle / not-boundary、Mathlib projective-resolution Tor iso から `example56_zmod2_mathlibTor1_nonzero` を証明済み。任意 `CommRing k` の非零性は主張しない。 |
| V-2 | `Intersection.lean` Tor0 bridge | 実装済み(#3098) | Mathlib `Tor_0` zero-th left-derived/tensor 同型と quotient tensor 同型から `canonicalSelectedTorBridge` と canonical `LawConflictPackage` route を構成し、定理6.1 / 7.3(V) surface と AxiomAudit で発火済み。 |
| V-3 | `TaylorResolution.lean` | 昇格 | `TwoGeneratorPresentation`、`face_card_le_two`、`selected_pair_multidegree_eq_union`、`TwoGeneratorTaylorResolutionPackage`、`resolvesQuotient_from_selectedExactBridge` を追加し、2生成 presentation の Taylor face cardinality と selected exactness bridge から quotient-resolution を読む assumption-relative theorem surface を導入。さらに `TwoGeneratorPrincipalTaylor.d₂` / `d₁` で `A -> A^2 -> A` の concrete 2生成 Taylor/Koszul 微分を実構成し、`d₁ ∘ d₂ = 0`、`PrincipalSyzygyExact a b` からの `exact_visible_complex`、regular pair 条件 `IsRegularPair a b` から syzygy exactness を証明する `principalSyzygyExact_of_isRegularPair`、`range_d₁_eq_spanPair`、`quotientLinearEquivIdealSpanPair : coker(d₁) ≃ₗ[A] A/(a,b)`、`exact_visible_complex_of_isRegularPair` を追加した。さらに具体係数環 `(ZMod 2)[x₀,x₁]` の pair `(X 0, X 1)` について `zmod2XY_isRegularPair` と `zmod2XY_exact_visible_complex` を証明し、`AxiomAudit.twoGeneratorPrincipalTaylorExactVisible` / `twoGeneratorPrincipalTaylorExactVisibleOfRegularPair` / `twoGeneratorPrincipalTaylorZMod2XYExactVisible` で標準公理範囲を固定した。任意係数環・任意2生成 monomial presentation からの一般 Taylor 自動構成は PRD-R V-3 の外側の非主張境界として残す。 |
| V-4 | `FreeResolution.lean` exact field | 実装済み | `SelectedFiniteFreeResolution.exact` を `Function.Exact (d 0) augmentation ∧ ∀ n, Function.Exact (d n.succ) (d n)` に置換し、augmentation / positive degree exactness accessor を追加済み。 |
| V-5 | mislabeled / content-free theorems | 削除 / 実質化 | `sharedWitnessG5_window_interference_zero` と `finite_trace_certificate` は削除済み。theorem-grade 主張は `sharedWitnessG5_all_degree_coefficient_identity` / `sharedWitnessG5_window_identity` / `SoundRepairSynthesisPackage.output_cleared_or_noSolution` 側で読む。 |
| V-6 | `HilbertSeries.lean` | 実装済み | `HilbertSeriesBasisCountPackage` と shared-witness の ambient / quotient / joint / Tor-one basis-count package を追加し、係数を各次数の selected finite monomial basis cardinality として読む。 |
| V.R11 | `Examples/DerivedPart5.lean` repair synthesis fixtures | 未達・降格記録 | `smallRepairClearedSynthesis` / `smallRepairNoSolutionSynthesis` は finite trace と output theorem を持つが、`emitsOnlySoundStepsOrNoSolutionCertificate := True` / `_holds := trivial` が残る。#3100 では theorem-grade sound-step emission evidence へ昇格していないため、定理13.4の実発火 evidence ではなく fixture 限定の未達項目として降格記録する。 |
| VI-1 | Part VI toy models | 実装済み | #3099 で `Bool` / `Fin 2` ベースの concrete nondegenerate data instance を追加し、singular boundary、operation square、transport zero/nonzero、refactor Galois、decomposition gerbe の5 toy model firing theorem を発火済み。#3139 追補で `toyBoundaryObstruction_nonzero`、`toyOperationCategory_operation_nontrivial`、`toyPresentedPi_pi1_nontrivial`、`toyTransportDescent_square_nontrivial`、`toyRefactorGroupoid_hom_carries_state_equality`、`toyDecompositionGroupoid_hom_carries_object_equality` と対応する AxiomAudit entries を追加し、`PUnit` / `True` / `False` だけの空 witness を completion evidence から排除した。 |
| VI-2 | `OperationHomotopy.lean` pi1 | 昇格 | R8 で `FreeEdgeWord.toFreeGroup` / `PresentedArchitectureFundamentalGroup.presentedRelators` / `pi1AAT` を追加し、Mathlib `PresentedGroup` の relator identity と `toGroup` universal property へ bridge 済み。既存 package API は compatibility surface として残る。 |
| VI-3 | `ArchitectureStack.lean` | 実装済み | `ArchitectureStackBase` に triple-overlap context と pairwise overlap への restriction arrow を追加し、`TripleOverlapCocycle` / `ArchitectureStack.tripleCocycle_eq` で `ij ≫ jk = ik` の実等式 witness を保持する。 |
| VI-4 | `CotangentInterface.lean` / `Kuranishi.lean` | 実装済み | `CotangentData.ofConDef` で IV-6 `ConDef_U = I_U/I_U²` を selected cotangent carrier として読み、`TangentData.ofDerOb` で `DerOb_U` を obstruction target とする bridge を追加済み。 |
| VI-5 | `Formal/AG/SingularityMonodromyStack/DecompositionGerbe.lean` | 宣言 | B項目。現 R0 では soundness / nonzero が supplied boundary であることを公理的境界として明示し、昇格可能性は後続 Issue の判断に残す。 |
| VII-1 | `Synthesis.lean` theorem 16.1 | 未達・降格記録 | R9 で `Formal/AG/Examples/RepresentationAnalysisPart7.lean` に `finiteSynthesisAATSynthesisAssumptions` / `finiteSynthesisAATSynthesisPackage` / `finiteSynthesis_algebraicGeometricAATSynthesis_fires` を追加したが、現 fixture は PUnit / singleton 係数の限定発火で、#3100 の theorem-grade evidence としては未達に降格する。同ファイルの `marginDistanceToFlatness.costToDistanceValue _ := measured 0` は定数後退のままなので、忠実な `ENat` reading へは未昇格として記録する。 |
| VII-2 | `AATSch.lean` | 実装済み | `AATSchReadingParameter` 側に fixed compatibility predicate と identity / composition closure を移し、`Category (AATSch p)`、target `Category` wrapper、`AnalyticRepresentation.toFunctor` bridge を追加した。ローカル検証は targeted Lean checks に限定し、full `lake build` / `FormalAGResearch` は PR CI gate で確認する。 |
| VII-3 | `FiniteHomology.lean` strict period | 昇格 | `ZeroChainCompatiblePairing` と `coboundary_pair_eq_zero_on_closed_chain` を追加し、Stokes-compatible pairing と zero-chain equation から closed chain 上の coboundary pairing が実際に 0 になることを証明済み。 |
| VII-4 | `AnalyticContext.lean` theorem 15.4 | 昇格 | `RepresentationConservativityUnderAdequacy` が adequacy 4条件、`WitnessZero_U alpha -> alpha = zeroClass`、および `IsZeroClass zeroClass` を保持し、全 selected reading zero から `alpha = zeroClass` と `IsZeroClass alpha` を証明する。Part VII toy example も actual-zero theorem を発火済み。 |
| VII-5 | `DistanceFlatnessMass.lean` | 実装済み | `CostInfimumDomain.completeLatticeInfimumDomain` を追加し、example の fake `True` GLB を `ℕ∞` 上の Mathlib `iInf` / actual lower-bound GLB に置換済み。 |
| VII-6 | `GraphMatrix.lean` walk count | 部分昇格(B項目境界) | `edgeFiberCard`、`adjacencyMatrix_apply_eq_edgeFiber_card`、`matrixWalkCount_one_eq_edgeFiber_card` を追加し、length-one walk count を selected edge-fiber cardinality へ接続。Part VII toy DAG で `dependencyDAG_length_one_walkCount_eq_edgeFiber_card` と `dependencyDAG_ab_edgeFiber_card` を発火済み。一般 length-n walk cardinality theorem は未主張。 |
| VIII-1 | `Hodge.lean` 8.5/8.6/8.7 | 実装済み | `RealFiniteInnerProductComplex`、Mathlib `LinearMap.adjoint` 由来の adjoint、`RealFiniteHodgeDecomposition`、`RealHarmonicDebtMinimality`、`RealEssentialRepairLowerBound` を追加し、finite real inner-product complex 上の分解・harmonic debt norm・補正 residual 最小性・repair lower-bound inequality を load-bearing bridge に昇格した。 |
| VIII-2 | `SquareFreeRepair.lean` theorem 5.2 | 実装済み | PRD-3 `SquareFreeWitnessRegime` の Stanley-Reisner theorem を `SquareFreeRepairRegime.sourceWitnessRegime` へ再利用し、finite Alexander dual face predicate と minimal hitting-set bridge を Lean theorem surface にした。 |
| VIII-3 | `FiniteRegime.lean` / `Computability.lean` | 実装済み | `EffCoeff` と finite computation objects に `Fintype` carrier を追加し、`FiniteAATComputability.*CarrierFintype` / `computationCarriers_finite` で selected finite carrier を Prop でなく actual finite type として読む。 |
| VIII-4 | `LawConflict.lean` | 実装済み | `LawConflictMeasurement.ofDerivedLawConflictPackage` と `derivedLawConflictLinearEquivMathlibTor` を追加し、Part V `Derived.Intersection.LawConflictPackage` から Measurement の LawConflict reading と Mathlib Tor bridge を構成する。 |
| VIII-5 | `Packet.lean` / `GAGA.lean` | 実装済み(#3100追補) | `SelectedFiniteHodgeTheoremPackage` と `AATGAGACertifiedFields.finiteHodgeTheoremPackage` に加え、`SelectedPeriodStokesTheoremPackage`、`SelectedTopologicalDebtTheoremPackage`、`SelectedDerivedConflictTheoremPackage` と certified field slots / accessors を追加。Period/Stokes は selected `ExtensionHolonomyAccounting` と `period_stokes_accounting_additive` / `AATGAGACertifiedFields.periodStokesAccountingAdditive_holds` により実 additive theorem を読む。topological debt は selected `FiniteNerveCochainComplex` と `topological_debt_capacity_from_complex` / `AATGAGACertifiedFields.topologicalDebtCapacityFromComplex_holds` により `topologicalDebtCapacity_fromComplex` を読む。low-degree example と `AxiomAudit.gagaLowDegreePeriodStokesAccountingAdditive` / `gagaLowDegreeTopologicalDebtCapacityFromComplex` で発火済み。一般 Stokes pairing theorem や任意 cover 自動構成は未主張。 |
| VIII-6 | `Examples.lean` | Hodge / Alexander dual 実装済み | Hodge fixture は `LowDegreeRealCochain = EuclideanSpace ℝ (Fin 3)` の zero differential complex で発火し、`lowDegreeRealHodgeDecomposition`、`lowDegreeRealHarmonicDebtMinimality`、`lowDegreeRealEssentialRepairLowerBound` で 8.5/8.6/8.7 を実インスタンス化した。5.2 / Alexander dual fixture は `{p,q}` / `{q,r}` forbidden supports と `{q}` / `{p,r}` minimal finite hitting-set proofs で発火する。 |
| IX-1 | `ReplayDescent.lean` theorem 4.2 | 実装済み | `TemporalDescentRealization` と `TemporalDescentCriterion.ofRealization` を追加し、class vanishing と adjusted replay compatibility から selected global replay transition を構成する bridge として発火する。 |
| IX-2 | `Force.lean` candidate 7.2 | 実装済み | `IntegrableForce` は R5 `ReplayDescentData` / `TemporalDescentCriterion` / selected `GlobalReplayTransition` と selected `TemporalLaw.stateEquation` に接続された `ForceIntegrationData` の `Nonempty` になった。`ForceIntegrabilityObstructionCandidateData` は証明済み非可積分性を要求しない inhabitable candidate-data layer として追加され、finite fixture では selected nonzero marker を concrete `ZMod 2` obstruction value に backed している。旧 `ForceIntegrabilityObstructionCandidate` は theorem-candidate / future proof obligation 境界に残る。 |
| IX-3 | temporal product cohomology | 実装済み(#3100追補) | `TemporalCoefficient.FiberZeroCochain` / `FiberIncidenceOneCochain` / `incidenceDifferential` / `incidenceDifferential_id`、`ProductIncidenceComplex`、`ProductIncidencePRD4Comparison`、`FinitePosetTemporalCechBridge.cohomology_to_from` / `cohomology_from_to` は存在する。ただし Part IX two-step `unitProductIncidencePRD4Comparison` は `PUnit` singleton 係数の wrapper で、cohomology-level inverse theorem は `finitePosetBridge` accessor の射影に留まるため、完了証拠にしない。補強証拠として `EvolutionPart9.zmod2TemporalCoefficient` / `zmod2TemporalProductIncidenceComplex` / `zmod2TemporalSeparatedCochain` / `zmod2TemporalProductIncidence_d0_step_nonzero` / `zmod2TemporalProductIncidence_d0_step_ne_zero` を追加し、さらに `zmod2TemporalProductCoverRelativeCover` / `zmod2TemporalProductCoverRelativeComplex` / `zmod2TemporalProductIncidenceThreeTerm` / `zmod2TemporalProductCoverRelativeEquivalence` / `zmod2TemporalProductCoverRelativeH1_to_from` / `zmod2TemporalProductCoverRelativeH1_from_to` により、非自明 `ZMod 2` product-incidence surface から PRD-4 cover-relative H¹ comparison-level inverse を cochain-level equivalence 由来で生成する。追加で `zmod2TemporalIdentityLegH1Class_ne_zero` が `incidenceDifferential_id` を使って identity-leg-detected 1-cochain の H¹ class 非零性を証明し、`AxiomAudit.zmod2TemporalIdentityLegH1ClassNeZero` で kernel 監査対象にする。 |
| IX-4 | `TemporalLaw.lean` definition 3.3 | 実装済み | `TemporalLaw.ofStateEquation` と kind 別 canonical constructors、`ofStateEquation_kind` / `ofStateEquation_holdsStateEquation`、`EvolutionPart9.temporalLaw_kind` / `temporalLaw_stateEquation` を追加済み。 |
| IX-5 | `Examples/EvolutionPart9.lean` | 実装済み | two-chart finite replay fixture は theorem 4.2 を発火する。`selectedConcreteClassNonzero := True` は `pseudoCircleMismatch replayDescentNonzeroExample.edge ≠ 0` と `replay_selectedConcreteClassNonzero` に置換し、`replay_nonzero_and_prd10_circle_coverRelativeH1_nonzero` で PRD-10 circle/Part IV nonzero H1 instance と同じ theorem surface に束ねた。 |

## Old PRD AC reclassification

旧 PRD 1-9 の acceptance criteria は、PRD-R では次のように再判定する。

| PRD | AC item | Reclassified AC text | R0 tag | Evidence |
| --- | --- | --- | --- | --- |
| PRD-1 | AC11 | 旧 `ThreeReadingAgreementAssumptions` 版は explicit package field 由来。PRD-R R2 で required-law concrete counterpart が証明済み。 | `proved` / `packaged (assumption-relative)` | `Formal/AG/Atom/ThreeReading.lean`, `concreteThreeReadingAgreement`, `ThreeReadingAgreementAssumptions.*` |
| PRD-1 | AC13 | 旧 `exists_ofComponents` は selected components を束ねる theorem package。PRD-R R2 で `AtomTowerRealization` と HEq-free counterpart が証明済み。 | `proved` / `packaged (assumption-relative)` | `Formal/AG/Atom/AATCore.lean`, `exists_ofAxiomRealization_noHEq`, `AATCorePackage.*` |
| PRD-2 | AC5 | PRD-R R3 で seed-side support / axis coverage、required witness support、seed-overlap boundary visibility から closed admissible cover と `U`-adequacy を構成する additive counterpart を証明済み。旧 `WitnessClosureCover` 版は Research-compatible packaged surface として残る。 | `proved` / `packaged (assumption-relative)` | `Formal/AG/Site/Adequate.lean`, `SeedWitnessClosureCover.toAATCoverageFamily_admissible`, `SeedWitnessClosureCover.uAdequate`, `witnessClosureCover_uAdequate` |
| PRD-2 | AC11 | finite model examples は selected finite fixtures に相対化される。PRD-R R3 II-5 で singleton fixture に加えて two-patch + overlap finite site firing、unit descent、selected sheafification gap、nonzero Boolean Čech differential calculation を追加済み。 | `proved` / `packaged (assumption-relative)` | `Formal/AG/Examples/FiniteModel.lean`, `siteSingletonCover_uAdequate`, `twoPatchCover_uAdequate`, `twoPatchUnit_descent`, `twoPatchSheafificationGap`, `twoPatchSeparatedCochain_differential_nonzero` |
| PRD-3 | AC12 | Nullstellensatz candidate は statement surface に留まり、証明済み theorem ではない。 | `statement-only` | `Formal/AG/LawAlgebra/Nullstellensatz.lean`, `ArchitectureNullstellensatzCandidate` |
| PRD-3 | AC18 | 定理11.1 Lawfulness-Ideal Correspondence は selected witness / coverage package に相対化される。 | `packaged (assumption-relative)` | `Formal/AG/LawAlgebra/Correspondence.lean` |
| PRD-4 | AC3 / AC4 | Čech complex / finite-poset comparison は selected complex data と explicit d^2 field に相対化される。 | `packaged (assumption-relative)` | `Formal/AG/Cohomology/CechComplex.lean`, `Formal/AG/Cohomology/FinitePosetComparison.lean` |
| PRD-4 | AC11 / AC13 | flatness criterion and pseudo-circle H1 example are package/fixture-relative. | `packaged (assumption-relative)` | `Formal/AG/Cohomology/FlatnessCriterion.lean`, `Formal/AG/Cohomology/FiniteExamples.lean`, `CoverRelativeH1NonzeroWitness` |
| PRD-5 | AC5 / AC6 | finite free / Taylor resolution exactness contains package assumptions to be hardened. | `packaged (assumption-relative)` | `Formal/AG/Derived/TaylorResolution.lean`, `Formal/AG/Derived/FreeResolution.lean` |
| PRD-5 | AC16 | 例5.6 `Tor1` nonzero fixture is proved as a `ZMod 2` concrete counterexample theorem. | `proved concrete ZMod 2 theorem` | `Formal/AG/Derived/Counterexample.lean`, `example56_zmod2_mathlibTor1_nonzero`; 任意 `CommRing k` の非零性は非主張。 |
| PRD-6 | AC10 / PRD-R AC11 | `pi1^AAT` universal property is bridged to Mathlib `PresentedGroup` and `PresentedGroup.toGroup` uniqueness. | `proved PresentedGroup bridge` / `compatibility package` | `Formal/AG/SingularityMonodromyStack/OperationHomotopy.lean`, `PresentedArchitectureFundamentalGroup.pi1AAT`, `presentedGroupLift_unique` |
| PRD-6 | AC20 | five finite toy models are selected finite witness packages. R7 で transport descent の空型 package は zero/nonzero case へ分割済み。#3139 review follow-up で singular boundary は concrete `ob true != zeroObstruction`、operation category は nontrivial Bool operation carrier、operation-square filling は `mu axis = 0`、transport factorization は nontrivial `Multiplicative (ZMod 2)` pi1 と Bool square / Bool quotient transport、refactor Galois arrow は state-equality-carrying finite hom、decomposition gerbe obstruction は `gerbeClass = zero` の否定として発火し、`False` / `True` / `PUnit` だけの空 witness ではなくなった。 | `proved example theorem` / `selected finite witness package` | `Formal/AG/Examples/SingularityMonodromyStackPart6.lean`, `toyBoundaryObstruction_nonzero`, `toyOperationCategory_operation_nontrivial`, `toyPresentedPi_pi1_nontrivial`, `toyTransportDescent_square_nontrivial`, `toyRefactorGroupoid_hom_carries_state_equality`, `toyDecompositionGroupoid_hom_carries_object_equality` |
| PRD-7 | AC8 | strict period well-definedness is selected finite homology data relative. | `packaged (assumption-relative)` | `Formal/AG/RepresentationAnalysis/FiniteHomology.lean` |
| PRD-7 | AC19 | AAT synthesis theorem package now has finite model firing. | `proved finite synthesis firing` / `packaged theorem` | `Formal/AG/RepresentationAnalysis/Synthesis.lean`, `AATSynthesisPackage`, `Formal/AG/Examples/RepresentationAnalysisPart7.lean`, `finiteSynthesisAATSynthesisPackage` |
| PRD-8 | AC8 / AC14 / AC15 / AC16 | theorem 5.2 is connected to PRD-3 Stanley-Reisner assets and finite Alexander dual / hitting-set proofs; Hodge 8.5/8.6/8.7 has a real finite inner-product bridge and 3D fixture firing. | `Hodge implemented` / `theorem 5.2 SR-Alexander bridge implemented` | `Formal/AG/Measurement/SquareFreeRepair.lean`, `Formal/AG/Measurement/Hodge.lean`, `Formal/AG/Measurement/Examples.lean` |
| PRD-8 | AC9 / AC10 / AC17 | stability / spectral / base-change candidates remain statement-only. | `statement-only` | `Formal/AG/Measurement/Stability.lean`, `Formal/AG/Measurement/Hodge.lean`, `Formal/AG/Measurement/LawConflict.lean` |
| PRD-9 | AC13 / PRD-R AC17 | theorem 4.2 Temporal Descent Criterion is selected temporal realization relative and fires on a finite two-chart adjusted replay fixture. | `proved selected realization bridge` / `proved finite fixture` | `Formal/AG/Evolution/ReplayDescent.lean`, `Formal/AG/Examples/EvolutionPart9.lean`, `TemporalDescentRealization`, `zeroReplayTemporalDescentRealization` |
| PRD-9 | AC20 | finite temporal examples include selected / degenerate fixtures, force integration data, and concrete-value-backed inhabitable force candidate data. | `packaged (assumption-relative)` / `inhabitable candidate data` / `statement-only theorem candidate` | `Formal/AG/Examples/EvolutionPart9.lean`, `ForceCandidateFixture`, `toyForceIntegrationData`, `force_candidate_selected_nonzero_backed_by_concrete`, `force_candidate_data_inhabited`; `Formal/AG/Evolution/Force.lean`, `ForceIntegrabilityObstructionCandidateData`, `ForceIntegrabilityObstructionCandidate` |

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

Audit mechanism: every declaration in the `AAT.AG.AxiomAudit` namespace is
checked by the `#assert_standard_axioms_only` command
(`Formal/Util/AssertStandardAxioms.lean`) at the end of the file. The machine
guarantee is an allowlist: each entry depends on at most
`propext`, `Classical.choice`, `Quot.sound` (in particular no `sorryAx`,
no `Lean.ofReduceBool`, no custom `axiom`). Adding a declaration to the
namespace is sufficient to place it under the audit; per-entry
`#guard_msgs in #print axioms` blocks are not used. CI also checks textually
that the command remains the last non-empty line of the file.

R1 tracked declarations. The axiom-set column records the exact set observed
when the entry was introduced; the machine-enforced invariant is
"within the standard three axioms", not the exact per-entry set:

| Audit wrapper | Source declaration | Axiom set at introduction |
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
| `AAT.AG.AxiomAudit.finiteTwoPatchCoverUAdequate` | `AAT.AG.FiniteModel.twoPatchCover_uAdequate` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteTwoPatchUnitDescent` | `AAT.AG.FiniteModel.twoPatchUnit_descent` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteTwoPatchSheafificationGap` | `AAT.AG.FiniteModel.twoPatchSheafificationGap` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteTwoPatchCechDifferentialNonzero` | `AAT.AG.FiniteModel.twoPatchSeparatedCochain_differential_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteSiteTopologyEqCoverageToGrothendieck` | `AAT.AG.FiniteModel.siteTopology_eq_coverage_toGrothendieck` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteAcyclicLocalSectionLawfulFromWitnessIdeals` | `AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSection_lawful_from_witnessIdeals` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteAcyclicSectionPrimeMapMemLocalLawfulLocus` | `AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_sectionPrimeMap_mem_localLawfulLocus` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.structureSheafMathlibSheafificationLiftUnique` | `AAT.AG.LawAlgebra.LawAlgebraSheafificationBridge.mathlib_sheafification_lift_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.schemeSingleAffineSpecCompatibilityAllConditions` | `AAT.AG.LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec_compatibility_allConditions` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteConcreteGeneratorUnitCertificateOneMemSpan` | `AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorUnitCertificate_one_mem_span` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteConcreteGeneratorNSdepthEqOne` | `AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorNSdepth_eq_one` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.coverRelativeCohomologyClassSuccEqIffAdditiveH1ClassEq` | `AAT.AG.Cohomology.CoverRelativeCechComplex.cohomologyClassSucc_eq_iff_additiveH1Class_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.canonicalTupleStandardFinitePosetCechComplexDComp` | `AAT.AG.Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex_differential_comp` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.coverNerveTopologicalDebtCapacityFromComplex` | `AAT.AG.Cohomology.FiniteNerveCochainComplex.topologicalDebtCapacity_fromComplex` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.boundaryResidueTwoChartBoundaryAgreementSoundness` | `AAT.AG.Measurement.boundaryResidue_twoChart_boundaryAgreement_soundness` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.boundaryResidueTwoChartBoundaryResolvedCompleteness` | `AAT.AG.Measurement.boundaryResidue_twoChart_boundaryResolved_completeness` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.boundaryResidueTwoChartBoundaryResolvedSoundness` | `AAT.AG.Measurement.boundaryResidue_twoChart_boundaryResolved_soundness` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteIntervalStokesBasis` | `AAT.AG.Measurement.finiteIntervalStokes_basis` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.gagaLowDegreePeriodStokesAccountingAdditive` | `AAT.AG.Measurement.gagaLowDegreePeriodStokesAccounting_additive` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.gagaLowDegreeTopologicalDebtCapacityFromComplex` | `AAT.AG.Measurement.gagaLowDegreeTopologicalDebtCapacity_fromComplex` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteForestEdgeAbsorptionVanishing` | `AAT.AG.Cohomology.FiniteForestEdgeAbsorptionData.forestVanishing` | `propext` |
| `AAT.AG.AxiomAudit.derObUOfConDefCoefficientConDefClass` | `AAT.AG.Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient_conDefClass` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.derObUOfConDefCoefficientCoefficient` | `AAT.AG.Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient_coefficient` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.example56LawConflictPackageFiringLawConflict1Nonzero` | `AAT.AG.FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.lawConflict1_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.example56LawConflictPackageFiringTor1Nonzero` | `AAT.AG.FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.tor1_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.example56ZMod2MathlibTor1Nonzero` | `AAT.AG.Derived.Counterexample.SharedWitnessCoord.example56_zmod2_mathlibTor1_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.example56LawConflictPackageFiringDerivedNonTransverse` | `AAT.AG.FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.derivedNonTransverse` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.example56LawConflictPackageFiringDerivedTransversalityCriterion` | `AAT.AG.FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.derivedTransversalityCriterion` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.example56LawConflictPackageFiringPositiveTorVanishingIffClassicalAgreement` | `AAT.AG.FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.positiveTorVanishing_iff_classicalAgreement` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.canonicalSelectedTorBridgeLawConflict0AlgEquivClassicalJoint` | `AAT.AG.FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.lawConflict0AlgEquivClassicalJoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.canonicalSelectedTorBridgeLawConflict0LinearEquivMathlibTor` | `AAT.AG.FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.toDirectTorCalculation` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.twoGeneratorPrincipalTaylorExactVisible` | `AAT.AG.Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.exact_visible_complex` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.twoGeneratorPrincipalTaylorExactVisibleOfRegularPair` | `AAT.AG.Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.exact_visible_complex_of_isRegularPair` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.twoGeneratorPrincipalTaylorZMod2XYExactVisible` | `AAT.AG.Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2XY_exact_visible_complex` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVISingularBoundaryConcrete` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteSingularBoundaryToyModel_fires` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVISingularBoundaryConcreteNonzero` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBoundaryObstruction_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIOperationCarrierNontrivial` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOperationCategory_operation_nontrivial` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIOperationSquareConcrete` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteOperationSquareToyModel_fires` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIPresentedPiNontrivial` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi_pi1_nontrivial` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVITransportSquareNontrivial` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescent_square_nontrivial` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVITransportZeroConcrete` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentZero_descends` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVITransportNonzeroConcrete` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentNonzero_not_descend` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIRefactorGaloisConcrete` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteRefactorGaloisToyModel_fires` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIRefactorHomCarriesStateEquality` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid_hom_carries_state_equality` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIDecompositionGerbeConcrete` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteDecompositionGerbeToyModel_fires` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIDecompositionHomCarriesObjectEquality` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid_hom_carries_object_equality` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVICotangentConDefBridge` | `AAT.AG.SingularityMonodromyStack.CotangentData.ofConDef_cotangentComplex_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.partVIDerObObstructionTargetBridge` | `AAT.AG.SingularityMonodromyStack.TangentData.ofDerOb_obstructionTarget_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairTheorem34FiniteDescentPackage` | `AAT.AG.SemanticRepair.finiteSemanticRepairGluingDescent_package` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairTheorem48TrueSheafH1Gluing` | `AAT.AG.SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.globalRepairCoherent_iff_additiveH1Zero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairTheorem72H1ComparisonPackage` | `AAT.AG.SemanticRepair.SemanticRepairCoverRelativeH1Comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_package` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairTheorem73GroundedGlobalGluingPackage` | `AAT.AG.SemanticRepair.trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairTheorem75NativeGeneratedEndToEndFromNativeGeneratedInputs` | `AAT.AG.SemanticRepair.lawEquation_constructs_groundedComparisonPacket_fromNativeGeneratedInputs` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairExample91GeneratedLawQuotientNontrivial` | `AAT.AG.Examples.SemanticRepairPart10.generatedLawQuotientNontrivial` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairExample91GeneratedLawCircleSemanticH1Nonzero` | `AAT.AG.Examples.SemanticRepairPart10.generatedLawCircleSemanticH1_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairExample91GeneratedLawQuotientEndToEndFromNativeGeneratedInputs` | `AAT.AG.Examples.SemanticRepairPart10.lawfulFiring_generatedLawQuotient_endToEndPacket_fromNativeGeneratedInputs` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairExample91GeneratedLawCircleQuotientEndToEndFromConstructedInputs` | `AAT.AG.Examples.SemanticRepairPart10.lawfulFiring_generatedLawCircleQuotient_endToEndPacket_fromConstructedInputs` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.semanticRepairTheorem81DegreeZeroLawContribution` | `AAT.AG.SemanticRepair.displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.presentedArchitectureFundamentalGroupRelatorMapsToIdentity` | `AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelator_maps_to_identity` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.presentedArchitectureFundamentalGroupLiftOf` | `AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift_of` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.presentedArchitectureFundamentalGroupLiftUnique` | `AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.transportDescentZeroToyModelNonempty` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.nonempty_of_relationBoundaryZero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.transportDescentNonzeroToyModelNonempty` | `AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.nonempty_of_not_relationBoundaryZero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteSynthesisAATSynthesisPackageEqToPackage` | `AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisAATSynthesisPackage_eq_toPackage` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.finiteSynthesisFires` | `AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesis_algebraicGeometricAATSynthesis_fires` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.lowDegreeRealKernelEquivHarmonic` | `AAT.AG.Measurement.lowDegreeRealComplex_kernel_equiv_harmonicCohomology` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.nonzeroBoundaryRealComplexDPrevNonzero` | `AAT.AG.Measurement.nonzeroBoundaryRealComplex_dPrev_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.nonzeroBoundaryRealHodgeDecompositionFires` | `AAT.AG.Measurement.nonzeroBoundaryRealHodgeDecomposition_fires` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.squareFreeRepairSupportNotMemAlexanderDualIffHitsForbidden` | `AAT.AG.Measurement.squareFree_repairSupport_notMemAlexanderDual_iff_hitsForbidden` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.squareFreeSingletonQMinimalRepairHittingSet` | `AAT.AG.Measurement.squareFree_singletonQ_minimalRepairHittingSet` | `propext`, `Quot.sound` |
| `AAT.AG.AxiomAudit.replayZeroTheorem42GlobalTransitionExists` | `AAT.AG.Examples.EvolutionPart9.replay_zero_theorem42_global_transition_exists` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.toyForceIntegrable` | `AAT.AG.Examples.EvolutionPart9.toy_force_integrable` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.forceCandidateSelectedNonzeroBackedByConcrete` | `AAT.AG.Examples.EvolutionPart9.force_candidate_selected_nonzero_backed_by_concrete` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.forceCandidatePackageInhabited` | `AAT.AG.Examples.EvolutionPart9.force_candidate_package_inhabited` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.temporalProductIncidencePRD4CohomologyToFrom` | `AAT.AG.TemporalCoefficient.ProductIncidencePRD4Comparison.prd4_cohomology_to_from` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.temporalProductIncidencePRD4CohomologyFromTo` | `AAT.AG.TemporalCoefficient.ProductIncidencePRD4Comparison.prd4_cohomology_from_to` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.zmod2TemporalProductIncidenceD0StepNonzero` | `AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductIncidence_d0_step_nonzero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.zmod2TemporalProductIncidenceD0StepNeZero` | `AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductIncidence_d0_step_ne_zero` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.zmod2TemporalProductCoverRelativeH1ToFrom` | `AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductCoverRelativeH1_to_from` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.zmod2TemporalProductCoverRelativeH1FromTo` | `AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductCoverRelativeH1_from_to` | `propext`, `Classical.choice`, `Quot.sound` |
| `AAT.AG.AxiomAudit.zmod2TemporalIdentityLegH1ClassNeZero` | `AAT.AG.Examples.EvolutionPart9.zmod2TemporalIdentityLegH1Class_ne_zero` | `propext`, `Classical.choice`, `Quot.sound` |

The audit list is intentionally additive. AC19 synchronizes the PRD-R
completion evidence surface through IX-2. Later PRD-R or post-PRD hardening PRs
must add new wrappers when they promote theorem-package or firing-instance
declarations into the kernel-audited surface.

## PRD-10 Research-to-body declaration correspondence

PRD-10 R10 treats `Formal/AG/Research/**` as frozen reference material, not as
body evidence. The following table records the declaration-unit correspondence
used by the Part X ledger.

| Frozen Research anchor | Body file | Body declaration units | Boundary |
| --- | --- | --- | --- |
| `SemanticRepairGluingComplex` | `Formal/AG/SemanticRepair/GluingComplex.lean` | `FiniteSemanticRepairGluingComplex`, `SemanticFaithfulnessHypotheses`, `GlobalSemanticRepairCoherent`, `globalRepairCoherent_forces_obstructionVanishes`, `no_globalRepairCoherent_of_nonzero_obstruction`, `globalRepairCoherent_of_obstructionVanishes`, `finiteSemanticRepairGluingDescent_iff`, `finiteSemanticRepairGluingDescent_package` | 本体は selected finite cover / gluing complex と semantic faithfulness に相対化する。Research の巨大 selected witness family は移植しない。 |
| `SemanticRepairCechGrounding` §6 | `Formal/AG/SemanticRepair/SiteCech.lean` | `atomGeneratedCoverage_generates_AATGrothendieckTopology`, `selectedAATSiteTopology_eq_atomGeneratedGrothendieckTopology`, `SemanticRepairCoverRelativeCoverBridge`, `SemanticRepairCover.toCoverRelativeCechCover`, `EmptyIndexZeroSimplexIncidenceNoGo`, `chartIndexedZeroCover_constructs_zeroSimplexChartIncidence`, `coverNerve_typedComponent_adequacy`, `aatSheafCondition_coverMembership_descent_effectiveGluing` | cover-relative Čech bridge は selected zero-simplex incidence と cover membership に相対化する。bare cover から incidence を生成しない。 |
| `SemanticRepairCechGrounding` theorem 7.2/7.4 route | `Formal/AG/SemanticRepair/H1Comparison.lean` | `SemanticRepairAdditiveH1Surface`, `SemanticRepairCoverRelativeH1Comparison`, `SemanticRepairCoverRelativeCochainRealization`, `SemanticRepairCoverRelativeCochainRealization.toH1Comparison`, `semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero`, `semanticRepairAdditiveH1Nonzero_of_coverRelativeH1Nonzero`, `coverRelativeH1Nonzero_of_semanticRepairAdditiveH1Nonzero`, `semanticRepairAdditiveH1_coverRelativeH1_comparison_package` | comparison は degree-wise equivalence と differential compatibility を保持するだけで、zero / descent / global coherence は持たない。 |
| `SemanticRepairCechGrounding` theorem 7.3 route | `Formal/AG/SemanticRepair/SagaComparison.lean` | `SemanticRepairGroundedGlobalGluingPackage`, `trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package` | theorem 7.3 は selected true-sheaf certificate、gluing data、H1 comparison に相対化する。full sheaf cohomology comparison と refinement naturality は future boundary。 |
| `SemanticRepairLawEquationRealization` §5 | `Formal/AG/LawAlgebra/LawEquation.lean` | `SemanticLawEquationWitnessIdealCore`, `lawWitnessIdeal`, `selectedLawWitnessIdealFamily`, `obstructionIdeal`, `lawWitnessIdeal_le_obstructionIdeal`, `map_lawWitnessIdeal_le`, `restrictionCompatible`, `map_obstructionIdeal_le`, `obstructionQuotientRestrict`, `obstructionQuotientCoefficient`, `obstructionQuotientPresheaf`, `obstructionQuotientPresheaf_eq_forget_coefficient`, `quotient_mk_eq_zero_iff_mem_obstructionIdeal`, `generatedCoefficient_package` | law-equation generated coefficient は `obstructionQuotientCoefficient` を canonical な AddCommGrpCat-valued presheaf とし、Type-valued `obstructionQuotientPresheaf` は `obstructionQuotientCoefficient ⋙ forget` から得る。一般 quotient sheaf 生成は主張しない。 |
| `SemanticRepairLawEquationNativeGeneratedInputs` grounding route | `Formal/AG/LawAlgebra/LawEquation.lean`, `Formal/AG/SemanticRepair/SagaComparison.lean`, `Formal/AG/SemanticRepair/Boundary.lean` | `LawEquationDefectSource`, `DisplayedRequiredLawsHoldOn`, `GeneratedRestrictionEvaluator`, `displayedRequiredLawsHoldOn_constructs_interpret_eq_zero`, `displayedRequiredLawsHoldOn_constructs_restrictionEvaluator`, `interpret_eq_zero_iff_defect_mem_obstructionIdeal`, `interpret_ne_zero_of_defect_notMem_obstructionIdeal`, `obstructionQuotientCoefficient`, `obstructionQuotientPresheaf`, `lawEquation_grounding_packet`, `SemanticRepairNativeGeneratedEndToEndInputs`, `lawEquation_constructs_groundedComparisonPacket`, `lawEquation_constructs_groundedComparisonPacket_fromNativeGeneratedInputs`, `displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage` | law equation は degree-zero contribution と native generated quotient coefficient surface を供給する。native route の cover-relative complex は `ObstructionSheaf.ofAddCommGrpValued G.obstructionQuotientCoefficient certificate.sheafCondition` 上に型で固定される。旧 arbitrary-`F` generated route と field-copy provenance route は Lean 本体・AxiomAudit・台帳の completion surface から削除した。 |
| `SemanticRepairLawEquationEndToEndInstance` | `Formal/AG/SemanticRepair/LawEquationGeneratedPair.lean`, `Formal/AG/Examples/SemanticRepairPart10.lean`, `Formal/AG/AxiomAudit.lean` | `lawEquation_constructs_generatedPair_groundedComparisonPacket`, `AxiomAudit.semanticRepairTheorem75GeneratedPairGroundedComparisonPacket`, `generatedLawQuotientPresheaf`, `generatedLawQuotientIsSheaf`, `generatedLawQuotientObstructionSheaf`, `generatedLawQuotientOne_ne_zero`, `generatedLawQuotientNontrivial`, `generatedLawCircleCoverRelativeComplex`, `generatedLawCircleResidual_not_coboundary`, `generatedLawCircleSemanticH1_nonzero`, `lawfulFiring_generatedLawCircleQuotient_endToEndPacket_fromConstructedInputs`, `AxiomAudit.semanticRepairExample91GeneratedLawQuotientNontrivial`, `AxiomAudit.semanticRepairExample91GeneratedLawCircleSemanticH1Nonzero`, `AxiomAudit.semanticRepairExample91GeneratedLawCircleQuotientEndToEndFromConstructedInputs`, `lawfulFiring_generatedSourceC0Zero`, `circleNerve_nonzeroClassTransfer_packet` | #3102 の完了根拠は、Research completion theorem を本体側に移植した generated-pair route と、native `lawEquationCore.obstructionQuotientPresheaf` / `obstructionQuotientCoefficient` 由来の同じ constructed witness surface に置く。`lawEquation_constructs_generatedPair_groundedComparisonPacket` は同一 law-equation source から semantic surface、generated coefficient、canonical envelope、cochain realization、H1 comparison package、residual boundary statement、semantic/additive H1 zero を構成する。`generatedLawQuotientObstructionSheaf` は `ObstructionSheaf.ofAddCommGrpValued lawEquationCore.obstructionQuotientCoefficient generatedLawQuotientIsSheaf` から生成する。生成 quotient `ZMod 4 ⧸ span{2}` の `Nontrivial`、同じ係数上の circle 型 Cech complex の非零 H¹、theorem 内で inline 構成した native inputs からの theorem 7.5 firing をそれぞれ監査する。7.5 firing theorem 自体は H¹ 非零を結論に含めない。legacy `PUnit` singleton route と generated `F₂` route は completion evidence にしない。 |

## R11 external consistency checklist

R11 checks public / outreach-facing surfaces against the normalized AG Lean
ledger vocabulary. It does not rewrite those surfaces in this PRD-R pass.
When a drift is found, the required action is to record a follow-up Issue.

Checklist execution scope:

| Surface | Files checked | Check | Status | Follow-up |
| --- | --- | --- | --- | --- |
| Repo top-level overview | `README.md`, `PHILOSOPHY.md` | No standalone theorem-count number is advertised. Lean status is delegated to `docs/aat/lean_theorem_index.md` and proof-obligation ledgers. | aligned | none |
| Docs overview | `docs/README.md`, `docs/aat/README.md` | The docs overview separates `proved`, `defined only`, `future proof obligation`, and `empirical hypothesis`, and does not publish a numeric theorem-count claim. | aligned | none |
| Website planning notes | `docs/note/website_renewal_design_note.md`, `docs/note/website_renewal_w2_statement_wayfinding.md` | Planning notes require website Lean-status claims to trace to `lean_theorem_index_ag_aat.md`. They are not themselves external theorem-count claims. | aligned | none |
| Website AAT status page | `website/src/aat/status/index.html` | The page exposes the PRD-R vocabulary and representative proved anchors, but its canonical-source links are pinned to commit `bd3a1152a7b7ac067ac4862c1dac91e99db66861`, predating the final PRD-R AC19 sync. | drift recorded | #3082 |
| AG Lean ledgers | `docs/aat/lean_theorem_index_ag_aat.md`, `docs/aat/proof_obligations_ag_aat.md`, this inventory | The authoritative internal ledger vocabulary and R0 / R1 / AC19 validation are present and current through PRD-R AC19. | aligned | none |

Targeted scan commands:

```bash
rg -n "[0-9]+\s*(theorem|定理|証明|proved|formalized)|定理[0-9０-９]+本|[0-9０-９]+本" \
  README.md PHILOSOPHY.md docs/README.md docs/aat/README.md website/src/aat \
  docs/note/website_renewal_design_note.md docs/note/website_renewal_w2_statement_wayfinding.md

rg -n "bd3a1152|PRD-R|proved rows|theorems proved" \
  website/src/aat/status/index.html docs/aat/lean_ag_peer_review_inventory.md \
  docs/aat/proof_obligations_ag_aat.md docs/aat/lean_theorem_index_ag_aat.md
```

R11 conclusion: the required external-consistency checklist exists. No external
numeric theorem-count drift was found in the checked surfaces. The concrete
website snapshot drift found during the review is tracked separately as #3082;
AC20 does not modify protected mathematical text or website content.

## AC21 audit ledger

AC21 closes the PRD-R hardening inventory as a disposition ledger, not as a
claim that every statement-shaped surface became an unconditional theorem.
Rows below trace each R0 item I-* through IX-* either to a closed PRD-R
sub-issue or to this AC21 boundary record. Items completed by `宣言`,
`statement-only`, or `future proof obligation` remain explicit non-proved
surfaces.

| Items | Final disposition | Completion evidence | Tracking |
| --- | --- | --- | --- |
| I-1, I-2, I-3, I-4 | 昇格 / 実質化 / 宣言 | Part I concrete three-reading, AAT core realization, finite-support predicates, and frozen selected assumption slots are recorded in R2. | #2960 |
| II-1 | 昇格 | Seed witness closure cover makes the closure construction load-bearing. | #2966 |
| II-2 | 未達・降格記録 | Quotient finite-meet poset construction exists, but the old proposition-4.2 empty-theorem / over-promotion concern remains downgraded rather than closed as theorem-grade evidence. | #2969 / #3100 |
| II-3 | 実質化 | Context morphism roles are external concrete predicates over support / axis readings. | #2972 |
| II-4 | 昇格 | Standard finite-poset Čech route supplies the generated differential theorem. | #2977 |
| II-5 | 発火 | Two-patch finite site, unit descent, sheafification gap, and nonzero Boolean Čech calculation fire. | #2981 |
| II-6 | 発火 | Coverage-to-Grothendieck bridge fires on the selected finite equality-thin site. | #2986 |
| III-1 | 昇格 | Lawfulness-Ideal Correspondence is connected to selected witness ideals and generated defects. | #2989 |
| III-2 | 昇格 | Lawful-locus factorization is strengthened to the zeroLocus one-way theorem; the reverse radical gap remains non-claimed. | #2997 |
| III-3 | 昇格 | Sheafification bridge is tied to Mathlib sheafification under explicit `HasSheafify`. | #3001 |
| III-4 | 実質化 | Scheme chart compatibility is tied to selected affine `Spec` locally ringed surface. | #3004 |
| III-5 | 実質化 | NSdepth is generated from selected generator certificates and display degree; general Nullstellensatz remains statement boundary. | #3007 |
| IV-1 | 昇格 | Cover-relative cohomology gets additive `H^1 = Z^1 / B^1` and legacy bridge. | #3010 |
| IV-2 | 発火 | Pseudo-circle nonzero `H^1` fires in Part IV vocabulary. | #3012 |
| IV-3 | 昇格 | Local flatness gap uses finite pointwise restriction/coboundary soundness. | #3014 |
| IV-4 | 昇格 | Flatness criterion is connected to finite `C^0` adjustment and additive vanishing. | #3016 |
| IV-5 | 昇格 | Cover nerve debt uses finite cochain rank-nullity and forest absorption certificate. | #3020 |
| IV-6 | 昇格 | `DerOb_U` is no longer opaque and is a selected cotangent-coefficient carrier. | #3028 |
| IV-7 | 昇格 | concrete `TwoChartGloballyUFlat` / `TwoChartBoundaryResolved` 実述語、2チャート soundness、holonomy kernel exactness からの boundary resolution、13.2 one-simplex basis 計算を実証明済み。任意 cover の自動 Stokes 構成と derived Mayer-Vietoris triangle は PRD-R IV-7 の外側の非主張境界。 | #3100 |
| IV-8 | 宣言 | Type-valued obstruction sheaf / module sheaf surfaces remain defined-only carriers with additive/module boundary. | #3086 |
| V-1, V-2 | 実装済み | V-1 は `ZMod 2` concrete theorem `example56_zmod2_mathlibTor1_nonzero` で certificate-free Tor₁ 非零を証明済み。V-2 は canonical Tor0 bridge と canonical `LawConflictPackage` route で定理6.1 / 7.3(V) を発火済み。任意 `CommRing k` の Tor₁ 非零は非主張。 | #3098 |
| V-3, V-4 | 昇格 / 実装済み | V-4 は `SelectedFiniteFreeResolution.exact` を Mathlib `Function.Exact` predicate に置換済み。V-3 は 2生成 presentation の face cardinality / pair multidegree / concrete `d₂,d₁` / regular-pair exactness / `coker(d₁) ≃ₗ[A] A/(a,b)` bridge に加え、具体係数環 `(ZMod 2)[x₀,x₁]` の `(X 0, X 1)` で nondegenerate regular-pair exact complex を証明済み。任意係数環・任意2生成 monomial presentation からの一般 Taylor 自動構成は PRD-R V-3 の外側の非主張境界。 | #3100 |
| V-5 | 削除 / 実質化 | `finite_trace_certificate` と `sharedWitnessG5_window_interference_zero` は削除済み。theorem-grade reading は all-degree G5 identity と synthesis output theorem 側で読む。 | #3097 |
| V-6 | 実装済み | `HilbertSeriesBasisCountPackage` により Hilbert-series coefficient を degree-wise selected finite monomial basis cardinality へ接続し、shared-witness の ambient / quotient / joint / Tor-one 系列で発火済み。PowerSeries 有理関数表示は非主張のまま。 | #3100 |
| VI-1 | 実装済み | `toyCotangentData` / `toyTangentData` / `toyDeformationTheory` と concrete operation / monodromy / stack carriers から、5 toy model の concrete firing theorem を追加済み。 | #3099 |
| VI-2 | 昇格 | `pi1^AAT` is bridged to Mathlib `PresentedGroup` and its universal property. | #3041 |
| VI-3, VI-4 | 実装済み | VI-3 triple→pairwise restriction / cocycle 実等式化を追加済み。VI-4 は IV-6 `ConDef_U` を selected cotangent carrier とし、`DerOb_U` を tangent obstruction target とする constructor / audit theorem を追加済み。一般 cotangent complex / `Ext^1` は非主張。 | #3100 |
| VI-5 | 宣言 | B-level decomposition gerbe / non-abelian soundness remains supplied-boundary data; banded abelian bridge is explicitly conditional. | #3086 |
| VII-1 | 未達・降格記録 | `AATSynthesisPackage` fires only on the finite singleton/PUnit-style fixture; `costToDistanceValue _ := measured 0` remains a constant regression. This is not counted as theorem-grade synthesis evidence. | #3046 / #3100 |
| VII-2 | 実装済み | `AATSch` has a `Category` instance and `AnalyticRepresentation.toFunctor` bridge. | #3051 |
| VII-3, VII-4, VII-6 | 昇格 / 部分昇格(B項目境界) | VII-3 coboundary invariance は明示 Stokes + zero-chain equation から証明済み。VII-4 は adequacy 4条件と zeroClass actual-zero 接続を theorem package / toy firing に反映済み。VII-5 actual GLB は実装済み。VII-6 は length-one edge-fiber cardinality と toy firing を実装済みだが、一般 length-n cardinality theorem は未主張。#3086 の束ね closure では完了扱いしない。 | #3100 |
| VIII-1 | 実装済み | Finite Hodge decomposition, harmonic debt, and lower-bound fire on real finite inner-product complex data; #3091 adds a nonzero-boundary real fixture so AC15 is not witnessed only by the zero differential complex. | #3057 / #3091 |
| VIII-2 | 実装済み | Theorem 5.2 reuses PRD-3 Stanley-Reisner assets and finite Alexander dual / hitting-set bridge. | #3063 |
| VIII-3, VIII-4, VIII-5 | 実装済み(#3100追補) | VIII-3 finite/Fintype 実述語化と finite carrier lemma、VIII-4 Derived `LawConflictPackage` 接続、VIII-5 certified fields の theorem-package 化と low-degree example firing は実装済み。Period/Stokes は extension accounting additive theorem、topological debt は finite nerve cochain complex theorem へ接続済み。ただし一般 Stokes pairing theorem や任意 cover 自動構成は未主張。 | #3100 |
| VIII-6 | 実装済み | Hodge and Alexander dual fixtures fire as selected finite examples; Hodge now has both the original real 3D zero-differential fixture and the nonzero-boundary real fixture. | #3057 / #3063 / #3091 |
| IX-1 | 実装済み | Temporal descent theorem 4.2 fires through selected realization and nondegenerate replay fixture. | #3070 |
| IX-2 | 実装済み | `IntegrableForce` is a selected integration interface, and candidate 7.2 has inhabitable concrete-value-backed data plus an inhabitable literal `ForceIntegrabilityObstructionCandidate` package while the non-integrability implication remains statement-only. | #3073 / #3091 |
| IX-3, IX-4, IX-5 | 実装済み | IX-3 は fiber-valued incidence differential、product-incidence complex package、finite poset × two-point trace の legacy PRD-4 comparison wrapper を持つ。ただし既存 cohomology-level inverse firing は `PUnit` singleton 係数の wrapper/accessor であり、nondegenerate completion evidence ではない。#3100 追補として `ZMod 2` product-incidence differential の非零 theorem、`zmod2TemporalProductCoverRelativeEquivalence` 由来の PRD-4 cover-relative H¹ left/right inverse theorem、`incidenceDifferential_id` を使う `zmod2TemporalIdentityLegH1Class_ne_zero` を追加し、AxiomAudit entries に載せた。IX-4 kind 別 canonical constructor、IX-5 の `selectedConcreteClassNonzero := True` 解消と PRD-10 circle instance bridge も実装済み。 | #3100 |

AC21 audit note: IX-3's previous `PUnit` wrapper is still excluded as
completion evidence. The current closure relies on the nondegenerate `ZMod 2`
product-incidence PRD-4 cover-relative H¹ comparison route and its AxiomAudit
entries. Other `宣言`, `statement-only`, or future proof-obligation boundaries
remain scoped non-claims rather than cost-based downgrades.

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
| II-2 | 未達・降格記録 | `Formal/AG/Site/ContextCategory.lean` has the quotient finite-meet construction layer, but the old proposition-4.2 empty-theorem / over-promotion concern remains downgraded. The construction is retained as compatibility evidence, not as theorem-grade closure evidence for #3100. |
| II-2 firing | 降格記録 | `Formal/AG/Examples/FiniteModel.lean` has `siteRestrictionQuotientFiniteMeetPosetCategory_fromFiniteMeet` for the finite model's canonical restriction preorder, but this is not counted as closing the old theorem claim. |
| II-2 audit | 監査・降格記録 | `Formal/AG/AxiomAudit.lean` keeps `finiteRestrictionQuotientFiniteMeetPoset`, guarded at `propext`, `Classical.choice`, `Quot.sound`; the wrapper audits the construction only and is not promoted as #3100 completion evidence. |
| II-3 | 実質化 | `Formal/AG/Site/Context.lean` makes `MinimalContext.supportReads_objectFamily` load-bearing and replaces the old free Prop role slots with external concrete predicates: `SupportMapPreservesReads`, `AxisMapPreservesReads`, `ObservableRestrictionFunctorial`, `SupportMapNonGenerating`, `AxisMapForgetsOnlyReadableAxes`, `SupportMapReflectsReads`, `AxisMapReflectsReads`, `SupportMapRefinesReads`, `AxisMapRefinesReads`, `BaseChangeCompatibleReads`, and `ContextMorphism.ConcreteRestriction` / `ConcreteProjection` / `ConcreteRefinement` / `ConcreteBaseChange`. |
| II-3 firing | 発火 | `Formal/AG/Examples/FiniteModel.lean` adds `siteContext_supportReads_objectFamily` and `siteContextIdentityMorphism_rolesConcrete`, showing the finite singleton context and its identity morphism satisfy the concrete restriction / projection / refinement / base-change roles. |
| II-3 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteContextMorphismRolesConcrete`, guarded at `propext`. |
| II-4 | 昇格 | `Formal/AG/Site/FinitePosetGeometry.lean` and `Formal/AG/Cohomology/FinitePosetStandardComplex.lean` expose the PRD-10 standard route: coefficient-free cover geometry, canonical tuple nerve, simplicial face action, standard alternating differential, double-face cancellation, `standardFinitePosetCechComplex`, and `canonicalTupleStandardFinitePosetCechComplex`. The old selected-data complex remains a packaged compatibility surface; the canonical tuple route provides the generated `d ∘ d = 0` theorem. |
| II-4 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `canonicalTupleStandardFinitePosetCechComplexDComp`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| II-5 | 発火 | `Formal/AG/Examples/FiniteModel.lean` adds a non-singleton selected finite site: `TwoPatchContextIndex`, `twoPatchContextIndexLe`, `twoPatchContext`, `TwoPatchCoverIndex`, `twoPatchCover`, `twoPatchFinitePosetRegime`, and one-dimensional selected nerve data. The example includes an adequate two-patch cover, explicit overlap-to-patch morphisms, `twoPatchUnit_descent`, `twoPatchSheafificationGap`, and the nonzero Boolean Čech calculation `twoPatchSeparatedCochain_differential_nonzero`. |
| II-5 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteTwoPatchCoverUAdequate`, `finiteTwoPatchUnitDescent`, `finiteTwoPatchSheafificationGap`, and `finiteTwoPatchCechDifferentialNonzero`, all guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| II-6 | 発火 | `Formal/AG/Examples/FiniteModel.lean` adds `siteAdmissiblePrecoverage_hasPullbacks` and `siteAdmissiblePrecoverage_stableUnderBaseChange` for the singleton finite equality-thin site. The concrete theorem `siteTopology_eq_coverage_toGrothendieck` fires `AATGrothendieckTopology.eq_coverage_toGrothendieck` on that selected finite instance. |
| II-6 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteSiteTopologyEqCoverageToGrothendieck`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |

## R4 Law algebra correspondence hardening

R4 starts the Part III PRD-R items additively. It preserves the existing
`LawfulnessIdealCorrespondenceAssumptions` package while adding theorem
counterparts whose load-bearing premises are selected witness ideals and the
generated local obstruction ideal.

| ID | Disposition | New evidence |
| --- | --- | --- |
| III-1 | 昇格 | `Formal/AG/LawAlgebra/Correspondence.lean` adds `localObstructionIdeal_le_ker_iff_lawful`, `lawful_of_selectedWitnessIdeals_le_ker`, `lawful_of_generatedLawWitnessIdeals_le_ker`, and `displayedRequiredLawsHoldOn_defect_mem_localObstructionIdeal`. These connect section lawfulness to `SelectedLawWitnessIdealFamily.localObstructionIdeal` and PRD-10 R5 generated law-equation defects rather than consuming `witnessCoverage` as the conclusion. |
| III-1 firing | 発火 | `Formal/AG/LawAlgebra/FiniteExamples.lean` adds `acyclicLocalSectionData`, `acyclic_cycleWitnessIdeal_le_ker`, and `acyclicLocalSection_lawful_from_witnessIdeals` for the selected finite cycle witness example. |
| III-1 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteAcyclicLocalSectionLawfulFromWitnessIdeals`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| III-2 | 昇格 | `Formal/AG/LawAlgebra/LawfulLocus.lean` adds `LawfulSectionData.sectionPrimeMap`, `sectionPrimeMap_mem_lawfulLocus_of_le_ker`, `sectionPrimeMap_mem_lawfulLocus_of_pulledObstructionIdeal_eq_bot`, `sectionPrimeMap_mem_lawfulLocus_of_lawful`, `localSectionPrimeMap`, and `localSectionPrimeMap_mem_localLawfulLocus_of_lawful`. These expose the affine prime map induced by the section pullback and prove only the vanishing-to-zeroLocus containment direction. |
| III-2 firing | 発火 | `Formal/AG/LawAlgebra/FiniteExamples.lean` adds `acyclic_sectionPrimeMap_mem_localLawfulLocus`, firing the zeroLocus containment bridge on the selected finite cycle witness example. |
| III-2 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteAcyclicSectionPrimeMapMemLocalLawfulLocus`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| III-3 | 昇格 | `Formal/AG/LawAlgebra/StructureSheaf.lean` adds `mathlib_sheafification_lift_unique` and `ofMathlibSheafification`, deriving the selected bridge from Mathlib `toSheafify` / `sheafifyLift` / `sheafifyLift_unique` under explicit `HasSheafify S.topology (AATCommAlgCat k)`. |
| III-3 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `structureSheafMathlibSheafificationLiftUnique`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| III-4 | 実質化 | `Formal/AG/LawAlgebra/Scheme.lean` adds `affineChartMathlibSpecLocallyRingedSpace`, `ChartCompatibility.selfAffineSpec`, and `ArchitectureScheme.singleAffineSpec`, tying a selected affine AAT chart to Mathlib `Spec.toLocallyRingedSpace` and supplying the legacy compatibility slots for the single-chart identity atlas. |
| III-4 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `schemeSingleAffineSpecCompatibilityAllConditions`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| III-5 | 実質化 | `Formal/AG/LawAlgebra/Nullstellensatz.lean` adds `GeneratorUnitCertificate`, `HasSelectedGeneratorUnitCertificateAt`, `GeneratorNSdepthProfile`, `GeneratorNSdepthProfile.toNSdepthProfile`, and `GeneratorNSdepthProfile.NSdepth_mono_of_generatorCertificateExtension`. The legacy arbitrary `Nat -> Prop` profile remains as a compatibility surface, while the new profile is generated by selected finite linear-combination displays and their display degrees. |
| III-5 firing | 発火 | `Formal/AG/LawAlgebra/FiniteExamples.lean` adds the selected generator family `{x, x - 1}`, coefficient vector `1 = x - (x - 1)`, a concrete generator unit certificate, span membership, and a generator-backed `NSdepth = 1` profile. |
| III-5 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `finiteConcreteGeneratorUnitCertificateOneMemSpan` and `finiteConcreteGeneratorNSdepthEqOne`, both guarded at `propext`, `Classical.choice`, `Quot.sound`. |

## R5 Obstruction cohomology hardening

R5 starts the Part IV PRD-R items additively. It preserves the existing
`CechCohomologySucc` / `cohomologyClassSucc` / `CoverRelativeHn` signatures
consumed by Research and downstream modules, while adding explicit additive
surfaces and bridge theorems.

| ID | Disposition | New evidence |
| --- | --- | --- |
| IV-1 | 昇格 | `Formal/AG/Cohomology/CechComplex.lean` adds `AdditiveCochain`, `CechCocycleSubgroup`, `coboundaryCocycle`, `CechCoboundarySubgroupSucc`, `AdditiveCechH1`, `additiveH1Class`, `additiveH1Class_eq_zero_iff`, `additiveH1Class_eq_iff_legacy_setoid`, and `cohomologyClassSucc_eq_iff_additiveH1Class_eq`. The selected `d ∘ d = 0` field is used to put coboundaries inside the cocycle subgroup. |
| IV-1 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `coverRelativeCohomologyClassSuccEqIffAdditiveH1ClassEq`, guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| IV-2 | 発火 | `Formal/AG/Cohomology/FiniteExamples.lean` adds `PartIVCircleNonzeroH1Firing` and its cover-relative / additive H1 nonzero readings. `Formal/AG/Examples/SemanticRepairPart10.lean` adds `circlePartIVPseudoCircleFiring`, `circlePartIV_h0_invisible_coverRelativeH1_nonzero`, and `circlePartIV_h0_invisible_additiveH1_nonzero`, connecting the PRD-10 circle nonzero H1 instance to Part IV pseudo-circle vocabulary. |
| IV-3 | 昇格 | `Formal/AG/Cohomology/LocalFlatnessGap.lean` adds `FiniteGlobalRestrictionPointwiseSoundness`, `FiniteGlobalRestrictionPointwiseSoundness.toFiniteGlobalRestrictionCoboundarySurface`, `FiniteGlobalRestrictionCoboundarySurface`, `GlobalLawfulRestrictionCoboundaryData.ofFiniteGlobalRestrictionCoboundarySurface`, `localFlatnessGapHypotheses_of_finiteGlobalRestrictionPointwiseSoundness`, and `localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionPointwiseSoundness`. `Formal/AG/Cohomology/FiniteExamples.lean` adds `no_global_lawful_section_by_finiteGlobalRestrictionPointwiseSoundness` for the pseudo-circle witness. The existing theorem signature remains intact, while finite overlap-wise checks now assemble into theorem 7.1 without directly postulating `GlobalSectionCoboundarySoundness`. |
| IV-4 | 昇格 | `Formal/AG/Cohomology/FlatnessCriterion.lean` adds `AdditiveH1ClassVanishes`, `additiveH1ClassVanishes_iff_exists_c0_coboundary`, `FiniteC0AdjustmentSurface`, `FiniteC0AdjustmentSurface.adjustedOverlapResidual`, `FiniteC0AdjustmentSurface.adjustedOverlapAgreement`, `FiniteC0AdjustmentSurface.adjustedOverlapAgreement_iff_c0_coboundary`, `FiniteC0AdjustedGlobalLawfulSection`, `finiteC0AdjustedGlobalLawfulSection_iff_exists_c0_coboundary`, `finiteC0AdjustedGlobalLawfulSection_iff_additiveH1ClassVanishes`, and the two one-way accessors. The existing packaged `CohomologicalFlatnessCriterionHypotheses` theorem remains intact, while finite `C⁰` adjustment now proves `[g]=0 ↔ ∃ t, g=d⁰t ↔` concrete adjusted residual vanishing/global-condition existence in additive `H^1` form. |
| IV-5 | 昇格 | `Formal/AG/Cohomology/CoverNerve.lean` adds `FiniteNerveCochainComplex`, `boundaryToCycles`, additive `H1 = ker d1 / im d0`, `finrank_H1_add_finrank_boundary`, and `topologicalDebtCapacity_fromComplex`, proving the theorem-12.2 inequality from Mathlib rank-nullity instead of a supplied `rankNullity_H1` field. It also adds `FiniteForestEdgeAbsorptionData`, `classAt_eq_start`, `final_no_edgeSupport`, `forestVanishing`, and `forestVanishing_subsingleton`, decomposing forest vanishing through a finite edge-support absorption certificate plus a no-edge-support zero criterion. Existing `FiniteDimensionalNerveCohomologyData`, `ConstantCoefficientNerveReading`, `ForestCoverGluingData`, and `EulerCochainAccounting` signatures remain intact. |
| IV-5 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `coverNerveTopologicalDebtCapacityFromComplex`, guarded at `propext`, `Classical.choice`, `Quot.sound`, and `finiteForestEdgeAbsorptionVanishing`, guarded at `propext`. |
| IV-6 | 昇格 | `Formal/AG/Cohomology/ObstructionSheaf.lean` replaces opaque `DerOb_U` with a transparent selected naive cotangent-coefficient carrier whose fields are `conDefClass : ConDef_U A F` and `coefficient : M`. It adds `DerOb_U.ofConDefCoefficient` and accessor theorems while keeping general cotangent complex / derived category / `Ext^1` construction outside the claim boundary. |
| IV-6 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `derObUOfConDefCoefficientConDefClass` and `derObUOfConDefCoefficientCoefficient`, both guarded at `propext`, `Classical.choice`, `Quot.sound`. |
| V-1/V-2 | 実装済み | `Formal/AG/Derived/Counterexample.lean` adds the `ZMod 2` principal projective resolution and `example56_zmod2_mathlibTor1_nonzero`, proving the example-5.6 Tor₁ nonzero class without selected equivalence / package-field nonzero assumptions. `Formal/AG/Derived/Intersection.lean` and `Formal/AG/Examples/DerivedPart5.lean` provide the canonical Tor0 bridge / canonical `LawConflictPackage` firing route. |
| V-1/V-2 audit | 監査 | `Formal/AG/AxiomAudit.lean` adds `example56ZMod2MathlibTor1Nonzero`, `canonicalSelectedTorBridgeLawConflict0AlgEquivClassicalJoint`, and `canonicalSelectedTorBridgeLawConflict0LinearEquivMathlibTor`, guarded at standard axioms. Legacy package-relative `example56LawConflictPackageFiringLawConflict1Nonzero` / `example56LawConflictPackageFiringTor1Nonzero` remain audited but are not the #3098 V-1 completion evidence. |
