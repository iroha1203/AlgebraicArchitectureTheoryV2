# AAT代数幾何版 Lean形式化 PRD-R: 第I〜X部 査読耐性補強

対象: `Formal/AG` 本体全域(第I〜X部の Lean 形式化)と両台帳
(`lean_theorem_index_ag_aat.md` / `proof_obligations_ag_aat.md`)

先行PRD: [PRD-1](lean_ag_part_1_atoms_objects_laws_prd.md) 〜
[PRD-9](lean_ag_part_9_evolution_geometry_prd.md)、
[PRD-10 第X部 SAGA 蒸留移植](lean_ag_part_10_semantic_repair_descent_saga_prd.md)

**依存**: 本PRDは PRD-10 の完了を前提とする。PRD-10 が納品する
標準 Čech 複体(R1)、円周非零 `H^1` instance(R9)、第III部 定理11.4 の本体化
(R5)は、本PRDの複数の要求の前提部品である。

## 問い

AAT を外部に発表したとき、**数学者と Lean 専門家による批判的査読**に対して、
次を成立させられるか。

> 本文の任意の定理ラベルから台帳経由で Lean 宣言に辿り着いたとき、
> (a) その statement が本文の主張を忠実に表しており、
> (b) その証明が「結論を仮定パッケージのフィールドから取り出す」ものではなく、
> (c) その定理が少なくとも一つの非退化な有限モデルで実際に発火しており、
> (d) 証明が依存する公理が標準公理(propext / Classical.choice / Quot.sound)
>     のみである
>
> ——か、そうでない場合には、台帳がその宣言を「仮定パッケージの帰結」
> または「statement-only」として**機械的に区別できる語彙で**明示している。

現状の本体には、この基準に反する系統的なパターンが存在する(監査で確認済み):

```text
反証不能フィールド:  field : Prop + field_holds : field(True で充足可能)
                     — Measurement/RepAnalysis だけで247箇所、全体で300超
結論フィールド定理:  定理の結論そのものが仮定 record のフィールド
                     — 定理4.2(IX)、定理7.1/9.2/11.1/12.2/13.2(IV)、
                       定理16.1(VII)、定理8.5(VIII)ほか
空型仮定パッケージ:  P ∧ ¬P を要求し原理的に充足不能
                     — TransportDescentToyModel(VI例)、
                       ForceIntegrabilityObstructionCandidate(IX)
未発火の主定理:      非自明インスタンスがリポジトリにゼロ
                     — Part IV の H^1 非零、Part V の Tor₁ 非零、
                       Part VI の全 toy model、Part VII synthesis
公理検査の穴:        Formal/AG 内の native_decide 6箇所が Lean.ofReduceBool を
                     導入し、台帳の「no axiom scan」文言と #print axioms が矛盾
```

採否規律: 本PRDの対象は、既存ラベルの (a)〜(d) を成立させる補強
(statement の忠実化、仮定の実述語化、証明の昇格、非退化な発火例、
公理検査、台帳語彙の是正)に限る。理論の新規展開(新しい部・新しい定理系列)
は対象外とし、新概念の導入は既存ラベルの昇格に必要な補助構成
(restriction の実装、torsor 作用、gluing 操作など)に限る。
昇格にあたり statement を本文より弱めて `proved` を名乗ることを禁止する
(anti-weakening)。実装中に、昇格が本文の記述不足により不可能と判明した
場合(本文が仮定を明示していない等)、本文改訂はユーザー判断事項なので
ループを停止して報告する。`docs/aat/algebraic_geometric_theory/` は
本PRDでは変更しない。

さらに、`Formal/AG/Research` は evidence として凍結されている(PRD-10 R10)。
Research が import する本体宣言(PRD-10 中心方針(4)の凍結宣言群:
`finitePosetCoverRelativeCover` / `FinitePosetAATSiteRegime` /
`FinitePosetCechComplex` / `CoverRelativeCechCover` / `CoverRelativeCechComplex`
等に加え、R0 で `rg` により機械抽出する「Research 参照本体宣言リスト」の全件)
の変更は additive(新宣言 + 充足定理 + 旧版の `packaged` 明示)に限り、
削除・rename・シグネチャ変更の対象から除外する。全タスクで `lake build` に
加えて `lake build FormalAGResearch` の green を維持する。既存宣言の型変更・
削除がどうしても必要と判明した場合はループを停止し、ユーザー判断
(Research 側の対応改修か、evidence ビルドの明示的な降格決定)を仰ぐ。

## 中心方針

**(1) 横断パターンを部より先に潰す。**

査読者は部単位ではなくパターン単位で攻撃する。「`Prop + holds` は `True` で
充足できるため、この形式化は反証可能な主張を避ける設計になっている」という
一行批判は、個別の定理の修正では防げない。本PRDは最初に全数棚卸し(R0)を行い、
全対象を次の四択に落とす。

```text
(a) 昇格   — 実述語に置換し、証明する
(b) 実質化 — 実述語に置換し、仮定として残す(意味のある公理的境界)
(c) 宣言   — Prop のまま残すが、台帳とdocstringで「selected 公理スロット」と
             機械的に識別できる語彙を与える
(d) 削除   — 死にデータ・無内容定理・矛盾構造体
```

ただし Research 参照本体宣言リスト(採否規律参照)に載る宣言は (d) の対象に
しない((c) 宣言または deprecate に落とす)。

**(2) 台帳の status 語彙を三分化する。**

`proved` の一語が「実証明」「仮定パッケージの射影」「rfl accessor」を
区別できないことが台帳の信頼性リスクである。status 語彙を

```text
proved                      — 実証明(仮定はすべて明示的かつ実述語)
packaged (assumption-relative) — 仮定 record のフィールド合成による帰結
statement-only              — 型は正しいが証明しない candidate
```

に三分化し、既存全行を再分類する。旧PRD(1〜9)の AC 文言と実装の乖離
(「証明されている」と書かれた AC が実際には packaged である等)も
この機会に正直に再判定し、台帳に記録する。**開示は隠蔽より強い防御である。**

**(3) 昇格の基準線は既にリポジトリ内にある。**

`IdempotentCollapse.lean`(補題5.6A、Mathlib 深部資産での完全証明)、
`StanleyReisner.lean`(定理5.6C、本文より強い形での証明)、
`lawfulness_iff_omegaU_zero`(定理9.3本体)、
`sharedWitnessG5_all_degree_coefficient_identity`(全次数帰納)、
`operationInvariantGaloisCorrespondence`(Galois 橋)、
PRD-10 移植後の SAGA 定理群。補強はこの水準を目標とし、届かないものは
(b)(c) に落として明示する。

**(4) 発火なき定理は定理と数えない。**

主定理ごとに「非退化な有限モデルでの無条件発火」を要求する。
前提が空虚に満たされる例(全フィールド `True`、PUnit 係数、singleton site)は
発火と認めない。PRD-10 が納品する円周非零 `H^1` instance を Part IV/V/VII/IX の
発火例の共通土台として再利用する。

**(5) 公理検査を文字列 grep から kernel 検査へ格上げする。**

`native_decide` は `Lean.ofReduceBool` を証明項に導入するため、
「axiom scan no match」(ソース文字列基準)と `#print axioms`(kernel 基準)が
食い違う。`Formal/AG` 内の native_decide は6箇所であり、全て `decide` /
`norm_num` / `simp` で置換可能なことを監査で確認済み。これを全廃し、
CI に `#print axioms` 相当の公理検査を追加する(リポジトリ全体では41箇所
あるが、`Formal/Arch` の35箇所は本PRDの対象外)。

**(6) 部ごとの補強は「A級指摘」を優先する。**

各部の監査で優先度A(査読で理論の信頼性を毀損)と判定された項目を R2〜R10 に
列挙する。優先度B(防御可能だが弱い)は要求に含めるが、ループの選択順位は
A級を先にする。優先度C(磨き上げ)は R1 の横断整理に吸収する。

## 背景

- 2026-07-04 の査読耐性監査(5レーン並列、全 `Formal/AG` 本体読解)で、
  本体は「本物の数学」「正直なインターフェース」「空虚なパッケージ」の
  三層混在であることが確認された。sorry / axiom 宣言はゼロだが、
  「sorry なし」は「証明済み」を意味しない状態にある。
- 台帳は `proved under explicit ... data` 等の限定句で概ね正直に記述されて
  おり、この正直さ自体が第一防衛線である。本PRDはそれを「限定句」から
  「機械的に区別できる語彙」へ格上げする。
- 特に重大な単発事実として: 補題7.2A(II)の Lean statement は閉包構成なしで
  任意の admissible family について成立する(コンパイル検証済み)、
  `IntegrableForce`(IX)は恒真であり定理候補7.2 の仮定パッケージが空型、
  `TransportDescentToyModel`(VI例)は `P ∧ ¬P` を要求する空型、
  `Tor₁ ≠ 0`(V 例5.6)と `H^1 ≠ 0`(IV)はリポジトリ内で一度も無条件に
  証明されていない(後者は PRD-10 R9 で解消予定)、が挙がっている。
- `DerOb_U`(IV 定義2.4)は「Part V へ委譲」と注記されたまま PRD-5 が
  委譲を明文で拒否しており、参照ゼロの孤児 opaque になっている。
  台帳は `unassigned` と記録済みであり、本PRDが委譲先を確定する。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. `Formal/AG` 本体に、`True` で充足可能な `Prop + holds` フィールドが
   「(c) 宣言済み公理スロット」として台帳に登録されたものを除き存在しない。
2. 台帳の全行が三分化された status 語彙で再分類され、旧PRDの AC 充足状態が
   正直に再記録されている。
3. 各部の主定理([CBI] 定理と各部の看板定理)が、実証明+非退化発火、
   または「packaged」の明示のいずれかに落ちている。
4. `native_decide` がゼロになり、CI が kernel 水準の公理検査を行う。
5. 空型仮定パッケージ・無内容定理・誤ラベル定理が存在しない。
6. 対外整合チェックリストが存在し、外部発表資料の「定理N本」等の数字と
   三分化台帳の `proved` 行数のずれが全件 Issue 化されている(文書改稿は
   別作業)。

## 補強対象台帳(部別)

ギャップ分析はこの表(と R0 の全数棚卸し)を基準に行う。表の項目 ID
(I-1、IV-2 等)を本PRDの正式な要求 ID とする。
「昇格」= 実証明化、「実質化」= 実述語への置換、「発火」= 非退化例の追加。

各項目は監査の優先度Aを基本とするが、次の項目はB(弱いが防御可能)である:
**III-2 / III-3 / III-5 / VI-5 / VII-6**。B項目は昇格コストが高い場合、
(b) 実質化または (c) 宣言の処置で完了としてよい(その判断を台帳に記録する)。

### 第I部(Atom)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| I-1 | `ThreeReading.lean` 定理9.3後段 | 結論の iff 2本が仮定フィールド、前提4つが任意 Prop。インスタンスゼロ | 昇格: law-indexed witness family を導入し、witness completeness / axis exactness を具体述語化して `lawfulness_iff_omegaU_zero` と同型の実証明へ。有限モデルに非退化 witness family instance を**追加**する(現行 `badWitness := True` は三読み一致と両立しない退化定義だが、FiniteModel の既存定義は Research が消費するため変更せず、新 instance を並置する) |
| I-2 | `AATCore.lean` 定理10.5 | 塔の全成分が入力で公理系 S 未使用。`ObstructionCircuit` 必須のため law-failure なしでは package が作れない。`HEq` 使用 | 昇格: `AtomAxiomSystem` の Family / Configuration / Law を実際の塔の型に接続し、S から標準塔を構成する関数+性質定理へ。circuit は `Option` 化または分離。`HEq` を除去 |
| I-3 | `Configuration.lean` / `Obstruction.lean` の擬似有限性 | `finite : Prop` + `finite_holds`(`True` で充足可) | 実質化: `Set.Finite` / `Finite (Subtype mem)` へ置換。FiniteModel の instance を実有限性で更新 |
| I-4 | `Law.lean` の `coverageAssumptions` / `exactnessAssumptions` | 被参照ゼロの自由 Prop(「使われない公理」) | 削除し、必要な仮定は I-1 の具体述語へ移す |

### 第II部(Site)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| II-1 | `Adequate.lean` 補題7.2A | `UAdequateCover` は任意の `AATCoverageFamily` で成立(コンパイル検証済み)。閉包構成が結論に寄与せず、局所有限性が死に仮定 | 昇格(再定式化、additive): 「admissibility を仮定しない seed + witness support 表現可能性 → 閉包が admissible かつ adequate」の新定理を追加する。seed 側仮定を seed index 上に制限。`UAdequateCover` と `AdmissibleCover` の重複は additive に解消する(新述語+充足定理。Research が消費する既存宣言は凍結し `packaged` 明示) |
| II-2 | `ContextCategory.lean` 命題4.2 | 「Q が与えられれば Q が存在する」空定理。quotient poset がデータ供給 | 昇格: minimal context の成分ごとの meet 構成 + Mathlib `Antisymmetrization` による preorder → quotient poset 導出定理。空定理は削除 |
| II-3 | `Context.lean` | `MinimalContext` のパラメータ `A` が phantom。`ContextMorphism` の8役割述語が全て任意 Prop | 実質化: supportReads と `A.configuration.family` の関係、restriction の具体条件を定義し、`readableMorphism_isRestriction` を具体 instance で証明可能に |
| II-4 | `FinitePoset.lean` 命題7.2C | nerve が任意データ、d∘d=0 が仮定フィールド、cohomology が setoid 商 | 昇格: PRD-10 R1 の標準複体(tuple nerve、標準交代和、d∘d=0 証明済み)へ移行し、旧データ仮置き版はその canonical instance で充足する。次元消滅を実複体上で証明 |
| II-5 | `Examples/FiniteModel.lean`(Part II 面) | site 例が全部 singleton / `True` で、7.2A / 7.2C / sheaf / descent が空虚発火 | 発火: 2 patch + overlap の非退化 poset site を構成し、非自明 sheaf instance、descent の成立例と失敗例(sheafification gap)、非自明 Čech 計算例を追加 |
| II-6 | `Topology.lean` Mathlib Coverage bridge | `HasPullbacks` / `IsStableUnderBaseChange` instance がリポジトリに存在せず、bridge 定理が一度も適用可能になっていない | 発火: meet 付き thin site に instance を構成し有限モデルで発火 |

### 第III部(LawAlgebra)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| III-1 | `Correspondence.lean` 定理11.1 | 5項同値のうち3項が定義的同一、核心の `witnessCoverage` が結論そのもの、環と ideal が §5–6 の witness ideal 語彙と未接続 | 昇格(部分): `SelectedLawWitnessIdealFamily.localObstructionIdeal` に特化した版で witnessCoverage の片方向以上を定理化。PRD-10 R5 の定理11.4 本体化と接続し、台帳の第III部節を再編 |
| III-2 | `LawfulLocus.lean` 幾何的 factorization | rfl-rename(set-theoretic factorization と `s*I_Ob = 0` は radical の差で一般に非同値、という実数学を隠している) | 昇格(片方向): `PrimeSpectrum.comap` で誘導写像を定義し、消滅 → 像が zeroLocus に入る方向を実証明。逆向きの radical 障害を非主張に記録 |
| III-3 | `StructureSheaf.lean` sheafification bridge | `isSheafification` が仮定パッケージで、Mathlib `HasSheafify` からの製造関数が未実装(PRD-3 の明文要求) | 昇格: 製造補題を実装 |
| III-4 | `Scheme.lean` | `RingedAATTopos` / `ArchitectureScheme` の3成分を関係づける条件が皆無、`ChartCompatibility` 7条件が全て自由 Prop | 実質化+発火: affine 版で `AlgebraicGeometry.Spec` を underlying に取る実例、または整合条件フィールドの追加 |
| III-5 | `Nullstellensatz.lean` | NSdepth が ideal と無関係な任意 Nat 述語。候補7.2A に本文の閉体仮定が欠落 | 実質化: 生成系の線形結合表示と表示次数で NSdepth を実定義。候補7.2A の仮定を本文に整合させる |

### 第IV部(Cohomology)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| IV-1 | `CechComplex.lean` | `differential` / `differential_comp`(d∘d=0)がデータフィールド。`CoverRelativeHn` に群構造がなく `H1ClassVanishes` が外部から `AddCommGroup` を受給 | 昇格(additive): PRD-10 R1 の標準構成で充足定理を得た上で、coboundary を `AddSubgroup` に取る商群版 `H^1` を**新宣言として**導入し、`= 0` 読みを提供する。Research が消費する既存 `CechCohomologySucc` / `cohomologyClassSucc` / `CoverRelativeHn` のシグネチャは凍結し、新旧の一致定理で接続する |
| IV-2 | `FiniteExamples.lean` 擬円周 | `CoverRelativeH1NonzeroWitness` のインスタンスがリポジトリにゼロ。「H^0 で見えず H^1 で見える」実例が仮定言明のまま | 発火: PRD-10 R9 の円周 instance(無条件非零 H^1)へ接続し、AC13(旧PRD-4)を実体化 |
| IV-3 | `LocalFlatnessGap.lean` 定理7.1 | 「大域 section ⇒ coboundary」が関数ごと仮定。lawful section の restriction が未定義 | 昇格: lawful section の presheaf 化(context ごとの section 環と restriction)を導入し、mismatch を具体構成、coboundarySoundness を有限モデルで定理化 |
| IV-4 | `FlatnessCriterion.lean` 定理11.1 | 含意4本が仮定フィールド、11個の自由 Prop | 昇格(有限 regime): C⁰ 調整 torsor を具体化し `[g]=0 ↔ ∃t, g=dt ↔ 調整後一致` を実証明。一般 site 版は packaged と明示 |
| IV-5 | `CoverNerve.lean` 定理12.2 / 系12.3 / 定理12.4 | rank-nullity が仮定(Mathlib で即証明可能)、比較同型が phantom、forest 帰納法が仮定 | 昇格: 線形写像 d0/d1 のフィールド化 + `LinearMap.finrank_range_add_finrank_ker`、nerve 鎖複体と b₁ の実定義、forest の graph-theoretic 定義と帰納法 |
| IV-6 | `ObstructionSheaf.lean` `opaque DerOb_U` | 参照ゼロ・委譲先不在の孤児 placeholder。外部レビューで次数規約の指摘済み | 昇格または誠実化: 全射 `A → A/I` の naive cotangent complex を deformation module `M` へ Hom 双対した複体の H¹(naive `Ext¹`)で opaque を実定義に置換する: `DerOb_U F M := coker(Hom_{A/I}(Ω_{A/k} ⊗_A A/I, M) → Hom_{A/I}(I/I², M))`。本文定義2.4 は `M` に相対化された対象を要求する点に注意(`M` 非依存の `Algebra.H1Cotangent` そのものではない)。材料は `Ideal.Cotangent` / `KaehlerDifferential.map` / `Submodule.Quotient`。`AddCommGroup` instance と消滅例を付す。不可能なら opaque を削除し台帳を「未形式化」に更新。委譲先を本PRDで確定する |
| IV-7 | `BoundaryResidue.lean` 定理9.2 / `PeriodStokes.lean` 定理13.2 | `globally_UFlat` が自由 Prop で構造全体が自明充足可能 / stokes が仮定フィールド | 実質化+部分昇格: globally_UFlat を実述語(大域 lawful section の存在)に置換し、soundness 側を2チャート構成で証明。13.2 は d 具体化後に基底計算で証明 |
| IV-8 | `ObstructionSheaf.lean` Type値 sheaf | 手書き加法フィールドで abelian 圏資産への道を塞いでいる | 実質化(additive): PRD-10 R1(e) の `AddCommGrpCat` 値 constructor を正とし、新規開発はそちらに乗せる。既存 `ObstructionSheaf` は Research が広く消費するため凍結し、constructor 経由で充足する |

### 第V部(Derived)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| V-1 | `Counterexample.lean` 命題9.2(iii) | `Tor₁(R/⟨xy⟩, R/⟨xz⟩) ≠ 0` が certificate 仮定のまま(リポジトリで一度も無条件証明されていない) | 昇格: principal resolution から `(⟨xz⟩:xy)/⟨xz⟩` の `z` 類非零を実計算し、`Example56TorCalculation` のインスタンスを構成 |
| V-2 | `Intersection.lean` Tor₀ 補題 | `LawConflict_0 ≅ O/(I_U+I_V)`(旧PRD-5 R3 の明文要求)が仮定フィールド | 昇格: Mathlib の Tor 零次同型 + quotient tensor 同型で証明し、canonical `SelectedTorBridge` / `LawConflictPackage` instance を構成して定理6.1 / 7.3(V)を発火 |
| V-3 | `TaylorResolution.lean` | Taylor complex の項も微分も未構成(`resolvesQuotient : Prop` が任意) | 昇格(段階): 2生成系(principal syzygy)の Taylor complex を実構成し完全性を証明。一般形は packaged と明示 |
| V-4 | `FreeResolution.lean` `exact : Prop` | 完全性が任意 Prop | 実質化: `Function.Exact` による具体述語へ |
| V-5 | 無内容・誤ラベル定理 | `finite_trace_certificate`(∃n, length = n)、`sharedWitnessG5_window_interference_zero`(X−X=0 を「干渉零」と誤ラベル) | 削除(後者は「Tor₁ 級数に一致する」正しい定理へ差し替え可) |
| V-6 | `HilbertSeries.lean` | 無法則 Cauchy 積の自前 series。regime の手書き係数列と環の次数別次元が未接続 | 実質化: `PowerSeries ℤ` への橋、または係数列を単項式基底の濃度として証明 |

### 第VI部(SingularityMonodromyStack)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| VI-1 | `Examples/SingularityMonodromyStackPart6.lean` | **例が一つも構成されていない**(5 toy model 全てが instance ゼロの条件文)。`TransportDescentToyModel` は `P ∧ ¬P` を要求する空型 | 発火+修正: 空型構造を zero 版 / nonzero 版に分割し、`TinyState` 級の具体データで5 instance を実構成(旧PRD-6 R12 の再開) |
| VI-2 | `OperationHomotopy.lean` π₁^AAT | `Pi1` が演算経路と無関係な裸の群、`FreeWord` に群構造なし、普遍性が全てフィールド(旧PRD-6 R5 は Mathlib `PresentedGroup` 使用を明記) | 昇格: `PresentedGroup` で Pi1 を構成し、`PresentedGroup.lift` の普遍性で置換 |
| VI-3 | `ArchitectureStack.lean` | base に triple overlap → pairwise overlap の restriction 射が存在せず、本物の cocycle 等式が語彙上書けない | 実質化: base に triple 射を追加し cocycle 条件を実等式化。`∃ _, True` を `Nonempty` へ |
| VI-4 | `CotangentInterface.lean` / `Kuranishi.lean` | `TangentData` の certificate が「`_holds` すらない裸の Prop」、H0/H1 が全理論で未使用。deformation theory の数学的内容が型に存在しない | 実質化+発火: affine chart 上で `KaehlerDifferential` + conormal `I/I²` による `CotangentData` の実インスタンスを構成し、`ObstructionTarget ≃ H1` を型で結ぶ。IV-6 の `DerOb_U` と一本化 |
| VI-5 | `DecompositionGerbe.lean` 定理16.2 | gerbe class が descent datum から定義されず、soundness / nonzero が供給フィールド | 昇格(有限設定): 有限 cover・有限 groupoid で Čech 2-cocycle 型の gerbe class を定義し「global object 存在 ⇒ class 消滅」を定理化。届かない場合は soundness を (b) 公理的境界として残し台帳に記録(B項目) |

### 第VII部(RepresentationAnalysis)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| VII-1 | `Synthesis.lean` 定理16.1 | 11連言中9個が rfl の「コピーはコピー元と等しい」定理。`AATSynthesisPackage` のインスタンスがゼロ(塔が組み上がることが一度も実演されていない) | 発火: 有限モデルから `AATSynthesisAssumptions` の完全インスタンスを構成し、塔全体の inhabit を実演。定理を再定式化 |
| VII-2 | `AATSch.lean` | `AATSchMorphism` の互換性が射自身の選ぶ Prop(`True` で「互換」射が作れる)。`AnalyticTargetCategory` に結合律・単位律なし。本文2.1「圏・functor」が満たされていない | 実質化: 互換性述語を reading parameter 側の固定述語へ移し、`Category (AATSch p)` と functor 橋を成立させる |
| VII-3 | `FiniteHomology.lean` strict period(旧AC8) | 不変性そのものが仮定(`pairingRespectsCompatibility`)で、未インスタンス化 | 昇格: 擬円周の具体 pairing で「coboundary 摂動での pairing 値不変」を実証明し、非自明インスタンス化 |
| VII-4 | `AnalyticContext.lean` 定理15.4 | adequacy 4条件が証明で未使用(「under Adequacy」が名前だけ)。`zeroClass` が任意型の選点 | 実質化: 未使用仮定の解消(load-bearing 化または削除)、zeroClass を実零元(PRD-4 の H^n)に接続 |
| VII-5 | `DistanceFlatnessMass.lean` | `CostInfimumDomain` の唯一の instance が `infimum := 0`、`GLB := True` の偽物 | 実質化: Mathlib `iInf` / 実 GLB へ置換 |
| VII-6 | `GraphMatrix.lean` walk count | 「個数」の一致(`(A^n) i j = card (walks)`)が未証明(存在 iff のみ) | 昇格: card 等式へ強化 |

### 第VIII部(Measurement)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| VIII-1 | `Hodge.lean` 定理8.5 / 8.6 / 系8.7 | 全結論が Prop + cert フィールド。直交性・分解・同型が Lean 上に存在しない(旧PRD-8 R6 は Hilbert complex theorem としての証明を明記) | 昇格: `InnerProductSpace ℝ` + `FiniteDimensional` + `d∘d=0` 実等式でモデルを作り直し、`LinearMap.adjoint` と直交射影で分解・調和同型・残差最小性・下界を実証明。**本PRDの最重要昇格** |
| VIII-2 | `SquareFreeRepair.lean` 定理5.2 | 4対応が全て不透明 Prop。第1対応は PRD-3 で実証明済みなのに参照していない。Alexander dual がリポジトリに不存在 | 昇格: PRD-3 `StanleyReisner` 定理の再輸出 + `dual Δ = {S | Sᶜ ∉ Δ.faces}` の実装と hitting set 対応の Finset 証明 |
| VIII-3 | `FiniteRegime.lean` / `Computability.lean` 定理4.2 | 有限性9条件が不透明 Prop。「有限線形代数へ落ちる」数学が不在 | 実質化+部分昇格: `Finite` / `Fintype` 実述語へ置換し、有限 poset site → 有限次元 cochain の実補題を証明 |
| VIII-4 | `LawConflict.lean` | `TorObject` が PRD-5 の実 Tor 橋と未接続(名前だけ) | 実質化: `Derived.Intersection.LawConflictPackage` への接続フィールドと等式 |
| VIII-5 | `Packet.lean` 定理12.1 / `GAGA.lean` 定理12.3 | certified fields が Prop トークンの連言 | 実質化: certified fields を実 theorem package 型(`hodge : FiniteHodgeDecomposition D` 等)に置換(VIII-1 の後続) |
| VIII-6 | `Examples.lean` | fixture がほぼ全て `True` 充填(`kerL1_equiv_H1 := True` 等)。R11 総括定理が「True の束」 | 発火: Hodge fixture を実2〜3次元複体へ、refactor fixture を非自明 zero-iff へ、5.2 fixture を極小性込みの `decide` 証明へ差し替え |

### 第IX部(Evolution)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| IX-1 | `ReplayDescent.lean` 定理4.2 | 結論(`Nonempty GlobalReplayTransition`)が仮定フィールド `descends_from_adjusted`。`adjust` 操作が未定義で `m(adjust)=m−dc` が record field | 昇格: coefficient の torsor 作用と `StateTransitionSheaf` の gluing 操作を定義し、mismatch を replay の差として計算、adjust を作用で定義して等式を証明、4.2 を実証明化 |
| IX-2 | `Force.lean` 定理候補7.2 | `IntegrableForce` が恒真(`TemporalLaw` は `Witness := PEmpty` で常に構成可、3 Prop は `True` 可)なため候補の仮定パッケージが**空型** | 修正: `IntegrableForce` を R5 interface(大域 replay transition の存在等)で実定義し、candidate を inhabitable に再設計 |
| IX-3 | `TemporalObstruction.lean` / `TemporalProductSite.lean` | `H^n(Tr_E×X)` が実質 `H^n(X)`(trace 方向の微分なし)。`TemporalCoefficient` の fiber が obstruction 機構で未使用 | 昇格(最小): finite poset × two-point trace の incidence complex を実装し、temporal cochain を fiber 値で定義、PRD-4 複体への比較を定理化 |
| IX-4 | `TemporalLaw.lean` 定義3.3 | kind タグと述語の間に整合条件がなく、本文の代表 equation が一つも書かれていない | 実質化: kind ごとの canonical constructor(replay 冪等性等の実 equation)を定義し例で発火 |
| IX-5 | `Examples/EvolutionPart9.lean` | 定理4.2 の発火が全 PUnit 退化複体。「非零 class」が Čech class でない detached 値、零 class に `selectedNonzero := True` の札 | 発火: ZMod 2 係数 2-chart 複体で「非零 cochain だが coboundary → 調整 → 貼り合わせ」例、PRD-10 の円周 instance に接続した実非零 class 例。`selectedNonzero` に soundness 条件を追加 |

### 第X部(SemanticRepair、PRD-10 移植後の任意 hardening)

| # | 対象 | 問題 | 処置 |
| --- | --- | --- | --- |
| X-1 | 例9.2 の恒等 comparison | 非恒等 comparison を通じた非零転送が未演習(G-06 boundary notes の任意項目) | 任意: 非恒等 comparison での転送例を追加 |
| X-2 | witness site の退化 | singleton contexts / 自明位相(同 boundary notes) | 任意: atom-generated な非退化非零 instance |

X-1 / X-2 は義務ではない(受理境界の内側)。着手する場合も claim boundary の
拡大(chart 交叉からの生成主張等)をしないこと。

## 要求

### R0. 全数棚卸しと台帳語彙の三分化

- `Formal/AG` 本体全域の反証不能パターンを二層で棚卸しする。
  - (α) 機械抽出層: rg パターンで全数を確定できるもの。
    (i) `field : Prop` + `field_holds` / `_cert` 対、
    (iii) `Nonempty` を返すだけの定理、native_decide、
    および「Research 参照本体宣言リスト」(採否規律の凍結対象。
    `rg -o 'AAT\.AG\.[A-Za-z0-9_.]+' Formal/AG/Research/ | sort -u` 等で抽出)。
    使用した rg パターンを棚卸し台帳に記録し、全数性を主張する。
  - (β) レビュー層: 構文パターンで拾えないもの。(ii) 結論フィールド定理、
    (iv) rfl accessor、(v) インスタンスゼロの主要構造体、(vi) phantom
    パラメータ・死にフィールド。部別監査表(本PRDの補強対象台帳)を起点に
    ファイル単位の目視走査を行い、走査済みファイル一覧を Issue に記録する
    (全数性は走査記録で担保する)。
  - 全件を四択(昇格 / 実質化 / 宣言 / 削除)に分類し tracking Issue に記録する。
- 台帳の status 語彙に `packaged (assumption-relative)` と `statement-only` を
  追加し、theorem 系 status 行を再分類する。移行規則:
  - 三分化語彙は既存 status の**置換ではなく正規化タグの併記**とする。
    既存の限定句(`proved under explicit ... data` 等)は情報として残置し、
    その行に `packaged (assumption-relative)` を併記する。
  - 実述語のみを仮定に取る実証明は `proved` のまま。
  - `defined only` / `future proof obligation` / `empirical hypothesis` /
    explicit non-goal 行は三分化の対象外(現行のまま)。
    `statement-only candidate` は `statement-only` に正規化する。
  - `proved accessor` 行は R1 の格下げ後、定理計上から除外する。
  - 判定に迷う status 値は tracking Issue でユーザーへエスカレートする。
- 旧PRD 1〜9 の AC のうち実装が packaged に留まるもの(例: 旧PRD-4 AC3/AC4、
  旧PRD-8 R6、旧PRD-7 AC8)を特定し、`proof_obligations_ag_aat.md` の各部
  セクション末尾(締めの2列表の後)に「AC 再判定:」段落を新設して
  「旧PRD-N ACn: 旧文言 → 再判定 status と根拠宣言名」を箇条書きで記録する。
- 完了条件: 棚卸し台帳(α の rg パターン、β の走査記録込み)が存在し、
  両台帳の theorem 系全行が三分化タグ付きで再分類されている。

### R1. 横断規律(公理検査・無内容定理・恒久ガード)

- `native_decide` を全廃する。対象は `Formal/AG` 内の6箇所
  (`Cohomology/FiniteExamples.lean` 1、`Examples/DerivedPart5.lean` 3、
  `Examples/EvolutionPart9.lean` 2)で、`decide` / `norm_num` / `simp` へ
  置換する(`Formal/Arch` の35箇所は本PRDの対象外。必要なら別 Issue 化)。
- CI に kernel 水準の公理検査を追加する。検査対象は「各部の [CBI] 定理 +
  本PRDで昇格した定理」の宣言名リスト(R0 で tracking Issue に固定)とし、
  各宣言の公理依存が標準公理(propext / Classical.choice / Quot.sound)のみ
  であることをスクリプトで検査する。
- 無内容定理・誤ラベル定理・空型構造体を削除または修正する(V-5、VI-1 の
  空型、`selected_axis`(I)、`∃ _, True`(VI)、Bootstrap の rfl 儀式定理群、
  `comparisonName : String` ほか R0 棚卸しの (d) 分類全件。ただし
  Research 参照本体宣言リストに載るものは (c) 宣言へ落とす)。
- rfl accessor 定理を `@[simp]` 補題 / `example` へ格下げし、台帳の定理数
  計上から外す(Research が名前参照する accessor は残置し計上のみ除外)。
- 恒久規律として「新規の `Prop + holds` フィールドを導入しない/導入する場合は
  台帳の公理スロット台帳に登録する」および status 語彙への
  `packaged (assumption-relative)` / `statement-only` の追加を
  `docs/aat/guideline.md` の Lean status 節に追記する(guideline は保護
  ファイルではないが、変更は最小限にする)。
- 完了条件: `rg 'native_decide' Formal/AG` が no match、公理検査が CI で
  実行されている、`lake build` と `lake build FormalAGResearch` が green。

### R2〜R10. 部別補強

上記「補強対象台帳」の I-* 〜 IX-* を要求として実施する。R 番号と部の対応:
R2 = 第I部(I-*)、R3 = 第II部(II-*)、R4 = 第III部(III-*)、
R5 = 第IV部(IV-*)、R6 = 第V部(V-*)、R7 = 第VI部(VI-*)、
R8 = 第VII部(VII-*)、R9 = 第VIII部(VIII-*)、R10 = 第IX部(IX-*)。
第X部の X-1 / X-2 は R 外の任意項目である。Issue・台帳のリンクは表の
項目 ID(I-1 等)を第一とし、R 番号は部単位の束ねに使う。
各項目の完了条件は:

- **昇格**: 当該 statement が実述語の上で sorry なしで証明され、台帳 status が
  `proved` に更新されている。統合前の仮定パッケージ版が残る場合は
  `packaged` と明記され、昇格版から充足定理が張られている。
- **実質化**: `True` で充足できないこと(意味のある反例が書けること)が
  docstring で説明され、非自明インスタンスが1つ以上存在する。
- **発火**: 前提が空虚でない有限モデル上で主定理が無条件に適用され、
  結論が非自明(型が PUnit でない、値が定数でない、係数が自明群でない)である。
- **削除**: 参照が残っていない。

優先順は A 級 → B 級(B 級は補強対象台帳の冒頭に列挙: III-2 / III-3 /
III-5 / VI-5 / VII-6)。B 級項目は昇格コストが高い場合 (b)(c) 処置で
完了としてよいが、その判断を台帳に記録する。

### R11. 対外整合

- 外部発表資料(website / outreach 文書)が引用する「定理数」「機械検証済み」
  等の数字・文言を、三分化台帳の `proved` 行と整合させる(対象文書の特定と
  整合チェックリストの作成まで。文書自体の改稿は別作業とし、ずれのある箇所を
  Issue 化する)。
- 完了条件: 整合チェックリストが存在し、ずれが Issue 化されている。

## 非主張(claim boundary)

- 本PRDは理論の新規展開をしない。第I〜X部の既存ラベルの外側に新しい数学的
  主張を追加しない。
- 全ての昇格は本文の仮定体系の内部で行う。本文が仮定を明示していない箇所を
  Lean 側で勝手に強い仮定で埋めない(発見時は停止・報告)。
- 「(b) 実質化」「(c) 宣言」に落ちた項目は、公理的境界として残ることを
  台帳が明示する。本PRDの完了は「全定理の実証明化」を意味しない。
- 査読耐性は Lean 形式化と台帳の整合性についての性質であり、理論の経験的
  妥当性の主張ではない。
- Part X の X-1 / X-2 は任意項目であり、未実施でも本PRDは完了できる。

## 完了条件(Acceptance Criteria)

- [ ] AC1. 反証不能パターンの全数棚卸し台帳が存在し、全件が四択分類済み(R0)
- [ ] AC2. 両台帳の status 語彙が三分化され、全行が再分類されている(R0)
- [ ] AC3. 旧PRD AC の再判定が台帳に記録されている(R0)
- [ ] AC4. `native_decide` ゼロ、CI に kernel 公理検査(R1)
- [ ] AC5. 空型仮定パッケージ(`TransportDescentToyModel`、
      `ForceIntegrabilityObstructionCandidate`)が inhabitable に修正されている
      (VI-1 / IX-2)
- [ ] AC6. 補題7.2A が再定式化され、閉包構成が結論に寄与する定理として
      証明されている(II-1)
- [ ] AC7. 三読み一致(I-1)と定理10.5(I-2)が昇格され、有限モデルで
      発火している
- [ ] AC8. `CoverRelativeHn` が商群として実装され、`H^1` 非零の無条件実例が
      Part IV の語彙で発火している(IV-1 / IV-2)
- [ ] AC9. `DerOb_U` が実定義に置換されたか、削除+台帳誠実化されている(IV-6)
- [ ] AC10. `Tor₁ ≠ 0`(例5.6)と Tor₀ 補題が無条件に証明され、
      `LawConflictPackage` の canonical instance が存在する(V-1 / V-2)
- [ ] AC11. π₁^AAT が `PresentedGroup` で構成され普遍性が証明されている(VI-2)
- [ ] AC12. Part VI の5 toy model が具体データで instance 化されている(VI-1)
- [ ] AC13. `AATSynthesisPackage` が有限モデルで inhabit し、塔の組み上げが
      実演されている(VII-1)
- [ ] AC14. `Category (AATSch p)` が成立している(VII-2)
- [ ] AC15. 有限 Hodge 分解(8.5/8.6/系8.7)が Mathlib 内積空間上の実定理として
      証明され、実複体 fixture で発火している(VIII-1 / VIII-6)
- [ ] AC16. 定理5.2 が PRD-3 資産に接続され、Alexander dual が実装されている
      (VIII-2)
- [ ] AC17. 定理4.2(IX)が実証明化され、非退化例で発火している(IX-1 / IX-5)
- [ ] AC18. `IntegrableForce` が実定義になり候補7.2 が inhabitable(IX-2)
- [ ] AC19. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が
      存在せず、公理検査対象リスト(R0 で固定した [CBI] 定理+昇格定理)の
      全宣言の公理依存が標準公理のみ(R1)
- [ ] AC20. 対外整合チェックリストが存在する(R11)
- [ ] AC21. 補強対象台帳の全項目(I-* 〜 IX-*)が四択処置のいずれかで完了し、
      処置結果(B級の (b)(c) 落とし判断を含む)が台帳と tracking Issue に
      記録されている(R2〜R10)
- [ ] AC22. 全変更を通じて `lake build FormalAGResearch` が green を維持して
      いる(または既存宣言の型変更が避けられず、ユーザーの明示的な降格決定が
      記録されている)(採否規律)

## 実行順序の指針

```text
R0 -> R1
   -> IV-1/IV-2(PRD-10 成果の接続。多くの発火例の土台)
   -> I-* -> II-*
   -> III-* -> IV-3..8
   -> V-* -> VI-*
   -> VII-* -> VIII-*(VIII-1 は独立に早期着手可)
   -> IX-*
   -> R11
```

- R0 / R1 は全部の前提(棚卸しなしに部別補強を始めると分類が二度手間になる)。
- VIII-1(Hodge 実定理化)は他部と独立で、単独の売りになるため早期着手を推奨。
- IV-1/IV-2 は PRD-10 の R1/R9 成果を接続するだけで大きく進むため、
  PRD-10 完了直後に置く。
- IX-1 / IX-3 は本PRD内で最も設計作業が重い(gluing / torsor / temporal 複体の
  新規構成)。他の昇格で得た書法を流用できる後半に置く。
