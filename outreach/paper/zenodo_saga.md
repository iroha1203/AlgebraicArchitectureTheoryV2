# Zenodo 向け SAGA 論文 要件整理

## 0. この文書の役割

この文書は、Zenodo で公開する SAGA 長編論文の主張、構成、証拠、成果物を固定するための
要件文書である。論文本文を書き始める前に、数学、Lean、ArchSig の三つを一つの研究成果として
接続し、各 claim が固定された一次証拠へ降りられる状態を作る。

論文を支える各内容の正本を次へ置く。

| 対象 | 正本 |
| --- | --- |
| AAT と SAGA の数学 | `docs/aat/algebraic_geometric_theory/` |
| Lean statement と proof | `Formal/AG/` および release 時点の Lean source |
| Lean status | 現行 AAT 台帳と release 時点の declaration manifest |
| ArchSig の計算 | `tools/archsig/` |
| 実コード診断 | 固定 input、run manifest、packet、gate output |
| 論文の読みと構成 | 本書および将来の paper source |

本書は release 時点の正本から、論文に採用する statement、declaration、measurement と
それらを結ぶ読みを固定する。

### 0.1 最重要公開要件: SAGA 数学本文の再構成

Zenodo 論文の執筆と公開に先立ち、SAGA 数学本文を Issue
[#3760](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3760)
の受け入れ要件に従って改訂する。

現在の標準 route は、semantic repair complex を AAT 側の Čech complex から transport し、
comparison data の主要性質を入力として受け取り、semantic residual を幾何側 residual の逆像として
定義している。この構成を、次の独立生成と定理へ置き換える。

1. semantic atom、semantic projection、repair support、局所 repair relation から
   semantic repair complex と semantic residual を構成する。
2. Atom-indexed equation system、equation-generated coefficient \(Q_E\)、AAT cover から
   cover-relative Čech complex と幾何側 residual を構成する。
3. semantic data と Atom / equation / cover data の対応から comparison map を構成する。
4. comparison map と differential の可換性を証明し、cocycle、coboundary、商上の
   \(H^1\) 同値を導く。
5. semantic mismatch から生成した residual が幾何側 residual へ写ることを証明する。

複体同値、逆写像、differential compatibility、residual 対応を結論相当の
certificate、structure field、typeclass として受け取る theorem は、この要件の完了根拠としない。
comparison core、equation semantics、true sheaf descent、finite executable realization は、
それぞれが実際に使う入力だけを受け取る別 statement として整理する。

数学本文の改訂と独立レビューが完了すれば、paper-level SAGA theorem を
プレプリント初稿の本文と Abstract に記載できる。general SAGA theorem の Lean 実装、
G-07 の本体蒸留、Lean status 同期は
[#3757](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3757)
で扱い、初稿では数学 claim と Lean claim を別の status 表で示す。

## 1. 論文の identity

### 1.1 推奨タイトル

プレプリント初稿の第一候補を次とする。

> **SAGA: A Comparison Theorem for Local-to-Global Software Architecture**
>
> *From Semantic Repair Cohomology to Algebraic-Geometric Descent*

`Lean-Formalized` を title に含める版は、Issue #3757 により general SAGA statement と
residual correspondence の本体形式化が完了した後に固定する。
数学、Lean、ArchSig の三つを統合する後続版では、一セントを ArchSig case study で初めて明かし、
後半の発見として働かせる。

### 1.2 中心主張

論文全体を次の主張で貫く。

> SAGA 定理は、architecture semantics における semantic repair の障害 `H¹` と、
> architectural equation system から生成された係数を持つ AAT site 上の
> cover-relative Čech `H¹` を比較する。二つの complex を各々の一次データから独立に構成し、
> Atom/equation generator map から semantic-to-geometric comparison map を構成し、
> cochain compatibility、`H¹` 同型、residual class 対応を証明する。

中心式は次の二つである。

\[
H^1_{\mathrm{sem}}(\mathcal U)
\cong
\check H^1(\mathcal U,Q_E)
\]

\[
\operatorname{GlobalCoherent}
\iff
[r_{\mathrm{Čech}}]=0
\]

二つ目の式は、semantic repair object の additive torsor structure、true sheaf condition、
selected AAT cover とともに提示する。零類から corrected matching family を構成し、
sheaf amalgamation が actual global section を与える証明を本文に置く。

Lean と ArchSig の claim は、この数学 claim へ接続済みの範囲を status 表で区別する。
初稿は paper-level theorem の完成を主張し、general SAGA theorem 全体の Lean 形式化は
Issue #3757 の完了後に主張する。

### 1.3 論文の成果

論文は三つの貢献を同じ重さで提示する。

1. **Mathematics**

   semantic repair additive `H¹` と AAT site 上の cover-relative Čech `H¹` を結ぶ
   SAGA 比較定理、および大域的な貼り合わせとの接続。

2. **Lean formalization status**

   generic cochain machinery、G-07 first-order conormal descent、零類と非零類の
   witness を declaration 単位で示し、general SAGA comparison の未形式化部分を
   Issue #3757 と対応づける。

3. **ArchSig measurement**

   明示された architecture data から residual、`B¹` membership、`H¹` class、
   comparison、gate、repair comparison を計算する有限診断と、実在 OSS での測定。

### 1.4 全体の物語

論文の流れを次で固定する。

```text
Atom と Law
  -> semantic repair H¹
  -> AAT site 上の Čech H¹
  -> SAGA 比較定理
  -> Lean 形式化
  -> ArchSig による有限診断
  -> 実在 software の一セント
  -> Cape of Good Hope
  -> Atom foundations
  -> architecture schemes
  -> Software Field Theory
  -> Rising Sea
```

前半は一般理論と circle-nerve witness によって進める。一セントは、大きな数学的構成が現実へ
到達した瞬間を示す、論文後半の payoff として用いる。

## 2. 執筆原則

### 2.1 成果から書く

各章は、構成した対象、証明した定理、得られた計算、研究上の意義から始める。
statement の条件は、その定理を正確に読むための数学データとして説明する。

論文の標準的な説明順を次とする。

1. 何を構成したか
2. 何を証明したか
3. なぜ重要か
4. Lean でどこまで形式化したか
5. ArchSig で何を測定したか
6. そこからどの研究へ進むか

### 2.2 AAT の対象を正確に書く

AAT は、Atom と Law から architecture object を構成し、その geometry を研究する。
論文は次の対象系列を一貫して使う。

```text
observed architectural fact
  -> Atom family
  -> architecture object
  -> Law equation
  -> geometry
```

Atom は、言語や framework を越えて architectural fact を扱う中間表現である。
SAGA の定理は、この architecture object 上の局所データと貼り合わせを扱う。

### 2.3 定理の仮定を数学として読む

選択した Atom、Law、cover、係数、faithfulness、sheaf condition、incidence data は、
それぞれ statement が扱う数学的対象と適用条件を定める。一般定理では入力として明示し、
具体例では構成済みの対象と検証済みの条件を示す。

レビューは各仮定について、次の一点を確認する。

> この仮定は statement が必要とする正当な数学的入力か、それとも結論相当の内容を
> certificate、structure field、typeclass として先取りしているか。

前者は定理の一部として受理する。後者が見つかった場合は、Lean 品質基準に従って
`certificate escape`、`structure-field escape`、`typeclass escape`、`未放電仮定` の
具体的な状態名で記録する。

### 2.4 Lean status が証明強度を伝える

本文は数学的成果を述べ、Lean status は各 claim の機械検証状態を伝える。
主要 claim には、少なくとも次を含む status table を付ける。

| 項目 | 内容 |
| --- | --- |
| Text theorem | 論文内の定理名 |
| Mathematical source | 数学本文の節・定理 |
| Lean declaration | exact declaration |
| Statement summary | 対象、仮定、結論 |
| Status | release 時点の正式 status |
| Source file | declaration の所在 |
| Evidence | focused check、axiom audit、CI |

status 名は release 時点の現行規律に合わせる。status table から読者が statement と証拠へ
直接降りられるようにする。

### 2.5 三つの証拠の provenance

論文では、次の三つを隣接させつつ、それぞれ固有の証拠を示す。

| 層 | 述べること | 一次証拠 |
| --- | --- | --- |
| Mathematics | statement と proof の内容 | 数学本文 |
| Lean | statement が機械検証された状態 | Lean source、audit、CI |
| ArchSig | 固定 input に対する有限 measurement | packet、manifest、digest |

この対応によって、研究成果の provenance を明瞭にする。

## 3. Abstract の要件

Abstract は六文程度で構成する。

1. 各局所領域が Law を満たしていても、大域的な貼り合わせは別の数学的問題として現れる。
2. semantic repair の貼り合わせ障害を additive `H¹ = Z¹/B¹` として定式化する。
3. SAGA 比較定理により、この `H¹` と equation-generated coefficient を持つ
   AAT site 上の cover-relative Čech `H¹` の同値を証明する。
4. Atom から比較同値までの定理連鎖を Lean 4 で形式化する。
5. ArchSig として有限診断を実装し、実在する microservice system で非自明な
   局所―大域障害と repair 後の変化を測定する。
6. 数学的定理、機械検証、architecture diagnosis が一つの監査可能な経路へ接続されたことを述べる。

Abstract は一般理論と三つの貢献に集中する。一セントの reveal は ArchSig case study まで温存する。

### 3.1 プレプリント初稿の固定数学 claim

プレプリント初稿の Abstract では、数学 claim を次の強さで固定する。

> For a selected AAT cover, we construct a semantic repair coefficient from
> semantic atoms and local repair relations, and an equation coefficient from
> an Atom-indexed architectural equation system. Under explicit
> generator-and-relation exactness, the primary Atom interpretation induces an
> isomorphism of the independently generated Čech complexes and hence an
> isomorphism on first cohomology. The isomorphism carries the residual class
> generated by local semantic-repair mismatch to the residual class generated
> by local equation lifts. When the semantic repair object is a sheaf, class
> vanishing is equivalent to the existence of an actual global repair.

Lean status は §4.6.1 の別表で示す。general SAGA theorem 全体を
Lean-formalized と呼ぶ版は Issue #3757 の完了後に固定する。

## 4. 論文構成

### 4.1 Introduction

Introduction は一般問題から始める。

> 各 component が自身の規約を満たすことと、それらが system 全体で一つの意味へ
> 貼り合うことは、異なる数学的条件である。

金額、認可、状態遷移、補償、event semantics、data ownership、単位、時刻、精度を、
局所―大域問題が現れる領域として簡潔に示す。特定の一例を主役にせず、SAGA が扱う問いを
先に固定する。

Introduction の必須要素は次である。

- research question
- mathematical contribution
- Lean formalization contribution
- ArchSig measurement contribution
- paper organization

### 4.2 AAT Foundations Required by SAGA

SAGA に必要な AAT construction spine を集中的に示す。

```text
Atom
  -> architecture object
  -> architectural equations
  -> witness ideals
  -> obstruction quotient Q_E
  -> AAT site
  -> cover-relative Čech complex
```

必須項目は次である。

- Atom と architecture object
- Law as equation
- witness ideal と obstruction ideal
- equation-generated coefficient \(Q_E=\mathcal O_E/I_{\mathrm{Ob}}\)
- coverage-generated AAT site
- selected cover と cover nerve

### 4.3 Semantic Repair as a Descent Problem

各 local context で semantic atom projection

\[
\pi_V:\Lambda(V)\to \operatorname{At}(V)
\]

と repair support \(S(V)\)、restriction-stable な局所 repair relation
\(R_{\mathrm{rep}}(V)\) を固定する。supported atom 上の free abelian group を relation で割り、

\[
M_{\mathrm{sem}}(V)
=
\mathbb Z^{(S(V))}/R_{\mathrm{rep}}(V)
\]

を構成する。この coefficient と AAT cover から semantic Čech complex を作る。

local semantic repair states には semantic repair words が作用する。
relation soundness、stabilizer completeness、local transitivity から
`M_sem`-torsor structure を導き、selected local repairs \(p_i\) の差

\[
p_j|_{U_{ij}}=r_{\mathrm{sem},ij}+p_i|_{U_{ij}}
\]

として semantic residual を生成する。triple overlap 上の torsor 計算から
\(\delta^1r_{\mathrm{sem}}=0\) を証明し、local atlas の変更が
\(\delta^0\)-像だけを加えることを証明する。

### 4.4 Semantic Repair Additive H¹

三項 complex

\[
C^0\xrightarrow{\delta^0}C^1\xrightarrow{\delta^1}C^2
\]

と

\[
Z^1=\ker\delta^1,\qquad
B^1=\operatorname{im}\delta^0,\qquad
H^1_{\mathrm{sem}}=Z^1/B^1
\]

を導入する。

必須の結論は次である。

\[
[r]=[0]\iff r\in B^1
\]

これにより、局所調整で消える residual と、cohomology class として残る residual を区別する。

### 4.5 The SAGA Comparison Theorem

この章を数学的中心とする。

必須項目は次である。

1. semantic atom と repair relation から独立に生成される semantic repair complex
2. Atom-indexed equation system、\(Q_E\)、AAT cover から独立に生成される Čech complex
3. semantic mismatch と equation local-lift mismatch から別々に生成される二つの residual
4. supported semantic generator を equation residual class へ送る一次写像
5. repair relation soundness / completeness と equation generator completeness
6. presentation exactness から構成される coefficient isomorphism
7. coefficient isomorphism から構成される degreewise comparison map
8. differential compatibility の成分計算
9. cocycle と coboundary relation の保存・反映
10. 商上の well-defined map と inverse
11. `H¹` equivalence と residual class 対応
12. true sheaf descent を実際に用いる grounded global gluing

中心定理は theorem box で提示する。

\[
H^1_{\mathrm{sem}}(\mathcal U)
\cong
\check H^1(\mathcal U,Q_E)
\]

comparison map は generator-level equation interpretation を free abelian group へ延長し、
local repair relation で割ることで構成する。kernel と relation の一致が単射性を、
equation generator completeness が全射性を与える。restriction naturality が
cochain differential との可換性を与える。

presentation comparison core は任意の target coefficient `Q` と generator map `χ` だけを受け取る。
別の equation-semantics statement が第III部の displayed residual interpretation から
`Q=Q_E` と `χ=χ^E` を構成する。true sheaf descent と finite matrix realization も
それぞれ別 statement に置く。

semantic repair complex を Čech complex の reindex / transport として定義すること、
comparison equivalence を supplied data として受け取ること、semantic residual を
幾何側 residual の逆像として定義することでは、この章の要件を満たさない。

displayed equation fulfillment が displayed interpretation class を零へ送る第III部の定理は、
presentation exactness と selected residual class の計算から分けて説明する。

### 4.6 Lean Formalization

Lean 章は、statement と依存関係を監査可能にした成果として構成する。

必須項目は次である。

- 数学節と Lean module の対応
- release 時点の theorem spine
- canonical entry declaration
- law-dependent conclusion と generated comparison conclusion の分解
- lawful firing instance
- circle-nerve nonzero instance
- theorem / declaration / status ledger
- axiom audit と CI

依存図は概ね次の形で示し、release source に合わせて正確な declaration 名へ置き換える。

```text
semantic atoms + support + repair relations
  -> M_sem
  -> C_sem and r_sem

equation system E
  -> Q_E
  -> C_E and r_E

primary generator interpretation + presentation exactness
  -> Phi
  -> cochain commutation
  -> H¹ comparison and residual correspondence

true sheaf condition
  -> corrected matching family
  -> actual global repair
```

circle-nerve instance は、SAGA comparison が零類の構成だけでなく非零類にも作用する
mathematical witness として提示する。ここでは有限数学そのものに焦点を合わせる。

#### 4.6.1 プレプリント初稿の SAGA claim / Lean status

数学本文は数学的 statement と proof に専念し、実装状況は本節で declaration 単位に記録する。

| claim | 数学 source | Lean status |
| --- | --- | --- |
| semantic presentation `M_sem` と independently generated complex | 第X部 定義 3.1–3.4、命題 3.3 | `Formal/AG` では未証明。Issue #3757 |
| semantic mismatch からの cocycle と choice independence | 第X部 定義 4.2、補題 4.3、定理 4.4 | generic statement は `Formal/AG` では未証明。G-07 の `localLiftDifferenceFor_cocycle`、`connectingClass_choice_independent` は `unported (Research-proved)` |
| `Q_E` と restriction の equation generation | 第III部 定理 11.4、第X部 定義 5.1 | `Formal/AG/LawAlgebra/LawEquation.lean` の `obstructionQuotientRestrict`、`obstructionQuotientCoefficient`、`obstructionQuotientPresheaf`、`generatedCoefficient_package`、`interpret` |
| primary presentation から `M_sem≃Q_E` | 第X部 定理 6.3、系 6.7 | `Formal/AG` では未証明。Issue #3757 |
| cochain commutation と `H¹` comparison | 第X部 定理 7.2、7.4 | `Formal/AG/Cohomology/CochainComparison.lean` は supplied cochain equivalence からの商上輸送を形式化済み。SAGA exact presentation から comparison を構成する段は Issue #3757 |
| residual class correspondence | 第X部 定理 7.5 | `Formal/AG` では未証明。Issue #3757 |
| zero class と actual global repair | 第X部 定理 8.2 | G-07 の `connectingClassFor_isZero_iff_nonempty_globalLift` と `connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair` は `unported (Research-proved)` |
| G-07 conormal package | 第X部 定理 9.1 | `lawGeneratedConormalFirstOrderDescent_package` は `ResearchLean` で証明済み。本体への蒸留は Issue #3757 |
| circle zero/nonzero witness | 第X部 例 10.2、付録 B.9 | `conormalH1_zero_nonzero_pair` を含む G-07 Boolean-circle witness は `unported (Research-proved)` |

`lake build` の成功、declaration 名の存在、status 表の更新は、
未証明の general SAGA statement の代替にしない。

#### 4.6.2 G-07 declaration map と依存監査

G-07 の reuse / generalize / specialization を実装宣言へ接続する。

| G-07 declaration | 第X部での扱い | 数学的役割 |
| --- | --- | --- |
| `PatchReadingSource` | generalize | semantic local input と required-law support の一次 source |
| `OverlapLawCombination` | generalize | pairwise reading difference を required-law generators で表す局所 relation |
| `evaluateCombination_mem_obstructionIdeal` | reuse pattern | generator relation が equation ideal で零になる soundness |
| `rawQ0_pair_compatible` | specialization | required-law relationから `O/I` compatibility を生成 |
| `LocalLiftData` | reuse | base section と explicit local lifts だけを入力にする local-lift problem |
| `localLiftDifferenceFor` | reuse | local lifts の差から kernel-valued residual を生成 |
| `localLiftDifferenceFor_cocycle` | reuse | `d¹d⁰=0` と kernel identification による cocycle proof |
| `connectingClass_choice_independent` | reuse | local lift choice の変更が `δ⁰`-像になる証明 |
| `correctedLocalLiftCochain_d_eq_zero` | reuse | zero class から matching correction を構成 |
| `amalgamatedCorrectedLocalLift` | reuse | true sheaf amalgamation による actual global lift |
| `connectingClassFor_isZero_iff_nonempty_globalLift` | reuse | class zero と global lift existence の同値 |
| `SemanticFirstOrderRepair` | specialization | conormal-valued correction primitive を独立に定義 |
| `SemanticFirstOrderRepairEquiv` | specialization | correction primitive と global first-order lift の構成的同値 |
| `connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair` | specialization | conormal class zero と semantic first-order repair existence の同値 |
| `lawGeneratedConormalFirstOrderDescent_package` | specialization | choice independence、effectivity、`H⁰` torsor、zero/nonzero witness の統合 |

G-07 の実装 route は `LawGeneratedLargeCoefficientCech`、sheafified short exact sequence、
local-lift difference、sheaf amalgamation から構成される。
`LawGeneratedLargeCoefficientCech` は generic な
`Formal.AG.Cohomology.CochainComparison` を使うが、
`SemanticRepairCechGrounding`、`SagaComparison`、`H1Comparison` の
SAGA-specific route を import しない。したがって一般 SAGA comparison を premise とせず、
第X部 定理 9.1 の first-order conormal specialization として接続できる。

### 4.7 ArchSig: Executable SAGA Diagnosis

ArchSig 章は、有限 input から diagnosis へ進む計算を示す。

入力 artifact は少なくとも次を含む。

- ArchMap
- LawPolicy
- law-equation surface
- MeasurementProfile
- RepairPlan
- incidence / comparison data
- gate policy

数学と計算の対応を表にする。

| 数学 | ArchSig |
| --- | --- |
| chart / overlap / triple overlap | repair-plan complex |
| residual \(r\) | residual support |
| \(r\in B^1\) | boundary-membership computation |
| semantic closure | coverage / faithfulness diagnostics |
| \([r]\in Z^1/B^1\) | residual-class invariant |
| comparison data | incidence and cochain-map contract |
| zero-predicate transfer | comparison invariant |
| global coherence | repair-gluing verdict |

diagnostic staircase を次の順で示す。

```text
local law evaluation
  -> generated coefficient reading
  -> cocycle verification
  -> boundary membership
  -> residual H¹ class
  -> semantic / Čech transfer
  -> gate decision
  -> repair comparison
```

各結果には input digest、source reference、run manifest、assumption ledger、packet、
gate output を対応させる。

### 4.8 The Cape of Good Hope: A One-Cent Obstruction

この章で一セントを初めて明かす。

導入文の核を次とする。

> The mathematical construction developed so far is deliberately general. Its first
> full-scale application to an existing codebase, however, revealed something remarkably
> small: one cent.

case study は次の順で構成する。

1. 対象 repository と commit
2. 三つの monetary convention
3. chart、overlap、triple-overlap data
4. local grounding
5. nonzero residual class
6. semantic / Čech comparison
7. gate result
8. hypothetical repair
9. repaired measurement
10. head / repaired comparison

結果表は、release artifact の実値で固定する。

| Stage | Head | Repaired |
| --- | --- | --- |
| local grounding | release result | release result |
| residual boundary | release result | release result |
| residual class | release result | release result |
| comparison | release result | release result |
| gate | release result | release result |

この case study は、各 chart の局所的な成立と、loop 全体の貼り合わせ不能性が同時に
観測された構造を中心に置く。

章の結語では、小さな硬貨を理論が実務へ到達した証拠として描く。

> 私たちが見つけたのは、わずか一セントのずれだった。
>
> しかし、その小さな硬貨は、Atom から始まり、方程式、ideal、sheaf、cohomology を経て、
> Lean で形式化された理論が、実在する software の上で一つの障害を捉えた証拠だった。
>
> 一セントは、理論が抽象の海を渡り切り、実務へ至る航路を見つけた最初の陸地だった。
> その小さな一セント硬貨は、私たちにとって大きな一歩であり、SAGA の喜望峰であった。

### 4.9 Discussion

Discussion は、SAGA が可能にしたことを正面から整理する。

- local lawfulness と global coherence を別の数学的対象として扱う
- architectural inconsistency を `Z¹/B¹` の class として扱う
- semantic repair と AAT geometry を comparison theorem で接続する
- repair plan を実装前に class の変化として測定する
- theorem、formalization、measurement を一つの provenance へ接続する

### 4.10 Related Work

関連研究の選定、比較表、引用候補、本文ドラフトは
[zenodo_saga_related_work.md](zenodo_saga_related_work.md) を作業面とする。
本文では Halley Young の 2026 年論文を最初の直接比較対象に置く。

関連研究は次の四群から選び、原典を直接確認する。

1. sheaf-cohomological program and system analysis
2. sheaf-based architecture and multi-view consistency
3. software architecture conformance and formal architecture description
4. mechanized mathematics and executable analysis

比較軸は次とする。

- local-to-global obstruction を equivalence class として扱うか
- semantic complex と geometric complex の comparison theorem を持つか
- machine-checked theorem chain を持つか
- executable finite measurement へ接続するか
- mathematical source、formal proof、measurement artifact の provenance を固定するか

必須の直接比較は次とする。

- Young 2026: semantic presheaf、program site、Čech `H¹`、Lean、Deppy
- Gibson 2026: architectural site、multi-view consistency、sheaf condition、Lean
- Felber–Flores–Galeana 2025: distributed task sheaf、global section、cohomological obstruction
- Abramsky 系: global-section obstruction と Čech cohomology
- architecture conformance 系: mismatch、reflexion model、formal connector、ADL

Young との比較では、AAT の二つの特徴を明示する。

1. AAT は programming language の syntax ではなく Atom と Law から architecture object を構成し、
   複数の言語、service、framework、storage representation を同じ幾何の上で扱う。
2. SAGA は実装上の型が一致していても、意味規約が貼り合わない構造を捉える。one-cent obstruction は、
   値が `string` として型整合していても、その価格意味論が service 間で一致しない実例である。

### 4.11 Future Work: The Rising Sea

Future Work は、喜望峰から開く研究計画を提示する。

#### Atom foundations

Atom の semantic identity、relation、provenance、composition を精密化し、
architecture geometry が立つ地盤を強化する。

#### Architecture schemes

Atom と Law から architecture scheme、lawful closed subscheme、scheme morphism へ進む。
software change を morphism として扱い、law transport、composition、deformation、
intersection、singularity、moduli、stack を同じ幾何学的言語へ置く。

#### Software Field Theory

AAT の architecture geometry を時間方向へ開き、artifact、practice、AI、review、CI、
operational feedback が software evolution の reachable future をどう変えるかを研究する。

#### Rising Sea

研究方法を次の一節へ収束させる。

> 一セントの障害は、この海が現実へ届いた最初の波だった。
>
> Atom から architecture scheme へ。
>
> architecture scheme から Software Field Theory へ。
>
> 局所的な整合性の診断から、software の未来そのものの計算へ。
>
> **海は、ここからさらに上昇する。**

### 4.12 Conclusion

Conclusion は三つの成果を再提示する。

1. semantic repair obstruction を `H¹` として定式化した。
2. SAGA 比較定理により、AAT site 上の Čech `H¹` へ接続した。
3. Lean 形式化と ArchSig measurement により、定理が実在 software の一セントへ到達した。

最後は Cape of Good Hope から Rising Sea への連続性を保ち、長期研究計画へ視線を開く。

## 5. 図表要件

### 5.1 必須図

1. **SAGA construction spine**

   ```text
   Atom -> Equation -> Ideal -> Q_E -> Site -> Čech -> H¹
   ```

2. **Semantic / Čech comparison**

   二つの complex と \(\kappa^0,\kappa^1,\kappa^2\) の可換図。

3. **Lean theorem dependency graph**

   数学本文、Lean declaration、finite witness の接続。

4. **ArchSig diagnostic staircase**

   input artifact から residual class、comparison、gate、repair comparison まで。

5. **The One-Cent Obstruction**

   三頂点、三辺、対象の face data を示す図。実コード参照へ接続する。

6. **From the Cape of Good Hope to the Rising Sea**

   ```text
   SAGA
     -> Atom foundations
     -> architecture schemes
     -> scheme morphisms as events
     -> SFT
     -> reachable software futures
   ```

### 5.2 必須表

1. contributions
2. mathematical theorem / Lean declaration / status
3. lawful witness / nonzero circle witness
4. mathematics / ArchSig correspondence
5. head / repaired measurement
6. claim-to-evidence matrix
7. Zenodo artifact manifest

## 6. Claim-to-Evidence 要件

論文で使う claim は、次の matrix に登録する。

| ID | Paper claim | Math source | Lean declaration / status | ArchSig evidence | Release artifact |
| --- | --- | --- | --- | --- | --- |
| M-* | 数学的構成・定理 | required | 対応する場合に必須 | - | theorem map |
| L-* | Lean 形式化 | statement source | required | - | source / log / audit |
| A-* | 有限 measurement | 対応する定義・定理 | 利用する theorem | required | input / packet / manifest |
| E-* | 実コード上の観測 | 数学的 reading | 利用する theorem | required | source refs / digest / output |

各行は次を満たす。

- claim の主語、対象、条件、結論が一文で特定されている
- 数学 source の節または theorem が特定されている
- Lean claim は exact declaration と source file に対応する
- measurement claim は固定 input と output field に対応する
- 実コード claim は repository、commit、source reference に対応する
- release artifact 内の相対 path から証拠へ到達できる

## 7. Zenodo 成果物

### 7.1 Deposit の単位

Zenodo deposit は、論文 PDF と再現 artifact を同じ release identity へ結びつける。
Git tag、release commit、paper version、artifact manifest、checksum を一致させる。

推奨構成は次である。

```text
paper.pdf
paper-source/
README.md
CITATION.cff
LICENSES/
SHA256SUMS
manifest.json

math/
  theorem-map.md
  claim-to-evidence.csv

lean/
  source-manifest.txt
  declaration-manifest.md
  status-ledger.md
  focused-checks.txt
  axiom-audit.txt
  ci-links.md

archsig/
  README.md
  inputs/
  head-output/
  repaired-output/
  comparison-output/
  gate-output/
  run-manifest.json

reproduction/
  README_REPRODUCE.md
  reproduce.sh
  expected-results.md
```

### 7.2 固定情報

成果物には次を記録する。

- repository URL
- release tag
- commit SHA
- Lean version
- Mathlib revision
- Rust toolchain
- OS と必要 dependency
- exact reproduction commands
- input digests
- expected output
- artifact checksums
- license
- citation metadata

### 7.3 再現確認

再現手順は clean checkout で実行し、次を確認する。

- focused Lean checks が対象 declaration を elaborate する
- axiom audit が対象 declaration を列挙する
- ArchSig が固定 input から expected packet を生成する
- head と repaired の比較が論文表と一致する
- manifest と checksum が deposit 内の file と一致する
- artifact 内の path と identifier が移植可能な形に整理されている

本体の full Lean build は PR 作成後の CI を証拠として用いる。ローカル検証は repository の
Lean build 運用に従い、対象となる非 aggregate file の focused check を実行する。

### 7.4 Zenodo metadata

deposit の metadata は paper、repository release、citation file と一致させる。

| Field | 要件 |
| --- | --- |
| Title | paper title と一致 |
| Creators | 著者名、affiliation、ORCID を確認 |
| Description | abstract と三つの contribution を要約 |
| Publication date | deposit 公開日 |
| Resource type | publication / preprint または article から公開形態に合う値を選択 |
| Version | paper version と release tag を一致 |
| Language | paper 本文の言語 |
| Keywords | AAT、SAGA、software architecture、algebraic geometry、Čech cohomology、Lean、ArchSig |
| License | paper、source、code、data の各 license と整合 |
| Visibility | paper と再現 artifact を公開する release では Public を選択 |
| Related identifiers | GitHub release、repository、関連する dataset / software release |
| Communities | 適合する Zenodo community を公開時に確認 |
| Funding | 該当情報を事実どおり記録 |

reserved DOI を paper source と `CITATION.cff` に反映し、最終 PDF、deposit metadata、
release notes の identifier を一致させてから公開する。新versionの公開時は Zenodo の
version relation を用い、concept DOI と version DOI の役割を citation guide に記録する。

paper PDF を default preview に指定する。公開後の file 更新は、再現対象が変わる更新では
新しい version record を作成し、metadata 修正は既存 record の metadata edit として扱う。

Zenodo 操作時に参照する公式資料を次に固定する。

- [Deposit documentation](https://help.zenodo.org/docs/deposit/)
- [Reserve a DOI](https://help.zenodo.org/docs/deposit/describe-records/reserve-doi/)
- [Manage versions](https://help.zenodo.org/docs/deposit/manage-versions/)
- [DOI versioning](https://zenodo.org/help/versioning)
- [About records](https://help.zenodo.org/docs/deposit/about-records/)

## 8. 優先度別チェックリスト

checklist は GitHub Issue へ分割できる単位で管理する。

### P0: 論文と deposit を成立させる

#### P0-0 SAGA 数学本文の再構成

- [ ] Issue #3760 の paper-level target statement を固定する
- [ ] semantic repair complex を semantic atom と repair relation から独立に構成する
- [ ] Čech complex を Atom-indexed equation system、\(Q_E\)、AAT cover から独立に構成する
- [ ] semantic-to-geometric comparison map を一次データから構成する
- [ ] differential compatibility、cocycle / coboundary 保存、商上の `H¹` 同値を証明する
- [ ] semantic mismatch から residual を生成し、幾何側 residual への写像定理を証明する
- [ ] comparison core、equation semantics、true sheaf descent、finite realization を分離する
- [ ] conclusion で使わない sheaf、gluing、finiteness、displayed-source 仮定を削除する
- [ ] additive `H¹` theorem と torsor / higher / stack の statement を分離する
- [ ] G-07 declaration の reuse / generalize / specialization と循環しない依存を固定する
- [ ] protected math source の独立 LLM レビューを完了する
- [ ] paper claim と現行 Lean status を別表で固定する
- [ ] Issue #3760 を close する
- [ ] general SAGA Lean 実装を Issue #3757 へ引き渡す

#### P0-1 Paper identity

- [ ] title と subtitle を固定する
- [ ] research question を一文で固定する
- [ ] central theorem を release statement に合わせて固定する
- [ ] contribution 三項目を固定する
- [ ] abstract を完成させる

#### P0-2 Mathematical source map

- [ ] SAGA に必要な数学本文の節を列挙する
- [ ] paper theorem と数学本文 theorem を対応させる
- [ ] notation table を作る
- [ ] semantic `H¹` と Čech `H¹` の comparison diagram を作る
- [ ] grounded global gluing の statement と条件を固定する

#### P0-3 Lean theorem manifest

- [ ] exact declaration manifest を作る
- [ ] theorem dependency graph を作る
- [ ] 各 declaration の statement を paper claim と照合する
- [ ] Lean status table を作る
- [ ] lawful firing instance を固定する
- [ ] circle-nerve nonzero instance を固定する
- [ ] focused check、axiom audit、CI evidence を保存する

#### P0-4 ArchSig measurement manifest

- [ ] paper で使う input schema と fixture を固定する
- [ ] residual と `B¹` membership の計算を固定する
- [ ] residual-class invariant を固定する
- [ ] comparison output を固定する
- [ ] gate output を固定する
- [ ] head / repaired comparison を固定する
- [ ] input digest と run manifest を保存する

#### P0-5 One-Cent case study

- [ ] 対象 OSS repository と commit を固定する
- [ ] 三つの chart と source reference を固定する
- [ ] selected complex を図示する
- [ ] local grounding の証拠を保存する
- [ ] nonzero class の証拠を保存する
- [ ] hypothetical repair input を固定する
- [ ] repaired result と比較結果を保存する
- [ ] Cape of Good Hope 節を執筆する

#### P0-6 Paper body

- [ ] Introduction を執筆する
- [ ] AAT foundations を執筆する
- [ ] semantic repair と additive `H¹` を執筆する
- [ ] SAGA comparison theorem を執筆する
- [ ] Lean formalization を執筆する
- [ ] ArchSig diagnosis を執筆する
- [ ] One-Cent case study を執筆する
- [ ] Discussion と Related Work を執筆する
- [ ] Future Work と Conclusion を執筆する

#### P0-7 Figures and tables

- [ ] 必須図六点を完成させる
- [ ] 必須表七点を完成させる
- [ ] caption だけで各図表の要点が読める状態にする
- [ ] 数式、図、表、本文の notation を統一する

#### P0-8 Claim-to-Evidence

- [ ] 全 paper claim を matrix に登録する
- [ ] 数学 claim を source theorem へ接続する
- [ ] Lean claim を declaration と status へ接続する
- [ ] measurement claim を packet field へ接続する
- [ ] empirical claim を source reference と digest へ接続する
- [ ] 全 artifact path を deposit 内の相対 path で解決する

#### P0-9 Zenodo bundle

- [ ] release tag と commit を固定する
- [ ] paper PDF と source を収録する
- [ ] Lean evidence を収録する
- [ ] ArchSig inputs と outputs を収録する
- [ ] reproduction guide を収録する
- [ ] manifest、checksum、license、citation metadata を完成させる
- [ ] clean checkout reproduction を完了する

#### P0-10 Zenodo metadata and publication

- [ ] 著者名、affiliation、ORCID を確認する
- [ ] title、description、version、language、keywords を固定する
- [ ] resource type、visibility、default preview を固定する
- [ ] paper、source、code、data の license を確認する
- [ ] GitHub release と関連成果物の identifier を登録する
- [ ] reserved DOI を paper、`CITATION.cff`、release notes へ反映する
- [ ] concept DOI と version DOI の citation guide を作る
- [ ] deposit preview と checksum を照合して公開する
- [ ] 公開後の DOI landing page と download artifact を確認する

#### P0-11 Final review

- [ ] 数学本文と paper statement を直接照合する
- [ ] Lean source と status table を直接照合する
- [ ] ArchSig output と paper result table を直接照合する
- [ ] claim-to-evidence matrix の全行を監査する
- [ ] PDF の数式、図、参照、link、font、metadata を確認する
- [ ] deposit preview の file、metadata、version、license を確認する

### P1: 説明力と再利用性を高める

#### P1-1 Verified certificate

- [ ] zero witness の verifier と artifact を固定する
- [ ] nonzero class の dual witness を固定する
- [ ] verifier の property test を固定する
- [ ] circle instance と実コード instance の certificate を対応づける

#### P1-2 Independent artifact use

- [ ] analyzer と verifier の実行手順を分離する
- [ ] paper 専用 fixture bundle を作る
- [ ] container または再現可能な environment 定義を用意する
- [ ] 別環境で reproduction record を残す

#### P1-3 Explanatory assets

- [ ] interactive または高解像度の SAGA comparison figure を用意する
- [ ] Lean dependency graph の machine-readable source を用意する
- [ ] One-Cent figure を source landing 付きで用意する
- [ ] Cape of Good Hope から Rising Sea への research map を用意する

#### P1-4 Related work matrix

- [ ] 各研究群の原典を確認する
- [ ] DOI、著者、年、venue を確認する
- [ ] comparison axes を表にする
- [ ] AAT / SAGA の novelty claim を claim-to-evidence matrix へ登録する

## 9. 完了条件

### 9.1 数学プレプリント初稿

Zenodo に提出する数学プレプリント初稿は、次の条件で candidate となる。

1. Issue #3760 が完了し、semantic repair complex と equation Čech complex が独立に生成され、
   comparison map、cochain compatibility、residual 対応、商上の `H¹` 同型が紙上証明されている。
2. zero class から corrected matching family を構成し、true sheaf descent により
   actual global repair を得る証明がある。
3. G-07 の reuse / generalize / specialization と循環しない依存が declaration 単位で示されている。
4. circle instance が非零 class に対する comparison の具体的 witness を与える。
5. paper theorem、数学 source、現行 Lean status が別表で対応し、
   `unported (Research-proved)` と未証明の general statement を区別している。
6. protected math source の独立 LLM review と人間の差分確認が完了している。
7. Abstract、本文、図、notation、reference が同じ fixed statement を使う。

### 9.2 Math + Lean + ArchSig 統合版

数学、Lean、ArchSig を一つの主張系列として提示する統合版は、さらに次を要求する。

1. Issue #3757 が完了し、general SAGA statement と residual correspondence が
   `Formal/AG` に蒸留されている。
2. 各 Lean claim が release 時点の exact declaration と axiom audit に接続されている。
3. ArchSig measurement、one-cent case study、input digest、run manifest、reproduction bundle が
   同じ release identity を参照する。
4. Future Work が Atom foundations、architecture schemes、SFT を Rising Sea として接続する。
5. paper PDF、source、Lean evidence、ArchSig evidence、checksum、metadata の最終レビューが完了している。
