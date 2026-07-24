# Zenodo 向け SAGA プレプリント計画

## 0. この文書の役割

この文書は、Zenodo で公開する SAGA プレプリント初稿について、論文が説明する対象、
各対象に要求する証拠、公開成果物、完了条件を固定する。

論文の詳細な章構成、本文、証明記述、図表の個数は執筆時に決定する。本書は、
「この論文で何を説明するか」の固定に集中する。

論文を支える正本は次のとおりである。

| 対象 | 正本 |
| --- | --- |
| AAT と SAGA の数学 | `docs/aat/algebraic_geometric_theory/` |
| Lean 形式化 | `Formal/AG/` と release 時点の監査記録 |
| ArchSig の計算 | `tools/archsig/` |
| one-cent 診断 | 固定 input、run manifest、packet、比較結果 |
| 論文の主張と読み | 本書および将来の paper source |

## 1. プレプリント初稿の identity

### 1.1 タイトル候補

> **SAGA: A Comparison Theorem for Local-to-Global Software Architecture**
>
> *From Semantic Repair Cohomology to Algebraic-Geometric Descent*

### 1.2 公開時の中心主張

プレプリント初稿は、次の三層を一つの研究成果として提示する。

1. **数学面: 完成版**

   semantic repair cohomology と、Atom-indexed architectural equation system から生成される
   AAT Čech cohomology の比較を構成し、SAGA 比較定理と residual class 対応を証明する。

2. **Lean: 現状 status**

   SAGA 数学のうち release 時点で形式化されている定義、定理、witness、proof chain を
   declaration 単位で示し、数学本文との対応を固定する。

3. **ArchSig: one-cent**

   one-cent obstruction を対象として、数学的対象が有限 architecture evidence から
   どのように計算され、repair 前後でどのように変化するかを再現可能な形で示す。

この三層の役割を次のように固定する。

| 層 | 論文での役割 |
| --- | --- |
| 数学 | プレプリントの主成果 |
| Lean | 数学成果に対する release 時点の機械形式化 status |
| ArchSig | one-cent obstruction に対する有限かつ実行可能な realization |

### 1.3 論文全体を貫く読み

```text
完成した SAGA 数学
  -> release 時点の Lean 形式化
  -> ArchSig による one-cent obstruction の有限計算
  -> repair 前後の比較
```

プレプリント初稿は、数学的比較定理が形式化と有限 measurement へ降り、
実在 software architecture の semantic repair を読めることを示す。

## 2. 記述ポリシー

### 2.1 成果から書く

各章は、構成した対象、証明した定理、得られた計算、研究上の意義から始める。
statement の条件は、その定理を正確に読むための数学データとして説明する。

論文の標準的な説明順を次とする。

1. 何を構成したか
2. 何を証明したか
3. なぜ重要か
4. ArchSig で何を測定したか
5. そこからどの研究へ進むか

各節と各段落の冒頭には、対象の肯定的な定義、達成した構成、証明した結果、
得られた測定、または研究上の価値を置く。

### 2.2 適用条件と status 情報を配置する

適用条件と status 情報は、それを正確に読める場所へ集約する。

| 情報 | 配置 |
| --- | --- |
| theorem の仮定と対象 | statement と proof の近く |
| Lean の proof status、未証明、未接続、未移植 | `Lean Formalization Status` |
| ArchSig の selected input と measurement condition | one-cent の計算結果の近く |
| empirical claim の対象 repository、commit、evidence | one-cent case study と artifact manifest |
| 将来の定理、形式化、tooling | `Discussion and Research Outlook` |

Introduction、identity、各章の導入、Conclusion は、主要成果とその意義を前面に置く。
同じ適用条件や status 一覧は一つの担当箇所で管理し、本文の各所から参照する。

### 2.3 Identity を肯定形で書く

数学、Lean、ArchSig の identity は、それぞれが構成、証明、記録、計算するものから書く。

| 対象 | 採用する identity |
| --- | --- |
| SAGA | semantic repair cohomology と equation-generated AAT Čech cohomology を比較する定理 |
| Lean | SAGA 数学の machine-checked definitions、theorems、witnesses、proof chain を記録する形式化 |
| ArchSig | ArchMap、LawPolicy、MeasurementProfile から residual、class、comparison、gate を計算する measurement system |

各 identity は固有の入力、構成、出力、成果を述べる。異なる種類の道具との比較による
免責表現は identity から分離する。実在する誤読を解く説明は、該当する claim の近くに
一度だけ配置する。

### 2.4 条件を成果へ接続して書く

仮定、selected input、coverage、coefficient、measurement profile は、
その条件によって構成できる対象と証明できる結論へ直接接続する。

```text
input
  -> construction
  -> theorem or measurement
  -> evidence
  -> significance
```

この因果順により、数学的な相対性、Lean status、ArchSig measurement の精度を保ちながら、
論文の中心を成果へ置く。

### 2.5 簡潔で読みやすい文体にする

一文に一つの中心 claim を置き、具体的な主語と動詞で書く。同じ概念には同じ用語を使い、
同義語の連鎖、言い換えの反復、説明済み事項の再列挙を整理する。

列挙は、各項目が独立した情報を持つ場合に使う。共通規則や説明は担当箇所で一度定義し、
後続箇所から参照する。段落ごとに役割を一つに絞り、短い文で論理の接続を示す。

## 3. 章立て

章立ては、各章が説明責任を持つ対象を固定する。節構成、証明の配置、図表、
本文の展開順は執筆時に決定する。

| 章 | 仮題 | この章で説明するもの |
| --- | --- | --- |
| 1 | Introduction | local-to-global architecture problem、SAGA の研究課題、数学完成版・Lean status・ArchSig one-cent の三層 |
| 2 | The AAT Approach | architecture を Atom と連立方程式から幾何対象として構成する方法、その利点、SAGA がこの方法から生まれる理由 |
| 3 | AAT Foundations for SAGA | SAGA を読むために必要な Atom、architecture object、Atom-indexed architectural equation system、AAT site、cover、equation-generated coefficient |
| 4 | Semantic Repair and Equation-Generated Geometry | semantic repair complex と equation-generated Čech complex の独立した構成、および両者の residual |
| 5 | The SAGA Comparison Theorem | comparison map、differential compatibility、`H¹` 同型、residual class 対応、global repair |
| 6 | Lean Formalization Status | paper claim と Lean declaration の対応、release 時点の proof status、仮定、axiom 状況、未証明・未接続・未移植 |
| 7 | ArchSig and the One-Cent Obstruction | one-cent の architecture evidence、有限計算、SAGA comparison、repair 前後の変化、再現方法 |
| 8 | Related Work | sheaf cohomology、architecture consistency、formal architecture、mechanized mathematics、executable analysis との比較 |
| 9 | Discussion and Research Outlook | SAGA の意義と、Atom foundations、architecture schemes、Software Field Theory、Rising Sea へ進む研究方向 |
| 10 | Conclusion | 完成した数学、Lean の形式化到達状況、one-cent realization によって得られた成果 |

## 4. AAT アプローチで説明するもの

`The AAT Approach` は、software architecture を代数幾何として構成する方法と、
その方法が開く分析能力を説明する。定義と証明に必要な数学的対象は、
続く `AAT Foundations for SAGA` が担当する。

この章は次を説明する。

- primitive architectural fact を Atom として公理化し、言語や framework を越えた
  architecture object を生成すること
- 複数の architecture condition を Atom-indexed architectural equation system として組織し、
  residual、obstruction ideal、lawful locus を構成すること
- 局所 context、cover、restriction、overlap を AAT site として組織し、
  local-to-global problem を sheaf と cohomology で扱うこと
- failure を residual、ideal、cohomology class、Tor conflict、singularity として構造化し、
  diagnosis と repair を同じ幾何対象の変化として読むこと
- ringed geometry を構成することで、scheme、derived intersection、deformation、
  monodromy、stack、base change の道具が architecture 上で働くこと
- vocabulary、equation system、coverage、coefficient を固定した相対的な幾何として、
  claim と計算の provenance を追跡できること
- SAGA が、semantic repair obstruction と equation-generated Čech obstruction を比較することで、
  AAT アプローチの local-to-global 能力を具体化すること

この章の中心メッセージを次に固定する。

> AAT constructs software architecture as a relative algebraic geometry generated
> from primitive architectural facts and simultaneous architectural equations,
> so that local consistency, global obstruction, and repair become geometric objects.

`AAT Foundations for SAGA` は、このアプローチを受けて、SAGA の statement と proof に
必要な数学的対象を定義する。

## 5. 数学面で説明するもの

数学面は、SAGA の完成した理論を論文の中心として説明する。

論文では、Atom-indexed architectural equation system `E` を数学上の一次対象とする。
自然言語の architectural law reading は `E` から導かれる表示 `U_E` として導入する。

論文は次の数学的内容を読者が追える状態にする。

- SAGA に必要な Atom、architecture object、Atom-indexed architectural equation system、
  AAT site、cover、equation-generated coefficient の定義
- semantic atom、semantic projection、repair support、局所 repair relation からの
  semantic repair complex と semantic residual の構成
- Atom-indexed equation system、equation-generated coefficient、AAT cover からの
  cover-relative Čech complex と幾何側 residual の構成
- semantic data と Atom / equation / cover data からの comparison map の構成
- comparison map と differential の可換性
- cocycle、coboundary、商上の `H¹` 同型
- semantic residual class と幾何側 residual class の対応
- class vanishing と global repair を結ぶ定理
- 一般定理の内容を具体的に読める有限 witness

数学本文は、各構成の入力、定理の仮定、結論、証明を論文内で完結して読める形にする。
AAT 全体系の紹介は SAGA を読むために必要な対象へ集中し、architecture schemes、
Software Field Theory、Rising Sea は研究展望として位置づける。

数学面の証拠は次を要求する。

- canonical な数学本文
- paper theorem と canonical theorem の対応表
- notation の対応
- 定理ごとの仮定と依存
- protected math source に対する独立レビュー記録

## 6. Lean で説明するもの

Lean は、SAGA 数学の release 時点における形式化 status を正確に報告する。

論文は次を説明する。

- 形式化済みの主要定義
- 形式化済みの主要定理と witness
- paper theorem と Lean declaration の対応
- 各 declaration が実際に使用する仮定
- theorem chain の接続状況
- `#print axioms` などによる axiom 状況
- 数学本文に対して残る未証明、未接続、未移植

status は少なくとも次の情報を持つ表として固定する。

| 項目 | 内容 |
| --- | --- |
| Mathematical claim | 論文中の数学的主張 |
| Lean declaration | 対応する宣言名 |
| Status | `docs/aat/guideline.md` の Lean status vocabulary |
| Assumptions | declaration が使用する仮定 |
| Source | release 内の source path |
| Evidence | focused check と axiom audit |

論文の Lean claim は、release tag で再確認した declaration と監査結果に基づく。
形式化の到達地点を statement の強さと proof-use によって記述し、数学本文との対応を
読者が直接追える状態にする。

## 7. ArchSig と one-cent で説明するもの

ArchSig は、one-cent obstruction を SAGA の有限 realization として示す。

論文は次を説明する。

- 対象 software artifact と固定 commit
- one-cent を構成する architectural facts
- 使用する Atom vocabulary、`LawPolicy`、MeasurementProfile、cover、および
  `LawPolicy` が固定する selected equation reading
- source evidence から ArchMap input への対応
- residual、`B¹` membership、`H¹` class の計算
- semantic residual と equation-generated residual の comparison
- diagnosis と SAGA 数学の対応
- repair input と repair 後の再計算
- repair 前後の class、comparison、gate の変化

one-cent の主張は固定 input と出力 field へ対応させる。再現 bundle は、第三者が同じ
ArchSig version と input から論文中の結果を生成できる状態にする。

ArchSig の経験的 claim は one-cent case study に集中する。広い benchmark 評価、
一般的な検出性能、複数 repository に対する性能比較は、別の実証研究として扱う。

## 8. Claim の種類と証拠

論文中の claim は、数学、Lean、measurement、実コード観測を区別する。

| Claim type | 論文で述べること | 必要な一次証拠 |
| --- | --- | --- |
| Mathematics | 定義、構成、定理、証明 | canonical math source、theorem map |
| Lean | 形式化済みの範囲と proof status | declaration、source、focused check、axiom audit |
| Measurement | 固定 input に対する ArchSig の計算結果 | packet、manifest、digest |
| Empirical | one-cent artifact 上の観測 | repository、commit、source reference、input |

各主要 claim は、主語、対象、仮定、結論を特定し、deposit 内の相対 path から証拠へ
到達できるようにする。

## 9. Related Work で説明するもの

Related Work は、SAGA の主成果を次の研究群の中へ位置づける。

- sheaf cohomology による program analysis
- sheaf による architecture と multi-view consistency
- local-to-global obstruction と global section
- software architecture conformance と formal architecture description
- mechanized mathematics と executable analysis

比較では、対象、site、係数の生成、`H¹` の意味、comparison theorem、repair、
Lean、実行系、実証単位を確認する。原典調査と比較候補は
[`zenodo_saga_related_work.md`](zenodo_saga_related_work.md) で管理する。

## 10. 研究展望として扱うもの

次の研究は、完成した SAGA 数学から開く方向として短く示す。

- Atom foundations の深化
- architecture schemes と morphism theory
- descent、moduli、stack、derived deformation
- Software Field Theory
- Rising Sea research program

プレプリント初稿では、これらの研究課題、期待される接続、次の数学的対象を示す。
個別の定理開発、Lean 実装計画、tooling roadmap はそれぞれの正本で管理する。

## 11. Zenodo 成果物

Zenodo deposit は、次の成果物を同じ release identity へ結びつける。

- paper PDF
- paper source
- mathematical theorem map
- Lean status table と監査結果
- one-cent の ArchSig inputs、outputs、comparison
- reproduction guide
- claim-to-evidence matrix
- manifest と checksums
- license と citation metadata

Git tag、release commit、paper version、artifact manifest、Zenodo metadata を一致させる。
deposit には repository URL、commit SHA、toolchain、実行 command、input digest、
expected output、license、citation 情報を記録する。

## 12. 優先度別チェックリスト

checklist は GitHub Issue へ分割できる単位で管理する。

### P0: プレプリント初稿と deposit を成立させる

#### P0-1 Scope と identity

- [ ] 数学完成版、Lean 現状 status、ArchSig one-cent の三層を固定する
- [ ] title、中心主張、用語を固定する
- [ ] mathematical theorem map を固定する

#### P0-2 Lean status

- [ ] paper claim と Lean declaration を対応させる
- [ ] declaration ごとの status、仮定、source、proof-use を固定する
- [ ] focused check と axiom audit の結果を固定する
- [ ] 未証明、未接続、未移植を正確に記録する

#### P0-3 ArchSig one-cent

- [ ] 対象 repository と commit を固定する
- [ ] source evidence と input artifact を固定する
- [ ] repair 前の residual、class、comparison、gate を固定する
- [ ] repair input と repair 後の結果を固定する
- [ ] run manifest、digest、expected output を固定する

#### P0-4 Paper

- [ ] AAT アプローチと、その幾何的な利点を説明する
- [ ] 数学完成版を論文内で完結して説明する
- [ ] Lean status を release snapshot として説明する
- [ ] one-cent を有限 realization として説明する
- [ ] Related Work と研究展望を完成させる
- [ ] 全 claim を一次証拠へ対応させる
- [ ] 各章を構成、証明、計算、意義から始める
- [ ] 適用条件と status 情報を担当箇所へ集約する
- [ ] 数学、Lean、ArchSig の identity を入力、構成、出力、成果から記述する
- [ ] 一文一 claim、用語の統一、段落ごとの単一責務を保つ

#### P0-5 Zenodo release

- [ ] PDF、source、evidence、reproduction bundle を作成する
- [ ] manifest、checksums、license、citation metadata を固定する
- [ ] reserved DOI と release identity を反映する
- [ ] clean checkout で one-cent の再現確認を行う
- [ ] deposit preview と公開後の download artifact を確認する

#### P0-6 Final review

- [ ] 数学本文と paper statement を直接照合する
- [ ] Lean status table と release source を直接照合する
- [ ] ArchSig output と paper result を直接照合する
- [ ] claim-to-evidence matrix を監査する
- [ ] 各節と各段落の冒頭が成果または価値を示していることを確認する
- [ ] 適用条件と status 情報が担当箇所へ集約されていることを確認する
- [ ] identity 文が固有の入力、構成、出力、成果だけで成立していることを確認する
- [ ] 同義語の連鎖、言い換えの反復、説明済み事項の再列挙が整理されていることを確認する
- [ ] PDF と deposit metadata を確認する

### P1: 説明力と再利用性を高める

- [ ] 数学、Lean、ArchSig の対応図を用意する
- [ ] one-cent の source landing を用意する
- [ ] verifier と machine-readable certificate を収録する
- [ ] 別環境で reproduction record を作成する
- [ ] Related Work の比較表を完成させる

## 13. 完了条件

Zenodo プレプリント初稿は、次をすべて満たした時点で release candidate となる。

1. SAGA 数学が完成版として論文内で説明され、canonical math source と一致している。
2. paper theorem、仮定、証明、数学 source の対応が固定されている。
3. Lean の形式化 status が release snapshot に基づき、declaration 単位で確認されている。
4. one-cent の source evidence、input、計算、comparison、repair 前後の結果が固定されている。
5. 数学、Lean、measurement、実コード観測の各 claim が一次証拠へ接続されている。
6. paper PDF、source、reproduction bundle、manifest、checksums、metadata が
   同じ release identity を参照している。
7. 数学、Lean status、ArchSig result、deposit に対する最終レビューが完了している。
