# ArchSig Website Improvement Policy

## 目的

ArchSig の解説サイトを、研究成果の仕様書ではなく、**公開製品マニュアル**として再設計する。

現在のサイトは、ArchSig の構成要素や概念は揃っている。しかし、初見の読者にとっては、最初に「何ができるのか」「どう使えばよいのか」「どのような価値があるのか」が伝わりにくい。

今後の改善方針は、次の順番に変えることである。

> 何ができる → すぐ試す → 例で腹落ち → 境界で信頼する → 参照で深掘る

ArchSig は、AAT / SFT の理論を背後に持つが、ArchSig の website では、最初から理論を前面に出しすぎない。まず製品としての利用価値を伝え、その後に理論的な奥行きを提示する。

---

## ArchSig の製品ポジション

ArchSig は、AI ネイティブな **Architecture Evidence Layer** である。

コード変更をレビュー可能なアーキテクチャシグナルに変換し、すべてのシグナルを構造・意味・運用の証拠に結びつけ、日々の PR レビューを通じてソフトウェア進化を制御可能にする。

### 英語コピー案

> ArchSig is an AI-native Architecture Evidence Layer that turns code changes into reviewable architectural signals, grounds every signal in structural, semantic, or operational evidence, and helps teams steer software evolution through everyday PR review.

### 日本語コピー案

> ArchSig は、コード変更をレビュー可能なアーキテクチャシグナルに変換し、すべてのシグナルを構造・意味・運用の証拠に結びつけ、日々の PR レビューを通じてソフトウェア進化を制御可能にする、AI ネイティブな Architecture Evidence Layer である。

---

## ArchSig の魅力 3つ

### 1. コード差分ではなく、アーキテクチャ変更をレビューできる

ArchSig は、PR の diff をそのまま読むのではなく、変更が設計上どのような意味を持つのかをレビュー可能な形に変換する。

扱う対象は、単なる import や依存関係だけではない。

- 依存関係の変化
- 境界越え
- 責務の移動
- 意味論的な結合
- 運用上の影響

これにより、レビューは「コードの読解」から「設計変化の判断」へ進化する。

### 2. すべてのシグナルを、構造・意味・運用の証拠に結びつける

ArchSig は、曖昧に「危険そう」と言うツールではない。

すべてのシグナルを、明示的な証拠に結びつける。

- **Structural evidence**: import, dependency, boundary, ownership
- **Semantic evidence**: business rule, responsibility, state transition, assumption
- **Operational evidence**: trace, incident, latency, error propagation

特に、LLM を意味論的観測器として利用することで、コードを読ませて直接 AIR を生成する運用も考えられる。

このとき重要なのは、LLM の出力を「判定」ではなく「意味論的観測」として扱うこと。

ArchSig は、曖昧な AI コメントを出すのではなく、境界づけられたアーキテクチャ証拠を生成する。

### 3. 日々の PR レビューを、ソフトウェア進化の理論へ接続する

ArchSig は、単なる linter やメトリクスダッシュボードではない。

PR レビュー、CI、feature report、AIR、operational feedback を通じて、日々の変更を Architecture Signature として蓄積する。

その先に SFT や AAT がある。

ArchSig は、ソフトウェア進化を日常の開発フローの中で観測可能にする道具である。

---

## ArchSig が生むアウトカム 3つ

### 1. PR レビューの質が上がる

ArchSig によって、レビュアーは細かい実装差分だけでなく、設計上の変化を見られるようになる。

レビュアーは次のような観点を持てる。

- どの境界が動いたか
- どの責務が移動したか
- どの意味論的前提が変わったか
- どの部分を重点的に読むべきか

アウトカムは、レビューが「コードの読解」から「設計変化の判断」へ進化することである。

### 2. アーキテクチャ劣化を早期に検知できる

AI 駆動開発では、コード生成速度が上がるぶん、設計劣化も高速化する。

ArchSig は、構造・意味・運用のシグナルを継続的に観測することで、アーキテクチャ負債が大きくなる前に兆候を検出する。

検知対象の例は次の通り。

- 境界の侵食
- 責務のにじみ出し
- 暗黙の業務ルールの混入
- 運用上の結合増加
- 負のアトラクターへの接近

アウトカムは、アーキテクチャ負債が大きくなる前に、レビュー可能な兆候として発見できることである。

### 3. AI エージェントが安全に走れる開発環境を作れる

AI エージェントが大量にコードを書く時代には、単にテストで止めるだけでは足りない。

必要なのは、AI が変更したコードを、アーキテクチャ上の意味として観測し続ける仕組みである。

ArchSig があると、次の流れが作れる。

1. AI が生成した変更を読む
2. AIR として意味論的に記述する
3. 構造・意味・運用の証拠に結びつける
4. 危険な変化を PR レビューへ返す
5. 安全な変更は高速に流す

アウトカムは、AI ネイティブな開発を、制御ではなく観測とフィードバックで安全にすることである。

---

## Website 改善の基本方針

### 1. 前半は「使い方」をわかりやすく丁寧に説明する

公開マニュアルの前半では、理論の正確さよりも、読者が迷わず最初の成功体験に到達できることを優先する。

前半で答えるべき問いは次の通り。

- ArchSig は何をするツールなのか
- 何をインストールすればよいのか
- 最初にどのコマンドを実行すればよいのか
- 出力のどこを見ればよいのか
- PR レビューではどう使えばよいのか

ここでは、Sig0、AIR、claim boundary などの概念名は出してよい。ただし、最初は必ず実務的な言い換えを添える。

例:

> Sig0 is the first architecture signature emitted by ArchSig. Think of it as the baseline observation of your repository.

### 2. 中盤は「日常利用」を支える

Getting Started の次に、日常的に使うための導線を用意する。

- Inputs
- Workflows
- Artifacts
- Reading Reports
- Operational Feedback

この領域では、CI、PR review、feature report、signature diff、operational feedback など、実務の流れに沿って説明する。

### 3. 後半で「理論や考え方」に触れる

理論は削らない。ただし、入口ではなく、信頼を深めるための奥行きとして配置する。

後半で扱うべき内容は次の通り。

- Architecture Signature
- Claim Boundaries
- AIR
- Measurement Status
- Non-conclusions
- ArchSig and SFT
- From Review to Forecast

ここで初めて、ArchSig が AAT / SFT とどう接続するのかを丁寧に説明する。

### 4. 末尾に Reference を置く

コマンドリストやスキーマは、読者が必要なときに引けるように末尾へ置く。

- Commands
- Schemas
- Artifact Formats
- Configuration Reference

Reference は、読み物ではなく索引である。

---

## 推奨サイト構成

### Start Here

初めて来た読者を、最初の成功体験まで連れていく領域。

- What is ArchSig?
- Quick Start
- First Scan
- First PR Review

### Use ArchSig

日常利用のための実践領域。

- Inputs
- Workflows
- Artifacts
- Operational Feedback

### Read ArchSig

出力を読むための領域。

- Reading Output
- Examples
- Report Anatomy
- PR Comment Anatomy

### Trust Boundaries

ArchSig の信頼性を説明する領域。

- Claim Boundaries
- Measurement Status
- Non-conclusions
- Runtime and Semantic Evidence

### Theory Behind ArchSig

ArchSig の背後にある理論を説明する領域。

- Architecture Signature
- AIR
- SFT Connection
- From Observation to Review
- From Review to Forecast

### Reference

詳細仕様を引くための領域。

- Commands
- Schemas
- Artifact Formats
- Configuration Reference

---

## トップページ改善方針

トップページは、単なる Manual Overview ではなく、製品の入口ページにする。

### 推奨構成

```md
# ArchSig

Architecture review, measured without overclaiming.

ArchSig scans repository structure and review evidence, then produces bounded architecture signatures, diffs, AIR, feature reports, and PR comments.

## What you can do with ArchSig

- Review architectural change, not just code diff
- Trace every signal to bounded structural, semantic, or operational evidence
- Bring software evolution theory into everyday PR review

## 5-minute path

1. Run your first scan
2. Validate the generated signature
3. Read measured / unmeasured axes
4. Generate a feature report
5. Use the result in PR review

## Choose your path

- New to ArchSig → Quick Start
- Reviewing a PR → First PR Review
- Reading JSON output → Reading Output
- Setting up CI → Workflows
- Understanding claim boundaries → Boundaries
- Looking for commands → Commands
```

---

## 追加したいページ

### `/archsig/anatomy/`

ArchSig の中核思想を、一枚で理解させるページ。

タイトル案:

> The Anatomy of an Architecture Signal

このページでは、ArchSig の出力を単なる JSON やスコアとしてではなく、**レビュー可能なアーキテクチャシグナル**として解剖する。

ArchSig のシグナルは、単に「危険そう」と言うものではない。信頼できるシグナルは、次の要素を持つ。

```text
Architecture Signal
├── What changed?
├── Why it matters?
├── What evidence supports it?
├── What should the reviewer inspect?
├── What is not proven?
└── What should be observed next?
```

この構成により、ArchSig の価値が直感的に伝わる。

- コード差分をアーキテクチャ変更として読む
- 変更の設計上の意味を説明する
- シグナルを証拠に結びつける
- レビュアーが見るべき観点を提示する
- 過剰主張せず、証明されていないことを明示する
- 次に観測すべき対象を示す

特に重要なのは、`What is not proven?` を弱みとしてではなく、信頼できるシグナルの構成要素として扱うこと。

ArchSig の思想は、次の一文に集約できる。

> A trustworthy architecture signal includes its own evidence boundary.

日本語では次の通り。

> 信頼できるアーキテクチャシグナルは、自分自身の証拠境界を含んでいる。

このページは、ArchSig website 全体の中核ページとして扱う。

推奨配置:

- トップページの `What you can do with ArchSig` 直後
- `Read ArchSig` セクションの最初
- `Why ArchSig?` からの主要リンク

このページを読むことで、読者は ArchSig が単なる linter、メトリクスツール、AI コメント生成ツールではないことを理解する。

ArchSig は、アーキテクチャレビューに必要な問いを、証拠境界つきのシグナルとして構造化するツールである。


### `/archsig/why/`

ArchSig の製品価値を説明するページ。

タイトル案:

> Why ArchSig?

扱う内容:

```md
Linters tell you whether code violates a rule.
Metrics dashboards show numbers.
Architecture review needs something else:

- what changed
- why it matters
- what evidence supports it
- what remains unknown
- what should be reviewed next

ArchSig is built for that gap.
```

### `/archsig/ci/`

CI 導入ページ。

ArchSig は PR レビュー支援として見せると強い。Workflows の中に埋めるのではなく、CI / PR review 導入ページとして独立させる。

扱う内容:

- before scan
- after scan
- signature diff
- AIR
- feature report
- PR comment
- review gate policy

### `/archsig/semantic-air/`

LLM による意味論的 AIR 生成を扱うページ。

扱う内容:

- LLM is a semantic observer, not a judge
- LLM-generated AIR as semantic observation
- semantic evidence boundary
- requires human confirmation
- example: business rule moved from Pricing to Coupon

---

## Before / After を前面に出す

ArchSig の魅力は、抽象説明よりも Before / After で伝わりやすい。

トップページまたは Why ArchSig? に、次のような例を置く。

### Before

```text
PRで CouponService が PaymentAdapter.internalCache を直接参照した。
人間レビューでは見落とすかもしれない。
```

### After

```text
ArchSig found a non-split coupon extension.

Reason:
- CouponService reaches PaymentAdapter.internalCache.
- The selected semantic diagram also shows rounding-order mismatch.

Suggested review action:
- Move cache access behind a PaymentPort contract.
- Add or confirm an explicit coupon/payment semantic contract.

Boundary:
- Runtime completeness was not established.
- This is a measured review witness, not a Lean theorem proof.
```

この例によって、ArchSig が「アーキテクチャレビューのための測定された証人」を出すツールであることが直感的に伝わる。

---

## 表現方針

### 避けたい表現

次の表現は思想としては正しいが、製品 PR としては弱く見える。

> 測れたことと測れていないことを分ける

これは、防御的に見える可能性がある。

### 推奨表現

外向きには、次のように言い換える。

- Make architecture review decisions with explicit evidence boundaries
- Trace every signal to bounded evidence
- Architectural judgment, backed by bounded evidence
- Evidence-backed architecture review
- Review signals with explicit scope and evidence

内部概念と外向き表現の対応:

| 内部概念 | 外向き表現 |
|---|---|
| measured / unmeasured / outOfScope / non-conclusion | bounded evidence |
| claim boundary | evidence boundary |
| metric status | signal status |
| blocked formal claim | review evidence, not theorem proof |
| AIR | architecture interpretation record |

---

## LLM / Semantic AIR の扱い

ArchSig が意味論を扱えるようになると、製品価値は大きく増す。

LLM にコードを読ませて、直接 AIR を作成させる運用が考えられる。

ただし、LLM は裁判官ではない。

ArchSig における LLM は、**意味論的観測器**である。

LLM の出力は、次のように扱う。

- semantic_observation
- semantic_hypothesis
- review_signal
- evidence_boundary
- requires_human_confirmation

これにより、ArchSig は AI レビューコメント生成ツールではなく、AI ネイティブな Architecture Evidence Layer になる。

### Semantic AIR の例

```text
AIR: CouponFeature introduces a semantic dependency on PaymentCalculation.

Observed behavior:
- Coupon discount is applied before tax calculation.
- PaymentAdapter previously assumed final amount was already normalized.
- New flow changes rounding order for discounted payments.

Architectural interpretation:
- CouponService is no longer a purely independent feature extension.
- It interacts with Payment semantics.
- Review should confirm whether rounding and tax rules belong to Coupon, Payment, or Pricing.

Evidence boundary:
- Static code paths were inspected.
- Runtime behavior was not executed.
- External payment provider behavior was not verified.
```

---

## 最終的なメッセージ

ArchSig website の改善では、次のメッセージを一貫して伝える。

> ArchSig は、AI ネイティブな Architecture Evidence Layer である。
>
> コード差分ではなく、アーキテクチャ変更をレビューする。
> すべてのシグナルを、構造・意味・運用の証拠に結びつける。
> 日々の PR レビューを、ソフトウェア進化の理論へ接続する。

これにより、ArchSig は単なる研究デモでも、静的解析ツールでも、AI コメント生成ツールでもなくなる。

ArchSig は、AI 駆動開発時代における、ソフトウェア進化の観測レイヤーとして位置づけられる。
