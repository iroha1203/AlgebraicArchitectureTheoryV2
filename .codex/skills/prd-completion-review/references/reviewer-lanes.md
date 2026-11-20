# PRD Completion Review lanes

対象 PRD の種別に応じて規定本数の重複独立査読を実行する。
A / B を主査と補助に分けず、各 lane が PRD 全文から条件を独立抽出し、累積実体を確認する。
親の条件リスト、会話履歴、期待結論、他 lane の出力、前の監査結果を渡さない。
新規起動と履歴を渡さない方法は共有 review protocol の「Subagent 入力」に従う。

## Lane 構成の選択

- **ツール専用 PRD**（`tools/`・`docs/tool/` を主対象とし、Lean / 数学要件を含まないもの）:
  **独立 2 lane（ツール完了査読 A / B）**。同一の観点・合格基準で 2 本独立に走らせ、査読の揺らぎを吸収する。
- **Lean / 数学要件を含む PRD、およびその他分野の PRD**:
  **独立 4 lane（要件査読 A/B、実装・検証査読 A/B）**。

## Lane 定義

### ツール専用 PRD: ツール完了査読 A / B（2 本・同一基準）

2 本とも次の全観点を同じ基準で独立に確認する。

- PRD の問い、全達成条件、拘束条件、requirement matrix、must-not-remain を全文から独立抽出する。
  抽出の範囲と除外規則は [標準手順 2](../SKILL.md#標準手順) に従う。
- 全条件をコード、仕様書（`docs/tool/archsig_v0_6_0_io/` 等）、fixture、test、同梱 SKILL、必要な GitHub 状態へ一次証拠で追い、部分実装・記載のみの充足・欠落・旧構造の残存を探す。AC とは別に問いへの回答を判定する。
- [Tool guideline](../../../../docs/tool/guideline.md) に照らし、入力区分・由来分離・数学対応（適用条件検査と範囲外の沈黙）、設計の直交性と肥大化、assertion 内容・負系・代表規模ベンチマーク（実行時間・最大 RSS の実測）の妥当性を確認する。

### 標準（Lean / 数学要件を含む PRD 等）: 要件査読 A / B・実装・検証査読 A / B（4 本）

#### 要件査読 A / B

- PRD の問い、全達成条件、拘束条件、requirement matrix、must-not-remain を全文から抽出する。
  抽出の範囲と除外規則は [標準手順 2](../SKILL.md#標準手順) に従う。
- 各条件と一次証拠の強さ・範囲を照合し、部分実装、許可外の降格、記載のみの充足、
  欠落した条件群、PRD 外の要求混入を探す。AC とは別に問いの回答を判定する。

#### 実装・検証査読 A / B

- 要件査読と同じ抽出を独立に行い、全条件をコード、宣言、schema、fixture、test、docs、
  必要な GitHub 状態へ追う。名前や台帳の status だけで充足扱いしない。
- assertion 内容、負系、未接続 surface、旧構造・旧挙動の残存、検証の再現性を確認する。
  Lean 要件では statement、依存、仮定放電、axiom 等の該当する反証項目も適用する。

## 全 lane 共通の合格基準

各 lane は要件充足、欠落・反例、検証再現性、scope・状態整合の全観点を確認する。
theoremRef の実在と主張方向、public artifact の privacy も対象とする。
条件群の深掘りは同じ lane 内で順次行う。抽出専用・深掘りの追加 lane は起動しない。
全数を実読できない条件群は sampling で充足扱いせず、条件 ID と理由を付けて未確認とする。

## Lane 入力

- 固定した PRD パス・内容 hash と全文、対象 commit。作業ツリー差分を含む場合は対象の内容 hash。
- lane 名と反証目的、適用 guideline と必要な reference。
- 累積実体への参照、実行済みの検証コマンド・結果と対象 snapshot。
- tracking Issue / PR 番号は証拠検索の索引としてのみ渡す。
- 一次証拠規則。台帳、Issue、PR 本文、tracking checklist は監査対象とする。

## 追加出力

共有 review protocol の出力に加え、各 lane は次を返す。

1. 独立抽出した全条件・拘束条件・requirement matrix・must-not-remain と除外理由。
   PRD に ID がなければ、節・原文引用で親が対応を照合できる形にする。
2. 条件ごとの推奨 status:
   `満たした` / `未達` / `未確認` / `PRD欠陥` / `範囲外`。
3. 一次証拠。test を使う場合は assertion 内容を含める。
4. 問いに対するアウトカム判定。
5. 確認した条件と未確認の条件・実体・検証、その理由。

## 親の報告

1. 総合判定:
   `達成済み` / `未達あり` / `未確認あり` / `PRD欠陥あり` /
   `範囲限定レビュー`。
2. PRD の「問い」に対するアウトカム判定。
3. Scoreboard。
4. 条件別レビュー表。独立抽出の差分と解消根拠を含む。
5. Findings。
6. Lane 別の反証試行・判定と、親による一次証拠の再判定。
7. 実行した検証、対象 commit・PRD 内容 hash・必要な実体 hash。
8. Coverage limits。
9. 次アクション案。実装は行わない。

`達成済み` には規定全 lane（ツール専用 PRD は 2 本、その他は 4 本）すべてと親の全必須項目の確認を要求する。
未完了 lane、未解消 finding、抽出の不一致、必要な coverage の不足が残る場合は完了にしない。

`prd-loop` の最終レビュー、または tracking Issue がある単独レビューでは、
1〜8 を tracking Issue へコメントする。投稿不能でも一次証拠に基づく判定は返し、
`tracking Issue未同期` として報告する。`prd-loop` 側の close 操作は同期まで停止する。
