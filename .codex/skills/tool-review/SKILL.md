---
name: tool-review
description: ArchSig v0.6.0 / ArchView / FieldSig の実装および docs/tool の完了後差分を、独立 1 lane で敵対レビューし、編集せず合否を返す。"$tool-review"、review-prの最終ゲート、リリース前監査で使う。
---

# Tool Review

ArchSig v0.6.0・ArchView・FieldSig の実装と `docs/tool/` の差分を、実装セッションから独立した **1 lane（新規 subagent 1本）** で一貫して敵対レビューする。

## 必須規則

`.codex/skills/_shared/review-protocol.md` と
`.codex/skills/_shared/refutation-checklist.md` を全文読み、
非編集・独立査読（履歴なし `fork_turns: "none"`）・fail-closed・報告形式を適用する。
設計・品質・テストの基準は [Tool guideline](../../../docs/tool/guideline.md) を参照する。

## 査読体制（独立 1 lane）

- 実装セッションの履歴・期待結論を引き継がない新規 subagent を **1本** 起動し、差分・周辺コード・仕様書全体を通して一貫した視点で監査する。
- 1本の subagent 内で、以下の4つの確認軸を漏れなく反証的に検査する。
- 仕様書に未定義の境界や設計判断が必要な論点は、必須修正として実装と往復させず、設計判断事項（人間判断待ち）として切り出して報告する。

### 確認軸（1 lane 内で一貫検査）

1. **入力区分・由来分離・数学対応**（checklist §8・[Tool guideline「責務範囲」](../../../docs/tool/guideline.md#責務範囲入力トライアドの正本)）
   - 入力が Atom 定義・Law・ArchMap・問いの4区分に中身で帰属しているか。結論相当データの外部注入や、読解候補・観測・計算結果・数学的証明の混同がないかを疑う。
   - ArchView / FieldSig が AAT 構造解析の判定・結論を独自生成せず、ArchSig の計算結果を用いているかを確認する。
   - 論文・SHIGURE GOAL・Lean 定理の有限特殊化を含む場合、対応する定理参照、適用条件の実行時検査、条件外入力の沈黙（未対応理由）、実コード復元と再観測の境界が揃っているかを確認する。

2. **仕様整合・導出の実体性**（checklist §5・`docs/tool/archsig_v0_6_0_io/`）
   - 実装・同梱 SKILL・[ArchSig v0.6.0 I/O 仕様](../../../docs/tool/archsig_v0_6_0_io/README.md)・クレート README の記述と実動作が一致しているか。
   - 計算結果（値・成立・反証・反例・障害・修復解・必要観測・未決理由）がダミーや proxy ではなく計算核から実際に導出され、根拠と元位置を追跡できるかを追う。
   - 仕様上の名前を名乗る fixture や golden 期待値の出自を仕様と突合する。

3. **設計構造・複雑度・性能**（[Rust 品質規約](../../../docs/tool/guideline.md#rust-品質規約)・[簡素化と引き算](../../../docs/tool/guideline.md#簡素化と引き算)）
   - 直交する軸（型 × 演算 × 問い × 局所/大域 × 欠測等）を特例分岐やファイル複製で横並び増築していないか、肥大化停止線（1,000行超ファイルへの無条件追記、既存 `observed/` への無制限な継ぎ足し）に抵触していないかを疑う。
   - 変更関数だけで判断せず、呼出し元・下流・既存の類似実装を読み、同一リクエスト内の重複検証・重複生成・不要なコピー・全件走査・過大な寿命やメモリ保持がないかを追う。
   - 欠落入力の `unwrap_or_default` や重複入力の黙殺、`panic!` / `unwrap`、不正な path / 出力先処理がないか、代表題材での実測なしにキャッシュ・予算制御・パッケージング等を先回り実装していないかを疑う。
   - 公開物・fixture・出力にローカルパス・個人名・内部情報が露出していないか確認する（checklist §6）。

4. **テストの妥当性・実測確認**（[テストの書き方](../../../docs/tool/guideline.md#テストの書き方)）
   - テストは名前ではなく assertion 内容で証拠にする。仕様の組合せごとに巨大な統合／CLI テストファイルを複製せず、代数的不変条件・負系・境界条件を最も狭い層（単体・パラメトリック・property-based・代表 E2E）で検証しているか確認する。
   - CI 3分要件を圧迫する過剰テストがないか、計算核の大きな変更や性能関連変更で代表規模ベンチマーク（実行時間・最大 RSS）の実測比較が揃っているかを確認する。

## 検証

- [Tool guideline「テスト責務と実行経路」](../../../docs/tool/guideline.md#テスト責務と実行経路)に従って変更ワークスペースのテストを確認する。
- checklist §6 の横断機械 scan（`git diff --check`、hidden/bidi、privacy、語彙ルール）を実行する。
- 実行できない検証は理由と残リスクとして報告する。

## 親の統合判定

[レビューでの扱い](../../../docs/tool/guideline.md#レビューでの扱い)に従い、指摘を簡潔に示す。
共有ルールの統合出力に従い、判定を
`Needs changes` / `No major findings` / `Blocked / cannot determine` で返す。
仕様未定義の設計判断事項は判定を空転させず、人間判断事項として明記する。
