---
name: research-loop
description: 探索型 research GOAL で、候補探索・Lean 検証・ライバル比較・SCORE 監査・PR 化を反復する。"$research-loop goal-id"、"探索研究ループ"、"研究ループを回して" の依頼で使う。
---

# Research Loop

この skill は、研究 GOAL に向けて候補を探索し、価値の高いものを Lean で検証し、研究貢献 SCORE を積み上げる探索型ループである。応答、Issue、PR は日本語で行う。

`research mode: target-theorem` の GOAL は `$target-theorem-loop <goal-id>` の対象である。GOAL カードで大定理証明モードを検出したら、そちらを案内する。

## 入口

起動は `$research-loop <goal-id>` とする。`goal-id` は [research/GOALS.md](../../../research/GOALS.md) の active な score-phase GOAL を指す。任意で `threshold <N>`、`score-threshold <N>`、`max-cycles <N>`、対象カテゴリ、探索寄りの指示を渡してよい。

最初に次を読む。

- [research/README.md](../../../research/README.md)
- [research/GOALS.md](../../../research/GOALS.md)
- [research/ideas/TEMPLATE.md](../../../research/ideas/TEMPLATE.md)
- [research/reports/README.md](../../../research/reports/README.md)
- [research/DESIGN.md](../../../research/DESIGN.md)

参照ファイル:

- G0 の GOAL card 検査: [references/goal-card-contract.md](references/goal-card-contract.md)
- genius / 1000 点判定: [references/genius-scoring.md](references/genius-scoring.md)
- 候補カード作成 / 同期: [references/candidate-card-contract.md](references/candidate-card-contract.md)
- tracking Issue コメント: [references/ledger-templates.md](references/ledger-templates.md)
- subagent 起動: [references/subagent-prompts.md](references/subagent-prompts.md)

`research/GOALS.md` は不変入力として扱う。GOAL 本文、status、threshold policy、rubric、frontier、spine をループ中に編集しない。active threshold、current SCORE、cycle 履歴、phase summary は GitHub tracking Issue の runtime state として扱う。

## SCORE の原則

SCORE は研究能力の増分に対して与える。証明数、ファイル数、定理数には与えない。

- `0`: 定義展開、既存結果の言い換え、GOAL の能力を増やさない局所補題。
- `10-20`: 小さいが必要な補助結果。単独では GOAL の景色を変えない。
- `30-40`: 新しい測定量、構成、比較、計算手段を与える。
- `50-70`: 複数の品質概念、obstruction、cohomology、metric、lawfulness を一つの枠で説明する。
- `80-100`: 反例、obstruction、新しい不変量、主定理候補により GOAL の見方や到達像を変える。
- `1000`: 大定理レベルの希少な `genius` 候補。詳細条件は [references/genius-scoring.md](references/genius-scoring.md) を読む。

証拠 multiplier は `x1.0` 手計算、`x1.2` 有限例、`x1.5` Lean statement / conjecture、`x2.0` sorry なし Lean proof + axiom audit + 形式化品質監査 clean とする。強い問いの不自然な弱化、SCORE 稼ぎの分割、rival 比較不足、claim boundary 越えには減点を入れる。

## サイクル

```text
G0 状態確認
G1 探索と候補生成
G2 価値スコア審判
G3 Lean 検証または証拠固定
G3.5 候補カード同期
G4 SCORE 確定とレポート
G5 PR レビューとマージ
G6 研究フェーズ区切り判定
```

ひとサイクルで PR に入れる主成果は原則ひとつにする。一つの貢献を構成する補題群はまとめてよい。研究主張の revise は一巡だけにする。Lean の機械的修正、候補カード同期、PR メタデータ修正は二巡まで許す。

### G0 状態確認

1. `git status --short --branch` と `git ls-files --others --exclude-standard` を確認する。ユーザーの未コミット変更は戻さない。
2. `main` を最新化する。
3. GOAL card を読む。GOAL が active でなければ Issue を作らず止まる。`research mode: target-theorem` なら Issue を作らず `$target-theorem-loop <goal-id>` へ誘導する。省略または `score-phase` の場合だけ続ける。
4. tracking Issue `Research Loop: <goal-id>` を探し、なければ作る。
5. 起動引数または tracking Issue から active threshold を読む。見つからなければ `threshold missing` として止まる。
6. tracking Issue から current SCORE、カテゴリ別 SCORE、直近 cycle、停止条件、open な `genius target theorem` があればその state を読む。
7. G0 state を短い入力メモにして G1、G2、G3.5、G4、G6 の該当 subagent に渡す。

GOAL card の必須項目や欠陥判定は [references/goal-card-contract.md](references/goal-card-contract.md) を正とする。

### G1 探索と候補生成

候補生成では、spine を埋めるものだけでなく、GOAL の見方を変えるものを探す。毎サイクル、独立した候補生成サブエージェントを四体走らせ、最低四案の候補 pool を作る。四体には互いの出力を渡さず、`closer`、`obstruction`、`unifier`、`wildcard` を一つずつ割り当てる。

良い候補は次を満たす。

- 定義展開や即時系ではなく、新しい構成、比較、不変量、反例、obstruction、統一定式化のいずれかを含む。
- GOAL のどの能力カテゴリがどう増えるかを一文で言える。
- GOAL の `rival` に対して、どの能力で有効な差分を作るかを一文で言える。
- 驚き、圧縮、射程、反例性、計算可能性、古典理論や CS / SWE への橋のうち少なくとも一つを持つ。
- 証明または証拠の道筋があり、claim boundary を守る。

候補種別は `closure`、`orientation`、`unification`、`computability`、`bridge`、`genius`、`genius-target`、`genius-support` とする。候補カードは `research/ideas/` に置き、詳細は [references/candidate-card-contract.md](references/candidate-card-contract.md) に従う。

### G2 価値スコア審判

四人の独立サブエージェントに審判させる。渡すのは GOAL、候補カード、GOAL の `rival`、関連する既存結果、reward rubric、dullness filter、必要な repo overview だけにする。本体の期待や途中判断は渡さない。

- 審判 A: 厳密性、claim boundary、既存結果の即時系でないこと、Lean 予定 statement の弱化や結論相当前提逃がしがないこと。
- 審判 B: GOAL への研究価値、surprise、compression、leverage。
- 審判 C: AAT / SFT / Tooling / Website / Research 全体に照らした価値。
- 審判 D: GOAL の `rival` に対する新規性、有効性、統合力、分離力。

四者が `accept` した候補のうち最も強いものを picked にする。`revise` は一度だけ直して再審判する。`reject` は `status: archived` とし、理由を残す。`genius` 基本点を採るには、[references/genius-scoring.md](references/genius-scoring.md) の条件を満たし、四者全員が `genius_eligibility: yes` を返し、G4 が confirm する必要がある。

### G3 Lean 検証または証拠固定

定理候補は `Formal/AG/Research/<slug>.lean` に形式化する。`Formal/AG` 本体は参照または import のみ可とし、このループでは直接編集しない。import 方向は **Research → 本体のみ**であり、本体側(`Formal/AG` 本線・`Formal.lean` 配線)へ `Formal.AG.Research` の import を持ち込むことは、このループでも蒸留移植でも常に禁止する(疎結合不変条件。破ると math-lean-review の境界侵犯検査で hard fail)。

合格条件:

1. `lake build FormalAGResearch` が通る。
2. 独立サブエージェントの公理検査が通る。
3. 独立サブエージェントの Lean 形式化品質監査を通る。判定正本は
   `docs/aat/lean_quality_standard.md`(受理点への適用。同 §6)。
   `True` で充足可能なフィールド、退化 witness(PUnit / 自明群 / singleton)、
   instance の無い仮定パッケージ、結論相当前提の field 逃がしは
   その代表例である。
4. **固定 statement 突合**: 候補カードの `planned_lean_statement` と実装
   declaration の signature が一致する(判定形式は同 §5.2)。premise の
   追加・結論の弱化・対象の縮小があれば G3 合格を出さず、実装を直すか
   候補カードを改訂して **G2 再審判へ戻す**。乖離した statement のまま
   G4 / G5 へ進む経路を残さない。

ローカルでは対象範囲に応じて次を実行または同等に確認する。

```bash
lake env lean Formal/AG/Research/<file>.lean
lake build FormalAGResearch
#print axioms <declaration>
rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal/AG/Research
rg -nP "[\\x{200B}-\\x{200F}\\x{202A}-\\x{202E}\\x{2066}-\\x{2069}]" <changed-files>
rg -n "$HOME|${TMPDIR%/}" <changed-files>
```

反例、orientation result、計算例は Lean proof だけを要求しないが、最小反例、計算手順、対象 family、仮定、既存理論との対応を証拠 artifact に固定する。

足場衛生を保つ。受理ルートが名前参照するスパイン宣言と、サイクル足場(premise 順列帯、再入口変種、checkpoint 帯)を、ファイル分割または命名で区別できる状態に保ち、足場の量産を避ける。研究 evidence は将来の蒸留移植(正典化)の入力になるため、スパインが行範囲でも時系列でも切り出せない状態を作らない。

### G3.5 候補カード同期

G4 へ進む前に、候補カード、証拠、Lean declaration、審判メモを同期する。候補カードは生成時の期待値ではなく、実際に固定された証拠の index として読める状態にする。同期すべき最低項目は [references/candidate-card-contract.md](references/candidate-card-contract.md) を正とする。

### G4 SCORE 確定とレポート

検証と G3.5 同期後、独立サブエージェントに SCORE 監査を行わせる。渡すのは GOAL、GOAL の `rival`、同期済み候補カード、証拠、G2 の四審判結果、G3 の監査結果、diff だけにする。

`confirm` または `reduce` の場合だけ `research/reports/<goal-id>.md` に書く。レポート、カテゴリ別 SCORE、total SCORE、proof portfolio、cycle section、Next Frontier / phase boundary メモは G4 監査後の値で同時に更新する。`seed-only` は `genius-target` seed 専用で、total SCORE に加算しない。

### G5 PR レビューとマージ

ひとつの picked の成果をひとつの PR にまとめる。PR には候補カード、Lean ファイルまたは証拠、レポート、tracking Issue の SCORE 更新を含める。**Lean 検証済み(G3 で `lean-verified`)の theorem を受理する PR では、`docs/aat/research_evidence_index.md` への1行登録(theorem 名、ファイル、本文ラベル、conjuncts 要旨、未放電仮定、受理点、移植状況 `unported`)を出力義務とする**(Research 下限原則の検索基盤。scaffolding・探索残骸は `not-for-porting` として登録するか、スパイン宣言でないものは登録対象外としてよい)。tracking Issue は研究状態の正本であり、PR 本文では原則 `Refs #<tracking-issue>` を使う。

PR 前に `git diff --check`、`git diff --cached --check`、未追跡ファイル、不可視 Unicode、ローカル絶対パス、保護対象 docs の編集有無を確認する。PR レビューは `$review-pr <PR番号>` を実行する。マージは `$review-pr` が mergeable で、CI または必要なローカル検証が通った場合だけ行う。

### G6 研究フェーズ区切り判定

PR マージ後、tracking Issue に iteration コメントを残し、独立サブエージェントに研究フェーズ区切り判定を行わせる。渡すのは GOAL、active threshold、SCORE 台帳、レポート、カテゴリ別 SCORE、証拠段階、phase boundary criteria だけにする。

total SCORE が active threshold に到達または超過したら、必ず G6 の `phase-boundary-candidate` として扱う。ただし score-phase の GOAL は「完全達成」を判定する対象ではない。判定するのは、この時点でひとつの研究フェーズとして区切るだけの成果とまとまりがあるかである。フェーズ区切りなら Issue は閉じず、phase summary コメントを残して止まる。区切りでなければ、threshold 到達後でも理由を明記して同じ GOAL で次サイクルへ戻る。

## 停止条件

- `low-value stagnation`: 二サイクル続けて期待 final SCORE が 30 未満の候補しか出ない。
- `proof stagnation`: 高 SCORE 候補はあるが、二サイクル続けて証拠固定に失敗する。
- `review stagnation`: 同じ PR が二巡してもマージ可能にならない。
- `score dispute`: 独立審判間で SCORE が大きく割れ、根拠を読んでも解消できない。
- `score-threshold reached`: total SCORE が active threshold に到達または超過した。G6 で phase boundary として止めるか、明示理由つきで継続するかを判定する。
- `threshold missing`: tracking Issue に active threshold がなく、起動引数でも threshold が指定されていない。
- `phase boundary`: active threshold、portfolio constraint、phase boundary criteria を満たし、研究としてキリが良い。
- `exhausted`, `max-cycles`, `goal defect`, `all blocked`, `undecidable`。

## サブエージェント規律

候補生成、G2 審判 A/B/C/D、G3 公理検査、G3 Lean 形式化品質監査、G4 SCORE 監査、G6 フェーズ区切り判定は、独立したサブエージェントに行わせる。G5 PR レビューは `$review-pr` に渡す。サブエージェントを使えない環境では止まり、人間のレビューに委ねる。標準プロンプトは [references/subagent-prompts.md](references/subagent-prompts.md) を使う。

## 安全規則

- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、docs/note は編集しない。
- `research/GOALS.md` は research-loop 中に編集しない。改訂が必要なら tracking Issue または別 Issue に提案する。
- AAT の内側に source observation、measurement tooling、ArchMap validation の完全性 claim を持ち込まない。
- Lean の依存は `Formal/AG/Research` から `Formal/AG` への一方向に保つ。
- `axiom`、予想以外の `sorry`、`unsafe` を相談なく持ち込まない。
- tracking Issue は明示的な人間指示なしに `Closes` で閉じない。
- 破壊的な git 操作は使わない。一時出力は `.tmp/` または `/private/tmp` に置く。

## 報告

終えるときは、日本語で停止条件または継続状態、picked 候補、証拠段階、確定 SCORE、PR とマージ結果、GOAL に対する delta、次に狙うべき frontier を短く報告する。
