---
name: target-theorem-loop
description: "research/GOALS.md の `research mode: target-theorem` GOAL に対して、大定理の証明へ向けて support node、premise discharge、obstruction/refutation、Lean theorem package を積み上げる専用ループ。完了判定では `$math-lean-review` の4並列査読を必須 gate にする。Use when the user says \"$target-theorem-loop <goal-id>\", \"大定理証明ループ\", \"target theorem loop\", or asks Codex to prove a GOALS.md target theorem to completion."
---

# Target Theorem Loop

この skill は、`research/GOALS.md` の `research mode: target-theorem` GOAL だけを扱う大定理証明ループである。探索型 SCORE phase は `$research-loop` の責務であり、この skill では実行しない。

目的は、GOAL カードに定義された target theorem を弱めず、support theorem、premise discharge、obstruction/refutation、Lean theorem package、candidate card、report、tracking Issue ledger を積み上げることである。SCORE は補助台帳であり、完了条件ではない。

大定理の完了判定では、必ず `$math-lean-review research/GOALS.md <goal-id>` を実行し、その正式判定を T6 completion ledger に取り込む。`$math-lean-review` が実行不能、4 並列査読不能、coverage 不足、または verdict が `No major findings` 以外の場合、`target-theorem-proved` を出してはならない。結果は `target-proof-checkpoint`、`target-blocked`、または `target-refuted` に倒す。

## 入口

起動は `$target-theorem-loop <goal-id>` とする。`goal-id` は [research/GOALS.md](../../../research/GOALS.md) の active な `research mode: target-theorem` GOAL を指す。任意で `max-cycles <N>`、特定 support node、特定 blocker、証明寄り / 反例寄りの指示を渡してよい。

最初に次を読む。

- [research/README.md](../../../research/README.md)
- [research/GOALS.md](../../../research/GOALS.md)
- [research/ideas/TEMPLATE.md](../../../research/ideas/TEMPLATE.md)
- [research/reports/README.md](../../../research/reports/README.md)
- [research/DESIGN.md](../../../research/DESIGN.md)
- [../math-lean-review/SKILL.md](../math-lean-review/SKILL.md)

必要なときだけ読む。

- T0 の target GOAL card 検査: [references/target-goal-contract.md](references/target-goal-contract.md)
- 候補カード作成 / 同期: [references/target-candidate-card-contract.md](references/target-candidate-card-contract.md)
- tracking Issue コメント: [references/target-ledger-templates.md](references/target-ledger-templates.md)
- subagent 起動: [references/target-subagent-prompts.md](references/target-subagent-prompts.md)

`research/GOALS.md` は target theorem の正本として扱い、ループ中に編集しない。target statement、boundary、completion criteria、premise discharge policy、material premise ledger、anti-weakening rule、failure policy を弱める必要がある場合は、tracking Issue または別 Issue に GOAL 改訂提案を残して止まる。

## Target Proof Contract

target theorem の完了条件は GOAL カードの `target theorem completion criteria` と `target proof artifacts` で決まる。SCORE threshold、候補カードの `proved` 表現、PR merge、CI green、Lean file が build することは必要な証拠ではあっても完了条件ではない。

大定理証明候補は次のいずれかに分類する。

- `target-support`: support map の node を進める補題、構成、有限 witness、normalization、bridge。
- `target-obstruction`: target theorem の仮説不足、反例、必要条件、proof blocker を固定する結果。
- `target-refinement`: target theorem を弱めず、型、仮定、support map、claim boundary を鋭くする整理。GOAL card 改訂が必要なら提案で止める。
- `target-proof`: target theorem 本体または theorem package を証明する候補。

`target-proof` 候補でも、material premise が theorem argument、typeclass、structure field、certificate field、opaque membership に残る場合は、completion ではなく checkpoint とする。ambient boundary として残せるのは、対象 site、finite vocabulary、cover、coefficient object、supplied observation contract などの入力幾何だけである。

## SCORE の扱い

SCORE は support progress の研究価値を測る補助台帳として使ってよい。target theorem が未証明なら SCORE threshold 到達だけでは止まらない。`target-support` や `target-obstruction` は通常の `0-100` 基本点で採点する。target theorem 自体が `genius` 級でも、`target-theorem` は制御ループであり、`genius` 評価とは分けて扱う。

## サイクル

```text
T0 状態確認
T1 proof-support 候補生成
T2 target proof 価値・厳密性審判
T3 Lean 検証または証拠固定
T3.5 候補カード同期
T4 SCORE / target progress 監査
T5 PR レビューとマージ
T6 target completion 判定
```

ひとサイクルで PR に入れる主成果は原則ひとつにする。ただし一つの proof node を構成する補題群はまとめてよい。target statement を弱めて成功扱いしない。

### T0 状態確認

1. `git status --short --branch` と `git ls-files --others --exclude-standard` を確認する。ユーザーの未コミット変更は戻さない。
2. `main` を最新化する。
3. GOAL card が active かつ `research mode: target-theorem` か確認する。GOAL が active でなければ Issue を作らず止まる。mode が違う場合も Issue を作らず `$research-loop <goal-id>` へ誘導して止まる。
4. tracking Issue `Research Loop: <goal-id>` を探し、なければ作る。
5. GOAL card から target theorem、boundary、proof artifacts、proof strategy、completion criteria、premise discharge policy、material premise ledger、anti-weakening rule、failure policy を抽出する。
6. tracking Issue から proof state、完了 support node、未完 support node、blocker、PR、直近 proof attempt、補助 SCORE を読む。
7. T0 state を短い入力メモにして各 gate の subagent に渡す。

target GOAL card の必須項目と欠陥判定は [references/target-goal-contract.md](references/target-goal-contract.md) を正とする。

### T1 proof-support 候補生成

候補生成は広い探索ではなく、target theorem の proof distance を縮める候補に絞る。毎サイクル、独立した候補生成 subagent を四体走らせ、次の役割を割り当てる。

- `premise-discharge`: material premise ledger の未放電行を theorem / finite witness / concrete certificate で消す。
- `statement-audit`: Lean statement、target boundary、anti-weakening rule の弱化や結論相当前提逃がしを探す。
- `proof-dag`: support map、依存補題、normalization、bridge、proof DAG の未接続 node を進める。
- `obstruction`: 反例、必要条件、target-refuted / target-blocked につながる proof blocker を探す。

候補 pool は重複を除いて最低四案を目標にする。target theorem を弱める候補は picked にしない。target が反例で壊れそうな場合は `target-obstruction` として明示する。

### T2 target proof 価値・厳密性審判

四人の独立 subagent に審判させる。渡すのは GOAL target、候補カード、tracking Issue proof state、material premise ledger、anti-weakening rule、関連 Lean / docs だけにし、本体の期待は渡さない。

- 審判 A: 数学的厳密性と claim boundary。
- 審判 B: target proof distance の短縮度。
- 審判 C: material premise と anti-weakening。
- 審判 D: project / rival delta と将来の paper / docs / Lean 価値。

審判 A が reject した候補は進めない。material premise を隠す候補、新規 material premise を ledger なしに導入する候補、target statement を弱める候補は `target-proof` ではなく `target-refinement` / `target-obstruction` / checkpoint に戻す。

### T3 Lean 検証または証拠固定

Lean 証拠は `Formal/AG/Research/<goal-area>/...` に置く。`Formal/AG` 本体は参照または import のみ可とし、このループでは直接編集しない。

合格条件:

1. focused `lake env lean <target-file>` が通る。
2. `lake build FormalAGResearch` が通る。
3. 報告対象 declaration すべての `#print axioms` audit が通る。
4. placeholder scan が clean。
5. Lean statement と target claim の対応、material premise、anti-weakening を独立監査する。

ローカルでは対象範囲に応じて次を実行または同等に確認する。

```bash
lake env lean <target-file>
lake build FormalAGResearch
#print axioms <declaration>
rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal/AG/Research
rg -nP "[\\x{200B}-\\x{200F}\\x{202A}-\\x{202E}\\x{2066}-\\x{2069}]" <changed-files>
rg -n "$HOME|${TMPDIR%/}" <changed-files>
```

### T3.5 候補カード同期

候補カード、Lean declaration、report、tracking Issue proof state、premise discharge status、G2/T3 監査結果を同期する。候補カードは期待値ではなく、実際に固定された proof artifact の index として読める状態にする。詳細は [references/target-candidate-card-contract.md](references/target-candidate-card-contract.md) に従う。

### T4 SCORE / target progress 監査

独立 subagent に SCORE と target progress を監査させる。SCORE は補助値として確定してよいが、`target_progress: target-proved` は T6 と `$math-lean-review` を通るまで確定しない。

T4 は必ず次を返す。

- candidate type と target support node。
- proof obligation delta。
- material premises と premise discharge status。
- new material premise の有無。
- anti-weakening verdict。
- target_progress: `support-node` / `blocker-found` / `target-refined` / `target-proof-candidate` / `target-proof-checkpoint-candidate` / `target-refuted`。

`target-proof` が completion criteria を満たす可能性がある場合でも、未放電 premise や statement 弱化があれば `target-proof-checkpoint-candidate` として T6 へ渡す。

### T5 PR レビューとマージ

PR には候補カード、Lean ファイルまたは証拠、report、tracking Issue の proof progress / SCORE update を含める。PR 本文は原則 `Refs #<tracking-issue>` を使い、人間の明示指示なしに tracking Issue を close しない。

PR 前に `git diff --check`、`git diff --cached --check`、未追跡ファイル、不可視 Unicode、ローカル絶対パス、保護対象 docs の編集有無を確認する。PR レビューは `$review-pr <PR番号>` を独立 subagent で実行する。マージは独立レビューが mergeable で、CI または必要なローカル検証が通った場合だけ行う。

### T6 target completion 判定

T6 は必ず先に `$math-lean-review research/GOALS.md <goal-id>` を実行する。入力には GOAL claim、candidate Lean declarations、proof artifacts、tracking Issue proof state、T3/T3.5/T4/T5 の evidence を渡す。`$math-lean-review` の 4 並列査読が正式に走らなければ完了判定はできない。

`target-theorem-proved` を出せるのは次をすべて満たす場合だけである。

- GOAL card の target theorem completion criteria が満たされている。
- target proof artifacts が存在し、Lean build、axiom audit、placeholder scan が clean。
- material premise ledger の `discharge-required` 行が theorem / finite witness / concrete certificate で discharge 済み。
- Lean statement が自然言語 target を弱めていない。
- dependency proof DAG、definition unfolding、nonvacuity、direction coverage、artifact sync が確認済み。
- T4 と T5 に blocking finding がない。
- `$math-lean-review` の verdict が `No major findings` で、coverage に中心 claim の未確認・弱化・未放電・台帳不一致が残っていない。

どれか一つでも満たせない場合、`target-theorem-proved` を出さない。`$math-lean-review` が `Reject / 証明として不十分`、`Major revisions`、`Minor issues`、`Blocked / cannot determine`、または coverage 不足なら `target-proof-checkpoint` に落とす。target statement が反例で壊れた場合は `target-refuted`、support map が二サイクル続けて進まない場合は `target-blocked` とする。

## 停止条件

- `target-theorem-proved`: GOAL の completion criteria を満たし、`$math-lean-review` が `No major findings`。
- `target-proof-checkpoint`: proof package や support map のまとまりはあるが、未放電 premise、弱化、coverage gap、math-lean-review 不合格が残る。
- `target-refuted`: 現 target statement に反例または必要仮定不足が固定された。
- `target-blocked`: 未完 support node または proof blocker が二サイクル続けて解消しない。
- `goal defect`: target GOAL card の必須項目や anti-weakening / material premise ledger に欠陥がある。
- `proof stagnation`, `review stagnation`, `max-cycles`, `all blocked`, `undecidable`。

## サブエージェント規律

T1 候補生成、T2 審判、T3 公理検査、T3 Lean 形式化品質監査、T4 監査、T5 PR レビュー、T6 `$math-lean-review` は独立文脈で行う。subagent を使えない環境では、T6 で `target-theorem-proved` を出してはならない。標準プロンプトは [references/target-subagent-prompts.md](references/target-subagent-prompts.md) を使う。

## 安全規則

- `research/GOALS.md` は編集しない。target 改訂は提案に留める。
- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、docs/note は編集しない。
- AAT の target theorem に ArchMap extraction completeness、runtime measurement completeness、whole-codebase quality を混ぜない。GOAL が明示する claim boundary だけを判定する。
- Lean の依存は `Formal/AG/Research` から `Formal/AG` への一方向に保つ。
- `axiom`、予想以外の `sorry`、`unsafe` を相談なく持ち込まない。
- tracking Issue は人間の明示指示なしに close しない。
- 破壊的 git 操作は使わない。一時出力は `.tmp/` または `/private/tmp` に置く。

## 報告

終えるときは、日本語で停止条件、target proof state、完了 support node、未完 support node、premise discharge status、`$math-lean-review` verdict、PR / merge 結果、次の proof obligation を短く報告する。
