---
name: target-theorem-loop
description: "research/GOALS.md の `research mode: target-theorem` GOAL に対して、大定理までの proof obligation を一つずつ Lean theorem、premise discharge、blocker/refutation として固定する専用ループ。SCORE と candidate card は使わず、material premise の certificate provenance / proof-use / structure-field escape を監査し、完了判定では `$math-lean-review` の4並列査読を必須 gate にする。Use when the user says \"$target-theorem-loop <goal-id>\", \"大定理証明ループ\", \"target theorem loop\", or asks Codex to prove a GOALS.md target theorem to completion."
---

# Target Theorem Loop

この skill は、`research/GOALS.md` の `research mode: target-theorem` GOAL だけを扱う大定理証明義務消化ループである。探索型 SCORE phase は `$research-loop` の責務であり、この skill では実行しない。

目的は、GOAL カードに定義された target theorem を弱めず、必要な proof obligation を一つずつ Lean theorem、finite witness、concrete certificate、または blocker / obstruction として固定し、大定理本体の完了条件へ近づけることである。SCORE と candidate card はこの skill では使わない。進捗は `approve` / `reject` と proof obligation delta だけで判定する。

explicit certificate はそれだけでは premise discharge ではない。certificate / class membership / structure field / theorem argument が material premise を透明に保持しているだけなら、target theorem completion ではなく checkpoint とする。target loop は、certificate を受け取る theorem だけでなく、その certificate を対象境界の入力 data から生成する theorem / construction / finite witness / instance chain を proof obligation として潰す。

ズルい proof route は fail-closed に扱う。ここでいうズルい route とは、target theorem を直接弱めなくても、証明しやすい object / cover / coefficient / certificate / class を後から選び、結論相当の性質を construction choice、structure field、certificate field、opaque membership、または未使用 premise に移して completion へ近道する経路である。特に、欲しい differential / exactness / descent / effectivity / vanishing / comparison law に合わせて selected object を ad hoc に作る場合、canonical / free / universal property / input-boundary construction / nonvacuity theorem のいずれかで正当化できなければ `proof-checkpoint` または `rejected` とする。

各 cycle は `route_integrity_audit` を持つ。T1 は現在の最短 route が target-fitting construction、premise relocation、vacuous witness、unused package component、one-way theorem sold as equivalence、GOAL/report 後追い改訂のどれに近いかを明示する。T3 は独立にこの audit を検査し、中心 claim に関係する未確認項目があれば completion candidate を `no` にする。T5 では `$math-lean-review` の verdict とは別に親 Codex が route integrity を再判定し、未確認なら `target-theorem-proved` を出さない。

大定理の完了判定では、必ず `$math-lean-review research/GOALS.md <goal-id>` を実行し、その正式判定を final completion record に取り込む。`$math-lean-review` が実行不能、4 並列査読不能、coverage 不足、または verdict が `No major findings` 以外の場合、`target-theorem-proved` を出してはならない。結果は `target-proof-checkpoint`、`target-blocked`、または `target-refuted` に倒す。

## 入口

起動は `$target-theorem-loop <goal-id>` とする。`goal-id` は [research/GOALS.md](../../../research/GOALS.md) の active な `research mode: target-theorem` GOAL を指す。任意で `max-cycles <N>`、特定 proof obligation、特定 blocker、証明寄り / 反例寄りの指示を渡してよい。

最初に次を読む。

- [research/README.md](../../../research/README.md)
- [research/GOALS.md](../../../research/GOALS.md)
- [research/reports/README.md](../../../research/reports/README.md)
- [research/DESIGN.md](../../../research/DESIGN.md)
- [../math-lean-review/SKILL.md](../math-lean-review/SKILL.md)

必要なときだけ読む。

- T0 の target GOAL card 検査: [references/target-goal-contract.md](references/target-goal-contract.md)
- T1 selector / T3 audit / PR review / final review の標準プロンプト: [references/target-subagent-prompts.md](references/target-subagent-prompts.md)
- T4 cycle result / merge / completion の tracking Issue コメント: [references/target-ledger-templates.md](references/target-ledger-templates.md)

`research/GOALS.md` は target theorem の正本として扱い、ループ中に編集しない。target statement、boundary、completion criteria、premise discharge policy、material premise ledger、anti-weakening rule、failure policy を弱める必要がある場合は、tracking Issue または別 Issue に GOAL 改訂提案を残して止まる。

## Target Proof Contract

target theorem の完了条件は GOAL カードの `target theorem completion criteria` と `target proof artifacts` で決まる。PR merge、CI green、Lean file が build することは必要な証拠ではあっても完了条件ではない。

cycle result は次のいずれかに分類する。

- `proof-obligation-discharged`: proof DAG の node、material premise、bridge、normalization、finite witness などを Lean 証明または concrete certificate で消した。
- `blocker-fixed`: target theorem の仮説不足、反例、必要条件、proof blocker を固定した。
- `proof-checkpoint`: target theorem 本体または theorem package に近いまとまりはあるが、未放電 premise、弱化 risk、coverage gap、final review 未実行が残る。
- `rejected`: target statement の弱化、hidden premise、Lean evidence 不足、claim boundary 越え、または proof distance が縮まらないため採用しない。

`target-theorem-proved` は cycle result ではなく、final `$math-lean-review` 後の completion verdict 専用の状態である。

`proof-checkpoint` でも、material premise が theorem argument、typeclass、structure field、certificate field、opaque membership に残る場合は、completion ではない。ambient boundary として残せるのは、対象 site、finite vocabulary、cover、coefficient object、supplied observation contract などの入力幾何だけである。

`route_integrity_audit` は、proof route が target conclusion に合わせて作られたものではなく、GOAL の入力境界、canonical/free construction、universal property、finite witness、または reviewed predecessor theorem から来ているかを確認する audit である。次のいずれかが中心 claim に関係する場合は、`target-theorem-proved` を禁止する。

- selected object / cover / sheaf / coefficient / complex / certificate が、欲しい theorem を成立させるためだけに選ばれている。
- differential、exactness、descent、effectivity、global coherence、obstruction vanishing、comparison/naturality が field として与えられ、その field の入力境界からの構成 theorem がない。
- 空型、singleton、trivial relation、degenerate cover などにより theorem が vacuous になるが、nonvacuity / adequacy theorem がない。
- 片方向 theorem、conditional package、wrapper theorem を target の同値または completion として扱っている。
- GOAL / report / ledger を proof 後に弱い証明へ合わせて読み替えている。

`proof-obligation-discharged` と呼べるのは、対象 GOAL の `discharge-required` premise が次のいずれかで閉じた場合だけである。

- 入力境界から certificate / witness を構成する Lean theorem。
- 有限 witness / concrete construction が Lean theorem として固定されている。
- 既に `$math-lean-review` または同等の target-loop audit を通った predecessor theorem から導かれる。

次は discharge ではなく `proof-checkpoint` または `rejected` とする。

- theorem が certificate を明示引数として受け取るだけ。
- certificate / structure field が exactness、descent、effectivity、global coherence、obstruction vanishing、comparison/naturality、semantic closure などを直接保持している。
- main theorem の proof term で material premise が使われず、package の別成分として添付されるだけ。
- field から accessor theorem を出しているだけで、field の生成 theorem がない。

判定は常に `approve` / `reject` で返す。`approve` は target theorem 完了を意味しない。何として承認したかは `result_type` で表す。

```yaml
decision: approve | reject
result_type: proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected
completion_candidate: yes | no
```

## サイクル

```text
T0 状態確認
T1 selector subagent が次に潰す proof obligation を一つ選ぶ
T2 Lean 証明または blocker を固定する
T3 audit subagent が最小監査する
T4 report と tracking Issue を同期する
T5 completion candidate なら final review
```

ひとサイクルで扱う主成果は原則ひとつにする。ただし一つの proof obligation を構成する補題群はまとめてよい。target statement を弱めて成功扱いしない。

### T0 状態確認

1. `git status --short --branch` と `git ls-files --others --exclude-standard` を確認する。ユーザーの未コミット変更は戻さない。
2. `main` を最新化する。
3. GOAL card が active かつ `research mode: target-theorem` か確認する。GOAL が active でなければ Issue を作らず止まる。mode が違う場合も Issue を作らず `$research-loop <goal-id>` へ誘導して止まる。
4. tracking Issue `Research Loop: <goal-id>` を探し、なければ作る。
5. GOAL card から target theorem、boundary、proof artifacts、proof strategy、completion criteria、premise discharge policy、material premise ledger、anti-weakening rule、failure policy を抽出する。
   - material premise ledger の各行を `ambient-boundary`、`direction-hypothesis`、`discharge-required`、`conclusion-equivalent-risk` に分類する。
   - `discharge-required` premise について、現状の証拠が certificate argument / structure field / opaque membership に止まっていないか初期分類する。
   - selected / canonical / free / realization / certificate / finite witness / class-boundary を使う GOAL では、GOAL card に route integrity gate があるか確認する。ない場合は `goal defect` または `proof-checkpoint` とし、tracking Issue に改訂提案を残す。
   - 現在の proof route について target-fitting construction、vacuity、one-way-as-equivalence、premise relocation の初期 risk を列挙する。
6. tracking Issue と report から proof state、完了 proof obligation、未完 proof obligation、blocker、PR、直近 proof attempt を読む。
7. T0 state を短い入力メモにして T1 selector subagent に渡す。

target GOAL card の必須項目と欠陥判定は [references/target-goal-contract.md](references/target-goal-contract.md) を正とする。

### T1 selector subagent が次に潰す proof obligation を一つ選ぶ

広い探索や候補 pool は作らない。メインスレッドで候補比較を抱え込まず、独立した selector subagent 一体に GOAL card、tracking Issue、report、Lean ファイル、T0 state memo だけを渡し、大定理までの proof distance を最も直接縮める proof obligation を一つ選ばせる。本体の期待、採用したい結論、実装方針は渡さない。

優先順:

1. `discharge-required` の material premise。
2. certificate provenance gap。certificate を受け取る theorem はあるが、その certificate を構成する theorem / finite witness がない場合。
3. proof-use gap。main theorem の material premise が未使用、または package の別成分として添付されるだけの場合。
4. structure-field escape。exactness、descent、effectivity、coherence、vanishing、comparison/naturality が field として供給されるだけの場合。
5. target theorem 本体の Lean statement と自然言語 target の対応 gap。
6. support map / proof DAG の未接続 node。
7. blocker、反例、必要条件として固定すべき obstruction。
8. report / tracking Issue の同期 drift。

selector subagent は、選んだ obligation について次を cycle input として返す。

```yaml
proof_obligation:
expected_result_type: proof-obligation-discharged | blocker-fixed | proof-checkpoint
lean_targets:
premise_risk:
anti_weakening_risk:
certificate_provenance_risk:
proof_use_risk:
structure_field_escape_risk:
route_integrity_risk:
cheat_route_risk:
selection_reason:
rejected_alternatives_summary:
completion_candidate: yes | no
```

### T2 Lean 証明または blocker を固定する

Lean 証拠は `Formal/AG/Research/<goal-area>/...` に置く。`Formal/AG` 本体は参照または import のみ可とし、このループでは直接編集しない。

cycle は次のどちらかを固定する。

- Lean theorem / theorem package / finite witness / concrete certificate。
- target theorem の現 statement では進めないことを示す blocker / obstruction / refutation evidence。

certificate を導入する場合は、次を同じ cycle で明示する。

- certificate の field が何を保持するか。
- その certificate が conclusion-equivalent data を保持しない理由。
- certificate を入力境界から構成する theorem / finite witness があるか。ない場合は `proof-checkpoint` とし、次 obligation を certificate construction / premise discharge にする。
- main theorem で certificate が proof term に使われるか。未使用なら main theorem の completion candidate にしない。

selected object / cover / sheaf / coefficient / complex / realization layer を導入する場合は、同じ cycle で次を明示する。明示できない場合、成果は route construction checkpoint であり completion candidate ではない。

- どの入力境界から構成されたか。
- conclusion-side law を field に持っていない理由。
- canonical / free / universal property / finite construction / reviewed predecessor theorem のどれで正当化されるか。
- degenerate / vacuous な選択でないことを示す nonvacuity / adequacy evidence。
- selected differential や comparison law が restriction map、functoriality、構成展開、または証明済み theorem から出ること。

単なる未採用候補、途中で潰れた idea、reject 候補は永続化しない。後続 cycle で同じ失敗を避ける必要がある blocker だけ report / tracking Issue に残す。

足場衛生を保つ。受理ルートが名前参照する宣言(スパイン)と、サイクル足場(premise 順列帯、`of_X_via_Y` 型再入口変種、checkpoint 帯)を、ファイル分割または命名で区別できる状態に保つ。同一ファイルへの cycle 挿入の累積で、スパインが行範囲でも時系列でも切り出せない状態を作らない。正典化(蒸留移植)の単位になるスパイン宣言リストは、tracking Issue または report で追える状態を保つ。

### T3 audit subagent が最小監査する

通常 cycle の合格条件:

1. focused `lake env lean <target-file>` が通る。
2. 必要に応じて `lake build FormalAGResearch` が通る。
3. 報告対象 declaration の `#print axioms` audit が通る。
4. placeholder scan が clean。
5. target statement を弱めていない。
6. hidden material premise がない。
7. 必要 premise が discharge 済み、または remaining として明記されている。
8. `discharge-required` premise の certificate provenance が確認済み、または未放電として残っている。
9. main theorem / package の material premise が proof term で使われている。未使用 premise は completion candidate から除外する。
10. structure / certificate field が conclusion-side content を供給していない。供給している場合は checkpoint として扱う。
11. route integrity が確認済み。ad hoc target-fitting construction、vacuity、one-way-as-equivalence、GOAL/report 後追い読み替えがあれば rejected または checkpoint とする。

ローカルでは対象範囲に応じて次を実行または同等に確認する。

```bash
lake env lean <target-file>
lake build FormalAGResearch
#print axioms <declaration>
rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal/AG/Research
rg -nP "[\\x{200B}-\\x{200F}\\x{202A}-\\x{202E}\\x{2066}-\\x{2069}]" <changed-files>
rg -n "$HOME|${TMPDIR%/}" <changed-files>
```

ローカル検証結果、diff、T1 cycle input、Lean declaration、premise ledger を独立した audit subagent 一体に渡し、公平に監査させる。本体の期待、成功させたい verdict、実装者の自己評価は渡さない。

audit subagent は `approve` / `reject` で返す。`approve` の場合も、`completion_candidate: yes` でなければ final review は走らせない。

```yaml
cycle_result:
  decision: approve | reject
  result_type: proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected
  lean_artifacts:
    - file:
      declarations:
  premise_delta:
    discharged:
    remaining:
  certificate_provenance:
    discharged:
    unresolved:
  proof_use_audit:
  structure_field_escape_audit:
  route_integrity_audit:
  cheat_route_audit:
  blocking_findings:
  next_obligation:
  completion_candidate: yes | no
```

### T4 report と tracking Issue を同期する

cycle 完了時だけ report と tracking Issue を同期する。candidate card は作らない。

同期する最小項目:

- `decision`
- `result_type`
- Lean file と declaration
- `premise_delta`
- `certificate_provenance`
- `proof_use_audit`
- `structure_field_escape_audit`
- `route_integrity_audit`
- `cheat_route_audit`
- `blocking_findings`
- `next_obligation`
- `completion_candidate`
- final review を走らせた場合は `$math-lean-review` verdict

tracking Issue には runtime state を置く。report には証拠索引と proof obligation delta を置く。`research/GOALS.md` は編集しない。

### T5 completion candidate なら final review

`completion_candidate: yes` かつ T3 の最小監査が通った場合だけ、final review に進む。

final review 前に、親 Codex は次の `final_review_packet` を固定する。中心 claim に関わる項目が欠ける場合は `$math-lean-review` に進まず `target-proof-checkpoint` に落とす。

```yaml
final_review_packet:
  goal_claim:
  completion_criteria:
  lean_declarations:
  proof_artifacts:
  completed_proof_obligations:
  remaining_proof_obligations:
  material_premise_discharge:
  certificate_provenance_audit:
  proof_use_audit:
  structure_field_escape_audit:
  route_integrity_audit:
  cheat_route_audit:
  axiom_audit:
  placeholder_scan:
  dependency_dag:
  anti_weakening_audit:
  report_refs:
  tracking_issue_refs:
```

final review では必ず `$math-lean-review research/GOALS.md <goal-id>` を実行する。入力には `final_review_packet`、GOAL claim、completion Lean declarations、proof artifacts、tracking Issue proof state、T3/T4 の evidence を渡す。`$math-lean-review` の 4 並列査読が正式に走らなければ完了判定はできない。

4 査読すべてに veto 権を持たせる。数学査読 A/B、Lean 査読 A/B のどれか一つでも `Reject / 証明として不十分`、`Major revisions`、`Minor issues`、`Blocked / cannot determine`、または中心 claim に関わる `unchecked` を返した場合、`target-theorem-proved` は出さない。

final review では `unchecked` を fail-closed に扱う。中心 claim、material premise、anti-weakening、route integrity、dependency theorem、axiom audit、placeholder scan、ledger/report sync のどれかが未確認なら、結果は `target-proof-checkpoint` または `Blocked / cannot determine` に倒す。

`target-theorem-proved` を出せるのは次をすべて満たす場合だけである。

- GOAL card の target theorem completion criteria が満たされている。
- target proof artifacts が存在し、Lean build、axiom audit、placeholder scan が clean。
- material premise ledger の `discharge-required` 行が theorem / finite witness / concrete certificate で discharge 済み。
- `discharge-required` 行に対応する certificate / structure / instance の provenance が確認済み。
- main theorem の proof term で material premise が実質的に使われており、未使用 premise による見せかけの強化がない。
- structure / certificate field が結論成分、exactness、descent、effectivity、global coherence、obstruction vanishing を単に供給していない。
- selected construction / realization / certificate が target-fitting な ad hoc 選択ではなく、入力境界、canonical/free construction、universal property、finite witness、または reviewed predecessor theorem から来ている。
- vacuity / degeneracy / one-way-as-equivalence / wrapper theorem による見せかけ completion がない。
- Lean statement が自然言語 target を弱めていない。
- dependency proof DAG、definition unfolding、nonvacuity、direction coverage、artifact sync が確認済み。
- material premise audit が全行 `discharged` または正当な `ambient-boundary` / `direction-hypothesis` として説明済み。
- anti-weakening audit で theorem argument、typeclass、structure field、certificate field、opaque membership への結論相当前提逃がしがない。
- route integrity audit で target-fitting construction、vacuity、後追い GOAL/report 読み替え、one-way theorem の同値扱いがない。
- main theorem だけでなく、support theorem、bridge theorem、finite witness theorem、certificate construction の依存 audit が確認済み。
- `$math-lean-review` の統合 verdict が正確に `No major findings` で、4 査読の不一致、中心 claim の unchecked、弱化、未放電、route integrity gap、台帳不一致が残っていない。

どれか一つでも満たせない場合、`target-theorem-proved` を出さない。`$math-lean-review` が `Reject / 証明として不十分`、`Major revisions`、`Minor issues`、`Blocked / cannot determine`、または coverage 不足なら `target-proof-checkpoint` に落とす。親 Codex は `$math-lean-review` の verdict を貼るだけでなく、final_review_packet、4 査読の不一致、unchecked item、ledger/report/Lean declaration の対応を再判定する。target statement が反例で壊れた場合は `target-refuted`、同じ blocker が二サイクル続けて解消しない場合は `target-blocked` とする。

## PR レビューとマージ

PR には Lean ファイルまたは証拠、report、tracking Issue の cycle result を含める。PR 本文は原則 `Refs #<tracking-issue>` を使い、人間の明示指示なしに tracking Issue を close しない。

受理(proof obligation の discharge 確定、および `target-theorem-proved`)を含む PR では、**`docs/aat/research_evidence_index.md` への1行登録(theorem 名、ファイル、本文ラベル、conjuncts 要旨、受理点、移植状況 `unported`)を出力義務とする**(Research 下限原則の検索基盤)。

PR 前に `git diff --check`、`git diff --cached --check`、未追跡ファイル、不可視 Unicode、ローカル絶対パス、保護対象 docs の編集有無を確認する。completion candidate、proof obligation discharge、material premise delta、または report / tracking Issue の proof ledger 更新を含む PR は `$review-pr <PR番号>` を独立 subagent で実行する。マージは独立レビューが mergeable で、CI または必要なローカル検証が通った場合だけ行う。

## 停止条件

- `target-theorem-proved`: GOAL の completion criteria を満たし、`$math-lean-review` が `No major findings`。
- `target-proof-checkpoint`: proof package や proof obligation のまとまりはあるが、未放電 premise、弱化、coverage gap、math-lean-review 不合格が残る。
- `target-refuted`: 現 target statement に反例または必要仮定不足が固定された。
- `target-blocked`: 未完 proof obligation または proof blocker が二サイクル続けて解消しない。
- `goal defect`: target GOAL card の必須項目や anti-weakening / material premise ledger に欠陥がある。
- `proof stagnation`, `review stagnation`, `max-cycles`, `all blocked`, `undecidable`。

## サブエージェント規律

通常 cycle では T1 selector subagent 一体と T3 audit subagent 一体を必須にする。T1 は proof obligation 選定だけを行い、T3 は evidence / Lean / premise / anti-weakening を公平に監査する。どちらにも本体の期待や採用したい結論を渡してはならない。

追加 subagent は原則使わない。必要な場合だけ、hidden premise audit、Lean axiom audit、PR review のような狭い focused audit に限定する。

final completion では `$math-lean-review` の 4 並列査読を必須にする。subagent を使えない環境では、`target-theorem-proved` を出してはならない。

## 安全規則

- `research/GOALS.md` は編集しない。target 改訂は提案に留める。
- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、docs/note は編集しない。
- AAT の target theorem に ArchMap extraction completeness、runtime measurement completeness、whole-codebase quality を混ぜない。GOAL が明示する claim boundary だけを判定する。
- Lean の依存は `Formal/AG/Research` から `Formal/AG` への一方向に保つ。
- `axiom`、予想以外の `sorry`、`unsafe` を相談なく持ち込まない。
- tracking Issue は人間の明示指示なしに close しない。
- 破壊的 git 操作は使わない。一時出力は `.tmp/` または `/private/tmp` に置く。

## 報告

終えるときは、日本語で停止条件、target proof state、完了 proof obligation、未完 proof obligation、premise discharge status、`$math-lean-review` verdict、PR / merge 結果、次の proof obligation を短く報告する。
