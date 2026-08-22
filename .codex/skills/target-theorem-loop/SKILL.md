---
name: target-theorem-loop
description: "research/goals/GOAL-ID.mdのactiveなtarget-theorem GOALで、固定targetを弱めずproof obligationをLean theorem、premise discharge、finite witness、blockerとして消化し、標準PR監査と最終math-lean-reviewまで進める。\"$target-theorem-loop goal-id\"、\"大定理証明ループ\"で使う。探索型SCORE phaseにはresearch-loopを使う。"
---

# Target Theorem Loop

`research mode: target-theorem`のactive GOALだけを扱う。GOALのtarget statement、boundary、completion criteria、premise ledger、anti-weakening rule、failure policyを固定入力とし、進捗を一つのproof obligation deltaで管理する。

GOALまたは指定一次仕様を弱める必要が生じたら、改訂案をtracking Issueへ記録して`goal defect`で止まる。ループ中に正本を書き換えない。

起動は`$target-theorem-loop <goal-id>`とし、必要なら`max-cycles <N>`を付ける。

## 読むもの

開始時に次を読む。

- `research/README.md`
- `research/goals/<goal-id>.md`
- [target GOAL contract](references/target-goal-contract.md)
- [acceptance contract](references/acceptance-contract.md)

到達した段階のreferenceだけを追加で読む。

- 実装・検証: `docs/aat/lean_quality_standard.md`、`docs/aat/guideline.md`
- obligation選定・PR作成: [cycle ledger](references/cycle-ledger.md)
- PRレビュー: `../review-pr/SKILL.md`
- 完了候補: [completion ledger](references/completion-ledger.md)、`../math-lean-review/SKILL.md`

## Research full build hard rule

Research packageの全体buildは実行しない。`cd research/lean && lake build`、全Research module、aggregate root、全file loopをelaborateする同等操作も、親・subagent・CIのすべてで実行しない。Researchの検証は対象fileのfocused check、必要なtargeted module check、axiom・placeholder・Unicode・privacy scanで行う。

## 実行

1. `git status --short --branch`と未追跡fileを確認し、base/headを固定する。mainから開始する場合はmainを最新化する。
2. GOALがactiveかつtarget-theorem modeであり、[target GOAL contract](references/target-goal-contract.md)を満たすことを確認する。欠陥時はIssueを新設せず停止理由を返す。
3. tracking Issueを特定し、なければ一本だけ作る。GOALのtarget節、Issueの直近state、reportの現proof obligation節、proof DAG、対象Lean宣言から現在状態を復元する。
4. rootが[cycle ledger](references/cycle-ledger.md)のselectionを埋め、大定理までのproof distanceを最も直接縮めるproof obligationを一つ選ぶ。
5. rootがLean theorem/package、input-generated witness/certificate、またはblocker/refutationを固定する。Lean証拠は`research/lean/ResearchLean/AG/<goal-area>/`に置き、`Formal/AG`は参照/importだけに使う。受理spineとcycle scaffoldを命名またはfileで分け、spine declaration listをreportに固定する。
6. rootが対象fileのfocused check、報告対象全宣言の`#print axioms`、placeholder、hidden/BiDi、privacy、import方向を検査する。中心項目の未確認はpacketへ残す。
7. `git diff --check`、staged diff、未追跡file、保護領域の変更有無を確認し、実装、report、cycle ledgerを同じPRへ収録する。PR本文は原則`Refs #<tracking-issue>`とする。
8. PR headを固定し、標準`$review-pr <PR番号> tracking Issue #<N>`でそのPRのexact diffと変更責務を監査する。`Refs`だけにIssue関連付けを委ねない。監査コメントでAAT/Lean数学claimとして`$math-lean-review`へ委譲されたことを確認し、未委譲なら`Blocked / cannot determine`としてmergeしない。標準レビュー後、rootが[acceptance contract](references/acceptance-contract.md)をreview evidenceと差分実体へ適用し、結果をPRコメントへ置く。completion candidateでは両方の合格後に[completion ledger](references/completion-ledger.md)のfinal packetを同じ固定headから生成し、独立`$math-lean-review research/goals/<goal-id>.md <goal-id>`でGOALカードと累積証拠全体を照合する。必要な全判定とCIが通った場合だけmergeし、merge commit、CI、PR review、completion review、次obligationをtracking Issueへコメントする。

PR作成まではroot一体で完結する。最初の独立subagent起動点はPRレビューである。

cycleの書込範囲は、対象ResearchLean証拠、同じPRのreport/ledger、completion candidateのfinal packet、標準review-pr監査記録、merge後のtracking Issueコメントとする。final packetは固定headに対するPRコメントであり、treeへ追加しない。数学claimの判定範囲はGOALのclaim boundaryに限る。

## Cycle result

- `proof-obligation-discharged`: 選んだobligationを、入力dataからのLean theorem/construction、finite witness、またはreview済みpredecessor theoremで閉じた。
- `blocker-fixed`: 反例、必要条件、仮説不足、proof blockerを再利用可能な証拠として固定した。
- `proof-checkpoint`: 証拠はあるが、未放電premise、provenance、proof-use、route、coverage、reviewのいずれかが残る。
- `rejected`: statement不一致、hidden premise、証拠不足、claim越境、target-fitting routeがある。

`approve`は上記resultの受理だけを表す。`target-theorem-proved`は最終完了判定専用である。

## PR gate

すべてのPRを標準`$review-pr`へ渡す。target-theorem固有のroute、lane、修正後確認を`review-pr`へ追加しない。標準review-prは固定headのexact diff、変更責務、Issue受入条件を監査し、責務に対応する分野別敵対レビューへ委譲する。

1 cycleの正式レビューは、初回と本筋修正後の再実行1回までとする(findingの中心/非中心の区分、本筋修正と微調整の手続き、後出しの扱いは共有review protocol「レビューバッチと修正後確認」が正本)。再実行後になお中心findingが残る、または新たに出る場合は、そのheadをmergeせず、cycle resultを`rejected`として記録し、次cycleで選定し直す。非中心findingは直接対応で解消するまでmergeしない。

標準レビュー後、rootはその独立review evidenceと固定headの実体からstatement、premise discharge、provenance、proof-use、field escape、route、nonvacuity、dependency、回帰scenarioを再統合する。中心項目の未確認、不一致、証拠なしはmerge不可とする。

completion candidateでは、PR内容判定を再利用せず、別の`$math-lean-review`を数学2本・Lean 2本で起動する。固定GOALカードのtarget、boundary、全completion criteria、全material premise ledger行を、累積Lean declarations、proof artifacts、依存DAG、report/ledgerへ照合する。4本すべてと統合verdictが正確に`No major findings`でなければcompletion不可とする。

## Completion

`target-theorem-proved`は、次をすべて満たす場合だけ出す。

- GOALの全completion criteriaと全proof artifactsが満たされる。
- 全`discharge-required`行が入力dataからのtheorem/construction、finite witness、またはreview済みpredecessor theoremで放電される。
- statement強度、certificate provenance、proof-use、structure-field escape、route integrity、nonvacuity、全方向、definition unfolding、dependency DAGが確認済みである。
- 対象全宣言のaxiom audit、placeholder scan、report/ledger/Issue対応が確認済みである。
- final packetに中心claimの`unchecked`がなく、4本査読の統合verdictが正確に`No major findings`である。

rootは4本の結果を貼るだけで終えず、final packet、unchecked、Lean declaration、report/ledgerの対応を再判定する。判定範囲はGOALのclaim scopeに限る。

一項でも欠ければ`target-theorem-proved`を出さず、[completion ledger](references/completion-ledger.md)のschemaで`target-proof-checkpoint`、`target-refuted`、または`target-blocked`をPR監査コメントとtracking Issueに記録する。CI green、merge、定理名の存在、wrapper、supplied certificateだけでは完了にしない。

## 停止条件

- `target-theorem-proved`: 上のCompletionを満たす。
- `target-proof-checkpoint`: 有用なproof packageは固定したが、未放電・弱化risk・coverage gap・最終査読不合格が残る。
- `target-refuted`: 現target statementへの反例または必要仮定不足を固定した。
- `target-blocked`: 同じblockerが二cycle連続で解消しない。
- `goal defect`: GOAL契約の欠陥または正本改訂が必要である。
- `proof stagnation`: 二cycle連続で受理可能なproof DAG、premise、blockerのdeltaがない。
- `review stagnation`: 二cycle連続で、本筋修正後の再実行でも中心findingが残る、または新たに出る。
- `max-cycles`: 指定した上限に達する。
- `all blocked`: 全未完obligationにblockerがあり、GOAL内で実行可能な次手がない。
- `undecidable`: 必須判定を分ける証拠もboundedな検査経路も固定できない。

停止条件または人間の明示停止まで反復する。終了時は停止理由、完了/未完obligation、premise status、review verdict、PR/merge、次obligationを報告する。tracking Issueは人間の明示指示なしにcloseしない。
