# PRD guideline

この文書は、PRDの責務、lifecycle、参照規律、完了後削除の条件を定める正本である。

## PRD lifecycle

- PRDは実装作業中だけ有効な一時的実行契約である。
- PRDに置いてよい内容は、問い、現状診断、現行source of truth・非PRD依存・Issueへの参照、
  要求、acceptance criteria、当該作業の失敗判定としてのFailure Contract、実装計画、
  task固有のtarget statement、non-goals、停止条件に限定する。
- PRDに恒久的な規律、編集ルール、schema / artifact contract、status語彙、
  product/runtimeのFailure Contract、運用手順の正本を書いてはならない。これらはPRD着手前に
  数学本文、guideline、仕様書、台帳、schema文書などの現行source of truthへ置き、PRDは参照だけを持つ。
- target statementの一次仕様は、PRD、GOAL・候補カード、GitHub Issue、現行docs、数学本文、
  その他のtask artifactのいずれでもよい。実装開始前に一次仕様を1つ指定し、target claim、
  必要な結論、明示された仮定・受け入れ条件を実装者と査読者が作業中に参照できる状態を保つ。
  target theoremや新規defの完全Lean signatureは必要に応じて記録してよいが必須ではない。
  同じclaimやsignatureを複数箇所へ正本として複製しない。
- 実装前に、完成実装の写し、全補題の証明列、生成物一式、またはそれらを説明する
  大規模または恒久的なevidence packetを作ることを要求してはならない。必要な事前固定は、実装する対象、
  acceptance criteria、必要なら target theorem と新規def の最小 signature に限る。
  実装・証明の一次証拠は実装PRの固定headに置き、検証結果はそのheadに紐付く
  PR・CIの記録に置く。一次証拠への短いlink索引は作ってよい。
- 作業中に恒久ルールが必要になった場合も、先に現行source of truthへ反映してから
  PRDのacceptance criteriaへ組み込む。

## 完了と削除

PRDは次をすべて満たした後に削除する。

1. acceptance criteriaがすべて充足されている。
2. 必要な分野別review、test、CIが完了している。
3. taskが要求する実装・docs・台帳・website等がmerge済み、または明示された納品状態にある。
4. 成果物、恒久contract、恒久ルール、statusが現行source of truthへ反映されている。
5. repository全体から、そのPRDへの参照がゼロである。

完了後のPRDは削除する。archiveは作らない。
既存PRDや既存参照も例外扱いせず、上記条件を満たすまで文書整理の完了根拠に数えない。
PRDがtask固有のtarget statementの一次仕様である場合も、履歴はGit commit historyとGitHub Issue / PR / reviewに残る。
同じclaimやsignatureを完了後の現行docsへ移すことは削除条件にしない。

## PRD参照の禁止

現行のdocs、README、台帳、guideline、website、source code、test、fixture、schema、workflowから
個別PRD本文、個別PRDのpath、title、contractへの参照を禁止する。作業中の別PRDからの参照も禁止し、PRD間の依存は
GitHub Issueのdependencyで管理する。Git commit historyとGitHub Issue / PR / reviewの
作業履歴もrepositoryの現行文書・コードではないため、この参照禁止の対象外とする。

完了scanでは、対象PRDについて少なくとも次を検索する。

- 現在path
- filename
- 文書title
- `PRD-N`などの固有identifier

一般語としての `PRD` や、別PRDを指すidentifierのhitは対象PRDへの参照として数えない。
各hitを実読し、対象PRDへのlink、path、citation、sourceRef、fixture metadata、正本依存であれば
除去または恒久sourceへの置換を行う。

PRDの削除によって失われる恒久規律・恒久contract・statusがある場合、削除条件4は未達である。
