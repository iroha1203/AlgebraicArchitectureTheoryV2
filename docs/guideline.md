# Repository documentation guideline

この文書は、repository全体の文書lifecycleとPRDの責務を定める正本である。
各domain guidelineはdomain固有の配置先・claim規律だけを補足し、本規律を弱めない。

## PRD lifecycle

- PRDは実装作業中だけ有効な一時的実行契約である。
- PRDに置いてよい内容は、問い、現状診断、現行source of truth・非PRD依存・Issueへの参照、
  要求、acceptance criteria、当該作業の失敗判定としてのFailure Contract、実装計画、
  task固有のstatement contract、non-goals、停止条件に限定する。
- PRDに恒久的な規律、編集ルール、schema / artifact contract、status語彙、
  product/runtimeのFailure Contract、運用手順の正本を書いてはならない。これらはPRD着手前に
  数学本文、guideline、仕様書、台帳、schema文書などの現行source of truthへ置き、PRDは参照だけを持つ。
- statement contractの置き場所は固定しない。PRD、GOAL・候補カード、GitHub Issue、現行docs、
  その他のartifactのいずれでもよい。実装開始前に正本を1つ指定し、target theoremの名前と完全な
  signature、statementが参照する新規defのsignatureを固定し、実装者と査読者が作業中に参照できる
  状態を保つ。同じcontractを複数箇所へ正本として複製しない。
- 作業中に恒久ルールが必要になった場合も、先に現行source of truthへ反映してから
  PRDのacceptance criteriaへ組み込む。

## 完了とarchive

PRDは次をすべて満たした後にarchiveする。

1. acceptance criteriaがすべて充足されている。
2. 必要な分野別review、test、CIが完了している。
3. taskが要求する実装・docs・台帳・website等がmerge済み、または明示された納品状態にある。
4. 成果物、恒久contract、恒久ルール、statusが現行source of truthへ反映されている。
5. `docs/archive/`を除くrepository全体から、そのPRDへの参照がゼロである。

完了後のPRDは `docs/archive/` へ移す。archiveは履歴であり、現行source of truthとして扱わない。
既存PRDや既存参照も例外扱いせず、上記条件を満たすまで文書整理の完了根拠に数えない。
task固有のstatement contractがPRDにある場合、その履歴はarchiveされたPRDに保存される。
同じcontractを完了後の現行docsへ移すことはarchive条件にしない。

## PRD参照の禁止

現行のdocs、README、台帳、guideline、website、source code、test、fixture、schema、workflowから
PRDへの参照を持つことを禁止する。作業中の別PRDからの参照も禁止し、PRD間の依存は
GitHub Issueのdependencyで管理する。`docs/archive/`へ移したPRD本文は履歴であるため、当時の
参照を保存し、現行規律に合わせた遡及改稿を行わない。Git commit historyとGitHub Issue / PR / reviewの
作業履歴もrepositoryの現行文書・コードではないため、この参照禁止の対象外とする。

完了scanでは、対象PRDについて少なくとも次を検索する。

- 現在pathとarchive予定path
- filename
- 文書title
- `PRD-N`などの固有identifier
- 移動前pathや旧filename

一般語としての `PRD` や、別PRDを指すidentifierのhitは対象PRDへの参照として数えない。
各hitを実読し、対象PRDへのlink、path、citation、sourceRef、fixture metadata、正本依存であれば
除去または恒久sourceへの置換を行う。現行文書からarchive directoryへのcatalog linkも、対象PRDを発見する
導線である場合は禁止する。

## Domain source of truth

- AAT / Lean: 数学本文、`docs/aat/lean_quality_standard.md`、分割索引・台帳、merge済みLean宣言と機械的なstatement一致検査。
- SFT: `docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、SFT台帳。
- Tooling: `docs/tool/` の現行仕様、schema docs、CLI docs、source、test、fixture。
- Website: `docs/website/guideline.md`、`DESIGN.md`、`SITEMAP.md`、現行website source。

PRDのarchiveによって失われる恒久規律・恒久contract・statusがある場合、archive条件4は未達である。
