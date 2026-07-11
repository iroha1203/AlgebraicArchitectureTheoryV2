---
name: docs-review
description: docs/sft、非数学docs/note、PRD、README、.codex/skills、Lean差分を含まないdocs/aat台帳を扱う。docs-only差分やPR packetでは、claim・整合・情報密度・冗長記述を4観点で非編集レビューする。"$docs-review"単独のdrift点検では保守を行う。数学本文・GOAL・数学claimはmath-lean-reviewを使う。
---

# Docs Review

docs 分野のレビューと保守。分野の所有範囲は `docs/aat/` 台帳のみ、
`docs/sft/`, 非数学的な `docs/note/`, PRD, `.codex/skills/`, cross-domain docs,
README 類。Lean 実装(`Formal/`)を含む PR の `docs/aat/` 台帳差分は
math-lean-review が statement と一体で扱う。Lean 実装を含まない
docs-only の `docs/aat/` 台帳差分はこの skill のレビューモードで扱う。
数学本文・研究GOAL・固定statement・数学claimの変更は、Lean差分の有無に
かかわらず math-lean-review が扱う。
`docs/tool/` は tool-review、`docs/website/` は website-review の所有。

2つのモードを持つ。docs-only diff / docs review packet が渡された場合は
常にレビューモードであり、保守モードはユーザーの単独起動時のみ。

## レビューモード(敵対レビュー)

`.codex/skills/_shared/review-protocol.md` と
`.codex/skills/_shared/refutation-checklist.md` の全体を読み、
非編集・独立査読・fail-closed・報告形式をそのまま適用する。
AAT / Lean status・theorem・GOALを扱う場合だけ
`.codex/skills/_shared/lean-refutation-checklist.md`も読む。

### 4観点(サブエージェント必須)

4観点を4つの独立したsubagentに分け、共有契約どおり利用可能枠まで並行する。

1. **保護対象と責務分離**
   - `docs/aat/algebraic_geometric_theory/`, `docs/sft/software_field_theory.md`,
     `docs/sft/aat_interface.md` への明示依頼なしの変更を疑う。
   - AAT / SFT / Tooling / Website の責務と完了条件の混同、
     Archive の source of truth 化を疑う。

2. **完了・claim 規律**
   - Issue / PRD / acceptance test が要求する concrete condition 以外を
     完了判定に持ち込んでいないかを疑う。
   - AAT の完了レビューに source extraction / ArchMap observation /
     tooling validation の完全性を `non-conclusion`・残タスク・証明不能な
     限界として持ち込んでいないかを疑う(source-observation layer は
     AAT theorem package の外側にある)。
   - 実装・証明・発火を要求する条件を docs 記載だけで完了側へ動かす
     差分(宣言落とし)を疑う。処置ラベルの降格は PRD の許容リストと
     照合する。
   - scope記載(「〜とは主張しない」等)には checklist §4 の資格条件を
     適用する。Research 側に受理済み theorem がある欠落はscope制限ではなく
     `unported (Research-proved)` と書かれているかを疑う。

3. **整合・追跡可能性**
   - Issue、PRD、AC、実装状態、docs ledger 間の drift を疑う。
   - status table、リンク、参照先、用語、章構成が現在の実装・タスク状態と
     一致するかを突合する。帰属(部・定理番号)は checklist §5 で検査する。
   - 監査カバレッジの主張(「lint 済み」「監査済み」)は実際の検査対象
     リストと突合する。

4. **情報密度・公開品質・privacy**
   - 文書の目的、問い、要件、判定、証拠、制約、失敗防止規則のいずれにも
     寄与しない記述を疑う。長さだけで冗長と判定せず、各記述が防いでいる
     失敗、保持する判断、追加する証拠、必要な例外を確認する。
   - 同じ規則・説明・template・検証手順が複数箇所にあり、正本への参照で
     置き換えられる重複を探す。削除候補には残す正本を明記する。
   - `.codex/skills/` では、skill固有でない一般規律、別skillの手順再説明、
     必要stageより前に読む長いreference、発火後にしか読まれない使用条件を疑う。
   - PRDでは「問い」・達成条件・Failure Contract・設計判断に影響しない
     経緯説明、研究文書ではclaim・証拠・未解決事項・次の判断に影響しない
     進行談を疑う。日付入りの改訂経緯や過去事案は、現行規則の意味に必要な
     場合を除き、runtime promptから外す。
   - AATが比喩ではないこと、禁止語のhard stop、仮定放電、anti-weakeningなど、
     実際の失敗を防ぐ固有規則は、同じ保護を別の正本が提供すると証明できない
     限り冗長扱いしない。
   - 読者向けの構成、根拠、用語、説明順を疑う。
   - public-facing text の private name / path / 内部事情を疑う
     (checklist §6)。
   - 主張が強すぎる場合・防御的非主張リスト化している場合を疑う。

### 統合判定

共有契約の統合出力に従い、判定を
`Needs changes` / `No major findings` / `Blocked / cannot determine` で返す。

## 保守モード(単独起動時のみ)

旧 `docs-consistency-review` の機能を継承する。ユーザーが drift 点検・
docs 保守を単独で依頼した場合に使う。

### 手順

1. 作業ベースを確認する(`git status --short --branch`。未コミット変更は
   ユーザー変更として扱い、勝手に戻さない)。PR 化する作業なら `main` を
   最新化し、短い docs 用ブランチを切る。
2. **repo 全体を棚卸しする**(diff に紐づかない sweep):
   - `rg --files docs Formal tools .github | sort`
   - status / task marker: `Lean status`, `proved`, `defined only`,
     `future proof obligation`, `empirical hypothesis`,
     `packaged (assumption-relative)`, `statement-only`,
     `unported (Research-proved)`, `Issue`, `TODO`, `完了`, `証明済み`
   - Lean declaration: `rg -n "^(def|theorem|lemma|structure|class|inductive|abbrev)\s+" Formal`
   - placeholder: `rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs`
3. docs の主張を実装と照合する。`proved`・昇格・発火を主張する行は
   宣言名の存在確認で済ませず、サンプルで statement を実読する
   (`lean-refutation-checklist.md` §1–§2を適用)。tooling claim は `tools/` の README・
   source・tests を確認する。

### 分類基準(旧 docs-consistency-review を継承)

- **軽微な docs drift**: wording が古い、実装済み API が索引にない、
  完了済み項目が future のまま。→ 直接修正する。
- **冗長記述**: 本筋に寄与せず、固有の失敗防止規則・判断・証拠・例外を
  持たない重複や経緯説明。残す正本を特定できる場合だけ直接削除または参照へ
  置換する。保護規則か判断できない場合は削除せずfindingとして報告する。
- **claim scope の明確化**: docs が実装より強い theorem や未定義 contract を
  示唆している。正しい書き方が明確なら直接修正する。scopeを書く場合は
  checklist §4 の資格条件を満たすこと。
- **status 降格を伴う乖離**: docs / 台帳が `proved`・昇格・発火を主張するが
  実装が支えていない場合、そのラベルが PRD / Issue の実装要求に対応する
  なら docs 側を弱めて閉じず「複雑な gap」として報告する。
  実装要求と無関係な純粋な docs 誇張だけ、status を
  正直な値へ弱めて直接修正してよい。Research 側に受理済み theorem が
  ある場合の正直な値は `unported (Research-proved)` である。
- **複雑な gap**: 新しい Lean theorem、tooling 変更、設計判断が必要。
  勝手に直さず、根拠と follow-up を報告する。
- **意図的な非主張**: `empirical hypothesis`, `future proof obligation`,
  tooling scope と明示されているもの。維持する。

### 修正方針

- 明示的な依頼がない限り docs-only にする。
- 実装が支えていない研究主張を強めない。必要以上に弱めもしない。
- Lean status vocabulary は `docs/aat/guideline.md` の Lean status 節が正。
  三分化タグ(`packaged (assumption-relative)` / `statement-only`)や
  `unported (Research-proved)` の併記を、旧語彙への回帰として
  「修正」しない(退行修正の禁止)。
- `ArchitectureSignature` は単一スコアではなく多軸診断として扱う。
- source-observation output は、proof-carrying bridge や validation report が
  ない限り `ComponentUniverse` と同一視しない。
- equivalence chain が部分実装なら、次に分けて書く:
  無条件に `proved` な事実/finite universe 下で `proved` な事実/
  `future proof obligation`。
- `proof_obligations` 台帳は task / status ledger として扱い、
  GitHub Issues の完全な複製にはしない。
- 大きな rewrite より、小さな wording update、status table、索引追加を
  優先する。
- 修正後は checklist §6 の横断機械 scan と、影響があれば統括エージェントが
  PR前に`lake build`を1回だけ実行する。Research packageのfull buildはCIで実行せず、
  必要な場合だけ統括エージェントがローカルで1回実行する。subagentは`lake build`、aggregate root、module群、
  全file loopのelaborationを実行しない。focused checkは共有契約の単一file制限に従う。
  該当cargo testは変更範囲に応じて実行する。

### 報告

編集したファイル、修正した軽微 drift、あえて残した複雑な gap、
実行した検証を簡潔に報告する。PR を作る場合はリポジトリの PR template に
従い、日本語で書き、`Closes #N` を入れ、`gh pr checks --watch` で CI を
確認する。
