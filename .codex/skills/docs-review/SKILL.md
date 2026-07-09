---
name: docs-review
description: Docs / SFT / Research Notes / .codex/skills の docs-only 差分を敵対レビューし、単独依頼では docs drift も保守する。"$docs-review"、"docs の drift を点検して"、docs-only 差分レビューの依頼で使う。
---

# Docs Review

docs 分野のレビューと保守。分野の所有範囲は `docs/aat/` 台帳のみ、
`docs/sft/`, `docs/note/`, PRD, `.codex/skills/`, cross-domain docs,
README 類。Lean 実装(`Formal/`)を含む PR の `docs/aat/` 台帳差分は
math-lean-review が statement と一体で扱う。Lean 実装を含まない
docs-only の `docs/aat/` 台帳差分はこの skill のレビューモードで扱う。
`docs/tool/` は tool-review、`docs/website/` は website-review の所有。

2つのモードを持つ。docs-only diff / docs review packet が渡された場合は
常にレビューモードであり、保守モードはユーザーの単独起動時のみ。

## レビューモード(敵対レビュー)

これは**敵対レビュー**である。レビュワーの成果は反証の試行記録であり、
チェックリストの消化ではない。承認は反証の失敗としてのみ与える。
反証の手がかりの正本は `.codex/skills/_shared/refutation-checklist.md`
(特に §4 no-go 適用範囲、§5 帰属・名前だけ repackage・監査カバレッジ、
§6 横断機械 scan、§7 finding ゼロの資格条件)。

このモードではファイルを編集しない。実装者の自己申告は監査対象であって
証拠ではない。

### 4観点(サブエージェント必須)

4観点を4つのサブエージェントに分けて**必ず**並列実行する。起動できない
場合は親が代替せず `Blocked / cannot determine` に落とす(fail-closed)。

1. **保護対象と責務境界**
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
   - 境界記載(「〜とは主張しない」等)には checklist §4 の資格条件を
     適用する。Research 側に受理済み theorem がある欠落は境界ではなく
     `unported (Research-proved)` と書かれているかを疑う。

3. **整合・追跡可能性**
   - Issue、PRD、AC、実装状態、docs ledger 間の drift を疑う。
   - status table、リンク、参照先、用語、章構成が現在の実装・タスク状態と
     一致するかを突合する。帰属(部・定理番号)は checklist §5 で検査する。
   - 監査カバレッジの主張(「lint 済み」「監査済み」)は実際の検査対象
     リストと突合する。

4. **公開品質と privacy**
   - 読者向けの構成、根拠、用語、説明順を疑う。
   - public-facing text の private name / path / 内部事情を疑う
     (checklist §6)。
   - 主張が強すぎる場合・防御的非主張リスト化している場合を疑う。

### Sub-Agent Prompt

```text
Use the docs-review skill context (review mode). Review only the assigned
perspective. You are an adversarial reviewer: you are called to find grounds
for rejecting this diff, not to approve it. Read
.codex/skills/_shared/refutation-checklist.md and use it as refutation leads.
Perspective: <観点1〜4の名前>
Target: <files, diff range, or working tree scope>

Report in Japanese:
1. Findings, ordered by severity, with file/line references.
2. Refutation attempts: what you tried to refute and what evidence defeated
   each attempt (at least 3 entries when you report no findings).
3. Evidence checked.
4. Coverage limits.

Do not edit files. Do not treat the implementer's claim list as evidence.
Report any privacy leak regardless of your lane. The parent must not pass
expected findings to you.
```

### 統合判定

1. 判定: `Needs changes`, `No major findings`, `Blocked / cannot determine`
2. Findings: 重大度順。
3. 観点別まとめ(反証試行を含む)。
4. 実行した検証。
5. Coverage / residual risk。

4観点すべての報告が揃わない限り合格を出さない。finding ゼロの観点報告に
反証試行3件の記載がなければレビュー未実施として扱う。

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
   (checklist §1 / §2 を適用)。tooling claim は `tools/` の README・
   source・tests を確認する。

### 分類基準(旧 docs-consistency-review を継承)

- **軽微な docs drift**: wording が古い、実装済み API が索引にない、
  完了済み項目が future のまま。→ 直接修正する。
- **境界の明確化**: docs が実装より強い theorem や未定義 contract を
  示唆している。正しい書き方が明確なら直接修正する。境界を書く場合は
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
  tooling boundary と明示されているもの。維持する。

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
- 修正後は checklist §6 の横断機械 scan と、影響があれば `lake build` /
  該当 cargo test を実行する。

### 報告

編集したファイル、修正した軽微 drift、あえて残した複雑な gap、
実行した検証を簡潔に報告する。PR を作る場合はリポジトリの PR template に
従い、日本語で書き、`Closes #N` を入れ、`gh pr checks --watch` で CI を
確認する。
