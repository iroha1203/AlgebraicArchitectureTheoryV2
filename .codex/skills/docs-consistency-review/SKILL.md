---
name: docs-consistency-review
description: リポジトリのドキュメントと実装・タスク状態の乖離を確認する。特に docs/ と Lean source、tools、GitHub Issues、proof_obligations の対応を調べ、documented done/proved/implemented claims が実装と一致するか検証し、軽微な docs drift は修正し、複雑な実装不足・証明不足・設計判断が必要な差分は報告する場合に使う。
---

# Docs Consistency Review

## 目的

ドキュメントが現在の実装とタスク状態を正しく反映しているか確認する。小さく低リスクなドキュメント乖離は直接修正し、実装・証明・研究判断が必要な差分は follow-up として報告する。

## 手順

1. 作業ベースを確認する。
   - `git status --short --branch` を確認する。
   - PR 化する作業なら `main` を最新化し、短い docs 用ブランチを切る。
   - 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。
   - ユーザーが明示しない限り、実装や証明ではなく docs 修正に絞る。

2. docs と実装を棚卸しする。
   - 対象ファイルを確認する:
     `rg --files docs Formal tools .github | sort`
   - docs の status / task marker を探す:
     `Lean status`, `proved`, `defined only`, `future proof obligation`, `empirical hypothesis`, `Issue`, `TODO`, `完了`, `証明済み`, `未評価`, `未実装`
   - Lean declaration を確認する:
     `rg -n "^(def|theorem|lemma|structure|class|inductive|abbrev)\\s+" Formal`
   - Lean placeholder / 禁止語を確認する:
     `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal docs`

3. docs の主張を実装と照合する。
   - `docs/formal/lean_theorem_index.md` は実装済み API の入口として扱う。ただし重要な名前は `Formal/` 側でも確認する。
   - `docs/proof_obligations.md` は task / status ledger として扱う。ただし GitHub Issues の完全な複製にはしない。
   - tooling claim は該当する `tools/` の README、source、tests を確認する。
   - 見つけた差分を短く列挙し、修正対象か報告対象か分類する。

## 分類基準

- **軽微な docs drift**: wording が古い、実装済み API が索引にない、完了済み項目が future のまま、README の案内が不足している。直接修正する。
- **境界の明確化**: docs が実装より強い theorem、extractor completeness、empirical claim を示唆している。正しい書き方が明確なら直接修正する。
- **複雑な gap**: 解消に新しい Lean theorem、tooling behavior の変更、Issue triage、研究判断、設計判断が必要。勝手に直さず、根拠と follow-up を報告する。
- **意図的な非主張**: `empirical hypothesis`, `future proof obligation`, tooling boundary と明示されている。Lean theorem と混同しないよう維持する。

## 修正方針

- 明示的な依頼がない限り docs-only にする。
- 実装が支えていない研究主張を強めない。必要以上に弱めもしない。
- Lean status vocabulary は `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` を使う。
- `ArchitectureSignature` は単一スコアではなく多軸診断として扱う。
- extractor output は、proof-carrying bridge や validation report がない限り `ComponentUniverse` と同一視しない。
- equivalence chain が部分実装なら、次に分けて書く。
  - 無条件に `proved` な事実
  - finite universe 下で `proved` な事実
  - `future proof obligation`
- 大きな rewrite より、小さな wording update、status table、index 追加を優先する。

## 検証

docs-only 変更では次を実行する。

```bash
git diff --check
rg -n "[\\u200B-\\u200F\\u202A-\\u202E\\u2066-\\u2069]" <changed-doc-files>
rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal docs
lake build
```

placeholder scan は文脈を見る。docs の方針説明に出る `axiom` / `sorry` は許容できるが、Lean source に新規混入してはいけない。

tooling docs または tooling behavior に触れた場合は、該当 tool のテストも実行する。

```bash
cargo test --manifest-path tools/sig0-extractor/Cargo.toml
```

## 報告

完了時に次を簡潔に報告する。

- 編集したファイル
- 修正した軽微な drift
- あえて残した複雑な gap
- 実行した検証コマンドと結果

PR を作る場合は、リポジトリの PR template に従い、タイトルと本文を日本語で書き、`Closes #N` を入れ、`gh pr checks --watch` で CI を確認する。
