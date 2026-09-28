# Research Lean package

`ResearchLean.AG` is the separate source root for research-only Lean modules. It
depends on the repository root package; the root package does not depend on it.

Do not run the Research package full build, including `lake build`, aggregate
roots, all-module elaboration, or all-file loops. This applies to coordinating
agents, subagents, and CI. Focused checks are driven by the module manifest:

```bash
research/lean/check_research_modules.sh --focused ResearchLean/AG/Smoke.lean
```

## Lean 成果物の退役

退役条件と証拠の保持は [研究領域の案内](../README.md#定義証拠進行状態) に従う。
対象成果物の退役時は、次の順で処理する。

1. report または proof record に最終検証 commit と退役する成果物一覧を固定する。
2. `research/lean/research-modules.txt` と `ResearchLean` の aggregate から対象を除去する。
3. 対象ファイルを削除し、現行文書の参照を固定 commit 付き参照へ置き換える。
