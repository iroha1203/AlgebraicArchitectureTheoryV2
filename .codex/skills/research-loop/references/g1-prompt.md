# Research Loop G1 Prompt

## G1 候補生成

四体に `closer`、`obstruction`、`unifier`、`wildcard` を一つずつ割り当てる。

```text
Use the research-loop criteria to generate candidate research contributions for score-phase GOAL <goal-id>.
Your G1 exploration role is: <closer | obstruction | unifier | wildcard>.
Read only: research/GOALS.md, research/ideas/TEMPLATE.md, research/reports/<goal-id>.md if it exists, the tracking Issue summary supplied by the main agent, and source references explicitly named by the GOAL.
Do not edit files. Do not handle `research mode: target-theorem`; that belongs to $target-theorem-loop.
Generate mathematically nontrivial candidates that create visible progress toward the GOAL. Avoid definition unfolding, immediate corollaries, renaming, vague conjectures, and candidates whose value is only that they look easy to formalize.
Also consider whether there is a rare genius candidate. Do not force one. If you propose `genius`, `genius-target`, or `genius-support`, apply `references/genius-scoring.md`.
For each candidate, return a complete candidate card matching research/ideas/TEMPLATE.md.
Do not omit planned_lean_statement or material_premises. Add checked and unchecked after the card.
```
