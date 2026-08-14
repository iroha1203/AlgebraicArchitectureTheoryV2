# Research Lean package

`ResearchLean.AG` is the separate source root for research-only Lean modules. It
depends on the repository root package; the root package does not depend on it.

Do not run the Research package full build, including `lake build`, aggregate
roots, all-module elaboration, or all-file loops. This applies to coordinating
agents, subagents, and CI. Focused checks are driven by the module manifest:

```bash
research/lean/check_research_modules.sh --focused ResearchLean/AG/Smoke.lean
```
