# Research Lean package

`ResearchLean.AG` is the separate source root for research-only Lean modules. It
depends on the repository root package; the root package does not depend on it.

The coordinating agent may run the full package build once before a PR:

```bash
cd research/lean && lake build
```

Subagents must not run this command or any aggregate/module-loop elaboration.
Focused checks are driven by the module manifest:

```bash
research/lean/check_research_modules.sh --focused ResearchLean/AG/Smoke.lean
```
