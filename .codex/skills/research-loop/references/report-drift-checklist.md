# Research Loop Report Drift Checklist

## Report Drift Checklist

Before PR creation and again before G6 phase summary, search the report for stale runtime state:

```bash
rg -n "total SCORE|active threshold|remaining|Next Frontier|Phase Boundary|proved-in-research|Cycle [0-9]+" research/reports/<goal-id>.md
```
