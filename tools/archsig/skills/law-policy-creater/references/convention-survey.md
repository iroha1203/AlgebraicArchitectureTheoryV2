# Convention Survey

Use this when deriving LawPolicy from an unfamiliar repository.

## Search Targets

Start with explicit instructions:

```bash
rg -n "must|shall|required|forbid|forbidden|boundary|permission|tenant|transaction|idempot|retry|provider|LLM|OpenAI|architecture|layer|dependency|policy" \
  AGENTS.md README* CONTRIBUTING* docs .github 2>/dev/null
```

Then inspect likely config and architecture surfaces:

- `AGENTS.md`, `CLAUDE.md`, `.cursorrules`, `.github/copilot-instructions.md`
- `README*`, `CONTRIBUTING*`, `docs/**`, `architecture/**`, ADRs
- CI workflows and required checks
- framework config and route/dependency declarations
- security, tenancy, permissions, auth, transaction, provider, LLM, and runtime docs
- tests that encode required behavior, when tests are in scope
- ArchMap v2 covers and source-grounded context boundaries when an AG
  measurement profile is requested

## Evidence Classification

- **Normative**: explicit rules or user-approved decisions. Eligible for an evaluator selector when the registry has a matching evaluator.
- **Conventional**: repeated source pattern without explicit rule. Good for questions or future evaluator registry work.
- **Source shape only**: current code shape. Do not promote to policy without user confirmation.
- **Missing**: no evidence. Ask questions before writing a policy.

## Mapping Evidence To Policy

| Evidence | LawPolicy surface |
| --- | --- |
| "Measure selected cover for Čech obstruction" | `law: "ag.cech-obstruction"`, `evaluator: "ag.cech-obstruction"`, plus `measurementProfileRef` |
| "Measure square-free repair candidates" | `law: "ag.square-free-repair"`, `evaluator: "ag.square-free-repair"`, plus `measurementProfileRef` |
| "Measure law-conflict Tor for a selected pair" | `lawPair: ["law:left", "law:right"]`, `evaluator: "ag.law-conflict-tor"`, plus `measurementProfileRef` |
| "Check a supplied SAGA repair descent input" | `law: "ag.saga-descent"`, `evaluator: "ag.saga-descent"`, plus `measurementProfileRef` and a checked RepairPlan |
| repeated but undocumented pattern | question to user, not policy yet |

Do not translate evidence into witness rules, signature axes, coverage
requirements, exactness assumptions, or distance profiles. Those are law-equation-surface
and evaluator registry responsibilities in the current surface. For AG, put selected cover, coefficient,
resolution selector, predicates, certificate selector, and
verdict discipline in the separate `measurement-profile/v0.5.4` artifact.

## Survey Output

Before drafting JSON, summarize:

- docs and files read
- candidate laws with evidence refs
- candidate evaluator selectors
- candidate AG measurement profile fields, if applicable
- decisions that need user confirmation
- blind spots and excluded evidence

## PRD-3 Residual-Zero Scope

The PRD-3 residual-zero review must include the publication and authoring
surfaces below, in addition to the runtime and archived-document checks:

- `website/src/archsig/reference/index.html`
- `website/src/archsig/getting-started/index.html`
- `tools/fieldsig/README.md`
- `tools/archsig/skills/law-policy-creater/references/schema-guide.md`
- `tools/archsig/skills/law-policy-creater/references/question-bank.md`
- `tools/archsig/skills/law-policy-creater/references/convention-survey.md`

Run the same repository-root `rg` lint over all six paths after changing the
current CLI, schema, or registry vocabulary. Historical material belongs under
`docs/archive/` and is not a current claim.
