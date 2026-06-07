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

## Evidence Classification

- **Normative**: explicit rules or user-approved decisions. Eligible for a v1 policy pack or evaluator selector.
- **Conventional**: repeated source pattern without explicit rule. Good for coverage requirements or questions.
- **Observed only**: current code shape. Do not promote to law without user confirmation.
- **Missing**: no evidence. Ask questions before writing a selected law.

## Mapping Evidence To Policy

| Evidence | LawPolicy surface |
| --- | --- |
| "Repository adopts SOLID" | `pack: "solid@1"`, `basis: ["policy-basis:solid"]` |
| "Domain layer must not depend on infrastructure" | `law: "domain.no-direct-infra-dependency"`, `evaluator: "domain.no-direct-infra-dependency@1"`, `basis: ["policy-basis:layering"]` |
| repeated but undocumented pattern | question to user, not selected policy yet |

Do not translate evidence into witness rules, signature axes, coverage
requirements, exactness assumptions, or distance profiles. Those are evaluator
registry responsibilities in v1.

## Survey Output

Before drafting JSON, summarize:

- docs and files read
- candidate laws with evidence refs
- candidate policy pack / evaluator selectors
- decisions that need user confirmation
- blind spots and excluded evidence
