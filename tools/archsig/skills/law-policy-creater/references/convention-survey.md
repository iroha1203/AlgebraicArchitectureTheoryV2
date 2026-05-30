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

- **Normative**: explicit rules or user-approved decisions. Eligible for `selectedLaws[]`.
- **Conventional**: repeated source pattern without explicit rule. Good for coverage requirements or questions.
- **Observed only**: current code shape. Do not promote to law without user confirmation.
- **Missing**: no evidence. Ask questions before writing a selected law.

## Mapping Evidence To Policy

| Evidence | LawPolicy surface |
| --- | --- |
| "Routes must use permission dependency X" | selected law + permission axis + coverage requirement for routes |
| "Tenant data must be scoped by workspace/org" | selected law + tenant boundary witness + model/route coverage |
| "External provider output must be validated before persistence" | selected law + provider mediation witness + trust/effect/contract coverage |
| "Jobs must be idempotent and retry-safe" | selected law + state/effect ordering axis + runtime/test coverage |
| "Repository owns transaction flush" | selected law + transaction boundary witness + state/effect coverage |
| repeated but undocumented pattern | question to user, not selected law yet |

## Survey Output

Before drafting JSON, summarize:

- docs and files read
- candidate laws with evidence refs
- candidate coverage requirements
- decisions that need user confirmation
- blind spots and excluded evidence
