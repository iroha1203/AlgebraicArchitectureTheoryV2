# ArchSig Input / Output Layout

Use this reference to choose paths without relying on the ArchSig source repository.

## Binary

Use the built executable:

```bash
${ARCHSIG_BIN:-archsig} --help
```

If it fails because the binary is not found, ask for one of:

- `ARCHSIG_BIN=/absolute/path/to/archsig`
- an `archsig` executable on `PATH`
- permission to build or install ArchSig, if the source repository is available

Do not assume `tools/archsig/Cargo.toml` exists.

## Output Root

Use `.archsig/` for generated local artifacts:

```text
.archsig/
├── signature/
│   ├── sig0.json
│   ├── sig0-validation.json
│   ├── current/
│   ├── previous/
│   └── baseline/
├── archmap/
│   ├── archmap.json
│   ├── validation.json
│   ├── air.json
│   ├── air-validation.json
│   ├── theorem-check.json
│   ├── feature-report.json
│   ├── operation-support-estimate.json
│   ├── forecast-cone-skeleton.json
│   └── consequence-envelope-report.json
├── sft/
│   └── forecast-calibration-hook.json
├── operational/
└── reports/
```

The CLI creates parent directories for `--out` and `--out-dir`. Do not require users to create them.

## Inputs

Common inputs:

- repository root: `--root .`
- ArchMap JSON: `.archsig/archmap/archmap.json` or a user-specified path
- validation report: `.archsig/archmap/validation.json`
- Sig0: `.archsig/signature/sig0.json`
- PR metadata: `.archsig/pr-metadata.json`
- previous snapshot: `.archsig/signature/previous/snapshot.json`
- current snapshot: `.archsig/signature/current/snapshot.json`

If an expected input does not exist, do not fabricate it. Either run the upstream command or ask for the input path.

## Path Rules

- Keep generated files under `.archsig/` unless the user asks for another location.
- Keep canonical examples, fixtures, docs, and checked-in reports outside `.archsig/`.
- Do not read `.archsig/` as source evidence unless the user explicitly asks to analyze generated artifacts.
- Report exact output paths in the final answer.
