# ArchSig vX.Y.Z

## Overview

ArchSig vX.Y.Z is <one-sentence summary of this release line>.

This release adds or improves <main user-facing value>.
ArchSig should be read as <AAT structural telemetry / analysis packet / review artifact / other release-specific role>.

## Downloads

| Platform | Asset |
| --- | --- |
| macOS | `archsig-vX.Y.Z-macos-universal.tar.gz` |
| Linux x86_64 | `archsig-vX.Y.Z-linux-x86_64.tar.gz` |
| Linux arm64 | `archsig-vX.Y.Z-linux-arm64.tar.gz` |
| Windows x86_64 | `archsig-vX.Y.Z-windows-x86_64.zip` |

Use `SHA256SUMS.txt` to verify checksums.

## Getting Started

```bash
archsig --help
```

Representative workflow:

```bash
archsig llm-native-workflow \
  --archmap path/to/archmap.json \
  --law-policy path/to/law_policy.json \
  --out-dir .archsig/llm-native
```

## Highlights

- <User-visible change>
- <CLI / artifact / schema / report change>
- <Docs / examples / fixtures change>

## Compatibility And Migration

- Breaking change: <yes / no>
- Artifact schema: `<schema-name>` <changed / unchanged>
- CLI surface: <added / changed / removed>
- Existing workflow impact: <short note>

## Verification

This release line was verified with:

- [ ] `cargo test --manifest-path tools/archsig/Cargo.toml`
- [ ] `cargo test --manifest-path tools/fieldsig/Cargo.toml` when FieldSig boundaries are affected
- [ ] `lake build` when Lean or docs claims are affected
- [ ] Release asset build
- [ ] `SHA256SUMS.txt` generation

## Positioning

ArchSig vX.Y.Z reads <which AAT-facing surface this release covers>.

FieldSig remains responsible for <forecast / governance / calibration / operational feedback>, which is intentionally separated from this ArchSig release.

## Boundaries

ArchSig analysis packets are not Lean theorem proofs or global architecture truth.
It is a structural reading artifact based on the observed ArchMap and interpretation profile. It should carry coverage gaps, nonConclusions, and representation boundaries into review.

## Related

- Release tag: `vX.Y.Z`
- Issues / PRs: #...
- Command guide: `tools/archsig/docs/commands.md`
