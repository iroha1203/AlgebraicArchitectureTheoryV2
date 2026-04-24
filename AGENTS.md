# Repository Guidelines

## Project Structure

- The Lean library root is `Formal.lean`.
- Core formalization lives under `Formal/Arch`.
- Research notes live under `docs`.
- `Main.lean` provides the executable target `aatv2`.
- Build configuration is `lakefile.toml`; the Lean version is pinned by
  `lean-toolchain`.

## Build Commands

- `lake build`: build all targets.
- `lake build Formal`: build the Lean library only.
- `lake exe aatv2`: run the executable target.
- `lake env lean Formal/Arch/Layering.lean`: type-check one file.

## Formalization Policy

- Do not introduce `axiom`, `admit`, `sorry`, or `unsafe` without explicit
  discussion.
- Keep definitions small and grow equivalences as theorems.
- `Decomposable` currently means `StrictLayered`; acyclicity, finite
  propagation, nilpotence, and spectral conditions should remain separate
  theorems or future proof obligations.
- `ComponentCategory` is thin and intentionally forgets path counts and walk
  lengths. Quantitative metrics should use `Walk`, `Path`, adjacency matrices,
  or a future free-category construction.

## Documentation Policy

- When changing a research claim in `docs`, keep the corresponding Lean status
  clear: proved, defined only, future proof obligation, or empirical hypothesis.
- Keep Lean-proved claims separate from empirical validation claims.

