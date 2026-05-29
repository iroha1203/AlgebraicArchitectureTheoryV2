# Sharded ArchMap Fixtures

These fixtures define the planned horizontal sharded authoring layout for large
ArchMaps. They are design fixtures, not current CLI inputs.

- `manifest.json` uses `archmap-shard-manifest-v0`.
- `slices/*.archmap-slice.json` use `archmap-observation-slice-v0`.
- Each slice is a bounded observation slice over one repository surface, such as
  authority, state, or runtime evidence.
- A future bundle/export command should combine these shards into one
  `archmap-observation-map-v0` JSON document before running current ArchSig
  validation or analysis commands.

The fixtures use synthetic source refs only. They must not include private
real-codebase source content.
