# Sharded ArchMap Authoring

Large source surveys may be drafted in slices, but ArchSig commands consume a
single exported `archmap/v0.5.0` document.

Slice merge checks should ensure:

- source ids are globally unique;
- atom ids are globally unique;
- context ids are globally unique;
- cover refs resolve to exported contexts;
- source refs resolve to exported sources;
- the final document declares the fixed extraction doctrine.

The exported artifact remains the only command input.
