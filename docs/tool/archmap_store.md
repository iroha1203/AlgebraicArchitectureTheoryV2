# ArchMapStore Notes

ArchMapStore is a forward storage idea for ArchMap history. It is not the
current ArchSig runtime input surface.

Current PR / CI comparison is handled by ArchSig compare + gate over concrete
measurement runs. The computed comparison report owns the current change-local
diff surface.

Historical ArchMapDelta / snapshot / index designs are retained only as future
storage notes. They are not accepted by the current CLI, and they are not a
compatibility replacement for retired PR review commands.

Current boundary:

```text
ArchMap + policy-bundle(LawPolicy + law-equation-surface + MeasurementProfile)
  -> archsig analyze
  -> measurement packet / summary / viewer data / run manifest
  -> archsig compare
  -> archsig gate
```

If ArchMapStore is revived, it should feed ArchMap-level evidence into this
same measurement workflow rather than introduce a second diagnostic path.
