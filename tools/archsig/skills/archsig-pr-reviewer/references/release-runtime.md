# Release Runtime

Release bundles need the `archsig` binary, this skill directory, ArchView, and
the command guide.

Required commands:

```bash
"$ARCHSIG_BIN" compare --base-run <base> --head-run <head> --out-dir <compare>
"$ARCHSIG_BIN" gate --packet <head>/archsig-measurement-packet.json --policy <policy> --comparison <compare>/archsig-comparison-report.json --out <gate-report>
```
