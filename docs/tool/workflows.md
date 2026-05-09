# Workflows

Tooling workflow は、artifact を段階的に作り、claim boundary を落とさずに report へ進める。

## First adoption

初回導入の最小 flow は次である。

```text
scan
  -> validate
  -> snapshot
  -> baseline policy
  -> first signature report
```

初回導入では、未測定軸と unsupported constructs を明示することを優先する。

## PR review

PR review の基本 flow は次である。

```text
before scan
  -> after scan
  -> signature diff
  -> AIR
  -> theorem precondition check
  -> feature extension report
  -> policy decision
  -> PR comment summary
```

PR 上で読むべきものは、blocking finding だけではない。
unmeasured axes、coverage gaps、missing preconditions、non-conclusions を同時に読む。

## Generated-change provenance

generated change は、prompt、model、generated patch、human review boundary を evidence として
保持する。

```text
ai session evidence:
  provider
  model
  prompt ref
  generated patch
  human reviewed
```

generated change であることは、良いとも悪いとも結論しない。provenance は review boundary と
reproducibility のために保持する。

## Scheduled scan

scheduled scan は drift ledger を更新する。

```text
scheduled scan
  -> signature snapshot
  -> drift ledger
  -> ownership boundary monitor
  -> operational feedback
```

daily drift は trend を示す artifact であり、因果効果を証明する artifact ではない。

## Architecture Dynamics workflow

Architecture Dynamics tooling は、PR force report、signature trajectory report、
dynamics metrics report を扱う。

```text
architecture field snapshot
  + operation proposal log
  + PR force report
  -> signature trajectory report
  -> architecture dynamics metrics report
```

probabilistic operation distribution は empirical reading として扱い、formal core では
finite support と bounded script を明示する。
